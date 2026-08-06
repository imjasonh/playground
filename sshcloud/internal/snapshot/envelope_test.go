package snapshot

import (
	"bytes"
	"context"
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"
)

type memoryObject struct {
	body       []byte
	generation int64
}

type memoryObjects struct {
	mu          sync.Mutex
	next        int64
	objects     map[string]memoryObject
	versions    map[string]map[int64]memoryObject
	currentGate chan struct{}
	currentSeen chan struct{}
	currentErr  error
}

func newMemoryObjects() *memoryObjects {
	return &memoryObjects{
		objects: make(map[string]memoryObject), versions: make(map[string]map[int64]memoryObject),
		next: 100,
	}
}

func (m *memoryObjects) Write(_ context.Context, name string, condition ObjectCondition, write func(io.Writer) error) (ObjectAttrs, error) {
	var body bytes.Buffer
	if err := write(&body); err != nil {
		return ObjectAttrs{}, err
	}
	if strings.HasSuffix(name, "/current.json") && m.currentGate != nil {
		m.currentSeen <- struct{}{}
		<-m.currentGate
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	old, exists := m.objects[name]
	if condition.DoesNotExist && exists {
		return ObjectAttrs{}, ErrObjectPrecondition
	}
	if condition.MatchGeneration && (!exists || old.generation != condition.Generation) {
		return ObjectAttrs{}, ErrObjectPrecondition
	}
	m.next++
	object := memoryObject{body: append([]byte(nil), body.Bytes()...), generation: m.next}
	m.objects[name] = object
	if m.versions[name] == nil {
		m.versions[name] = make(map[int64]memoryObject)
	}
	m.versions[name][object.generation] = object
	if strings.HasSuffix(name, "/current.json") && m.currentErr != nil {
		return ObjectAttrs{}, m.currentErr
	}
	return ObjectAttrs{Generation: object.generation, Size: int64(len(object.body))}, nil
}

func (m *memoryObjects) Read(_ context.Context, name string, generation int64) (io.ReadCloser, ObjectAttrs, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	object, ok := m.objects[name]
	if generation > 0 && (!ok || object.generation != generation) {
		object, ok = m.versions[name][generation]
	}
	if !ok {
		return nil, ObjectAttrs{}, ErrObjectNotFound
	}
	body := append([]byte(nil), object.body...)
	return io.NopCloser(bytes.NewReader(body)), ObjectAttrs{
		Generation: object.generation, Size: int64(len(body)),
	}, nil
}

func (m *memoryObjects) Stat(_ context.Context, name string) (ObjectAttrs, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	object, ok := m.objects[name]
	if !ok {
		return ObjectAttrs{}, ErrObjectNotFound
	}
	return ObjectAttrs{Generation: object.generation, Size: int64(len(object.body))}, nil
}

func (m *memoryObjects) Delete(_ context.Context, name string, generation int64) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if generation <= 0 {
		return errors.New("object generation must be positive")
	}
	object, ok := m.objects[name]
	if _, ok := m.versions[name][generation]; !ok {
		return nil
	}
	delete(m.versions[name], generation)
	if ok && object.generation == generation {
		delete(m.objects, name)
	}
	return nil
}

func (m *memoryObjects) DeleteCurrent(_ context.Context, name string, generation int64) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	object, ok := m.objects[name]
	if !ok || generation <= 0 || object.generation != generation {
		return ErrObjectPrecondition
	}
	delete(m.objects, name)
	delete(m.versions[name], generation)
	return nil
}

func (*memoryObjects) Health(context.Context) error { return nil }
func (*memoryObjects) Close() error                 { return nil }

func (m *memoryObjects) alter(name string, alter func([]byte) []byte) {
	m.mu.Lock()
	defer m.mu.Unlock()
	object := m.objects[name]
	object.body = alter(append([]byte(nil), object.body...))
	m.objects[name] = object
	m.versions[name][object.generation] = object
}

type fakeKMS struct {
	aead cipher.AEAD
}

func newFakeKMS(t *testing.T) *fakeKMS {
	t.Helper()
	key := make([]byte, 32)
	if _, err := rand.Read(key); err != nil {
		t.Fatal(err)
	}
	block, err := aes.NewCipher(key)
	if err != nil {
		t.Fatal(err)
	}
	aead, err := cipher.NewGCM(block)
	if err != nil {
		t.Fatal(err)
	}
	return &fakeKMS{aead: aead}
}

func (k *fakeKMS) Wrap(_ context.Context, plaintext, aad []byte) ([]byte, error) {
	nonce := make([]byte, k.aead.NonceSize())
	if _, err := rand.Read(nonce); err != nil {
		return nil, err
	}
	return k.aead.Seal(nonce, nonce, plaintext, aad), nil
}

func (k *fakeKMS) Unwrap(_ context.Context, ciphertext, aad []byte) ([]byte, error) {
	if len(ciphertext) < k.aead.NonceSize() {
		return nil, fmt.Errorf("truncated wrapped key")
	}
	nonce := ciphertext[:k.aead.NonceSize()]
	return k.aead.Open(nil, nonce, ciphertext[k.aead.NonceSize():], aad)
}

func (*fakeKMS) Close() error { return nil }

func TestEnvelopeRejectsTamperSwapTruncationAndWrongAAD(t *testing.T) {
	t.Parallel()
	ctx := t.Context()
	refA := Ref{User: "alice", App: "fortune", Gen: "g1"}
	refB := Ref{User: "carol", App: "fortune", Gen: "g2"}

	t.Run("tamper", func(t *testing.T) {
		store, objects := testEnvelope(t)
		if err := store.Put(ctx, refA, testPackage(t, refA)); err != nil {
			t.Fatal(err)
		}
		name := currentPackageName(t, store, refA)
		objects.alter(name, func(body []byte) []byte {
			body[len(body)/2] ^= 0x80
			return body
		})
		if _, err := store.Get(ctx, refA, filepath.Join(t.TempDir(), "out")); err == nil {
			t.Fatal("tampered package authenticated")
		}
	})

	t.Run("truncation", func(t *testing.T) {
		store, objects := testEnvelope(t)
		if err := store.Put(ctx, refA, testPackage(t, refA)); err != nil {
			t.Fatal(err)
		}
		name := currentPackageName(t, store, refA)
		objects.alter(name, func(body []byte) []byte { return body[:len(body)-1] })
		if _, err := store.Get(ctx, refA, filepath.Join(t.TempDir(), "out")); err == nil {
			t.Fatal("truncated package authenticated")
		}
	})

	t.Run("tenant swap", func(t *testing.T) {
		store, objects := testEnvelope(t)
		if err := store.Put(ctx, refA, testPackage(t, refA)); err != nil {
			t.Fatal(err)
		}
		if err := store.Put(ctx, refB, testPackage(t, refB)); err != nil {
			t.Fatal(err)
		}
		nameA := currentPackageName(t, store, refA)
		nameB := currentPackageName(t, store, refB)
		objects.mu.Lock()
		a, b := objects.objects[nameA], objects.objects[nameB]
		a.body, b.body = b.body, a.body
		objects.objects[nameA], objects.objects[nameB] = a, b
		objects.mu.Unlock()
		if _, err := store.Get(ctx, refA, filepath.Join(t.TempDir(), "out")); err == nil {
			t.Fatal("cross-tenant package swap authenticated")
		}
	})

	t.Run("keyset AAD", func(t *testing.T) {
		store, objects := testEnvelope(t)
		if err := store.Put(ctx, refA, testPackage(t, refA)); err != nil {
			t.Fatal(err)
		}
		if err := store.Put(ctx, refB, testPackage(t, refB)); err != nil {
			t.Fatal(err)
		}
		manifestA := currentManifestName(t, store, refA)
		manifestB := currentManifestName(t, store, refB)
		objects.mu.Lock()
		var a, b versionManifest
		if err := json.Unmarshal(objects.objects[manifestA].body, &a); err != nil {
			objects.mu.Unlock()
			t.Fatal(err)
		}
		if err := json.Unmarshal(objects.objects[manifestB].body, &b); err != nil {
			objects.mu.Unlock()
			t.Fatal(err)
		}
		a.WrappedKeyset = append([]byte(nil), b.WrappedKeyset...)
		body, err := json.Marshal(a)
		if err != nil {
			objects.mu.Unlock()
			t.Fatal(err)
		}
		object := objects.objects[manifestA]
		object.body = append(body, '\n')
		objects.objects[manifestA] = object
		objects.mu.Unlock()
		if _, err := store.Get(ctx, refA, filepath.Join(t.TempDir(), "out")); err == nil {
			t.Fatal("wrapped keyset accepted different tenant AAD")
		}
	})
}

func TestEnvelopeCurrentPublicationUsesGenerationPrecondition(t *testing.T) {
	t.Parallel()
	store, objects := testEnvelope(t)
	ids := make(chan string, 3)
	ids <- strings.Repeat("a", 32)
	ids <- strings.Repeat("b", 32)
	ids <- strings.Repeat("c", 32)
	store.NewSnapshotID = func() (string, error) { return <-ids, nil }
	ref := Ref{User: "alice", App: "fortune", Gen: "g1"}
	pkg := testPackage(t, ref)
	if err := store.Put(t.Context(), ref, pkg); err != nil {
		t.Fatal(err)
	}

	objects.currentGate = make(chan struct{})
	objects.currentSeen = make(chan struct{}, 2)

	results := make(chan error, 2)
	go func() { results <- store.Put(t.Context(), ref, pkg) }()
	go func() { results <- store.Put(t.Context(), ref, pkg) }()
	<-objects.currentSeen
	<-objects.currentSeen
	close(objects.currentGate)
	first, second := <-results, <-results
	if (first == nil) == (second == nil) {
		t.Fatalf("exactly one publication must win: first=%v second=%v", first, second)
	}
	if first != nil && !errors.Is(first, ErrConcurrentPublication) {
		t.Fatalf("first error = %v", first)
	}
	if second != nil && !errors.Is(second, ErrConcurrentPublication) {
		t.Fatalf("second error = %v", second)
	}
}

func TestEnvelopeRetainsImmutableObjectsWhenPublicationOutcomeIsUnknown(t *testing.T) {
	t.Parallel()
	store, objects := testEnvelope(t)
	ref := Ref{User: "alice", App: "fortune", Gen: "g1"}
	objects.currentErr = errors.New("lost write acknowledgement")
	err := store.Put(t.Context(), ref, testPackage(t, ref))
	if err == nil || !strings.Contains(err.Error(), "outcome is unknown") {
		t.Fatalf("ambiguous publication error = %v", err)
	}
	objects.currentErr = nil
	if _, err := store.Get(
		t.Context(),
		ref,
		filepath.Join(t.TempDir(), "out"),
	); err != nil {
		t.Fatalf("committed ambiguous publication was corrupted by cleanup: %v", err)
	}
}

func TestEnvelopeRejectsIdentityLayoutAndFileLimitsBeforePublish(t *testing.T) {
	t.Parallel()
	ref := Ref{User: "alice", App: "fortune", Gen: "g1"}
	for name, mutate := range map[string]func(*testing.T, Package){
		"identity": func(t *testing.T, pkg Package) {
			meta, err := pkg.ReadMeta()
			if err != nil {
				t.Fatal(err)
			}
			meta.Gen = "g2"
			if err := pkg.WriteMeta(meta); err != nil {
				t.Fatal(err)
			}
		},
		"layout": func(t *testing.T, pkg Package) {
			meta, err := pkg.ReadMeta()
			if err != nil {
				t.Fatal(err)
			}
			meta.LayoutVersion = "firecracker-direct-v1"
			if err := pkg.WriteMeta(meta); err != nil {
				t.Fatal(err)
			}
		},
		"rootfs size": func(t *testing.T, pkg Package) {
			if err := os.Truncate(pkg.RootfsPath, MaxRootfsBytes+1); err != nil {
				t.Fatal(err)
			}
		},
	} {
		t.Run(name, func(t *testing.T) {
			store, objects := testEnvelope(t)
			pkg := testPackage(t, ref)
			mutate(t, pkg)
			if err := store.Put(t.Context(), ref, pkg); err == nil {
				t.Fatal("invalid package was published")
			}
			if _, ok := objects.objects[store.currentObject(ref)]; ok {
				t.Fatal("current pointer exists after rejected package")
			}
		})
	}
}

func TestEnvelopeRetainsOnlyCurrentAndPreviousEncryptedVersions(t *testing.T) {
	t.Parallel()
	store, objects := testEnvelope(t)
	ids := []string{
		strings.Repeat("a", 32),
		strings.Repeat("b", 32),
		strings.Repeat("c", 32),
	}
	next := 0
	store.NewSnapshotID = func() (string, error) {
		id := ids[next]
		next++
		return id, nil
	}
	ref := Ref{User: "alice", App: "fortune", Gen: "g1"}
	pkg := testPackage(t, ref)
	for range ids {
		if err := store.Put(t.Context(), ref, pkg); err != nil {
			t.Fatal(err)
		}
	}
	current := readCurrentForTest(t, store, ref)
	if current.SnapshotID != ids[2] || current.Previous == nil ||
		current.Previous.SnapshotID != ids[1] {
		t.Fatalf("current chain = %+v", current)
	}
	objects.mu.Lock()
	defer objects.mu.Unlock()
	if generations := objects.versions[store.currentObject(ref)]; len(generations) != 1 {
		t.Fatalf("current pointer retained %d object generations", len(generations))
	}
	for _, suffix := range []string{"package.tink", "manifest.json"} {
		if _, ok := objects.objects[store.versionObject(ref, ids[0], suffix)]; ok {
			t.Fatalf("superseded version %s remains", suffix)
		}
		for _, retained := range ids[1:] {
			if _, ok := objects.objects[store.versionObject(ref, retained, suffix)]; !ok {
				t.Fatalf("retained version %s %s is missing", retained, suffix)
			}
		}
	}
}

func TestEnvelopeGuardFailureCannotPublishOrDeleteCurrent(t *testing.T) {
	t.Parallel()
	store, _ := testEnvelope(t)
	ref := Ref{User: "alice", App: "fortune", Gen: "g1"}
	pkg := testPackage(t, ref)
	if err := store.Put(t.Context(), ref, pkg); err != nil {
		t.Fatal(err)
	}
	before := readCurrentForTest(t, store, ref)
	denied := errors.New("fence expired")
	if err := store.PutGuarded(
		t.Context(), ref, pkg, func(context.Context) error { return denied },
	); !errors.Is(err, denied) {
		t.Fatalf("guarded put error = %v", err)
	}
	if after := readCurrentForTest(t, store, ref); after != before {
		t.Fatalf("guarded put changed current: before=%+v after=%+v", before, after)
	}
	if err := store.DeleteGuarded(
		t.Context(), ref, func(context.Context) error { return denied },
	); !errors.Is(err, denied) {
		t.Fatalf("guarded delete error = %v", err)
	}
	if after := readCurrentForTest(t, store, ref); after != before {
		t.Fatalf("guarded delete changed current: before=%+v after=%+v", before, after)
	}
}

func TestEnvelopeDeleteCASCannotRemoveConcurrentPublicationPredecessor(t *testing.T) {
	t.Parallel()
	store, _ := testEnvelope(t)
	ids := make(chan string, 2)
	ids <- strings.Repeat("a", 32)
	ids <- strings.Repeat("b", 32)
	store.NewSnapshotID = func() (string, error) { return <-ids, nil }
	ref := Ref{User: "alice", App: "fortune", Gen: "g1"}
	pkg := testPackage(t, ref)
	if err := store.Put(t.Context(), ref, pkg); err != nil {
		t.Fatal(err)
	}

	err := store.DeleteGuarded(t.Context(), ref, func(ctx context.Context) error {
		return store.Put(ctx, ref, pkg)
	})
	if !errors.Is(err, ErrConcurrentPublication) {
		t.Fatalf("delete raced with publication: %v", err)
	}
	current := readCurrentForTest(t, store, ref)
	if current.SnapshotID != strings.Repeat("b", 32) || current.Previous == nil ||
		current.Previous.SnapshotID != strings.Repeat("a", 32) {
		t.Fatalf("concurrent current chain was damaged: %+v", current)
	}
	if _, err := store.Get(t.Context(), ref, filepath.Join(t.TempDir(), "out")); err != nil {
		t.Fatalf("concurrent publication is unreadable: %v", err)
	}
}

func TestEnvelopeMetaAuthenticatesPinnedManifestMetadata(t *testing.T) {
	t.Parallel()
	store, objects := testEnvelope(t)
	ref := Ref{User: "alice", App: "fortune", Gen: "g1"}
	if err := store.Put(t.Context(), ref, testPackage(t, ref)); err != nil {
		t.Fatal(err)
	}
	name := currentManifestName(t, store, ref)
	objects.mu.Lock()
	object := objects.objects[name]
	var manifest versionManifest
	if err := json.Unmarshal(object.body, &manifest); err != nil {
		objects.mu.Unlock()
		t.Fatal(err)
	}
	manifest.Meta.Tier = "small"
	_, manifest.MetaSHA256, _ = digestMeta(manifest.Meta)
	body, err := json.Marshal(manifest)
	if err != nil {
		objects.mu.Unlock()
		t.Fatal(err)
	}
	object.body = append(body, '\n')
	objects.objects[name] = object
	objects.versions[name][object.generation] = object
	objects.mu.Unlock()
	if _, err := store.Meta(t.Context(), ref); err == nil {
		t.Fatal("tampered manifest metadata authenticated")
	}
	before := readCurrentForTest(t, store, ref)
	if err := store.Delete(t.Context(), ref); err == nil {
		t.Fatal("delete trusted unauthenticated manifest metadata")
	}
	if after := readCurrentForTest(t, store, ref); after != before {
		t.Fatalf("failed authenticated delete changed current: before=%+v after=%+v", before, after)
	}
}

func testEnvelope(t *testing.T) (*EnvelopeStore, *memoryObjects) {
	t.Helper()
	objects := newMemoryObjects()
	return &EnvelopeStore{
		Objects: objects, Wrapper: newFakeKMS(t), Prefix: "test",
		ExpectedLayout: "firecracker-jailer-v1",
		Now:            func() time.Time { return time.Unix(1_800_000_000, 0) },
	}, objects
}

func testPackage(t *testing.T, ref Ref) Package {
	t.Helper()
	pkg := NewPackageDir(filepath.Join(t.TempDir(), "package"))
	if err := os.MkdirAll(pkg.Dir, 0o700); err != nil {
		t.Fatal(err)
	}
	for _, file := range []string{pkg.StatePath, pkg.MemPath, pkg.RootfsPath} {
		if err := os.WriteFile(file, []byte(filepath.Base(file)+" bytes"), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	if err := pkg.WriteMeta(Meta{
		SchemaVersion: SchemaVersion, LayoutVersion: "firecracker-jailer-v1",
		User: ref.User, App: ref.App, Gen: ref.Gen, CreatedAt: time.Unix(1_800_000_000, 0),
	}); err != nil {
		t.Fatal(err)
	}
	return pkg
}

func currentPackageName(t *testing.T, store *EnvelopeStore, ref Ref) string {
	t.Helper()
	current := readCurrentForTest(t, store, ref)
	return store.versionObject(ref, current.SnapshotID, "package.tink")
}

func currentManifestName(t *testing.T, store *EnvelopeStore, ref Ref) string {
	t.Helper()
	current := readCurrentForTest(t, store, ref)
	return store.versionObject(ref, current.SnapshotID, "manifest.json")
}

func readCurrentForTest(t *testing.T, store *EnvelopeStore, ref Ref) currentManifest {
	t.Helper()
	objects := store.Objects.(*memoryObjects)
	objects.mu.Lock()
	currentBody := append([]byte(nil), objects.objects[store.currentObject(ref)].body...)
	objects.mu.Unlock()
	var current currentManifest
	if err := json.Unmarshal(currentBody, &current); err != nil {
		t.Fatal(err)
	}
	return current
}
