package snapshot

import (
	"bytes"
	"context"
	"crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path"
	"strings"
	"time"

	"github.com/tink-crypto/tink-go/v2/insecurecleartextkeyset"
	"github.com/tink-crypto/tink-go/v2/keyset"
	"github.com/tink-crypto/tink-go/v2/streamingaead"
)

const (
	envelopeSchemaVersion = 2
	maxManifestBytes      = 32 << 10
)

var ErrConcurrentPublication = errors.New("concurrent snapshot publication")

type versionManifest struct {
	SchemaVersion     int       `json:"schema_version"`
	Ref               Ref       `json:"ref"`
	SnapshotID        string    `json:"snapshot_id"`
	PackageGeneration int64     `json:"package_generation"`
	PackageSize       int64     `json:"package_size"`
	WrappedKeyset     []byte    `json:"wrapped_keyset"`
	Meta              Meta      `json:"meta"`
	MetaSHA256        string    `json:"meta_sha256"`
	CreatedAt         time.Time `json:"created_at"`
}

type versionPointer struct {
	SnapshotID         string `json:"snapshot_id"`
	ManifestGeneration int64  `json:"manifest_generation"`
}

type currentManifest struct {
	SchemaVersion      int             `json:"schema_version"`
	Ref                Ref             `json:"ref"`
	SnapshotID         string          `json:"snapshot_id"`
	ManifestGeneration int64           `json:"manifest_generation"`
	Previous           *versionPointer `json:"previous,omitempty"`
}

// EnvelopeStore stores immutable Tink Streaming AEAD packages and publishes a
// small current pointer with an exact generation precondition.
type EnvelopeStore struct {
	Objects        ObjectStore
	Wrapper        KeyWrapper
	Prefix         string
	ExpectedLayout string
	Now            func() time.Time
	NewSnapshotID  func() (string, error)
}

func NewGCSStore(ctx context.Context, bucket, prefix, kmsKey, expectedLayout string) (*EnvelopeStore, error) {
	if strings.TrimSpace(expectedLayout) == "" {
		return nil, fmt.Errorf("expected snapshot layout is required")
	}
	objects, err := NewGCSObjects(ctx, bucket)
	if err != nil {
		return nil, err
	}
	wrapper, err := NewCloudKMSWrapper(ctx, kmsKey)
	if err != nil {
		_ = objects.Close()
		return nil, err
	}
	return &EnvelopeStore{
		Objects: objects, Wrapper: wrapper, Prefix: strings.Trim(prefix, "/"),
		ExpectedLayout: expectedLayout,
	}, nil
}

func (s *EnvelopeStore) Put(ctx context.Context, ref Ref, pkg Package) error {
	return s.PutGuarded(ctx, ref, pkg, nil)
}

func (s *EnvelopeStore) PutGuarded(
	ctx context.Context,
	ref Ref,
	pkg Package,
	guard CommitGuard,
) (retErr error) {
	if err := s.validate(ref); err != nil {
		return err
	}
	validated, err := validatePackage(ref, pkg, s.ExpectedLayout)
	if err != nil {
		return err
	}
	previous, previousAttrs, exists, err := s.readCurrent(ctx, ref)
	if err != nil {
		return err
	}
	snapshotID, err := s.snapshotID()
	if err != nil {
		return err
	}
	metaDigest, metaDigestHex, err := digestMeta(validated.meta)
	if err != nil {
		return err
	}
	keyAAD := envelopeAAD(ref, snapshotID, metaDigest)
	handle, err := keyset.NewHandle(streamingaead.AES256GCMHKDF1MBKeyTemplate())
	if err != nil {
		return fmt.Errorf("generate snapshot streaming key: %w", err)
	}
	var cleartextKeyset bytes.Buffer
	if err := insecurecleartextkeyset.Write(handle, keyset.NewBinaryWriter(&cleartextKeyset)); err != nil {
		return fmt.Errorf("serialize snapshot keyset: %w", err)
	}
	keyBytes := cleartextKeyset.Bytes()
	defer wipe(keyBytes)
	wrappedKeyset, err := s.Wrapper.Wrap(ctx, keyBytes, keyAAD)
	if err != nil {
		return err
	}
	primitive, err := streamingaead.New(handle)
	if err != nil {
		return fmt.Errorf("create snapshot streaming AEAD: %w", err)
	}

	packageName := s.versionObject(ref, snapshotID, "package.tink")
	var packageAttrs ObjectAttrs
	packageAttrs, err = s.Objects.Write(ctx, packageName, ObjectCondition{DoesNotExist: true}, func(out io.Writer) error {
		encrypted, err := primitive.NewEncryptingWriter(out, packageAAD(keyAAD))
		if err != nil {
			return err
		}
		writeErr := writeValidatedArchive(ctx, encrypted, validated)
		closeErr := encrypted.Close()
		return errors.Join(writeErr, closeErr)
	})
	if err != nil {
		return fmt.Errorf("write immutable encrypted snapshot package: %w", err)
	}
	published := false
	var manifestAttrs ObjectAttrs
	defer func() {
		if published {
			return
		}
		cleanupCtx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
		defer cancel()
		var cleanupErr error
		if manifestAttrs.Generation > 0 {
			cleanupErr = errors.Join(
				cleanupErr,
				s.Objects.Delete(cleanupCtx, s.versionObject(ref, snapshotID, "manifest.json"), manifestAttrs.Generation),
			)
		}
		if packageAttrs.Generation > 0 {
			cleanupErr = errors.Join(cleanupErr, s.Objects.Delete(cleanupCtx, packageName, packageAttrs.Generation))
		}
		if cleanupErr != nil {
			retErr = errors.Join(retErr, fmt.Errorf("clean unpublished immutable snapshot objects: %w", cleanupErr))
		}
	}()
	if packageAttrs.Generation <= 0 || packageAttrs.Size <= 0 || packageAttrs.Size > MaxRequestBytes {
		return fmt.Errorf("encrypted snapshot package has invalid generation or size")
	}

	manifest := versionManifest{
		SchemaVersion: envelopeSchemaVersion, Ref: ref, SnapshotID: snapshotID,
		PackageGeneration: packageAttrs.Generation, PackageSize: packageAttrs.Size,
		WrappedKeyset: append([]byte(nil), wrappedKeyset...), Meta: validated.meta,
		MetaSHA256: metaDigestHex, CreatedAt: s.now(),
	}
	manifestName := s.versionObject(ref, snapshotID, "manifest.json")
	manifestAttrs, err = s.writeJSON(ctx, manifestName, ObjectCondition{DoesNotExist: true}, manifest)
	if err != nil {
		return fmt.Errorf("write immutable snapshot manifest: %w", err)
	}
	if manifestAttrs.Generation <= 0 {
		return fmt.Errorf("immutable snapshot manifest has invalid generation")
	}

	current := currentManifest{
		SchemaVersion: envelopeSchemaVersion, Ref: ref, SnapshotID: snapshotID,
		ManifestGeneration: manifestAttrs.Generation,
	}
	condition := ObjectCondition{DoesNotExist: true}
	if exists {
		condition = ObjectCondition{MatchGeneration: true, Generation: previousAttrs.Generation}
		current.Previous = &versionPointer{
			SnapshotID: previous.SnapshotID, ManifestGeneration: previous.ManifestGeneration,
		}
	}
	currentBody, err := marshalManifest(current)
	if err != nil {
		return err
	}
	if guard != nil {
		if err := guard(ctx); err != nil {
			return fmt.Errorf("revalidate snapshot publication fence: %w", err)
		}
	}
	if _, err := s.writeManifestBytes(ctx, s.currentObject(ref), condition, currentBody); err != nil {
		if errors.Is(err, ErrObjectPrecondition) {
			return fmt.Errorf("%w: %v", ErrConcurrentPublication, err)
		}
		// A transport error may arrive after GCS committed the conditional
		// write. Retaining the immutable package and manifest is safer than
		// deleting objects that an acknowledged current pointer may reference.
		// The error surfaces the ambiguous outcome for an explicit retry.
		published = true
		return fmt.Errorf(
			"publish current snapshot outcome is unknown; immutable objects retained: %w",
			err,
		)
	}
	published = true

	cleanupCtx, cancelCleanup := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancelCleanup()
	var cleanupErr error
	if exists {
		cleanupErr = errors.Join(
			cleanupErr,
			s.Objects.Delete(cleanupCtx, s.currentObject(ref), previousAttrs.Generation),
		)
		if previous.Previous != nil {
			cleanupErr = errors.Join(
				cleanupErr,
				s.deleteVersion(cleanupCtx, ref, *previous.Previous),
			)
		}
	}
	if cleanupErr != nil {
		return fmt.Errorf("snapshot published but retention cleanup failed: %w", cleanupErr)
	}
	return nil
}

func (s *EnvelopeStore) Get(ctx context.Context, ref Ref, destDir string) (Package, error) {
	pkg := NewPackageDir(destDir)
	if err := s.validate(ref); err != nil {
		return pkg, err
	}
	current, _, exists, err := s.readCurrent(ctx, ref)
	if err != nil {
		return pkg, err
	}
	if !exists {
		return pkg, os.ErrNotExist
	}
	manifest, err := s.readVersion(ctx, ref, current.pointer())
	if err != nil {
		return pkg, err
	}
	metaDigest, _, err := digestMeta(manifest.Meta)
	if err != nil {
		return pkg, err
	}
	keyAAD := envelopeAAD(ref, current.SnapshotID, metaDigest)
	cleartextKeyset, err := s.Wrapper.Unwrap(ctx, manifest.WrappedKeyset, keyAAD)
	if err != nil {
		return pkg, err
	}
	defer wipe(cleartextKeyset)
	handle, err := insecurecleartextkeyset.Read(keyset.NewBinaryReader(bytes.NewReader(cleartextKeyset)))
	if err != nil {
		return pkg, fmt.Errorf("read unwrapped snapshot keyset: %w", err)
	}
	primitive, err := streamingaead.New(handle)
	if err != nil {
		return pkg, fmt.Errorf("create snapshot streaming AEAD: %w", err)
	}
	reader, attrs, err := s.Objects.Read(
		ctx, s.versionObject(ref, current.SnapshotID, "package.tink"), manifest.PackageGeneration,
	)
	if err != nil {
		return pkg, fmt.Errorf("read encrypted snapshot package: %w", err)
	}
	defer reader.Close()
	if attrs.Generation != manifest.PackageGeneration || attrs.Size != manifest.PackageSize ||
		attrs.Size <= 0 || attrs.Size > MaxRequestBytes {
		return pkg, fmt.Errorf("encrypted snapshot package generation or size changed")
	}
	decrypted, err := primitive.NewDecryptingReader(io.LimitReader(reader, manifest.PackageSize), packageAAD(keyAAD))
	if err != nil {
		return pkg, fmt.Errorf("open encrypted snapshot package: %w", err)
	}
	pkg, err = ReadArchive(ctx, decrypted, ref, destDir, s.ExpectedLayout)
	if err != nil {
		return pkg, fmt.Errorf("authenticate snapshot package: %w", err)
	}
	archiveDigest, _, err := digestMeta(pkg.Meta)
	if err != nil || !bytes.Equal(archiveDigest, metaDigest) {
		if err == nil {
			err = fmt.Errorf("snapshot archive metadata differs from pinned manifest")
		}
		if cleanupErr := os.RemoveAll(destDir); cleanupErr != nil {
			err = errors.Join(
				err,
				fmt.Errorf("clean unauthenticated snapshot package: %w", cleanupErr),
			)
		}
		return NewPackageDir(destDir), err
	}
	return pkg, nil
}

func (s *EnvelopeStore) Has(ctx context.Context, ref Ref) (bool, error) {
	if err := s.validate(ref); err != nil {
		return false, err
	}
	current, _, exists, err := s.readCurrent(ctx, ref)
	if err != nil || !exists {
		return false, err
	}
	manifest, err := s.readVersion(ctx, ref, current.pointer())
	if err != nil {
		return false, err
	}
	cleartextKeyset, err := s.unwrapManifestKey(ctx, ref, current.pointer(), manifest)
	if err != nil {
		return false, err
	}
	wipe(cleartextKeyset)
	attrs, err := s.Objects.Stat(ctx, s.versionObject(ref, current.SnapshotID, "package.tink"))
	if errors.Is(err, ErrObjectNotFound) {
		return false, fmt.Errorf("published snapshot package is missing")
	}
	if err != nil {
		return false, err
	}
	if attrs.Generation != manifest.PackageGeneration || attrs.Size != manifest.PackageSize {
		return false, fmt.Errorf("published snapshot package generation changed")
	}
	return true, nil
}

func (s *EnvelopeStore) Meta(ctx context.Context, ref Ref) (Meta, error) {
	if err := s.validate(ref); err != nil {
		return Meta{}, err
	}
	current, _, exists, err := s.readCurrent(ctx, ref)
	if err != nil {
		return Meta{}, err
	}
	if !exists {
		return Meta{}, os.ErrNotExist
	}
	manifest, err := s.readVersion(ctx, ref, current.pointer())
	if err != nil {
		return Meta{}, err
	}
	cleartextKeyset, err := s.unwrapManifestKey(ctx, ref, current.pointer(), manifest)
	if err != nil {
		return Meta{}, err
	}
	wipe(cleartextKeyset)
	return manifest.Meta, nil
}

func (s *EnvelopeStore) Delete(ctx context.Context, ref Ref) error {
	return s.DeleteGuarded(ctx, ref, nil)
}

func (s *EnvelopeStore) DeleteGuarded(ctx context.Context, ref Ref, guard CommitGuard) error {
	if err := s.validate(ref); err != nil {
		return err
	}
	current, attrs, exists, err := s.readCurrent(ctx, ref)
	if err != nil || !exists {
		return err
	}
	currentVersion, err := s.readVersion(ctx, ref, current.pointer())
	if err != nil {
		return err
	}
	currentKeyset, err := s.unwrapManifestKey(ctx, ref, current.pointer(), currentVersion)
	if err != nil {
		return err
	}
	wipe(currentKeyset)
	var previousVersion *versionManifest
	if current.Previous != nil {
		manifest, err := s.readVersion(ctx, ref, *current.Previous)
		if err != nil {
			return err
		}
		previousKeyset, err := s.unwrapManifestKey(ctx, ref, *current.Previous, manifest)
		if err != nil {
			return err
		}
		wipe(previousKeyset)
		previousVersion = &manifest
	}
	if guard != nil {
		if err := guard(ctx); err != nil {
			return fmt.Errorf("revalidate snapshot delete fence: %w", err)
		}
	}
	if err := s.Objects.DeleteCurrent(ctx, s.currentObject(ref), attrs.Generation); err != nil {
		if errors.Is(err, ErrObjectPrecondition) {
			return fmt.Errorf("%w: %v", ErrConcurrentPublication, err)
		}
		return err
	}
	cleanupCtx, cancelCleanup := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancelCleanup()
	cleanupErr := s.deleteVersionManifest(cleanupCtx, ref, current.pointer(), currentVersion)
	if current.Previous != nil && previousVersion != nil {
		cleanupErr = errors.Join(
			cleanupErr,
			s.deleteVersionManifest(
				cleanupCtx,
				ref,
				*current.Previous,
				*previousVersion,
			),
		)
	}
	if cleanupErr != nil {
		return fmt.Errorf("snapshot pointer deleted but encrypted version cleanup failed: %w", cleanupErr)
	}
	return nil
}

func (s *EnvelopeStore) Health(ctx context.Context) error {
	if s == nil || s.Objects == nil || s.Wrapper == nil {
		return fmt.Errorf("snapshot envelope store is not configured")
	}
	return s.Objects.Health(ctx)
}

func (s *EnvelopeStore) Close() error {
	var first error
	if s != nil && s.Objects != nil {
		first = s.Objects.Close()
	}
	if s != nil && s.Wrapper != nil {
		if err := s.Wrapper.Close(); first == nil {
			first = err
		}
	}
	return first
}

func (s *EnvelopeStore) validate(ref Ref) error {
	if s == nil || s.Objects == nil || s.Wrapper == nil {
		return fmt.Errorf("snapshot envelope store is not configured")
	}
	if strings.TrimSpace(s.ExpectedLayout) == "" {
		return fmt.Errorf("expected snapshot layout is required")
	}
	return ref.Validate()
}

func (s *EnvelopeStore) readCurrent(ctx context.Context, ref Ref) (currentManifest, ObjectAttrs, bool, error) {
	var current currentManifest
	attrs, err := s.readJSON(ctx, s.currentObject(ref), 0, &current)
	if errors.Is(err, ErrObjectNotFound) {
		return current, ObjectAttrs{}, false, nil
	}
	if err != nil {
		return current, ObjectAttrs{}, false, fmt.Errorf("read current snapshot: %w", err)
	}
	if current.SchemaVersion != envelopeSchemaVersion || current.Ref != ref ||
		!validSnapshotID(current.SnapshotID) || current.ManifestGeneration <= 0 ||
		attrs.Generation <= 0 {
		return current, ObjectAttrs{}, false, fmt.Errorf("invalid current snapshot manifest")
	}
	if current.Previous != nil {
		if err := current.Previous.validate(); err != nil ||
			current.Previous.SnapshotID == current.SnapshotID {
			return current, ObjectAttrs{}, false, fmt.Errorf("invalid previous snapshot manifest pointer")
		}
	}
	return current, attrs, true, nil
}

func (s *EnvelopeStore) readVersion(ctx context.Context, ref Ref, pointer versionPointer) (versionManifest, error) {
	var manifest versionManifest
	attrs, err := s.readJSON(
		ctx, s.versionObject(ref, pointer.SnapshotID, "manifest.json"),
		pointer.ManifestGeneration, &manifest,
	)
	if err != nil {
		return manifest, fmt.Errorf("read immutable snapshot manifest: %w", err)
	}
	if manifest.SchemaVersion != envelopeSchemaVersion || manifest.Ref != ref ||
		manifest.SnapshotID != pointer.SnapshotID || manifest.PackageGeneration <= 0 ||
		manifest.PackageSize <= 0 || manifest.PackageSize > MaxRequestBytes ||
		len(manifest.WrappedKeyset) == 0 || len(manifest.WrappedKeyset) > 16<<10 ||
		manifest.CreatedAt.IsZero() || attrs.Generation != pointer.ManifestGeneration {
		return manifest, fmt.Errorf("invalid immutable snapshot manifest")
	}
	if err := ValidateMeta(ref, manifest.Meta, s.ExpectedLayout); err != nil {
		return manifest, fmt.Errorf("invalid immutable snapshot metadata: %w", err)
	}
	_, digest, err := digestMeta(manifest.Meta)
	if err != nil || digest != manifest.MetaSHA256 {
		return manifest, fmt.Errorf("invalid immutable snapshot metadata digest")
	}
	return manifest, nil
}

func (s *EnvelopeStore) unwrapManifestKey(
	ctx context.Context,
	ref Ref,
	pointer versionPointer,
	manifest versionManifest,
) ([]byte, error) {
	metaDigest, _, err := digestMeta(manifest.Meta)
	if err != nil {
		return nil, err
	}
	cleartext, err := s.Wrapper.Unwrap(
		ctx,
		manifest.WrappedKeyset,
		envelopeAAD(ref, pointer.SnapshotID, metaDigest),
	)
	if err != nil {
		return nil, fmt.Errorf("authenticate pinned snapshot manifest metadata: %w", err)
	}
	return cleartext, nil
}

func (s *EnvelopeStore) deleteVersion(ctx context.Context, ref Ref, pointer versionPointer) error {
	manifest, err := s.readVersion(ctx, ref, pointer)
	if errors.Is(err, ErrObjectNotFound) {
		return nil
	}
	if err != nil {
		return err
	}
	cleartextKeyset, err := s.unwrapManifestKey(ctx, ref, pointer, manifest)
	if err != nil {
		return err
	}
	wipe(cleartextKeyset)
	return s.deleteVersionManifest(ctx, ref, pointer, manifest)
}

func (s *EnvelopeStore) deleteVersionManifest(
	ctx context.Context,
	ref Ref,
	pointer versionPointer,
	manifest versionManifest,
) error {
	packageErr := s.Objects.Delete(
		ctx,
		s.versionObject(ref, pointer.SnapshotID, "package.tink"),
		manifest.PackageGeneration,
	)
	if packageErr != nil {
		packageErr = fmt.Errorf(
			"delete encrypted snapshot package %s: %w",
			pointer.SnapshotID,
			packageErr,
		)
	}
	manifestErr := s.Objects.Delete(
		ctx,
		s.versionObject(ref, pointer.SnapshotID, "manifest.json"),
		pointer.ManifestGeneration,
	)
	if manifestErr != nil {
		manifestErr = fmt.Errorf(
			"delete encrypted snapshot manifest %s: %w",
			pointer.SnapshotID,
			manifestErr,
		)
	}
	return errors.Join(packageErr, manifestErr)
}

func (s *EnvelopeStore) writeJSON(ctx context.Context, name string, condition ObjectCondition, value any) (ObjectAttrs, error) {
	body, err := marshalManifest(value)
	if err != nil {
		return ObjectAttrs{}, err
	}
	return s.writeManifestBytes(ctx, name, condition, body)
}

func marshalManifest(value any) ([]byte, error) {
	body, err := json.Marshal(value)
	if err != nil {
		return nil, err
	}
	if len(body) > maxManifestBytes {
		return nil, fmt.Errorf("snapshot manifest is too large")
	}
	return append(body, '\n'), nil
}

func (s *EnvelopeStore) writeManifestBytes(
	ctx context.Context,
	name string,
	condition ObjectCondition,
	body []byte,
) (ObjectAttrs, error) {
	return s.Objects.Write(ctx, name, condition, func(out io.Writer) error {
		_, err := out.Write(body)
		return err
	})
}

func (s *EnvelopeStore) readJSON(ctx context.Context, name string, generation int64, value any) (ObjectAttrs, error) {
	reader, attrs, err := s.Objects.Read(ctx, name, generation)
	if err != nil {
		return ObjectAttrs{}, err
	}
	defer reader.Close()
	if attrs.Size <= 0 || attrs.Size > maxManifestBytes {
		return ObjectAttrs{}, fmt.Errorf("snapshot manifest has invalid size")
	}
	decoder := json.NewDecoder(io.LimitReader(reader, maxManifestBytes+1))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(value); err != nil {
		return ObjectAttrs{}, err
	}
	if err := decoder.Decode(&struct{}{}); err != io.EOF {
		return ObjectAttrs{}, fmt.Errorf("snapshot manifest must contain one JSON object")
	}
	return attrs, nil
}

func (s *EnvelopeStore) currentObject(ref Ref) string {
	return path.Join(s.Prefix, ref.Key(), "current.json")
}

func (s *EnvelopeStore) versionObject(ref Ref, snapshotID, name string) string {
	return path.Join(s.Prefix, ref.Key(), "versions", snapshotID, name)
}

func (c currentManifest) pointer() versionPointer {
	return versionPointer{
		SnapshotID: c.SnapshotID, ManifestGeneration: c.ManifestGeneration,
	}
}

func (p versionPointer) validate() error {
	if !validSnapshotID(p.SnapshotID) || p.ManifestGeneration <= 0 {
		return fmt.Errorf("invalid snapshot version pointer")
	}
	return nil
}

func (s *EnvelopeStore) snapshotID() (string, error) {
	if s.NewSnapshotID != nil {
		id, err := s.NewSnapshotID()
		if err != nil {
			return "", err
		}
		if !validSnapshotID(id) {
			return "", fmt.Errorf("invalid generated snapshot ID")
		}
		return id, nil
	}
	var raw [16]byte
	if _, err := rand.Read(raw[:]); err != nil {
		return "", err
	}
	return hex.EncodeToString(raw[:]), nil
}

func (s *EnvelopeStore) now() time.Time {
	if s.Now != nil {
		return s.Now().UTC()
	}
	return time.Now().UTC()
}

func validSnapshotID(id string) bool {
	return len(id) == 32 && strings.Trim(id, "0123456789abcdef") == ""
}

func digestMeta(meta Meta) ([]byte, string, error) {
	body, err := json.Marshal(meta)
	if err != nil {
		return nil, "", fmt.Errorf("canonicalize snapshot metadata: %w", err)
	}
	if len(body) == 0 || int64(len(body)) > MaxMetadataBytes {
		return nil, "", fmt.Errorf("canonical snapshot metadata has invalid size")
	}
	digest := sha256.Sum256(body)
	return digest[:], hex.EncodeToString(digest[:]), nil
}

func envelopeAAD(ref Ref, snapshotID string, metaDigest []byte) []byte {
	aad := []byte("sshcloud-snapshot-keyset-v2\x00" + ref.User + "\x00" + ref.App + "\x00" + ref.Gen + "\x00" + snapshotID + "\x00")
	return append(aad, metaDigest...)
}

func packageAAD(keyAAD []byte) []byte {
	return append(append([]byte(nil), keyAAD...), []byte("\x00package")...)
}

func wipe(data []byte) {
	for i := range data {
		data[i] = 0
	}
}

var _ Store = (*EnvelopeStore)(nil)
var _ GuardedStore = (*EnvelopeStore)(nil)
