package store

import (
	"context"
	"fmt"
	"strings"

	"cloud.google.com/go/firestore"
	"google.golang.org/api/iterator"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

// Firestore collections (Native mode).
//
//	keys/{fingerprint}              → { user_id }
//	users/{userID}                  → { id }
//	users/{userID}/apps/{appName}   → app fields
//
// Firestore is a Store backed by Cloud Firestore (or the emulator).
type Firestore struct {
	client   *firestore.Client
	colKeys  string
	colUsers string
	colApps  string
}

// NewFirestore connects to the given GCP project. When FIRESTORE_EMULATOR_HOST
// is set, the client talks to the emulator instead of production.
func NewFirestore(ctx context.Context, projectID string) (*Firestore, error) {
	return NewFirestoreWithPrefix(ctx, projectID, "sshcloud")
}

func NewFirestoreWithPrefix(ctx context.Context, projectID, prefix string) (*Firestore, error) {
	if projectID == "" {
		return nil, fmt.Errorf("firestore project ID required")
	}
	prefix = strings.TrimSpace(prefix)
	if prefix == "" {
		return nil, fmt.Errorf("firestore collection prefix required")
	}
	client, err := firestore.NewClient(ctx, projectID)
	if err != nil {
		return nil, err
	}
	return &Firestore{
		client: client, colKeys: prefix + "_keys",
		colUsers: prefix + "_users", colApps: prefix + "_apps",
	}, nil
}

// Close releases the Firestore client.
func (f *Firestore) Close() error {
	if f == nil || f.client == nil {
		return nil
	}
	return f.client.Close()
}

type keyDoc struct {
	UserID string `firestore:"user_id"`
}

type userDoc struct {
	ID string `firestore:"id"`
}

type appDoc struct {
	Owner           string `firestore:"owner"`
	Name            string `firestore:"name"`
	Image           string `firestore:"image"`
	PreviousImage   string `firestore:"previous_image"`
	Tier            string `firestore:"tier"`
	SessionStrategy string `firestore:"session_strategy"`
	ActiveGen       string `firestore:"active_gen"`
	DrainingGen     string `firestore:"draining_gen"`
	DrainUntilUnix  int64  `firestore:"drain_until_unix"`
}

func keyDocID(fingerprint string) string {
	// Firestore doc IDs cannot contain '/'; fingerprints use 'SHA256:…'.
	return strings.ReplaceAll(fingerprint, "/", "_")
}

func (f *Firestore) keyRef(fingerprint string) *firestore.DocumentRef {
	return f.client.Collection(f.colKeys).Doc(keyDocID(fingerprint))
}

func (f *Firestore) userRef(userID string) *firestore.DocumentRef {
	return f.client.Collection(f.colUsers).Doc(userID)
}

func (f *Firestore) appRef(userID, app string) *firestore.DocumentRef {
	return f.userRef(userID).Collection(f.colApps).Doc(app)
}

func (f *Firestore) LookupUserByKey(ctx context.Context, keyFingerprint string) (*User, error) {
	snap, err := f.keyRef(keyFingerprint).Get(ctx)
	if err != nil {
		if status.Code(err) == codes.NotFound {
			return nil, nil
		}
		return nil, err
	}
	var kd keyDoc
	if err := snap.DataTo(&kd); err != nil {
		return nil, err
	}
	if kd.UserID == "" {
		return nil, nil
	}
	return &User{ID: kd.UserID}, nil
}

func (f *Firestore) CreateUser(ctx context.Context, id, keyFingerprint string) error {
	if id == "" || keyFingerprint == "" {
		return fmt.Errorf("user id and key fingerprint required")
	}
	userRef := f.userRef(id)
	keyRef := f.keyRef(keyFingerprint)
	return f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		if err := requireMissing(tx, userRef, fmt.Sprintf("user %q already exists", id)); err != nil {
			return err
		}
		if err := requireMissing(tx, keyRef, "key already registered"); err != nil {
			return err
		}
		if err := tx.Set(userRef, userDoc{ID: id}); err != nil {
			return err
		}
		return tx.Set(keyRef, keyDoc{UserID: id})
	})
}

func (f *Firestore) AddKey(ctx context.Context, userID, keyFingerprint string) error {
	if userID == "" || keyFingerprint == "" {
		return fmt.Errorf("user id and key fingerprint required")
	}
	userRef := f.userRef(userID)
	keyRef := f.keyRef(keyFingerprint)
	return f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		if err := requireExists(tx, userRef, fmt.Sprintf("unknown user %q", userID)); err != nil {
			return err
		}
		if err := requireMissing(tx, keyRef, "key already registered"); err != nil {
			return err
		}
		return tx.Set(keyRef, keyDoc{UserID: userID})
	})
}

func (f *Firestore) HasApp(ctx context.Context, userID, app string) (bool, error) {
	snap, err := f.appRef(userID, app).Get(ctx)
	if err != nil {
		if status.Code(err) == codes.NotFound {
			return false, nil
		}
		return false, err
	}
	return snap.Exists(), nil
}

func (f *Firestore) GetApp(ctx context.Context, userID, app string) (*App, error) {
	snap, err := f.appRef(userID, app).Get(ctx)
	if err != nil {
		if status.Code(err) == codes.NotFound {
			return nil, nil
		}
		return nil, err
	}
	a, err := appFromSnap(snap)
	if err != nil {
		return nil, err
	}
	return &a, nil
}

func (f *Firestore) UpsertApp(ctx context.Context, app App) error {
	if app.Owner == "" || app.Name == "" {
		return fmt.Errorf("app owner and name required")
	}
	if app.Tier == "" {
		app.Tier = "tiny"
	}
	if app.SessionStrategy == "" {
		app.SessionStrategy = StrategyDrain
	}

	userRef := f.userRef(app.Owner)
	appRef := f.appRef(app.Owner, app.Name)
	return f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		if err := requireExists(tx, userRef, fmt.Sprintf("unknown user %q", app.Owner)); err != nil {
			return err
		}
		return tx.Set(appRef, appToDoc(app))
	})
}

func (f *Firestore) ListApps(ctx context.Context, userID string) ([]App, error) {
	iter := f.userRef(userID).Collection(f.colApps).Documents(ctx)
	defer iter.Stop()
	out := []App{}
	for {
		snap, err := iter.Next()
		if err == iterator.Done {
			break
		}
		if err != nil {
			return nil, err
		}
		a, err := appFromSnap(snap)
		if err != nil {
			return nil, err
		}
		out = append(out, a)
	}
	return out, nil
}

func (f *Firestore) ListAllApps(ctx context.Context) ([]App, error) {
	iter := f.client.CollectionGroup(f.colApps).Documents(ctx)
	defer iter.Stop()
	var out []App
	for {
		snap, err := iter.Next()
		if err == iterator.Done {
			return out, nil
		}
		if err != nil {
			return nil, err
		}
		app, err := appFromSnap(snap)
		if err != nil {
			return nil, err
		}
		out = append(out, app)
	}
}

func appToDoc(a App) appDoc {
	return appDoc{
		Owner:           a.Owner,
		Name:            a.Name,
		Image:           a.Image,
		PreviousImage:   a.PreviousImage,
		Tier:            a.Tier,
		SessionStrategy: a.SessionStrategy,
		ActiveGen:       a.ActiveGen,
		DrainingGen:     a.DrainingGen,
		DrainUntilUnix:  a.DrainUntilUnix,
	}
}

func appFromSnap(snap *firestore.DocumentSnapshot) (App, error) {
	var d appDoc
	if err := snap.DataTo(&d); err != nil {
		return App{}, err
	}
	name := d.Name
	if name == "" {
		name = snap.Ref.ID
	}
	owner := d.Owner
	if owner == "" && snap.Ref.Parent != nil && snap.Ref.Parent.Parent != nil {
		owner = snap.Ref.Parent.Parent.ID
	}
	return App{
		Owner:           owner,
		Name:            name,
		Image:           d.Image,
		PreviousImage:   d.PreviousImage,
		Tier:            d.Tier,
		SessionStrategy: d.SessionStrategy,
		ActiveGen:       d.ActiveGen,
		DrainingGen:     d.DrainingGen,
		DrainUntilUnix:  d.DrainUntilUnix,
	}, nil
}

func requireMissing(tx *firestore.Transaction, ref *firestore.DocumentRef, existsErr string) error {
	snap, err := tx.Get(ref)
	if err != nil {
		if status.Code(err) == codes.NotFound {
			return nil
		}
		return err
	}
	if snap.Exists() {
		return fmt.Errorf("%s", existsErr)
	}
	return nil
}

func requireExists(tx *firestore.Transaction, ref *firestore.DocumentRef, missingErr string) error {
	snap, err := tx.Get(ref)
	if err != nil {
		if status.Code(err) == codes.NotFound {
			return fmt.Errorf("%s", missingErr)
		}
		return err
	}
	if !snap.Exists() {
		return fmt.Errorf("%s", missingErr)
	}
	return nil
}
