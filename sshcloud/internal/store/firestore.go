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
const (
	colKeys  = "keys"
	colUsers = "users"
	colApps  = "apps"
)

// Firestore is a Store backed by Cloud Firestore (or the emulator).
type Firestore struct {
	client *firestore.Client
}

// NewFirestore connects to the given GCP project. When FIRESTORE_EMULATOR_HOST
// is set, the client talks to the emulator instead of production.
func NewFirestore(ctx context.Context, projectID string) (*Firestore, error) {
	if projectID == "" {
		return nil, fmt.Errorf("firestore project ID required")
	}
	client, err := firestore.NewClient(ctx, projectID)
	if err != nil {
		return nil, err
	}
	return &Firestore{client: client}, nil
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
	Demo            bool   `firestore:"demo"`
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
	return f.client.Collection(colKeys).Doc(keyDocID(fingerprint))
}

func (f *Firestore) userRef(userID string) *firestore.DocumentRef {
	return f.client.Collection(colUsers).Doc(userID)
}

func (f *Firestore) appRef(userID, app string) *firestore.DocumentRef {
	return f.userRef(userID).Collection(colApps).Doc(app)
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
	if IsPlatformDemo(app.Name) {
		return fmt.Errorf("%q is a platform demo; deploy a different name", app.Name)
	}
	if app.Tier == "" {
		app.Tier = "tiny"
	}
	if app.SessionStrategy == "" {
		app.SessionStrategy = StrategyDrain
	}
	app.Demo = false

	userRef := f.userRef(app.Owner)
	appRef := f.appRef(app.Owner, app.Name)
	return f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		if err := requireExists(tx, userRef, fmt.Sprintf("unknown user %q", app.Owner)); err != nil {
			return err
		}
		snap, err := tx.Get(appRef)
		if err != nil && status.Code(err) != codes.NotFound {
			return err
		}
		if err == nil && snap.Exists() {
			var existing appDoc
			if err := snap.DataTo(&existing); err != nil {
				return err
			}
			if existing.Demo {
				return fmt.Errorf("%q is a platform demo; deploy a different name", app.Name)
			}
		}
		return tx.Set(appRef, appToDoc(app))
	})
}

func (f *Firestore) EnsureDemoApp(ctx context.Context, userID, app string) error {
	if userID == "" || app == "" {
		return fmt.Errorf("user and app required")
	}
	userRef := f.userRef(userID)
	appRef := f.appRef(userID, app)
	return f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		if err := requireExists(tx, userRef, fmt.Sprintf("unknown user %q", userID)); err != nil {
			return err
		}
		snap, err := tx.Get(appRef)
		if err != nil && status.Code(err) != codes.NotFound {
			return err
		}
		if err == nil && snap.Exists() {
			return nil
		}
		return tx.Set(appRef, appToDoc(App{
			Owner: userID,
			Name:  app,
			Tier:  "tiny",
			Demo:  true,
		}))
	})
}

func (f *Firestore) ListApps(ctx context.Context, userID string) ([]App, error) {
	iter := f.userRef(userID).Collection(colApps).Documents(ctx)
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

func appToDoc(a App) appDoc {
	return appDoc{
		Owner:           a.Owner,
		Name:            a.Name,
		Image:           a.Image,
		PreviousImage:   a.PreviousImage,
		Tier:            a.Tier,
		Demo:            a.Demo,
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
		Demo:            d.Demo,
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
