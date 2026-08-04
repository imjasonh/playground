package placement

import (
	"context"
	"fmt"
	"strings"

	"cloud.google.com/go/firestore"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

const colPlacement = "placement"

// Firestore maps user/app → host ID in Cloud Firestore (or the emulator).
type Firestore struct {
	client *firestore.Client
}

type placementDoc struct {
	User   string `firestore:"user"`
	App    string `firestore:"app"`
	HostID string `firestore:"host_id"`
}

// NewFirestore connects to the given GCP project.
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

func placementDocID(user, app string) string {
	// Doc IDs cannot contain '/'.
	return strings.ReplaceAll(user, "/", "_") + "__" + strings.ReplaceAll(app, "/", "_")
}

func (f *Firestore) ref(user, app string) *firestore.DocumentRef {
	return f.client.Collection(colPlacement).Doc(placementDocID(user, app))
}

func (f *Firestore) Get(ctx context.Context, user, app string) (string, bool, error) {
	snap, err := f.ref(user, app).Get(ctx)
	if err != nil {
		if status.Code(err) == codes.NotFound {
			return "", false, nil
		}
		return "", false, err
	}
	var d placementDoc
	if err := snap.DataTo(&d); err != nil {
		return "", false, err
	}
	if d.HostID == "" {
		return "", false, nil
	}
	return d.HostID, true, nil
}

func (f *Firestore) Set(ctx context.Context, user, app, hostID string) error {
	if user == "" || app == "" || hostID == "" {
		return fmt.Errorf("user, app, and hostID required")
	}
	_, err := f.ref(user, app).Set(ctx, placementDoc{User: user, App: app, HostID: hostID})
	return err
}

func (f *Firestore) Delete(ctx context.Context, user, app string) error {
	_, err := f.ref(user, app).Delete(ctx)
	if err != nil && status.Code(err) == codes.NotFound {
		return nil
	}
	return err
}
