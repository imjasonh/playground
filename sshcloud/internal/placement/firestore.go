package placement

import (
	"context"
	"fmt"
	"strings"
	"time"

	"cloud.google.com/go/firestore"
	"google.golang.org/api/iterator"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

const colPlacement = "placement"

// Firestore maps user/app → host ID in Cloud Firestore (or the emulator).
type Firestore struct {
	client *firestore.Client
}

type placementDoc struct {
	User           string `firestore:"user"`
	App            string `firestore:"app"`
	HostID         string `firestore:"host_id"`
	Revision       int64  `firestore:"revision"`
	LeaseOwner     string `firestore:"lease_owner"`
	LeaseUntilUnix int64  `firestore:"lease_until_unix"`
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
	ref := f.ref(user, app)
	return f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		d, _, err := readPlacementTx(tx, ref)
		if err != nil {
			return err
		}
		r := recordFromDoc(d)
		if leaseActive(r, time.Now()) {
			return ErrLeaseHeld{User: user, App: app, Owner: r.LeaseOwner, Until: time.Unix(0, r.LeaseUntilUnix)}
		}
		d.User, d.App, d.HostID = user, app, hostID
		d.Revision++
		d.LeaseOwner, d.LeaseUntilUnix = "", 0
		return tx.Set(ref, d)
	})
}

func (f *Firestore) Delete(ctx context.Context, user, app string) error {
	ref := f.ref(user, app)
	return f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		d, ok, err := readPlacementTx(tx, ref)
		if err != nil || !ok {
			return err
		}
		r := recordFromDoc(d)
		if leaseActive(r, time.Now()) {
			return ErrLeaseHeld{User: user, App: app, Owner: r.LeaseOwner, Until: time.Unix(0, r.LeaseUntilUnix)}
		}
		return tx.Delete(ref)
	})
}

func (f *Firestore) GetRecord(ctx context.Context, user, app string) (Record, bool, error) {
	snap, err := f.ref(user, app).Get(ctx)
	if err != nil {
		if status.Code(err) == codes.NotFound {
			return Record{}, false, nil
		}
		return Record{}, false, err
	}
	var d placementDoc
	if err := snap.DataTo(&d); err != nil {
		return Record{}, false, err
	}
	return recordFromDoc(d), true, nil
}

func (f *Firestore) ListRecords(ctx context.Context) ([]Record, error) {
	iter := f.client.Collection(colPlacement).Documents(ctx)
	defer iter.Stop()
	var out []Record
	for {
		snap, err := iter.Next()
		if err == iterator.Done {
			return out, nil
		}
		if err != nil {
			return nil, err
		}
		var d placementDoc
		if err := snap.DataTo(&d); err != nil {
			return nil, err
		}
		out = append(out, recordFromDoc(d))
	}
}

func (f *Firestore) Acquire(ctx context.Context, user, app, owner string, ttl time.Duration, now time.Time) (Lease, error) {
	if user == "" || app == "" || owner == "" || ttl <= 0 {
		return Lease{}, fmt.Errorf("user, app, owner, and positive ttl required")
	}
	ref := f.ref(user, app)
	var lease Lease
	err := f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		d, _, err := readPlacementTx(tx, ref)
		if err != nil {
			return err
		}
		r := recordFromDoc(d)
		if leaseActive(r, now) && r.LeaseOwner != owner {
			return ErrLeaseHeld{User: user, App: app, Owner: r.LeaseOwner, Until: time.Unix(0, r.LeaseUntilUnix)}
		}
		d.User, d.App = user, app
		d.Revision++
		d.LeaseOwner = owner
		d.LeaseUntilUnix = now.Add(ttl).UnixNano()
		if err := tx.Set(ref, d); err != nil {
			return err
		}
		lease = leaseFromRecord(recordFromDoc(d))
		return nil
	})
	return lease, err
}

func (f *Firestore) Renew(ctx context.Context, lease Lease, ttl time.Duration, now time.Time) (Lease, error) {
	if ttl <= 0 {
		return Lease{}, fmt.Errorf("positive ttl required")
	}
	ref := f.ref(lease.User, lease.App)
	var renewed Lease
	err := f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		d, ok, err := readPlacementTx(tx, ref)
		if err != nil {
			return err
		}
		r := recordFromDoc(d)
		if !ok || !leaseMatches(r, lease) || !leaseActive(r, now) {
			return ErrLeaseLost{User: lease.User, App: lease.App}
		}
		d.LeaseUntilUnix = now.Add(ttl).UnixNano()
		if err := tx.Set(ref, d); err != nil {
			return err
		}
		renewed = leaseFromRecord(recordFromDoc(d))
		return nil
	})
	return renewed, err
}

func (f *Firestore) Commit(ctx context.Context, lease Lease, hostID string, now time.Time) error {
	if hostID == "" {
		return fmt.Errorf("hostID required")
	}
	ref := f.ref(lease.User, lease.App)
	return f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		d, ok, err := readPlacementTx(tx, ref)
		if err != nil {
			return err
		}
		r := recordFromDoc(d)
		if !ok || !leaseMatches(r, lease) || !leaseActive(r, now) {
			return ErrLeaseLost{User: lease.User, App: lease.App}
		}
		d.HostID = hostID
		d.Revision++
		d.LeaseOwner, d.LeaseUntilUnix = "", 0
		return tx.Set(ref, d)
	})
}

func (f *Firestore) Release(ctx context.Context, lease Lease) error {
	ref := f.ref(lease.User, lease.App)
	return f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		d, ok, err := readPlacementTx(tx, ref)
		if err != nil || !ok {
			return err
		}
		r := recordFromDoc(d)
		if !leaseMatches(r, lease) {
			return ErrLeaseLost{User: lease.User, App: lease.App}
		}
		d.Revision++
		d.LeaseOwner, d.LeaseUntilUnix = "", 0
		return tx.Set(ref, d)
	})
}

func readPlacementTx(tx *firestore.Transaction, ref *firestore.DocumentRef) (placementDoc, bool, error) {
	snap, err := tx.Get(ref)
	if err != nil {
		if status.Code(err) == codes.NotFound {
			return placementDoc{}, false, nil
		}
		return placementDoc{}, false, err
	}
	var d placementDoc
	if err := snap.DataTo(&d); err != nil {
		return placementDoc{}, false, err
	}
	return d, snap.Exists(), nil
}

func recordFromDoc(d placementDoc) Record {
	return Record{
		User: d.User, App: d.App, HostID: d.HostID, Revision: d.Revision,
		LeaseOwner: d.LeaseOwner, LeaseUntilUnix: d.LeaseUntilUnix,
	}
}
