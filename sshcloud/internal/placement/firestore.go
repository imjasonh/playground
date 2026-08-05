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

// Firestore maps user/app → host ID in Cloud Firestore (or the emulator).
type Firestore struct {
	client       *firestore.Client
	colPlacement string
}

type placementDoc struct {
	User           string       `firestore:"user"`
	App            string       `firestore:"app"`
	HostID         string       `firestore:"host_id"`
	HostInstanceID string       `firestore:"host_instance_id"`
	Revision       int64        `firestore:"revision"`
	LeaseOwner     string       `firestore:"lease_owner"`
	LeaseUntilUnix int64        `firestore:"lease_until_unix"`
	Operation      Operation    `firestore:"operation"`
	Generations    []Generation `firestore:"generations"`
}

// NewFirestore connects to the given GCP project.
func NewFirestore(ctx context.Context, projectID string) (*Firestore, error) {
	return NewFirestoreWithPrefix(ctx, projectID, "sshcloud")
}

func NewFirestoreWithPrefix(ctx context.Context, projectID, prefix string) (*Firestore, error) {
	return NewFirestoreDatabase(ctx, projectID, "(default)", prefix)
}

func NewFirestoreDatabase(ctx context.Context, projectID, database, prefix string) (*Firestore, error) {
	if projectID == "" {
		return nil, fmt.Errorf("firestore project ID required")
	}
	if strings.TrimSpace(database) == "" {
		return nil, fmt.Errorf("firestore database required")
	}
	prefix = strings.TrimSpace(prefix)
	if prefix == "" {
		return nil, fmt.Errorf("firestore collection prefix required")
	}
	client, err := firestore.NewClientWithDatabase(ctx, projectID, database)
	if err != nil {
		return nil, err
	}
	return &Firestore{client: client, colPlacement: prefix + "_placement"}, nil
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
	return f.client.Collection(f.colPlacement).Doc(placementDocID(user, app))
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

func (f *Firestore) SetIdentity(ctx context.Context, user, app, hostID, hostInstanceID string) error {
	if hostInstanceID == "" {
		return fmt.Errorf("host instance ID required")
	}
	return f.setIdentity(ctx, user, app, hostID, hostInstanceID)
}

func (f *Firestore) setIdentity(ctx context.Context, user, app, hostID, hostInstanceID string) error {
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
		d.User, d.App, d.HostID, d.HostInstanceID = user, app, hostID, hostInstanceID
		d.Revision++
		d.LeaseOwner, d.LeaseUntilUnix = "", 0
		d.Operation = Operation{}
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
	iter := f.client.Collection(f.colPlacement).Documents(ctx)
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

func (f *Firestore) Acquire(ctx context.Context, user, app, owner string, ttl time.Duration, _ time.Time) (Lease, error) {
	if user == "" || app == "" || owner == "" || ttl <= 0 {
		return Lease{}, fmt.Errorf("user, app, owner, and positive ttl required")
	}
	ref := f.ref(user, app)
	var lease Lease
	err := f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		attemptNow := time.Now()
		d, _, err := readPlacementTx(tx, ref)
		if err != nil {
			return err
		}
		r := recordFromDoc(d)
		if r.Operation.Kind != "" {
			return ErrRecoveryRequired{User: user, App: app, Operation: r.Operation.ID}
		}
		if leaseActive(r, attemptNow) && r.LeaseOwner != owner {
			return ErrLeaseHeld{User: user, App: app, Owner: r.LeaseOwner, Until: time.Unix(0, r.LeaseUntilUnix)}
		}
		d.User, d.App = user, app
		d.Revision++
		d.LeaseOwner = owner
		d.LeaseUntilUnix = attemptNow.Add(ttl).UnixNano()
		if err := tx.Set(ref, d); err != nil {
			return err
		}
		lease = leaseFromRecord(recordFromDoc(d))
		return nil
	})
	return lease, err
}

func (f *Firestore) AcquireRecovery(ctx context.Context, expected Record, owner string, ttl time.Duration, _ time.Time) (Lease, error) {
	if owner == "" || ttl <= 0 || expected.Operation.Kind == "" {
		return Lease{}, fmt.Errorf("owner, positive ttl, and operation required")
	}
	ref := f.ref(expected.User, expected.App)
	var lease Lease
	err := f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		attemptNow := time.Now()
		d, ok, err := readPlacementTx(tx, ref)
		if err != nil {
			return err
		}
		r := recordFromDoc(d)
		if !ok || r.Revision != expected.Revision || r.Operation.ID != expected.Operation.ID ||
			r.Operation.Kind != expected.Operation.Kind || r.Operation.Sequence != expected.Operation.Sequence {
			return ErrLeaseLost{User: expected.User, App: expected.App}
		}
		if leaseActive(r, attemptNow) {
			return ErrLeaseHeld{User: r.User, App: r.App, Owner: r.LeaseOwner, Until: time.Unix(0, r.LeaseUntilUnix)}
		}
		d.Revision++
		d.LeaseOwner = owner
		d.LeaseUntilUnix = attemptNow.Add(ttl).UnixNano()
		if err := tx.Set(ref, d); err != nil {
			return err
		}
		lease = leaseFromRecord(recordFromDoc(d))
		return nil
	})
	return lease, err
}

func (f *Firestore) Renew(ctx context.Context, lease Lease, ttl time.Duration, _ time.Time) (Lease, error) {
	if ttl <= 0 {
		return Lease{}, fmt.Errorf("positive ttl required")
	}
	ref := f.ref(lease.User, lease.App)
	var renewed Lease
	err := f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		attemptNow := time.Now()
		d, ok, err := readPlacementTx(tx, ref)
		if err != nil {
			return err
		}
		r := recordFromDoc(d)
		if !ok || !leaseMatches(r, lease) || !leaseActive(r, attemptNow) {
			return ErrLeaseLost{User: lease.User, App: lease.App}
		}
		d.LeaseUntilUnix = attemptNow.Add(ttl).UnixNano()
		if err := tx.Set(ref, d); err != nil {
			return err
		}
		renewed = leaseFromRecord(recordFromDoc(d))
		return nil
	})
	return renewed, err
}

func (f *Firestore) Mark(ctx context.Context, lease Lease, operation Operation) error {
	ref := f.ref(lease.User, lease.App)
	return f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		d, ok, err := readPlacementTx(tx, ref)
		if err != nil {
			return err
		}
		r := recordFromDoc(d)
		if !ok || !leaseMatches(r, lease) {
			return ErrLeaseLost{User: lease.User, App: lease.App}
		}
		operation.Sequence = r.Operation.Sequence + 1
		d.Operation = cloneOperation(operation)
		return tx.Set(ref, d)
	})
}

func (f *Firestore) CommitStateIdentity(ctx context.Context, lease Lease, hostID, hostInstanceID string, generations []Generation, _ time.Time) error {
	return f.commitStateIdentity(ctx, lease, hostID, hostInstanceID, generations)
}

func (f *Firestore) commitStateIdentity(ctx context.Context, lease Lease, hostID, hostInstanceID string, generations []Generation) error {
	if hostID == "" || hostInstanceID == "" {
		return fmt.Errorf("host ID and host instance ID required")
	}
	ref := f.ref(lease.User, lease.App)
	return f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		attemptNow := time.Now()
		d, ok, err := readPlacementTx(tx, ref)
		if err != nil {
			return err
		}
		r := recordFromDoc(d)
		if !ok || !leaseMatches(r, lease) || !leaseActive(r, attemptNow) {
			return ErrLeaseLost{User: lease.User, App: lease.App}
		}
		d.HostID = hostID
		d.HostInstanceID = hostInstanceID
		d.Generations = append([]Generation(nil), generations...)
		d.Revision++
		d.LeaseOwner, d.LeaseUntilUnix = "", 0
		d.Operation = Operation{}
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
		d.Operation = Operation{}
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
	return cloneRecord(Record{
		User: d.User, App: d.App, HostID: d.HostID, HostInstanceID: d.HostInstanceID, Revision: d.Revision,
		LeaseOwner: d.LeaseOwner, LeaseUntilUnix: d.LeaseUntilUnix,
		Operation:   d.Operation,
		Generations: d.Generations,
	})
}
