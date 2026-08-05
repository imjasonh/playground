package quota

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"sort"
	"strings"
	"time"

	"cloud.google.com/go/firestore"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type Firestore struct {
	client     *firestore.Client
	collection string
}

type eventDoc struct {
	ID     string `firestore:"id"`
	AtUnix int64  `firestore:"at_unix"`
}

type windowDoc struct {
	Version    int        `firestore:"version"`
	Kind       string     `firestore:"kind"`
	Events     []eventDoc `firestore:"events"`
	ExpireUnix int64      `firestore:"expire_unix"`
}

func NewFirestore(ctx context.Context, projectID, prefix string) (*Firestore, error) {
	if projectID == "" || strings.TrimSpace(prefix) == "" {
		return nil, fmt.Errorf("firestore project and prefix required")
	}
	client, err := firestore.NewClient(ctx, projectID)
	if err != nil {
		return nil, err
	}
	return &Firestore{client: client, collection: prefix + "_quota_windows"}, nil
}

func (f *Firestore) Take(ctx context.Context, req Request) error {
	if err := validate(req); err != nil {
		return err
	}
	sum := sha256.Sum256([]byte(req.Kind + "\x00" + req.Subject))
	ref := f.client.Collection(f.collection).Doc(hex.EncodeToString(sum[:]))
	return f.client.RunTransaction(ctx, func(ctx context.Context, tx *firestore.Transaction) error {
		var doc windowDoc
		snap, err := tx.Get(ref)
		if err != nil && status.Code(err) != codes.NotFound {
			return err
		}
		if err == nil {
			if err := snap.DataTo(&doc); err != nil {
				return err
			}
		}
		cutoff := req.At.Add(-req.Limit.Window).UnixNano()
		events := make([]eventDoc, 0, len(doc.Events)+1)
		for _, existing := range doc.Events {
			if existing.AtUnix > cutoff {
				events = append(events, existing)
			}
			if existing.ID == req.EventID && existing.AtUnix > cutoff {
				return nil
			}
		}
		sort.Slice(events, func(i, j int) bool { return events[i].AtUnix < events[j].AtUnix })
		if len(events) >= req.Limit.Max {
			return ErrExceeded{
				Kind: req.Kind, Limit: req.Limit.Max,
				RetryAt: time.Unix(0, events[0].AtUnix).Add(req.Limit.Window),
			}
		}
		events = append(events, eventDoc{ID: req.EventID, AtUnix: req.At.UnixNano()})
		return tx.Set(ref, windowDoc{
			Version: 1, Kind: req.Kind, Events: events,
			ExpireUnix: req.At.Add(req.Limit.Window).Unix(),
		})
	})
}

func (f *Firestore) Close() error {
	if f == nil || f.client == nil {
		return nil
	}
	return f.client.Close()
}
