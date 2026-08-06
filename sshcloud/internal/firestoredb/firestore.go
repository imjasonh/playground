// Package firestoredb owns the shared Firestore client configuration boundary.
package firestoredb

import (
	"context"
	"fmt"
	"strings"

	"cloud.google.com/go/firestore"
)

// Open validates common database coordinates and returns a client plus the
// normalized collection prefix. Callers retain ownership of collection names.
func Open(ctx context.Context, projectID, database, prefix string) (*firestore.Client, string, error) {
	if strings.TrimSpace(projectID) == "" {
		return nil, "", fmt.Errorf("firestore project ID required")
	}
	if strings.TrimSpace(database) == "" {
		return nil, "", fmt.Errorf("firestore database required")
	}
	prefix = strings.TrimSpace(prefix)
	if prefix == "" {
		return nil, "", fmt.Errorf("firestore collection prefix required")
	}
	client, err := firestore.NewClientWithDatabase(ctx, projectID, database)
	return client, prefix, err
}

// Close releases client when present.
func Close(client *firestore.Client) error {
	if client == nil {
		return nil
	}
	return client.Close()
}
