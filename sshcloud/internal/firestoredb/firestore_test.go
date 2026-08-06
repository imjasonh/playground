package firestoredb

import (
	"context"
	"strings"
	"testing"
)

func TestOpenValidatesCoordinatesBeforeCreatingClient(t *testing.T) {
	t.Parallel()
	for _, tc := range []struct {
		name                      string
		project, database, prefix string
		want                      string
	}{
		{"project", " ", "database", "prefix", "project ID"},
		{"database", "project", " ", "prefix", "database"},
		{"prefix", "project", "database", " ", "collection prefix"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			_, _, err := Open(context.Background(), tc.project, tc.database, tc.prefix)
			if err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Fatalf("error = %v, want substring %q", err, tc.want)
			}
		})
	}
}
