package gsgrpc

import (
	"net/url"
	"testing"
)

func TestNewReplicaClientFromURL(t *testing.T) {
	tests := []struct {
		name    string
		host    string
		path    string
		query   url.Values
		wantErr bool
	}{
		{
			name:  "regular bucket",
			host:  "replica",
			path:  "db",
			query: url.Values{},
		},
		{
			name:  "rapid bucket",
			host:  "replica",
			path:  "db",
			query: url.Values{"rapid": {"true"}},
		},
		{
			name:    "missing bucket",
			path:    "db",
			query:   url.Values{},
			wantErr: true,
		},
		{
			name:    "invalid rapid value",
			host:    "replica",
			path:    "db",
			query:   url.Values{"rapid": {"sometimes"}},
			wantErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			client, err := NewReplicaClientFromURL(ReplicaClientType, tt.host, tt.path, tt.query, nil)
			if tt.wantErr {
				if err == nil {
					t.Fatal("NewReplicaClientFromURL error = nil")
				}
				return
			}
			if err != nil {
				t.Fatalf("NewReplicaClientFromURL: %v", err)
			}

			gcsClient, ok := client.(*ReplicaClient)
			if !ok {
				t.Fatalf("client type = %T, want *ReplicaClient", client)
			}
			if got, want := gcsClient.Type(), ReplicaClientType; got != want {
				t.Errorf("Type() = %q, want %q", got, want)
			}
			if got, want := gcsClient.Bucket, tt.host; got != want {
				t.Errorf("Bucket = %q, want %q", got, want)
			}
			if got, want := gcsClient.Path, tt.path; got != want {
				t.Errorf("Path = %q, want %q", got, want)
			}
		})
	}
}
