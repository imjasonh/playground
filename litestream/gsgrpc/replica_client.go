// Package gsgrpc provides a Cloud Storage replica client that uses gRPC.
package gsgrpc

import (
	"context"
	"fmt"
	"net/url"
	"strconv"

	"cloud.google.com/go/storage"
	"google.golang.org/api/option"

	"github.com/benbjohnson/litestream"
	"github.com/benbjohnson/litestream/gs"
)

func init() {
	litestream.RegisterReplicaClientFactory(ReplicaClientType, NewReplicaClientFromURL)
}

// ReplicaClientType is the URL scheme and client type for this package.
const ReplicaClientType = "gcs-grpc"

// ReplicaClient is a Cloud Storage replica client that uses the gRPC transport.
type ReplicaClient struct {
	*gs.ReplicaClient
}

// NewReplicaClient returns a gRPC Cloud Storage replica client. When rapid is
// true, it enables the appendable upload and bidirectional read APIs required
// by RAPID zonal buckets.
func NewReplicaClient(rapid bool) *ReplicaClient {
	options := make([]option.ClientOption, 0, 2)
	if rapid {
		options = append(options, storage.WithAppendableUploads(), storage.WithGRPCBidiReads())
	}

	client := gs.NewReplicaClientWithClientFactory(ReplicaClientType, func(ctx context.Context) (*storage.Client, error) {
		return storage.NewGRPCClient(ctx, options...)
	})
	client.SetFinalizeOnClose(rapid)
	return &ReplicaClient{ReplicaClient: client}
}

// NewReplicaClientFromURL creates a gRPC Cloud Storage replica client from URL
// components. Set rapid=true only for a RAPID zonal bucket.
func NewReplicaClientFromURL(scheme, host, urlPath string, query url.Values, userinfo *url.Userinfo) (litestream.ReplicaClient, error) {
	if host == "" {
		return nil, fmt.Errorf("bucket required for %s replica URL", ReplicaClientType)
	}

	rapid := false
	if raw := query.Get("rapid"); raw != "" {
		var err error
		rapid, err = strconv.ParseBool(raw)
		if err != nil {
			return nil, fmt.Errorf("parse rapid query parameter: %w", err)
		}
	}

	client := NewReplicaClient(rapid)
	client.Bucket = host
	client.Path = urlPath
	return client, nil
}
