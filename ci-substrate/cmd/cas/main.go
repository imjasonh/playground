// Command cas is the authoritative, multi-tenant CAS and action cache of the
// ci-substrate control plane. It speaks the Bazel Remote Execution API
// (ContentAddressableStorage, ActionCache, ByteStream, Capabilities) over
// gRPC, backed by a content-addressed blob store on disk.
package main

import (
	"context"
	"log/slog"
	"net"
	"os"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"github.com/sethvargo/go-envconfig"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc"
	"google.golang.org/grpc/health"
	healthpb "google.golang.org/grpc/health/grpc_health_v1"

	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

type config struct {
	Addr     string `env:"ADDR, default=:8980"`
	StoreDir string `env:"STORE_DIR, default=/data"`
	// Tenants is a JSON object mapping tokens to instance names. Empty means
	// the demo default of one token that may use the empty instance name.
	Tenants string `env:"TENANTS"`
}

func main() {
	ctx := context.Background()
	var c config
	envconfig.MustProcess(ctx, &c)

	store, err := blob.NewStore(c.StoreDir)
	if err != nil {
		slog.Error("opening blob store", "dir", c.StoreDir, "err", err)
		os.Exit(1)
	}
	tenantsJSON := c.Tenants
	if tenantsJSON == "" {
		tenantsJSON = `{"demo":[""]}`
	}
	tenants, err := tenant.LoadJSON([]byte(tenantsJSON))
	if err != nil {
		slog.Error("parsing tenants", "err", err)
		os.Exit(1)
	}

	origin := remote.NewOrigin(store, tenants)
	srv := grpc.NewServer()
	repb.RegisterContentAddressableStorageServer(srv, origin)
	repb.RegisterActionCacheServer(srv, origin)
	repb.RegisterCapabilitiesServer(srv, origin)
	bytestream.RegisterByteStreamServer(srv, origin)
	hs := health.NewServer()
	hs.SetServingStatus("", healthpb.HealthCheckResponse_SERVING)
	healthpb.RegisterHealthServer(srv, hs)

	lis, err := net.Listen("tcp", c.Addr)
	if err != nil {
		slog.Error("listen", "addr", c.Addr, "err", err)
		os.Exit(1)
	}
	slog.Info("cas serving", "addr", c.Addr, "store", c.StoreDir)
	if err := srv.Serve(lis); err != nil {
		slog.Error("serve", "err", err)
		os.Exit(1)
	}
}
