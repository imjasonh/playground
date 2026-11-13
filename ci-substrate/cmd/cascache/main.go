// Command cascache is the node-local, read-only CAS proxy. It runs as a
// DaemonSet on every worker node, backed by local disk, and serves build
// actors on that node from a verified read-through cache in front of the
// central cas origin. A blob fetched once is served to every later reader on
// the node, and every served blob is verified against its digest in flight so
// a corrupted or poisoned cache entry can never be handed out.
package main

import (
	"context"
	"encoding/json"
	"log/slog"
	"net"
	"net/http"
	"os"
	"os/signal"
	"syscall"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	_ "github.com/chainguard-dev/clog/gcp/init"
	"github.com/sethvargo/go-envconfig"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/health"
	healthpb "google.golang.org/grpc/health/grpc_health_v1"

	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/cache"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

type config struct {
	Addr        string `env:"ADDR, default=:9092"`
	MetricsAddr string `env:"METRICS_ADDR, default=:9090"`
	StoreDir    string `env:"STORE_DIR, default=/cache"`
	OriginAddr  string `env:"ORIGIN_ADDR, required"`
	// Tenants is a JSON object mapping tokens to instance names. Empty means
	// the demo default of one token that may use the empty instance name.
	Tenants string `env:"TENANTS"`
}

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGTERM, os.Interrupt)
	defer stop()
	var c config
	envconfig.MustProcess(ctx, &c)
	shutdown, err := telemetry.Setup(ctx, "cascache")
	if err != nil {
		slog.Error("setting up telemetry", "err", err)
		os.Exit(1)
	}

	store, err := blob.NewStore(c.StoreDir)
	if err != nil {
		slog.Error("opening local cache store", "dir", c.StoreDir, "err", err)
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

	telemetry.ObserveDisk(c.StoreDir)
	conn, err := grpc.NewClient(c.OriginAddr, append(telemetry.DialOptions(), grpc.WithTransportCredentials(insecure.NewCredentials()))...)
	if err != nil {
		slog.Error("dialing origin", "addr", c.OriginAddr, "err", err)
		os.Exit(1)
	}
	defer conn.Close()

	originClient := remote.NewClient(conn)
	rtc := cache.New(store, originClient)
	cs := remote.NewCacheServer(rtc, originClient, tenants)

	srv := grpc.NewServer(telemetry.ServerOptions()...)
	repb.RegisterContentAddressableStorageServer(srv, cs)
	bytestream.RegisterByteStreamServer(srv, cs)
	hs := health.NewServer()
	hs.SetServingStatus("", healthpb.HealthCheckResponse_SERVING)
	healthpb.RegisterHealthServer(srv, hs)

	go serveMetrics(c.MetricsAddr, rtc)

	lis, err := net.Listen("tcp", c.Addr)
	if err != nil {
		slog.Error("listen", "addr", c.Addr, "err", err)
		os.Exit(1)
	}
	slog.Info("cascache serving", "addr", c.Addr, "origin", c.OriginAddr, "store", c.StoreDir)
	go func() {
		<-ctx.Done()
		slog.Info("shutting down")
		hs.Shutdown()
		srv.GracefulStop()
	}()
	if err := srv.Serve(lis); err != nil {
		slog.Error("serve", "err", err)
		os.Exit(1)
	}
	sctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	if err := shutdown(sctx); err != nil {
		slog.Error("flushing telemetry", "err", err)
	}
}

// serveMetrics exposes the cache counters as JSON so a demo can prove that a
// warm read served no origin fetch and that a poisoned entry was rejected.
// The same counts go to the collector as cascache.requests.
func serveMetrics(addr string, c *cache.Cache) {
	mux := http.NewServeMux()
	mux.HandleFunc("/stats", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		if err := json.NewEncoder(w).Encode(c.Stats()); err != nil {
			slog.Error("encoding stats", "err", err)
		}
	})
	srv := &http.Server{Addr: addr, Handler: mux, ReadHeaderTimeout: 5 * time.Second}
	if err := srv.ListenAndServe(); err != nil {
		slog.Error("metrics server", "err", err)
	}
}
