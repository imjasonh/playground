// Command cas is the authoritative, multi-tenant CAS, action cache, scheduler,
// Remote Asset, Remote Logstream, and Build Event Service (BES) server of the
// ci-substrate control plane. It speaks the Bazel Remote Execution API
// (ContentAddressableStorage, ActionCache, ByteStream, Capabilities, Execution,
// Operations), Remote Asset API (Fetch, Push), Remote Logstream API
// (LogStreamService), and Build Event Service (PublishBuildEvent) over gRPC,
// and leases queued actions to runners over the WorkerService protocol.
package main

import (
	"context"
	"errors"
	"log/slog"
	"net"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"
	"time"

	longrunning "cloud.google.com/go/longrunning/autogen/longrunningpb"
	assetpb "github.com/bazelbuild/remote-apis/build/bazel/remote/asset/v1"
	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	logstreampb "github.com/bazelbuild/remote-apis/build/bazel/remote/logstream/v1"
	_ "github.com/chainguard-dev/clog/gcp/init"
	"github.com/sethvargo/go-envconfig"
	"google.golang.org/genproto/googleapis/bytestream"
	buildpb "google.golang.org/genproto/googleapis/devtools/build/v1"
	"google.golang.org/grpc"
	"google.golang.org/grpc/health"
	healthpb "google.golang.org/grpc/health/grpc_health_v1"

	workerv1 "github.com/imjasonh/playground/ci-substrate/api/worker/v1"
	"github.com/imjasonh/playground/ci-substrate/internal/actioncache"
	"github.com/imjasonh/playground/ci-substrate/internal/asset"
	"github.com/imjasonh/playground/ci-substrate/internal/bes"
	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/exec"
	"github.com/imjasonh/playground/ci-substrate/internal/invocation"
	"github.com/imjasonh/playground/ci-substrate/internal/logstream"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
	"github.com/imjasonh/playground/ci-substrate/internal/tlscfg"
)

type config struct {
	Addr     string `env:"ADDR, default=:8980"`
	HTTPAddr string `env:"HTTP_ADDR"`
	StoreDir string `env:"STORE_DIR, default=/data"`
	// Tenants is a JSON object mapping tokens to instance names or grant
	// objects. Empty means the demo default of one token that may use the
	// empty instance name.
	Tenants string `env:"TENANTS"`
	// LeaseDuration is how long a runner may go without a heartbeat before
	// its job is handed to another runner.
	LeaseDuration time.Duration `env:"LEASE_DURATION, default=30s"`
	// InvocationIdle is how long a Bazel invocation goes without a call
	// before cas records it as finished.
	InvocationIdle time.Duration `env:"INVOCATION_IDLE, default=1m"`
	// CASMaxBytes enables LRU eviction on the CAS blob store when positive.
	CASMaxBytes int64 `env:"CAS_MAX_BYTES"`
	// MaxBlobBytes bounds the largest single blob upload accepted by CAS and
	// advertised in CacheCapabilities.max_cas_blob_size_bytes.
	MaxBlobBytes int64 `env:"MAX_CAS_BLOB_SIZE_BYTES"`
	// TLS server credentials; when unset, cas serves plaintext gRPC.
	TLSCertFile     string `env:"TLS_CERT_FILE"`
	TLSKeyFile      string `env:"TLS_KEY_FILE"`
	TLSClientCAFile string `env:"TLS_CLIENT_CA_FILE"`
	// Substrate Actor JWT verification; when ActorJWTIssuer is set, cas
	// verifies short-lived Actor JWTs injected by atenet-egress via OIDC
	// discovery against ate-idp-server.
	ActorJWTIssuer   string `env:"ACTOR_JWT_ISSUER"`
	ActorJWTAudience string `env:"ACTOR_JWT_AUDIENCE, default=cas.ci-substrate.svc.cluster.local"`
	ActorJWTCAFile   string `env:"ACTOR_JWT_CA_FILE"`
}

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGTERM, os.Interrupt)
	defer stop()
	var c config
	envconfig.MustProcess(ctx, &c)
	shutdown, err := telemetry.Setup(ctx, "cas")
	if err != nil {
		slog.Error("setting up telemetry", "err", err)
		os.Exit(1)
	}

	store, err := blob.NewStoreWithLimit(filepath.Join(c.StoreDir, "cas"), c.CASMaxBytes)
	if err != nil {
		slog.Error("opening blob store", "dir", c.StoreDir, "err", err)
		os.Exit(1)
	}
	actions, err := actioncache.NewStore(filepath.Join(c.StoreDir, "ac"))
	if err != nil {
		slog.Error("opening action cache", "dir", c.StoreDir, "err", err)
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
	if c.ActorJWTIssuer != "" {
		v, err := tenant.NewActorJWTVerifier(tenant.ActorJWTConfig{
			Issuer:   c.ActorJWTIssuer,
			Audience: c.ActorJWTAudience,
			CAFile:   c.ActorJWTCAFile,
		})
		if err != nil {
			slog.Error("configuring actor JWT verifier", "err", err)
			os.Exit(1)
		}
		tenants.SetActorJWTVerifier(v)
		slog.Info("actor JWT verification enabled", "issuer", c.ActorJWTIssuer, "audience", c.ActorJWTAudience)
	}
	assets, err := asset.New(filepath.Join(c.StoreDir, "asset"), store, tenants)
	if err != nil {
		slog.Error("opening asset store", "dir", c.StoreDir, "err", err)
		os.Exit(1)
	}

	telemetry.ObserveDisk(c.StoreDir)
	invocations := invocation.New(c.InvocationIdle)
	flushed := make(chan struct{})
	go func() {
		invocations.Run(ctx)
		close(flushed)
	}()

	besSrv, err := bes.New(filepath.Join(c.StoreDir, "bes"), tenants, invocations)
	if err != nil {
		slog.Error("opening BES store", "dir", c.StoreDir, "err", err)
		os.Exit(1)
	}
	logs := logstream.New(tenants)

	origin := remote.NewOrigin(store, actions, tenants, invocations)
	origin.SetLogStream(logs)
	origin.SetMaxBlobBytes(c.MaxBlobBytes)

	scheduler := exec.New(store, actions, tenants, c.LeaseDuration, invocations)
	go scheduler.Run(ctx)

	opts := telemetry.ServerOptions()
	tlsOpt, err := (tlscfg.ServerConfig{
		CertFile:     c.TLSCertFile,
		KeyFile:      c.TLSKeyFile,
		ClientCAFile: c.TLSClientCAFile,
	}).ServerOption()
	if err != nil {
		slog.Error("configuring TLS", "err", err)
		os.Exit(1)
	}
	if tlsOpt != nil {
		opts = append(opts, tlsOpt)
	}
	srv := grpc.NewServer(opts...)
	repb.RegisterExecutionServer(srv, scheduler)
	longrunning.RegisterOperationsServer(srv, scheduler)
	workerv1.RegisterWorkerServiceServer(srv, scheduler)
	repb.RegisterContentAddressableStorageServer(srv, origin)
	repb.RegisterActionCacheServer(srv, origin)
	repb.RegisterCapabilitiesServer(srv, origin)
	bytestream.RegisterByteStreamServer(srv, origin)
	assetpb.RegisterFetchServer(srv, assets)
	assetpb.RegisterPushServer(srv, assets)
	logstreampb.RegisterLogStreamServiceServer(srv, logs)
	buildpb.RegisterPublishBuildEventServer(srv, besSrv)
	hs := health.NewServer()
	hs.SetServingStatus("", healthpb.HealthCheckResponse_SERVING)
	healthpb.RegisterHealthServer(srv, hs)

	var httpSrv *http.Server
	if c.HTTPAddr != "" {
		httpSrv = &http.Server{
			Addr:              c.HTTPAddr,
			Handler:           besSrv.Handler(),
			ReadHeaderTimeout: 5 * time.Second,
		}
		go func() {
			slog.Info("cas HTTP API serving", "addr", c.HTTPAddr)
			if err := httpSrv.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
				slog.Error("HTTP server", "err", err)
			}
		}()
	}

	lis, err := net.Listen("tcp", c.Addr)
	if err != nil {
		slog.Error("listen", "addr", c.Addr, "err", err)
		os.Exit(1)
	}
	slog.Info("cas serving", "addr", c.Addr, "store", c.StoreDir)
	go func() {
		<-ctx.Done()
		slog.Info("shutting down")
		hs.Shutdown()
		if httpSrv != nil {
			sctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()
			_ = httpSrv.Shutdown(sctx)
		}
		srv.GracefulStop()
	}()
	if err := srv.Serve(lis); err != nil {
		slog.Error("serve", "err", err)
		os.Exit(1)
	}
	<-flushed
	sctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	if err := shutdown(sctx); err != nil {
		slog.Error("flushing telemetry", "err", err)
	}
}
