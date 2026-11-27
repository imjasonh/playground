// Command pool keeps one tenant's Substrate runners sized to that tenant's
// queue. It reads the queue from the scheduler in cas with the tenant's
// token, and creates, resumes, suspends, and deletes actors in the tenant's
// atespace through Substrate's control API. One pool runs per tenant.
//
// With WORKER_POOL set, it also sizes that WorkerPool through the Kubernetes
// API: workers for the actors that do not fit in BASE_SLOTS, down to zero
// when none needs one.
//
// It runs in the ci-substrate namespace as a per-tenant ServiceAccount with
// the editor role in its tenant's atespace, with the API's trust bundle and a
// ServiceAccount token projected into the pod, and a second token for the
// Kubernetes API when it sizes a WorkerPool; see deploy/substrate/pool.yaml.
package main

import (
	"context"
	"errors"
	"log/slog"
	"os"
	"os/signal"
	"syscall"
	"time"

	_ "github.com/chainguard-dev/clog/gcp/init"
	"github.com/sethvargo/go-envconfig"
	ateapi "go.ate.dev/substrate/api/ateapi/v1"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"

	workerv1 "github.com/imjasonh/playground/ci-substrate/api/worker/v1"
	"github.com/imjasonh/playground/ci-substrate/internal/actorpool"
	"github.com/imjasonh/playground/ci-substrate/internal/substrate"
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
	"github.com/imjasonh/playground/ci-substrate/internal/workerpool"
)

type config struct {
	// AteAddr is Substrate's control API. AteServerName is the name on its
	// serving certificate and the audience of the token in AteTokenFile.
	AteAddr       string `env:"ATE_ADDR, default=api.ate-system.svc:443"`
	AteServerName string `env:"ATE_SERVER_NAME, default=api.ate-system.svc"`
	AteCAFile     string `env:"ATE_CA_FILE, default=/run/ate/trust-bundle.pem"`
	AteTokenFile  string `env:"ATE_TOKEN_FILE, default=/run/ate/token"`

	// Atespace and Template name the tenant's actor template. Prefix starts
	// the name of every actor the pool creates. EgressPolicyFile is the
	// policy each actor gets before it first resumes.
	Atespace         string `env:"ATESPACE, required"`
	Template         string `env:"TEMPLATE, default=ci-runner"`
	Prefix           string `env:"PREFIX, default=ci-runner-"`
	EgressPolicyFile string `env:"EGRESS_POLICY_FILE, required"`

	// CasAddr is the scheduler, and Token the tenant token the pool reads
	// its queue with. Instances narrows the queue to those instances.
	CasAddr   string   `env:"CAS_ADDR, default=cas.ci-substrate.svc.cluster.local:8980"`
	Token     string   `env:"TENANT_TOKEN, required"`
	Instances []string `env:"INSTANCES"`

	Warm      int           `env:"WARM, default=1"`
	Max       int           `env:"MAX, default=4"`
	IdleAfter time.Duration `env:"IDLE_AFTER, default=2m"`
	// Interval is how often the pool reconciles with no queue change, and
	// MinInterval the least time between reconciles that queue changes start.
	Interval    time.Duration `env:"INTERVAL, default=5s"`
	MinInterval time.Duration `env:"MIN_INTERVAL, default=250ms"`

	// WorkerPool is the namespace/name of the WorkerPool the pool sizes, or
	// empty for none. The other fields fill actorpool.Burst.
	WorkerPool      string `env:"WORKER_POOL"`
	BaseSlots       int    `env:"BASE_SLOTS, default=1"`
	ActorsPerWorker int    `env:"ACTORS_PER_WORKER, default=1"`
	MaxWorkers      int    `env:"MAX_WORKERS, default=4"`

	// Kubernetes sets the API server's address in every pod.
	KubeHost      string `env:"KUBERNETES_SERVICE_HOST"`
	KubePort      string `env:"KUBERNETES_SERVICE_PORT"`
	KubeCAFile    string `env:"KUBE_CA_FILE, default=/var/run/secrets/kubernetes.io/serviceaccount/ca.crt"`
	KubeTokenFile string `env:"KUBE_TOKEN_FILE, default=/var/run/secrets/kubernetes.io/serviceaccount/token"`
}

// queue reads the tenant's queue from the scheduler.
type queue struct {
	client    workerv1.WorkerServiceClient
	token     string
	instances []string
}

func (q *queue) Status(ctx context.Context) (int, []string, error) {
	byPlatform, busy, err := q.StatusByPlatform(ctx)
	if err != nil {
		return 0, nil, err
	}
	return byPlatform[""], busy, nil
}

func (q *queue) StatusByPlatform(ctx context.Context) (map[string]int, []string, error) {
	ctx, cancel := context.WithTimeout(tenant.Outgoing(ctx, q.token), 10*time.Second)
	defer cancel()
	resp, err := q.client.Status(ctx, &workerv1.StatusRequest{InstanceNames: q.instances})
	if err != nil {
		return nil, nil, err
	}
	out := make(map[string]int, len(resp.GetQueuedByPlatform()))
	for k, v := range resp.GetQueuedByPlatform() {
		out[k] = int(v)
	}
	if _, ok := out[""]; !ok && resp.GetQueued() > 0 {
		out[""] = int(resp.GetQueued())
	}
	return out, resp.GetBusyBotIds(), nil
}

func (q *queue) Watch(ctx context.Context, changed func()) error {
	stream, err := q.client.WatchStatus(tenant.Outgoing(ctx, q.token), &workerv1.StatusRequest{InstanceNames: q.instances})
	if err != nil {
		return err
	}
	for {
		if _, err := stream.Recv(); err != nil {
			return err
		}
		changed()
	}
}

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGTERM, os.Interrupt)
	defer stop()
	var c config
	envconfig.MustProcess(ctx, &c)
	shutdown, err := telemetry.Setup(ctx, "pool")
	if err != nil {
		slog.Error("setting up telemetry", "err", err)
		os.Exit(1)
	}
	defer func() {
		sctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()
		if err := shutdown(sctx); err != nil {
			slog.Error("flushing telemetry", "err", err)
		}
	}()

	policy, err := os.ReadFile(c.EgressPolicyFile)
	if err != nil {
		slog.Error("reading egress policy", "err", err)
		os.Exit(1)
	}
	ateConn, err := substrate.Dial(c.AteAddr, c.AteServerName, c.AteCAFile, c.AteTokenFile)
	if err != nil {
		slog.Error("dialing Substrate", "err", err)
		os.Exit(1)
	}
	defer ateConn.Close()
	casConn, err := grpc.NewClient(c.CasAddr, append(telemetry.DialOptions(), grpc.WithTransportCredentials(insecure.NewCredentials()))...)
	if err != nil {
		slog.Error("dialing cas", "err", err)
		os.Exit(1)
	}
	defer casConn.Close()

	actors, err := substrate.NewActors(ctx, ateapi.NewControlClient(ateConn), c.Atespace, c.Template, policy)
	if err != nil {
		slog.Error("configuring Substrate actors", "err", err)
		os.Exit(1)
	}
	cfg := actorpool.Config{
		Actors:      actors,
		Queue:       &queue{client: workerv1.NewWorkerServiceClient(casConn), token: c.Token, instances: c.Instances},
		Prefix:      c.Prefix,
		Warm:        c.Warm,
		Max:         c.Max,
		IdleAfter:   c.IdleAfter,
		Interval:    c.Interval,
		MinInterval: c.MinInterval,
	}
	if c.WorkerPool != "" {
		workers, err := workerpool.New(c.KubeHost, c.KubePort, c.KubeCAFile, c.KubeTokenFile, c.WorkerPool)
		if err != nil {
			slog.Error("configuring WorkerPool scaling", "err", err)
			os.Exit(1)
		}
		cfg.Burst = &actorpool.Burst{
			Workers:         workers,
			Name:            c.WorkerPool,
			BaseSlots:       c.BaseSlots,
			ActorsPerWorker: c.ActorsPerWorker,
			MaxWorkers:      c.MaxWorkers,
		}
	}
	pool, err := actorpool.New(cfg)
	if err != nil {
		slog.Error("configuring pool", "err", err)
		os.Exit(1)
	}
	slog.Info("pool running", "atespace", c.Atespace, "template", c.Template, "warm", c.Warm, "max", c.Max, "idleAfter", c.IdleAfter,
		"workerPool", c.WorkerPool, "baseSlots", c.BaseSlots, "actorsPerWorker", c.ActorsPerWorker, "maxWorkers", c.MaxWorkers)
	if err := pool.Run(ctx); err != nil && !errors.Is(err, context.Canceled) {
		slog.Error("pool stopped", "err", err)
		os.Exit(1)
	}
}
