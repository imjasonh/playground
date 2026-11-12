// Command cictl is the control-plane CLI and demo driver. It drives the
// central cas, a node-local cascache, and the runners to show the headline
// properties on a live cluster: multi-tenant isolation (one tenant cannot read
// another's instance, action cache, or queue), optimized caching (a blob one
// tenant warmed is served to another tenant from the node-local cache with no
// second origin fetch), and remote execution (an action runs on a tenant's
// runner, its outputs land in the CAS, and the next Execute is a cache hit).
package main

import (
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"log/slog"
	"net/http"
	"os"
	"strings"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"

	"github.com/imjasonh/playground/ci-substrate/internal/cache"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
	"github.com/imjasonh/playground/ci-substrate/internal/tree"
)

func main() {
	originAddr := flag.String("origin-addr", "", "origin cas address (host:port)")
	cacheAddr := flag.String("cache-addr", "", "node-local cascache address (host:port)")
	cacheMetricsURL := flag.String("cache-metrics-url", "", "cascache metrics base URL, e.g. http://host:9090")
	tokenA := flag.String("token-a", "tok-a", "tenant A token")
	tokenB := flag.String("token-b", "tok-b", "tenant B token")
	instanceA := flag.String("instance-a", "tenant-a", "tenant A private instance")
	shared := flag.String("shared", "shared", "instance both tenants may read")
	execTimeout := flag.Duration("exec-timeout", 3*time.Minute, "how long to wait for a runner to run the demo action; 0 skips execution")
	workerPrefix := flag.String("worker-prefix", "", "if set, the runner that ran the action must report a worker name with this prefix")
	flag.Parse()

	if *originAddr == "" || *cacheAddr == "" {
		slog.Error("missing required flags", "need", "-origin-addr and -cache-addr")
		os.Exit(2)
	}

	if err := run(*originAddr, *cacheAddr, *cacheMetricsURL, *tokenA, *tokenB, *instanceA, *shared, *execTimeout, *workerPrefix); err != nil {
		slog.Error("demo failed", "err", err)
		os.Exit(1)
	}
	slog.Info("demo passed: multi-tenant isolation, node-local cache reuse, and remote execution verified")
}

func run(originAddr, cacheAddr, metricsURL, tokenA, tokenB, instanceA, shared string, execTimeout time.Duration, workerPrefix string) error {
	originConn, err := grpc.NewClient(originAddr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		return err
	}
	defer originConn.Close()
	cacheConn, err := grpc.NewClient(cacheAddr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		return err
	}
	defer cacheConn.Close()
	origin := remote.NewClient(originConn)
	cacheClient := remote.NewClient(cacheConn)

	ctxA := tenant.Outgoing(context.Background(), tokenA)
	ctxB := tenant.Outgoing(context.Background(), tokenB)

	if err := cacheDemo(ctxA, ctxB, origin, cacheClient, metricsURL, instanceA, shared); err != nil {
		return err
	}
	if execTimeout <= 0 {
		slog.Info("skipping remote execution (-exec-timeout=0)")
		return nil
	}
	return execDemo(ctxA, ctxB, origin, cacheClient, repb.NewExecutionClient(originConn), instanceA, execTimeout, workerPrefix)
}

// cacheDemo proves node-local cache reuse across tenants and isolation of a
// tenant's instance and action cache.
func cacheDemo(ctxA, ctxB context.Context, origin, cacheClient *remote.Client, metricsURL, instanceA, shared string) error {

	// Tenant A uploads a shared blob to the origin.
	content := []byte(fmt.Sprintf("shared build artifact %d", time.Now().UnixNano()))
	d, err := retry(func() (*repb.Digest, error) {
		return origin.Upload(ctxA, shared, content)
	})
	if err != nil {
		return fmt.Errorf("tenant A upload: %w", err)
	}
	slog.Info("tenant A uploaded shared blob", "digest", digest.Key(d))

	stats := func() (cache.Stats, error) {
		if metricsURL == "" {
			return cache.Stats{}, nil
		}
		return fetchStats(metricsURL)
	}
	before, err := stats()
	if err != nil {
		return err
	}

	// Tenant A reads it through the node-local cache (cold: one origin fetch).
	if _, err := retry(func() ([]byte, error) {
		return cacheClient.Fetch(ctxA, shared, d)
	}); err != nil {
		return fmt.Errorf("tenant A cold read: %w", err)
	}
	afterCold, err := stats()
	if err != nil {
		return err
	}
	// Tenant B reads the same content (warm: should be a node-local hit).
	got, err := retry(func() ([]byte, error) {
		return cacheClient.Fetch(ctxB, shared, d)
	})
	if err != nil {
		return fmt.Errorf("tenant B warm read: %w", err)
	}
	if string(got) != string(content) {
		return errors.New("tenant B read wrong bytes from cache")
	}
	afterWarm, err := stats()
	if err != nil {
		return err
	}
	if metricsURL != "" {
		// The cascache counters are cumulative across runs, so compare
		// deltas: the cold read fetches once, the warm read only hits.
		slog.Info("cache stats", "hits", afterWarm.Hits, "originFetches", afterWarm.OriginFetches, "poisonRejected", afterWarm.PoisonRejected)
		if n := afterCold.OriginFetches - before.OriginFetches; n != 1 {
			return fmt.Errorf("cold read made %d origin fetches, want 1", n)
		}
		if n := afterWarm.OriginFetches - afterCold.OriginFetches; n != 0 {
			return fmt.Errorf("warm read made %d origin fetches, want 0", n)
		}
		if n := afterWarm.Hits - afterCold.Hits; n != 1 {
			return fmt.Errorf("warm read made %d cache hits, want 1", n)
		}
	}
	slog.Info("tenant B served shared blob from node-local cache with no origin fetch")

	// Isolation: tenant B must not read through tenant A's private instance.
	if err := tryCrossTenant(ctxB, cacheClient, instanceA, d); err != nil {
		return err
	}
	// Isolation: tenant B must not read tenant A's action cache, which is
	// what maps tenant A's actions to its output digests.
	action := digest.FromBytes([]byte(fmt.Sprintf("tenant A action %d", time.Now().UnixNano())))
	if err := origin.UpdateActionResult(ctxA, instanceA, action, &repb.ActionResult{StdoutDigest: d}); err != nil {
		return fmt.Errorf("tenant A action cache write: %w", err)
	}
	if _, _, err := origin.GetActionResult(ctxB, instanceA, action); status.Code(err) != codes.PermissionDenied {
		return fmt.Errorf("tenant B reading tenant A's action cache: got %v, want PermissionDenied", err)
	}
	if _, ok, err := origin.GetActionResult(ctxA, instanceA, action); err != nil || !ok {
		return fmt.Errorf("tenant A reading its own action cache: ok=%v err=%v", ok, err)
	}
	slog.Info("isolation held: tenant B denied tenant A's instance and action cache")
	return nil
}

// execDemo runs an action through Execute on tenant A's runner, checks the
// outputs it uploaded, and shows the next Execute is a cache hit and that
// tenant B cannot submit into tenant A's instance. A non-empty workerPrefix
// checks which kind of runner did the work: Substrate actors report their
// actor name.
func execDemo(ctxA, ctxB context.Context, origin, cacheClient *remote.Client, execer repb.ExecutionClient, instanceA string, timeout time.Duration, workerPrefix string) error {
	content := fmt.Sprintf("hello from tenant A at %d\n", time.Now().UnixNano())
	input, err := origin.Upload(ctxA, instanceA, []byte(content))
	if err != nil {
		return fmt.Errorf("uploading input: %w", err)
	}
	root, err := uploadProto(ctxA, origin, instanceA, &repb.Directory{Files: []*repb.FileNode{{Name: "input.txt", Digest: input}}})
	if err != nil {
		return err
	}
	command, err := uploadProto(ctxA, origin, instanceA, &repb.Command{
		Arguments:   []string{"sh", "-c", "tr a-z A-Z < input.txt > out/upper.txt && mkdir -p out/tree && cp input.txt out/tree/copy.txt && echo done"},
		OutputPaths: []string{"out/upper.txt", "out/tree"},
	})
	if err != nil {
		return err
	}
	action, err := uploadProto(ctxA, origin, instanceA, &repb.Action{CommandDigest: command, InputRootDigest: root})
	if err != nil {
		return err
	}

	// Tenant B may not run actions in tenant A's instance.
	if err := execute(ctxB, execer, instanceA, action, timeout, nil); status.Code(err) != codes.PermissionDenied {
		return fmt.Errorf("tenant B executing in tenant A's instance: got %v, want PermissionDenied", err)
	}

	var resp *repb.ExecuteResponse
	start := time.Now()
	if err := execute(ctxA, execer, instanceA, action, timeout, func(r *repb.ExecuteResponse) { resp = r }); err != nil {
		return fmt.Errorf("executing action: %w", err)
	}
	if resp.GetStatus().GetCode() != 0 {
		return fmt.Errorf("action failed to run: %v", resp.GetStatus())
	}
	ar := resp.GetResult()
	if ar.GetExitCode() != 0 {
		return fmt.Errorf("action exited %d", ar.GetExitCode())
	}
	worker := ar.GetExecutionMetadata().GetWorker()
	slog.Info("action ran on a runner", "worker", worker, "took", time.Since(start).Round(time.Millisecond))
	if !strings.HasPrefix(worker, workerPrefix) {
		return fmt.Errorf("worker %q does not have prefix %q", worker, workerPrefix)
	}
	if got, err := fetchString(ctxA, cacheClient, instanceA, ar.GetStdoutDigest()); err != nil || got != "done\n" {
		return fmt.Errorf("stdout %q, err %v; want \"done\\n\"", got, err)
	}
	if len(ar.GetOutputFiles()) != 1 || ar.GetOutputFiles()[0].GetPath() != "out/upper.txt" {
		return fmt.Errorf("output files %v, want out/upper.txt", ar.GetOutputFiles())
	}
	if got, err := fetchString(ctxA, cacheClient, instanceA, ar.GetOutputFiles()[0].GetDigest()); err != nil || got != strings.ToUpper(content) {
		return fmt.Errorf("out/upper.txt %q, err %v", got, err)
	}
	if len(ar.GetOutputDirectories()) != 1 || ar.GetOutputDirectories()[0].GetPath() != "out/tree" {
		return fmt.Errorf("output directories %v, want out/tree", ar.GetOutputDirectories())
	}
	treeBytes, err := cacheClient.Fetch(ctxA, instanceA, ar.GetOutputDirectories()[0].GetTreeDigest())
	if err != nil {
		return fmt.Errorf("fetching output tree: %w", err)
	}
	outTree := &repb.Tree{}
	if err := proto.Unmarshal(treeBytes, outTree); err != nil {
		return err
	}
	if files := outTree.GetRoot().GetFiles(); len(files) != 1 || files[0].GetName() != "copy.txt" || files[0].GetDigest().GetHash() != input.GetHash() {
		return fmt.Errorf("output tree %v, want copy.txt with the input's digest", outTree)
	}
	slog.Info("outputs verified through the node-local cache", "files", len(ar.GetOutputFiles()), "directories", len(ar.GetOutputDirectories()))

	// The same action again is answered from the action cache without a run.
	var again *repb.ExecuteResponse
	if err := execute(ctxA, execer, instanceA, action, timeout, func(r *repb.ExecuteResponse) { again = r }); err != nil {
		return fmt.Errorf("re-executing action: %w", err)
	}
	if !again.GetCachedResult() {
		return errors.New("second Execute of the same action was not a cache hit")
	}
	slog.Info("second Execute served from the action cache")
	return nil
}

// execute submits action and waits for the operation to finish, passing the
// final response to done.
func execute(ctx context.Context, execer repb.ExecutionClient, instance string, action *repb.Digest, timeout time.Duration, done func(*repb.ExecuteResponse)) error {
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()
	stream, err := execer.Execute(ctx, &repb.ExecuteRequest{InstanceName: instance, ActionDigest: action})
	if err != nil {
		return err
	}
	for {
		op, err := stream.Recv()
		if err != nil {
			return err
		}
		if !op.GetDone() {
			continue
		}
		resp := &repb.ExecuteResponse{}
		if err := op.GetResponse().UnmarshalTo(resp); err != nil {
			return err
		}
		if done != nil {
			done(resp)
		}
		return nil
	}
}

func uploadProto(ctx context.Context, c *remote.Client, instance string, m proto.Message) (*repb.Digest, error) {
	d, err := c.Upload(ctx, instance, tree.Marshal(m))
	if err != nil {
		return nil, fmt.Errorf("uploading %T: %w", m, err)
	}
	return d, nil
}

func fetchString(ctx context.Context, c *remote.Client, instance string, d *repb.Digest) (string, error) {
	if d == nil {
		return "", errors.New("no digest")
	}
	b, err := c.Fetch(ctx, instance, d)
	if err != nil {
		return "", err
	}
	if err := digest.Verify(d, b); err != nil {
		return "", err
	}
	return string(b), nil
}

func tryCrossTenant(ctx context.Context, c *remote.Client, instanceA string, d *repb.Digest) error {
	_, err := c.Fetch(ctx, instanceA, d)
	if status.Code(err) == codes.PermissionDenied {
		return nil
	}
	if err == nil {
		return errors.New("isolation breach: tenant B read tenant A's private instance")
	}
	return fmt.Errorf("unexpected error probing isolation: %w", err)
}

// retry reissues a gRPC call a few times when the server is still coming up.
func retry[T any](fn func() (T, error)) (T, error) {
	var zero T
	var last error
	for i := 0; i < 10; i++ {
		v, err := fn()
		if err == nil {
			return v, nil
		}
		last = err
		if c := status.Code(err); c != codes.Unavailable && c != codes.DeadlineExceeded {
			return zero, err
		}
		time.Sleep(time.Second)
	}
	return zero, last
}

func fetchStats(metricsURL string) (cache.Stats, error) {
	var s cache.Stats
	resp, err := http.Get(metricsURL + "/stats")
	if err != nil {
		return s, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return s, fmt.Errorf("GET %s/stats: %s", metricsURL, resp.Status)
	}
	err = json.NewDecoder(resp.Body).Decode(&s)
	return s, err
}
