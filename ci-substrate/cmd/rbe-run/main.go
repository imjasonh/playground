// Command rbe-run sends one raw Remote Execution API call to cas: it uploads
// a bash script as an Action, executes it, and prints what the runner wrote.
// It shows how a client with no build system asks for work that can't be
// cached, by setting Action.do_not_cache.
//
//	rbe-run -addr 127.0.0.1:18980 -runs 3
//
// With the default script (the current time), each run prints a new time and
// reports that a runner ran it. With -cacheable the action is an ordinary
// one: the first run executes and every later run is answered from the
// action cache with the first run's time.
package main

import (
	"context"
	"errors"
	"flag"
	"fmt"
	"log/slog"
	"os"
	"strings"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
	"github.com/imjasonh/playground/ci-substrate/internal/tree"
)

func main() {
	addr := flag.String("addr", "", "cas address (host:port)")
	instance := flag.String("instance", "tenant-a", "REAPI instance name")
	token := flag.String("token", "tok-a", "tenant token for the instance")
	script := flag.String("script", `date -u +%Y-%m-%dT%H:%M:%SZ`, "bash script to run")
	runs := flag.Int("runs", 3, "how many times to execute the action")
	cacheable := flag.Bool("cacheable", false, "leave do_not_cache unset, so the action cache can answer")
	timeout := flag.Duration("timeout", 2*time.Minute, "how long to wait for each run")
	flag.Parse()

	if *addr == "" {
		slog.Error("missing required flag", "need", "-addr")
		os.Exit(2)
	}
	if err := run(*addr, *instance, *token, *script, *runs, *cacheable, *timeout); err != nil {
		slog.Error("rbe-run failed", "err", err)
		os.Exit(1)
	}
}

func run(addr, instance, token, script string, runs int, cacheable bool, timeout time.Duration) error {
	conn, err := grpc.NewClient(addr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		return err
	}
	defer conn.Close()
	cas := remote.NewClient(conn)
	execer := repb.NewExecutionClient(conn)
	ctx := tenant.Outgoing(context.Background(), token)

	command, err := cas.Upload(ctx, instance, tree.Marshal(&repb.Command{Arguments: []string{"bash", "-c", script}}))
	if err != nil {
		return fmt.Errorf("uploading command: %w", err)
	}
	inputRoot, err := cas.Upload(ctx, instance, tree.Marshal(&repb.Directory{}))
	if err != nil {
		return fmt.Errorf("uploading input root: %w", err)
	}
	action, err := cas.Upload(ctx, instance, tree.Marshal(&repb.Action{
		CommandDigest:   command,
		InputRootDigest: inputRoot,
		DoNotCache:      !cacheable,
	}))
	if err != nil {
		return fmt.Errorf("uploading action: %w", err)
	}
	slog.Info("uploaded action", "action", digest.Key(action), "doNotCache", !cacheable, "script", script)

	for i := 1; i <= runs; i++ {
		resp, took, err := execute(ctx, execer, instance, action, timeout)
		if err != nil {
			return fmt.Errorf("run %d: %w", i, err)
		}
		if resp.GetStatus().GetCode() != 0 {
			return fmt.Errorf("run %d did not run: %v", i, resp.GetStatus())
		}
		ar := resp.GetResult()
		stdout, err := fetch(ctx, cas, instance, ar.GetStdoutDigest())
		if err != nil {
			return fmt.Errorf("run %d stdout: %w", i, err)
		}
		slog.Info("executed",
			"run", i,
			"stdout", strings.TrimSpace(stdout),
			"cachedResult", resp.GetCachedResult(),
			"worker", ar.GetExecutionMetadata().GetWorker(),
			"exitCode", ar.GetExitCode(),
			"took", took.Round(time.Millisecond),
		)
		time.Sleep(1100 * time.Millisecond)
	}
	return nil
}

// execute runs action and returns the final response and how long the call
// took.
func execute(ctx context.Context, execer repb.ExecutionClient, instance string, action *repb.Digest, timeout time.Duration) (*repb.ExecuteResponse, time.Duration, error) {
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()
	start := time.Now()
	stream, err := execer.Execute(ctx, &repb.ExecuteRequest{InstanceName: instance, ActionDigest: action})
	if err != nil {
		return nil, 0, err
	}
	for {
		op, err := stream.Recv()
		if err != nil {
			return nil, 0, err
		}
		if !op.GetDone() {
			continue
		}
		resp := &repb.ExecuteResponse{}
		if err := op.GetResponse().UnmarshalTo(resp); err != nil {
			return nil, 0, err
		}
		return resp, time.Since(start), nil
	}
}

func fetch(ctx context.Context, c *remote.Client, instance string, d *repb.Digest) (string, error) {
	if d == nil {
		return "", errors.New("the result has no stdout digest")
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
