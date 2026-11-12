// Command runner is the in-actor CI/build runner. It is the binary a build
// actor runs: it reads its inputs from the node-local cache, checks the action
// cache, executes the command on a miss, and pushes the outputs and a new
// action-cache entry to the origin. It demonstrates the output-handling rules
// from the plan: small blobs go through BatchUpdateBlobs and large ones
// through ByteStream, and FindMissingBlobs skips blobs the CAS already holds.
package main

import (
	"context"
	"flag"
	"log/slog"
	"os"
	"os/exec"
	"slices"
	"strings"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/protobuf/proto"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

func main() {
	cacheAddr := flag.String("cache-addr", "", "node-local cascache address for reads (host:port)")
	originAddr := flag.String("origin-addr", "", "origin cas address for writes and the action cache (host:port)")
	instance := flag.String("instance", "", "Remote Execution instance name (the tenant's instance)")
	token := flag.String("token", "", "tenant token")
	command := flag.String("command", "", "command to run, via sh -c")
	inputs := flag.String("inputs", "", "comma-separated hash/size digests to prefetch from the node-local cache")
	flag.Parse()

	if *originAddr == "" || *command == "" {
		slog.Error("missing required flags", "need", "-origin-addr and -command")
		os.Exit(2)
	}
	ctx := tenant.Outgoing(context.Background(), *token)

	originConn, err := grpc.NewClient(*originAddr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		slog.Error("dialing origin", "err", err)
		os.Exit(1)
	}
	defer originConn.Close()
	origin := remote.NewClient(originConn)

	// Prefetch inputs from the node-local cache, proving reads are served near
	// the actor. Each read is verified against its digest by the cache.
	var inputDigests []*repb.Digest
	if *inputs != "" {
		addr := *cacheAddr
		if addr == "" {
			addr = *originAddr
		}
		cacheConn, err := grpc.NewClient(addr, grpc.WithTransportCredentials(insecure.NewCredentials()))
		if err != nil {
			slog.Error("dialing cache", "err", err)
			os.Exit(1)
		}
		defer cacheConn.Close()
		cacheClient := remote.NewClient(cacheConn)
		for _, in := range strings.Split(*inputs, ",") {
			d, err := parseDigest(in)
			if err != nil {
				slog.Error("bad input digest", "input", in, "err", err)
				os.Exit(2)
			}
			b, err := cacheClient.Fetch(ctx, *instance, d)
			if err != nil {
				slog.Error("prefetch input", "digest", in, "err", err)
				os.Exit(1)
			}
			slog.Info("prefetched input from node-local cache", "digest", in, "bytes", len(b))
			inputDigests = append(inputDigests, d)
		}
	}

	// Describe the action and look it up in the action cache first. The
	// action names its inputs through an input root, so the same command over
	// different inputs is a different action.
	cmdDigest, err := uploadProto(ctx, origin, *instance, &repb.Command{Arguments: []string{"sh", "-c", *command}})
	if err != nil {
		slog.Error("uploading command", "err", err)
		os.Exit(1)
	}
	rootDigest, err := uploadProto(ctx, origin, *instance, inputRoot(inputDigests))
	if err != nil {
		slog.Error("uploading input root", "err", err)
		os.Exit(1)
	}
	actionDigest, err := uploadProto(ctx, origin, *instance, &repb.Action{CommandDigest: cmdDigest, InputRootDigest: rootDigest})
	if err != nil {
		slog.Error("uploading action", "err", err)
		os.Exit(1)
	}

	if ar, ok, err := origin.GetActionResult(ctx, *instance, actionDigest); err != nil {
		slog.Error("checking action cache", "err", err)
		os.Exit(1)
	} else if ok {
		slog.Info("action cache hit; skipping execution", "action", digest.Key(actionDigest), "exitCode", ar.GetExitCode())
		if err := replay(ctx, origin, *instance, ar); err != nil {
			slog.Error("replaying cached output", "err", err)
			os.Exit(1)
		}
		os.Exit(int(ar.GetExitCode()))
	}

	// Cache miss: execute, then push the result.
	slog.Info("action cache miss; executing", "action", digest.Key(actionDigest))
	cmd := exec.CommandContext(ctx, "sh", "-c", *command)
	stdout, runErr := cmd.Output()
	var exitCode int32
	var stderr []byte
	if ee, ok := runErr.(*exec.ExitError); ok {
		exitCode = int32(ee.ExitCode())
		stderr = ee.Stderr
	} else if runErr != nil {
		slog.Error("executing command", "err", runErr)
		os.Exit(1)
	}

	stdoutDigest, err := origin.Upload(ctx, *instance, stdout)
	if err != nil {
		slog.Error("uploading stdout", "err", err)
		os.Exit(1)
	}
	ar := &repb.ActionResult{
		ExitCode:     exitCode,
		StdoutDigest: stdoutDigest,
	}
	if len(stderr) > 0 {
		stderrDigest, err := origin.Upload(ctx, *instance, stderr)
		if err != nil {
			slog.Error("uploading stderr", "err", err)
			os.Exit(1)
		}
		ar.StderrDigest = stderrDigest
	}
	if err := origin.UpdateActionResult(ctx, *instance, actionDigest, ar); err != nil {
		slog.Error("updating action cache", "err", err)
		os.Exit(1)
	}
	slog.Info("executed and cached action", "action", digest.Key(actionDigest), "exitCode", exitCode, "stdoutBytes", len(stdout))
	os.Stdout.Write(stdout)
	os.Stderr.Write(stderr)
	os.Exit(int(exitCode))
}

// uploadProto stores m under its digest. Marshaling is deterministic so the
// same message always has the same digest, which the action cache relies on.
func uploadProto(ctx context.Context, c *remote.Client, instance string, m proto.Message) (*repb.Digest, error) {
	b, err := proto.MarshalOptions{Deterministic: true}.Marshal(m)
	if err != nil {
		return nil, err
	}
	return c.Upload(ctx, instance, b)
}

// inputRoot lists the prefetched inputs as files named by their hashes, in
// the sorted order the Remote Execution API requires of a Directory.
func inputRoot(inputs []*repb.Digest) *repb.Directory {
	dir := &repb.Directory{}
	for _, d := range inputs {
		dir.Files = append(dir.Files, &repb.FileNode{Name: d.GetHash(), Digest: d})
	}
	slices.SortFunc(dir.Files, func(a, b *repb.FileNode) int { return strings.Compare(a.GetName(), b.GetName()) })
	dir.Files = slices.CompactFunc(dir.Files, func(a, b *repb.FileNode) bool { return a.GetName() == b.GetName() })
	return dir
}

// replay writes a cached action's stdout and stderr, so a cache hit looks the
// same to the caller as the run that produced it.
func replay(ctx context.Context, c *remote.Client, instance string, ar *repb.ActionResult) error {
	for _, out := range []struct {
		d *repb.Digest
		w *os.File
	}{{ar.GetStdoutDigest(), os.Stdout}, {ar.GetStderrDigest(), os.Stderr}} {
		if out.d == nil {
			continue
		}
		b, err := c.Fetch(ctx, instance, out.d)
		if err != nil {
			return err
		}
		if err := digest.Verify(out.d, b); err != nil {
			return err
		}
		if _, err := out.w.Write(b); err != nil {
			return err
		}
	}
	return nil
}

func parseDigest(s string) (*repb.Digest, error) {
	_, d, err := remote.ParseReadResource("blobs/" + s)
	return d, err
}
