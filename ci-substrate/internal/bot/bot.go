// Package bot runs leased actions. A Bot asks the scheduler for jobs with its
// tenant token, builds each action's exec root from the node-local cache,
// runs the command, and sends back an ActionResult whose outputs it uploaded
// to the origin.
//
// Output handling follows the plan's rules: every output file, the Tree of
// every output directory, and stdout and stderr become blobs; FindMissingBlobs
// trims the set to what the CAS lacks; small blobs go in batches and large
// ones over ByteStream (the client decides per blob). A failed action still
// reports its outputs and exit code, so a client can show what went wrong.
package bot

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"io/fs"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/known/anypb"
	"google.golang.org/protobuf/types/known/timestamppb"

	workerv1 "github.com/imjasonh/playground/ci-substrate/api/worker/v1"
	"github.com/imjasonh/playground/ci-substrate/internal/casfs"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
	"github.com/imjasonh/playground/ci-substrate/internal/tree"
)

// InputMode selects how the exec root is built.
type InputMode string

const (
	// InputCopy writes every input file before the action starts.
	InputCopy InputMode = "copy"
	// InputFUSE mounts the input root with casfs and fetches files as the
	// action reads them.
	InputFUSE InputMode = "fuse"
	// InputAuto uses FUSE when /dev/fuse is present, and copies otherwise.
	InputAuto InputMode = "auto"
)

// Config wires a Bot.
type Config struct {
	// BotID identifies this runner to the scheduler. Under Substrate it is
	// the actor name.
	BotID string
	// Token is the tenant token sent on every call. Under Substrate it is a
	// placeholder that the egress gateway replaces.
	Token string
	// Instances narrows which instances the bot leases from. Empty means
	// every instance its token allows.
	Instances []string
	// Worker is the scheduler's lease protocol.
	Worker workerv1.WorkerServiceClient
	// Origin receives uploads.
	Origin *remote.Client
	// Cache serves reads. It is usually the node-local cascache, and may be
	// the origin when there is none.
	Cache tree.Fetcher
	// WorkDir holds one exec root per job.
	WorkDir string
	// InputMode selects how the exec root is built.
	InputMode InputMode
	// LeaseWait bounds each Lease call. Zero means the scheduler's default.
	LeaseWait time.Duration
}

// Bot runs leased actions until its context ends.
type Bot struct {
	cfg   Config
	cache tree.Fetcher
}

// tokenFetcher sends the tenant token with every read. casfs calls Fetch
// with the kernel's request context, which carries no token.
type tokenFetcher struct {
	f     tree.Fetcher
	token string
}

func (t tokenFetcher) Fetch(ctx context.Context, instance string, d *repb.Digest) ([]byte, error) {
	return t.f.Fetch(tenant.Outgoing(ctx, t.token), instance, d)
}

// New returns a Bot. It fails when the configuration cannot work on this
// host, such as InputFUSE with no /dev/fuse.
func New(cfg Config) (*Bot, error) {
	if cfg.BotID == "" || cfg.Worker == nil || cfg.Origin == nil || cfg.Cache == nil || cfg.WorkDir == "" {
		return nil, errors.New("bot: BotID, Worker, Origin, Cache, and WorkDir are required")
	}
	switch cfg.InputMode {
	case InputCopy, InputFUSE:
	case InputAuto, "":
		cfg.InputMode = InputCopy
		if fuseAvailable() {
			cfg.InputMode = InputFUSE
		}
	default:
		return nil, fmt.Errorf("bot: unknown input mode %q", cfg.InputMode)
	}
	if cfg.InputMode == InputFUSE && !fuseAvailable() {
		return nil, errors.New("bot: input mode fuse needs /dev/fuse")
	}
	if cfg.LeaseWait <= 0 {
		cfg.LeaseWait = 20 * time.Second
	}
	if err := os.MkdirAll(cfg.WorkDir, 0o755); err != nil {
		return nil, err
	}
	return &Bot{cfg: cfg, cache: tokenFetcher{f: cfg.Cache, token: cfg.Token}}, nil
}

func fuseAvailable() bool {
	_, err := os.Stat("/dev/fuse")
	return err == nil
}

// InputMode reports how the bot builds exec roots.
func (b *Bot) InputMode() InputMode { return b.cfg.InputMode }

// Run leases and runs jobs until ctx ends. Errors from the scheduler are
// logged and retried; the loop only returns with ctx's error.
func (b *Bot) Run(ctx context.Context) error {
	ctx = tenant.Outgoing(ctx, b.cfg.Token)
	for {
		if err := ctx.Err(); err != nil {
			return err
		}
		job, err := b.lease(ctx)
		if err != nil {
			if ctx.Err() != nil {
				return ctx.Err()
			}
			slog.Warn("lease failed; retrying", "err", err)
			select {
			case <-ctx.Done():
				return ctx.Err()
			case <-time.After(time.Second):
			}
			continue
		}
		if job == nil {
			continue
		}
		b.RunJob(ctx, job)
	}
}

// RunOnce leases at most one job and runs it. It reports whether a job ran.
func (b *Bot) RunOnce(ctx context.Context) (bool, error) {
	ctx = tenant.Outgoing(ctx, b.cfg.Token)
	job, err := b.lease(ctx)
	if err != nil || job == nil {
		return false, err
	}
	b.RunJob(ctx, job)
	return true, nil
}

func (b *Bot) lease(ctx context.Context) (*workerv1.Job, error) {
	ctx, cancel := context.WithTimeout(ctx, b.cfg.LeaseWait)
	defer cancel()
	resp, err := b.cfg.Worker.Lease(ctx, &workerv1.LeaseRequest{BotId: b.cfg.BotID, InstanceNames: b.cfg.Instances})
	if err != nil {
		return nil, err
	}
	return resp.GetJob(), nil
}

// RunJob runs one leased job and reports its outcome to the scheduler,
// heartbeating while it runs.
func (b *Bot) RunJob(ctx context.Context, job *workerv1.Job) {
	ctx, cancel := context.WithCancel(tenant.Outgoing(ctx, b.cfg.Token))
	defer cancel()
	go b.heartbeat(ctx, cancel, job)

	start := time.Now()
	ar, err := b.execute(ctx, job)
	req := &workerv1.CompleteRequest{BotId: b.cfg.BotID, JobId: job.GetId()}
	if err != nil {
		slog.Error("action failed to run", "job", job.GetId(), "err", err)
		req.ErrorMessage = err.Error()
	} else if anyAR, err := anypb.New(ar); err != nil {
		req.ErrorMessage = err.Error()
	} else {
		req.ActionResult = anyAR
		slog.Info("action ran", "job", job.GetId(), "exitCode", ar.GetExitCode(), "took", time.Since(start))
	}
	// Report with a context that outlives a cancelled lease, so a result
	// is not lost to the cancel that stopped the heartbeat.
	reportCtx, reportCancel := context.WithTimeout(context.WithoutCancel(ctx), 30*time.Second)
	defer reportCancel()
	if _, err := b.cfg.Worker.Complete(reportCtx, req); err != nil {
		slog.Error("reporting result", "job", job.GetId(), "err", err)
	}
}

// heartbeat renews the lease every third of its duration and cancels the job
// when the scheduler says the lease is gone.
func (b *Bot) heartbeat(ctx context.Context, cancel context.CancelFunc, job *workerv1.Job) {
	interval := job.GetLeaseDuration().AsDuration() / 3
	if interval <= 0 {
		interval = 10 * time.Second
	}
	tick := time.NewTicker(interval)
	defer tick.Stop()
	for {
		select {
		case <-ctx.Done():
			return
		case <-tick.C:
			resp, err := b.cfg.Worker.Heartbeat(ctx, &workerv1.HeartbeatRequest{BotId: b.cfg.BotID, JobId: job.GetId()})
			if err != nil {
				if status.Code(err) == codes.Canceled {
					return
				}
				slog.Warn("heartbeat failed", "job", job.GetId(), "err", err)
				continue
			}
			if resp.GetCancelled() {
				slog.Warn("lease cancelled; stopping action", "job", job.GetId())
				cancel()
				return
			}
		}
	}
}

// execute builds the exec root, runs the command, and uploads the outputs.
func (b *Bot) execute(ctx context.Context, job *workerv1.Job) (*repb.ActionResult, error) {
	instance := job.GetInstanceName()
	actionDigest := &repb.Digest{Hash: job.GetActionDigest().GetHash(), SizeBytes: job.GetActionDigest().GetSizeBytes()}
	action := &repb.Action{}
	if err := b.fetchProto(ctx, instance, actionDigest, action); err != nil {
		return nil, fmt.Errorf("action: %w", err)
	}
	command := &repb.Command{}
	if err := b.fetchProto(ctx, instance, action.GetCommandDigest(), command); err != nil {
		return nil, fmt.Errorf("command: %w", err)
	}
	if len(command.GetArguments()) == 0 {
		return nil, errors.New("command has no arguments")
	}
	rootDigest := action.GetInputRootDigest()
	if rootDigest == nil {
		rootDigest = tree.Digest(&repb.Directory{})
	}
	var inputs *tree.Tree
	if rootDigest.GetSizeBytes() == 0 {
		inputs = &tree.Tree{Root: rootDigest, Dirs: map[string]*repb.Directory{digest.Key(rootDigest): {}}}
	} else {
		var err error
		inputs, err = tree.Load(ctx, b.cache, instance, rootDigest)
		if err != nil {
			return nil, fmt.Errorf("input root: %w", err)
		}
	}

	jobDir, err := os.MkdirTemp(b.cfg.WorkDir, "job-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(jobDir)
	execRoot := filepath.Join(jobDir, "root")
	if err := os.MkdirAll(execRoot, 0o755); err != nil {
		return nil, err
	}
	md := &repb.ExecutedActionMetadata{Worker: b.cfg.BotID, InputFetchStartTimestamp: timestamppb.Now()}
	switch b.cfg.InputMode {
	case InputFUSE:
		server, err := casfs.Mount(execRoot, inputs, b.cache, instance)
		if err != nil {
			return nil, fmt.Errorf("mounting input root: %w", err)
		}
		defer func() {
			if err := server.Unmount(); err != nil {
				slog.Warn("unmounting exec root", "dir", execRoot, "err", err)
			}
		}()
	default:
		if err := tree.Materialize(ctx, b.cache, instance, inputs, execRoot); err != nil {
			return nil, fmt.Errorf("materializing input root: %w", err)
		}
	}
	md.InputFetchCompletedTimestamp = timestamppb.Now()

	workDir, err := within(execRoot, command.GetWorkingDirectory())
	if err != nil {
		return nil, err
	}
	if err := os.MkdirAll(workDir, 0o755); err != nil {
		return nil, err
	}
	// Create the parents of every output path, as the API requires.
	for _, p := range outputPaths(command) {
		full, err := within(workDir, p)
		if err != nil {
			return nil, err
		}
		if err := os.MkdirAll(filepath.Dir(full), 0o755); err != nil {
			return nil, err
		}
	}

	runCtx := ctx
	if timeout := action.GetTimeout(); timeout != nil && timeout.AsDuration() > 0 {
		var cancel context.CancelFunc
		runCtx, cancel = context.WithTimeout(ctx, timeout.AsDuration())
		defer cancel()
	}
	cmd := exec.CommandContext(runCtx, command.GetArguments()[0], command.GetArguments()[1:]...)
	cmd.Dir = workDir
	cmd.Env = environment(command)
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	md.ExecutionStartTimestamp = timestamppb.Now()
	runErr := cmd.Run()
	md.ExecutionCompletedTimestamp = timestamppb.Now()
	ar := &repb.ActionResult{ExecutionMetadata: md}
	var exitErr *exec.ExitError
	switch {
	case runErr == nil:
	case errors.As(runErr, &exitErr):
		ar.ExitCode = int32(exitErr.ExitCode())
	case runCtx.Err() != nil && ctx.Err() == nil:
		return nil, status.Error(codes.DeadlineExceeded, "action timed out")
	default:
		return nil, fmt.Errorf("starting command: %w", runErr)
	}

	md.OutputUploadStartTimestamp = timestamppb.Now()
	if err := b.collectOutputs(ctx, instance, workDir, command, ar, stdout.Bytes(), stderr.Bytes()); err != nil {
		return nil, fmt.Errorf("uploading outputs: %w", err)
	}
	md.OutputUploadCompletedTimestamp = timestamppb.Now()
	return ar, nil
}

// fetchProto reads and verifies a message from the cache.
func (b *Bot) fetchProto(ctx context.Context, instance string, d *repb.Digest, m proto.Message) error {
	if err := digest.Validate(d); err != nil {
		return err
	}
	raw, err := b.cache.Fetch(ctx, instance, d)
	if err != nil {
		return err
	}
	if err := digest.Verify(d, raw); err != nil {
		return err
	}
	return proto.Unmarshal(raw, m)
}

// within joins rel onto root and refuses paths that would leave it.
func within(root, rel string) (string, error) {
	if filepath.IsAbs(rel) {
		return "", fmt.Errorf("path %q is absolute", rel)
	}
	full := filepath.Join(root, rel)
	if full != root && !strings.HasPrefix(full, root+string(filepath.Separator)) {
		return "", fmt.Errorf("path %q escapes the exec root", rel)
	}
	return full, nil
}

// outputPaths lists the paths the command declares, in the v2.1 output_paths
// field or the older output_files and output_directories.
func outputPaths(c *repb.Command) []string {
	if len(c.GetOutputPaths()) > 0 {
		return c.GetOutputPaths()
	}
	return append(append([]string{}, c.GetOutputFiles()...), c.GetOutputDirectories()...)
}

// environment is the command's environment. PATH gets a default when the
// command sets none, so a bare `sh` resolves.
func environment(c *repb.Command) []string {
	env := []string{}
	hasPath := false
	for _, kv := range c.GetEnvironmentVariables() {
		if kv.GetName() == "PATH" {
			hasPath = true
		}
		env = append(env, kv.GetName()+"="+kv.GetValue())
	}
	if !hasPath {
		env = append(env, "PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin")
	}
	return env
}

// collectOutputs reads every declared output, builds the ActionResult's
// output lists, and uploads the blobs the CAS does not already hold.
func (b *Bot) collectOutputs(ctx context.Context, instance, workDir string, command *repb.Command, ar *repb.ActionResult, stdout, stderr []byte) error {
	blobs := map[string][]byte{}
	add := func(data []byte) *repb.Digest {
		d := digest.FromBytes(data)
		blobs[digest.Key(d)] = data
		return d
	}
	if len(stdout) > 0 {
		ar.StdoutDigest = add(stdout)
	}
	if len(stderr) > 0 {
		ar.StderrDigest = add(stderr)
	}
	for _, p := range outputPaths(command) {
		full, err := within(workDir, p)
		if err != nil {
			return err
		}
		info, err := os.Lstat(full)
		if errors.Is(err, fs.ErrNotExist) {
			// An output the action did not produce is left out, as the API
			// specifies, rather than failing the action.
			continue
		}
		if err != nil {
			return err
		}
		switch {
		case info.Mode()&fs.ModeSymlink != 0:
			target, err := os.Readlink(full)
			if err != nil {
				return err
			}
			ar.OutputSymlinks = append(ar.OutputSymlinks, &repb.OutputSymlink{Path: p, Target: target})
		case info.IsDir():
			out, err := tree.FromDir(full)
			if err != nil {
				return err
			}
			for k, v := range out.Blobs {
				blobs[k] = v
			}
			ar.OutputDirectories = append(ar.OutputDirectories, &repb.OutputDirectory{Path: p, TreeDigest: add(tree.Marshal(out.Tree))})
		default:
			data, err := os.ReadFile(full)
			if err != nil {
				return err
			}
			ar.OutputFiles = append(ar.OutputFiles, &repb.OutputFile{Path: p, Digest: add(data), IsExecutable: info.Mode()&0o111 != 0})
		}
	}
	return b.upload(ctx, instance, blobs)
}

// upload sends the blobs the CAS is missing. Each blob goes through
// remote.Client.Upload, which batches small blobs and streams large ones.
func (b *Bot) upload(ctx context.Context, instance string, blobs map[string][]byte) error {
	if len(blobs) == 0 {
		return nil
	}
	var digests []*repb.Digest
	for _, data := range blobs {
		digests = append(digests, digest.FromBytes(data))
	}
	missing, err := b.cfg.Origin.FindMissing(ctx, instance, digests)
	if err != nil {
		return err
	}
	var sent int64
	for _, d := range missing {
		if _, err := b.cfg.Origin.Upload(ctx, instance, blobs[digest.Key(d)]); err != nil {
			return fmt.Errorf("uploading %s: %w", digest.Key(d), err)
		}
		sent += d.GetSizeBytes()
	}
	slog.Info("uploaded outputs", "blobs", len(blobs), "missing", len(missing), "bytes", sent)
	return nil
}
