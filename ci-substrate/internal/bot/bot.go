// Package bot runs leased actions. A Bot asks the scheduler for jobs with its
// tenant token, builds each action's exec root from the node-local cache,
// runs the command, and sends back an ActionResult whose outputs it uploaded
// to the origin.
//
// Every output file, the Tree of every output directory, and stdout and
// stderr become blobs, uploaded in one PutBatch. A failed action still
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
	"github.com/chainguard-dev/clog"
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
	// InputVolume makes the exec root on a casfs inputs volume that the host
	// mounted (Config.InputsVolume): a mkdir of the input root's digest
	// materializes it there, with files fetched on the host side as the
	// action reads them, and an rmdir drops it. The runner itself fetches
	// no input bytes. A Substrate actor, which can't mount FUSE, gets lazy
	// hydration from its own node this way.
	InputVolume InputMode = "volume"
	// InputAuto uses the inputs volume when one is configured and answers,
	// else FUSE when /dev/fuse is present, else copies.
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
	// WorkDir holds one exec root per job, in the copy and FUSE modes.
	WorkDir string
	// InputMode selects how the exec root is built.
	InputMode InputMode
	// InputsVolume is the mounted casfs inputs volume that InputVolume
	// makes exec roots on.
	InputsVolume string
	// LeaseWait bounds each Lease call. Zero means the scheduler's default.
	LeaseWait time.Duration
}

// Bot runs leased actions until its context ends.
type Bot struct {
	cfg   Config
	cache tree.Fetcher
	// shell is the absolute path of bash. Every action starts through it, so
	// the runner process never changes into an exec root it serves itself.
	shell string
}

// New returns a Bot. It fails when the configuration cannot work on this
// host, such as InputFUSE with no /dev/fuse, InputVolume with a volume that
// does not answer, or a host with no bash to start commands through.
func New(cfg Config) (*Bot, error) {
	if cfg.BotID == "" || cfg.Worker == nil || cfg.Origin == nil || cfg.Cache == nil || cfg.WorkDir == "" {
		return nil, errors.New("bot: BotID, Worker, Origin, Cache, and WorkDir are required")
	}
	if cfg.LeaseWait <= 0 {
		cfg.LeaseWait = 20 * time.Second
	}
	if err := os.MkdirAll(cfg.WorkDir, 0o755); err != nil {
		return nil, err
	}
	switch cfg.InputMode {
	case InputCopy:
	case InputFUSE:
		if err := probeFUSE(cfg.WorkDir); err != nil {
			return nil, fmt.Errorf("bot: input mode fuse: %w", err)
		}
	case InputVolume:
		if cfg.InputsVolume == "" {
			return nil, errors.New("bot: input mode volume needs InputsVolume")
		}
		if err := probeVolume(cfg.InputsVolume); err != nil {
			return nil, fmt.Errorf("bot: input mode volume: %w", err)
		}
	case InputAuto, "":
		switch {
		case cfg.InputsVolume != "" && probeVolume(cfg.InputsVolume) == nil:
			cfg.InputMode = InputVolume
		case probeFUSE(cfg.WorkDir) == nil:
			cfg.InputMode = InputFUSE
		default:
			slog.Info("no inputs volume and no FUSE; copying inputs")
			cfg.InputMode = InputCopy
		}
	default:
		return nil, fmt.Errorf("bot: unknown input mode %q", cfg.InputMode)
	}
	shell, err := exec.LookPath("bash")
	if err != nil {
		return nil, fmt.Errorf("bot: finding bash: %w", err)
	}
	return &Bot{cfg: cfg, cache: tree.WithToken(cfg.Cache, cfg.Token), shell: shell}, nil
}

// probeVolume materializes the empty input root on the volume and drops it,
// so a volume that is not a casfs mount, or whose server is gone, is found
// out at startup. A plain directory accepts the mkdir but would serve no
// inputs, so the probe also checks that the volume refuses a name that is
// not a digest.
func probeVolume(dir string) error {
	probe := filepath.Join(dir, casfs.ExecRootName(tree.Digest(&repb.Directory{}), "probe"))
	if err := os.Mkdir(probe, 0o755); err != nil {
		return err
	}
	if err := os.Remove(probe); err != nil {
		return err
	}
	if err := os.Mkdir(filepath.Join(dir, "not-a-digest"), 0o755); err == nil {
		os.Remove(filepath.Join(dir, "not-a-digest"))
		return fmt.Errorf("%s is not a casfs volume", dir)
	}
	return nil
}

// probeFUSE mounts an empty tree under dir and unmounts it, so a host that
// has /dev/fuse but not the privilege to mount is found out at startup
// rather than on the first job.
func probeFUSE(dir string) error {
	if _, err := os.Stat("/dev/fuse"); err != nil {
		return err
	}
	mnt, err := os.MkdirTemp(dir, "fuse-probe-")
	if err != nil {
		return err
	}
	defer os.Remove(mnt)
	empty := tree.Digest(&repb.Directory{})
	server, err := casfs.Mount(mnt, &tree.Tree{Root: empty, Dirs: map[string]*repb.Directory{digest.Key(empty): {}}}, noFetcher{}, "")
	if err != nil {
		return err
	}
	return server.Unmount()
}

// noFetcher backs the probe mount, which has no files to fetch.
type noFetcher struct{}

func (noFetcher) Fetch(context.Context, string, *repb.Digest) ([]byte, error) {
	return nil, errors.New("probe mount has no blobs")
}

// InputMode reports how the bot builds exec roots.
func (b *Bot) InputMode() InputMode { return b.cfg.InputMode }

// InputsVolume is the volume the bot makes exec roots on, or "" outside the
// volume mode.
func (b *Bot) InputsVolume() string {
	if b.cfg.InputMode != InputVolume {
		return ""
	}
	return b.cfg.InputsVolume
}

// Run leases and runs jobs until ctx ends. Errors from the scheduler are
// logged and retried; the loop only returns with ctx's error. A job that is
// running when ctx ends runs to completion: the action's own timeout and the
// pod's termination grace period bound it, and its result still reaches the
// scheduler.
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
			clog.WarnContext(ctx, "lease failed; retrying", "err", err)
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
		b.RunJob(context.WithoutCancel(ctx), job)
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
	ctx = clog.WithLogger(ctx, clog.FromContext(ctx).With("job", job.GetId(), "instance", job.GetInstanceName()))
	ctx, cancel := context.WithCancel(tenant.Outgoing(ctx, b.cfg.Token))
	defer cancel()
	go b.heartbeat(ctx, cancel, job)

	start := time.Now()
	ar, err := b.execute(ctx, job)
	req := &workerv1.CompleteRequest{BotId: b.cfg.BotID, JobId: job.GetId()}
	if err != nil {
		clog.ErrorContext(ctx, "action failed to run", "err", err)
		req.ErrorMessage = err.Error()
	} else if anyAR, err := anypb.New(ar); err != nil {
		req.ErrorMessage = err.Error()
	} else {
		req.ActionResult = anyAR
		clog.InfoContext(ctx, "action ran", "exitCode", ar.GetExitCode(), "took", time.Since(start))
	}
	// Report with a context that outlives a cancelled lease, so a result
	// is not lost to the cancel that stopped the heartbeat.
	reportCtx, reportCancel := context.WithTimeout(context.WithoutCancel(ctx), 30*time.Second)
	defer reportCancel()
	if _, err := b.cfg.Worker.Complete(reportCtx, req); err != nil {
		clog.ErrorContext(ctx, "reporting result", "err", err)
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
				clog.WarnContext(ctx, "heartbeat failed", "err", err)
				continue
			}
			if resp.GetCancelled() {
				clog.WarnContext(ctx, "lease cancelled; stopping action")
				cancel()
				return
			}
		}
	}
}

// execute builds the exec root, runs the command, and uploads the outputs.
func (b *Bot) execute(ctx context.Context, job *workerv1.Job) (*repb.ActionResult, error) {
	workerStart := timestamppb.Now()
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

	md := &repb.ExecutedActionMetadata{Worker: b.cfg.BotID, WorkerStartTimestamp: workerStart, InputFetchStartTimestamp: timestamppb.Now()}
	execRoot, cleanup, err := b.execRoot(ctx, instance, rootDigest, job.GetId())
	if err != nil {
		return nil, err
	}
	defer cleanup()
	md.InputFetchCompletedTimestamp = timestamppb.Now()
	runnerMD, err := anypb.New(&workerv1.RunnerMetadata{InputMode: string(b.cfg.InputMode)})
	if err != nil {
		return nil, err
	}
	md.AuxiliaryMetadata = []*anypb.Any{runnerMD}

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
	cmd, err := b.command(runCtx, workDir, command.GetArguments())
	if err != nil {
		return nil, fmt.Errorf("starting command: %w", err)
	}
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
	md.WorkerCompletedTimestamp = md.OutputUploadCompletedTimestamp
	return ar, nil
}

// execRoot builds the exec root for an action whose input root is root, in
// the configured mode, and returns it with the function that tears it down.
// In the volume mode the host loads the tree and serves the files, so the
// runner fetches nothing but the mkdir; the other modes load the tree here.
func (b *Bot) execRoot(ctx context.Context, instance string, root *repb.Digest, jobID string) (string, func(), error) {
	if b.cfg.InputMode == InputVolume {
		dir := filepath.Join(b.cfg.InputsVolume, casfs.ExecRootName(root, jobID))
		if err := os.Mkdir(dir, 0o755); err != nil {
			return "", nil, fmt.Errorf("materializing input root on %s: %w", b.cfg.InputsVolume, err)
		}
		return dir, func() {
			if err := os.Remove(dir); err != nil {
				clog.WarnContext(ctx, "dropping exec root", "dir", dir, "err", err)
			}
		}, nil
	}

	inputs, err := tree.Load(ctx, b.cache, instance, root)
	if err != nil {
		return "", nil, fmt.Errorf("input root: %w", err)
	}
	jobDir, err := os.MkdirTemp(b.cfg.WorkDir, "job-")
	if err != nil {
		return "", nil, err
	}
	dir := filepath.Join(jobDir, "root")
	if err := os.MkdirAll(dir, 0o755); err != nil {
		os.RemoveAll(jobDir)
		return "", nil, err
	}
	if b.cfg.InputMode == InputFUSE {
		server, err := casfs.Mount(dir, inputs, b.cache, instance)
		if err != nil {
			os.RemoveAll(jobDir)
			return "", nil, fmt.Errorf("mounting input root: %w", err)
		}
		return dir, func() {
			if err := server.Unmount(); err != nil {
				clog.WarnContext(ctx, "unmounting exec root", "dir", dir, "err", err)
			}
			os.RemoveAll(jobDir)
		}, nil
	}
	if err := tree.Materialize(ctx, b.cache, instance, inputs, dir); err != nil {
		os.RemoveAll(jobDir)
		return "", nil, fmt.Errorf("materializing input root: %w", err)
	}
	return dir, func() { os.RemoveAll(jobDir) }, nil
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

// upload sends the blobs the CAS is missing, in as few calls as the batch
// limit allows.
func (b *Bot) upload(ctx context.Context, instance string, blobs map[string][]byte) error {
	missing, sent, err := b.cfg.Origin.PutBatch(ctx, instance, blobs)
	if err != nil {
		return err
	}
	if len(blobs) > 0 {
		clog.InfoContext(ctx, "uploaded outputs", "blobs", len(blobs), "missing", missing, "bytes", sent)
	}
	return nil
}
