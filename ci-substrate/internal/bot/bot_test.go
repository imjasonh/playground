package bot_test

import (
	"context"
	"fmt"
	"io"
	"net"
	"os"
	osexec "os/exec"
	"runtime"
	"testing"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/known/timestamppb"

	workerv1 "github.com/imjasonh/playground/ci-substrate/api/worker/v1"
	"github.com/imjasonh/playground/ci-substrate/internal/actioncache"
	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/bot"
	"github.com/imjasonh/playground/ci-substrate/internal/casfs"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/exec"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
	"github.com/imjasonh/playground/ci-substrate/internal/tree"
)

const (
	token    = "tok-a"
	instance = "tenant-a"
)

// stack is a cas (CAS, action cache, scheduler) on loopback, plus clients
// for a tenant and for the bot.
type stack struct {
	client *remote.Client
	execer repb.ExecutionClient
	worker workerv1.WorkerServiceClient
}

func newStack(t *testing.T) *stack {
	t.Helper()
	tenants := tenant.NewRegistry()
	tenants.Allow(token, instance)
	store, err := blob.NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	actions, err := actioncache.NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	origin := remote.NewOrigin(store, actions, tenants)
	sched := exec.New(store, actions, tenants, 0)
	go sched.Run(t.Context())

	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	srv := grpc.NewServer()
	repb.RegisterContentAddressableStorageServer(srv, origin)
	repb.RegisterActionCacheServer(srv, origin)
	repb.RegisterCapabilitiesServer(srv, origin)
	bytestream.RegisterByteStreamServer(srv, origin)
	repb.RegisterExecutionServer(srv, sched)
	workerv1.RegisterWorkerServiceServer(srv, sched)
	go srv.Serve(lis)
	t.Cleanup(srv.Stop)

	conn, err := grpc.NewClient(lis.Addr().String(), grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { conn.Close() })
	return &stack{
		client: remote.NewClient(conn),
		execer: repb.NewExecutionClient(conn),
		worker: workerv1.NewWorkerServiceClient(conn),
	}
}

// ctx is a tenant call context.
func ctx(t *testing.T) context.Context {
	t.Helper()
	return tenant.Outgoing(t.Context(), token)
}

func (s *stack) upload(t *testing.T, b []byte) *repb.Digest {
	t.Helper()
	d, err := s.client.Upload(ctx(t), instance, b)
	if err != nil {
		t.Fatal(err)
	}
	return d
}

func (s *stack) uploadProto(t *testing.T, m proto.Message) *repb.Digest {
	t.Helper()
	return s.upload(t, tree.Marshal(m))
}

func (s *stack) fetch(t *testing.T, d *repb.Digest) []byte {
	t.Helper()
	b, err := s.client.Fetch(ctx(t), instance, d)
	if err != nil {
		t.Fatal(err)
	}
	return b
}

// newBot returns a bot in mode. In the volume mode it also plays the host:
// it mounts a casfs inputs volume, with the tenant token, for the bot to
// make exec roots on.
func (s *stack) newBot(t *testing.T, mode bot.InputMode) *bot.Bot {
	t.Helper()
	cfg := bot.Config{
		BotID:     "bot-" + string(mode),
		Token:     token,
		Worker:    s.worker,
		Origin:    s.client,
		Cache:     s.client,
		WorkDir:   t.TempDir(),
		InputMode: mode,
	}
	if mode == bot.InputVolume {
		cfg.InputsVolume = t.TempDir()
		server, err := casfs.MountVolume(cfg.InputsVolume, tree.WithToken(s.client, token), instance)
		if err != nil {
			t.Fatal(err)
		}
		t.Cleanup(func() { server.Unmount() })
	}
	b, err := bot.New(cfg)
	if err != nil {
		t.Fatal(err)
	}
	return b
}

// execute runs Execute for action and returns the final response once a bot
// has run it in the background.
func (s *stack) execute(t *testing.T, b *bot.Bot, action *repb.Digest) *repb.ExecuteResponse {
	t.Helper()
	stream, err := s.execer.Execute(ctx(t), &repb.ExecuteRequest{InstanceName: instance, ActionDigest: action})
	if err != nil {
		t.Fatal(err)
	}
	// The bot's lease ends when the operation does, so a cache hit that
	// needs no bot does not wait out the lease.
	botCtx, stopBot := context.WithCancel(t.Context())
	defer stopBot()
	done := make(chan error, 1)
	go func() {
		ran, err := b.RunOnce(botCtx)
		if err == nil && !ran {
			err = io.ErrUnexpectedEOF
		}
		done <- err
	}()
	resp := &repb.ExecuteResponse{}
	for {
		op, err := stream.Recv()
		if err != nil {
			t.Fatal(err)
		}
		if op.GetDone() {
			if err := op.GetResponse().UnmarshalTo(resp); err != nil {
				t.Fatal(err)
			}
			break
		}
	}
	stopBot()
	if err := <-done; err != nil && !resp.GetCachedResult() {
		t.Fatalf("bot: %v", err)
	}
	return resp
}

func TestMain(m *testing.M) {
	bot.RunLauncher()
	os.Exit(m.Run())
}

// gcChildEnv marks the copy of the test binary that
// TestActionsSurviveGarbageCollection runs the workload in.
const gcChildEnv = "CI_SUBSTRATE_BOT_GC_CHILD"

// A FUSE exec root is served by the bot's own process. Starting an action in
// it while a garbage collection stops the world deadlocked the whole process
// (see RunLauncher). A deadlocked runtime can't time itself out, so the
// workload runs in a child process that this test kills at a deadline.
func TestActionsSurviveGarbageCollection(t *testing.T) {
	if _, err := os.Stat("/dev/fuse"); err != nil {
		t.Skip("needs /dev/fuse")
	}
	if os.Getenv(gcChildEnv) == "" {
		ctx, cancel := context.WithTimeout(t.Context(), 2*time.Minute)
		defer cancel()
		child := osexec.CommandContext(ctx, os.Args[0], "-test.run=^TestActionsSurviveGarbageCollection$", "-test.v")
		child.Env = append(os.Environ(), gcChildEnv+"=1")
		// A deadlocked child can't be reaped: its vfork child waits on the
		// FUSE mount uninterruptibly. Stop waiting for it shortly after the
		// kill.
		child.WaitDelay = 5 * time.Second
		out, err := child.CombinedOutput()
		if ctx.Err() != nil {
			t.Fatalf("actions deadlocked under garbage collection:\n%s", out)
		}
		if err != nil {
			t.Fatalf("workload: %v\n%s", err, out)
		}
		return
	}

	for _, mode := range []bot.InputMode{bot.InputFUSE, bot.InputVolume} {
		t.Run(string(mode), func(t *testing.T) {
			s := newStack(t)
			b := s.newBot(t, mode)
			stop := make(chan struct{})
			defer close(stop)
			go func() {
				for {
					select {
					case <-stop:
						return
					default:
						runtime.GC()
					}
				}
			}()
			input := s.upload(t, []byte("alpha\n"))
			root := s.uploadProto(t, &repb.Directory{Files: []*repb.FileNode{{Name: "input.txt", Digest: input}}})
			for i := range 40 {
				command := s.uploadProto(t, &repb.Command{
					Arguments:   []string{"sh", "-c", fmt.Sprintf("cat input.txt > out.txt && echo %d >> out.txt", i)},
					OutputPaths: []string{"out.txt"},
				})
				action := s.uploadProto(t, &repb.Action{CommandDigest: command, InputRootDigest: root})
				if resp := s.execute(t, b, action); resp.GetResult().GetExitCode() != 0 || resp.GetStatus().GetCode() != 0 {
					t.Fatalf("action %d: %v", i, resp)
				}
			}
		})
	}
}

func modes(t *testing.T) []bot.InputMode {
	t.Helper()
	ms := []bot.InputMode{bot.InputCopy}
	if _, err := os.Stat("/dev/fuse"); err == nil {
		ms = append(ms, bot.InputFUSE, bot.InputVolume)
	} else {
		t.Log("/dev/fuse not available; testing copy mode only")
	}
	return ms
}

// inputMode is the mode the runner recorded on the result.
func inputMode(t *testing.T, ar *repb.ActionResult) string {
	t.Helper()
	for _, a := range ar.GetExecutionMetadata().GetAuxiliaryMetadata() {
		md := &workerv1.RunnerMetadata{}
		if a.MessageIs(md) {
			if err := a.UnmarshalTo(md); err != nil {
				t.Fatal(err)
			}
			return md.GetInputMode()
		}
	}
	t.Fatal("result carries no RunnerMetadata")
	return ""
}

func TestRunsActionWithInputsAndOutputs(t *testing.T) {
	for _, mode := range modes(t) {
		t.Run(string(mode), func(t *testing.T) {
			s := newStack(t)
			b := s.newBot(t, mode)

			input := s.upload(t, []byte("alpha\n"))
			unread := s.upload(t, make([]byte, 2<<20))
			root := s.uploadProto(t, &repb.Directory{
				Files: []*repb.FileNode{
					{Name: "input.txt", Digest: input},
					{Name: "unread.bin", Digest: unread},
				},
			})
			command := s.uploadProto(t, &repb.Command{
				Arguments:   []string{"sh", "-c", "cat input.txt > out/copy.txt && echo built >&2 && mkdir -p out/tree/deep && echo leaf > out/tree/deep/leaf.txt && printf hello && exit 0"},
				OutputPaths: []string{"out/copy.txt", "out/tree", "missing.txt"},
			})
			action := s.uploadProto(t, &repb.Action{CommandDigest: command, InputRootDigest: root})

			resp := s.execute(t, b, action)
			if resp.GetStatus().GetCode() != 0 {
				t.Fatalf("execute status: %v", resp.GetStatus())
			}
			ar := resp.GetResult()
			if ar.GetExitCode() != 0 {
				t.Fatalf("exit code %d", ar.GetExitCode())
			}
			if got := s.fetch(t, ar.GetStdoutDigest()); string(got) != "hello" {
				t.Fatalf("stdout %q", got)
			}
			if got := s.fetch(t, ar.GetStderrDigest()); string(got) != "built\n" {
				t.Fatalf("stderr %q", got)
			}
			if len(ar.GetOutputFiles()) != 1 || ar.GetOutputFiles()[0].GetPath() != "out/copy.txt" {
				t.Fatalf("output files %v", ar.GetOutputFiles())
			}
			if got := s.fetch(t, ar.GetOutputFiles()[0].GetDigest()); string(got) != "alpha\n" {
				t.Fatalf("out/copy.txt %q", got)
			}
			if len(ar.GetOutputDirectories()) != 1 || ar.GetOutputDirectories()[0].GetPath() != "out/tree" {
				t.Fatalf("output directories %v", ar.GetOutputDirectories())
			}
			tr := &repb.Tree{}
			if err := proto.Unmarshal(s.fetch(t, ar.GetOutputDirectories()[0].GetTreeDigest()), tr); err != nil {
				t.Fatal(err)
			}
			if len(tr.GetChildren()) != 1 || tr.GetRoot().GetDirectories()[0].GetName() != "deep" {
				t.Fatalf("tree %v", tr)
			}
			leaf := tr.GetChildren()[0].GetFiles()[0]
			if leaf.GetName() != "leaf.txt" || string(s.fetch(t, leaf.GetDigest())) != "leaf\n" {
				t.Fatalf("leaf %v", leaf)
			}
			if ar.GetExecutionMetadata().GetWorker() != "bot-"+string(mode) {
				t.Fatalf("worker %q", ar.GetExecutionMetadata().GetWorker())
			}
			// Bazel reads queue, fetch, execution, and upload times from these,
			// so each stage starts no earlier than the one before ends.
			md := ar.GetExecutionMetadata()
			stages := []*timestamppb.Timestamp{
				md.GetQueuedTimestamp(), md.GetWorkerStartTimestamp(),
				md.GetInputFetchStartTimestamp(), md.GetInputFetchCompletedTimestamp(),
				md.GetExecutionStartTimestamp(), md.GetExecutionCompletedTimestamp(),
				md.GetOutputUploadStartTimestamp(), md.GetOutputUploadCompletedTimestamp(),
				md.GetWorkerCompletedTimestamp(),
			}
			for i, ts := range stages {
				if ts == nil {
					t.Fatalf("timestamp %d of the execution metadata is unset: %v", i, md)
				}
				if i > 0 && ts.AsTime().Before(stages[i-1].AsTime()) {
					t.Fatalf("timestamp %d is before timestamp %d: %v", i, i-1, md)
				}
			}
			if got := inputMode(t, ar); got != string(mode) {
				t.Fatalf("result records input mode %q, want %q", got, mode)
			}
			if mode == bot.InputVolume {
				if entries, err := os.ReadDir(b.InputsVolume()); err != nil || len(entries) != 0 {
					t.Fatalf("exec root left on the volume: %v, %v", entries, err)
				}
			}

			// A second Execute of the same action is served from the action
			// cache without a bot.
			again := s.execute(t, b, action)
			if !again.GetCachedResult() {
				t.Fatal("second Execute was not a cache hit")
			}
			if again.GetResult().GetOutputFiles()[0].GetDigest().GetHash() != ar.GetOutputFiles()[0].GetDigest().GetHash() {
				t.Fatal("cached result differs")
			}
		})
	}
}

func TestFailedActionReportsExitCode(t *testing.T) {
	s := newStack(t)
	b := s.newBot(t, bot.InputCopy)
	command := s.uploadProto(t, &repb.Command{Arguments: []string{"sh", "-c", "echo nope >&2; exit 3"}})
	action := s.uploadProto(t, &repb.Action{CommandDigest: command})
	resp := s.execute(t, b, action)
	if resp.GetResult().GetExitCode() != 3 {
		t.Fatalf("exit code %d, want 3", resp.GetResult().GetExitCode())
	}
	if got := s.fetch(t, resp.GetResult().GetStderrDigest()); string(got) != "nope\n" {
		t.Fatalf("stderr %q", got)
	}
	if digest.Key(resp.GetResult().GetStdoutDigest()) == digest.Key(resp.GetResult().GetStderrDigest()) {
		t.Fatal("stdout and stderr confused")
	}
}

func TestRejectsEscapingOutputPath(t *testing.T) {
	s := newStack(t)
	b := s.newBot(t, bot.InputCopy)
	command := s.uploadProto(t, &repb.Command{Arguments: []string{"true"}, OutputPaths: []string{"../outside"}})
	action := s.uploadProto(t, &repb.Action{CommandDigest: command})
	resp := s.execute(t, b, action)
	if resp.GetStatus().GetCode() == 0 {
		t.Fatalf("action with an escaping output path ran: %v", resp)
	}
}
