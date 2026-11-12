package bot_test

import (
	"context"
	"io"
	"net"
	"os"
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/protobuf/proto"

	workerv1 "github.com/imjasonh/playground/ci-substrate/api/worker/v1"
	"github.com/imjasonh/playground/ci-substrate/internal/actioncache"
	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/bot"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/exec"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
	"github.com/imjasonh/playground/ci-substrate/internal/tree"
)

// stack is a cas (CAS, action cache, scheduler) on loopback, plus clients
// for a tenant and for the bot.
type stack struct {
	client   *remote.Client
	execer   repb.ExecutionClient
	worker   workerv1.WorkerServiceClient
	ctx      context.Context
	instance string
}

func newStack(t *testing.T) *stack {
	t.Helper()
	tenants := tenant.NewRegistry()
	tenants.Allow("tok-a", "tenant-a")
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
		client:   remote.NewClient(conn),
		execer:   repb.NewExecutionClient(conn),
		worker:   workerv1.NewWorkerServiceClient(conn),
		ctx:      tenant.Outgoing(t.Context(), "tok-a"),
		instance: "tenant-a",
	}
}

func (s *stack) upload(t *testing.T, b []byte) *repb.Digest {
	t.Helper()
	d, err := s.client.Upload(s.ctx, s.instance, b)
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
	b, err := s.client.Fetch(s.ctx, s.instance, d)
	if err != nil {
		t.Fatal(err)
	}
	return b
}

func (s *stack) newBot(t *testing.T, mode bot.InputMode) *bot.Bot {
	t.Helper()
	b, err := bot.New(bot.Config{
		BotID:     "bot-" + string(mode),
		Worker:    s.worker,
		Origin:    s.client,
		Cache:     s.client,
		WorkDir:   t.TempDir(),
		InputMode: mode,
	})
	if err != nil {
		t.Fatal(err)
	}
	return b
}

// execute runs Execute for action and returns the final response once a bot
// has run it in the background.
func (s *stack) execute(t *testing.T, b *bot.Bot, action *repb.Digest) *repb.ExecuteResponse {
	t.Helper()
	stream, err := s.execer.Execute(s.ctx, &repb.ExecuteRequest{InstanceName: s.instance, ActionDigest: action})
	if err != nil {
		t.Fatal(err)
	}
	// The bot's lease ends when the operation does, so a cache hit that
	// needs no bot does not wait out the lease.
	botCtx, stopBot := context.WithCancel(tenant.Outgoing(context.WithoutCancel(s.ctx), "tok-a"))
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

func modes(t *testing.T) []bot.InputMode {
	t.Helper()
	ms := []bot.InputMode{bot.InputCopy}
	if _, err := os.Stat("/dev/fuse"); err == nil {
		ms = append(ms, bot.InputFUSE)
	} else {
		t.Log("/dev/fuse not available; testing copy mode only")
	}
	return ms
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
				Arguments: []string{"sh", "-c", "cat input.txt > out/copy.txt && echo built >&2 && mkdir -p out/tree/deep && echo leaf > out/tree/deep/leaf.txt && printf hello && exit 0"},
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
