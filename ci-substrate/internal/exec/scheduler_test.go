package exec_test

import (
	"context"
	"errors"
	"io"
	"net"
	"slices"
	"testing"
	"time"

	longrunning "cloud.google.com/go/longrunning/autogen/longrunningpb"
	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/known/anypb"

	workerv1 "github.com/imjasonh/playground/ci-substrate/api/worker/v1"
	"github.com/imjasonh/playground/ci-substrate/internal/actioncache"
	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/exec"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

type harness struct {
	store   *blob.Store
	actions *actioncache.Store
	sched   *exec.Scheduler
	exec    repb.ExecutionClient
	worker  workerv1.WorkerServiceClient
}

const leaseDuration = 200 * time.Millisecond

func newHarness(t *testing.T) *harness {
	t.Helper()
	tenants := tenant.NewRegistry()
	tenants.Allow("tok-a", "tenant-a", "shared")
	tenants.Allow("tok-b", "tenant-b", "shared")
	store, err := blob.NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	actions, err := actioncache.NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	s := exec.New(store, actions, tenants, leaseDuration, nil)
	go s.Run(t.Context())

	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	srv := grpc.NewServer()
	repb.RegisterExecutionServer(srv, s)
	workerv1.RegisterWorkerServiceServer(srv, s)
	go srv.Serve(lis)
	t.Cleanup(srv.Stop)
	conn, err := grpc.NewClient(lis.Addr().String(), grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { conn.Close() })
	return &harness{
		store:   store,
		actions: actions,
		sched:   s,
		exec:    repb.NewExecutionClient(conn),
		worker:  workerv1.NewWorkerServiceClient(conn),
	}
}

func (h *harness) putAction(t *testing.T, action *repb.Action) *repb.Digest {
	t.Helper()
	b, err := proto.MarshalOptions{Deterministic: true}.Marshal(action)
	if err != nil {
		t.Fatal(err)
	}
	d := digest.FromBytes(b)
	if err := h.store.Put(d, b); err != nil {
		t.Fatal(err)
	}
	return d
}

func ctxTok(t *testing.T, token string) context.Context {
	t.Helper()
	return tenant.Outgoing(t.Context(), token)
}

// drain reads operations until the stream ends and returns the last one.
func drain(t *testing.T, stream grpc.ServerStreamingClient[longrunning.Operation]) (*longrunning.Operation, error) {
	t.Helper()
	var last *longrunning.Operation
	for {
		op, err := stream.Recv()
		if err == io.EOF {
			return last, nil
		}
		if err != nil {
			return last, err
		}
		last = op
	}
}

func response(t *testing.T, op *longrunning.Operation) *repb.ExecuteResponse {
	t.Helper()
	if !op.GetDone() {
		t.Fatalf("operation %s not done", op.GetName())
	}
	resp := &repb.ExecuteResponse{}
	if err := op.GetResponse().UnmarshalTo(resp); err != nil {
		t.Fatal(err)
	}
	return resp
}

func complete(t *testing.T, h *harness, token, bot, jobID string, ar *repb.ActionResult) {
	t.Helper()
	anyAR, err := anypb.New(ar)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := h.worker.Complete(ctxTok(t, token), &workerv1.CompleteRequest{BotId: bot, JobId: jobID, ActionResult: anyAR}); err != nil {
		t.Fatal(err)
	}
}

func TestExecuteRoundTrip(t *testing.T) {
	h := newHarness(t)
	action := h.putAction(t, &repb.Action{CommandDigest: digest.FromBytes([]byte("cmd"))})

	stream, err := h.exec.Execute(ctxTok(t, "tok-a"), &repb.ExecuteRequest{InstanceName: "tenant-a", ActionDigest: action})
	if err != nil {
		t.Fatal(err)
	}
	first, err := stream.Recv()
	if err != nil {
		t.Fatal(err)
	}
	md := &repb.ExecuteOperationMetadata{}
	if err := first.GetMetadata().UnmarshalTo(md); err != nil {
		t.Fatal(err)
	}
	if md.GetStage() != repb.ExecutionStage_QUEUED {
		t.Fatalf("first stage %v, want QUEUED", md.GetStage())
	}

	lease, err := h.worker.Lease(ctxTok(t, "tok-a"), &workerv1.LeaseRequest{BotId: "bot-1", InstanceNames: []string{"tenant-a"}})
	if err != nil {
		t.Fatal(err)
	}
	if lease.GetJob().GetId() != first.GetName() {
		t.Fatalf("leased job %q, want operation %q", lease.GetJob().GetId(), first.GetName())
	}
	if lease.GetJob().GetActionDigest().GetHash() != action.GetHash() {
		t.Fatalf("leased action %v, want %v", lease.GetJob().GetActionDigest(), action)
	}
	if _, err := h.worker.Heartbeat(ctxTok(t, "tok-a"), &workerv1.HeartbeatRequest{BotId: "bot-1", JobId: lease.GetJob().GetId()}); err != nil {
		t.Fatal(err)
	}
	complete(t, h, "tok-a", "bot-1", lease.GetJob().GetId(), &repb.ActionResult{ExitCode: 0, StdoutDigest: digest.FromBytes([]byte("hi"))})

	last, err := drain(t, stream)
	if err != nil {
		t.Fatal(err)
	}
	resp := response(t, last)
	if resp.GetCachedResult() || resp.GetResult().GetStdoutDigest().GetHash() != digest.FromBytes([]byte("hi")).GetHash() {
		t.Fatalf("unexpected response %v", resp)
	}

	// The successful result is in the action cache, so a second Execute is
	// served without a runner.
	stream, err = h.exec.Execute(ctxTok(t, "tok-a"), &repb.ExecuteRequest{InstanceName: "tenant-a", ActionDigest: action})
	if err != nil {
		t.Fatal(err)
	}
	last, err = drain(t, stream)
	if err != nil {
		t.Fatal(err)
	}
	if !response(t, last).GetCachedResult() {
		t.Fatal("second Execute was not served from the action cache")
	}
}

func TestFailedRunIsNotCached(t *testing.T) {
	h := newHarness(t)
	action := h.putAction(t, &repb.Action{CommandDigest: digest.FromBytes([]byte("cmd"))})
	stream, err := h.exec.Execute(ctxTok(t, "tok-a"), &repb.ExecuteRequest{InstanceName: "tenant-a", ActionDigest: action})
	if err != nil {
		t.Fatal(err)
	}
	lease, err := h.worker.Lease(ctxTok(t, "tok-a"), &workerv1.LeaseRequest{BotId: "bot-1"})
	if err != nil {
		t.Fatal(err)
	}
	complete(t, h, "tok-a", "bot-1", lease.GetJob().GetId(), &repb.ActionResult{ExitCode: 7})
	last, err := drain(t, stream)
	if err != nil {
		t.Fatal(err)
	}
	if got := response(t, last).GetResult().GetExitCode(); got != 7 {
		t.Fatalf("exit code %d, want 7", got)
	}
	if _, err := h.actions.Get("tenant-a", action); !errors.Is(err, actioncache.ErrNotFound) {
		t.Fatalf("failed action was cached: %v", err)
	}
}

func TestTenantsCannotLeaseOrWatchEachOther(t *testing.T) {
	h := newHarness(t)
	action := h.putAction(t, &repb.Action{CommandDigest: digest.FromBytes([]byte("cmd"))})
	stream, err := h.exec.Execute(ctxTok(t, "tok-a"), &repb.ExecuteRequest{InstanceName: "tenant-a", ActionDigest: action})
	if err != nil {
		t.Fatal(err)
	}
	first, err := stream.Recv()
	if err != nil {
		t.Fatal(err)
	}

	// Tenant B's runner asks for tenant A's instance by name.
	if _, err := h.worker.Lease(ctxTok(t, "tok-b"), &workerv1.LeaseRequest{BotId: "bot-b", InstanceNames: []string{"tenant-a"}}); status.Code(err) != codes.PermissionDenied {
		t.Fatalf("tenant B leasing tenant-a: got %v, want PermissionDenied", err)
	}
	// Tenant B's runner asks for anything it may have: the queue holds only
	// tenant A's job, so it gets nothing by the deadline.
	ctx, cancel := context.WithTimeout(ctxTok(t, "tok-b"), 500*time.Millisecond)
	defer cancel()
	lease, err := h.worker.Lease(ctx, &workerv1.LeaseRequest{BotId: "bot-b"})
	if err != nil || lease.GetJob() != nil {
		t.Fatalf("tenant B lease: job=%v err=%v, want no job", lease.GetJob(), err)
	}
	// Tenant B cannot watch tenant A's operation.
	w, err := h.exec.WaitExecution(ctxTok(t, "tok-b"), &repb.WaitExecutionRequest{Name: first.GetName()})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := w.Recv(); status.Code(err) != codes.PermissionDenied {
		t.Fatalf("tenant B WaitExecution: got %v, want PermissionDenied", err)
	}
	// Tenant B's runner cannot complete tenant A's job either.
	anyAR, _ := anypb.New(&repb.ActionResult{})
	if _, err := h.worker.Complete(ctxTok(t, "tok-b"), &workerv1.CompleteRequest{BotId: "bot-b", JobId: first.GetName(), ActionResult: anyAR}); status.Code(err) != codes.PermissionDenied {
		t.Fatalf("tenant B completing tenant A's job: got %v, want PermissionDenied", err)
	}

	// Tenant A's runner still gets it.
	lease, err = h.worker.Lease(ctxTok(t, "tok-a"), &workerv1.LeaseRequest{BotId: "bot-a"})
	if err != nil || lease.GetJob() == nil {
		t.Fatalf("tenant A lease: job=%v err=%v", lease.GetJob(), err)
	}
}

func TestLeaseExpiryRequeues(t *testing.T) {
	h := newHarness(t)
	action := h.putAction(t, &repb.Action{CommandDigest: digest.FromBytes([]byte("cmd"))})
	stream, err := h.exec.Execute(ctxTok(t, "tok-a"), &repb.ExecuteRequest{InstanceName: "tenant-a", ActionDigest: action})
	if err != nil {
		t.Fatal(err)
	}
	lease, err := h.worker.Lease(ctxTok(t, "tok-a"), &workerv1.LeaseRequest{BotId: "dead-bot"})
	if err != nil {
		t.Fatal(err)
	}
	// dead-bot never heartbeats. After the lease lapses, another runner gets
	// the same job and finishes it.
	ctx, cancel := context.WithTimeout(ctxTok(t, "tok-a"), 5*time.Second)
	defer cancel()
	release, err := h.worker.Lease(ctx, &workerv1.LeaseRequest{BotId: "live-bot"})
	if err != nil {
		t.Fatal(err)
	}
	if release.GetJob().GetId() != lease.GetJob().GetId() {
		t.Fatalf("re-leased %q, want %q", release.GetJob().GetId(), lease.GetJob().GetId())
	}
	hb, err := h.worker.Heartbeat(ctxTok(t, "tok-a"), &workerv1.HeartbeatRequest{BotId: "dead-bot", JobId: lease.GetJob().GetId()})
	if err != nil || !hb.GetCancelled() {
		t.Fatalf("dead-bot heartbeat: cancelled=%v err=%v, want cancelled", hb.GetCancelled(), err)
	}
	complete(t, h, "tok-a", "live-bot", release.GetJob().GetId(), &repb.ActionResult{})
	if _, err := drain(t, stream); err != nil {
		t.Fatal(err)
	}
}

func TestRunnerErrorIsFinal(t *testing.T) {
	h := newHarness(t)
	action := h.putAction(t, &repb.Action{CommandDigest: digest.FromBytes([]byte("cmd"))})
	stream, err := h.exec.Execute(ctxTok(t, "tok-a"), &repb.ExecuteRequest{InstanceName: "tenant-a", ActionDigest: action})
	if err != nil {
		t.Fatal(err)
	}
	lease, err := h.worker.Lease(ctxTok(t, "tok-a"), &workerv1.LeaseRequest{BotId: "bot-1"})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := h.worker.Complete(ctxTok(t, "tok-a"), &workerv1.CompleteRequest{BotId: "bot-1", JobId: lease.GetJob().GetId(), ErrorMessage: "bad output path"}); err != nil {
		t.Fatal(err)
	}
	last, err := drain(t, stream)
	if err != nil {
		t.Fatal(err)
	}
	if got := status.FromProto(response(t, last).GetStatus()); got.Code() != codes.Internal || got.Message() != "bad output path" {
		t.Fatalf("status %v, want Internal with the runner's message", got)
	}
}

func TestSameActionSharesOneJob(t *testing.T) {
	h := newHarness(t)
	action := h.putAction(t, &repb.Action{CommandDigest: digest.FromBytes([]byte("cmd"))})
	s1, err := h.exec.Execute(ctxTok(t, "tok-a"), &repb.ExecuteRequest{InstanceName: "tenant-a", ActionDigest: action})
	if err != nil {
		t.Fatal(err)
	}
	s2, err := h.exec.Execute(ctxTok(t, "tok-a"), &repb.ExecuteRequest{InstanceName: "tenant-a", ActionDigest: action})
	if err != nil {
		t.Fatal(err)
	}
	// The same action in another tenant's instance is a separate job.
	s3, err := h.exec.Execute(ctxTok(t, "tok-b"), &repb.ExecuteRequest{InstanceName: "tenant-b", ActionDigest: action})
	if err != nil {
		t.Fatal(err)
	}
	o1, _ := s1.Recv()
	o2, _ := s2.Recv()
	o3, _ := s3.Recv()
	if o1.GetName() != o2.GetName() {
		t.Fatalf("tenant A's two Executes got different operations %q and %q", o1.GetName(), o2.GetName())
	}
	if o3.GetName() == o1.GetName() {
		t.Fatal("tenant B joined tenant A's job")
	}
	// Each tenant's Status sees its own queue only.
	for _, tok := range []string{"tok-a", "tok-b"} {
		st, err := h.worker.Status(ctxTok(t, tok), &workerv1.StatusRequest{})
		if err != nil {
			t.Fatal(err)
		}
		if st.GetQueued() != 1 || st.GetExecuting() != 0 || len(st.GetBusyBotIds()) != 0 {
			t.Fatalf("%s status %v, want one queued job", tok, st)
		}
	}
	// Once a runner leases tenant A's job, tenant A's Status names it.
	lease, err := h.worker.Lease(ctxTok(t, "tok-a"), &workerv1.LeaseRequest{BotId: "bot-1"})
	if err != nil || lease.GetJob() == nil {
		t.Fatalf("lease: job=%v err=%v", lease.GetJob(), err)
	}
	st, err := h.worker.Status(ctxTok(t, "tok-a"), &workerv1.StatusRequest{InstanceNames: []string{"tenant-a"}})
	if err != nil {
		t.Fatal(err)
	}
	if st.GetQueued() != 0 || st.GetExecuting() != 1 || !slices.Equal(st.GetBusyBotIds(), []string{"bot-1"}) {
		t.Fatalf("status after lease %v", st)
	}
	if _, err := h.worker.Status(ctxTok(t, "tok-b"), &workerv1.StatusRequest{InstanceNames: []string{"tenant-a"}}); status.Code(err) != codes.PermissionDenied {
		t.Fatalf("tenant B reading tenant A's status: %v, want PermissionDenied", err)
	}
}

// An action marked do_not_cache stands for work whose result can change from
// one run to the next, such as one that reads the clock. Every Execute runs
// it, two requests for it at once don't share a run, and its result is never
// stored for a later Execute to find.
func TestDoNotCacheActionRunsEveryTime(t *testing.T) {
	h := newHarness(t)
	action := h.putAction(t, &repb.Action{CommandDigest: digest.FromBytes([]byte("date")), DoNotCache: true})
	execute := func() grpc.ServerStreamingClient[longrunning.Operation] {
		t.Helper()
		stream, err := h.exec.Execute(ctxTok(t, "tok-a"), &repb.ExecuteRequest{InstanceName: "tenant-a", ActionDigest: action})
		if err != nil {
			t.Fatal(err)
		}
		return stream
	}

	s1, s2 := execute(), execute()
	o1, err := s1.Recv()
	if err != nil {
		t.Fatal(err)
	}
	o2, err := s2.Recv()
	if err != nil {
		t.Fatal(err)
	}
	if o1.GetName() == o2.GetName() {
		t.Fatalf("two do_not_cache Executes shared operation %q", o1.GetName())
	}

	// The scheduler leases the two jobs in either order, so complete both
	// before reading either stream.
	for i := range 2 {
		lease, err := h.worker.Lease(ctxTok(t, "tok-a"), &workerv1.LeaseRequest{BotId: "bot-1"})
		if err != nil || lease.GetJob() == nil {
			t.Fatalf("lease %d: job=%v err=%v", i, lease.GetJob(), err)
		}
		complete(t, h, "tok-a", "bot-1", lease.GetJob().GetId(), &repb.ActionResult{})
	}
	for i, s := range []grpc.ServerStreamingClient[longrunning.Operation]{s1, s2} {
		last, err := drain(t, s)
		if err != nil {
			t.Fatal(err)
		}
		if response(t, last).GetCachedResult() {
			t.Fatalf("run %d was served from the action cache", i)
		}
	}
	if _, err := h.actions.Get("tenant-a", action); !errors.Is(err, actioncache.ErrNotFound) {
		t.Fatalf("do_not_cache result was stored: %v", err)
	}

	o3, err := execute().Recv()
	if err != nil {
		t.Fatal(err)
	}
	if o3.GetDone() {
		t.Fatal("a later Execute was answered without a run")
	}
}

func TestExecuteRejectsUnknownAction(t *testing.T) {
	h := newHarness(t)
	missing := digest.FromBytes([]byte("never uploaded"))
	stream, err := h.exec.Execute(ctxTok(t, "tok-a"), &repb.ExecuteRequest{InstanceName: "tenant-a", ActionDigest: missing})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := stream.Recv(); status.Code(err) != codes.FailedPrecondition {
		t.Fatalf("got %v, want FailedPrecondition", err)
	}
}
