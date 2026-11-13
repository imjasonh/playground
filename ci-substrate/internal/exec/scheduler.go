// Package exec is the Remote Execution scheduler. It serves the Execution
// service of the Bazel Remote Execution API to clients, and the WorkerService
// lease protocol to runners. A job is one Action to run in one instance; the
// scheduler queues it, hands it to a runner that the same tenant owns, keeps
// the lease alive through heartbeats, and turns the runner's ActionResult into
// the ExecuteResponse every waiting client receives.
//
// Tenancy follows the token on each RPC. A client's Execute is authorized for
// its instance, and a runner's Lease only returns jobs from instances its own
// token allows. One tenant's actions therefore never run on another tenant's
// runner, and a tenant cannot observe another's operations.
package exec

import (
	"context"
	"errors"
	"fmt"
	"log/slog"
	"slices"
	"sync"
	"time"

	longrunning "cloud.google.com/go/longrunning/autogen/longrunningpb"
	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"github.com/google/uuid"
	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/trace"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/known/anypb"
	"google.golang.org/protobuf/types/known/durationpb"
	"google.golang.org/protobuf/types/known/timestamppb"

	workerv1 "github.com/imjasonh/playground/ci-substrate/api/worker/v1"
	"github.com/imjasonh/playground/ci-substrate/internal/actioncache"
	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/invocation"
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

// DefaultLeaseDuration is how long a runner may go without a heartbeat before
// its job goes back to the queue.
const DefaultLeaseDuration = 30 * time.Second

// maxLeaseWait is how long Lease holds a request with no deadline before it
// answers with no job. leaseReplyGrace is how far ahead of a client's own
// deadline the server answers.
const (
	maxLeaseWait    = 30 * time.Second
	leaseReplyGrace = 100 * time.Millisecond
)

// maxAttempts bounds how many times a job is handed out before it fails. A
// runner that keeps dying mid-action should not hold a job forever.
const maxAttempts = 3

// Scheduler implements the Execution and WorkerService servers.
type Scheduler struct {
	repb.UnimplementedExecutionServer
	workerv1.UnimplementedWorkerServiceServer

	store         *blob.Store
	actions       *actioncache.Store
	tenants       *tenant.Registry
	leaseDuration time.Duration
	invocations   *invocation.Tracker
	metrics       metrics

	mu       sync.Mutex
	jobs     map[string]*job
	inflight map[string]*job
	queue    []*job
	waiters  map[*waiter]struct{}
}

type job struct {
	id         string
	instance   string
	action     *repb.Digest
	doNotCache bool
	enqueued   time.Time

	// parent is the span of the Execute call that queued the job, and
	// traceContext carries it to the runner. requestMetadata is that call's
	// RequestMetadata, and requestMetadataBytes its encoding for the runner.
	parent               trace.SpanContext
	traceContext         map[string]string
	requestMetadata      *repb.RequestMetadata
	requestMetadataBytes []byte

	stage    repb.ExecutionStage_Value
	botID    string
	expiry   time.Time
	attempts int
	response *repb.ExecuteResponse

	// queuedAt is when the current attempt was queued, leasedAt when a
	// runner last leased the job, and queued the time all attempts waited.
	queuedAt time.Time
	leasedAt time.Time
	queued   time.Duration

	// changed is closed and replaced on every state change, so watchers can
	// wait on it without holding the scheduler lock.
	changed chan struct{}
}

type waiter struct {
	instances map[string]bool
	ch        chan *job
}

// New returns a scheduler that reads Actions from store, caches results in
// actions, authorizes callers with tenants, and accounts each action to its
// Bazel invocation in invocations, which may be nil.
func New(store *blob.Store, actions *actioncache.Store, tenants *tenant.Registry, leaseDuration time.Duration, invocations *invocation.Tracker) *Scheduler {
	if leaseDuration <= 0 {
		leaseDuration = DefaultLeaseDuration
	}
	s := &Scheduler{
		store:         store,
		actions:       actions,
		tenants:       tenants,
		leaseDuration: leaseDuration,
		invocations:   invocations,
		jobs:          map[string]*job{},
		inflight:      map[string]*job{},
		waiters:       map[*waiter]struct{}{},
	}
	s.metrics = newMetrics(s)
	return s
}

// Run expires leases until ctx is done. Jobs whose runner stopped heartbeating
// return to the queue; after maxAttempts they fail.
func (s *Scheduler) Run(ctx context.Context) {
	tick := time.NewTicker(s.leaseDuration / 4)
	defer tick.Stop()
	for {
		select {
		case <-ctx.Done():
			return
		case now := <-tick.C:
			s.expireLeases(now)
		}
	}
}

func (s *Scheduler) expireLeases(now time.Time) {
	s.mu.Lock()
	defer s.mu.Unlock()
	for _, j := range s.jobs {
		if j.stage != repb.ExecutionStage_EXECUTING || now.Before(j.expiry) {
			continue
		}
		s.metrics.expirations.Add(context.Background(), 1, metric.WithAttributes(telemetry.AttrInstance.String(j.instance)))
		slog.WarnContext(trace.ContextWithSpanContext(context.Background(), j.parent), "lease expired", "job", j.id, "bot", j.botID, "attempts", j.attempts)
		if j.attempts >= maxAttempts {
			s.finishLocked(j, &repb.ExecuteResponse{
				Status: status.Newf(codes.Unavailable, "lease expired %d times", j.attempts).Proto(),
			})
			continue
		}
		j.botID = ""
		s.enqueueLocked(j)
	}
}

// Status reports the queued and executing jobs, and the runners holding
// leases, for the instances the caller's token allows. The runner pool sizes
// a tenant's runners from it, and sees only that tenant's queue.
func (s *Scheduler) Status(ctx context.Context, req *workerv1.StatusRequest) (*workerv1.StatusResponse, error) {
	instances, err := s.leaseInstances(ctx, req.GetInstanceNames())
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	resp := &workerv1.StatusResponse{}
	busy := map[string]bool{}
	for _, j := range s.jobs {
		if !instances[j.instance] {
			continue
		}
		switch j.stage {
		case repb.ExecutionStage_QUEUED:
			resp.Queued++
		case repb.ExecutionStage_EXECUTING:
			resp.Executing++
			if !busy[j.botID] {
				busy[j.botID] = true
				resp.BusyBotIds = append(resp.BusyBotIds, j.botID)
			}
		}
	}
	slices.Sort(resp.BusyBotIds)
	return resp, nil
}

// Execute queues an action and streams its operation until it completes.
func (s *Scheduler) Execute(req *repb.ExecuteRequest, stream repb.Execution_ExecuteServer) error {
	ctx := stream.Context()
	if err := s.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
		return err
	}
	if err := digest.Validate(req.GetActionDigest()); err != nil {
		return status.Error(codes.InvalidArgument, err.Error())
	}
	action, err := s.loadAction(req.GetActionDigest())
	if err != nil {
		return err
	}
	if !req.GetSkipCacheLookup() && !action.GetDoNotCache() {
		ar, err := s.actions.Get(req.GetInstanceName(), req.GetActionDigest())
		if err == nil {
			s.recordExecute(ctx, req.GetInstanceName(), "cached")
			op, err := operation(uuid.NewString(), req.GetActionDigest(), repb.ExecutionStage_COMPLETED, &repb.ExecuteResponse{Result: ar, CachedResult: true})
			if err != nil {
				return err
			}
			return stream.Send(op)
		}
		if !errors.Is(err, actioncache.ErrNotFound) {
			return status.Error(codes.Internal, err.Error())
		}
	}
	j, merged := s.submit(ctx, req.GetInstanceName(), req.GetActionDigest(), action.GetDoNotCache())
	result := "queued"
	if merged {
		result = "merged"
		trace.SpanFromContext(ctx).AddLink(trace.Link{SpanContext: j.parent})
	}
	s.recordExecute(ctx, req.GetInstanceName(), result)
	trace.SpanFromContext(ctx).SetAttributes(attribute.String("ci_substrate.operation", j.id))
	return s.watch(ctx, j, stream.Send)
}

// recordExecute counts an Execute call by how it was served.
func (s *Scheduler) recordExecute(ctx context.Context, instance, result string) {
	trace.SpanFromContext(ctx).SetAttributes(attribute.String("ci_substrate.execute.result", result))
	s.metrics.executions.Add(ctx, 1, metric.WithAttributes(telemetry.AttrInstance.String(instance), telemetry.AttrResult.String(result)))
	c := invocation.Counts{ExecuteRequests: 1}
	switch result {
	case "cached":
		c.ExecuteCached = 1
	case "merged":
		c.ExecuteMerged = 1
	}
	s.invocations.Add(ctx, instance, c)
}

// WaitExecution resumes streaming an operation a prior Execute started.
func (s *Scheduler) WaitExecution(req *repb.WaitExecutionRequest, stream repb.Execution_WaitExecutionServer) error {
	s.mu.Lock()
	j, ok := s.jobs[req.GetName()]
	s.mu.Unlock()
	if !ok {
		return status.Error(codes.NotFound, "operation not found")
	}
	if err := s.tenants.Authorize(stream.Context(), j.instance); err != nil {
		return err
	}
	return s.watch(stream.Context(), j, stream.Send)
}

func (s *Scheduler) loadAction(d *repb.Digest) (*repb.Action, error) {
	b, err := s.store.Get(d)
	if errors.Is(err, blob.ErrNotFound) {
		return nil, status.Errorf(codes.FailedPrecondition, "action %s not in CAS", digest.Key(d))
	}
	if err != nil {
		return nil, status.Error(codes.Internal, err.Error())
	}
	if err := digest.Verify(d, b); err != nil {
		return nil, status.Error(codes.Internal, err.Error())
	}
	action := &repb.Action{}
	if err := proto.Unmarshal(b, action); err != nil {
		return nil, status.Errorf(codes.InvalidArgument, "action %s: %v", digest.Key(d), err)
	}
	return action, nil
}

// submit queues an action, or joins the job already in flight for the same
// action in the same instance, so two clients asking for one action get one
// run, and reports whether it joined one. Jobs never merge across
// instances: that would let one tenant's queue position reveal another
// tenant's actions.
func (s *Scheduler) submit(ctx context.Context, instance string, action *repb.Digest, doNotCache bool) (*job, bool) {
	carrier := propagation.MapCarrier{}
	otel.GetTextMapPropagator().Inject(ctx, carrier)
	md := telemetry.RequestMetadata(ctx)
	mdBytes, _ := proto.Marshal(md)

	s.mu.Lock()
	defer s.mu.Unlock()
	key := instance + "\x00" + digest.Key(action)
	if j, ok := s.inflight[key]; ok && !doNotCache {
		return j, true
	}
	j := &job{
		id:                   uuid.NewString(),
		instance:             instance,
		action:               action,
		doNotCache:           doNotCache,
		enqueued:             time.Now(),
		parent:               trace.SpanContextFromContext(ctx),
		traceContext:         carrier,
		requestMetadata:      md,
		requestMetadataBytes: mdBytes,
		changed:              make(chan struct{}),
	}
	s.jobs[j.id] = j
	if !doNotCache {
		s.inflight[key] = j
	}
	s.enqueueLocked(j)
	return j, false
}

func (s *Scheduler) enqueueLocked(j *job) {
	j.stage = repb.ExecutionStage_QUEUED
	j.queuedAt = time.Now()
	s.notifyLocked(j)
	for w := range s.waiters {
		if w.instances[j.instance] {
			select {
			case w.ch <- j:
				delete(s.waiters, w)
				s.leaseLocked(j, "")
				return
			default:
			}
		}
	}
	s.queue = append(s.queue, j)
}

// leaseLocked marks j executing by botID. A job handed to a waiting Lease
// has no bot until that Lease wakes and leases it again, and only then
// counts as an attempt.
func (s *Scheduler) leaseLocked(j *job, botID string) {
	now := time.Now()
	j.stage = repb.ExecutionStage_EXECUTING
	j.botID = botID
	if botID != "" {
		j.attempts++
		j.leasedAt = now
		j.queued += now.Sub(j.queuedAt)
		s.metrics.queueTime.Record(context.Background(), now.Sub(j.queuedAt).Seconds(),
			metric.WithAttributes(telemetry.AttrInstance.String(j.instance)))
		_, span := telemetry.Tracer().Start(trace.ContextWithSpanContext(context.Background(), j.parent), "scheduler.queue",
			trace.WithTimestamp(j.queuedAt),
			trace.WithAttributes(
				attribute.String("ci_substrate.operation", j.id),
				attribute.String("ci_substrate.instance", j.instance),
				attribute.String("ci_substrate.bot", botID),
				attribute.Int("ci_substrate.attempt", j.attempts),
			))
		span.End(trace.WithTimestamp(now))
	}
	j.expiry = now.Add(s.leaseDuration)
	s.notifyLocked(j)
}

func (s *Scheduler) notifyLocked(j *job) {
	close(j.changed)
	j.changed = make(chan struct{})
}

func (s *Scheduler) finishLocked(j *job, resp *repb.ExecuteResponse) {
	j.stage = repb.ExecutionStage_COMPLETED
	j.response = resp
	delete(s.inflight, j.instance+"\x00"+digest.Key(j.action))
	s.notifyLocked(j)
	s.recordFinish(j)
	// Keep the record for WaitExecution callers that arrive late, but not
	// forever.
	go func() {
		time.Sleep(time.Minute)
		s.mu.Lock()
		delete(s.jobs, j.id)
		s.mu.Unlock()
	}()
}

// recordFinish accounts a finished job to the metrics and its invocation.
func (s *Scheduler) recordFinish(j *job) {
	outcome := "ok"
	switch {
	case status.FromProto(j.response.GetStatus()).Code() == codes.Unavailable:
		outcome = "lease_expired"
	case j.response.GetStatus().GetCode() != 0:
		outcome = "error"
	case j.response.GetResult().GetExitCode() != 0:
		outcome = "exit_nonzero"
	}
	ctx := context.Background()
	instance := telemetry.AttrInstance.String(j.instance)
	s.metrics.completed.Add(ctx, 1, metric.WithAttributes(instance, telemetry.AttrOutcome.String(outcome)))
	c := invocation.Counts{QueueTime: j.queued}
	if !j.leasedAt.IsZero() {
		run := time.Since(j.leasedAt)
		c.ExecutionTime = run
		s.metrics.runTime.Record(ctx, run.Seconds(), metric.WithAttributes(instance,
			telemetry.AttrMnemonic.String(j.requestMetadata.GetActionMnemonic())))
	}
	if outcome == "ok" {
		c.ActionsRun = 1
	} else {
		c.ActionsFailed = 1
	}
	s.invocations.AddFor(j.requestMetadata, j.instance, c)
}

// watch sends the job's operation on every state change until it completes or
// ctx ends. A client that disconnects does not cancel the job: another client
// may be waiting on the same operation.
func (s *Scheduler) watch(ctx context.Context, j *job, send func(*longrunning.Operation) error) error {
	for {
		s.mu.Lock()
		stage, resp, changed := j.stage, j.response, j.changed
		s.mu.Unlock()
		op, err := operation(j.id, j.action, stage, resp)
		if err != nil {
			return err
		}
		if err := send(op); err != nil {
			return err
		}
		trace.SpanFromContext(ctx).AddEvent(stage.String())
		if stage == repb.ExecutionStage_COMPLETED {
			return nil
		}
		select {
		case <-ctx.Done():
			return status.FromContextError(ctx.Err()).Err()
		case <-changed:
		}
	}
}

func operation(name string, action *repb.Digest, stage repb.ExecutionStage_Value, resp *repb.ExecuteResponse) (*longrunning.Operation, error) {
	md, err := anypb.New(&repb.ExecuteOperationMetadata{Stage: stage, ActionDigest: action})
	if err != nil {
		return nil, status.Error(codes.Internal, err.Error())
	}
	op := &longrunning.Operation{Name: name, Metadata: md}
	if stage == repb.ExecutionStage_COMPLETED {
		op.Done = true
		r, err := anypb.New(resp)
		if err != nil {
			return nil, status.Error(codes.Internal, err.Error())
		}
		op.Result = &longrunning.Operation_Response{Response: r}
	}
	return op, nil
}

// Lease hands the runner one job from an instance its token allows, waiting
// until the request deadline for one to arrive.
func (s *Scheduler) Lease(ctx context.Context, req *workerv1.LeaseRequest) (*workerv1.LeaseResponse, error) {
	if req.GetBotId() == "" {
		return nil, status.Error(codes.InvalidArgument, "missing bot_id")
	}
	instances, err := s.leaseInstances(ctx, req.GetInstanceNames())
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	for i, j := range s.queue {
		if instances[j.instance] {
			s.queue = append(s.queue[:i], s.queue[i+1:]...)
			s.leaseLocked(j, req.GetBotId())
			s.mu.Unlock()
			return &workerv1.LeaseResponse{Job: s.jobProto(j)}, nil
		}
	}
	w := &waiter{instances: instances, ch: make(chan *job, 1)}
	s.waiters[w] = struct{}{}
	s.mu.Unlock()

	// Answer before the client's deadline, so the runner gets an empty
	// response rather than DeadlineExceeded and calls again.
	wait := maxLeaseWait
	if deadline, ok := ctx.Deadline(); ok {
		wait = max(0, time.Until(deadline)-leaseReplyGrace)
	}
	timer := time.NewTimer(wait)
	defer timer.Stop()

	select {
	case <-timer.C:
		s.mu.Lock()
		delete(s.waiters, w)
		s.mu.Unlock()
		select {
		case j := <-w.ch:
			s.mu.Lock()
			j.botID = ""
			s.enqueueLocked(j)
			s.mu.Unlock()
		default:
		}
		return &workerv1.LeaseResponse{}, nil
	case j := <-w.ch:
		s.mu.Lock()
		defer s.mu.Unlock()
		if ctx.Err() != nil {
			// The runner went away while the job was handed over, as a
			// stopping pod does. Requeue now instead of waiting for the
			// lease to expire.
			j.botID = ""
			s.enqueueLocked(j)
			return nil, status.FromContextError(ctx.Err()).Err()
		}
		s.leaseLocked(j, req.GetBotId())
		return &workerv1.LeaseResponse{Job: s.jobProto(j)}, nil
	}
}

// leaseInstances returns the instances a runner may lease from: the ones its
// token allows, narrowed to the ones it asked for.
func (s *Scheduler) leaseInstances(ctx context.Context, requested []string) (map[string]bool, error) {
	allowed := s.tenants.Instances(ctx)
	if len(allowed) == 0 {
		return nil, status.Error(codes.Unauthenticated, "unknown tenant token")
	}
	if len(requested) == 0 {
		return allowed, nil
	}
	out := map[string]bool{}
	for _, name := range requested {
		if !allowed[name] {
			return nil, status.Errorf(codes.PermissionDenied, "tenant not authorized for instance %q", name)
		}
		out[name] = true
	}
	return out, nil
}

func (s *Scheduler) jobProto(j *job) *workerv1.Job {
	return &workerv1.Job{
		Id:              j.id,
		InstanceName:    j.instance,
		ActionDigest:    &workerv1.Digest{Hash: j.action.GetHash(), SizeBytes: j.action.GetSizeBytes()},
		LeaseDuration:   durationpb.New(s.leaseDuration),
		TraceContext:    j.traceContext,
		RequestMetadata: j.requestMetadataBytes,
	}
}

// Heartbeat renews the runner's lease on a job.
func (s *Scheduler) Heartbeat(ctx context.Context, req *workerv1.HeartbeatRequest) (*workerv1.HeartbeatResponse, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	j, err := s.ownedLocked(ctx, req.GetBotId(), req.GetJobId())
	if err != nil {
		if status.Code(err) == codes.NotFound {
			return &workerv1.HeartbeatResponse{Cancelled: true}, nil
		}
		return nil, err
	}
	j.expiry = time.Now().Add(s.leaseDuration)
	return &workerv1.HeartbeatResponse{}, nil
}

// Complete records the outcome of a leased job and wakes its watchers.
func (s *Scheduler) Complete(ctx context.Context, req *workerv1.CompleteRequest) (*workerv1.CompleteResponse, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	j, err := s.ownedLocked(ctx, req.GetBotId(), req.GetJobId())
	if err != nil {
		return nil, err
	}
	// The runner can't tell a transient failure from a bad action, so an
	// error is final; only a runner that stops heartbeating is retried.
	if msg := req.GetErrorMessage(); msg != "" {
		s.finishLocked(j, &repb.ExecuteResponse{Status: status.New(codes.Internal, msg).Proto()})
		return &workerv1.CompleteResponse{}, nil
	}
	ar := &repb.ActionResult{}
	if err := req.GetActionResult().UnmarshalTo(ar); err != nil {
		return nil, status.Errorf(codes.InvalidArgument, "action_result: %v", err)
	}
	if ar.ExecutionMetadata == nil {
		ar.ExecutionMetadata = &repb.ExecutedActionMetadata{}
	}
	ar.ExecutionMetadata.QueuedTimestamp = timestamppb.New(j.enqueued)
	// Only a successful run is worth caching. A failed one is retried by the
	// next Execute, and do_not_cache actions are never stored.
	if ar.GetExitCode() == 0 && !j.doNotCache {
		if err := s.actions.Put(j.instance, j.action, ar); err != nil {
			return nil, status.Error(codes.Internal, err.Error())
		}
	}
	s.finishLocked(j, &repb.ExecuteResponse{Result: ar})
	return &workerv1.CompleteResponse{}, nil
}

// ownedLocked returns the executing job that botID holds, after checking the
// caller's token allows the job's instance.
func (s *Scheduler) ownedLocked(ctx context.Context, botID, jobID string) (*job, error) {
	j, ok := s.jobs[jobID]
	if !ok {
		return nil, status.Error(codes.NotFound, "job not found")
	}
	if err := s.tenants.Authorize(ctx, j.instance); err != nil {
		return nil, err
	}
	if j.stage != repb.ExecutionStage_EXECUTING || j.botID != botID {
		return nil, status.Error(codes.NotFound, fmt.Sprintf("job %s not leased by %s", jobID, botID))
	}
	return j, nil
}
