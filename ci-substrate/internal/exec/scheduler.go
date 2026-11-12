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
	"sync"
	"time"

	longrunning "cloud.google.com/go/longrunning/autogen/longrunningpb"
	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"github.com/google/uuid"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/known/anypb"
	"google.golang.org/protobuf/types/known/durationpb"

	workerv1 "github.com/imjasonh/playground/ci-substrate/api/worker/v1"
	"github.com/imjasonh/playground/ci-substrate/internal/actioncache"
	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
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

	stage    repb.ExecutionStage_Value
	botID    string
	expiry   time.Time
	attempts int
	response *repb.ExecuteResponse

	// changed is closed and replaced on every state change, so watchers can
	// wait on it without holding the scheduler lock.
	changed chan struct{}
}

type waiter struct {
	instances map[string]bool
	ch        chan *job
}

// New returns a scheduler that reads Actions from store, caches results in
// actions, and authorizes callers with tenants.
func New(store *blob.Store, actions *actioncache.Store, tenants *tenant.Registry, leaseDuration time.Duration) *Scheduler {
	if leaseDuration <= 0 {
		leaseDuration = DefaultLeaseDuration
	}
	return &Scheduler{
		store:         store,
		actions:       actions,
		tenants:       tenants,
		leaseDuration: leaseDuration,
		jobs:          map[string]*job{},
		inflight:      map[string]*job{},
		waiters:       map[*waiter]struct{}{},
	}
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
		slog.Warn("lease expired", "job", j.id, "bot", j.botID, "attempts", j.attempts)
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

// Depth reports how many jobs are queued or executing per instance. The
// Substrate pool sizes each tenant's runners from it.
func (s *Scheduler) Depth() map[string]int {
	s.mu.Lock()
	defer s.mu.Unlock()
	depth := map[string]int{}
	for _, j := range s.jobs {
		if j.stage == repb.ExecutionStage_QUEUED || j.stage == repb.ExecutionStage_EXECUTING {
			depth[j.instance]++
		}
	}
	return depth
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
	j := s.submit(req.GetInstanceName(), req.GetActionDigest(), action.GetDoNotCache())
	return s.watch(ctx, j, stream.Send)
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
// run. Jobs never merge across instances: that would let one tenant's queue
// position reveal another tenant's actions.
func (s *Scheduler) submit(instance string, action *repb.Digest, doNotCache bool) *job {
	s.mu.Lock()
	defer s.mu.Unlock()
	key := instance + "\x00" + digest.Key(action)
	if j, ok := s.inflight[key]; ok && !doNotCache {
		return j
	}
	j := &job{
		id:         uuid.NewString(),
		instance:   instance,
		action:     action,
		doNotCache: doNotCache,
		enqueued:   time.Now(),
		changed:    make(chan struct{}),
	}
	s.jobs[j.id] = j
	if !doNotCache {
		s.inflight[key] = j
	}
	s.enqueueLocked(j)
	return j
}

func (s *Scheduler) enqueueLocked(j *job) {
	j.stage = repb.ExecutionStage_QUEUED
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

// leaseLocked marks j executing. The bot id is filled in by Lease once the
// waiter wakes, since the waiter holds it.
func (s *Scheduler) leaseLocked(j *job, botID string) {
	j.stage = repb.ExecutionStage_EXECUTING
	j.botID = botID
	j.attempts++
	j.expiry = time.Now().Add(s.leaseDuration)
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
	// Keep the record for WaitExecution callers that arrive late, but not
	// forever.
	go func() {
		time.Sleep(time.Minute)
		s.mu.Lock()
		delete(s.jobs, j.id)
		s.mu.Unlock()
	}()
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
		// A job may have been handed over as the deadline passed.
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
		j.botID = req.GetBotId()
		resp := &workerv1.LeaseResponse{Job: s.jobProto(j)}
		s.mu.Unlock()
		return resp, nil
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
		Id:            j.id,
		InstanceName:  j.instance,
		ActionDigest:  &workerv1.Digest{Hash: j.action.GetHash(), SizeBytes: j.action.GetSizeBytes()},
		LeaseDuration: durationpb.New(s.leaseDuration),
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
	if req.GetErrorMessage() != "" {
		s.finishLocked(j, &repb.ExecuteResponse{Status: status.New(codes.Internal, req.GetErrorMessage()).Proto()})
		return &workerv1.CompleteResponse{}, nil
	}
	ar := &repb.ActionResult{}
	if err := req.GetActionResult().UnmarshalTo(ar); err != nil {
		return nil, status.Errorf(codes.InvalidArgument, "action_result: %v", err)
	}
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
