// Package bes implements the Google Build Event Service (BES)
// PublishBuildEvent gRPC API so Bazel can stream Build Event Protocol (BEP)
// events directly to cas via --bes_backend. It indexes build lifecycle state,
// client-side BuildMetrics, test results, coverage outputs, and JSON trace
// profile references per tenant, emits OpenTelemetry metrics and span
// attributes into the build's trace, and serves a tenant-authorized HTTP JSON
// endpoint for querying invocation records.
package bes

import (
	"context"
	"encoding/hex"
	"encoding/json"
	"errors"
	"io"
	"io/fs"
	"log/slog"
	"net/http"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"sync"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
	buildpb "google.golang.org/genproto/googleapis/devtools/build/v1"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/types/known/emptypb"

	"github.com/imjasonh/playground/ci-substrate/internal/invocation"
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

// InvocationRecord is the structured summary persisted for a Bazel invocation
// received over BES.
type InvocationRecord struct {
	InvocationID     string              `json:"invocation_id"`
	BuildID          string              `json:"build_id,omitempty"`
	Instance         string              `json:"instance"`
	Command          string              `json:"command,omitempty"`
	BuildToolVersion string              `json:"build_tool_version,omitempty"`
	Workspace        string              `json:"workspace,omitempty"`
	Host             string              `json:"host,omitempty"`
	User             string              `json:"user,omitempty"`
	StartedAt        time.Time           `json:"started_at"`
	FinishedAt       *time.Time          `json:"finished_at,omitempty"`
	Success          *bool               `json:"success,omitempty"`
	ExitCode         *int32              `json:"exit_code,omitempty"`
	ExitCodeName     string              `json:"exit_code_name,omitempty"`
	EventCount       int64               `json:"event_count"`
	Metrics          *BuildMetrics       `json:"build_metrics,omitempty"`
	Profiles         []FileRef           `json:"profiles,omitempty"`
	ToolLogs         []FileRef           `json:"tool_logs,omitempty"`
	CoverageFiles    []FileRef           `json:"coverage_files,omitempty"`
	Tests            []TestResultSummary `json:"tests,omitempty"`

	// emitted reports whether telemetry was already recorded for this
	// invocation. Records reloaded from disk were finalized, so they set it.
	emitted bool
	// touched is when the record last received an event, for evicting
	// streams that never finish.
	touched time.Time
}

// clone returns a deep copy of r safe to read without holding Server.mu.
func (r *InvocationRecord) clone() *InvocationRecord {
	cp := *r
	if r.Metrics != nil {
		m := *r.Metrics
		cp.Metrics = &m
	}
	cp.Profiles = slices.Clone(r.Profiles)
	cp.ToolLogs = slices.Clone(r.ToolLogs)
	cp.CoverageFiles = slices.Clone(r.CoverageFiles)
	cp.Tests = slices.Clone(r.Tests)
	for i := range cp.Tests {
		cp.Tests[i].Outputs = slices.Clone(cp.Tests[i].Outputs)
	}
	return &cp
}

// staleAfter is how long an unfinished invocation may go without events
// before the server persists and evicts it, so streams that fail and never
// retry don't hold memory forever.
const staleAfter = time.Hour

// Server implements buildpb.PublishBuildEventServer and serves invocation
// summaries over HTTP.
type Server struct {
	buildpb.UnimplementedPublishBuildEventServer

	root        string
	tenants     *tenant.Registry
	invocations *invocation.Tracker
	metrics     besMetrics

	mu        sync.Mutex
	active    map[string]*InvocationRecord // keyed by instance + "\x00" + invocationID
	lastSweep time.Time
}

type besMetrics struct {
	builds            metric.Int64Counter
	wallTime          metric.Float64Histogram
	cpuTime           metric.Float64Histogram
	analysisTime      metric.Float64Histogram
	executionTime     metric.Float64Histogram
	actionsCreated    metric.Int64Histogram
	actionsExecuted   metric.Int64Histogram
	packagesLoaded    metric.Int64Histogram
	targetsConfigured metric.Int64Histogram
	peakHeapBytes     metric.Int64Histogram
	tests             metric.Int64Counter
}

func newBESMetrics() besMetrics {
	m := telemetry.Meter()
	durBuckets := metric.WithExplicitBucketBoundaries(0.1, 0.5, 1, 5, 15, 30, 60, 120, 300, 600, 1800)
	countBuckets := metric.WithExplicitBucketBoundaries(0, 1, 10, 100, 1000, 10000, 100000)
	memBuckets := metric.WithExplicitBucketBoundaries(0, 64<<20, 256<<20, 512<<20, 1<<30, 2<<30, 4<<30, 8<<30, 16<<30)
	return besMetrics{
		builds: telemetry.Handle(m.Int64Counter("bazel.bep.builds",
			metric.WithDescription("Bazel builds reported through the Build Event Service."))),
		wallTime: telemetry.Handle(m.Float64Histogram("bazel.bep.wall_time", metric.WithUnit("s"),
			metric.WithDescription("Client-reported wall time from BEP BuildMetrics."), durBuckets)),
		cpuTime: telemetry.Handle(m.Float64Histogram("bazel.bep.cpu_time", metric.WithUnit("s"),
			metric.WithDescription("Client-reported CPU time from BEP BuildMetrics."), durBuckets)),
		analysisTime: telemetry.Handle(m.Float64Histogram("bazel.bep.analysis_time", metric.WithUnit("s"),
			metric.WithDescription("Client-reported analysis phase time from BEP BuildMetrics."), durBuckets)),
		executionTime: telemetry.Handle(m.Float64Histogram("bazel.bep.execution_time", metric.WithUnit("s"),
			metric.WithDescription("Client-reported execution phase time from BEP BuildMetrics."), durBuckets)),
		actionsCreated: telemetry.Handle(m.Int64Histogram("bazel.bep.actions_created",
			metric.WithDescription("Actions created per build from BEP BuildMetrics."), countBuckets)),
		actionsExecuted: telemetry.Handle(m.Int64Histogram("bazel.bep.actions_executed",
			metric.WithDescription("Actions executed per build from BEP BuildMetrics."), countBuckets)),
		packagesLoaded: telemetry.Handle(m.Int64Histogram("bazel.bep.packages_loaded",
			metric.WithDescription("Packages loaded per build from BEP BuildMetrics."), countBuckets)),
		targetsConfigured: telemetry.Handle(m.Int64Histogram("bazel.bep.targets_configured",
			metric.WithDescription("Targets configured per build from BEP BuildMetrics."), countBuckets)),
		peakHeapBytes: telemetry.Handle(m.Int64Histogram("bazel.bep.memory.peak_post_gc_heap", metric.WithUnit("By"),
			metric.WithDescription("Peak post-GC JVM heap size from BEP BuildMetrics."), memBuckets)),
		tests: telemetry.Handle(m.Int64Counter("bazel.bep.tests",
			metric.WithDescription("Test results reported through BEP, by status."))),
	}
}

// New creates the BES storage directory and returns a PublishBuildEvent server.
func New(root string, tenants *tenant.Registry, invocations *invocation.Tracker) (*Server, error) {
	if err := os.MkdirAll(root, 0o755); err != nil {
		return nil, err
	}
	return &Server{
		root:        root,
		tenants:     tenants,
		invocations: invocations,
		metrics:     newBESMetrics(),
		active:      map[string]*InvocationRecord{},
	}, nil
}

// resolveInstance authorizes ctx for projectID, or selects the token's primary
// instance when projectID is empty (Bazel omits project_id unless
// --bes_instance_name is passed).
func (s *Server) resolveInstance(ctx context.Context, projectID string) (string, error) {
	if projectID != "" {
		if err := s.tenants.Authorize(ctx, projectID); err != nil {
			return "", err
		}
		return projectID, nil
	}
	if err := s.tenants.Authorize(ctx, ""); err == nil {
		return "", nil
	}
	allowed := s.tenants.Instances(ctx)
	if len(allowed) == 0 {
		return "", status.Error(codes.Unauthenticated, "missing or unknown tenant token")
	}
	names := make([]string, 0, len(allowed))
	for name := range allowed {
		names = append(names, name)
	}
	slices.Sort(names)
	return names[0], nil
}

// PublishLifecycleEvent records high-level build lifecycle transitions.
func (s *Server) PublishLifecycleEvent(ctx context.Context, req *buildpb.PublishLifecycleEventRequest) (*emptypb.Empty, error) {
	instance, err := s.resolveInstance(ctx, req.GetProjectId())
	if err != nil {
		return nil, err
	}
	obe := req.GetBuildEvent()
	if obe == nil || obe.GetStreamId() == nil {
		return nil, status.Error(codes.InvalidArgument, "missing build_event.stream_id")
	}
	sid := obe.GetStreamId()
	invID := sid.GetInvocationId()
	if invID == "" {
		invID = sid.GetBuildId()
	}
	if err := validateID(invID); err != nil {
		return nil, status.Error(codes.InvalidArgument, err.Error())
	}

	ev := obe.GetEvent()
	var shouldFinish bool
	if ev != nil {
		switch ev.GetEvent().(type) {
		case *buildpb.BuildEvent_InvocationAttemptFinished_, *buildpb.BuildEvent_BuildFinished_:
			shouldFinish = true
		}
	}

	// BuildFinished lifecycle events carry only build_id (empty invocation_id);
	// nothing to record separately once the invocation stream has finished.
	if sid.GetInvocationId() == "" {
		return &emptypb.Empty{}, nil
	}

	rec := s.getOrCreate(instance, invID, sid.GetBuildId())
	if shouldFinish {
		s.finalize(ctx, instance, invID, rec)
	}
	return &emptypb.Empty{}, nil
}

// PublishBuildToolEventStream receives Bazel's ordered BEP events, acknowledges
// each event, extracts build metrics, test results, coverage files, and JSON
// trace profile references, and persists the invocation summary on completion.
func (s *Server) PublishBuildToolEventStream(stream buildpb.PublishBuildEvent_PublishBuildToolEventStreamServer) error {
	ctx := stream.Context()
	var (
		authed   bool
		instance string
		invID    string
		buildID  string
		rec      *InvocationRecord
	)
	for {
		req, err := stream.Recv()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
		obe := req.GetOrderedBuildEvent()
		if obe == nil || obe.GetStreamId() == nil {
			return status.Error(codes.InvalidArgument, "missing ordered_build_event.stream_id")
		}
		sid := obe.GetStreamId()
		if authed && !sameStream(sid, invID, buildID) {
			return status.Error(codes.InvalidArgument, "stream_id changed within a single event stream")
		}
		if !authed {
			s.sweepStale(ctx, time.Now())
			instance, err = s.resolveInstance(ctx, req.GetProjectId())
			if err != nil {
				return err
			}
			invID = sid.GetInvocationId()
			buildID = sid.GetBuildId()
			if invID == "" {
				invID = buildID
			}
			if err := validateID(invID); err != nil {
				return status.Error(codes.InvalidArgument, err.Error())
			}
			rec = s.getOrCreate(instance, invID, buildID)
			authed = true
		}

		s.applyEvent(ctx, instance, rec, obe.GetEvent())

		if err := stream.Send(&buildpb.PublishBuildToolEventStreamResponse{
			StreamId:       sid,
			SequenceNumber: obe.GetSequenceNumber(),
		}); err != nil {
			return err
		}
	}
	if rec != nil {
		s.finalize(ctx, instance, invID, rec)
	}
	return nil
}

// sameStream reports whether sid names the invocation a stream started with.
func sameStream(sid *buildpb.StreamId, invID, buildID string) bool {
	got := sid.GetInvocationId()
	if got == "" {
		got = sid.GetBuildId()
	}
	return got == invID && (sid.GetBuildId() == "" || buildID == "" || sid.GetBuildId() == buildID)
}

// sweepStale persists and evicts active invocations that received no events
// for staleAfter. It scans at most once per minute.
func (s *Server) sweepStale(ctx context.Context, now time.Time) {
	s.mu.Lock()
	if now.Sub(s.lastSweep) < time.Minute {
		s.mu.Unlock()
		return
	}
	s.lastSweep = now
	var stale []*InvocationRecord
	for _, rec := range s.active {
		if now.Sub(rec.touched) > staleAfter {
			stale = append(stale, rec)
		}
	}
	s.mu.Unlock()
	for _, rec := range stale {
		slog.WarnContext(ctx, "evicting unfinished BES invocation", "invocation", rec.InvocationID, "instance", rec.Instance)
		s.finalize(ctx, rec.Instance, rec.InvocationID, rec)
	}
}

func (s *Server) getOrCreate(instance, invID, buildID string) *InvocationRecord {
	key := instance + "\x00" + invID
	s.mu.Lock()
	defer s.mu.Unlock()
	if rec, ok := s.active[key]; ok {
		if rec.BuildID == "" && buildID != "" {
			rec.BuildID = buildID
		}
		rec.touched = time.Now()
		return rec
	}
	// If the stream already persisted this invocation, reload it so a
	// trailing InvocationAttemptFinished lifecycle event merges cleanly
	// instead of overwriting the recorded metrics and events.
	if b, err := os.ReadFile(s.recordPath(instance, invID)); err == nil {
		var existing InvocationRecord
		if json.Unmarshal(b, &existing) == nil {
			if existing.BuildID == "" && buildID != "" {
				existing.BuildID = buildID
			}
			existing.emitted = true
			existing.touched = time.Now()
			s.active[key] = &existing
			return &existing
		}
	}
	rec := &InvocationRecord{
		InvocationID: invID,
		BuildID:      buildID,
		Instance:     instance,
		StartedAt:    time.Now().UTC(),
		touched:      time.Now(),
	}
	s.active[key] = rec
	return rec
}

func (s *Server) applyEvent(ctx context.Context, instance string, rec *InvocationRecord, ev *buildpb.BuildEvent) {
	if ev == nil {
		return
	}
	s.mu.Lock()
	rec.EventCount++
	rec.touched = time.Now()
	s.mu.Unlock()

	bazelAny := ev.GetBazelEvent()
	if bazelAny == nil {
		return
	}
	parsed := decodeBazelEvent(bazelAny.GetValue())

	s.mu.Lock()
	defer s.mu.Unlock()
	if parsed.started != nil {
		if parsed.started.Command != "" {
			rec.Command = parsed.started.Command
		}
		if parsed.started.BuildToolVersion != "" {
			rec.BuildToolVersion = parsed.started.BuildToolVersion
		}
		if parsed.started.Workspace != "" {
			rec.Workspace = parsed.started.Workspace
		}
		if parsed.started.Host != "" {
			rec.Host = parsed.started.Host
		}
		if parsed.started.User != "" {
			rec.User = parsed.started.User
		}
	}
	if parsed.finished != nil {
		now := time.Now().UTC()
		rec.FinishedAt = &now
		ok := parsed.finished.OverallSuccess
		rec.Success = &ok
		if parsed.finished.HasExitCode {
			code := parsed.finished.ExitCode
			rec.ExitCode = &code
			rec.ExitCodeName = parsed.finished.ExitCodeName
		}
	}
	if parsed.metrics != nil {
		rec.Metrics = parsed.metrics
	}
	for _, f := range parsed.toolLogs {
		rec.ToolLogs = append(rec.ToolLogs, f)
		if isProfileFile(f) {
			rec.Profiles = append(rec.Profiles, f)
		}
	}
	if parsed.testResult != nil {
		rec.Tests = append(rec.Tests, *parsed.testResult)
		s.metrics.tests.Add(ctx, 1, metric.WithAttributes(
			telemetry.AttrInstance.String(instance),
			attribute.String("status", parsed.testResult.Status),
		))
		for _, f := range parsed.testResult.Outputs {
			if isCoverageFile(f) {
				rec.CoverageFiles = appendUnique(rec.CoverageFiles, f)
			}
		}
	}
	for _, f := range parsed.namedFiles {
		if isCoverageFile(f) {
			rec.CoverageFiles = appendUnique(rec.CoverageFiles, f)
		}
	}
}

// appendUnique appends f unless files already holds the same artifact: a
// coverage report appears both in its TestResult and in a NamedSetOfFiles.
func appendUnique(files []FileRef, f FileRef) []FileRef {
	for _, g := range files {
		if g.URI == f.URI && g.Name == f.Name {
			return files
		}
	}
	return append(files, f)
}

func (s *Server) finalize(ctx context.Context, instance, invID string, rec *InvocationRecord) {
	key := instance + "\x00" + invID
	s.mu.Lock()
	snap := rec.clone()
	if snap.FinishedAt == nil {
		now := time.Now().UTC()
		snap.FinishedAt = &now
	}
	shouldEmit := !rec.emitted
	rec.emitted = true
	if s.active[key] == rec {
		delete(s.active, key)
	}
	s.mu.Unlock()

	if err := s.persist(snap); err != nil {
		slog.ErrorContext(ctx, "persisting BES invocation", "invocation", invID, "instance", instance, "err", err)
	}
	if !shouldEmit {
		return
	}
	s.emitTelemetry(ctx, snap)
	s.invocations.Finish(ctx, instance, invID)
}

func (s *Server) emitTelemetry(ctx context.Context, rec *InvocationRecord) {
	outcome := "unknown"
	if rec.Success != nil {
		if *rec.Success {
			outcome = "ok"
		} else {
			outcome = "failed"
		}
	}
	instAttr := telemetry.AttrInstance.String(rec.Instance)
	cmdAttr := attribute.String("command", rec.Command)
	s.metrics.builds.Add(ctx, 1, metric.WithAttributes(instAttr, cmdAttr, telemetry.AttrOutcome.String(outcome)))

	attrs := []attribute.KeyValue{
		attribute.String("bazel.invocation_id", rec.InvocationID),
		attribute.String("bazel.bep.command", rec.Command),
		attribute.String("bazel.bep.tool_version", rec.BuildToolVersion),
		attribute.String("bazel.bep.outcome", outcome),
		attribute.Int64("bazel.bep.events", rec.EventCount),
		attribute.Int("bazel.bep.tests", len(rec.Tests)),
		attribute.Int("bazel.bep.profiles", len(rec.Profiles)),
		attribute.Int("bazel.bep.coverage_files", len(rec.CoverageFiles)),
	}
	if bm := rec.Metrics; bm != nil {
		if bm.WallTimeMs > 0 {
			s.metrics.wallTime.Record(ctx, float64(bm.WallTimeMs)/1000.0, metric.WithAttributes(instAttr, cmdAttr))
		}
		if bm.CPUTimeMs > 0 {
			s.metrics.cpuTime.Record(ctx, float64(bm.CPUTimeMs)/1000.0, metric.WithAttributes(instAttr, cmdAttr))
		}
		if bm.AnalysisPhaseTimeMs > 0 {
			s.metrics.analysisTime.Record(ctx, float64(bm.AnalysisPhaseTimeMs)/1000.0, metric.WithAttributes(instAttr, cmdAttr))
		}
		if bm.ExecutionPhaseTimeMs > 0 {
			s.metrics.executionTime.Record(ctx, float64(bm.ExecutionPhaseTimeMs)/1000.0, metric.WithAttributes(instAttr, cmdAttr))
		}
		s.metrics.actionsCreated.Record(ctx, bm.ActionsCreated, metric.WithAttributes(instAttr))
		s.metrics.actionsExecuted.Record(ctx, bm.ActionsExecuted, metric.WithAttributes(instAttr))
		s.metrics.packagesLoaded.Record(ctx, bm.PackagesLoaded, metric.WithAttributes(instAttr))
		s.metrics.targetsConfigured.Record(ctx, bm.TargetsConfigured, metric.WithAttributes(instAttr))
		if bm.PeakPostGCHeapSize > 0 {
			s.metrics.peakHeapBytes.Record(ctx, bm.PeakPostGCHeapSize, metric.WithAttributes(instAttr))
		}
		attrs = append(attrs,
			attribute.Int64("bazel.bep.actions_created", bm.ActionsCreated),
			attribute.Int64("bazel.bep.actions_executed", bm.ActionsExecuted),
			attribute.Int64("bazel.bep.packages_loaded", bm.PackagesLoaded),
			attribute.Int64("bazel.bep.targets_configured", bm.TargetsConfigured),
			attribute.Int64("bazel.bep.wall_time_ms", bm.WallTimeMs),
			attribute.Int64("bazel.bep.analysis_time_ms", bm.AnalysisPhaseTimeMs),
			attribute.Int64("bazel.bep.execution_time_ms", bm.ExecutionPhaseTimeMs),
			attribute.Int64("bazel.bep.peak_post_gc_heap_bytes", bm.PeakPostGCHeapSize),
		)
	}

	sc := telemetry.InvocationSpanContext(rec.InvocationID)
	spanCtx := trace.ContextWithSpanContext(context.Background(), sc)
	_, span := telemetry.Tracer().Start(spanCtx, "bes.invocation",
		trace.WithTimestamp(rec.StartedAt),
		trace.WithAttributes(attrs...),
	)
	endTime := time.Now().UTC()
	if rec.FinishedAt != nil {
		endTime = *rec.FinishedAt
	}
	span.End(trace.WithTimestamp(endTime))
	slog.InfoContext(spanCtx, "bes invocation recorded",
		"invocation", rec.InvocationID, "instance", rec.Instance,
		"command", rec.Command, "outcome", outcome, "events", rec.EventCount,
		"tests", len(rec.Tests), "profiles", len(rec.Profiles), "coverage_files", len(rec.CoverageFiles))
}

func (s *Server) recordPath(instance, invID string) string {
	return filepath.Join(s.root, hex.EncodeToString([]byte(instance)), invID+".json")
}

func (s *Server) persist(rec *InvocationRecord) error {
	p := s.recordPath(rec.Instance, rec.InvocationID)
	b, err := json.MarshalIndent(rec, "", "  ")
	if err != nil {
		return err
	}
	if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
		return err
	}
	tmp, err := os.CreateTemp(filepath.Dir(p), ".tmp-*")
	if err != nil {
		return err
	}
	tmpName := tmp.Name()
	defer os.Remove(tmpName)
	if _, err := tmp.Write(b); err != nil {
		tmp.Close()
		return err
	}
	if err := tmp.Close(); err != nil {
		return err
	}
	return os.Rename(tmpName, p)
}

// Get returns a persisted or active invocation summary for instance and invID.
func (s *Server) Get(instance, invID string) (*InvocationRecord, error) {
	if err := validateID(invID); err != nil {
		return nil, err
	}
	s.mu.Lock()
	if rec, ok := s.active[instance+"\x00"+invID]; ok {
		cp := rec.clone()
		s.mu.Unlock()
		return cp, nil
	}
	s.mu.Unlock()

	b, err := os.ReadFile(s.recordPath(instance, invID))
	if errors.Is(err, fs.ErrNotExist) {
		return nil, fs.ErrNotExist
	}
	if err != nil {
		return nil, err
	}
	var rec InvocationRecord
	if err := json.Unmarshal(b, &rec); err != nil {
		return nil, err
	}
	return &rec, nil
}

// Handler returns a tenant-authorized HTTP handler serving GET /invocations/{id}.
// Callers supply the tenant token in the x-ci-substrate-tenant HTTP header and
// may optionally narrow the lookup with ?instance=<name>.
func (s *Server) Handler() http.Handler {
	mux := http.NewServeMux()
	mux.HandleFunc("/invocations/", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodGet {
			http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
			return
		}
		invID := strings.TrimPrefix(r.URL.Path, "/invocations/")
		if err := validateID(invID); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		tok := r.Header.Get(tenant.MetadataKey)
		ctx := metadata.NewIncomingContext(r.Context(), metadata.Pairs(tenant.MetadataKey, tok))
		if q := r.URL.Query().Get("instance"); q != "" {
			if err := s.tenants.Authorize(ctx, q); err != nil {
				writeAuthError(w, err)
				return
			}
			rec, err := s.Get(q, invID)
			if errors.Is(err, fs.ErrNotExist) {
				http.Error(w, "invocation not found", http.StatusNotFound)
				return
			}
			if err != nil {
				http.Error(w, "internal error", http.StatusInternalServerError)
				return
			}
			writeJSON(w, rec)
			return
		}
		allowed := s.tenants.Instances(ctx)
		if len(allowed) == 0 {
			http.Error(w, "unauthorized", http.StatusUnauthorized)
			return
		}
		names := make([]string, 0, len(allowed))
		for name := range allowed {
			names = append(names, name)
		}
		slices.Sort(names)
		for _, inst := range names {
			if rec, err := s.Get(inst, invID); err == nil {
				writeJSON(w, rec)
				return
			}
		}
		http.Error(w, "invocation not found", http.StatusNotFound)
	})
	return mux
}

func writeAuthError(w http.ResponseWriter, err error) {
	if status.Code(err) == codes.Unauthenticated {
		http.Error(w, "unauthorized", http.StatusUnauthorized)
		return
	}
	http.Error(w, "forbidden", http.StatusForbidden)
}

func writeJSON(w http.ResponseWriter, v any) {
	w.Header().Set("Content-Type", "application/json")
	if err := json.NewEncoder(w).Encode(v); err != nil {
		slog.Error("encoding BES response", "err", err)
	}
}

func validateID(id string) error {
	if id == "" || len(id) > 128 {
		return errors.New("invalid invocation id")
	}
	for _, c := range id {
		isAlphaNum := (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
		if !isAlphaNum && c != '-' && c != '_' && c != '.' {
			return errors.New("invalid invocation id")
		}
	}
	if id == "." || id == ".." || strings.Contains(id, "..") {
		return errors.New("invalid invocation id")
	}
	return nil
}
