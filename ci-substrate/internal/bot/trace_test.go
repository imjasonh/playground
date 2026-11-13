package bot_test

import (
	"net"
	"testing"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/propagation"
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/metric/metricdata"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/sdk/trace/tracetest"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/metadata"
	"google.golang.org/protobuf/proto"

	workerv1 "github.com/imjasonh/playground/ci-substrate/api/worker/v1"
	"github.com/imjasonh/playground/ci-substrate/internal/actioncache"
	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/bot"
	"github.com/imjasonh/playground/ci-substrate/internal/cache"
	"github.com/imjasonh/playground/ci-substrate/internal/exec"
	"github.com/imjasonh/playground/ci-substrate/internal/invocation"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

// serve runs srv on loopback and returns its address.
func serve(t *testing.T, srv *grpc.Server) string {
	t.Helper()
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	go srv.Serve(lis)
	t.Cleanup(srv.Stop)
	return lis.Addr().String()
}

func dial(t *testing.T, addr string, opts ...grpc.DialOption) *grpc.ClientConn {
	t.Helper()
	conn, err := grpc.NewClient(addr, append(opts, grpc.WithTransportCredentials(insecure.NewCredentials()))...)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { conn.Close() })
	return conn
}

// One Bazel invocation, through cas, cascache, and a runner, makes one
// trace whose ID is derived from the invocation ID, and one invocation
// summary with its cache hits, actions, and bytes.
func TestInvocationTrace(t *testing.T) {
	spans := tracetest.NewSpanRecorder()
	tp := sdktrace.NewTracerProvider(sdktrace.WithSpanProcessor(spans), sdktrace.WithIDGenerator(telemetry.IDGenerator()))
	reader := sdkmetric.NewManualReader()
	mp := sdkmetric.NewMeterProvider(sdkmetric.WithReader(reader))
	otel.SetTracerProvider(tp)
	otel.SetMeterProvider(mp)
	otel.SetTextMapPropagator(propagation.TraceContext{})

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
	invocations := invocation.New(time.Minute)
	sched := exec.New(store, actions, tenants, 0, invocations)
	origin := remote.NewOrigin(store, actions, tenants, invocations)
	casSrv := grpc.NewServer(telemetry.ServerOptions()...)
	repb.RegisterContentAddressableStorageServer(casSrv, origin)
	repb.RegisterActionCacheServer(casSrv, origin)
	bytestream.RegisterByteStreamServer(casSrv, origin)
	repb.RegisterExecutionServer(casSrv, sched)
	workerv1.RegisterWorkerServiceServer(casSrv, sched)
	casAddr := serve(t, casSrv)
	casConn := dial(t, casAddr, telemetry.DialOptions()...)
	casClient := remote.NewClient(casConn)
	// Bazel sends no trace context, only RequestMetadata.
	bazelConn := dial(t, casAddr)
	bazelClient := remote.NewClient(bazelConn)

	cacheStore, err := blob.NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	cacheSrv := grpc.NewServer(telemetry.ServerOptions()...)
	cs := remote.NewCacheServer(cache.New(cacheStore, casClient), casClient, tenants)
	repb.RegisterContentAddressableStorageServer(cacheSrv, cs)
	bytestream.RegisterByteStreamServer(cacheSrv, cs)
	cacheClient := remote.NewClient(dial(t, serve(t, cacheSrv), telemetry.DialOptions()...))

	b, err := bot.New(bot.Config{
		BotID:     "bot-trace",
		Token:     token,
		Worker:    workerv1.NewWorkerServiceClient(casConn),
		Origin:    casClient,
		Cache:     cacheClient,
		WorkDir:   t.TempDir(),
		InputMode: bot.InputCopy,
	})
	if err != nil {
		t.Fatal(err)
	}

	const invocationID = "11111111-2222-3333-4444-555555555555"
	md, err := proto.Marshal(&repb.RequestMetadata{
		ToolDetails:      &repb.ToolDetails{ToolName: "bazel", ToolVersion: "8.4.2"},
		ToolInvocationId: invocationID,
		ActionMnemonic:   "Genrule",
		TargetId:         "//:hello",
	})
	if err != nil {
		t.Fatal(err)
	}
	bazel := metadata.AppendToOutgoingContext(tenant.Outgoing(t.Context(), token), telemetry.RequestMetadataKey, string(md))

	input, err := bazelClient.Upload(bazel, instance, []byte("hello\n"))
	if err != nil {
		t.Fatal(err)
	}
	root, err := bazelClient.Upload(bazel, instance, mustMarshal(t, &repb.Directory{
		Files: []*repb.FileNode{{Name: "in.txt", Digest: input}},
	}))
	if err != nil {
		t.Fatal(err)
	}
	cmd, err := bazelClient.Upload(bazel, instance, mustMarshal(t, &repb.Command{
		Arguments:   []string{"sh", "-c", "tr a-z A-Z < in.txt > out.txt"},
		OutputPaths: []string{"out.txt"},
	}))
	if err != nil {
		t.Fatal(err)
	}
	action, err := bazelClient.Upload(bazel, instance, mustMarshal(t, &repb.Action{CommandDigest: cmd, InputRootDigest: root}))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := repb.NewActionCacheClient(bazelConn).GetActionResult(bazel, &repb.GetActionResultRequest{InstanceName: instance, ActionDigest: action}); err == nil {
		t.Fatal("GetActionResult before the action ran: got a result")
	}

	stream, err := repb.NewExecutionClient(bazelConn).Execute(bazel, &repb.ExecuteRequest{InstanceName: instance, ActionDigest: action})
	if err != nil {
		t.Fatal(err)
	}
	if ran, err := b.RunOnce(t.Context()); err != nil || !ran {
		t.Fatalf("RunOnce = %v, %v", ran, err)
	}
	for {
		op, err := stream.Recv()
		if err != nil {
			t.Fatal(err)
		}
		if op.GetDone() {
			break
		}
	}
	if _, err := repb.NewActionCacheClient(bazelConn).GetActionResult(bazel, &repb.GetActionResultRequest{InstanceName: instance, ActionDigest: action}); err != nil {
		t.Fatalf("GetActionResult after the action ran: %v", err)
	}

	summaries := invocations.Flush(t.Context(), time.Time{})
	if len(summaries) != 1 {
		t.Fatalf("got %d invocations, want 1", len(summaries))
	}
	s := summaries[0]
	if s.ID != invocationID || s.Tool != "bazel" {
		t.Errorf("invocation = %q from %q, want %q from bazel", s.ID, s.Tool, invocationID)
	}
	if s.ActionCacheHits != 1 || s.ActionCacheMisses != 1 || s.ExecuteRequests != 1 || s.ActionsRun != 1 {
		t.Errorf("counts = %+v, want one action cache hit, one miss, one Execute, one action run", s.Counts)
	}
	if s.BlobsUploaded != 4 || s.RunnerBytesUploaded == 0 || s.CacheFillBytes == 0 {
		t.Errorf("counts = %+v, want 4 blobs uploaded, runner outputs, and cascache fills", s.Counts)
	}
	if got := s.HitRatio(); got != 0.5 {
		t.Errorf("HitRatio = %v, want 0.5", got)
	}

	if err := tp.ForceFlush(t.Context()); err != nil {
		t.Fatal(err)
	}
	want := telemetry.InvocationSpanContext(invocationID).TraceID()
	names := map[string]bool{}
	for _, sp := range spans.Ended() {
		if sp.SpanContext().TraceID() != want {
			t.Errorf("span %q is in trace %s, want %s", sp.Name(), sp.SpanContext().TraceID(), want)
		}
		names[sp.Name()] = true
	}
	for _, name := range []string{
		"bazel invocation",
		"build.bazel.remote.execution.v2.Execution/Execute",
		"build.bazel.remote.execution.v2.ContentAddressableStorage/BatchReadBlobs",
		"scheduler.queue",
		"runner.execute",
		"runner.fetch_action",
		"runner.prepare_inputs",
		"runner.run",
		"runner.upload_outputs",
		"runner.complete",
		"cascache.origin_fetch",
	} {
		if !names[name] {
			t.Errorf("no %q span; got %v", name, names)
		}
	}

	var rm metricdata.ResourceMetrics
	if err := reader.Collect(t.Context(), &rm); err != nil {
		t.Fatal(err)
	}
	got := map[string]bool{}
	for _, sm := range rm.ScopeMetrics {
		for _, m := range sm.Metrics {
			got[m.Name] = true
		}
	}
	for _, name := range []string{
		"cas.blob.bytes",
		"cas.action_cache.requests",
		"cas.find_missing.digests",
		"cascache.requests",
		"cascache.bytes",
		"scheduler.executions",
		"scheduler.jobs.completed",
		"scheduler.queue.duration",
		"runner.actions",
		"runner.stage.duration",
		"runner.upload.bytes",
		"bazel.invocations",
		"bazel.invocation.cache_hit_ratio",
		"rpc.server.call.duration",
		"rpc.client.call.duration",
	} {
		if !got[name] {
			t.Errorf("no %q metric; got %v", name, got)
		}
	}
}

func mustMarshal(t *testing.T, m proto.Message) []byte {
	t.Helper()
	b, err := proto.Marshal(m)
	if err != nil {
		t.Fatal(err)
	}
	return b
}
