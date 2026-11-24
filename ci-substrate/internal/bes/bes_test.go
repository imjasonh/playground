package bes

import (
	"context"
	"encoding/json"
	"net"
	"net/http"
	"net/http/httptest"
	"testing"

	buildpb "google.golang.org/genproto/googleapis/devtools/build/v1"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"
	"google.golang.org/grpc/test/bufconn"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/types/known/anypb"

	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

func encodeString(num protowire.Number, s string) []byte {
	var b []byte
	b = protowire.AppendTag(b, num, protowire.BytesType)
	return protowire.AppendString(b, s)
}

func encodeVarint(num protowire.Number, v uint64) []byte {
	var b []byte
	b = protowire.AppendTag(b, num, protowire.VarintType)
	return protowire.AppendVarint(b, v)
}

func encodeMsg(num protowire.Number, inner []byte) []byte {
	var b []byte
	b = protowire.AppendTag(b, num, protowire.BytesType)
	return protowire.AppendBytes(b, inner)
}

func concat(parts ...[]byte) []byte {
	var out []byte
	for _, p := range parts {
		out = append(out, p...)
	}
	return out
}

func TestBESStreamMetricsProfileCoverageAndIsolation(t *testing.T) {
	reg := tenant.NewRegistry()
	reg.Allow("tok-a", "tenant-a")
	reg.Allow("tok-b", "tenant-b")

	srv, err := New(t.TempDir(), reg, nil)
	if err != nil {
		t.Fatal(err)
	}
	lis := bufconn.Listen(1 << 20)
	gs := grpc.NewServer()
	buildpb.RegisterPublishBuildEventServer(gs, srv)
	go func() { _ = gs.Serve(lis) }()
	t.Cleanup(func() {
		gs.Stop()
		lis.Close()
	})
	conn, err := grpc.NewClient("passthrough:///bufnet",
		grpc.WithContextDialer(func(ctx context.Context, _ string) (net.Conn, error) {
			return lis.DialContext(ctx)
		}),
		grpc.WithTransportCredentials(insecure.NewCredentials()),
	)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { conn.Close() })
	client := buildpb.NewPublishBuildEventClient(conn)

	ctxA := tenant.Outgoing(t.Context(), "tok-a")
	ctxB := tenant.Outgoing(t.Context(), "tok-b")
	invID := "inv-12345"
	sid := &buildpb.StreamId{
		BuildId:      "build-1",
		InvocationId: invID,
		Component:    buildpb.StreamId_TOOL,
	}

	// Cross-tenant lifecycle event must be denied.
	if _, err := client.PublishLifecycleEvent(ctxB, &buildpb.PublishLifecycleEventRequest{
		ProjectId: "tenant-a",
		BuildEvent: &buildpb.OrderedBuildEvent{
			StreamId:       sid,
			SequenceNumber: 1,
		},
	}); status.Code(err) != codes.PermissionDenied {
		t.Fatalf("cross-tenant PublishLifecycleEvent = %v, want PermissionDenied", err)
	}

	// BuildStarted
	startedPayload := encodeMsg(5, concat(
		encodeString(1, invID),
		encodeString(3, "8.4.2"),
		encodeString(5, "coverage"),
		encodeString(7, "/workspace"),
	))
	// TestResult with coverage.dat output
	testPayload := concat(
		encodeMsg(1, encodeMsg(8, encodeString(1, "//pkg:foo_test"))),
		encodeMsg(10, concat(
			encodeVarint(5, 1), // PASSED
			encodeMsg(2, concat(
				encodeString(1, "test.log"),
				encodeString(2, "bytestream://cas/tenant-a/blobs/aaa/10"),
			)),
			encodeMsg(2, concat(
				encodeString(1, "coverage.dat"),
				encodeString(2, "bytestream://cas/tenant-a/blobs/bbb/200"),
				encodeString(5, "bbb"),
				encodeVarint(6, 200),
			)),
		)),
	)
	// BuildToolLogs with JSON trace profile
	logsPayload := encodeMsg(23, encodeMsg(1, concat(
		encodeString(1, "command.profile.gz"),
		encodeString(2, "bytestream://cas/tenant-a/blobs/ccc/5000"),
		encodeString(5, "ccc"),
		encodeVarint(6, 5000),
	)))
	// BuildMetrics
	metricsPayload := encodeMsg(24, concat(
		encodeMsg(1, concat(encodeVarint(1, 42), encodeVarint(2, 12), encodeVarint(5, 8))),
		encodeMsg(2, concat(encodeVarint(1, 100<<20), encodeVarint(2, 250<<20))),
		encodeMsg(3, encodeVarint(2, 15)),
		encodeMsg(4, encodeVarint(1, 4)),
		encodeMsg(5, concat(encodeVarint(1, 4500), encodeVarint(2, 12000), encodeVarint(3, 1500), encodeVarint(4, 10000))),
		encodeMsg(6, concat(encodeVarint(11, 1), encodeVarint(12, 1), encodeString(13, "srv-1"))),
		encodeMsg(10, encodeMsg(1, concat(encodeVarint(1, 1024), encodeVarint(2, 2048)))),
	))
	// BuildFinished
	finishedPayload := concat(
		encodeMsg(14, encodeMsg(3, concat(encodeString(1, "SUCCESS"), encodeVarint(2, 0)))),
		encodeVarint(20, 1),
	)

	stream, err := client.PublishBuildToolEventStream(ctxA)
	if err != nil {
		t.Fatal(err)
	}
	payloads := [][]byte{startedPayload, testPayload, logsPayload, metricsPayload, finishedPayload}
	for i, p := range payloads {
		seq := int64(i + 1)
		if err := stream.Send(&buildpb.PublishBuildToolEventStreamRequest{
			ProjectId: "tenant-a",
			OrderedBuildEvent: &buildpb.OrderedBuildEvent{
				StreamId:       sid,
				SequenceNumber: seq,
				Event: &buildpb.BuildEvent{
					Event: &buildpb.BuildEvent_BazelEvent{
						BazelEvent: &anypb.Any{
							TypeUrl: "type.googleapis.com/build_event_stream.BuildEvent",
							Value:   p,
						},
					},
				},
			},
		}); err != nil {
			t.Fatalf("Send seq %d: %v", seq, err)
		}
		ack, err := stream.Recv()
		if err != nil {
			t.Fatalf("Recv ack %d: %v", seq, err)
		}
		if ack.GetSequenceNumber() != seq {
			t.Errorf("ack seq = %d, want %d", ack.GetSequenceNumber(), seq)
		}
	}
	if err := stream.CloseSend(); err != nil {
		t.Fatal(err)
	}
	if _, err := stream.Recv(); err == nil {
		t.Fatal("expected EOF after CloseSend")
	}
	// Bazel sends InvocationAttemptFinished and BuildFinished after the tool
	// event stream closes; verify they do not overwrite the recorded events.
	if _, err := client.PublishLifecycleEvent(ctxA, &buildpb.PublishLifecycleEventRequest{
		ProjectId: "tenant-a",
		BuildEvent: &buildpb.OrderedBuildEvent{
			StreamId:       &buildpb.StreamId{BuildId: "build-1", InvocationId: invID, Component: buildpb.StreamId_CONTROLLER},
			SequenceNumber: 2,
			Event:          &buildpb.BuildEvent{Event: &buildpb.BuildEvent_InvocationAttemptFinished_{InvocationAttemptFinished: &buildpb.BuildEvent_InvocationAttemptFinished{}}},
		},
	}); err != nil {
		t.Fatalf("PublishLifecycleEvent(InvocationAttemptFinished): %v", err)
	}
	if _, err := client.PublishLifecycleEvent(ctxA, &buildpb.PublishLifecycleEventRequest{
		ProjectId: "tenant-a",
		BuildEvent: &buildpb.OrderedBuildEvent{
			StreamId:       &buildpb.StreamId{BuildId: "build-1", Component: buildpb.StreamId_CONTROLLER},
			SequenceNumber: 2,
			Event:          &buildpb.BuildEvent{Event: &buildpb.BuildEvent_BuildFinished_{BuildFinished: &buildpb.BuildEvent_BuildFinished{}}},
		},
	}); err != nil {
		t.Fatalf("PublishLifecycleEvent(BuildFinished): %v", err)
	}

	// Verify persisted record via HTTP handler with tenant isolation.
	h := srv.Handler()
	reqB := httptest.NewRequest(http.MethodGet, "/invocations/"+invID, nil)
	reqB.Header.Set(tenant.MetadataKey, "tok-b")
	rrB := httptest.NewRecorder()
	h.ServeHTTP(rrB, reqB)
	if rrB.Code != http.StatusNotFound {
		t.Errorf("tenant B GET status = %d, want 404", rrB.Code)
	}

	reqA := httptest.NewRequest(http.MethodGet, "/invocations/"+invID, nil)
	reqA.Header.Set(tenant.MetadataKey, "tok-a")
	rrA := httptest.NewRecorder()
	h.ServeHTTP(rrA, reqA)
	if rrA.Code != http.StatusOK {
		t.Fatalf("tenant A GET status = %d, body = %s", rrA.Code, rrA.Body.String())
	}
	var got InvocationRecord
	if err := json.Unmarshal(rrA.Body.Bytes(), &got); err != nil {
		t.Fatal(err)
	}
	if got.Command != "coverage" || got.BuildToolVersion != "8.4.2" {
		t.Errorf("command/version = (%q, %q), want (coverage, 8.4.2)", got.Command, got.BuildToolVersion)
	}
	if got.Success == nil || !*got.Success || got.ExitCode == nil || *got.ExitCode != 0 {
		t.Errorf("finished state = (success=%v, exit=%v), want (true, 0)", got.Success, got.ExitCode)
	}
	if got.Metrics == nil || got.Metrics.ActionsExecuted != 12 || got.Metrics.WallTimeMs != 12000 || got.Metrics.PeakPostGCHeapSize != 250<<20 {
		t.Errorf("unexpected build_metrics: %+v", got.Metrics)
	}
	if len(got.Profiles) != 1 || got.Profiles[0].Name != "command.profile.gz" {
		t.Errorf("profiles = %+v, want command.profile.gz", got.Profiles)
	}
	if len(got.CoverageFiles) != 1 || got.CoverageFiles[0].Name != "coverage.dat" {
		t.Errorf("coverage_files = %+v, want coverage.dat", got.CoverageFiles)
	}
	if len(got.Tests) != 1 || got.Tests[0].Label != "//pkg:foo_test" || got.Tests[0].Status != "PASSED" {
		t.Errorf("tests = %+v, want PASSED //pkg:foo_test", got.Tests)
	}
}

func TestDecodeMalformedBuildFinished(t *testing.T) {
	// Field 3 (ExitCode) containing a truncated string (field 1, declared len 50,
	// only 2 bytes present) and a truncated varint (field 2, continuation bit set).
	// Previously caused an infinite loop in decodeBuildFinished.
	badExit := encodeString(1, "ab")
	badExit[1] = 50 // corrupt declared length
	ev := encodeMsg(14, encodeMsg(3, badExit))
	parsed := decodeBazelEvent(ev)
	if parsed.finished == nil || !parsed.finished.HasExitCode {
		t.Errorf("expected finished event with HasExitCode, got %+v", parsed.finished)
	}

	// Truncated varint inside ExitCode.code (field 2).
	var badVarint []byte
	badVarint = protowire.AppendTag(badVarint, 2, protowire.VarintType)
	badVarint = append(badVarint, 0x80)
	_ = decodeBazelEvent(encodeMsg(14, encodeMsg(3, badVarint)))
}
