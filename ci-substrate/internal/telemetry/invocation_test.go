package telemetry

import (
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/trace"
	"google.golang.org/grpc/metadata"
	"google.golang.org/protobuf/proto"
)

func carrier(t *testing.T, md *repb.RequestMetadata, traceparent string) propagation.MapCarrier {
	t.Helper()
	c := propagation.MapCarrier{}
	if md != nil {
		b, err := proto.Marshal(md)
		if err != nil {
			t.Fatal(err)
		}
		c[RequestMetadataKey] = string(b)
	}
	if traceparent != "" {
		c["traceparent"] = traceparent
	}
	return c
}

func TestPropagatorParentsOnInvocation(t *testing.T) {
	p := invocationPropagator{propagation.TraceContext{}}
	md := &repb.RequestMetadata{ToolInvocationId: "inv-1"}

	got := trace.SpanContextFromContext(p.Extract(t.Context(), carrier(t, md, "")))
	if want := InvocationSpanContext("inv-1"); !got.Equal(want) {
		t.Errorf("parent = %v, want the invocation's %v", got, want)
	}
	if InvocationSpanContext("inv-1").TraceID() == InvocationSpanContext("inv-2").TraceID() {
		t.Error("two invocations share a trace ID")
	}

	const traceparent = "00-0af7651916cd43dd8448eb211c80319c-b7ad6b7169203331-01"
	got = trace.SpanContextFromContext(p.Extract(t.Context(), carrier(t, md, traceparent)))
	if got.TraceID().String() != "0af7651916cd43dd8448eb211c80319c" {
		t.Errorf("with a traceparent, parent = %v, want the traceparent's", got)
	}

	if got := trace.SpanContextFromContext(p.Extract(t.Context(), carrier(t, nil, ""))); got.IsValid() {
		t.Errorf("with neither, parent = %v, want none", got)
	}
}

func TestOutgoingRenamesTool(t *testing.T) {
	md := &repb.RequestMetadata{
		ToolDetails:      &repb.ToolDetails{ToolName: "bazel"},
		ToolInvocationId: "inv-1",
		ActionId:         "action-1",
	}
	ctx := Outgoing(WithRequestMetadata(t.Context(), md), ToolRunner)
	out, _ := metadata.FromOutgoingContext(ctx)
	vs := out.Get(RequestMetadataKey)
	if len(vs) != 1 {
		t.Fatalf("outgoing %s = %q, want one value", RequestMetadataKey, vs)
	}
	got := parseRequestMetadata(vs[0])
	if got.GetToolInvocationId() != "inv-1" || got.GetActionId() != "action-1" || Peer(got) != "runner" {
		t.Errorf("outgoing RequestMetadata = %v, want inv-1 and action-1 from the runner", got)
	}
	if md.GetToolDetails().GetToolName() != "bazel" {
		t.Error("Outgoing changed the caller's RequestMetadata")
	}
	if base := t.Context(); Outgoing(base, ToolRunner) != base {
		t.Error("Outgoing without RequestMetadata changed the context")
	}
}

func TestPeer(t *testing.T) {
	for _, tc := range []struct {
		md   *repb.RequestMetadata
		want string
	}{
		{nil, "unknown"},
		{&repb.RequestMetadata{ToolDetails: &repb.ToolDetails{ToolName: "bazel"}}, "bazel"},
		{&repb.RequestMetadata{ToolDetails: &repb.ToolDetails{ToolName: ToolCascache}}, "cascache"},
		{&repb.RequestMetadata{ToolDetails: &repb.ToolDetails{ToolName: "buck2"}}, "other"},
	} {
		if got := Peer(tc.md); got != tc.want {
			t.Errorf("Peer(%v) = %q, want %q", tc.md, got, tc.want)
		}
	}
}
