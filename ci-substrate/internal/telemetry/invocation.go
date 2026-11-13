package telemetry

import (
	"context"
	"crypto/sha256"
	"encoding/binary"
	"math/rand/v2"
	"strings"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/propagation"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
	"google.golang.org/grpc/metadata"
	"google.golang.org/protobuf/proto"
)

// RequestMetadataKey is the gRPC header in which REAPI clients send a
// RequestMetadata on every call.
const RequestMetadataKey = "build.bazel.remote.execution.v2.requestmetadata-bin"

// Tool names the ci-substrate components send in RequestMetadata, so the
// server can tell their traffic from the build client's.
const (
	ToolRunner   = "ci-substrate-runner"
	ToolCascache = "ci-substrate-cascache"
)

// InvocationSpanContext returns the span that stands for one Bazel
// invocation: its trace and span IDs are hashes of the invocation ID.
//
// Bazel sends no trace context, but it sends the same tool_invocation_id
// on every call of a build. Each server that sees a call with no
// traceparent parents its span here, so cas, cascache, and every runner
// put a build's spans in one trace without coordinating, and cas later
// records the invocation span itself (see the invocation package).
func InvocationSpanContext(invocationID string) trace.SpanContext {
	sum := sha256.Sum256([]byte("ci-substrate/invocation/" + invocationID))
	var tid trace.TraceID
	var sid trace.SpanID
	copy(tid[:], sum[:16])
	copy(sid[:], sum[16:24])
	return trace.NewSpanContext(trace.SpanContextConfig{
		TraceID:    tid,
		SpanID:     sid,
		TraceFlags: trace.FlagsSampled,
		Remote:     true,
	})
}

type forcedIDsKey struct{}

// WithIDs makes the next root span started from ctx use the IDs of sc.
func WithIDs(ctx context.Context, sc trace.SpanContext) context.Context {
	return context.WithValue(ctx, forcedIDsKey{}, sc)
}

// IDGenerator returns the ID generator Setup installs: random IDs, except
// for a root span started from a context made by WithIDs.
func IDGenerator() sdktrace.IDGenerator { return idGenerator{} }

type idGenerator struct{}

func (idGenerator) NewIDs(ctx context.Context) (trace.TraceID, trace.SpanID) {
	if sc, ok := ctx.Value(forcedIDsKey{}).(trace.SpanContext); ok {
		return sc.TraceID(), sc.SpanID()
	}
	var tid trace.TraceID
	for !tid.IsValid() {
		binary.BigEndian.PutUint64(tid[:8], rand.Uint64())
		binary.BigEndian.PutUint64(tid[8:], rand.Uint64())
	}
	return tid, randomSpanID()
}

func (idGenerator) NewSpanID(context.Context, trace.TraceID) trace.SpanID { return randomSpanID() }

func randomSpanID() trace.SpanID {
	var sid trace.SpanID
	for !sid.IsValid() {
		binary.BigEndian.PutUint64(sid[:], rand.Uint64())
	}
	return sid
}

// invocationPropagator extracts with inner and, when that finds no parent,
// parents the call on the invocation span named by its RequestMetadata.
type invocationPropagator struct{ inner propagation.TextMapPropagator }

func (p invocationPropagator) Inject(ctx context.Context, c propagation.TextMapCarrier) {
	p.inner.Inject(ctx, c)
}

func (p invocationPropagator) Extract(ctx context.Context, c propagation.TextMapCarrier) context.Context {
	ctx = p.inner.Extract(ctx, c)
	if trace.SpanContextFromContext(ctx).IsValid() {
		return ctx
	}
	md := parseRequestMetadata(c.Get(RequestMetadataKey))
	if id := md.GetToolInvocationId(); id != "" {
		ctx = trace.ContextWithRemoteSpanContext(ctx, InvocationSpanContext(id))
	}
	return ctx
}

func (p invocationPropagator) Fields() []string {
	return append(p.inner.Fields(), RequestMetadataKey)
}

func parseRequestMetadata(b string) *repb.RequestMetadata {
	if b == "" {
		return nil
	}
	md := &repb.RequestMetadata{}
	if proto.Unmarshal([]byte(b), md) != nil {
		return nil
	}
	return md
}

type requestMetadataKey struct{}

// RequestMetadata returns the RequestMetadata of the call ctx belongs to:
// the one ServerOptions stored for an incoming call, or nil.
func RequestMetadata(ctx context.Context) *repb.RequestMetadata {
	md, _ := ctx.Value(requestMetadataKey{}).(*repb.RequestMetadata)
	return md
}

// WithRequestMetadata stores md as ctx's RequestMetadata, for work that
// continues a call outside of it, such as a runner executing a job.
func WithRequestMetadata(ctx context.Context, md *repb.RequestMetadata) context.Context {
	if md == nil {
		return ctx
	}
	return context.WithValue(ctx, requestMetadataKey{}, md)
}

// incomingRequestMetadata reads the RequestMetadata header of a call.
func incomingRequestMetadata(ctx context.Context) *repb.RequestMetadata {
	vs := metadata.ValueFromIncomingContext(ctx, RequestMetadataKey)
	if len(vs) == 0 {
		return nil
	}
	return parseRequestMetadata(vs[0])
}

// Outgoing sends ctx's RequestMetadata on outgoing calls, with the tool
// name replaced by tool, so the server attributes them to the same
// invocation and action and knows which component made them.
func Outgoing(ctx context.Context, tool string) context.Context {
	md := RequestMetadata(ctx)
	if md == nil {
		return ctx
	}
	md = proto.CloneOf(md)
	md.ToolDetails = &repb.ToolDetails{ToolName: tool}
	b, err := proto.Marshal(md)
	if err != nil {
		return ctx
	}
	return metadata.AppendToOutgoingContext(ctx, RequestMetadataKey, string(b))
}

// Peer names the kind of client that sent md: bazel for a build client,
// runner or cascache for ci-substrate's own components, and unknown when
// the call carried no RequestMetadata.
func Peer(md *repb.RequestMetadata) string {
	switch name := md.GetToolDetails().GetToolName(); {
	case md == nil:
		return "unknown"
	case name == ToolRunner:
		return "runner"
	case name == ToolCascache:
		return "cascache"
	case strings.Contains(strings.ToLower(name), "bazel"):
		return "bazel"
	default:
		return "other"
	}
}

// Attributes describes md on a span.
func Attributes(md *repb.RequestMetadata) []attribute.KeyValue {
	if md == nil {
		return nil
	}
	var as []attribute.KeyValue
	add := func(k, v string) {
		if v != "" {
			as = append(as, attribute.String(k, v))
		}
	}
	add("bazel.invocation_id", md.GetToolInvocationId())
	add("bazel.correlated_invocations_id", md.GetCorrelatedInvocationsId())
	add("bazel.action_id", md.GetActionId())
	add("bazel.action_mnemonic", md.GetActionMnemonic())
	add("bazel.target_id", md.GetTargetId())
	add("bazel.configuration_id", md.GetConfigurationId())
	add("bazel.tool", md.GetToolDetails().GetToolName())
	add("bazel.tool_version", md.GetToolDetails().GetToolVersion())
	as = append(as, attribute.String("ci_substrate.peer", Peer(md)))
	return as
}
