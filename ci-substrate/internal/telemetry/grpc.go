package telemetry

import (
	"context"

	"go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
	"go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc/filters"
	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/trace"
	"google.golang.org/grpc"
)

// untraced selects the calls that get neither spans nor RPC metrics: health
// probes, and the runner's long polls and heartbeats, which would put a
// span a second per idle runner in the trace backend. The scheduler's own
// metrics cover them.
var untraced = filters.None(
	filters.HealthCheck(),
	filters.MethodName("Lease"),
	filters.MethodName("Heartbeat"),
	filters.MethodName("Status"),
)

// ServerOptions trace and measure every call a server handles (the
// rpc.server.* metrics), parent calls without a traceparent on their
// invocation (see InvocationSpanContext), and store each call's
// RequestMetadata on its context and span.
func ServerOptions() []grpc.ServerOption {
	return []grpc.ServerOption{
		grpc.StatsHandler(otelgrpc.NewServerHandler(
			otelgrpc.WithPropagators(invocationPropagator{otel.GetTextMapPropagator()}),
			otelgrpc.WithFilter(untraced),
		)),
		grpc.ChainUnaryInterceptor(func(ctx context.Context, req any, _ *grpc.UnaryServerInfo, h grpc.UnaryHandler) (any, error) {
			return h(annotate(ctx), req)
		}),
		grpc.ChainStreamInterceptor(func(srv any, ss grpc.ServerStream, _ *grpc.StreamServerInfo, h grpc.StreamHandler) error {
			return h(srv, annotatedStream{ss, annotate(ss.Context())})
		}),
	}
}

// DialOptions trace and measure every call a client makes (the
// rpc.client.* metrics) and send the trace context with it.
func DialOptions() []grpc.DialOption {
	return []grpc.DialOption{
		grpc.WithStatsHandler(otelgrpc.NewClientHandler(otelgrpc.WithFilter(untraced))),
	}
}

func annotate(ctx context.Context) context.Context {
	md := incomingRequestMetadata(ctx)
	if md == nil {
		return ctx
	}
	trace.SpanFromContext(ctx).SetAttributes(Attributes(md)...)
	return WithRequestMetadata(ctx, md)
}

// annotatedStream overrides the stream's context, which a
// grpc.ServerStream can only expose through Context.
type annotatedStream struct {
	grpc.ServerStream
	ctx context.Context // pasta:ignore go_context_field
}

func (s annotatedStream) Context() context.Context { return s.ctx }
