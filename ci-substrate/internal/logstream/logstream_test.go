package logstream

import (
	"bytes"
	"context"
	"io"
	"net"
	"testing"

	logstreampb "github.com/bazelbuild/remote-apis/build/bazel/remote/logstream/v1"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"
	"google.golang.org/grpc/test/bufconn"

	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

type testHarness struct {
	ls logstreampb.LogStreamServiceClient
	bs bytestream.ByteStreamClient
}

func startTestServer(t *testing.T, reg *tenant.Registry) *testHarness {
	t.Helper()
	lis := bufconn.Listen(1 << 20)
	srv := grpc.NewServer()
	s := New(reg)
	logstreampb.RegisterLogStreamServiceServer(srv, s)
	bytestream.RegisterByteStreamServer(srv, &bsBridge{s: s})
	go func() { _ = srv.Serve(lis) }()
	t.Cleanup(func() {
		srv.Stop()
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
	return &testHarness{
		ls: logstreampb.NewLogStreamServiceClient(conn),
		bs: bytestream.NewByteStreamClient(conn),
	}
}

type bsBridge struct {
	bytestream.UnimplementedByteStreamServer
	s *Server
}

func (b *bsBridge) Read(req *bytestream.ReadRequest, stream bytestream.ByteStream_ReadServer) error {
	return b.s.Read(req, stream)
}

func (b *bsBridge) Write(stream bytestream.ByteStream_WriteServer) error {
	return b.s.Write(stream)
}

func (b *bsBridge) QueryWriteStatus(ctx context.Context, req *bytestream.QueryWriteStatusRequest) (*bytestream.QueryWriteStatusResponse, error) {
	return b.s.QueryWriteStatus(ctx, req)
}

func TestLogStreamLiveTailAndIsolation(t *testing.T) {
	reg := tenant.NewRegistry()
	reg.Allow("tok-a", "tenant-a")
	reg.Allow("tok-b", "tenant-b")
	h := startTestServer(t, reg)

	ctxA := tenant.Outgoing(t.Context(), "tok-a")
	ctxB := tenant.Outgoing(t.Context(), "tok-b")

	// Tenant B cannot create a stream under tenant A.
	if _, err := h.ls.CreateLogStream(ctxB, &logstreampb.CreateLogStreamRequest{Parent: "tenant-a"}); status.Code(err) != codes.PermissionDenied {
		t.Fatalf("cross-tenant CreateLogStream = %v, want PermissionDenied", err)
	}

	streamInfo, err := h.ls.CreateLogStream(ctxA, &logstreampb.CreateLogStreamRequest{Parent: "tenant-a"})
	if err != nil {
		t.Fatalf("CreateLogStream: %v", err)
	}

	// Reading the write_resource_name must fail with InvalidArgument.
	badRead, err := h.bs.Read(ctxA, &bytestream.ReadRequest{ResourceName: streamInfo.GetWriteResourceName()})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := badRead.Recv(); status.Code(err) != codes.InvalidArgument {
		t.Errorf("Read(write_resource_name) = %v, want InvalidArgument", err)
	}

	// Tenant B cannot read tenant A's log stream.
	crossRead, err := h.bs.Read(ctxB, &bytestream.ReadRequest{ResourceName: streamInfo.GetName()})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := crossRead.Recv(); status.Code(err) != codes.PermissionDenied {
		t.Errorf("cross-tenant Read = %v, want PermissionDenied", err)
	}

	// Start a live reader before the writer finishes.
	readDone := make(chan []byte, 1)
	readErr := make(chan error, 1)
	go func() {
		rs, err := h.bs.Read(ctxA, &bytestream.ReadRequest{ResourceName: streamInfo.GetName()})
		if err != nil {
			readErr <- err
			return
		}
		var buf bytes.Buffer
		for {
			resp, err := rs.Recv()
			if err == io.EOF {
				readDone <- buf.Bytes()
				return
			}
			if err != nil {
				readErr <- err
				return
			}
			buf.Write(resp.GetData())
		}
	}()

	ws, err := h.bs.Write(ctxA)
	if err != nil {
		t.Fatal(err)
	}
	if err := ws.Send(&bytestream.WriteRequest{
		ResourceName: streamInfo.GetWriteResourceName(),
		WriteOffset:  0,
		Data:         []byte("line 1\n"),
	}); err != nil {
		t.Fatal(err)
	}
	if err := ws.Send(&bytestream.WriteRequest{
		ResourceName: streamInfo.GetWriteResourceName(),
		WriteOffset:  7,
		Data:         []byte("line 2\n"),
		FinishWrite:  true,
	}); err != nil {
		t.Fatal(err)
	}
	wresp, err := ws.CloseAndRecv()
	if err != nil {
		t.Fatalf("CloseAndRecv: %v", err)
	}
	if wresp.GetCommittedSize() != 14 {
		t.Errorf("CommittedSize = %d, want 14", wresp.GetCommittedSize())
	}

	select {
	case err := <-readErr:
		t.Fatalf("Read failed: %v", err)
	case got := <-readDone:
		if string(got) != "line 1\nline 2\n" {
			t.Errorf("Read = %q, want %q", got, "line 1\nline 2\n")
		}
	}

	q, err := h.bs.QueryWriteStatus(ctxA, &bytestream.QueryWriteStatusRequest{ResourceName: streamInfo.GetWriteResourceName()})
	if err != nil {
		t.Fatalf("QueryWriteStatus: %v", err)
	}
	if !q.GetComplete() || q.GetCommittedSize() != 14 {
		t.Errorf("QueryWriteStatus = (%v, %d), want (true, 14)", q.GetComplete(), q.GetCommittedSize())
	}
}
