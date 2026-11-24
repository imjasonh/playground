// Package logstream implements the Bazel Remote Logstream API
// (build.bazel.remote.logstream.v1) and its ByteStream read/write backing. A
// producer creates a stream with CreateLogStream, writes chunks to its
// write_resource_name, and one or more consumers tail the stream live over
// ByteStream.Read using its read name.
package logstream

import (
	"context"
	"crypto/subtle"
	"fmt"
	"io"
	"strings"
	"sync"
	"time"

	logstreampb "github.com/bazelbuild/remote-apis/build/bazel/remote/logstream/v1"
	"github.com/google/uuid"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

const (
	// defaultMaxStreamBytes bounds a single log stream in memory.
	defaultMaxStreamBytes = 64 << 20
	// defaultTTL is how long a finished log stream remains readable.
	defaultTTL = 15 * time.Minute
)

// Server implements LogStreamServiceServer and serves ByteStream reads and
// writes for logstream resources.
type Server struct {
	logstreampb.UnimplementedLogStreamServiceServer

	tenants        *tenant.Registry
	maxStreamBytes int64
	ttl            time.Duration

	mu      sync.Mutex
	streams map[string]*streamState // keyed by read Name
}

type streamState struct {
	instance   string
	name       string
	writeToken string

	mu        sync.Mutex
	buf       []byte
	finished  bool
	updatedAt time.Time
	notify    chan struct{}
}

// New returns a LogStream server authorized by tenants.
func New(tenants *tenant.Registry) *Server {
	return &Server{
		tenants:        tenants,
		maxStreamBytes: defaultMaxStreamBytes,
		ttl:            defaultTTL,
		streams:        map[string]*streamState{},
	}
}

// IsResource reports whether a ByteStream resource name addresses a logstream.
func IsResource(name string) bool {
	return strings.HasPrefix(name, "logstreams/") || strings.Contains(name, "/logstreams/")
}

// CreateLogStream allocates a new tenant-scoped log stream with separate read
// and write resource names.
func (s *Server) CreateLogStream(ctx context.Context, req *logstreampb.CreateLogStreamRequest) (*logstreampb.LogStream, error) {
	parent := strings.TrimSuffix(req.GetParent(), "/")
	if err := s.tenants.Authorize(ctx, parent); err != nil {
		return nil, err
	}
	id := uuid.NewString()
	writeToken := uuid.NewString()
	name := fmt.Sprintf("logstreams/%s", id)
	if parent != "" {
		name = fmt.Sprintf("%s/logstreams/%s", parent, id)
	}
	writeName := name + "/" + writeToken

	st := &streamState{
		instance:   parent,
		name:       name,
		writeToken: writeToken,
		updatedAt:  time.Now(),
		notify:     make(chan struct{}),
	}
	s.mu.Lock()
	s.gcLocked(time.Now())
	s.streams[name] = st
	s.mu.Unlock()

	return &logstreampb.LogStream{
		Name:              name,
		WriteResourceName: writeName,
	}, nil
}

func (s *Server) gcLocked(now time.Time) {
	for name, st := range s.streams {
		st.mu.Lock()
		expired := st.finished && now.Sub(st.updatedAt) > s.ttl
		st.mu.Unlock()
		if expired {
			delete(s.streams, name)
		}
	}
}

// parseResource splits a logstream ByteStream resource into its parent
// instance, read name, and optional write token.
func parseResource(resource string) (instance, readName, writeToken string, err error) {
	parts := strings.Split(resource, "/")
	for i := 0; i < len(parts); i++ {
		if parts[i] != "logstreams" {
			continue
		}
		rest := parts[i+1:]
		if len(rest) == 1 && rest[0] != "" {
			instance = strings.Join(parts[:i], "/")
			return instance, resource, "", nil
		}
		if len(rest) == 2 && rest[0] != "" && rest[1] != "" {
			instance = strings.Join(parts[:i], "/")
			readName = strings.Join(parts[:i+2], "/")
			return instance, readName, rest[1], nil
		}
		return "", "", "", fmt.Errorf("invalid logstream resource %q", resource)
	}
	return "", "", "", fmt.Errorf("invalid logstream resource %q", resource)
}

// Read serves a logstream over ByteStream, blocking for live data until the
// writer sends finish_write or ctx cancels. Reading a write_resource_name is
// rejected per the Remote Logstream specification.
func (s *Server) Read(req *bytestream.ReadRequest, stream bytestream.ByteStream_ReadServer) error {
	instance, readName, writeToken, err := parseResource(req.GetResourceName())
	if err != nil {
		return status.Error(codes.InvalidArgument, err.Error())
	}
	if writeToken != "" {
		return status.Error(codes.InvalidArgument, "cannot read from a logstream write_resource_name")
	}
	if err := s.tenants.Authorize(stream.Context(), instance); err != nil {
		return err
	}
	s.mu.Lock()
	st, ok := s.streams[readName]
	s.mu.Unlock()
	if !ok {
		return status.Error(codes.NotFound, "logstream not found")
	}
	offset := req.GetReadOffset()
	limit := req.GetReadLimit()
	if offset < 0 || limit < 0 {
		return status.Error(codes.InvalidArgument, "negative read offset or limit")
	}
	var sent int64
	for {
		st.mu.Lock()
		n := int64(len(st.buf))
		finished := st.finished
		ch := st.notify
		var chunk []byte
		if offset < n {
			end := n
			if limit > 0 && offset+(limit-sent) < end {
				end = offset + (limit - sent)
			}
			chunk = append([]byte(nil), st.buf[offset:end]...)
		}
		st.mu.Unlock()

		if len(chunk) > 0 {
			if err := stream.Send(&bytestream.ReadResponse{Data: chunk}); err != nil {
				return err
			}
			offset += int64(len(chunk))
			sent += int64(len(chunk))
			if limit > 0 && sent >= limit {
				return nil
			}
			continue
		}
		if finished {
			if offset > n {
				return status.Errorf(codes.OutOfRange, "read offset %d exceeds stream length %d", offset, n)
			}
			return nil
		}
		select {
		case <-stream.Context().Done():
			return status.FromContextError(stream.Context().Err()).Err()
		case <-ch:
		}
	}
}

// Write appends chunks to a logstream addressed by its write_resource_name.
func (s *Server) Write(stream bytestream.ByteStream_WriteServer) error {
	var (
		st       *streamState
		finished bool
	)
	for !finished {
		req, err := stream.Recv()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
		if st == nil {
			instance, readName, writeToken, err := parseResource(req.GetResourceName())
			if err != nil {
				return status.Error(codes.InvalidArgument, err.Error())
			}
			if writeToken == "" {
				return status.Error(codes.InvalidArgument, "logstream write requires write_resource_name")
			}
			if err := s.tenants.Authorize(stream.Context(), instance); err != nil {
				return err
			}
			s.mu.Lock()
			found, ok := s.streams[readName]
			s.mu.Unlock()
			if !ok {
				return status.Error(codes.NotFound, "logstream not found")
			}
			if subtle.ConstantTimeCompare([]byte(found.writeToken), []byte(writeToken)) != 1 {
				return status.Error(codes.PermissionDenied, "invalid logstream write token")
			}
			st = found
		}

		st.mu.Lock()
		if st.finished {
			st.mu.Unlock()
			return status.Error(codes.FailedPrecondition, "logstream already finalized")
		}
		if req.GetWriteOffset() != int64(len(st.buf)) {
			want := len(st.buf)
			st.mu.Unlock()
			return status.Errorf(codes.InvalidArgument, "write offset %d, want %d", req.GetWriteOffset(), want)
		}
		if int64(len(st.buf)+len(req.GetData())) > s.maxStreamBytes {
			st.mu.Unlock()
			return status.Errorf(codes.ResourceExhausted, "logstream exceeds %d bytes", s.maxStreamBytes)
		}
		st.buf = append(st.buf, req.GetData()...)
		st.updatedAt = time.Now()
		if req.GetFinishWrite() {
			st.finished = true
			finished = true
		}
		close(st.notify)
		st.notify = make(chan struct{})
		st.mu.Unlock()
	}
	if st == nil {
		return status.Error(codes.InvalidArgument, "empty write stream")
	}
	st.mu.Lock()
	committed := int64(len(st.buf))
	st.mu.Unlock()
	return stream.SendAndClose(&bytestream.WriteResponse{CommittedSize: committed})
}

// QueryWriteStatus reports the current committed byte count of a logstream.
func (s *Server) QueryWriteStatus(ctx context.Context, req *bytestream.QueryWriteStatusRequest) (*bytestream.QueryWriteStatusResponse, error) {
	instance, readName, writeToken, err := parseResource(req.GetResourceName())
	if err != nil {
		return nil, status.Error(codes.InvalidArgument, err.Error())
	}
	if writeToken == "" {
		return nil, status.Error(codes.InvalidArgument, "logstream query requires write_resource_name")
	}
	if err := s.tenants.Authorize(ctx, instance); err != nil {
		return nil, err
	}
	s.mu.Lock()
	st, ok := s.streams[readName]
	s.mu.Unlock()
	if !ok {
		return nil, status.Error(codes.NotFound, "logstream not found")
	}
	if subtle.ConstantTimeCompare([]byte(st.writeToken), []byte(writeToken)) != 1 {
		return nil, status.Error(codes.PermissionDenied, "invalid logstream write token")
	}
	st.mu.Lock()
	resp := &bytestream.QueryWriteStatusResponse{
		CommittedSize: int64(len(st.buf)),
		Complete:      st.finished,
	}
	st.mu.Unlock()
	return resp, nil
}
