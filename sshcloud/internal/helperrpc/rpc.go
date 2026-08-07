// Package helperrpc implements the small authenticated Unix-socket protocol
// used by sshcloud's host-isolation helpers.
package helperrpc

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"os"
	"path/filepath"
	"strconv"
	"time"

	"golang.org/x/sys/unix"
)

const (
	maxMessageBytes  = 64 << 10
	requestTimeout   = 30 * time.Second
	operationTimeout = 5 * time.Minute
)

// Request is one operation and its operation-specific JSON payload.
type Request struct {
	Operation string          `json:"operation"`
	Payload   json.RawMessage `json:"payload,omitempty"`
}

// Response is one operation result.
type Response struct {
	OK      bool            `json:"ok"`
	Error   string          `json:"error,omitempty"`
	Payload json.RawMessage `json:"payload,omitempty"`
}

// RemoteError is a fail-closed error returned by a helper.
type RemoteError struct {
	Operation string
	Message   string
}

func (e *RemoteError) Error() string {
	return fmt.Sprintf("%s helper request failed: %s", e.Operation, e.Message)
}

// Handler processes one authenticated request.
type Handler func(ctx context.Context, operation string, payload json.RawMessage) (any, error)

// PeerCredentials returns Linux SO_PEERCRED credentials for a Unix stream.
func PeerCredentials(conn net.Conn) (*unix.Ucred, error) {
	unixConn, ok := conn.(*net.UnixConn)
	if !ok {
		return nil, fmt.Errorf("peer is not a Unix connection")
	}
	raw, err := unixConn.SyscallConn()
	if err != nil {
		return nil, fmt.Errorf("Unix connection syscall access: %w", err)
	}
	var (
		cred    *unix.Ucred
		sockErr error
	)
	if err := raw.Control(func(fd uintptr) {
		cred, sockErr = unix.GetsockoptUcred(int(fd), unix.SOL_SOCKET, unix.SO_PEERCRED)
	}); err != nil {
		return nil, fmt.Errorf("inspect peer credentials: %w", err)
	}
	if sockErr != nil {
		return nil, fmt.Errorf("inspect peer credentials: %w", sockErr)
	}
	if cred == nil {
		return nil, fmt.Errorf("peer credentials unavailable")
	}
	return cred, nil
}

// AuthorizePeer requires the connecting process to have the configured agent
// UID. Filesystem mode is defense in depth; this check is authoritative.
func AuthorizePeer(conn net.Conn, expectedUID uint32) (*unix.Ucred, error) {
	cred, err := PeerCredentials(conn)
	if err != nil {
		return nil, err
	}
	if cred.Uid != expectedUID {
		return nil, fmt.Errorf("unauthorized peer uid %d (want %d)", cred.Uid, expectedUID)
	}
	return cred, nil
}

// Serve accepts authenticated one-request connections until the listener is
// closed. Every accepted connection is independently authenticated.
func Serve(listener net.Listener, expectedUID uint32, handler Handler) error {
	for {
		conn, err := listener.Accept()
		if err != nil {
			if errors.Is(err, net.ErrClosed) {
				return nil
			}
			return err
		}
		go serveConn(conn, expectedUID, handler)
	}
}

func serveConn(conn net.Conn, expectedUID uint32, handler Handler) {
	defer conn.Close()
	_ = conn.SetDeadline(time.Now().Add(requestTimeout))
	if _, err := AuthorizePeer(conn, expectedUID); err != nil {
		_ = writeResponse(conn, Response{Error: err.Error()})
		return
	}

	var req Request
	if err := Decode(conn, &req); err != nil {
		_ = writeResponse(conn, Response{Error: fmt.Sprintf("decode request: %v", err)})
		return
	}
	if req.Operation == "" {
		_ = writeResponse(conn, Response{Error: "operation required"})
		return
	}
	_ = conn.SetDeadline(time.Now().Add(operationTimeout))
	handlerCtx, cancel := context.WithTimeout(context.Background(), operationTimeout)
	defer cancel()
	result, err := handler(handlerCtx, req.Operation, req.Payload)
	if err != nil {
		_ = writeResponse(conn, Response{Error: err.Error()})
		return
	}
	var payload json.RawMessage
	if result != nil {
		payload, err = json.Marshal(result)
		if err != nil {
			_ = writeResponse(conn, Response{Error: fmt.Sprintf("encode response: %v", err)})
			return
		}
	}
	_ = writeResponse(conn, Response{OK: true, Payload: payload})
}

func writeResponse(w io.Writer, response Response) error {
	if err := Encode(w, response); err != nil {
		return err
	}
	return closeWrite(w)
}

// Encode writes one size-bounded JSON value. The peer must close its write
// side after the value so Decode can prove there is no trailing data.
func Encode(w io.Writer, value any) error {
	data, err := json.Marshal(value)
	if err != nil {
		return fmt.Errorf("encode JSON: %w", err)
	}
	if len(data)+1 > maxMessageBytes {
		return fmt.Errorf("encode JSON: message exceeds %d bytes", maxMessageBytes)
	}
	data = append(data, '\n')
	for len(data) > 0 {
		n, writeErr := w.Write(data)
		if writeErr != nil {
			return fmt.Errorf("encode JSON: %w", writeErr)
		}
		if n == 0 {
			return fmt.Errorf("encode JSON: %w", io.ErrShortWrite)
		}
		data = data[n:]
	}
	return nil
}

// Decode reads exactly one size-bounded JSON value, rejects unknown fields,
// and requires EOF after optional JSON whitespace.
func Decode(r io.Reader, dst any) error {
	data, err := io.ReadAll(io.LimitReader(r, maxMessageBytes+1))
	if err != nil {
		return fmt.Errorf("read JSON: %w", err)
	}
	if len(data) > maxMessageBytes {
		return fmt.Errorf("read JSON: message exceeds %d bytes", maxMessageBytes)
	}
	decoder := json.NewDecoder(bytes.NewReader(data))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(dst); err != nil {
		return fmt.Errorf("decode JSON: %w", err)
	}
	if err := decoder.Decode(&struct{}{}); err != io.EOF {
		if err == nil {
			return fmt.Errorf("decode JSON: trailing value")
		}
		return fmt.Errorf("decode JSON: trailing data: %w", err)
	}
	return nil
}

// DecodePayload applies the same strict codec to an operation payload.
func DecodePayload(payload json.RawMessage, dst any) error {
	if err := Decode(bytes.NewReader(payload), dst); err != nil {
		return fmt.Errorf("decode payload: %w", err)
	}
	return nil
}

func closeWrite(w io.Writer) error {
	type closeWriter interface {
		CloseWrite() error
	}
	if closer, ok := w.(closeWriter); ok {
		return closer.CloseWrite()
	}
	return nil
}

// Call performs one request over a new authenticated-by-the-server connection.
func Call(ctx context.Context, socketPath, operation string, request, response any) error {
	payload, err := json.Marshal(request)
	if err != nil {
		return err
	}
	var dialer net.Dialer
	conn, err := dialer.DialContext(ctx, "unix", socketPath)
	if err != nil {
		return fmt.Errorf("dial %s helper: %w", operation, err)
	}
	defer conn.Close()
	if deadline, ok := ctx.Deadline(); ok {
		_ = conn.SetDeadline(deadline)
	} else {
		_ = conn.SetDeadline(time.Now().Add(operationTimeout))
	}
	if err := Encode(conn, Request{Operation: operation, Payload: payload}); err != nil {
		return fmt.Errorf("send %s helper request: %w", operation, err)
	}
	if err := closeWrite(conn); err != nil {
		return fmt.Errorf("finish %s helper request: %w", operation, err)
	}
	var result Response
	if err := Decode(conn, &result); err != nil {
		return fmt.Errorf("decode %s helper response: %w", operation, err)
	}
	if !result.OK {
		if result.Error == "" {
			result.Error = "unspecified error"
		}
		return &RemoteError{Operation: operation, Message: result.Error}
	}
	if response == nil || len(result.Payload) == 0 {
		return nil
	}
	if err := DecodePayload(result.Payload, response); err != nil {
		return fmt.Errorf("decode %s helper payload: %w", operation, err)
	}
	return nil
}

// ListenPath creates a private Unix socket for non-systemd local operation.
func ListenPath(path string, ownerUID, ownerGID int) (net.Listener, error) {
	if path == "" {
		return nil, fmt.Errorf("socket path required")
	}
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return nil, err
	}
	_ = os.Remove(path)
	listener, err := net.Listen("unix", path)
	if err != nil {
		return nil, err
	}
	cleanup := func(cause error) (net.Listener, error) {
		_ = listener.Close()
		_ = os.Remove(path)
		return nil, cause
	}
	if err := os.Chmod(path, 0o600); err != nil {
		return cleanup(err)
	}
	if ownerUID >= 0 || ownerGID >= 0 {
		if err := os.Chown(path, ownerUID, ownerGID); err != nil {
			return cleanup(err)
		}
	}
	return listener, nil
}

// ActivatedListener returns the single stream listener passed by systemd.
func ActivatedListener() (net.Listener, error) {
	pid, err := strconv.Atoi(os.Getenv("LISTEN_PID"))
	if err != nil || pid != os.Getpid() {
		return nil, fmt.Errorf("invalid LISTEN_PID")
	}
	if os.Getenv("LISTEN_FDS") != "1" {
		return nil, fmt.Errorf("expected exactly one systemd socket")
	}
	file := os.NewFile(uintptr(3), "systemd-listener")
	if file == nil {
		return nil, fmt.Errorf("systemd listener fd unavailable")
	}
	defer file.Close()
	listener, err := net.FileListener(file)
	if err != nil {
		return nil, fmt.Errorf("use systemd listener: %w", err)
	}
	return listener, nil
}
