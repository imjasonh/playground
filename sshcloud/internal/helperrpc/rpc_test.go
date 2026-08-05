package helperrpc

import (
	"context"
	"encoding/json"
	"errors"
	"net"
	"os"
	"path/filepath"
	"testing"
)

func TestPeerCredentialsAndUIDAuthorization(t *testing.T) {
	t.Parallel()
	socket := filepath.Join(t.TempDir(), "peer.sock")
	listener, err := net.Listen("unix", socket)
	if err != nil {
		t.Fatal(err)
	}
	defer listener.Close()

	result := make(chan error, 1)
	go func() {
		conn, err := listener.Accept()
		if err != nil {
			result <- err
			return
		}
		defer conn.Close()
		cred, err := AuthorizePeer(conn, uint32(os.Getuid()))
		if err == nil && cred.Pid <= 0 {
			err = errors.New("peer pid was not populated")
		}
		result <- err
	}()

	conn, err := net.Dial("unix", socket)
	if err != nil {
		t.Fatal(err)
	}
	_ = conn.Close()
	if err := <-result; err != nil {
		t.Fatal(err)
	}
}

func TestPeerCredentialsRejectWrongUID(t *testing.T) {
	t.Parallel()
	socket := filepath.Join(t.TempDir(), "peer.sock")
	listener, err := net.Listen("unix", socket)
	if err != nil {
		t.Fatal(err)
	}
	defer listener.Close()

	result := make(chan error, 1)
	go func() {
		conn, err := listener.Accept()
		if err != nil {
			result <- err
			return
		}
		defer conn.Close()
		_, err = AuthorizePeer(conn, uint32(os.Getuid())+1)
		result <- err
	}()
	conn, err := net.Dial("unix", socket)
	if err != nil {
		t.Fatal(err)
	}
	_ = conn.Close()
	if err := <-result; err == nil {
		t.Fatal("wrong peer UID was accepted")
	}
}

func TestCallPreservesHelperFailure(t *testing.T) {
	t.Parallel()
	socket := filepath.Join(t.TempDir(), "helper.sock")
	listener, err := net.Listen("unix", socket)
	if err != nil {
		t.Fatal(err)
	}
	defer listener.Close()
	go func() {
		_ = Serve(listener, uint32(os.Getuid()), func(context.Context, string, json.RawMessage) (any, error) {
			return nil, errors.New("injected launch failure")
		})
	}()

	err = Call(context.Background(), socket, "launch", struct{}{}, nil)
	var remote *RemoteError
	if !errors.As(err, &remote) || remote.Operation != "launch" ||
		remote.Message != "injected launch failure" {
		t.Fatalf("Call error = %T %v", err, err)
	}
}
