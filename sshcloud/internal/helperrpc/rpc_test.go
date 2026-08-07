package helperrpc

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"net"
	"os"
	"path/filepath"
	"strings"
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

func TestStrictJSONCodecRejectsInvalidMessages(t *testing.T) {
	t.Parallel()
	for name, message := range map[string][]byte{
		"unknown field":  []byte(`{"operation":"ready","unexpected":true}`),
		"trailing value": []byte(`{"operation":"ready"} {}`),
		"truncated":      []byte(`{"operation":"ready"`),
		"overflow":       bytes.Repeat([]byte(" "), maxMessageBytes+1),
	} {
		t.Run(name, func(t *testing.T) {
			var request Request
			if err := Decode(bytes.NewReader(message), &request); err == nil {
				t.Fatalf("Decode accepted %d-byte message", len(message))
			}
		})
	}
}

func TestDecodePayloadUsesStrictCodec(t *testing.T) {
	t.Parallel()
	type payload struct {
		VMID string `json:"vm_id"`
	}
	for name, raw := range map[string]string{
		"unknown field":  `{"vm_id":"0123abcdef89","owner":0}`,
		"trailing value": `{"vm_id":"0123abcdef89"} {}`,
	} {
		t.Run(name, func(t *testing.T) {
			var out payload
			if err := DecodePayload(json.RawMessage(raw), &out); err == nil {
				t.Fatalf("DecodePayload accepted %s", raw)
			}
		})
	}
}

func TestEncodeRejectsOversizedMessage(t *testing.T) {
	t.Parallel()
	var dst bytes.Buffer
	err := Encode(&dst, map[string]string{"value": strings.Repeat("x", maxMessageBytes)})
	if err == nil || dst.Len() != 0 {
		t.Fatalf("Encode error = %v, wrote %d bytes", err, dst.Len())
	}
}
