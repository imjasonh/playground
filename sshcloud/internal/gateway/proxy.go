package gateway

import (
	"context"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"net"
	"time"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/userca"
)

// DialRequest is a backend wake/dial for one app generation.
type DialRequest struct {
	User      string
	App       string
	Gen       string
	Image     string
	Tier      string
	NoIdle    bool
	RetryFor  time.Duration
	Purpose   string
	RequestID string
}

// DialTarget binds a backend address to its expected SSH host identity.
type DialTarget struct {
	Addr             string
	SSHHostPublicKey string
}

// DialFunc resolves a running app instance and its host identity.
type DialFunc func(ctx context.Context, req DialRequest) (DialTarget, error)

// ProxySSHStreams forwards one exact outer session contract to an app.
func ProxySSHStreams(ctx context.Context, input io.Reader, output, stderr io.Writer, ca *userca.CA, principal string, target DialTarget, spec *SessionSpec, ready chan<- error) (exit AppExit, retErr error) {
	started := false
	defer func() {
		if !started && ready != nil {
			select {
			case ready <- retErr:
			default:
			}
		}
	}()
	if ctx == nil {
		ctx = context.Background()
	}
	cert, err := ca.Mint(principal, 5*time.Minute)
	if err != nil {
		return AppExit{}, fmt.Errorf("mint cert: %w", err)
	}
	expectedHostKey, _, _, _, err := ssh.ParseAuthorizedKey([]byte(target.SSHHostPublicKey))
	if err != nil {
		return AppExit{}, fmt.Errorf("parse expected app host key: %w", err)
	}
	if expectedHostKey.Type() != ssh.KeyAlgoED25519 {
		return AppExit{}, fmt.Errorf("app host key must be Ed25519, got %s", expectedHostKey.Type())
	}
	cfg := &ssh.ClientConfig{
		User:              principal,
		Auth:              []ssh.AuthMethod{ssh.PublicKeys(cert.Signer)},
		HostKeyCallback:   ssh.FixedHostKey(expectedHostKey),
		HostKeyAlgorithms: []string{ssh.KeyAlgoED25519},
		Timeout:           10 * time.Second,
	}
	raw, err := (&net.Dialer{Timeout: 10 * time.Second}).DialContext(ctx, "tcp", target.Addr)
	if err != nil {
		return AppExit{}, fmt.Errorf("dial app: %w", err)
	}
	_ = raw.SetDeadline(time.Now().Add(10 * time.Second))
	handshakeDone := make(chan struct{})
	go func() {
		select {
		case <-ctx.Done():
			_ = raw.Close()
		case <-handshakeDone:
		}
	}()
	sshConn, chans, reqs, err := ssh.NewClientConn(raw, target.Addr, cfg)
	close(handshakeDone)
	if err != nil {
		_ = raw.Close()
		return AppExit{}, fmt.Errorf("handshake app: %w", err)
	}
	_ = raw.SetDeadline(time.Time{})
	conn := ssh.NewClient(sshConn, chans, reqs)
	defer conn.Close()

	backend, backendReqs, err := conn.OpenChannel("session", nil)
	if err != nil {
		return AppExit{}, err
	}
	defer backend.Close()
	for _, setup := range spec.SetupRequests() {
		ok, err := backend.SendRequest(setup.Type, true, setup.Payload)
		if err != nil || !ok {
			spec.ReplyStart(false)
			return AppExit{}, fmt.Errorf("backend rejected %s: %w", setup.Type, err)
		}
	}
	ok, err := backend.SendRequest(spec.StartType, true, spec.StartPayload)
	if err != nil || !ok {
		spec.ReplyStart(false)
		return AppExit{}, fmt.Errorf("backend rejected %s: %w", spec.StartType, err)
	}
	spec.ReplyStart(true)
	started = true
	if ready != nil {
		select {
		case ready <- nil:
		default:
		}
	}

	inputDone := make(chan struct{})
	go func() {
		defer close(inputDone)
		if buffered, ok := input.(*migrationAttachment); ok {
			_ = buffered.pumpTo(backend)
		} else {
			_, _ = io.Copy(backend, input)
		}
		_ = backend.CloseWrite()
	}()
	stopBufferedInput := func() {
		if buffered, ok := input.(*migrationAttachment); ok {
			_ = buffered.Close()
			<-inputDone
		}
	}

	stdoutDone := make(chan struct{})
	go func() {
		_, _ = io.Copy(output, backend)
		close(stdoutDone)
	}()
	stderrDone := make(chan struct{})
	go func() {
		_, _ = io.Copy(stderr, backend.Stderr())
		close(stderrDone)
	}()
	requestsDone := make(chan AppExit, 1)
	go func() {
		exit := AppExit{Code: 255}
		for req := range backendReqs {
			switch req.Type {
			case "exit-status":
				if len(req.Payload) == 4 {
					exit = AppExit{
						RequestType: req.Type, Payload: append([]byte(nil), req.Payload...),
						Code: int(binary.BigEndian.Uint32(req.Payload)),
					}
				}
			case "exit-signal":
				exit = AppExit{RequestType: req.Type, Payload: append([]byte(nil), req.Payload...), Code: 255}
			default:
				if req.WantReply {
					_ = req.Reply(false, nil)
				}
			}
		}
		requestsDone <- exit
	}()
	go func() {
		for {
			select {
			case <-ctx.Done():
				return
			case change, ok := <-spec.Changes:
				if !ok {
					return
				}
				_, _ = backend.SendRequest(change.Type, false, change.Payload)
			}
		}
	}()
	select {
	case <-ctx.Done():
		if !errors.Is(context.Cause(ctx), errBackendMigration) {
			_, _ = io.WriteString(output, "\r\n[sshcloud] session ended (deploy cutover)\r\n")
		}
		_ = conn.Close()
		stopBufferedInput()
		return AppExit{}, context.Cause(ctx)
	case exit := <-requestsDone:
		_ = backend.Close()
		stopBufferedInput()
		<-stdoutDone
		<-stderrDone
		return exit, nil
	}
}
