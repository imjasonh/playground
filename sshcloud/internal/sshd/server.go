// Package sshd runs the public SSH listener and dispatches sessions to the hub.
package sshd

import (
	"context"
	"encoding/binary"
	"fmt"
	"log"
	"net"
	"sync"
	"time"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/gateway"
)

const fingerprintExt = "sshcloud-key-fp"

// Server is a gateway SSH listener.
type Server struct {
	Hub     *gateway.Hub
	HostKey ssh.Signer
	Addr    string // e.g. "127.0.0.1:2222" or "127.0.0.1:0"
	Logger  *log.Logger
	// HandshakeTimeout bounds clients that connect but never finish SSH setup.
	// Zero defaults to 15 seconds.
	HandshakeTimeout time.Duration
	// MaxConnections bounds process-wide accepted TCP connections. Zero
	// defaults to 256.
	MaxConnections int
	listener       net.Listener
	limitOnce      sync.Once
	limit          chan struct{}
}

func (s *Server) logf(format string, args ...any) {
	if s.Logger != nil {
		s.Logger.Printf(format, args...)
	}
}

// Listen starts the TCP listener without accepting (for tests that need the bound addr).
func (s *Server) Listen() error {
	ln, err := net.Listen("tcp", s.Addr)
	if err != nil {
		return err
	}
	s.listener = ln
	s.Addr = ln.Addr().String()
	return nil
}

// Serve accepts connections until ctx is cancelled.
func (s *Server) Serve(ctx context.Context) error {
	if s.listener == nil {
		if err := s.Listen(); err != nil {
			return err
		}
	}
	ln := s.listener
	s.logf("listening on %s", ln.Addr())

	go func() {
		<-ctx.Done()
		_ = ln.Close()
	}()

	for {
		conn, err := ln.Accept()
		if err != nil {
			select {
			case <-ctx.Done():
				return nil
			default:
				return err
			}
		}
		go s.handleConn(ctx, conn)
	}
}

// ListenAndServe binds and serves until ctx is done.
func (s *Server) ListenAndServe(ctx context.Context) error {
	if err := s.Listen(); err != nil {
		return err
	}
	return s.Serve(ctx)
}

// Close stops the listener.
func (s *Server) Close() error {
	if s.listener != nil {
		return s.listener.Close()
	}
	return nil
}

func (s *Server) handleConn(ctx context.Context, nc net.Conn) {
	defer nc.Close()
	s.limitOnce.Do(func() {
		max := s.MaxConnections
		if max <= 0 {
			max = 256
		}
		s.limit = make(chan struct{}, max)
	})
	select {
	case s.limit <- struct{}{}:
		defer func() { <-s.limit }()
	default:
		s.logf("connection rejected: global limit reached")
		return
	}
	handshakeTimeout := s.HandshakeTimeout
	if handshakeTimeout <= 0 {
		handshakeTimeout = 15 * time.Second
	}
	_ = nc.SetDeadline(time.Now().Add(handshakeTimeout))
	cfg := &ssh.ServerConfig{
		PublicKeyCallback: func(conn ssh.ConnMetadata, key ssh.PublicKey) (*ssh.Permissions, error) {
			fp := ssh.FingerprintSHA256(key)
			return &ssh.Permissions{
				Extensions: map[string]string{fingerprintExt: fp},
			}, nil
		},
	}
	cfg.AddHostKey(s.HostKey)

	sc, chans, reqs, err := ssh.NewServerConn(nc, cfg)
	if err != nil {
		s.logf("handshake failed: %v", err)
		return
	}
	_ = nc.SetDeadline(time.Time{})
	defer sc.Close()
	connCtx, cancelConn := context.WithCancel(ctx)
	defer cancelConn()
	go ssh.DiscardRequests(reqs)

	fp := ""
	if sc.Permissions != nil {
		fp = sc.Permissions.Extensions[fingerprintExt]
	}

	for newCh := range chans {
		if newCh.ChannelType() != "session" {
			_ = newCh.Reject(ssh.UnknownChannelType, "only session supported")
			continue
		}
		ch, creqs, err := newCh.Accept()
		if err != nil {
			continue
		}
		go s.handleSession(connCtx, sc, ch, creqs, fp)
	}
}

type execMsg struct {
	Command string
}

type subsystemMsg struct {
	Name string
}

type ptyMsg struct {
	Term                    string
	Columns, Rows           uint32
	PixelWidth, PixelHeight uint32
	Modes                   string
}

type envMsg struct {
	Name, Value string
}

type windowMsg struct {
	Columns, Rows           uint32
	PixelWidth, PixelHeight uint32
}

type signalMsg struct {
	Signal string
}

func (s *Server) handleSession(ctx context.Context, sc *ssh.ServerConn, ch ssh.Channel, reqs <-chan *ssh.Request, fp string) {
	defer ch.Close()

	start := make(chan *gateway.SessionSpec, 1)
	changes := make(chan gateway.ForwardRequest, 32)
	reqDone := make(chan struct{})
	go func() {
		defer close(reqDone)
		defer close(changes)
		var setup []gateway.ForwardRequest
		started := false
		hasPTY := false
		for req := range reqs {
			switch req.Type {
			case "pty-req":
				var msg ptyMsg
				if started || hasPTY || ssh.Unmarshal(req.Payload, &msg) != nil {
					if req.WantReply {
						_ = req.Reply(false, nil)
					}
					continue
				}
				hasPTY = true
				setup = append(setup, gateway.ForwardRequest{Type: req.Type, Payload: append([]byte(nil), req.Payload...)})
				if req.WantReply {
					_ = req.Reply(true, nil)
				}
			case "env":
				var msg envMsg
				if started || ssh.Unmarshal(req.Payload, &msg) != nil {
					if req.WantReply {
						_ = req.Reply(false, nil)
					}
					continue
				}
				setup = append(setup, gateway.ForwardRequest{Type: req.Type, Payload: append([]byte(nil), req.Payload...)})
				if req.WantReply {
					_ = req.Reply(true, nil)
				}
			case "window-change":
				var msg windowMsg
				if ssh.Unmarshal(req.Payload, &msg) != nil {
					if req.WantReply {
						_ = req.Reply(false, nil)
					}
					continue
				}
				forward := gateway.ForwardRequest{Type: req.Type, Payload: append([]byte(nil), req.Payload...)}
				if !started {
					setup = append(setup, forward)
				} else {
					select {
					case changes <- forward:
					case <-ctx.Done():
						return
					}
				}
				if req.WantReply {
					_ = req.Reply(true, nil)
				}
			case "signal":
				var msg signalMsg
				if !started || ssh.Unmarshal(req.Payload, &msg) != nil {
					if req.WantReply {
						_ = req.Reply(false, nil)
					}
					continue
				}
				select {
				case changes <- gateway.ForwardRequest{Type: req.Type, Payload: append([]byte(nil), req.Payload...)}:
				case <-ctx.Done():
					return
				}
				if req.WantReply {
					_ = req.Reply(true, nil)
				}
			case "shell", "exec", "subsystem":
				if started {
					if req.WantReply {
						_ = req.Reply(false, nil)
					}
					continue
				}
				argument := ""
				switch req.Type {
				case "shell":
					if len(req.Payload) != 0 {
						if req.WantReply {
							_ = req.Reply(false, nil)
						}
						continue
					}
				case "exec":
					var msg execMsg
					if err := ssh.Unmarshal(req.Payload, &msg); err != nil {
						if req.WantReply {
							_ = req.Reply(false, nil)
						}
						continue
					}
					argument = msg.Command
				case "subsystem":
					var msg subsystemMsg
					if err := ssh.Unmarshal(req.Payload, &msg); err != nil {
						if req.WantReply {
							_ = req.Reply(false, nil)
						}
						continue
					}
					argument = msg.Name
				}
				started = true
				startReq := req
				spec := gateway.NewSessionSpec(
					req.Type, req.Payload, argument, setup, hasPTY, changes,
					func(ok bool) {
						if startReq.WantReply {
							_ = startReq.Reply(ok, nil)
						}
					},
				)
				select {
				case start <- spec:
				case <-ctx.Done():
					spec.ReplyStart(false)
					return
				}
			default:
				if req.WantReply {
					_ = req.Reply(false, nil)
				}
			}
		}
	}()

	var spec *gateway.SessionSpec
	select {
	case <-ctx.Done():
		return
	case spec = <-start:
	case <-reqDone:
		select {
		case spec = <-start:
		default:
			return
		}
	}
	s.runSession(ctx, sc, ch, fp, gateway.ClientSession{IO: ch, Stderr: ch.Stderr(), Spec: spec})
}

func (s *Server) runSession(ctx context.Context, sc *ssh.ServerConn, ch ssh.Channel, fp string, client gateway.ClientSession) {
	spec := client.Spec
	startKind, execCmd := spec.StartType, spec.Argument
	s.logf("session start user=%q fp=%q request=%s", sc.User(), fp, startKind)
	res, err := s.Hub.HandleConnect(ctx, gateway.Connect{
		SSHUser:        sc.User(),
		KeyFingerprint: fp,
	})
	if err != nil {
		spec.ReplyStart(false)
		fmt.Fprintf(client.Stderr, "error: %v\r\n", err)
		sendExit(ch, 1)
		return
	}
	defer s.Hub.ReleaseSession(res.Session)
	if res.Action == gateway.ActionJoin && res.User == "" && startKind == gateway.SessionExec && sc.User() != "join" {
		spec.ReplyStart(false)
		fmt.Fprint(client.Stderr, "Unknown keys may run non-interactive onboarding only as join@host.\r\n")
		sendExit(ch, 2)
		return
	}
	if res.Action == gateway.ActionMenu && startKind != gateway.SessionShell {
		spec.ReplyStart(false)
		fmt.Fprint(client.Stderr, "That SSH username is not a deployed app, and menu@host accepts interactive shells only.\r\n")
		sendExit(ch, 2)
		return
	}
	if (res.Action == gateway.ActionJoin || res.Action == gateway.ActionDeploy) && startKind == gateway.SessionSubsystem {
		spec.ReplyStart(false)
		fmt.Fprint(client.Stderr, "Platform commands do not support SSH subsystems.\r\n")
		sendExit(ch, 2)
		return
	}

	sessCtx := ctx
	if res.Session != "" {
		var cancel context.CancelFunc
		sessCtx, cancel = s.Hub.BindSession(ctx, res.Session)
		defer cancel()
	}

	exit := gateway.AppExit{Code: 0}
	switch res.Action {
	case gateway.ActionJoin:
		spec.ReplyStart(true)
		exit.Code = gateway.RunJoinSession(ctx, client, s.Hub, fp, res.User, execCmd)
	case gateway.ActionMenu:
		spec.ReplyStart(true)
		gateway.RunMenuSession(ctx, client, s.Hub, fp, res.User)
	case gateway.ActionDeploy:
		spec.ReplyStart(true)
		exit.Code = gateway.RunDeploySession(ctx, client, s.Hub, res.User, execCmd)
	case gateway.ActionRejectBusy:
		spec.ReplyStart(true)
		fmt.Fprintf(ch, "%s\r\n", res.Message)
		exit.Code = 1
	case gateway.ActionProxyApp:
		exit = gateway.RunAppSession(sessCtx, client, s.Hub, res)
	default:
		spec.ReplyStart(false)
		fmt.Fprintf(client.Stderr, "unhandled action %v\r\n", res.Action)
		exit.Code = 1
	}
	sendAppExit(ch, exit)
}

func sendAppExit(ch ssh.Channel, exit gateway.AppExit) {
	if exit.RequestType != "" && len(exit.Payload) > 0 {
		_, _ = ch.SendRequest(exit.RequestType, false, exit.Payload)
		return
	}
	sendExit(ch, exit.Code)
}

func sendExit(ch ssh.Channel, code int) {
	var buf [4]byte
	binary.BigEndian.PutUint32(buf[:], uint32(code))
	_, _ = ch.SendRequest("exit-status", false, buf[:])
}
