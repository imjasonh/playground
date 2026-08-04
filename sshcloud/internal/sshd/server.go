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

func (s *Server) handleSession(ctx context.Context, sc *ssh.ServerConn, ch ssh.Channel, reqs <-chan *ssh.Request, fp string) {
	defer ch.Close()

	type startInfo struct {
		execCmd string
		kind    string
	}
	start := make(chan startInfo, 1)
	reqDone := make(chan struct{})
	go func() {
		defer close(reqDone)
		for req := range reqs {
			switch req.Type {
			case "pty-req", "env", "window-change":
				if req.WantReply {
					_ = req.Reply(true, nil)
				}
			case "shell":
				if req.WantReply {
					_ = req.Reply(true, nil)
				}
				select {
				case start <- startInfo{kind: "shell"}:
				default:
				}
			case "exec":
				var msg execMsg
				if err := ssh.Unmarshal(req.Payload, &msg); err != nil {
					if req.WantReply {
						_ = req.Reply(false, nil)
					}
					continue
				}
				if req.WantReply {
					_ = req.Reply(true, nil)
				}
				select {
				case start <- startInfo{execCmd: msg.Command, kind: "exec"}:
				default:
				}
			default:
				if req.WantReply {
					_ = req.Reply(false, nil)
				}
			}
		}
	}()

	select {
	case <-ctx.Done():
		return
	case <-reqDone:
		return
	case info := <-start:
		s.runSession(ctx, sc, ch, fp, info.kind, info.execCmd)
	}
}

func (s *Server) runSession(ctx context.Context, sc *ssh.ServerConn, ch ssh.Channel, fp, startKind, execCmd string) {
	s.logf("session start user=%q fp=%q request=%s", sc.User(), fp, startKind)
	res, err := s.Hub.HandleConnect(ctx, gateway.Connect{
		SSHUser:        sc.User(),
		KeyFingerprint: fp,
	})
	if err != nil {
		fmt.Fprintf(ch, "error: %v\r\n", err)
		sendExit(ch, 1)
		return
	}
	defer s.Hub.ReleaseSession(res.Session)
	if res.Action == gateway.ActionJoin && res.User == "" && startKind == "exec" && sc.User() != "join" {
		fmt.Fprint(ch, "Unknown keys may run non-interactive onboarding only as join@host.\r\n")
		sendExit(ch, 2)
		return
	}
	if res.Action == gateway.ActionProxyApp && startKind == "exec" {
		fmt.Fprint(ch, "App exec forwarding is not implemented yet; open an interactive shell session instead.\r\n")
		sendExit(ch, 2)
		return
	}
	if res.Action == gateway.ActionMenu && startKind == "exec" {
		fmt.Fprint(ch, "That SSH username is not a deployed app, and menu@host accepts interactive sessions only.\r\n")
		sendExit(ch, 2)
		return
	}

	sessCtx := ctx
	if res.Session != "" {
		var cancel context.CancelFunc
		sessCtx, cancel = s.Hub.BindSession(ctx, res.Session)
		defer cancel()
	}

	code := 0
	switch res.Action {
	case gateway.ActionJoin:
		code = gateway.RunJoin(ctx, ch, s.Hub, fp, res.User, execCmd)
	case gateway.ActionMenu:
		gateway.RunMenu(ctx, ch, s.Hub, fp, res.User)
	case gateway.ActionDeploy:
		code = gateway.RunDeploy(ctx, ch, s.Hub, res.User, execCmd)
	case gateway.ActionRejectBusy:
		fmt.Fprintf(ch, "%s\r\n", res.Message)
		code = 1
	case gateway.ActionProxyApp:
		code = gateway.RunAppStub(sessCtx, ch, s.Hub, res)
	default:
		fmt.Fprintf(ch, "unhandled action %v\r\n", res.Action)
		code = 1
	}
	sendExit(ch, code)
}

func sendExit(ch ssh.Channel, code int) {
	var buf [4]byte
	binary.BigEndian.PutUint32(buf[:], uint32(code))
	_, _ = ch.SendRequest("exit-status", false, buf[:])
}
