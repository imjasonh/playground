// Package sshd runs the public SSH listener and dispatches sessions to the hub.
package sshd

import (
	"context"
	"fmt"
	"log"
	"net"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/gateway"
)

const fingerprintExt = "sshcloud-key-fp"

// Server is a gateway SSH listener.
type Server struct {
	Hub      *gateway.Hub
	HostKey  ssh.Signer
	Addr     string // e.g. "127.0.0.1:2222" or "127.0.0.1:0"
	Logger   *log.Logger
	listener net.Listener
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
	defer sc.Close()
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
		go s.handleSession(ctx, sc, ch, creqs, fp)
	}
}

func (s *Server) handleSession(ctx context.Context, sc *ssh.ServerConn, ch ssh.Channel, reqs <-chan *ssh.Request, fp string) {
	defer ch.Close()

	start := make(chan struct{}, 1)
	go func() {
		for req := range reqs {
			switch req.Type {
			case "pty-req", "env", "window-change":
				if req.WantReply {
					_ = req.Reply(true, nil)
				}
			case "shell", "exec":
				if req.WantReply {
					_ = req.Reply(true, nil)
				}
				select {
				case start <- struct{}{}:
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
	case <-start:
	}

	s.logf("session start user=%q fp=%q", sc.User(), fp)
	res, err := s.Hub.HandleConnect(ctx, gateway.Connect{
		SSHUser:        sc.User(),
		KeyFingerprint: fp,
	})
	if err != nil {
		fmt.Fprintf(ch, "error: %v\r\n", err)
		return
	}
	defer s.Hub.ReleaseSession(res.Session)

	switch res.Action {
	case gateway.ActionJoin:
		gateway.RunJoin(ctx, ch, s.Hub, fp, res.User)
	case gateway.ActionMenu:
		gateway.RunMenu(ctx, ch, s.Hub, fp, res.User)
	case gateway.ActionDeploy:
		fmt.Fprintf(ch, "deploy: not implemented yet\r\n")
	case gateway.ActionRejectBusy:
		fmt.Fprintf(ch, "%s\r\n", res.Message)
	case gateway.ActionProxyApp:
		gateway.RunAppStub(ctx, ch, s.Hub, res)
	default:
		fmt.Fprintf(ch, "unhandled action %v\r\n", res.Action)
	}
}
