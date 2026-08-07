// Package sshd runs the public SSH listener and dispatches sessions to the hub.
package sshd

import (
	"context"
	"encoding/binary"
	"fmt"
	"io"
	"log"
	"net"
	"sync"
	"sync/atomic"
	"time"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/observability"
	"github.com/imjasonh/playground/sshcloud/internal/quota"
)

const fingerprintExt = "sshcloud-key-fp"

const (
	maxSessionSetupRequests = 32
	maxSessionSetupBytes    = 16 << 10
)

// Server is a gateway SSH listener.
type Server struct {
	Hub     *gateway.Hub
	HostKey ssh.Signer
	Addr    string // e.g. "127.0.0.1:2222" or "127.0.0.1:0"
	Logger  *log.Logger
	// EventSink is optional and exists for privacy regression tests. Its API is
	// sealed to observability's metadata-only event schemas.
	EventSink *observability.JSONSink
	// HandshakeTimeout bounds clients that connect but never finish SSH setup.
	// Zero defaults to 15 seconds.
	HandshakeTimeout time.Duration
	// MaxConnections bounds process-wide accepted TCP connections. Zero
	// defaults to 256.
	MaxConnections           int
	MaxChannels              int
	MaxChannelsPerConnection int
	StartTimeout             time.Duration
	// AccessRecheckInterval bounds allowlist-revocation latency for open SSH
	// connections. Zero defaults to 30 seconds.
	AccessRecheckInterval time.Duration
	HandshakeLimiter      *quota.IPRateLimiter
	listener              net.Listener
	limitOnce             sync.Once
	limit                 chan struct{}
	channelLimit          chan struct{}
}

func (s *Server) logf(format string, args ...any) {
	if s.Logger != nil {
		s.Logger.Printf(format, args...)
	}
}

func (s *Server) emit(event observability.Event) {
	if s.EventSink != nil {
		_ = s.EventSink.Emit(event)
		return
	}
	observability.Emit(event)
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
		maxChannels := s.MaxChannels
		if maxChannels <= 0 {
			maxChannels = 512
		}
		s.channelLimit = make(chan struct{}, maxChannels)
		if s.HandshakeLimiter == nil {
			s.HandshakeLimiter = quota.NewIPRateLimiter(60, time.Minute)
		}
	})
	if !s.HandshakeLimiter.Allow(nc.RemoteAddr(), time.Now()) {
		s.logf("connection rejected: source handshake rate exceeded")
		return
	}
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
	recheckInterval := s.AccessRecheckInterval
	if recheckInterval <= 0 {
		recheckInterval = 30 * time.Second
	}
	go func() {
		ticker := time.NewTicker(recheckInterval)
		defer ticker.Stop()
		for {
			select {
			case <-connCtx.Done():
				return
			case <-ticker.C:
				if s.Hub != nil && !s.Hub.AllowsKey(fp) {
					s.logf("connection revoked by access policy")
					cancelConn()
					_ = sc.Close()
					return
				}
			}
		}
	}()

	maxPerConnection := s.MaxChannelsPerConnection
	if maxPerConnection <= 0 {
		maxPerConnection = 16
	}
	var activeChannels atomic.Int32
	for newCh := range chans {
		if newCh.ChannelType() != "session" {
			_ = newCh.Reject(ssh.UnknownChannelType, "only session supported")
			continue
		}
		if activeChannels.Load() >= int32(maxPerConnection) {
			_ = newCh.Reject(ssh.ResourceShortage, "too many session channels")
			continue
		}
		select {
		case s.channelLimit <- struct{}{}:
		default:
			_ = newCh.Reject(ssh.ResourceShortage, "gateway session capacity reached")
			continue
		}
		ch, creqs, err := newCh.Accept()
		if err != nil {
			<-s.channelLimit
			continue
		}
		activeChannels.Add(1)
		go func() {
			defer func() {
				activeChannels.Add(-1)
				<-s.channelLimit
			}()
			s.handleSession(connCtx, sc, ch, creqs, fp)
		}()
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
		setupBytes := 0
		started := false
		hasPTY := false
		var currentSpec *gateway.SessionSpec
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
				if len(setup) >= maxSessionSetupRequests || setupBytes+len(req.Payload) > maxSessionSetupBytes {
					if req.WantReply {
						_ = req.Reply(false, nil)
					}
					continue
				}
				hasPTY = true
				setup = append(setup, gateway.ForwardRequest{Type: req.Type, Payload: append([]byte(nil), req.Payload...)})
				setupBytes += len(req.Payload)
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
				if len(setup) >= maxSessionSetupRequests || setupBytes+len(req.Payload) > maxSessionSetupBytes {
					if req.WantReply {
						_ = req.Reply(false, nil)
					}
					continue
				}
				setup = append(setup, gateway.ForwardRequest{Type: req.Type, Payload: append([]byte(nil), req.Payload...)})
				setupBytes += len(req.Payload)
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
					if len(setup) < maxSessionSetupRequests && setupBytes+len(req.Payload) <= maxSessionSetupBytes {
						setup = append(setup, forward)
						setupBytes += len(req.Payload)
					}
				} else {
					if currentSpec != nil {
						_ = currentSpec.RecordDetachedChange(forward)
					}
					select {
					case changes <- forward:
					default:
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
				default:
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
				currentSpec = spec
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
	startTimeout := s.StartTimeout
	if startTimeout <= 0 {
		startTimeout = 15 * time.Second
	}
	timer := time.NewTimer(startTimeout)
	defer timer.Stop()
	select {
	case <-ctx.Done():
		return
	case <-timer.C:
		_, _ = io.WriteString(ch.Stderr(), "session start request timed out\r\n")
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
	startedAt := time.Now()
	res, err := s.Hub.HandleConnect(ctx, gateway.Connect{
		SSHUser:        sc.User(),
		KeyFingerprint: fp,
		SourceIP:       sourceIP(sc.RemoteAddr()),
	})
	if err != nil {
		s.emit(observability.SessionEvent{
			Action: "admit", Mode: startKind, Outcome: observability.OutcomeFailure,
			Duration: time.Since(startedAt),
		})
		spec.ReplyStart(false)
		fmt.Fprintf(client.Stderr, "error: %v\r\n", err)
		sendExit(ch, 1)
		return
	}
	admitOutcome := observability.OutcomeSuccess
	if res.Action == gateway.ActionRejectBusy || res.Action == gateway.ActionForbidden {
		admitOutcome = observability.OutcomeRejected
	}
	identity := observability.RuntimeIdentity{
		User: res.User, App: res.App, Generation: res.Gen,
	}
	route := observability.SessionRoute(res.Action.String())
	s.emit(observability.SessionEvent{
		Identity: identity, Action: "admit", Route: route, Mode: startKind,
		Outcome: admitOutcome, Duration: time.Since(startedAt),
	})
	endOutcome := observability.OutcomeFailure
	if admitOutcome == observability.OutcomeRejected {
		endOutcome = observability.OutcomeRejected
	}
	defer func() {
		s.emit(observability.SessionEvent{
			Identity: identity, Action: "end", Route: route, Mode: startKind,
			Outcome: endOutcome, Duration: time.Since(startedAt),
		})
	}()
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
		exit.Code = gateway.RunJoinSession(ctx, client, s.Hub, fp, res.User, res.SourceIP, execCmd)
	case gateway.ActionMenu:
		spec.ReplyStart(true)
		exit.Code = gateway.RunMenuSession(ctx, client, s.Hub, fp, res.User)
	case gateway.ActionDeploy:
		spec.ReplyStart(true)
		exit.Code = gateway.RunDeploySession(ctx, client, s.Hub, fp, res.User, execCmd)
	case gateway.ActionRejectBusy:
		spec.ReplyStart(true)
		fmt.Fprintf(ch, "%s\r\n", res.Message)
		exit.Code = 1
	case gateway.ActionForbidden:
		spec.ReplyStart(true)
		fmt.Fprintf(client.Stderr, "%s\r\n", res.Message)
		exit.Code = 1
	case gateway.ActionProxyApp:
		exit = gateway.RunAppSession(sessCtx, client, s.Hub, res)
	default:
		spec.ReplyStart(false)
		fmt.Fprintf(client.Stderr, "unhandled action %v\r\n", res.Action)
		exit.Code = 1
	}
	if exit.Code == 0 {
		endOutcome = observability.OutcomeSuccess
	} else if admitOutcome != observability.OutcomeRejected {
		endOutcome = observability.OutcomeFailure
	}
	sendAppExit(ch, exit)
}

func sourceIP(addr net.Addr) string {
	if tcp, ok := addr.(*net.TCPAddr); ok {
		if ip4 := tcp.IP.To4(); ip4 != nil {
			return ip4.String()
		}
		return tcp.IP.String()
	}
	host, _, _ := net.SplitHostPort(addr.String())
	return host
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
