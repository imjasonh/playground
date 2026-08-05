package gateway

import (
	"fmt"
	"io"
	"sync"
)

const (
	SessionShell     = "shell"
	SessionExec      = "exec"
	SessionSubsystem = "subsystem"
)

// ForwardRequest preserves one SSH session request payload byte-for-byte.
type ForwardRequest struct {
	Type    string
	Payload []byte
}

// SessionSpec is the outer client's requested app-session contract.
type SessionSpec struct {
	StartType    string
	StartPayload []byte
	Argument     string
	Setup        []ForwardRequest
	PTY          bool
	Changes      <-chan ForwardRequest

	mu        sync.Mutex
	replyOnce sync.Once
	reply     func(bool)
}

func (s *SessionSpec) SetupRequests() []ForwardRequest {
	s.mu.Lock()
	defer s.mu.Unlock()
	out := make([]ForwardRequest, len(s.Setup))
	copy(out, s.Setup)
	return out
}

// RecordDetachedChange keeps only declarative window state. Signals cannot be
// assigned safely to a replacement process.
func (s *SessionSpec) RecordDetachedChange(change ForwardRequest) error {
	if change.Type != "window-change" {
		return fmt.Errorf("cannot forward %s while backend is migrating", change.Type)
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	for i := len(s.Setup) - 1; i >= 0; i-- {
		if s.Setup[i].Type == "window-change" {
			s.Setup[i] = change
			return nil
		}
	}
	s.Setup = append(s.Setup, change)
	return nil
}

// NewSessionSpec constructs a request contract with a deferred start reply.
func NewSessionSpec(startType string, payload []byte, argument string, setup []ForwardRequest, pty bool, changes <-chan ForwardRequest, reply func(bool)) *SessionSpec {
	return &SessionSpec{
		StartType: startType, StartPayload: append([]byte(nil), payload...),
		Argument: argument, Setup: append([]ForwardRequest(nil), setup...),
		PTY: pty, Changes: changes, reply: reply,
	}
}

// ReplyStart acknowledges or rejects the outer shell/exec/subsystem request once.
func (s *SessionSpec) ReplyStart(ok bool) {
	if s == nil {
		return
	}
	s.replyOnce.Do(func() {
		if s.reply != nil {
			s.reply(ok)
		}
	})
}

// Migratable reports whether reconnecting a fresh backend is safe enough for
// the documented best-effort interactive migration behavior.
func (s *SessionSpec) Migratable() bool {
	return s != nil && s.StartType == SessionShell && s.PTY
}

// ClientSession carries outer streams and request metadata into the gateway.
type ClientSession struct {
	IO     io.ReadWriter
	Stderr io.Writer
	Spec   *SessionSpec
}

// AppExit preserves the backend's exact SSH termination request.
type AppExit struct {
	RequestType string
	Payload     []byte
	Code        int
}
