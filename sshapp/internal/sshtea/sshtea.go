// Package sshtea wraps Wish's Bubble Tea middleware for apps behind the mux.
//
// Prefer this over charm.land/wish/v2/bubbletea when the session is proxied
// (our mux) or otherwise closes the SSH session request channel early.
//
// Workaround: Wish v2.0.3's MiddlewareWithProgramHandler loops on
//
//	case w := <-windowChanges:
//		program.Send(tea.WindowSizeMsg{Width: w.Width, Height: w.Height})
//
// When charm.land/ssh closes winCh (defer close after the request channel
// ends), that receive never blocks and keeps sending {0,0}. The TUI then
// dies within milliseconds. We range the channel instead so close is clean.
// No upstream Wish issue was filed for this; delete this package and switch
// apps to wishtea.Middleware once Wish stops spinning on a closed winCh.
//
// Everything else is Wish: MakeOptions for PTY I/O, plus the usual
// activeterm / logging middlewares in each app.
package sshtea

import (
	tea "charm.land/bubbletea/v2"
	"charm.land/log/v2"
	"charm.land/ssh"
	"charm.land/wish/v2"
	wishtea "charm.land/wish/v2/bubbletea"
	"github.com/charmbracelet/colorprofile"
	"github.com/imjasonh/playground/sshapp/internal/sshpty"
)

// Handler is the same shape as wish/bubbletea.Handler.
type Handler func(sess ssh.Session) (tea.Model, []tea.ProgramOption)

// Middleware serves a Bubble Tea model over SSH, like wishtea.Middleware.
func Middleware(handler Handler) wish.Middleware {
	return MiddlewareWithProgramHandler(func(s ssh.Session) *tea.Program {
		m, opts := handler(s)
		if m == nil {
			return nil
		}
		return tea.NewProgram(m, append(opts, Options(s)...)...)
	})
}

// MiddlewareWithProgramHandler is like wishtea.MiddlewareWithProgramHandler.
// The only intentional difference is `for range winCh` (see package comment).
func MiddlewareWithProgramHandler(handler wishtea.ProgramHandler) wish.Middleware {
	return func(next ssh.Handler) ssh.Handler {
		return func(sess ssh.Session) {
			program := handler(sess)
			if program == nil {
				next(sess)
				return
			}
			_, winCh, ok := sess.Pty()
			if !ok {
				wish.Fatalln(sess, "no active terminal, skipping")
				return
			}
			go func() {
				for win := range winCh {
					program.Send(tea.WindowSizeMsg{Width: win.Width, Height: win.Height})
				}
			}()
			if _, err := program.Run(); err != nil {
				log.Error("app exit with error", "error", err)
			}
			program.Kill()
			next(sess)
		}
	}
}

// Options is wishtea.MakeOptions plus mux-safe env/size for emulated PTYs
// (see package sshpty: OpenSSH -tt over a pipe often reports dumb/0x0).
// Do not also pass tea.WithContext(sess.Context()): behind the mux that
// context can already be done when the program starts.
func Options(s ssh.Session) []tea.ProgramOption {
	opts := wishtea.MakeOptions(s)
	pty, _, ok := s.Pty()
	if !ok {
		return opts
	}
	term, width, height := sshpty.Normalize(pty.Term, pty.Window.Width, pty.Window.Height)
	if !s.EmulatedPty() && term == pty.Term && width == pty.Window.Width && height == pty.Window.Height {
		return opts
	}
	env := append(s.Environ(),
		"TERM="+term,
		"COLORTERM=truecolor",
		"SSH_TTY=/dev/pts/0",
	)
	return append(opts,
		tea.WithEnvironment(env),
		tea.WithColorProfile(colorprofile.ANSI256),
		tea.WithWindowSize(width, height),
	)
}
