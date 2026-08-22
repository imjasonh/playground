// Package sshtea wraps Wish's Bubble Tea middleware for apps behind the mux.
//
// Prefer this over charm.land/wish/v2/bubbletea directly: Wish's stock window-
// change loop does `case w := <-winCh` on a closed channel, which yields endless
// {0,0} resizes and Quits the program. That shows up behind the mux (and any
// Go SSH client that closes the session request channel early). Everything else
// is Wish — MakeOptions for PTY I/O, activeterm, logging.
package sshtea

import (
	tea "charm.land/bubbletea/v2"
	"charm.land/log/v2"
	"charm.land/ssh"
	"charm.land/wish/v2"
	wishtea "charm.land/wish/v2/bubbletea"
	"github.com/charmbracelet/colorprofile"
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

// MiddlewareWithProgramHandler is like wishtea.MiddlewareWithProgramHandler,
// but ranges the window-change channel so a closed channel stops cleanly.
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

// Options is wishtea.MakeOptions plus mux-safe env for emulated PTYs.
// Do not also pass tea.WithContext(sess.Context()): behind the mux that
// context can already be done when the program starts.
func Options(s ssh.Session) []tea.ProgramOption {
	opts := wishtea.MakeOptions(s)
	if !s.EmulatedPty() {
		return opts
	}
	term := "xterm-256color"
	if pty, _, ok := s.Pty(); ok && pty.Term != "" {
		term = pty.Term
	}
	env := append(s.Environ(),
		"TERM="+term,
		"COLORTERM=truecolor",
		"SSH_TTY=/dev/pts/0",
	)
	return append(opts,
		tea.WithEnvironment(env),
		tea.WithColorProfile(colorprofile.ANSI256),
	)
}
