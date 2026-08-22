// Package route picks which sshapp to dial from an SSH session without using
// the SSH username. Preference order: SSHAPP environ (SetEnv), subsystem name,
// then the first remote-command path segment (ssh host foo/bar → app foo).
package route

import (
	"strings"
)

const envKey = "SSHAPP"

// Target is the selected app and any remaining command args for the backend.
type Target struct {
	App  string
	Args []string
}

// Session carries the fields route needs. ssh.Session satisfies this.
type Session interface {
	Environ() []string
	Command() []string
	Subsystem() string
}

// FromSession resolves the backend app for sess.
func FromSession(sess Session) (Target, bool) {
	for _, env := range sess.Environ() {
		key, val, ok := strings.Cut(env, "=")
		if !ok || key != envKey {
			continue
		}
		app := normalizeApp(val)
		if app == "" {
			return Target{}, false
		}
		args := sess.Command()
		return Target{App: app, Args: args}, true
	}

	if sub := sess.Subsystem(); sub != "" {
		app := normalizeApp(sub)
		if app == "" {
			return Target{}, false
		}
		return Target{App: app}, true
	}

	cmd := sess.Command()
	if len(cmd) == 0 {
		return Target{}, false
	}
	app, rest := splitPath(cmd[0])
	if app == "" {
		return Target{}, false
	}
	args := append([]string{}, rest...)
	args = append(args, cmd[1:]...)
	return Target{App: app, Args: args}, true
}

func splitPath(path string) (app string, rest []string) {
	path = strings.Trim(path, "/")
	if path == "" {
		return "", nil
	}
	parts := strings.Split(path, "/")
	app = normalizeApp(parts[0])
	if app == "" {
		return "", nil
	}
	if len(parts) > 1 {
		rest = parts[1:]
	}
	return app, rest
}

func normalizeApp(s string) string {
	s = strings.TrimSpace(s)
	s = strings.Trim(s, "/")
	if s == "" {
		return ""
	}
	// Allow hello.domain.com from SetEnv SSHAPP=%n by taking the first label.
	if i := strings.IndexByte(s, '.'); i > 0 {
		s = s[:i]
	}
	for _, r := range s {
		ok := (r >= 'a' && r <= 'z') || (r >= '0' && r <= '9') || r == '-'
		if !ok {
			return ""
		}
	}
	return s
}
