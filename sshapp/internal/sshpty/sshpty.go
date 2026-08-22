// Package sshpty normalizes PTY term/size for Wish apps behind the mux.
//
// OpenSSH -tt with a non-TTY stdin (pipes/FIFOs in CI) still allocates a PTY,
// but reports TERM=dumb and 0x0. Bubble Tea then renders nothing useful.
package sshpty

const (
	DefaultTerm   = "xterm-256color"
	DefaultWidth  = 80
	DefaultHeight = 24
)

// Normalize returns a usable TERM and window size.
func Normalize(term string, width, height int) (string, int, int) {
	if term == "" || term == "dumb" {
		term = DefaultTerm
	}
	if width <= 0 {
		width = DefaultWidth
	}
	if height <= 0 {
		height = DefaultHeight
	}
	return term, width, height
}
