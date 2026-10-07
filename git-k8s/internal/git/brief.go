package git

import "strings"

// Brief returns err with the stderr of each Error in its tree cut down to
// git's own messages, the lines that start with "fatal: " or "error: ". The
// lines that Brief drops include what a remote sent, which git prints after
// "remote: ", such as the body of an HTTP error response from whatever
// server a URL names. Brief returns err itself if it drops nothing, and
// otherwise an error that wraps err.
func Brief(err error) error {
	if err == nil {
		return nil
	}
	full := err.Error()
	msg := full
	for _, e := range commandErrors(err) {
		brief := &Error{Command: e.Command, Code: e.Code, Stderr: ownMessages(e.Stderr)}
		msg = strings.ReplaceAll(msg, e.Error(), brief.Error())
	}
	if msg == full {
		return err
	}
	return &briefError{msg: msg, err: err}
}

// commandErrors returns the Errors in err's tree.
func commandErrors(err error) []*Error {
	switch err := err.(type) {
	case *Error:
		return []*Error{err}
	case interface{ Unwrap() error }:
		return commandErrors(err.Unwrap())
	case interface{ Unwrap() []error }:
		var all []*Error
		for _, err := range err.Unwrap() {
			all = append(all, commandErrors(err)...)
		}
		return all
	}
	return nil
}

// ownMessages returns the lines of a command's stderr that git wrote about
// its own failure.
func ownMessages(stderr string) string {
	var own []string
	for line := range strings.SplitSeq(stderr, "\n") {
		if strings.HasPrefix(line, "fatal: ") || strings.HasPrefix(line, "error: ") {
			own = append(own, line)
		}
	}
	return strings.Join(own, "\n")
}

type briefError struct {
	msg string
	err error
}

func (e *briefError) Error() string { return e.msg }

func (e *briefError) Unwrap() error { return e.err }
