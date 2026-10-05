package gitk8s

import (
	"errors"
	"fmt"
)

// Validate returns why the core program doesn't accept r from a check, or
// nil if it does. The core program accepts a result with a commit, a state
// that checks send, and sizes within the limits.
func (r *CheckResult) Validate() error {
	switch r.State {
	case Running, Passed, Failed, Fixed, Error:
	default:
		return fmt.Errorf("state %q isn't Running, Passed, Failed, Fixed, or Error", r.State)
	}
	switch {
	case r.Commit == "":
		return errors.New("the result has no commit")
	case len(r.Message) > MaxMessageLength:
		return fmt.Errorf("the message is longer than %d bytes", MaxMessageLength)
	case len(r.Outputs) > MaxOutputs:
		return fmt.Errorf("the result has more than %d outputs", MaxOutputs)
	}
	for k, v := range r.Outputs {
		switch {
		case k == "" || len(k) > MaxOutputNameLength:
			return fmt.Errorf("an output name isn't 1 to %d bytes long", MaxOutputNameLength)
		case len(v) > MaxOutputValueLength:
			return fmt.Errorf("output %s is longer than %d bytes", k, MaxOutputValueLength)
		}
	}
	return nil
}
