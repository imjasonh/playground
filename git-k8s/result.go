package gitk8s

import (
	"errors"
	"fmt"
)

// Validate returns why the core program doesn't accept r from a check, or
// nil if it does. The core program accepts a result with a commit, a state
// that checks send, a scope with the fields that it needs, a fix only for
// a Fixed result, and sizes within the limits.
func (r *CheckResult) Validate() error {
	switch r.State {
	case Running, Passed, Failed, Fixed, Error:
	default:
		return fmt.Errorf("state %q isn't Running, Passed, Failed, Fixed, or Error", r.State)
	}
	switch r.Scope {
	case ScopeHead:
		if r.ParentCommit != "" || r.MergeBase != "" {
			return errors.New("a result with the scope Head has neither parentCommit nor mergeBase")
		}
	case ScopeParent:
		if r.ParentCommit == "" || r.MergeBase != "" {
			return errors.New("a result with the scope Parent has parentCommit and not mergeBase")
		}
	case ScopeChange:
		if r.MergeBase == "" || r.ParentCommit != "" {
			return errors.New("a result with the scope Change has mergeBase and not parentCommit")
		}
	case "":
		return errors.New("the result has no scope")
	default:
		return fmt.Errorf("scope %q isn't Head, Parent, or Change", r.Scope)
	}
	switch {
	case r.Commit == "":
		return errors.New("the result has no commit")
	case r.State == Fixed && r.Fix == "":
		return errors.New("the Fixed result has no fix")
	case r.State != Fixed && r.Fix != "":
		return errors.New("only a Fixed result has a fix")
	case len(r.Message) > MaxMessageLength:
		return fmt.Errorf("the message is longer than %d bytes", MaxMessageLength)
	case len(r.Outputs) > MaxOutputs:
		return fmt.Errorf("the result has more than %d outputs", MaxOutputs)
	case len(r.Notes) > MaxNotes:
		return fmt.Errorf("the result has more than %d notes", MaxNotes)
	case len(r.Pod) > MaxPodNameLength:
		return fmt.Errorf("the Pod name is longer than %d bytes", MaxPodNameLength)
	}
	for k, v := range r.Outputs {
		switch {
		case k == "" || len(k) > MaxOutputNameLength:
			return fmt.Errorf("an output name isn't 1 to %d bytes long", MaxOutputNameLength)
		case len(v) > MaxOutputValueLength:
			return fmt.Errorf("output %s is longer than %d bytes", k, MaxOutputValueLength)
		}
	}
	for k, v := range r.Notes {
		switch {
		case k == "" || len(k) > MaxNoteNameLength:
			return fmt.Errorf("a note name isn't 1 to %d bytes long", MaxNoteNameLength)
		case len(v) > MaxNoteValueLength:
			return fmt.Errorf("note %s is longer than %d bytes", k, MaxNoteValueLength)
		}
	}
	return nil
}
