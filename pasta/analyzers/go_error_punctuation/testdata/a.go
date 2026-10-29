package a

import (
	"errors"
	"fmt"
)

func bad() error {
	if err := errors.New("something bad happened."); err != nil { // want "error string ends with punctuation"
		return err
	}
	if err := fmt.Errorf("something bad happened!"); err != nil { // want "error string ends with punctuation"
		return err
	}
	return fmt.Errorf("did you mean %s?", "x") // want "error string ends with punctuation"
}

func raw() error {
	return errors.New(`something bad happened.`) // want "error string ends with punctuation"
}

func ok() error {
	_ = errors.New("something bad happened")
	_ = fmt.Errorf("something bad happened: %w", errors.New("disk"))
	_ = errors.New("usage: stress analyze RUN_DIR...")
	_ = fmt.Errorf("Synced = %+v", 1)
	_ = fmt.Errorf("URL is invalid")
	return nil
}
