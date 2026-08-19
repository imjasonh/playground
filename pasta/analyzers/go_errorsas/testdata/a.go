package a

import (
	"errors"
	"os"
)

func bad(err error) {
	var e *os.PathError
	errors.As(err, e) // want "second argument to errors.As must be a non-nil pointer"
}

func ok(err error) {
	var e *os.PathError
	errors.As(err, &e)
	errors.Is(err, os.ErrNotExist)
}
