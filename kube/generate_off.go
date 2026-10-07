//go:build kube_nogenerate

package kube

import (
	"context"
	"errors"
	"io"
)

func (*Manager) generate(context.Context, []string, []Controller, io.Writer, io.Writer) error {
	return errors.New("generate: this build of the program leaves out the generate command; run it from the program's source with go run")
}
