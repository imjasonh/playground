// Command gateway is the public SSH entrypoint for SSH App Cloud.
//
// Status: scaffold — routing/session hub logic lives in internal/gateway;
// this binary does not yet accept SSH connections.
package main

import (
	"fmt"
	"os"

	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

func main() {
	_ = &gateway.Hub{
		Store:    store.NewMemory(),
		Sessions: session.NewRegistry(),
	}
	fmt.Fprintln(os.Stderr, "sshcloud gateway: SSH server not wired yet (see README)")
	os.Exit(0)
}
