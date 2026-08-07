// Command guestinit is injected into OCI-backed microVMs as PID 1.
// It reads /platform-boot.json (entrypoint/cmd/env/workingDir) and execs.
package main

import (
	"flag"

	"github.com/imjasonh/playground/sshcloud/internal/guestinit"
)

func main() {
	spec := flag.String("spec", guestinit.GuestSpec, "path to boot spec JSON")
	flag.Parse()
	guestinit.Run(*spec)
}
