// Command fakestore issues Sigstore bundles from a test-only Sigstore
// instance: a Fulcio CA, a Rekor v2 log, a CT log, and an RFC 3161 timestamp
// authority whose keys it generates and keeps on disk.
//
// The bundles have the same profile as the ones that Sigstore's public-good
// and staging instances produce for a GitHub Actions workflow, so c3-boot
// devices can be tested end to end without network access. Never put a
// trusted root that fakestore writes on a production device.
package main

import (
	"fmt"
	"io"
	"os"
)

const usage = `usage: fakestore <command> [flags]

Commands:
  init    create a CA, log, CT log, and TSA, and write trusted_root.json
  sign    sign an artifact and write a Sigstore bundle
  verify  verify a bundle with sigstore-go

Run "fakestore <command> -h" for the flags of a command.
`

func main() {
	os.Exit(run(os.Args[1:], os.Stdout, os.Stderr))
}

// run runs the command in args and returns the process exit code.
func run(args []string, stdout, stderr io.Writer) int {
	if len(args) == 0 {
		fmt.Fprint(stderr, usage)
		return 2
	}
	var err error
	switch args[0] {
	case "init":
		err = runInit(args[1:], stderr)
	case "sign":
		err = runSign(args[1:], stderr)
	case "verify":
		err = runVerify(args[1:], stdout, stderr)
	case "-h", "-help", "--help", "help":
		fmt.Fprint(stdout, usage)
		return 0
	default:
		fmt.Fprintf(stderr, "unknown command %q\n\n%s", args[0], usage)
		return 2
	}
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 1
	}
	return 0
}
