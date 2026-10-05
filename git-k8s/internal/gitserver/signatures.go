package gitserver

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
)

// preReceive checks every commit that a push adds to the repository. Like
// GitHub, it needs a good signature from a key that belongs to the
// committer: git log reports %G? as G when the allowed signers file lists
// the key, and %GS as the principal that it lists the key for.
const preReceive = `#!/bin/sh
while read -r old new ref; do
  case "$new" in *[!0]*) ;; *) continue ;; esac
  for commit in $(git rev-list "$new" --not --all); do
    set -- $(git log -1 --format='%G? %GS %ce' "$commit")
    if [ "$1" != G ] || [ "$2" != "$3" ]; then
      echo "$ref: commit $commit isn't signed with its committer's key" >&2
      exit 1
    fi
  done
done
`

// requireSignatures makes the repository at dir reject pushes that add
// commits that aren't signed with a key in allowedSigners.
func requireSignatures(dir, allowedSigners string) error {
	abs, err := filepath.Abs(allowedSigners)
	if err != nil {
		return err
	}
	cmd := exec.Command("git", "-C", dir, "config", "gpg.ssh.allowedSignersFile", abs)
	cmd.Env = append(os.Environ(), "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL="+os.DevNull)
	if out, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("git config: %v: %s", err, out)
	}
	hooks := filepath.Join(dir, "hooks")
	if err := os.MkdirAll(hooks, 0o755); err != nil {
		return err
	}
	return os.WriteFile(filepath.Join(hooks, "pre-receive"), []byte(preReceive), 0o755)
}
