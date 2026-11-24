package main

import (
	"fmt"
	"net/url"
	"strings"
)

// argVCS names a build argument that turns off vcs-url detection when it
// is "false", like apko build --vcs=false.
const argVCS = "APKO_VCS"

// detectVCSURL returns the vcs-url that apko build would detect for a git
// checkout, from the git details that Buildx sends with a build of one:
// the remote URL as the vcs:source option and the commit as vcs:revision.
// It returns "" when there's no vcs:source.
//
// Like apko, it removes credentials from the remote, rewrites an scp-style
// remote (user@host:path) as a git+ssh URL, and appends "@<commit>".
func detectVCSURL(opts map[string]string) string {
	src := opts["vcs:source"]
	if src == "" {
		return ""
	}
	u, err := url.Parse(src)
	if err != nil || u.Scheme == "" {
		u, err = url.Parse("git+ssh://" + strings.Replace(src, ":", "/", 1))
		if err != nil {
			return ""
		}
	}
	u.User = nil
	vcs := u.String()
	if rev := opts["vcs:revision"]; rev != "" {
		vcs = fmt.Sprintf("%s@%s", vcs, rev)
	}
	return vcs
}
