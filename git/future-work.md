# git — future work

This is the living roadmap for the in-browser `git` client. It started life as a
**read-only** code browser; the first milestone below — the **write / commit /
push flow** that the original README and PR called out as the explicit next step
— is now implemented. The rest is the backlog.

## Done

### Read-write editing (edit → stage → commit → push)

The `RepoSource` contract gained a write surface that both implementations
honor, so the whole flow is exercised without a network via the in-memory demo
source:

- `writeFile(path, content)` — create or modify a file (auto-staged).
- `deleteFile(path)` — remove a file (deletion staged).
- `status()` — working-tree changes vs the last commit (`new` / `modified` /
  `deleted`).
- `commit({ message, author })` — commit the staged changes on the current
  branch.
- `push({ token, username })` — publish the branch to its remote (real clones
  only; the demo is local-only).
- `readOnly` / `canPush` capability flags drive which UI affordances appear.

For `GitRepoSource` (isomorphic-git + lightning-fs), the first edit lazily
materializes a working tree for the current branch (a `checkout`, since clones
are made with `noCheckout`), resets the local branch ref to the displayed
commit, and from then on reads/status/commits come from that working tree and
local head. The remote-tracking read path used for plain browsing is unchanged.

UI: an **Edit/Delete** action on the file viewer, a **+ New file** modal, a
**Changes** drawer (staged list, author fields, commit message, commit + push),
dirty markers in the tree, and a session-only token field (never persisted).

## Backlog (not yet implemented)

Roughly in priority order:

- **Diff view** — show a line-level diff for a staged file instead of just its
  status, and a side-by-side/inline diff in the viewer.
- **Discard / unstage** — per-file "discard changes" and "unstage" actions in the
  Changes drawer (currently the only way to drop a change is to edit it back or
  switch branches).
- **Pull that merges** — `Pull / Update` fetches and advances the read view, but
  does not fast-forward/merge a local branch that has commits. Add a real
  fast-forward (and surface conflicts when it can't).
- **Branch + tag creation** — create a new branch from the current commit, and
  check it out for editing; lightweight tag creation.
- **Conflict resolution** — a minimal UI for resolving merge/push conflicts.
- **Pull requests** — optional host integrations (GitHub/GitLab) to open a PR
  from a pushed branch.
- **Syntax highlighting** — currently the viewer is plain monospaced text.
- **Larger-file editing** — the editor loads the whole file into a `<textarea>`;
  consider a virtualized editor for very large files.
- **Credential UX** — optional OAuth device-flow helper and clearer per-host
  guidance (GitHub username=token vs GitLab oauth2 + token).

## Testing constraints

The agent/CI sandbox blocks egress to git hosts and the CORS proxy, so the live
**network** paths (clone and push) cannot run in automated tests. They are
covered the same way the original clone path was:

- Unit tests drive `GitRepoSource` against an injected fake git that models the
  checkout → add → remove → statusMatrix → commit → push sequence (auth payload,
  ref advancement, status mapping, rejection handling).
- Playwright drives the entire edit → stage → commit UI end to end against the
  in-memory demo source (no network).
- The real push is best verified on the PR preview deploy.
