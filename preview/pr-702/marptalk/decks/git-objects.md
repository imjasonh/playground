---
marp: true
title: How Git stores your code
theme: default
paginate: true
lang: en-US
style: |
  section {
    font-size: 30px;
  }
  section.lead h1 {
    font-size: 64px;
  }
  pre {
    font-size: 26px;
  }
  svg {
    display: block;
    margin: 0 auto;
  }
---

<!-- _class: lead -->
<!-- _paginate: false -->

# How Git stores your code

Four kinds of object and a few pointers

<!--
Every time you commit, Git saves a snapshot of your whole project. Not a list of changes. A snapshot. That sounds wasteful, yet a repository with years of history often fits in a few megabytes. Let's open the dot git directory and see how four kinds of object, plus a handful of pointers, make that work.
-->

---

# Named by their contents

```console
$ echo 'hello' | git hash-object --stdin
ce013625030ba8dba906f756967f9e9ca394464a
```

- The name is a hash of the bytes
- Same bytes, same name, stored once

<!--
Git's object store is a key value database where the key is a hash of the value. Hash the word hello and you get a forty character name that starts with c e zero one. Anyone, on any machine, who hashes the same bytes gets the same name. So identical files are stored once, corruption is easy to spot, and two repositories can compare history by comparing names.
-->

---

# Blobs hold file contents

```console
$ git cat-file -p ce0136
hello
```

- Just the bytes
- No file name, no permissions, no date

<!--
The first kind of object is the blob. A blob is the contents of one file and nothing else. It has no name and no timestamp. If you rename a file, its blob doesn't change at all. If two files in different folders hold the same text, they share one blob.
-->

---

# Trees are directories

```console
$ git cat-file -p 'HEAD^{tree}'
100644 blob ce013625...  README.md
100755 blob 8f94139a...  build.sh
040000 tree 2b1f4c07...  src
```

Each line: mode, type, hash, name

<!--
Names live one level up, in trees. A tree is a directory listing. Each line has a file mode, an object type, a hash, and a name. A line can point at a blob, which is a file, or at another tree, which is a subdirectory. Because a tree lists hashes, the hash of the top tree depends on every file in the project.
-->

---

# Commits are snapshots

```console
$ git cat-file -p HEAD
tree 3c4e9cd7...
parent 1a410efb...
author Ada <ada@example.com> 1700000000 +0000

Fix the parser
```

<!--
A commit points at exactly one tree, the snapshot of the whole project, and at its parent commits. It adds who wrote it, when, and why. A merge commit simply has two parents. Change one byte anywhere and the top tree's hash changes, so the commit's hash changes too. That chain of hashes is what makes history tamper evident.
-->

---

# Tags name a commit

```console
$ git cat-file -p v1.0
object 9fceb02d...
type commit
tag v1.0
tagger Ada <ada@example.com> 1700003600 +0000

First stable release
```

<!--
The fourth kind of object is the annotated tag. It points at another object, almost always a commit, and adds a name, a tagger, and a message. It can also carry a signature. Lightweight tags skip the object entirely and are just a pointer, which brings us to refs.
-->

---

# A new commit reuses almost everything

<svg viewBox="0 0 1000 450" width="1000" role="img" aria-label="Commit B shares README.md and lex.go with commit A and adds one blob and two trees">
  <g stroke="#94a3b8" stroke-width="2">
    <line x1="170" y1="66" x2="170" y2="124" />
    <line x1="830" y1="66" x2="830" y2="124" />
    <line x1="170" y1="176" x2="500" y2="234" />
    <line x1="830" y1="176" x2="500" y2="234" />
    <line x1="170" y1="176" x2="170" y2="234" />
    <line x1="830" y1="176" x2="830" y2="234" />
    <line x1="170" y1="286" x2="500" y2="344" />
    <line x1="830" y1="286" x2="500" y2="344" />
    <line x1="170" y1="286" x2="170" y2="344" />
    <line x1="830" y1="286" x2="830" y2="344" />
  </g>
  <line x1="725" y1="40" x2="290" y2="40" stroke="#2563eb" stroke-width="2" stroke-dasharray="8 6" />
  <polygon points="276,40 292,32 292,48" fill="#2563eb" />
  <text x="500" y="28" text-anchor="middle" font-size="20" fill="#2563eb">parent</text>
  <rect x="65" y="14" width="210" height="52" rx="10" fill="#ffffff" stroke="#94a3b8" stroke-width="2" />
  <text x="170" y="48" text-anchor="middle" font-size="22" fill="currentColor">commit A</text>
  <rect x="725" y="14" width="210" height="52" rx="10" fill="#dbeafe" stroke="#2563eb" stroke-width="2" />
  <text x="830" y="48" text-anchor="middle" font-size="22" fill="currentColor">commit B</text>
  <rect x="65" y="124" width="210" height="52" rx="10" fill="#ffffff" stroke="#94a3b8" stroke-width="2" />
  <text x="170" y="158" text-anchor="middle" font-size="22" fill="currentColor">tree /</text>
  <rect x="725" y="124" width="210" height="52" rx="10" fill="#dbeafe" stroke="#2563eb" stroke-width="2" />
  <text x="830" y="158" text-anchor="middle" font-size="22" fill="currentColor">tree /</text>
  <rect x="65" y="234" width="210" height="52" rx="10" fill="#ffffff" stroke="#94a3b8" stroke-width="2" />
  <text x="170" y="268" text-anchor="middle" font-size="22" fill="currentColor">tree src/</text>
  <rect x="395" y="234" width="210" height="52" rx="10" fill="#ffffff" stroke="#94a3b8" stroke-width="2" />
  <text x="500" y="268" text-anchor="middle" font-size="22" fill="currentColor">README.md</text>
  <rect x="725" y="234" width="210" height="52" rx="10" fill="#dbeafe" stroke="#2563eb" stroke-width="2" />
  <text x="830" y="268" text-anchor="middle" font-size="22" fill="currentColor">tree src/</text>
  <rect x="65" y="344" width="210" height="52" rx="10" fill="#ffffff" stroke="#94a3b8" stroke-width="2" />
  <text x="170" y="378" text-anchor="middle" font-size="22" fill="currentColor">parse.go (old)</text>
  <rect x="395" y="344" width="210" height="52" rx="10" fill="#ffffff" stroke="#94a3b8" stroke-width="2" />
  <text x="500" y="378" text-anchor="middle" font-size="22" fill="currentColor">lex.go</text>
  <rect x="725" y="344" width="210" height="52" rx="10" fill="#dbeafe" stroke="#2563eb" stroke-width="2" />
  <text x="830" y="378" text-anchor="middle" font-size="22" fill="currentColor">parse.go (new)</text>
  <rect x="330" y="420" width="22" height="22" rx="4" fill="#dbeafe" stroke="#2563eb" stroke-width="2" />
  <text x="362" y="438" font-size="20" fill="currentColor">written by commit B</text>
  <rect x="580" y="420" width="22" height="22" rx="4" fill="#ffffff" stroke="#94a3b8" stroke-width="2" />
  <text x="612" y="438" font-size="20" fill="currentColor">already stored</text>
</svg>

<!--
So why doesn't storing full snapshots fill your disk? Say you edit parse dot go in the source folder and commit. Commit B, on the right, needs a new blob for that file, a new tree for the source folder, and a new root tree. The blue boxes are everything it writes. The README and lex dot go already have objects with the right hashes, so both trees point at the same ones. A snapshot costs only what changed.
-->

---

# Branches are files with a hash in them

```console
$ cat .git/HEAD
ref: refs/heads/main
$ cat .git/refs/heads/main
9fceb02d0ae598e95dc970b74767f19372d61af8
```

<!--
A branch is not a copy of anything. It's a small file holding one commit hash. Committing on main writes the new commit, then rewrites that file. HEAD is another file that names the branch you have checked out. Creating a branch writes forty one bytes, which is why branches in Git are nearly free.
-->

---

# Packfiles squeeze history

- Loose objects are zlib-compressed, one file each
- `git gc` packs them into one file
- Similar objects are stored as deltas against each other

<!--
Each new object starts as its own compressed file. Over time, Git packs them into a single packfile. Inside a pack, an object can be stored as a delta, a set of instructions for rebuilding it from a similar object. So snapshots are the model, and deltas are a storage trick underneath. Fetching and cloning send packfiles over the wire.
-->

---

<!-- _class: lead -->

# Recap

Blobs, trees, commits, tags.
Refs point at them. Packs compress them.

<!--
To recap. Blobs hold contents, trees hold names, commits hold snapshots and history, and tags label commits. Every object is named by the hash of its contents. Branches and HEAD are tiny files that point into that graph, and packfiles keep it small. If you want to look at a real pack, the packfile explorer in this playground fetches one and walks you through its objects.
-->
