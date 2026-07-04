import { InMemoryRepoSource } from './repoSource.js';

/**
 * A small but realistic sample project used by "demo mode". It exercises every
 * part of the browser without any network: a nested file tree, multiple file
 * types (JS/JSON/CSS/Markdown/SVG), two branches that differ, and commit
 * history. The real clone flow produces a RepoSource with the same shape.
 */

const README = `# Tasklite

A tiny dependency-free todo app, used here as demo data for the in-browser
git client. Everything you see was loaded from local storage — no network
request was made.

## Features

- Add, complete, and clear tasks
- Persists to localStorage
- Switch branches (try \`feature/dark-mode\`) to see the file tree change

## Layout

- \`src/\` — application code
- \`styles/\` — stylesheets
- \`assets/\` — static assets
`;

const PACKAGE_JSON = `{
  "name": "tasklite",
  "version": "0.3.0",
  "private": true,
  "type": "module",
  "scripts": {
    "start": "serve ."
  }
}
`;

const STORAGE_JS = `const KEY = 'tasklite.tasks';

export function loadTasks() {
  try {
    return JSON.parse(localStorage.getItem(KEY)) || [];
  } catch {
    return [];
  }
}

export function saveTasks(tasks) {
  localStorage.setItem(KEY, JSON.stringify(tasks));
}
`;

const RENDER_JS = `export function renderList(container, tasks, onToggle) {
  container.replaceChildren();
  for (const task of tasks) {
    const li = document.createElement('li');
    li.textContent = task.title;
    li.classList.toggle('done', task.done);
    li.addEventListener('click', () => onToggle(task.id));
    container.appendChild(li);
  }
}
`;

const MAIN_CSS = `:root {
  --accent: #2563eb;
  --bg: #ffffff;
  --fg: #1f2933;
}

body {
  font-family: system-ui, sans-serif;
  background: var(--bg);
  color: var(--fg);
  margin: 0 auto;
  max-width: 40rem;
  padding: 2rem;
}

li.done {
  text-decoration: line-through;
  opacity: 0.6;
}
`;

const THEME_CSS = `/* Added on feature/dark-mode */
:root {
  --accent: #60a5fa;
  --bg: #0b1020;
  --fg: #e5e7eb;
}
`;

const LOGO_SVG = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64" width="64" height="64">
  <rect width="64" height="64" rx="12" fill="#2563eb"/>
  <path d="M18 33l9 9 19-21" fill="none" stroke="#fff" stroke-width="6"
        stroke-linecap="round" stroke-linejoin="round"/>
</svg>
`;

const GITIGNORE = `node_modules/
dist/
*.log
`;

const GITATTRIBUTES = `assets/intro.mp4 filter=lfs diff=lfs merge=lfs -text
`;

// A Git LFS pointer: what's committed for an LFS-tracked file is this small text
// stub, not the real bytes. The viewer detects it and shows a notice instead of
// rendering the metadata as the file.
const INTRO_MP4_POINTER = `version https://git-lfs.github.com/spec/v1
oid sha256:9a8b7c6d5e4f30211223344556677889900aabbccddeeff00112233445566778
size 10485760
`;

// A `.gitmodules` entry describing the demo's submodule. The submodule itself is
// a gitlink (a pinned commit of another repo); its files aren't in this clone.
const GITMODULES = `[submodule "widget"]
\tpath = vendor/widget
\turl = https://github.com/acme/widget.git
`;

const LICENSE = `MIT License

Copyright (c) 2026 Tasklite contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction.
`;

const APP_JS_MAIN = `import { loadTasks, saveTasks } from './storage.js';
import { renderList } from './ui/render.js';

const list = document.getElementById('list');
let tasks = loadTasks();

function toggle(id) {
  tasks = tasks.map((t) => (t.id === id ? { ...t, done: !t.done } : t));
  saveTasks(tasks);
  renderList(list, tasks, toggle);
}

renderList(list, tasks, toggle);
`;

const APP_JS_DARK = `import { loadTasks, saveTasks } from './storage.js';
import { renderList } from './ui/render.js';
import { initTheme } from './theme.js';

const list = document.getElementById('list');
let tasks = loadTasks();

function toggle(id) {
  tasks = tasks.map((t) => (t.id === id ? { ...t, done: !t.done } : t));
  saveTasks(tasks);
  renderList(list, tasks, toggle);
}

initTheme();
renderList(list, tasks, toggle);
`;

// Earlier snapshots of src/app.js, so blame() on `main` has real per-commit
// content to attribute lines against. Newest (APP_JS_MAIN) first; each older
// version drops the lines a later commit introduced:
//   - "Initial commit" (Grace) — bare skeleton, no rendering or persistence,
//   - "Render task list…" (Ada) — adds the render import and its calls,
//   - "Persist tasks…" (Ada)   — adds storage import, loadTasks, saveTasks.
const APP_JS_RENDER = `import { renderList } from './ui/render.js';

const list = document.getElementById('list');
let tasks = [];

function toggle(id) {
  tasks = tasks.map((t) => (t.id === id ? { ...t, done: !t.done } : t));
  renderList(list, tasks, toggle);
}

renderList(list, tasks, toggle);
`;

const APP_JS_INITIAL = `const list = document.getElementById('list');
let tasks = [];

function toggle(id) {
  tasks = tasks.map((t) => (t.id === id ? { ...t, done: !t.done } : t));
}
`;

const THEME_JS = `const KEY = 'tasklite.theme';

export function initTheme() {
  const saved = localStorage.getItem(KEY) || 'light';
  document.documentElement.dataset.theme = saved;
}

export function toggleTheme() {
  const next =
    document.documentElement.dataset.theme === 'dark' ? 'light' : 'dark';
  document.documentElement.dataset.theme = next;
  localStorage.setItem(KEY, next);
}
`;

const sharedFiles = {
  'README.md': README,
  'package.json': PACKAGE_JSON,
  '.gitignore': GITIGNORE,
  '.gitattributes': GITATTRIBUTES,
  '.gitmodules': GITMODULES,
  LICENSE,
  'src/storage.js': STORAGE_JS,
  'src/ui/render.js': RENDER_JS,
  'styles/main.css': MAIN_CSS,
  'assets/logo.svg': LOGO_SVG,
  'assets/intro.mp4': INTRO_MP4_POINTER,
  // A symlink is committed as a blob whose content is the link target. The
  // viewer detects it (via entryMeta) and shows where it points.
  'docs/latest.md': '../README.md',
};

// Paths in `sharedFiles` that are actually symbolic links (value = target).
const sharedSymlinks = {
  'docs/latest.md': '../README.md',
};

// A gitlink: pins github.com/acme/widget at a commit not stored in this clone.
const sharedSubmodules = {
  'vendor/widget': {
    name: 'widget',
    url: 'https://github.com/acme/widget.git',
    oid: 'c0ffee0011223344556677889900aabbccddeeff',
  },
};

const mainCommits = [
  {
    oid: '9f1c0a7e2b5d4c8a1f3e6d9b0c2a4f7e8d1b3c5a',
    message: 'Persist tasks to localStorage',
    author: { name: 'Ada Lovelace', email: 'ada@example.com' },
    timestamp: 1717200000,
    changed: ['src/storage.js', 'src/app.js'],
  },
  {
    oid: '3b2a1c0d9e8f7a6b5c4d3e2f1a0b9c8d7e6f5a4b',
    message: 'Render task list and toggle completion',
    author: { name: 'Ada Lovelace', email: 'ada@example.com' },
    timestamp: 1717100000,
    changed: ['src/ui/render.js', 'src/app.js', 'styles/main.css'],
  },
  {
    oid: '7e6d5c4b3a2f1e0d9c8b7a6f5e4d3c2b1a0f9e8d',
    message: 'Initial commit',
    author: { name: 'Grace Hopper', email: 'grace@example.com' },
    timestamp: 1717000000,
    changed: [
      'README.md',
      'package.json',
      '.gitignore',
      'LICENSE',
      'src/app.js',
      'src/storage.js',
      'styles/main.css',
      'assets/logo.svg',
    ],
  },
];

const darkCommits = [
  {
    oid: 'a1b2c3d4e5f60718293a4b5c6d7e8f9001122334',
    message: 'Add dark mode theme and toggle',
    author: { name: 'Katherine Johnson', email: 'kj@example.com' },
    timestamp: 1717300000,
    changed: ['src/app.js', 'src/theme.js', 'styles/theme.css'],
  },
  ...mainCommits,
];

// src/app.js content at each commit that changed it (newest first), so blame()
// has real per-commit snapshots to attribute against. The oids mirror the
// matching commits above so blame chips link back to the right history entries.
const appJsHistory = [
  { oid: mainCommits[0].oid, content: APP_JS_MAIN },
  { oid: mainCommits[1].oid, content: APP_JS_RENDER },
  { oid: mainCommits[2].oid, content: APP_JS_INITIAL },
];

export function createDemoSource() {
  return new InMemoryRepoSource({
    fullName: 'tasklite/demo',
    url: null,
    defaultBranch: 'main',
    // A tag (aliased to a branch snapshot) so the ref picker shows tag browsing
    // without a network. Matches package.json's version.
    tags: { 'v0.3.0': 'main' },
    branches: {
      main: {
        files: {
          ...sharedFiles,
          'src/app.js': APP_JS_MAIN,
        },
        symlinks: sharedSymlinks,
        submodules: sharedSubmodules,
        fileVersions: { 'src/app.js': appJsHistory },
        commits: mainCommits,
      },
      'feature/dark-mode': {
        files: {
          ...sharedFiles,
          'src/app.js': APP_JS_DARK,
          'src/theme.js': THEME_JS,
          'styles/theme.css': THEME_CSS,
        },
        symlinks: sharedSymlinks,
        submodules: sharedSubmodules,
        commits: darkCommits,
      },
    },
  });
}
