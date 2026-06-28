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
  LICENSE,
  'src/storage.js': STORAGE_JS,
  'src/ui/render.js': RENDER_JS,
  'styles/main.css': MAIN_CSS,
  'assets/logo.svg': LOGO_SVG,
};

const mainCommits = [
  {
    oid: '9f1c0a7e2b5d4c8a1f3e6d9b0c2a4f7e8d1b3c5a',
    message: 'Persist tasks to localStorage',
    author: { name: 'Ada Lovelace', email: 'ada@example.com' },
    timestamp: 1717200000,
  },
  {
    oid: '3b2a1c0d9e8f7a6b5c4d3e2f1a0b9c8d7e6f5a4b',
    message: 'Render task list and toggle completion',
    author: { name: 'Ada Lovelace', email: 'ada@example.com' },
    timestamp: 1717100000,
  },
  {
    oid: '7e6d5c4b3a2f1e0d9c8b7a6f5e4d3c2b1a0f9e8d',
    message: 'Initial commit',
    author: { name: 'Grace Hopper', email: 'grace@example.com' },
    timestamp: 1717000000,
  },
];

const darkCommits = [
  {
    oid: 'a1b2c3d4e5f60718293a4b5c6d7e8f9001122334',
    message: 'Add dark mode theme and toggle',
    author: { name: 'Katherine Johnson', email: 'kj@example.com' },
    timestamp: 1717300000,
  },
  ...mainCommits,
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
        commits: mainCommits,
      },
      'feature/dark-mode': {
        files: {
          ...sharedFiles,
          'src/app.js': APP_JS_DARK,
          'src/theme.js': THEME_JS,
          'styles/theme.css': THEME_CSS,
        },
        commits: darkCommits,
      },
    },
  });
}
