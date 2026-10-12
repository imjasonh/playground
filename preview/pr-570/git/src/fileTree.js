import { splitPath } from './pathUtils.js';

/**
 * @typedef {Object} TreeNode
 * @property {string} name      Display name (last path segment)
 * @property {string} path      Full repo-relative path ('' for the root)
 * @property {'dir'|'file'} type
 * @property {TreeNode[]} children  Sorted children (dirs first), [] for files
 */

/** Case-insensitive name comparison with a stable tiebreak. */
function compareNames(a, b) {
  const an = a.name.toLowerCase();
  const bn = b.name.toLowerCase();
  if (an < bn) return -1;
  if (an > bn) return 1;
  if (a.name < b.name) return -1;
  if (a.name > b.name) return 1;
  return 0;
}

/** Sort a node list: directories first, then files, each alphabetical. */
export function sortNodes(nodes) {
  return [...nodes].sort((a, b) => {
    if (a.type !== b.type) return a.type === 'dir' ? -1 : 1;
    return compareNames(a, b);
  });
}

/**
 * Build a nested directory tree from a flat list of file paths.
 * Returns the synthetic root node whose children are the top-level entries.
 *
 * @param {string[]} paths
 * @returns {TreeNode}
 */
export function buildFileTree(paths) {
  const root = { name: '', path: '', type: 'dir', children: [], _index: new Map() };

  for (const rawPath of paths || []) {
    const segments = splitPath(rawPath);
    if (segments.length === 0) continue;

    let node = root;
    let prefix = '';
    for (let i = 0; i < segments.length; i += 1) {
      const segment = segments[i];
      prefix = prefix ? `${prefix}/${segment}` : segment;
      const isFile = i === segments.length - 1;

      let child = node._index.get(segment);
      if (!child) {
        child = {
          name: segment,
          path: prefix,
          type: isFile ? 'file' : 'dir',
          children: [],
          _index: new Map(),
        };
        node._index.set(segment, child);
        node.children.push(child);
      } else if (!isFile && child.type === 'file') {
        // A file and a directory shared a name segment; prefer directory.
        child.type = 'dir';
      }
      node = child;
    }
  }

  return finalize(root);
}

/** Recursively sort children and drop the internal index maps. */
function finalize(node) {
  const children = sortNodes(node.children.map(finalize));
  return { name: node.name, path: node.path, type: node.type, children };
}

/** Total number of file (leaf) nodes under a subtree. */
export function countFiles(node) {
  if (!node) return 0;
  if (node.type === 'file') return 1;
  return node.children.reduce((sum, child) => sum + countFiles(child), 0);
}

/**
 * Flatten a tree into an ordered list for rendering, honoring which directory
 * paths are expanded. Each row carries its depth for indentation.
 *
 * @param {TreeNode} root
 * @param {Set<string>} expanded  Set of directory paths that are open
 * @returns {{node: TreeNode, depth: number}[]}
 */
export function flattenVisible(root, expanded) {
  const rows = [];
  const walk = (nodes, depth) => {
    for (const node of nodes) {
      rows.push({ node, depth });
      if (node.type === 'dir' && expanded.has(node.path)) {
        walk(node.children, depth + 1);
      }
    }
  };
  walk(root.children, 0);
  return rows;
}
