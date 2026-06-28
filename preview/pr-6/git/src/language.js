import { basename, extname } from './pathUtils.js';

/** Extension (with dot) -> human-readable language label. */
const EXTENSION_LANGUAGES = {
  '.js': 'JavaScript',
  '.mjs': 'JavaScript',
  '.cjs': 'JavaScript',
  '.jsx': 'JavaScript (JSX)',
  '.ts': 'TypeScript',
  '.tsx': 'TypeScript (TSX)',
  '.json': 'JSON',
  '.html': 'HTML',
  '.htm': 'HTML',
  '.css': 'CSS',
  '.scss': 'SCSS',
  '.sass': 'Sass',
  '.less': 'Less',
  '.md': 'Markdown',
  '.markdown': 'Markdown',
  '.py': 'Python',
  '.rb': 'Ruby',
  '.go': 'Go',
  '.rs': 'Rust',
  '.java': 'Java',
  '.kt': 'Kotlin',
  '.c': 'C',
  '.h': 'C Header',
  '.cpp': 'C++',
  '.cc': 'C++',
  '.hpp': 'C++ Header',
  '.cs': 'C#',
  '.php': 'PHP',
  '.swift': 'Swift',
  '.sh': 'Shell',
  '.bash': 'Shell',
  '.zsh': 'Shell',
  '.yml': 'YAML',
  '.yaml': 'YAML',
  '.toml': 'TOML',
  '.xml': 'XML',
  '.sql': 'SQL',
  '.txt': 'Plain Text',
  '.svg': 'SVG',
  '.vue': 'Vue',
  '.svelte': 'Svelte',
  '.dockerfile': 'Dockerfile',
  '.makefile': 'Makefile',
  '.gradle': 'Gradle',
};

/** Exact filenames (no useful extension) -> language label. */
const FILENAME_LANGUAGES = {
  dockerfile: 'Dockerfile',
  makefile: 'Makefile',
  '.gitignore': 'Git Config',
  '.gitattributes': 'Git Config',
  '.npmrc': 'Config',
  '.editorconfig': 'Config',
  license: 'Plain Text',
};

const IMAGE_EXTENSIONS = new Set([
  '.png',
  '.jpg',
  '.jpeg',
  '.gif',
  '.webp',
  '.bmp',
  '.ico',
  '.avif',
  '.svg',
]);

/** Extensions whose contents are not human-readable text. */
const BINARY_EXTENSIONS = new Set([
  ...IMAGE_EXTENSIONS,
  '.pdf',
  '.zip',
  '.gz',
  '.tar',
  '.tgz',
  '.bz2',
  '.7z',
  '.rar',
  '.woff',
  '.woff2',
  '.ttf',
  '.otf',
  '.eot',
  '.mp3',
  '.wav',
  '.ogg',
  '.flac',
  '.mp4',
  '.webm',
  '.mov',
  '.avi',
  '.wasm',
  '.exe',
  '.dll',
  '.so',
  '.dylib',
  '.class',
  '.jar',
  '.bin',
  '.dat',
  '.o',
  '.a',
  '.lib',
  '.pyc',
  '.heic',
]);

/** Map an SVG/image extension set check. */
export function isImagePath(path) {
  return IMAGE_EXTENSIONS.has(extname(path));
}

/** MIME type for image extensions, used to build data/object URLs. */
export function imageMimeType(path) {
  const ext = extname(path);
  switch (ext) {
    case '.svg':
      return 'image/svg+xml';
    case '.jpg':
    case '.jpeg':
      return 'image/jpeg';
    case '.ico':
      return 'image/x-icon';
    default:
      return `image/${ext.slice(1)}`;
  }
}

/** True for extensions known to hold binary data. */
export function isBinaryExtension(path) {
  return BINARY_EXTENSIONS.has(extname(path));
}

/** Best-effort human-readable language label for a path. */
export function languageForPath(path) {
  const name = basename(path).toLowerCase();
  if (FILENAME_LANGUAGES[name]) return FILENAME_LANGUAGES[name];
  const ext = extname(path);
  return EXTENSION_LANGUAGES[ext] || 'Plain Text';
}

/**
 * Heuristically decide whether a byte buffer is binary by sampling for NUL
 * bytes and a high proportion of non-printable control characters.
 *
 * @param {Uint8Array} bytes
 */
export function looksBinary(bytes) {
  if (!bytes || bytes.length === 0) return false;
  const sample = Math.min(bytes.length, 8000);
  let suspicious = 0;
  for (let i = 0; i < sample; i += 1) {
    const byte = bytes[i];
    if (byte === 0) return true;
    // allow tab(9), LF(10), CR(13), FF(12), BS(8); flag other C0 controls
    if (byte < 9 || (byte > 13 && byte < 32)) suspicious += 1;
  }
  return suspicious / sample > 0.3;
}
