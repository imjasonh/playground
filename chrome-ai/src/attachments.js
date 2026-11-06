// Decides which files the model can take and turns them into prompt content.
// Images and audio go to the model as they are. Text files are read and sent
// as text. Other formats, such as PDF, need a converter this app doesn't have.

/** Text files larger than this don't fit in the context window anyway. */
export const MAX_TEXT_BYTES = 512 * 1024;

const TEXT_EXTENSIONS = Object.freeze([
  'bash', 'c', 'cc', 'cfg', 'conf', 'cpp', 'cs', 'css', 'csv', 'diff', 'go',
  'h', 'hpp', 'htm', 'html', 'ini', 'java', 'js', 'json', 'jsonl', 'jsx',
  'kt', 'log', 'markdown', 'md', 'mjs', 'patch', 'php', 'py', 'rb', 'rs',
  'scss', 'sh', 'sql', 'srt', 'svg', 'swift', 'tex', 'toml', 'ts', 'tsv',
  'tsx', 'txt', 'vtt', 'xml', 'yaml', 'yml', 'zsh',
]);

const TEXT_MIME_TYPES = new Set([
  'application/javascript',
  'application/json',
  'application/ld+json',
  'application/sql',
  'application/toml',
  'application/typescript',
  'application/x-sh',
  'application/x-yaml',
  'application/xml',
  'application/yaml',
  // The model can't decode SVG as an image, but it can read the markup.
  'image/svg+xml',
]);

const MEDIA_NOUNS = Object.freeze({image: 'images', audio: 'audio'});

/**
 * Returns the lowercase extension of `name` without the dot, or ''.
 * @param {string} name
 * @return {string}
 */
export function extensionOf(name) {
  const dot = name.lastIndexOf('.');
  return dot > 0 ? name.slice(dot + 1).toLowerCase() : '';
}

/**
 * Returns how the model would take a file: 'image', 'audio', 'text', or null.
 * @param {{name: string, type: string}} file
 * @return {?string}
 */
export function fileKind({name, type}) {
  if (
    type.startsWith('text/') ||
    TEXT_MIME_TYPES.has(type) ||
    TEXT_EXTENSIONS.includes(extensionOf(name))
  ) {
    return 'text';
  }
  if (type.startsWith('image/')) {
    return 'image';
  }
  if (type.startsWith('audio/')) {
    return 'audio';
  }
  return null;
}

/**
 * Checks whether the model can take `file`.
 * @param {{name: string, type: string, size: number}} file
 * @param {!Array<string>} media The media types this device accepts.
 * @return {{kind: string}|{error: string}}
 */
export function checkFile(file, media) {
  const kind = fileKind(file);
  if (kind === null) {
    return {error: `${file.name}: the model can't read this type of file.`};
  }
  if (kind === 'text' && file.size > MAX_TEXT_BYTES) {
    return {error: `${file.name}: text files can be up to 512 KB.`};
  }
  if (kind !== 'text' && !media.includes(kind)) {
    return {
      error: `${file.name}: the model on this device doesn't accept ${
        MEDIA_NOUNS[kind]
      }.`,
    };
  }
  return {kind};
}

/**
 * Returns the `accept` attribute for the file picker.
 * @param {!Array<string>} media The media types this device accepts.
 * @return {string}
 */
export function acceptList(media) {
  return [
    'text/*',
    ...TEXT_MIME_TYPES,
    ...TEXT_EXTENSIONS.map((ext) => `.${ext}`),
    ...media.map((type) => `${type}/*`),
  ].join(',');
}

/**
 * Builds the prompt for a user turn. Without attachments the prompt is the
 * text itself. Otherwise it's one user message whose content lists the text
 * files, then the images and audio, then the typed text.
 * @param {string} text
 * @param {!Array<{kind: string, name: string, file: !Blob, text: ?string}>}
 *     attachments
 * @return {string|!Array<!Object>}
 */
export function buildPrompt(text, attachments) {
  if (attachments.length === 0) {
    return text;
  }
  const files = attachments.filter((a) => a.kind === 'text');
  const media = attachments.filter((a) => a.kind !== 'text');
  const content = [
    ...files.map((a) => ({
      type: 'text',
      value: `Contents of the file ${a.name}:\n\n${a.text}`,
    })),
    ...media.map((a) => ({type: a.kind, value: a.file})),
  ];
  if (text !== '') {
    content.push({type: 'text', value: text});
  }
  return [{role: 'user', content}];
}
