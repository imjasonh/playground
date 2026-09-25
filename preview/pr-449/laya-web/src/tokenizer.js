/** Whitespace tokenizer used by tests. Special ids: pad 0, cls 1, sep 2, mask 3; words start at 100. */
export function createWhitespaceTokenizer() {
  const vocabulary = new Map();
  return {
    maskTok: "[MASK]",
    ids: { cls: 1, sep: 2, mask: 3, pad: 0, maskTok: "[MASK]" },
    encode(text) {
      return String(text)
        .split(/\s+/)
        .filter(Boolean)
        .map((word) => {
          if (vocabulary.has(word)) {
            return vocabulary.get(word);
          }
          const id = 100 + vocabulary.size;
          vocabulary.set(word, id);
          return id;
        });
    },
  };
}

/**
 * BERT WordPiece from a Hugging Face `tokenizer.json`.
 * Covers the ModernBERT / mmBERT files Laya ships: BertNormalizer,
 * BertPreTokenizer, WordPiece, and added specials.
 */
export function createWordPieceTokenizer(spec, config = {}) {
  const model = spec.model ?? {};
  const vocab = new Map(Object.entries(model.vocab ?? {}).map(([token, id]) => [token, Number(id)]));
  const unk = model.unk_token ?? "[UNK]";
  const prefix = model.continuing_subword_prefix ?? "##";
  const maxChars = model.max_input_chars_per_word ?? 100;
  const added = new Map();
  for (const token of spec.added_tokens ?? []) {
    added.set(token.content, token.id);
    vocab.set(token.content, token.id);
  }
  const specials = specialsFromConfig(config, added, vocab);
  const lowercase = spec.normalizer?.lowercase !== false;

  function encodeWord(word) {
    if (word.length > maxChars) {
      return [vocab.get(unk) ?? 0];
    }
    if (vocab.has(word)) {
      return [vocab.get(word)];
    }
    const pieces = [];
    let start = 0;
    while (start < word.length) {
      let end = word.length;
      let found = null;
      while (start < end) {
        const slice = word.slice(start, end);
        const candidate = start === 0 ? slice : prefix + slice;
        if (vocab.has(candidate)) {
          found = vocab.get(candidate);
          break;
        }
        end -= 1;
      }
      if (found === null) {
        return [vocab.get(unk) ?? 0];
      }
      pieces.push(found);
      start = end;
    }
    return pieces;
  }

  return {
    maskTok: specials.maskTok,
    ids: specials,
    vocabSize: vocab.size,
    encode(text) {
      const normalized = normalizeBert(text, lowercase);
      const words = pretokenizeBert(normalized);
      const ids = [];
      for (const word of words) {
        if (added.has(word)) {
          ids.push(added.get(word));
        } else {
          ids.push(...encodeWord(word));
        }
      }
      return ids;
    },
  };
}

export function specialsFromConfig(config, added, vocab) {
  const content = (value, fallback) => {
    if (typeof value === "string") {
      return value;
    }
    if (value && typeof value.content === "string") {
      return value.content;
    }
    return fallback;
  };
  const clsTok = content(config.cls_token, "[CLS]");
  const sepTok = content(config.sep_token, "[SEP]");
  const padTok = content(config.pad_token, "[PAD]");
  const maskTok = content(config.mask_token, "[MASK]");
  const idOf = (token, fallback) => added.get(token) ?? vocab.get(token) ?? fallback;
  return {
    cls: idOf(clsTok, 101),
    sep: idOf(sepTok, 102),
    pad: idOf(padTok, 0),
    mask: idOf(maskTok, 103),
    maskTok,
  };
}

export function normalizeBert(text, lowercase) {
  let out = "";
  for (const char of text.normalize("NFD")) {
    const code = char.codePointAt(0);
    if (code <= 0x1f || (code >= 0x7f && code <= 0x9f)) {
      out += " ";
      continue;
    }
    if (code >= 0x300 && code <= 0x36f) {
      continue;
    }
    out += char;
  }
  return lowercase ? out.toLowerCase() : out;
}

export function pretokenizeBert(text) {
  const words = [];
  let current = "";
  const flush = () => {
    if (current) {
      words.push(current);
      current = "";
    }
  };
  for (const char of text) {
    if (/\s/.test(char)) {
      flush();
    } else if (isPunctuation(char)) {
      flush();
      words.push(char);
    } else {
      current += char;
    }
  }
  flush();
  return words;
}

function isPunctuation(char) {
  const code = char.codePointAt(0);
  if (code >= 33 && code <= 47) {
    return true;
  }
  if (code >= 58 && code <= 64) {
    return true;
  }
  if (code >= 91 && code <= 96) {
    return true;
  }
  if (code >= 123 && code <= 126) {
    return true;
  }
  const category = charUnicodePunctuation(char);
  return category;
}

function charUnicodePunctuation(char) {
  return /\p{P}/u.test(char);
}

export function kevSpecialIdsFromLookup(lookup) {
  return {
    state: lookup("<|fim_prefix|>"),
    question: lookup("<|fim_middle|>"),
    optOpen: lookup("<|box_start|>"),
    optClose: lookup("<|box_end|>"),
    decide: lookup("<|fim_suffix|>"),
  };
}

/** Read Kev delimiter ids from Hub tokenizer files. */
export function kevSpecialIdsFromBundle(files) {
  const lookup = new Map();
  const added = files["added_tokens.json"];
  if (added) {
    if (Array.isArray(added)) {
      for (const token of added) {
        if (token?.content != null && token.id != null) {
          lookup.set(token.content, Number(token.id));
        }
      }
    } else {
      for (const [content, id] of Object.entries(added)) {
        lookup.set(content, Number(id));
      }
    }
  }
  const decoder = files["tokenizer_config.json"]?.added_tokens_decoder;
  if (decoder && typeof decoder === "object") {
    for (const [id, token] of Object.entries(decoder)) {
      const content = typeof token === "string" ? token : token?.content;
      if (content) {
        lookup.set(content, Number(id));
      }
    }
  }
  const ids = kevSpecialIdsFromLookup((token) => lookup.get(token));
  if (Object.values(ids).some((id) => id == null || Number.isNaN(id))) {
    return null;
  }
  return ids;
}
