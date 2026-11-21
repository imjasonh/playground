import fs from "node:fs";

// Collapse encode.js the way the data URL needs it: drop comments, keep
// statement separators, and leave a space only where two identifiers would
// otherwise glue together.

export function minify(src) {
  let out = "";
  let i = 0;
  const identifier = (ch) => !!ch && /[A-Za-z0-9_$]/.test(ch);
  while (i < src.length) {
    if (src[i] === "/" && src[i + 1] === "/") {
      while (i < src.length && src[i] !== "\n") {
        i++;
      }
      continue;
    }
    if (src[i] === '"' || src[i] === "'") {
      const quote = src[i];
      let j = i + 1;
      while (j < src.length && src[j] !== quote) {
        if (src[j] === "\\") {
          j++;
        }
        j++;
      }
      out += src.slice(i, j + 1);
      i = j + 1;
      continue;
    }
    if (src[i] === " " || src[i] === "\n" || src[i] === "\t") {
      const prev = out[out.length - 1];
      let k = i;
      while (src[k] === " " || src[k] === "\n" || src[k] === "\t") {
        k++;
      }
      if (identifier(prev) && identifier(src[k])) {
        out += " ";
      }
      i = k;
      continue;
    }
    out += src[i];
    i++;
  }
  return out.replaceAll("export ", "");
}

export function quineUrl(src) {
  const script = minify(src) + "D(location.href)";
  // Encode "%" first so the escapes added below stay single-encoded.
  // "?" would start a query and "#" a fragment, and the data URL decoder
  // turns "%25" back into the modulo operator.
  const encoded = script
    .replaceAll("%", "%25")
    .replaceAll("<", "%3C")
    .replaceAll(">", "%3E")
    .replaceAll("?", "%3F")
    .replaceAll("#", "%23")
    .replaceAll("`", "%60");
  return "data:text/html,%3Cscript%3E" + encoded + "%3C/script%3E";
}

const isMain = process.argv[1] && process.argv[1].endsWith("build.js");
if (isMain) {
  const src = fs.readFileSync(new URL("./src/encode.js", import.meta.url), "utf8");
  const url = quineUrl(src);
  const file = "export const quine = " + JSON.stringify(url) + ";\n";
  fs.writeFileSync(new URL("./src/quine.js", import.meta.url), file);
  console.log(url.length);
}
