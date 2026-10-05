/** Keeps the first n characters of s, ending with ... when it cuts. */
export function truncate(s: string, n: number): string {
  return s.length <= n ? s : `${s.slice(0, Math.max(0, n - 3))}...`;
}

/** Removes control characters other than newlines and tabs. */
export function stripControl(s: string): string {
  return s.replace(/\p{Cc}/gu, (c) => (c === "\n" || c === "\t" ? c : ""));
}

/** Replaces every copy of secret in s. */
export function redact(s: string, secret: string): string {
  return secret ? s.split(secret).join("[REDACTED]") : s;
}

/** Returns an error's message, with the messages of its causes. */
export function errorMessage(err: unknown): string {
  const parts: string[] = [];
  let cur: unknown = err;
  for (let depth = 0; cur !== undefined && cur !== null && depth < 5; depth++) {
    parts.push(cur instanceof Error ? cur.message : String(cur));
    cur = cur instanceof Error ? cur.cause : undefined;
  }
  return parts.join(": ");
}
