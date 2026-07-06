// Payment-request protocol + Web Payments helpers for the WebRTC app.
//
// One peer ("payee") composes a request for money; the message travels over the
// data channel to the other peer ("payer"), whose browser opens the standard
// Web Payments UI (`PaymentRequest`). The payer's browser hands the payment to
// whatever payment handler they have installed and returns a `PaymentResponse`;
// the payer then reports the outcome back to the payee.
//
// Important, honest limitation: the Web Payments API standardizes the *request*
// and hand-off UX, but actually settling funds is done by a payment
// handler/processor — i.e. someone's backend. A truly serverless app like this
// one can compose and present the request and defer to an installed payment
// app, but it cannot itself move money. When no payment handler is available
// the flow degrades to simply showing the requested amount.
//
// The functions here are pure and DOM-free so they can be unit tested under
// Node and reused unchanged in the browser.

export const PAYMENT_REQUEST_KIND = "payment-request";
export const PAYMENT_RESULT_KIND = "payment-result";

// Payment method identifiers offered by default. These are URL-based methods
// resolved to whatever payment handler the payer has installed; the set is
// intentionally overridable so a deployment can point at its own handlers.
export const DEFAULT_PAYMENT_METHODS = ["https://google.com/pay"];

let requestCounter = 0;

// Normalize a currency code to an uppercase 3-letter ISO 4217 string.
export function normalizeCurrency(currency) {
  const code = String(currency == null ? "" : currency).trim().toUpperCase();
  if (!/^[A-Z]{3}$/.test(code)) {
    throw new RangeError(`invalid currency code: ${String(currency)}`);
  }
  return code;
}

// Coerce an amount into the canonical decimal-string form the Web Payments API
// expects (e.g. "5", "5.5" -> "5.50"). Throws on non-positive / non-finite.
export function normalizeAmount(amount) {
  const value = typeof amount === "number" ? amount : Number(String(amount).trim());
  if (!Number.isFinite(value) || value <= 0) {
    throw new RangeError(`amount must be a positive number: ${String(amount)}`);
  }
  return value.toFixed(2);
}

// Build the JSON message a payee sends to request money.
export function createPaymentRequestMessage({ amount, currency, note = "" } = {}) {
  const value = normalizeAmount(amount);
  const code = normalizeCurrency(currency);
  requestCounter += 1;
  return {
    kind: PAYMENT_REQUEST_KIND,
    id: `${Date.now().toString(36)}-${requestCounter}`,
    amount: value,
    currency: code,
    note: typeof note === "string" ? note.slice(0, 140) : "",
  };
}

// Validate + normalize an incoming payment request. Returns a clean object or
// null when the payload isn't a usable request.
export function parsePaymentRequestMessage(msg) {
  if (!msg || msg.kind !== PAYMENT_REQUEST_KIND) return null;
  if (typeof msg.id !== "string" || msg.id.length === 0) return null;
  let amount;
  let currency;
  try {
    amount = normalizeAmount(msg.amount);
    currency = normalizeCurrency(msg.currency);
  } catch {
    return null;
  }
  return {
    id: msg.id,
    amount,
    currency,
    note: typeof msg.note === "string" ? msg.note : "",
  };
}

// Build the payer's reply reporting how the request resolved.
export function createPaymentResultMessage(id, status, detail = "") {
  const allowed = ["paid", "declined", "unsupported", "failed"];
  const normalized = allowed.includes(status) ? status : "failed";
  return {
    kind: PAYMENT_RESULT_KIND,
    id: String(id),
    status: normalized,
    detail: typeof detail === "string" ? detail.slice(0, 140) : "",
  };
}

export function parsePaymentResultMessage(msg) {
  if (!msg || msg.kind !== PAYMENT_RESULT_KIND) return null;
  if (typeof msg.id !== "string" || msg.id.length === 0) return null;
  return {
    id: msg.id,
    status: typeof msg.status === "string" ? msg.status : "failed",
    detail: typeof msg.detail === "string" ? msg.detail : "",
  };
}

// Localized money string for display, e.g. "$5.00". Falls back to a plain
// "5.00 USD" when Intl can't format the given currency.
export function formatAmount(amount, currency) {
  const value = Number(amount);
  const code = String(currency || "").toUpperCase();
  if (!Number.isFinite(value)) return "";
  try {
    return new Intl.NumberFormat(undefined, { style: "currency", currency: code }).format(value);
  } catch {
    return `${value.toFixed(2)} ${code}`;
  }
}

// Build the `methodData` array for `new PaymentRequest(...)`.
export function buildPaymentMethodData(methods = DEFAULT_PAYMENT_METHODS) {
  return methods.map((m) =>
    typeof m === "string" ? { supportedMethods: m } : m,
  );
}

// Build the `details` object for `new PaymentRequest(...)` from a request.
export function buildPaymentDetails(request) {
  const value = normalizeAmount(request.amount);
  const code = normalizeCurrency(request.currency);
  const label = request.note && request.note.trim() ? request.note.trim() : "Payment";
  return {
    total: {
      label,
      amount: { currency: code, value },
    },
  };
}
