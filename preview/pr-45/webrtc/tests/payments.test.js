import test from "node:test";
import assert from "node:assert/strict";

import {
  PAYMENT_REQUEST_KIND,
  PAYMENT_RESULT_KIND,
  DEFAULT_PAYMENT_METHODS,
  normalizeCurrency,
  normalizeAmount,
  createPaymentRequestMessage,
  parsePaymentRequestMessage,
  createPaymentResultMessage,
  parsePaymentResultMessage,
  formatAmount,
  buildPaymentMethodData,
  buildPaymentDetails,
} from "../src/payments.js";

test("normalizeCurrency uppercases and validates ISO codes", () => {
  assert.equal(normalizeCurrency("usd"), "USD");
  assert.equal(normalizeCurrency(" eur "), "EUR");
  assert.throws(() => normalizeCurrency("dollars"));
  assert.throws(() => normalizeCurrency("US"));
  assert.throws(() => normalizeCurrency(""));
});

test("normalizeAmount produces a 2dp string and rejects non-positive", () => {
  assert.equal(normalizeAmount(5), "5.00");
  assert.equal(normalizeAmount("5.5"), "5.50");
  assert.equal(normalizeAmount(0.1), "0.10");
  assert.throws(() => normalizeAmount(0));
  assert.throws(() => normalizeAmount(-3));
  assert.throws(() => normalizeAmount("abc"));
});

test("createPaymentRequestMessage builds a valid, uniquely-identified request", () => {
  const a = createPaymentRequestMessage({ amount: "5", currency: "usd", note: "Lunch" });
  const b = createPaymentRequestMessage({ amount: 10, currency: "EUR" });
  assert.equal(a.kind, PAYMENT_REQUEST_KIND);
  assert.equal(a.amount, "5.00");
  assert.equal(a.currency, "USD");
  assert.equal(a.note, "Lunch");
  assert.equal(b.note, "");
  assert.notEqual(a.id, b.id);
});

test("createPaymentRequestMessage rejects bad amounts/currencies", () => {
  assert.throws(() => createPaymentRequestMessage({ amount: -1, currency: "USD" }));
  assert.throws(() => createPaymentRequestMessage({ amount: 5, currency: "bogus" }));
});

test("parsePaymentRequestMessage validates and normalizes", () => {
  const msg = createPaymentRequestMessage({ amount: 5, currency: "usd", note: "x" });
  const parsed = parsePaymentRequestMessage(msg);
  assert.equal(parsed.amount, "5.00");
  assert.equal(parsed.currency, "USD");
  assert.equal(parsed.id, msg.id);

  assert.equal(parsePaymentRequestMessage(null), null);
  assert.equal(parsePaymentRequestMessage({ kind: "chat" }), null);
  assert.equal(
    parsePaymentRequestMessage({ kind: PAYMENT_REQUEST_KIND, id: "1", amount: -1, currency: "USD" }),
    null,
  );
  assert.equal(
    parsePaymentRequestMessage({ kind: PAYMENT_REQUEST_KIND, id: "", amount: 5, currency: "USD" }),
    null,
  );
});

test("payment result messages round-trip and clamp status", () => {
  const paid = createPaymentResultMessage("abc", "paid", "thanks");
  assert.deepEqual(paid, {
    kind: PAYMENT_RESULT_KIND,
    id: "abc",
    status: "paid",
    detail: "thanks",
  });
  assert.equal(createPaymentResultMessage("abc", "weird").status, "failed");
  assert.equal(parsePaymentResultMessage(paid).status, "paid");
  assert.equal(parsePaymentResultMessage({ kind: "chat" }), null);
});

test("formatAmount localizes currency with a graceful fallback", () => {
  assert.equal(formatAmount("5", "USD"), "$5.00");
  // A malformed currency code makes Intl throw; we fall back to plain text.
  assert.equal(formatAmount("5", "US"), "5.00 US");
  assert.equal(formatAmount("x", "USD"), "");
});

test("buildPaymentMethodData wraps string identifiers, passes objects through", () => {
  assert.deepEqual(buildPaymentMethodData(["https://x/pay"]), [
    { supportedMethods: "https://x/pay" },
  ]);
  const obj = { supportedMethods: "https://y/pay", data: { k: 1 } };
  assert.deepEqual(buildPaymentMethodData([obj]), [obj]);
  assert.deepEqual(buildPaymentMethodData(), [
    { supportedMethods: DEFAULT_PAYMENT_METHODS[0] },
  ]);
});

test("buildPaymentDetails constructs a PaymentRequest total", () => {
  const details = buildPaymentDetails({ amount: "5", currency: "usd", note: "Lunch" });
  assert.deepEqual(details, {
    total: { label: "Lunch", amount: { currency: "USD", value: "5.00" } },
  });
  const noNote = buildPaymentDetails({ amount: 3, currency: "eur", note: "" });
  assert.equal(noNote.total.label, "Payment");
});
