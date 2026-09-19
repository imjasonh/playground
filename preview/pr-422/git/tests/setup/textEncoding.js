/**
 * jsdom (in this Jest version) doesn't expose TextEncoder/TextDecoder as
 * globals, but several src modules construct them at import time. Polyfill from
 * Node's util only when missing, so the default `node` test environment — where
 * these are already globals — is unaffected.
 */
import { TextEncoder, TextDecoder } from 'node:util';

if (typeof globalThis.TextEncoder === 'undefined') globalThis.TextEncoder = TextEncoder;
if (typeof globalThis.TextDecoder === 'undefined') globalThis.TextDecoder = TextDecoder;
