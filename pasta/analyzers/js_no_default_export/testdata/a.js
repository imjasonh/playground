export default function Foo() {} // want "default export"

export default class Bar {} // want "default export"

export function baz() {}

export const qux = 1;

const local = 1;
export { local };
