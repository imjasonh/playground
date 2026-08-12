function f(xs: Array<number>): number { // want `Array<T> can be written as T[]`
    return xs[0];
}

function g(xs: number[]): number { // OK
    return xs[0];
}

function h(xs: Array<string>): string { // want `Array<T> can be written as T[]`
    return xs.join(",");
}

function u(xs: Array<string | number>): void {} // OK: union needs parens; leave alone

type M<T> = Map<string, T>; // OK: Map, not Array
