function uselessCall(fn, a) { return fn.call(undefined, a) } // want ".call/.apply with null or undefined this"
