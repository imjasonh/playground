function optCallOk(x) { return x?.fn() }
function optMemOk(x) { return x?.y?.z }
function coalesceCall(x, fallback) { return (x?.fn ?? fallback)() }
function coalesceMem(x, text) { return (x?.[1] ?? text).trim() }
