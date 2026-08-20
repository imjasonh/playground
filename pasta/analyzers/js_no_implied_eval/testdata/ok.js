function use(value) { return value }

function timerFn() { setTimeout(() => { use(1) }, 0) }
