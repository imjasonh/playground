function use(value) { return value }

function caseBlock(x) { switch (x) { case 1: { const y = 1; use(y); break } default: break } }
