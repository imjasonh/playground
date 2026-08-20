const bound = (function () { return 1 }).bind(this) // want ".bind(this) on a function that does not use this"
