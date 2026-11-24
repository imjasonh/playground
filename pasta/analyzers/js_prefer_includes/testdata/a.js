// Good
if (arr.includes(item)) {}
if (!str.includes("prefix")) {}
if (str.indexOf("prefix") === 0) {}

// Bad
if (arr.indexOf(item) !== -1) {} // want "use .includes() instead of comparing .indexOf()"
if (str.indexOf("prefix") === -1) {} // want "use !.includes() instead of comparing .indexOf()"
if (str.indexOf("foo") >= 0) {} // want "use .includes() instead of comparing .indexOf()"
if (str.indexOf("bar") < 0) {} // want "use !.includes() instead of comparing .indexOf()"
