const fs = require('fs');
const path = require('path');
const rimraf = require('rimraf');

if (!rimraf) {
  console.error('require(rimraf) failed');
  process.exit(1);
}

// Distroless has no /usr/bin/env for shebang bins — assert the .bin symlink
// resolves into the virtual store (relative target must be valid in-image).
const bin = path.join(__dirname, 'node_modules', '.bin', 'rimraf');
let st;
try {
  st = fs.lstatSync(bin);
} catch (err) {
  console.error('node_modules/.bin/rimraf missing:', err.message);
  process.exit(1);
}
if (!st.isSymbolicLink() && !st.isFile()) {
  console.error('unexpected .bin/rimraf mode');
  process.exit(1);
}
const target = fs.realpathSync(bin);
if (!target.includes(`${path.sep}.pnpm${path.sep}`) || !/rimraf/i.test(target)) {
  console.error('unexpected rimraf bin target:', target);
  process.exit(1);
}

console.log('ok');
