const fs = require('fs');
const ms = require('ms');

const src = fs.readFileSync(require.resolve('ms'), 'utf8');
if (!src.includes('node-image patched fixture marker')) {
  console.error('patched marker missing from ms source');
  process.exit(1);
}
if (ms('1s') !== 1000) {
  console.error('unexpected ms("1s")', ms('1s'));
  process.exit(1);
}
console.log('patched-ok');
