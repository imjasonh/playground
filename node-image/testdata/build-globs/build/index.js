const fs = require('fs');

const lua = fs.readFileSync('build/scripts/helper.lua', 'utf8');
if (!lua.includes('lua-ok')) {
  console.error('expected lua asset content missing');
  process.exit(1);
}
if (fs.existsSync('build/index.js.map')) {
  console.error('sourcemap should have been excluded from the image');
  process.exit(1);
}
console.log('globs-ok');
