// Sample app for the Docker-socket e2e: prove the image runs Node, can
// require a lock-resolved dependency, and prints a stable marker on stdout.
const ms = require('ms');

if (ms('1s') !== 1000) {
  console.error('unexpected ms("1s") result:', ms('1s'));
  process.exit(1);
}

console.log('node-image-e2e-ok');
