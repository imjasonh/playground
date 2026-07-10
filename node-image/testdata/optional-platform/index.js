const esbuild = require('esbuild');

// Loading the native @esbuild/linux-* optional must succeed; .version alone
// can pass even when the platform binary is missing from the image.
const result = esbuild.transformSync('export const n = 1 + 2', {
  format: 'cjs',
  loader: 'js',
});
if (!result || typeof result.code !== 'string' || !result.code.includes('1 + 2')) {
  console.error('esbuild.transformSync failed:', result && result.code);
  process.exit(1);
}
console.log('esbuild-native-ok');
