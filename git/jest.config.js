export default {
  testEnvironment: 'node',
  transform: {},
  // jsdom-environment suites (e.g. the GitStorage registry tests) need
  // TextEncoder/TextDecoder, which jsdom omits; this polyfill is a no-op under
  // the default node environment.
  setupFiles: ['<rootDir>/tests/setup/textEncoding.js'],
  testPathIgnorePatterns: ['/node_modules/', '/e2e/'],
};
