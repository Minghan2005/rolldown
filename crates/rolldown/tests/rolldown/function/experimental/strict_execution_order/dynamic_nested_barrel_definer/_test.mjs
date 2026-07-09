import assert from 'node:assert';

globalThis.__events = [];

const { loadPage } = await import('./dist/main.js');
await loadPage();

// The definer is reachable only through barrel-outer -> barrel-inner -> definer, and the reader
// that consumes it lives inside the dynamically imported chunk. Under strict execution order the
// barrel wrappers must initialize the definer before the reader reads `value`. A regression in the
// order-wrap machinery left the inner barrel's `init_*` wrapper empty, so the definer never ran:
// its `definer` event dropped and `value` read `undefined` (issue family #8777 / #8989).
assert.ok(globalThis.__events.includes('definer'), 'definer module must have been initialized');
assert.ok(
  globalThis.__events.includes('reader:5'),
  `reader must read the initialized definer value; got ${JSON.stringify(globalThis.__events)}`,
);
assert.ok(
  globalThis.__events.indexOf('definer') < globalThis.__events.indexOf('reader:5'),
  'definer must initialize before the reader reads it',
);
assert.deepStrictEqual(globalThis.__events, [
  'main',
  'leaf',
  'definer',
  'reader:5',
  'reader-host:105',
  'dynamic-page',
]);
