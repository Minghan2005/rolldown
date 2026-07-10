import assert from 'node:assert';

globalThis.__events = [];

// The entry kicks off `initApplication()` at top level and stores the promise; the async body
// calls the value imported through the pure barrel from the cross-chunk order-wrapped facade.
// Under on-demand wrapping the barrel stayed eager and never forwarded `init_facade()`, so the
// awaited call rejected with `getPref is not a function` — exactly vue-vben-admin's crash shape.
await import('./dist/main.js');

const result = await globalThis.__ready;

assert.strictEqual(
  result,
  'tag:PREF_OK',
  `the async entry body must observe the wrapped facade's init like source ESM would; got ${JSON.stringify(result)} events=${JSON.stringify(globalThis.__events)}`,
);
