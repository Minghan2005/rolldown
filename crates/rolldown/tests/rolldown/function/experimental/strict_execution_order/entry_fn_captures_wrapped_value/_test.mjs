import assert from 'node:assert';

globalThis.__events = [];

// Importing the entry runs its top-level `boot()`, which reads `getPref` — a value imported
// through the pure barrel from the cross-chunk order-wrapped facade. In source ESM the facade
// evaluates before the barrel and the barrel before the entry, so `getPref` is defined by the time
// `boot()` runs. Under on-demand wrapping the barrel stayed eager, its excluded star re-export
// forwarded nothing, and no one called `init_facade()` — `getPref` was `undefined` and `boot()`
// threw.
await import('./dist/main.js');

assert.strictEqual(
  globalThis.__result,
  'tag:PREF_OK',
  `the eager barrel must forward the wrapped facade's init from its excluded re-export hop; got ${JSON.stringify(globalThis.__result)} events=${JSON.stringify(globalThis.__events)}`,
);
