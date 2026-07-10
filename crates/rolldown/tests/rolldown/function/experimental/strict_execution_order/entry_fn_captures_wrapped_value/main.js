// Entry that imports a *value* binding through a pure package barrel from a cross-chunk
// order-wrapped facade, and reads it only from inside a locally-defined function invoked at top
// level during init — vue-vben-admin's `main.ts` shape:
//
//   import { initPreferences } from '@vben/preferences';   // pure barrel over the wrapped facade
//   function initApplication() { ... initPreferences({ ... }) ... }
//   initApplication();
//
// The read sits inside `boot`'s body, statically invisible to any init-time-use analysis, and the
// barrel hop hides the facade behind an eager module. Under on-demand wrapping the barrel stays
// eager (its package marks it side-effect free), its `export * from './facade.js'` statement is
// excluded (the binding resolves through), and nothing ever called `init_facade()` — so `getPref`
// was still `undefined` when `boot()` ran. In source ESM the facade always evaluates before the
// barrel and the barrel before this entry, so emitting the trigger at the barrel's position can
// never be too early; omitting it is the bug.
import './first.js';
import { getPref, tag } from 'pref-pkg';

(globalThis.__events ??= []).push('main');

function boot() {
  return tag(getPref());
}

globalThis.__result = boot();
