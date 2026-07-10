// Async-body variant of `entry_fn_captures_wrapped_value`, mirroring vue-vben-admin's `main.ts`
// exactly: the wrapped facade's value binding is awaited inside an async function the entry invokes
// at top level during init. No top-level await — the entry only stores the promise, and the test
// awaits it, so the run stays deterministic.
import './first.js';
import { getPref, tag } from 'pref-pkg';

(globalThis.__events ??= []).push('main');

async function initApplication() {
  const pref = await getPref();
  return tag(pref);
}

globalThis.__ready = initApplication();
