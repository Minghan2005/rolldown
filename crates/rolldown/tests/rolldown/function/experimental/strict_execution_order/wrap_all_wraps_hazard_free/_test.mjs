import assert from 'node:assert';
import fs from 'node:fs';
import { captureConsoleLog } from '../../../../_test_helpers/capture-console-log.mjs';

// Default strict mode is wrap-all: even a hazard-free graph wraps (unlike on-demand, which
// leaves it byte-identical to flag-off) and the init chain reproduces source order.
const logs = await captureConsoleLog(() => import('./dist/main.js'));

assert.deepStrictEqual(logs, ['dep', 'main v']);
const code = fs.readFileSync(new URL('./dist/main.js', import.meta.url), 'utf8');
assert.ok(code.includes('init_'), 'wrap-all must wrap');
