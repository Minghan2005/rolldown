import type { RawData } from 'ws';

function rawDataToString(data: Buffer | ArrayBuffer | Buffer[]): string {
  if (Buffer.isBuffer(data)) {
    return data.toString('utf8');
  }
  if (Array.isArray(data)) {
    return Buffer.concat(data).toString('utf8');
  }
  return Buffer.from(data).toString('utf8');
}

/**
 * The redesigned runtime sends no upstream state, so every inbound message is either a
 * legacy no-op (e.g. `hmr:invalidate` from the standalone hot context — handled fully
 * client-side under the redesign) or unknown; both are ignored.
 */
export function decodeClientMessage(data: RawData): null {
  const stringified = rawDataToString(data);
  try {
    JSON.parse(stringified);
  } catch {
    // not JSON — ignore
  }
  return null;
}
