// The redesigned dev runtime sends no upstream state: execution reports were deleted
// with the client-side HMR move, and `import.meta.hot.invalidate()` is handled fully
// client-side. Unknown/legacy messages are ignored by the server.
export type ClientMessage = null;
