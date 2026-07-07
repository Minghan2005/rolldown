use rustc_hash::FxHashMap;

/// Dev-engine-wide rebuild-stamp table backing the versioned shipped map: the server numbers
/// every rebuild and blind-stamps `latest[m] = rebuild_seq` for each changed module, so
/// `latest[m] > shipped[C][m]` reads exactly "this client's copy of `m` is stale".
///
/// A module that never changed since dev-server start has no entry; its stamp is 0
/// everywhere, which compares as never-stale until its first change.
#[derive(Debug, Default)]
pub struct HmrStampTable {
  rebuild_seq: u32,
  /// module stable id → the rebuild that last changed it
  latest: FxHashMap<String, u32>,
}

impl HmrStampTable {
  /// Advances the rebuild counter and returns the new rebuild's stamp.
  pub fn begin_rebuild(&mut self) -> u32 {
    self.rebuild_seq += 1;
    self.rebuild_seq
  }

  pub fn stamp(&mut self, module_stable_id: &str, rebuild_seq: u32) {
    self.latest.insert(module_stable_id.to_string(), rebuild_seq);
  }

  /// The stamp a delivery of `module_stable_id` records right now.
  pub fn render_time_stamp(&self, module_stable_id: &str) -> u32 {
    self.latest.get(module_stable_id).copied().unwrap_or(0)
  }

  pub fn is_stale(&self, module_stable_id: &str, shipped_stamp: u32) -> bool {
    self.render_time_stamp(module_stable_id) > shipped_stamp
  }
}
