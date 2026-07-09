use super::hmr_patch::HmrPatch;

/// The server never decides a reload: it ships a superset patch and the client's own
/// graph walk decides per tab whether to hot-apply, skip, or reload itself.
#[derive(Debug, Clone)]
pub enum HmrUpdate {
  Patch(HmrPatch),
  /// For the hmr request, there're no actual actions that need to be done.
  Noop,
}
