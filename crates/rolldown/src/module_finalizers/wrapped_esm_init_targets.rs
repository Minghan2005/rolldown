use rolldown_common::{
  ConcatenateWrappedModuleKind, ImportKind, ImportRecordIdx, ImportRecordMeta, IndexModules,
  ModuleIdx, NormalModule, Specifier, SymbolRef, SymbolRefDb, WrapKind,
};
use rustc_hash::FxHashSet;

use crate::{
  stages::generate_stage::order_wrap_state::{EsmInitOrigin, OrderWrapState},
  type_alias::IndexStmtInfos,
  types::linking_metadata::{LinkingMetadata, LinkingMetadataVec},
};

pub struct WrappedEsmInitTargetContext<'a> {
  pub importer: &'a NormalModule,
  pub importer_meta: &'a LinkingMetadata,
  pub modules: &'a IndexModules,
  pub metas: &'a LinkingMetadataVec,
  pub stmt_infos: &'a IndexStmtInfos,
  pub symbol_db: &'a SymbolRefDb,
  pub order_wrap_state: &'a OrderWrapState,
  /// Strict-gates the forwarder discharge check so flag-off output stays byte-identical to main.
  pub strict_execution_order: bool,
}

/// Resolve direct and forwarded ESM init targets for one static import record.
///
/// An eager (unwrapped) included same-chunk forwarder discharges the init of everything its own
/// finalized statements reach — its `init_*()` calls run at its earlier position in the shared
/// chunk. So a caller can delegate those targets to it. But a static-import statement tree-shaking
/// excluded (a pure barrel's `export * from` hop whose bindings resolve through it) emits nothing
/// there, so the forwarder does *not* discharge the targets that hop alone reaches, and the caller
/// must own them. The delegation is therefore **per obligation**: the caller resolves the wrapped
/// targets it consumes through the forwarder, then subtracts the ones the forwarder actually
/// discharges ([`forwarder_discharged_targets`]), owning only the difference — instead of the
/// module-wide all-or-nothing an earlier boolean forced (one unrelated excluded hop made the caller
/// re-own every binding). Full delegation is still an early-out when the forwarder discharges *all*
/// its hops or off-strict (flag-off parity with main).
pub fn collect_wrapped_esm_init_targets_for_import_record(
  ctx: &WrappedEsmInitTargetContext<'_>,
  rec_idx: ImportRecordIdx,
  wrapper_is_reachable: impl Fn(SymbolRef) -> bool,
  forwarding_module_owns_initialization: impl Fn(ModuleIdx) -> bool,
) -> Vec<ModuleIdx> {
  let mut visited_forwarders = FxHashSet::default();
  collect_esm_init_targets_for_record(
    ctx,
    rec_idx,
    &wrapper_is_reachable,
    &forwarding_module_owns_initialization,
    &mut visited_forwarders,
  )
}

fn collect_esm_init_targets_for_record(
  ctx: &WrappedEsmInitTargetContext<'_>,
  rec_idx: ImportRecordIdx,
  wrapper_is_reachable: &impl Fn(SymbolRef) -> bool,
  forwarding_module_owns_initialization: &impl Fn(ModuleIdx) -> bool,
  visited_forwarders: &mut FxHashSet<ModuleIdx>,
) -> Vec<ModuleIdx> {
  let mut targets = Vec::new();
  let record = &ctx.importer.import_records[rec_idx];
  let Some(importee_idx) = record.resolved_module else { return targets };
  let importee_meta = &ctx.metas[importee_idx];

  // An eager, unwrapped, included forwarder hosted in the importer's own chunk: it runs before the
  // importer in the shared chunk, so its own `init_*()` emission can be delegated to.
  let importee_is_eager_forwarder =
    ctx.order_wrap_state.esm_init_target(importee_idx, importee_meta).is_none()
      && matches!(importee_meta.wrap_kind(), WrapKind::None)
      && importee_meta.is_included
      && forwarding_module_owns_initialization(importee_idx);

  // Full delegation: off-strict keeps main's behavior (the forwarder owns everything); on-strict
  // this early-out fires only when the forwarder discharges *every* one of its hops, in which case
  // the per-obligation subtraction below would remove all targets anyway.
  if importee_is_eager_forwarder
    && (!ctx.strict_execution_order
      || eager_forwarder_discharges_own_hops(ctx, importee_idx, importee_meta))
  {
    return targets;
  }

  if wrapped_esm_target_is_reachable(
    importee_idx,
    importee_meta,
    ctx.order_wrap_state,
    wrapper_is_reachable,
  ) {
    targets.push(importee_idx);
    return targets;
  }

  let mut visited_symbols = FxHashSet::default();
  if record.meta.contains(ImportRecordMeta::IsExportStar) {
    for resolved_export in importee_meta.resolved_exports.values() {
      add_wrapped_esm_init_target_for_symbol(
        ctx,
        resolved_export.symbol_ref,
        wrapper_is_reachable,
        &mut targets,
        &mut visited_symbols,
      );
    }
  } else {
    for named_import in
      ctx.importer.named_imports.values().filter(|item| item.record_idx == rec_idx)
    {
      match &named_import.imported {
        Specifier::Star => {
          for resolved_export in importee_meta.resolved_exports.values() {
            add_wrapped_esm_init_target_for_symbol(
              ctx,
              resolved_export.symbol_ref,
              wrapper_is_reachable,
              &mut targets,
              &mut visited_symbols,
            );
          }
        }
        Specifier::Literal(name) => {
          let symbol_ref = importee_meta
            .resolved_exports
            .get(name)
            .map_or(named_import.imported_as, |resolved_export| resolved_export.symbol_ref);
          add_wrapped_esm_init_target_for_symbol(
            ctx,
            symbol_ref,
            wrapper_is_reachable,
            &mut targets,
            &mut visited_symbols,
          );
        }
      }
    }
  }

  // Strict-mode per-obligation delegation to a *partial* forwarder: reaching here with an eager
  // forwarder means it does not discharge all its hops, so subtract exactly the targets it does
  // discharge and keep the rest.
  if importee_is_eager_forwarder {
    let discharged = forwarder_discharged_targets(
      ctx,
      importee_idx,
      wrapper_is_reachable,
      forwarding_module_owns_initialization,
      visited_forwarders,
    );
    targets.retain(|target| !discharged.contains(target));
  }

  targets
}

fn add_wrapped_esm_init_target_for_symbol(
  ctx: &WrappedEsmInitTargetContext<'_>,
  symbol_ref: SymbolRef,
  wrapper_is_reachable: &impl Fn(SymbolRef) -> bool,
  targets: &mut Vec<ModuleIdx>,
  visited_symbols: &mut FxHashSet<SymbolRef>,
) {
  let canonical_ref = ctx.symbol_db.canonical_ref_resolving_namespace(symbol_ref);
  if !visited_symbols.insert(canonical_ref) {
    return;
  }
  let meta = &ctx.metas[canonical_ref.owner];
  if wrapped_esm_target_is_reachable(
    canonical_ref.owner,
    meta,
    ctx.order_wrap_state,
    wrapper_is_reachable,
  ) {
    targets.push(canonical_ref.owner);
    return;
  }

  let Some(module) = ctx.modules[canonical_ref.owner].as_normal() else {
    return;
  };
  let importer_is_order_wrapped = ctx
    .order_wrap_state
    .esm_init_target(ctx.importer.idx, ctx.importer_meta)
    .is_some_and(|target| matches!(target.origin, EsmInitOrigin::ExecutionOrder));
  if module.namespace_object_ref != canonical_ref || meta.is_included || !importer_is_order_wrapped
  {
    return;
  }

  for resolved_export in meta.resolved_exports.values() {
    add_wrapped_esm_init_target_for_symbol(
      ctx,
      resolved_export.symbol_ref,
      wrapper_is_reachable,
      targets,
      visited_symbols,
    );
  }
}

fn wrapped_esm_target_is_reachable(
  module_idx: ModuleIdx,
  meta: &LinkingMetadata,
  order_wrap_state: &OrderWrapState,
  wrapper_is_reachable: &impl Fn(SymbolRef) -> bool,
) -> bool {
  order_wrap_state
    .esm_init_target(module_idx, meta)
    .is_some_and(|target| wrapper_is_reachable(target.wrapper_ref))
    && meta.is_included
    && !matches!(meta.concatenated_wrapped_module_kind, ConcatenateWrappedModuleKind::Inner)
}

/// Whether an included, unwrapped forwarder discharges *all* its downstream initialization through
/// its own finalized statements — the full-delegation fast path. Its *included* import statements
/// do — the finalizer emits their `init_*()` calls at each statement's position — but a
/// static-import statement that tree-shaking excluded emits nothing there (a pure package barrel's
/// `export * from` hop whose bindings resolve through it is the canonical case). When every
/// static-import statement is included the forwarder owns every hop, so the caller can delegate
/// wholesale; when only some are, the caller delegates per obligation (see
/// [`forwarder_discharged_targets`]) rather than re-owning everything.
///
/// OPEN QUESTION (hypothesis, no repro — do not chase without one): this check consults only the
/// statement *inclusion* bits, while finalization additionally suppresses records marked "nested"
/// (`module_finalizers::mod` transform-or-remove and the `export *` path). If a directly consumed,
/// included hop could also be nested — and therefore emitted nowhere despite counting as
/// discharged here — the caller would wrongly delegate to a silent forwarder. No graph is known to
/// produce a nested *and* directly-consumed-included hop (nesting marks a record a wrapped ancestor
/// walks through, which owns the init instead), so this stays a documented invariant to revisit
/// only if a failing fixture appears.
fn eager_forwarder_discharges_own_hops(
  ctx: &WrappedEsmInitTargetContext<'_>,
  module_idx: ModuleIdx,
  meta: &LinkingMetadata,
) -> bool {
  let Some(module) = ctx.modules[module_idx].as_normal() else {
    return true;
  };
  ctx.stmt_infos[module_idx].iter_enumerated_without_namespace_stmt().all(
    |(stmt_idx, stmt_info)| {
      meta.stmt_info_included.has_bit(stmt_idx)
        || stmt_info
          .import_records
          .iter()
          .all(|rec_idx| module.import_records[*rec_idx].kind != ImportKind::Import)
    },
  )
}

/// The exact set of wrapped-ESM modules a *partial* eager forwarder discharges through its own
/// finalized statements: for each of the forwarder's **included**, non-nested static-import
/// records, the init targets that record's own emission reaches, resolved by the same collector the
/// forwarder itself runs when finalized (so this equals what the forwarder emits, never a superset —
/// subtracting it can only remove a redundant caller-side init, never a needed one).
///
/// A record tree-shaking excluded, or suppressed as a nested walk-through interior, emits nothing at
/// the forwarder and so discharges nothing (the caller must still own those). The forwarder is
/// hosted in the caller's own chunk (the delegation gate requires it), so the caller's
/// `wrapper_is_reachable` / same-chunk predicates apply unchanged to the forwarder's records.
/// `visited_forwarders` breaks same-chunk forwarder cycles by discharging nothing on re-entry
/// (under-approximating — a kept redundant init, never a dropped one).
fn forwarder_discharged_targets(
  ctx: &WrappedEsmInitTargetContext<'_>,
  forwarder_idx: ModuleIdx,
  wrapper_is_reachable: &impl Fn(SymbolRef) -> bool,
  forwarding_module_owns_initialization: &impl Fn(ModuleIdx) -> bool,
  visited_forwarders: &mut FxHashSet<ModuleIdx>,
) -> FxHashSet<ModuleIdx> {
  let mut discharged = FxHashSet::default();
  if !visited_forwarders.insert(forwarder_idx) {
    return discharged;
  }
  let Some(forwarder) = ctx.modules[forwarder_idx].as_normal() else {
    return discharged;
  };
  let forwarder_meta = &ctx.metas[forwarder_idx];
  let forwarder_ctx = WrappedEsmInitTargetContext {
    importer: forwarder,
    importer_meta: forwarder_meta,
    modules: ctx.modules,
    metas: ctx.metas,
    stmt_infos: ctx.stmt_infos,
    symbol_db: ctx.symbol_db,
    order_wrap_state: ctx.order_wrap_state,
    strict_execution_order: ctx.strict_execution_order,
  };
  for (stmt_idx, stmt_info) in
    ctx.stmt_infos[forwarder_idx].iter_enumerated_without_namespace_stmt()
  {
    if !forwarder_meta.stmt_info_included.has_bit(stmt_idx) {
      continue;
    }
    for &rec_idx in &stmt_info.import_records {
      if forwarder.import_records[rec_idx].kind != ImportKind::Import
        || ctx.order_wrap_state.is_nested_reexport_record(forwarder_idx, rec_idx)
      {
        continue;
      }
      discharged.extend(collect_esm_init_targets_for_record(
        &forwarder_ctx,
        rec_idx,
        wrapper_is_reachable,
        forwarding_module_owns_initialization,
        visited_forwarders,
      ));
    }
  }
  discharged
}
