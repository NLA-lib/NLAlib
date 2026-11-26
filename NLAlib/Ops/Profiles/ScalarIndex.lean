/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.Confined

/-!
# Scalar arithmetic with stored pivot indices

The closed signature has scalar arithmetic and dimension literals, with exact comparisons
and nonnegative floor queries. It contains no vector, matrix or sampling operation. Each
contract describes only one primitive; one interpretation realizes them jointly on any word
machine and decoding. The arithmetic accuracy and exact integer range are separate assumptions:
use `ExactModel`, `StdModel` or `MixedModel`, and `IsExactNatLit` for recorded pivot indices.

All operations, queries and structural instructions cost one unit. Span is sequential, scalar
operations use no additional workspace, and storage consists of abstract cells. These choices
assert neither a physical word encoding nor a native BLAS execution time.

## Main results

* `NLAlib.Ops.ScalarIndex.model`: a uniform, confined, charged scalar/index model.
* `NLAlib.Ops.ScalarIndex.laws`: recover all four primitive contract interfaces together.
* `NLAlib.Ops.ScalarIndex.interp_contracts`: joint realization without a run hypothesis.
-/

@[expose] public section

namespace NLAlib.Ops.ScalarIndex

/-- Scalar word arithmetic and evaluated dimension literals, with no higher primitives. -/
abbrev Operation := ScalarOp ⊕ IndexOp

/-- Exact comparisons and the conversion of an actual stored word to a natural index. -/
abbrev Queries := CmpTst ⊕ IdxTst

/-- The scalar and literal functions of the same machine. -/
def functions {K : Type} (M : Machine K) : Operation → BlockFn K
  | .inl o => M.fn o
  | .inr _ => M.indexFn

/-- One reference interpretation jointly implements arithmetic, literals and both query groups.
A negative decoded index fails; comparisons never perform an index conversion. -/
noncomputable def interp {K : Type} (M : Machine K) (dec : K → ℝ) :
    Interp Operation Queries K where
  call := (Interp.ofFns (Tst := Queries) (functions M)).call
  test q _ a m := match q with
    | .inl c => (m.readBlocks a c.lens).map (c.fn dec)
    | .inr _ => none
  index q a m := match q with
    | .inr .toNat => (m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn dec xs.flatten
    | .inl _ => none

/-- All functional and query laws hold on one interpretation, for any scalar machine. -/
theorem interp_contracts {K : Type} (M : Machine K) (dec : K → ℝ) :
    IsScalar M (interp M dec) ∧ IsIndexLit M (interp M dec) ∧
      IsCmp dec (interp M dec) ∧ IsToNat dec (interp M dec) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o
    exact Interp.ofFns_isFn (Tst := Queries) (functions M) .total (.inl o) AnyOperands
  · exact Interp.ofFns_isFn (Tst := Queries) (functions M) .total (.inr .lit) AnyOperands
  · intro c d a m xs h
    change (m.readBlocks a c.lens).map (c.fn dec) = _
    rw [h]
    rfl
  · intro a m xs h
    change ((m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn dec xs.flatten) = _
    rw [h]
    rfl

/-- Declared scalar operand formats; all outputs contain one abstract cell. -/
def signature : Operation → OperandSignature
  | .inl (.lit _) | .inr _ => ⟨[], [.cell]⟩
  | .inl .add | .inl .sub | .inl .mul | .inl .div => ⟨[.cell, .cell], [.cell]⟩
  | .inl .neg | .inl .sqrt | .inl .copy => ⟨[.cell], [.cell]⟩

/-- Unit charges for every primitive, query and structural step, with sequential span and
zero primitive workspace. Caller buffers and scoped allocations retain their actual sizes. -/
def resources : ResourceModel Operation Queries where
  formats := [.cell]
  operation := signature
  testInputs q := match q with
    | .inl c => c.lens.map (fun _ => .cell)
    | .inr _ => []
  indexInputs q := match q with
    | .inl _ => []
    | .inr _ => [.cell]
  workspace _ _ := 0
  queryWorkspace _ _ := 0
  operationWork _ _ := 1
  operationSpan _ _ := 1
  queryWork _ _ := 1
  querySpan _ _ := 1
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le _ _ := le_rfl
  core_span_le _ _ := le_rfl

/-- A jointly realized model of local scalar operations and operand-only stored-index queries.
The same contracts apply at every admitted input; no factorization or successful run is assumed. -/
noncomputable def model {K : Type} [Inhabited K] {r b : ℕ} (P : Problem K r b)
    (M : Machine K) (dec : K → ℝ) : AccessModel Operation Queries P where
  word := default
  operation _ _ o := ((functions M) o).rel.spec AnyOperands
  query _ _ := Dense.queryContract dec
  resources := resources
  realize _ _ _ := by
    refine ⟨interp M dec, ?_, ?_⟩
    · intro o
      exact Interp.ofFns_isFn (Tst := Queries) (functions M) .total o AnyOperands
    · intro q
      rcases q with c | ⟨⟩
      · exact ⟨(interp_contracts M dec).2.2.1 c, fun _ _ => rfl⟩
      · exact ⟨fun _ _ _ => rfl, (interp_contracts M dec).2.2.2⟩

/-- Every admitted interpretation satisfies the same arithmetic, literal, comparison and index
contracts, with no statement about any particular program. -/
theorem laws {K : Type} [Inhabited K] {r b : ℕ} {P : Problem K r b}
    {M : Machine K} {dec : K → ℝ} {d : Fin r → ℕ} {x : P.Input d}
    {I : Interp Operation Queries K} (h : (model P M dec).contracts d x I) :
    IsScalar M I ∧ IsIndexLit M I ∧ IsCmp dec I ∧ IsToNat dec I := by
  refine ⟨fun o => h.1 (.inl o), h.1 (.inr .lit), ?_, ?_⟩
  · intro c ds a m xs hr
    exact (h.2 (.inl c)).1 ds a m xs hr
  · intro a m xs hr
    exact (h.2 (.inr .toNat)).2 a m xs hr

instance confined_model {K : Type} [Inhabited K] {r b : ℕ} (P : Problem K r b)
    (M : Machine K) (dec : K → ℝ) : (model P M dec).Confined :=
  ⟨fun _ _ _ => BlockRel.confined_spec _ _, fun _ _ q => Dense.confined_queryContract dec q⟩

instance uniform_model {K : Type} [Inhabited K] {r b : ℕ} (P : Problem K r b)
    (M : Machine K) (dec : K → ℝ) : (model P M dec).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

instance charged_model {K : Type} [Inhabited K] {r b : ℕ} (P : Problem K r b)
    (M : Machine K) (dec : K → ℝ) : (model P M dec).Charged :=
  ⟨fun _ _ => Nat.one_pos, fun _ _ => Nat.one_pos, fun _ _ => Nat.one_pos⟩

end NLAlib.Ops.ScalarIndex
