/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.WeightedCost

/-!
# Finite envelopes for dimension-dependent operation weights

The envelope ranges over lists of bounded length and bounded natural entries, including the
empty dimension list. It converts a supplied primitive cost function into a finite maximum;
no global constant ceiling on costs at arbitrarily large dimensions is required.

## Main results

* `NLAlib.Ops.WorkEnvelope`: weights bounded on a finite dimension domain.
* `NLAlib.Ops.dimensionLists`: finite dimension lists within explicit size limits.
* `NLAlib.Ops.le_weightEnvelope`: every admitted dimension list is included.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst : Type}

/-- A finite-domain ceiling on operation and query weights, using at most `arity` dimensions
whose values are at most `extent`. No primitive is silently assigned zero weight. -/
def WorkEnvelope (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    (arity extent weight : ℕ) : Prop :=
  (∀ o ds, ds.length ≤ arity → (∀ x ∈ ds, x ≤ extent) → op o ds ≤ weight) ∧
  (∀ q ds, ds.length ≤ arity → (∀ x ∈ ds, x ≤ extent) → query q ds ≤ weight)

/-- Restricting the arity and index range preserves a weight ceiling. -/
theorem WorkEnvelope.mono {op : Op → List ℕ → ℕ} {query : Tst → List ℕ → ℕ}
    {a b t u w : ℕ} (h : WorkEnvelope op query b u w) (ha : a ≤ b) (ht : t ≤ u) :
    WorkEnvelope op query a t w := by
  constructor
  · intro o ds hl hv
    exact h.1 o ds (hl.trans ha) (fun x hx => (hv x hx).trans ht)
  · intro q ds hl hv
    exact h.2 q ds (hl.trans ha) (fun x hx => (hv x hx).trans ht)


/-- All dimension lists with at most `arity` entries, each at most `extent`. -/
def dimensionLists (extent : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | a + 1 => insert [] ((Finset.range (extent + 1)).biUnion fun n =>
      (dimensionLists extent a).image (n :: ·))

/-- A list lies in the finite dimension domain exactly when its length and entries fit. -/
theorem mem_dimensionLists {extent arity : ℕ} {ds : List ℕ} :
    ds ∈ dimensionLists extent arity ↔ ds.length ≤ arity ∧ ∀ x ∈ ds, x ≤ extent := by
  induction arity generalizing ds with
  | zero => cases ds <;> simp [dimensionLists]
  | succ a ih =>
    cases ds with
    | nil => simp [dimensionLists]
    | cons d ds =>
      simp only [dimensionLists, Finset.mem_insert, reduceCtorEq,
        Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, List.cons.injEq,
        false_or, List.length_cons, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨n, hn, tail, ht, rfl, rfl⟩
        exact ⟨by have := (ih.mp ht).1; omega, by omega, (ih.mp ht).2⟩
      · rintro ⟨hl, hd, ht⟩
        exact ⟨d, by omega, ds, ih.mpr ⟨by omega, ht⟩, rfl, rfl⟩

/-- The largest supplied weight on a finite, explicitly bounded dimension domain. -/
def weightEnvelope (weight : List ℕ → ℕ) (arity extent : ℕ) : ℕ :=
  (dimensionLists extent arity).sup weight

/-- A primitive cost at any admitted shape is below the explicit finite envelope. -/
theorem le_weightEnvelope (weight : List ℕ → ℕ) {arity extent : ℕ} {ds : List ℕ}
    (hl : ds.length ≤ arity) (hx : ∀ x ∈ ds, x ≤ extent) :
    weight ds ≤ weightEnvelope weight arity extent :=
  Finset.le_sup (mem_dimensionLists.mpr ⟨hl, hx⟩)

end NLAlib.Ops
