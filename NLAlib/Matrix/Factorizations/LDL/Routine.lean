/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LDL
public import NLAlib.Matrix.Factorizations.LU.Routine
public import NLAlib.Ops.Blas.DiagonalCopy

/-!
# Stored Hermitian LDL factorization

The actual scalar Gaussian routine computes its canonical lower and upper factors, with the
upper factor in scoped scratch. The ordinary diagonal-copy loop then materializes the pivot
vector. Hermitian symmetry gives the LDL Gram identity from these actual outputs. The input
condition permits indefinite Hermitian matrices with nonzero canonical pivots.

## Main results

* `NLAlib.LDL.factor`: the actual scalar factor and pivot-vector computation.
* `NLAlib.LDL.factor_meets`: its exact canonical LDL guarantee, including order zero.
-/

@[expose] public section

namespace NLAlib.LDL

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Compute the unit lower factor and diagonal pivots, releasing the temporary upper factor. -/
def factor : Routine Op Tst := routine% [n] (A : n * n) → (L : n * n, d : n) {
  ifPos n {
    let U ← alloc (n * n);
    run LU.factor [n] (A, L, U);
    run copyDiagonal [n, 0, n] (U, d)
  }
}

/-- At order zero the raw scalar body reads no operands and leaves the complete memory
unchanged, for arbitrary handles, offsets, aliases and even an empty caller store. -/
theorem eval_factor_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (factor (Op := Op) (Tst := Tst)).body (Env.frame [0] args) m = some m := by
  rfl

variable [Inhabited K]

/-- The actual outputs are canonical lower entries and Gaussian diagonal pivots, satisfying
the Hermitian LDL identity. Every canonical pivot is nonzero; this is vacuous at order zero. -/
def factorSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (as) → (ls, ds) requires
    (decodeMatrix dec n n as).IsHermitian ∧
      (∀ i : Fin n, gaussState (decodeMatrix dec n n as) i.val i i ≠ 0) ensures
    decodeMatrix dec n n ls = luLower (decodeMatrix dec n n as) ∧
      (∀ i : Fin n, dec (vec ds i.val) = gaussState (decodeMatrix dec n n as) i.val i i) ∧
      IsLDL (decodeMatrix dec n n as) (decodeMatrix dec n n ls)
        (fun i : Fin n => dec (vec ds i.val))

/-- Exact local arithmetic and the input's nonzero pivots imply actual full success and the
LDL guarantee. Only the two declared output blocks can change; scratch and tape are restored. -/
theorem factor_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) :
    (factor (Op := Op) (Tst := Tst)).Meets I (factorSpec dec) := by
  routine_intro [n] (A, L, d) reads (as)
  change Writes .total I τ _ (Env.frame [n] [A, L, d])
    (Fp.blocks [L, d] [n * n, n]) _ m
  obtain ⟨hherm, hpivot⟩ := hpre
  obtain ⟨hlA, hlL, hld⟩ := hl
  obtain ⟨hLroom, hdroom⟩ := hroom
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    alloc as U
    have hUeq : U = m.store.length := by
      change m.store.length + 0 = m.store.length
      exact Nat.add_zero _
    have hULive : U < s_U.length := by
      rw [hUeq]
      simp only [List.length_singleton] at hlen_U
      omega
    have hUA : U ≠ A.1 := by rw [hUeq]; omega
    have hUL : U ≠ L.1 := by rw [hUeq]; omega
    have hUd : U ≠ d.1 := by rw [hUeq]; omega
    call (LU.factor_meets hI hcmp hM) [n] (A, L, (U, 0)) (pre := hpivot)
      as m₁ hfr₁ hpos₁ (ls, us) hfactor
    case' hroom =>
      change (L.2 + n * n ≤ s_U.len L.1) ∧ (0 + n * n ≤ s_U.len U) ∧ True
      refine ⟨?_, ?_, trivial⟩
      · rw [(hbelow_U L.1 hlL).1]
        exact hLroom
      · simpa only [Nat.zero_add, U] using hU.ge
    obtain ⟨hlo, hup⟩ := hfactor
    call (copyDiagonal_meets hI) [n, 0, n] ((U, 0), d) (pre := by change 0 + n ≤ n; omega)
      as m₂ hfr₂ hpos₂ (ds) hdiag
    have hls₂ : m₂.store.readBlock L.1 L.2 (n * n) = some ls := by keep
    have hwords : ds = (List.range n).map fun i => vec us (i * n + i) := by
      change ds = (List.range n).map (fun i => vec us ((0 + i) * n + (0 + i))) at hdiag
      simpa only [Nat.zero_add] using hdiag
    have hd : ∀ i : Fin n, dec (vec ds i.val) = gaussState (decodeMatrix dec n n as) i.val i i := by
      intro i
      rw [hwords]
      simp only [vec, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range i.isLt, Option.map_some, Option.getD_some]
      have hv : decodeMatrix dec n n us i i =
          gaussState (decodeMatrix dec n n as) i.val i i := by
        rw [hup, luUpper_apply_self]
      simpa only [decodeMatrix_apply, vec, List.getD_eq_getElem?_getD] using hv
    intro s₂ hs₂ hB
    refine ⟨by simpa only [Nat.add_zero] using hpos₂.trans hpos₁, [ls, ds],
      Mem.readBlocks_of_cons ?_ (Mem.readBlocks_of_cons ?_ rfl),
      hlo, hd, ?_⟩
    · exact Store.Below.readBlock_of hB hlL hls₂
    · exact Store.Below.readBlock_of hB hld hds
    · rw [hlo, funext hd]
      exact hherm.isLDL_luLower hpivot
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    have hnum : decodeMatrix dec 0 0 [] = luLower (decodeMatrix dec 0 0 as) := by
      ext i j
      exact Fin.elim0 i
    have hd : ∀ i : Fin 0, dec (vec ([] : List K) i.val) =
        gaussState (decodeMatrix dec 0 0 as) i.val i i := fun i => Fin.elim0 i
    refine ⟨rfl, [[], []], Mem.readBlocks_of_cons rfl (Mem.readBlocks_of_cons rfl rfl),
      hnum, hd, ?_⟩
    rw [hnum, funext hd]
    exact hherm.isLDL_luLower hpivot

end NLAlib.LDL
