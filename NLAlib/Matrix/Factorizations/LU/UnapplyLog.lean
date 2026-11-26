/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ApplyLog

/-!
# Undoing an actual stored pivot history

Bounded queries read the same actual current-position choices in reverse order. Scalar
vector exchanges undo their forward composition exactly as words. Complete-pivot solves use
this tree to restore original column coordinates after solving through the stored factors.

## Main results

* `NLAlib.LU.unapplyLog_meets`: actual inverse pivot-log permutation of a stored vector.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IdxTst Tst]

/-- Read actual stored choices in reverse order and undo their vector exchanges. -/
def unapplyLog : Routine Op Tst := routine% [n] (H : n, x : n) → (x) {
  for i < n {
    let row ← index (Has.inj IdxTst.toNat) (H[n - 1 - i]) ≤ n - 1;
    run swapVector [n, n - 1 - i, row] (x)
  }
}

variable [Inhabited K]

/-- The actual bounded history determines the inverse exact word permutation. -/
def unapplyLogSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (hs, xs) → (ys) requires
    (∃ p : Fin n → Fin n, (∀ i : Fin n, i ≤ p i) ∧
      ∀ i : Fin n, dec (vec hs i.val) = (p i).val) ensures
    ∃ p : Fin n → Fin n, (∀ i : Fin n, i ≤ p i) ∧
      (∀ i : Fin n, dec (vec hs i.val) = (p i).val) ∧
      ∀ i : Fin n, vec ys i.val = vec xs (((luPivotPermutation p n).symm i).val)

/-- The actual bounded queries and copy-only exchanges undo the reported history. The
original log is retained, no numerical accuracy law is needed, and no run is assumed. -/
theorem unapplyLog_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hQ : IsToNat dec I) :
    (unapplyLog (Op := Op) (Tst := Tst)).Meets I (unapplyLogSpec dec) := by
  routine_intro [n] (H, x) reads (hs, xs)
  obtain ⟨p, hp, hlog⟩ := hpre
  have hstart : m.pos = m.pos ∧ ∃ ys : List K,
      m.store.readBlock x.1 x.2 n = some ys ∧ ∀ i : Fin n,
      vec ys i.val =
        vec xs (((luPivotPermutation p n).symm (luPivotPermutation p (n - 0) i)).val) :=
    ⟨rfl, xs, hxs, fun i => by simp only [Nat.sub_zero, Equiv.symm_apply_apply]⟩
  loop_inv (fun _ => Fp.blocks [x] [n])
    (fun t μ => μ.pos = m.pos ∧ ∃ ys : List K,
      μ.store.readBlock x.1 x.2 n = some ys ∧ ∀ i : Fin n,
      vec ys i.val =
        vec xs (((luPivotPermutation p n).symm (luPivotPermutation p (n - t) i)).val))
    with t ht m₁ hfr hP
  case round =>
    obtain ⟨hpos, ys, hys, hwords⟩ := hP
    let k := n - 1 - t
    have hk : k < n := by dsimp only [k]; omega
    have hhs₁ : m₁.store.readBlock H.1 H.2 n = some hs := by keep
    have hword := Store.get_of_readBlock hhs₁ hk default
    have hdecode := hlog ⟨k, hk⟩
    refine writes_bindIdx_of_decode_nat hQ rfl rfl hword hdecode
      (by have := (p ⟨k, hk⟩).isLt; omega) ?_
    call (swapVector_meets hI) [n, k, (p ⟨k, hk⟩).val] (x)
      (pre := ⟨hp ⟨k, hk⟩, (p ⟨k, hk⟩).isLt⟩)
      as m₂ hfr₂ hpos₂ (zs) hswap
    refine ⟨hpos₂.trans hpos, zs, hzs, ?_⟩
    intro i
    have hs := swapVectorSpec_apply (τ := τ.shift m₁.pos) ⟨k, hk⟩ (p ⟨k, hk⟩) hswap i
    rw [hs, hwords]
    have hbefore : n - t = k + 1 := by dsimp only [k]; omega
    have hafter : n - (t + 1) = k := by dsimp only [k]; omega
    rw [hbefore, luPivotPermutation_succ p k hk, hafter]
    simp only [Equiv.trans_apply, Equiv.swap_apply_self]
  case exit =>
    rintro m₁ _ ⟨hpos, ys, hys, hwords⟩
    refine ⟨hpos, [ys], Mem.readBlocks_of_cons hys rfl, p, hp, hlog, ?_⟩
    simpa only [Nat.sub_self, luPivotPermutation_zero, Equiv.refl_apply] using hwords

omit [Has ScalarOp Op] [Has IdxTst Tst] in
/-- Read reverse replay at the actual finite history supplied by the factorization. -/
theorem vec_eq_of_unapplyLogSpec {dec : K → ℝ} {n : ℕ} {hs xs ys : List K} {τ : Tape K}
    (hpost : (unapplyLogSpec dec).post [n] τ [hs, xs] [ys]) (p : Fin n → Fin n)
    (hlog : ∀ i : Fin n, dec (vec hs i.val) = (p i).val) :
    ∀ i : Fin n, vec ys i.val = vec xs (((luPivotPermutation p n).symm i).val) := by
  obtain ⟨q, -, hq, hwords⟩ := hpost
  obtain rfl := decodedPivotLog_unique hq hlog
  exact hwords

omit [Inhabited K] in
/-- An empty actual history touches no operand, for arbitrary handles, offsets, aliases and
interpretations, including an empty caller memory and missing arguments. -/
theorem eval_unapplyLog_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (unapplyLog (Op := Op) (Tst := Tst)).body (Env.frame [0] args) m = some m := by
  rfl

end NLAlib.LU
