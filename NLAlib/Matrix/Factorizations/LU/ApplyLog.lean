/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.VectorSwap
public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# Applying actual stored pivot histories to vectors

Each index is read from its stored history word through the bounded conversion interface.
The existing scalar vector-swap kernel applies the recorded exchanges in order. The result
is exact word permutation, with the history and all other buffers retained.

## Main results

* `NLAlib.LU.applyLog_meets`: applying the actual reported pivot log to a vector.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IdxTst Tst]

/-- Replay actual stored current-position row choices on a vector, in forward order. -/
def applyLog : Routine Op Tst := routine% [n] (H : n, x : n) → (x) {
  for k < n {
    let row ← index (Has.inj IdxTst.toNat) (H[k]) ≤ n - 1;
    run swapVector [n, k, row] (x)
  }
}

variable [Inhabited K]

/-- An active bounded history determines the exact resulting word permutation. The history
is part of the original read inputs, so no unstored permutation oracle reaches the program. -/
def applyLogSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (hs, xs) → (ys) requires
    (∃ p : Fin n → Fin n, (∀ i : Fin n, i ≤ p i) ∧
      ∀ i : Fin n, dec (vec hs i.val) = (p i).val) ensures
    ∃ p : Fin n → Fin n, (∀ i : Fin n, i ≤ p i) ∧
      (∀ i : Fin n, dec (vec hs i.val) = (p i).val) ∧
      ∀ i : Fin n, vec ys i.val = vec xs ((luPivotPermutation p n i).val)

/-- The actual bounded queries and scalar exchanges implement the stored history's word
permutation. No factorization, arithmetic accuracy or successful-run premise is required. -/
theorem applyLog_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hQ : IsToNat dec I) :
    (applyLog (Op := Op) (Tst := Tst)).Meets I (applyLogSpec dec) := by
  routine_intro [n] (H, x) reads (hs, xs)
  obtain ⟨p, hp, hlog⟩ := hpre
  have hstart : m.pos = m.pos ∧ ∃ ys : List K,
      m.store.readBlock x.1 x.2 n = some ys ∧
      ∀ i : Fin n, vec ys i.val = vec xs ((luPivotPermutation p 0 i).val) :=
    ⟨rfl, xs, hxs, fun _ => rfl⟩
  loop_inv (fun _ => Fp.blocks [x] [n])
    (fun k μ => μ.pos = m.pos ∧ ∃ ys : List K,
      μ.store.readBlock x.1 x.2 n = some ys ∧
      ∀ i : Fin n, vec ys i.val = vec xs ((luPivotPermutation p k i).val))
    with k hk m₁ hfr hP
  case round =>
    obtain ⟨hpos, ys, hys, hwords⟩ := hP
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
    rw [luPivotPermutation_succ p k hk]
    rfl
  case exit =>
    rintro m₁ _ ⟨hpos, ys, hys, hwords⟩
    exact ⟨hpos, [ys], Mem.readBlocks_of_cons hys rfl, p, hp, hlog, hwords⟩

omit [Has ScalarOp Op] [Has IdxTst Tst] in
/-- A fixed stored log determines at most one finite index choice at every position. -/
theorem decodedPivotLog_unique {dec : K → ℝ} {n : ℕ} {hs : List K} {p q : Fin n → Fin n}
    (hp : ∀ i : Fin n, dec (vec hs i.val) = (p i).val)
    (hq : ∀ i : Fin n, dec (vec hs i.val) = (q i).val) : p = q := by
  funext i
  apply Fin.ext
  exact_mod_cast (hp i).symm.trans (hq i)

omit [Has ScalarOp Op] [Has IdxTst Tst] in
/-- Read forward replay at the particular finite history supplied by the factorization.
The words of that history, rather than an unstored permutation, identify the result. -/
theorem vec_eq_of_applyLogSpec {dec : K → ℝ} {n : ℕ} {hs xs ys : List K} {τ : Tape K}
    (hpost : (applyLogSpec dec).post [n] τ [hs, xs] [ys]) (p : Fin n → Fin n)
    (hlog : ∀ i : Fin n, dec (vec hs i.val) = (p i).val) :
    ∀ i : Fin n, vec ys i.val = vec xs ((luPivotPermutation p n i).val) := by
  obtain ⟨q, -, hq, hwords⟩ := hpost
  obtain rfl := decodedPivotLog_unique hq hlog
  exact hwords

omit [Inhabited K] in
/-- An empty actual history touches no operand, for arbitrary handles, offsets, aliases and
interpretations, including an empty caller memory and missing arguments. -/
theorem eval_applyLog_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (applyLog (Op := Op) (Tst := Tst)).body (Env.frame [0] args) m = some m := by
  rfl

end NLAlib.LU
