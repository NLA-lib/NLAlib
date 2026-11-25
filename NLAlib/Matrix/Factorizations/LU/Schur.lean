/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PivotSaved
public import NLAlib.Matrix.Factorizations.LU.SchurValues
public import NLAlib.Ops.Catalog.Orth
public import NLAlib.Ops.Catalog.Compare

/-!
# Full saved-pivot Schur elimination as an Ops routine

The original pivot vectors are copied into scoped scratch before any residual write.
The scalar negative reciprocal and the actual column multiply-add routine then update the
whole residual. The word judgment is total for any scalar machine; exact arithmetic gives
Gaussian elimination at a nonzero pivot, and rounded analyses use the same computed words.

## Main results

* `NLAlib.LU.schurStep_meets`: actual stored saved-pivot elimination.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Save both original pivot vectors, form the negative reciprocal, and apply the scalar
rank-one update. All three scratch buffers are released on return. -/
def schurStep : Routine Op Tst := routine% [n, k] (A : n * n) → (A) {
  let c ← alloc n;
  let r ← alloc n;
  let a ← alloc 1;
  run (pivotSaved (Op := Op) (Tst := Tst)) [n, k] (A, c, r);
  call (Has.inj (ScalarOp.lit (-1))) [] () → (a);
  call (Has.inj ScalarOp.div) [] (a, A[k * n + k]) → (a);
  run (rankOne (Op := Op) (Tst := Tst)) [n, n] (a, c, r, A)
}

variable [Inhabited K]

/-- The word result of full saved-pivot elimination, on the actual source block. The pivot
index is bounded; numerical nonbreakdown is a separate property of decoded inputs. -/
def schurStepSpec (M : Machine K) : Routine.Spec K :=
  spec% [n, k] (As) → (Bs) requires k < n ensures
    Bs = (EntryCodec.scalar K).packMatrix n n
      (schurValues M (fun i j => vec As (j * n + i)) k)

omit [Has ScalarOp Op] in
/-- The saved original pivot vectors specialize the generic rank-one words to Schur words. -/
theorem rankOne_savedWords (M : Machine K) (As : List K) (n k : ℕ) :
    (EntryCodec.scalar K).packMatrix n n
      (rankOneValues M (M.div (M.lit (-1)) (vec As (k * n + k)))
        (vec (pivotColumnWords As n k)) (vec (pivotRowWords As n k))
        (fun i j => vec As (j * n + i))) =
      (EntryCodec.scalar K).packMatrix n n
        (schurValues M (fun i j => vec As (j * n + i)) k) := by
  rw [← (EntryCodec.scalar K).packFinMatrix_eq_packMatrix,
    ← (EntryCodec.scalar K).packFinMatrix_eq_packMatrix]
  congr 1
  funext i j
  simp only [Matrix.of_apply, rankOneValues, schurValues, pivotColumnWords, pivotRowWords,
    vec_map_range _ i.isLt, vec_map_range _ j.isLt]

/-- The full scalar routine writes the stated Schur words and retains every other buffer,
the original buffer shapes and the tape position. Its proof derives the actual run from
scalar contracts, without assuming it succeeds. -/
theorem schurStep_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (schurStep (Op := Op) (Tst := Tst)).Meets I (schurStepSpec M) := by
  routine_intro [n, k] (A) reads (As)
  change Writes .total I τ _ (Env.frame [n, k] [A, A]) (Fp.blocks [A] [n * n]) _ m
  alloc as c r a
  have hAc : A.1 ≠ c := by change A.1 ≠ m.store.length + 0; omega
  have hAr : A.1 ≠ r := by change A.1 ≠ m.store.length + 1; omega
  have hAa : A.1 ≠ a := by change A.1 ≠ m.store.length + 2; omega
  have hcr : c ≠ r := by change m.store.length + 0 ≠ m.store.length + 1; omega
  have hca : c ≠ a := by change m.store.length + 0 ≠ m.store.length + 2; omega
  have hra : r ≠ a := by change m.store.length + 1 ≠ m.store.length + 2; omega
  have hAs₀ := Store.Below.readBlock_of hbelow_c hl hAs
  call (pivotSaved_meets hI) [n, k] (A, (c, 0), (r, 0)) (pre := hpre)
    as m₁ hfr₁ hpos₁ (cs, rs) hsaved
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change A.1 < s_c.length ∧ m.store.length < s_c.length ∧ m.store.length + 1 < s_c.length
    simp only [List.length_cons, List.length_nil] at hlen_c
    exact ⟨by omega, by omega, by omega⟩
  case' hroom =>
    change (0 + n ≤ s_c.len c) ∧ (0 + n ≤ s_c.len r) ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hc.ge,
      by simpa only [Nat.zero_add] using hr_1.ge, trivial⟩
  obtain ⟨rfl, rfl⟩ := hsaved
  have hAs₁ : m₁.store.readBlock A.1 A.2 (n * n) = some As := by keep
  step (hI (.lit (-1))) as m₂ hfr₂ ⟨hpos₂, v, hv, rfl⟩
  change Store.EqOff (Store.inBlock a 0 1) m₁.store m₂.store at hfr₂
  have hcs₂ : m₂.store.readBlock c 0 n = some (pivotColumnWords As n k) := by keep
  have hrs₂ : m₂.store.readBlock r 0 n = some (pivotRowWords As n k) := by keep
  have hAs₂ : m₂.store.readBlock A.1 A.2 (n * n) = some As := by keep
  have hpivot := Store.get_of_readBlock hAs₂ (Idx.add_lt_mul hpre hpre) default
  have hpivot' : m₂.store.get A.1 (A.2 + k * n + k) = some (vec As (k * n + k)) := by
    simpa only [Nat.add_assoc] using hpivot
  step (hI .div) as m₃ hfr₃ ⟨hpos₃, q, hq, rfl⟩
  change Store.EqOff (Store.inBlock a 0 1) m₂.store m₃.store at hfr₃
  have hcs₃ : m₃.store.readBlock c 0 n = some (pivotColumnWords As n k) := by keep
  have hrs₃ : m₃.store.readBlock r 0 n = some (pivotRowWords As n k) := by keep
  have hAs₃ : m₃.store.readBlock A.1 A.2 (n * n) = some As := by keep
  call (rankOne_meets hI) [n, n] ((a, 0), (c, 0), (r, 0), A)
    as m₄ hfr₄ hpos₄ (Bs) hpost
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change m.store.length + 2 < m₃.store.length ∧ m.store.length < m₃.store.length ∧
      m.store.length + 1 < m₃.store.length ∧ A.1 < m₃.store.length
    simp only [List.length_cons, List.length_nil] at hlen_c
    exact ⟨by omega, by omega, by omega, by omega⟩
  intro s₂ hs₂ hB₂
  refine ⟨?_, [Bs], Mem.readBlocks_of_cons ?_ rfl, ?_⟩
  · change m₄.pos = m.pos + 0
    omega
  · exact Store.Below.readBlock_of hB₂ hl hBs
  · rw [hpost]
    exact rankOne_savedWords M As n k

omit [Has ScalarOp Op] in
/-- The word postcondition gives exact Gaussian elimination under exact decoded arithmetic
at a nonzero pivot. This reads the numerical conclusion off the generic word judgment. -/
theorem schurStepSpec_decode {M : Machine K} {dec : K → ℝ} (hM : ExactModel dec M)
    {N : ℕ} (k : Fin N) {As Bs : List K} {τ : Tape K}
    (hpost : (schurStepSpec M).post [N, k.val] τ [As] [Bs])
    (hk : decodeMatrix dec N N As k k ≠ 0) :
    decodeMatrix dec N N Bs = eliminationStep (decodeMatrix dec N N As) k := by
  obtain rfl : Bs = (EntryCodec.scalar K).packMatrix N N
      (schurValues M (fun i j => vec As (j * N + i)) k) := hpost
  have he := schurValues_eq_eliminationStep hM (fun i j => vec As (j * N + i)) k
    (by simpa only [decodeMatrix_apply] using hk)
  rw [decodeMatrix, EntryCodec.matrix_packMatrix]
  have hdec : decodeMatrix dec N N As = fun i j : Fin N => dec (vec As (j * N + i)) := by
    ext i j
    exact decodeMatrix_apply dec N N As i j
  rw [hdec]
  exact (show _ = (fun i j : Fin N => dec
    (schurValues M (fun i j => vec As (j * N + i)) k i j)) from by ext i j; rfl).trans he

section Guarded

variable [Has CmpTst Tst]

/-- A decoded zero pivot leaves the residual untouched and executes no division. The
nonzero branch uses the same saved-pivot scalar update as ordinary elimination. -/
def schurStepTotal : Routine Op Tst := routine% [n, k] (A : n * n) → (A) {
  if (Has.inj CmpTst.isZero) [] (A[k * n + k]) {
  } else {
    run (schurStep (Op := Op) (Tst := Tst)) [n, k] (A)
  }
}

/-- The zero-pivot branch preserves the original word block; otherwise the ordinary
saved-pivot word formula is returned. -/
def schurStepTotalSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n, k] (As) → (Bs) requires k < n ensures
    (dec (vec As (k * n + k)) = 0 → Bs = As) ∧
      (dec (vec As (k * n + k)) ≠ 0 → Bs = (EntryCodec.scalar K).packMatrix n n
        (schurValues M (fun i j => vec As (j * n + i)) k))

/-- The zero-safe scalar routine meets its word specification under exact decoded zero
tests. No nonzero-pivot or successful-execution premise is needed. -/
theorem schurStepTotal_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) :
    (schurStepTotal (Op := Op) (Tst := Tst)).Meets I (schurStepTotalSpec M dec) := by
  routine_intro [n, k] (A) reads (As)
  have hpivot := Store.get_of_readBlock hAs (Idx.add_lt_mul hpre hpre) default
  have hpivot' : m.store.get A.1 (A.2 + k * n + k) = some (vec As (k * n + k)) := by
    simpa only [Nat.add_assoc] using hpivot
  refine writes_ite rfl rfl (hcmp.test_isZero hpivot') ?_
  by_cases hz : dec (vec As (k * n + k)) = 0
  · simp only [hz, decide_true, ite_true]
    change Wp .total I τ .skip _ _ m
    apply wp_skip
    refine ⟨Store.EqOff.refl _ _, rfl, [As], Mem.readBlocks_of_cons hAs rfl, ?_⟩
    exact ⟨fun _ => rfl, fun h => (h hz).elim⟩
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
    call (schurStep_meets hI) [n, k] (A) (pre := hpre)
      as m₁ hfr₁ hpos₁ (Bs) hpost
    routine_exit
    exact ⟨fun h => (hz h).elim, fun _ => hpost⟩

omit [Has ScalarOp Op] [Has CmpTst Tst] in
/-- The guarded word postcondition gives the mathematical elimination step on every exact
input, including a zero pivot where both programs and mathematics retain the residual. -/
theorem schurStepTotalSpec_decode {M : Machine K} {dec : K → ℝ} (hM : ExactModel dec M)
    {N : ℕ} (k : Fin N) {As Bs : List K} {τ : Tape K}
    (hpost : (schurStepTotalSpec M dec).post [N, k.val] τ [As] [Bs]) :
    decodeMatrix dec N N Bs = eliminationStep (decodeMatrix dec N N As) k := by
  have hp : (dec (vec As (k * N + k)) = 0 → Bs = As) ∧
      (dec (vec As (k * N + k)) ≠ 0 → Bs = (EntryCodec.scalar K).packMatrix N N
        (schurValues M (fun i j => vec As (j * N + i)) k)) := hpost
  by_cases hz : dec (vec As (k * N + k)) = 0
  · obtain rfl := hp.1 hz
    exact (eliminationStep_eq_self_of_apply_self_eq_zero
      (by simpa only [decodeMatrix_apply] using hz)).symm
  · exact schurStepSpec_decode (τ := τ) hM k (hp.2 hz)
      (by simpa only [decodeMatrix_apply] using hz)

end Guarded

end NLAlib.LU
