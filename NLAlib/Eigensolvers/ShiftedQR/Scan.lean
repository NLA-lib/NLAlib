/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Storage
public import NLAlib.Ops.Blas.NormSq
public import NLAlib.Ops.Logic.IndexLiteral
public import NLAlib.Matrix.QRIteration.ShiftSearch

/-!
# Scalar scan for a small subdiagonal entry

The scan forms each squared modulus with two scalar multiplications and an addition, compares
it with the supplied squared threshold, and writes a flag and the last qualifying index. The
five-word output view contains three arithmetic temporaries, the flag, and the index.

## Main results

* `NLAlib.ShiftedQR.scan`: the computable scalar traversal.
* `NLAlib.ShiftedQR.scanPrefix`: its exact mathematical last-index specification.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- Squared modulus at one subdiagonal position, clamped outside the finite matrix domain.
The scan visits only positions where the clamping has no effect. -/
def subdiagonalSq {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : ℕ) : ℝ :=
  let z := H ⟨min (i + 1) n, Nat.lt_succ_of_le (min_le_right _ _)⟩
    ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩
  z.re ^ 2 + z.im ^ 2

open Classical in
/-- The last qualifying subdiagonal index among the first `k` visits. -/
noncomputable def scanPrefix {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (threshold : ℝ) : ℕ → Option ℕ
  | 0 => none
  | k + 1 => if subdiagonalSq H k ≤ threshold then some k else scanPrefix H threshold k

/-- A scan's exact stored flag and index; the index is zero when no entry qualifies. -/
def ScanHolds {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (threshold : ℝ)
    (k : ℕ) (r : ℕ × ℕ) (st : Store ℝ) : Prop :=
  st.get r.1 (r.2 + 3) = some (if (scanPrefix H threshold k).isSome then 1 else 0) ∧
  st.get r.1 (r.2 + 4) = some ((scanPrefix H threshold k).getD 0 : ℝ)

/-- A returned index was visited and met the exact squared-threshold comparison. -/
theorem scanPrefix_some {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (threshold : ℝ) (k i : ℕ) (hi : scanPrefix H threshold k = some i) :
    i < k ∧ subdiagonalSq H i ≤ threshold := by
  classical
  induction k with
  | zero => simp only [scanPrefix, reduceCtorEq] at hi
  | succ k ih =>
    by_cases hs : subdiagonalSq H k ≤ threshold
    · simp only [scanPrefix, if_pos hs, Option.some.injEq] at hi
      subst i
      exact ⟨Nat.lt_succ_self _, hs⟩
    · rw [scanPrefix, if_neg hs] at hi
      exact ⟨(ih hi).1.trans (Nat.lt_succ_self _), (ih hi).2⟩

/-- The prefix flag is set exactly when at least one visited squared modulus is small. -/
theorem scanPrefix_isSome_iff {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (threshold : ℝ) (k : ℕ) :
    (scanPrefix H threshold k).isSome = true ↔
      ∃ i < k, subdiagonalSq H i ≤ threshold := by
  classical
  induction k with
  | zero => simp [scanPrefix]
  | succ k ih =>
    by_cases hs : subdiagonalSq H k ≤ threshold
    · simp only [scanPrefix, if_pos hs, Option.isSome_some, true_iff]
      exact ⟨k, Nat.lt_succ_self _, hs⟩
    · rw [scanPrefix, if_neg hs, ih]
      constructor
      · rintro ⟨i, hi, hsmall⟩
        exact ⟨i, hi.trans (Nat.lt_succ_self _), hsmall⟩
      · rintro ⟨i, hi, hsmall⟩
        have hne : i ≠ k := fun he => hs (he ▸ hsmall)
        exact ⟨i, by omega, hsmall⟩

/-- On a valid subdiagonal position the scalar squared-parts formula is the squared modulus. -/
theorem subdiagonalSq_fin {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin n) : subdiagonalSq H i = ‖H i.succ i.castSucc‖ ^ 2 := by
  have hi : (i : ℕ) ≤ n := by omega
  have his : (i : ℕ) + 1 ≤ n := by omega
  simp only [subdiagonalSq, min_eq_left hi, min_eq_left his]
  have hr : (⟨(i : ℕ) + 1, Nat.lt_succ_of_le his⟩ : Fin (n + 1)) = i.succ := by
    apply Fin.ext
    simp
  have hc : (⟨(i : ℕ), Nat.lt_succ_of_le hi⟩ : Fin (n + 1)) = i.castSucc := by
    apply Fin.ext
    rfl
  rw [hr, hc, Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two]

/-- For a nonnegative absolute threshold, the full prefix flag is precisely decoupling. -/
theorem scanPrefix_isSome_iff_isDecoupledAbs {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) {τ : ℝ} (hτ : 0 ≤ τ) :
    (scanPrefix H (τ ^ 2) n).isSome = true ↔ IsDecoupledAbs τ H := by
  rw [scanPrefix_isSome_iff, IsDecoupledAbs]
  constructor
  · rintro ⟨i, hi, hs⟩
    refine ⟨⟨i, hi⟩, (sq_le_sq₀ (norm_nonneg _) hτ).mp ?_⟩
    simpa only [← subdiagonalSq_fin H ⟨i, hi⟩] using hs
  · rintro ⟨i, hi⟩
    exact ⟨i, i.isLt, by rw [subdiagonalSq_fin]; exact (sq_le_sq₀ (norm_nonneg _) hτ).mpr hi⟩

/-- The actual stored flag equals one exactly when the block is decoupled. -/
theorem ScanHolds.flag_iff {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {τ : ℝ} {r : ℕ × ℕ} {st : Store ℝ} (h : ScanHolds H (τ ^ 2) n r st) (hτ : 0 ≤ τ) :
    st.get r.1 (r.2 + 3) = some 1 ↔ IsDecoupledAbs τ H := by
  rw [h.1]
  by_cases hs : (scanPrefix H (τ ^ 2) n).isSome = true
  · simp only [hs, if_true, true_iff]
    exact (scanPrefix_isSome_iff_isDecoupledAbs H hτ).mp hs
  · have hnot := mt (scanPrefix_isSome_iff_isDecoupledAbs H hτ).mpr hs
    simp [hs, hnot]

/-- When the scan finds decoupling, its actual stored index identifies a small entry. -/
theorem ScanHolds.index_of_isDecoupledAbs {n : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ : ℝ} {r : ℕ × ℕ} {st : Store ℝ}
    (h : ScanHolds H (τ ^ 2) n r st) (hτ : 0 ≤ τ) (hdec : IsDecoupledAbs τ H) :
    ∃ i : Fin n, st.get r.1 (r.2 + 4) = some (i : ℝ) ∧ ‖H i.succ i.castSucc‖ ≤ τ := by
  have hs := (scanPrefix_isSome_iff_isDecoupledAbs H hτ).mpr hdec
  cases he : scanPrefix H (τ ^ 2) n with
  | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hs
  | some i =>
    obtain ⟨hi, hsmall⟩ := scanPrefix_some H (τ ^ 2) n i he
    refine ⟨⟨i, hi⟩, by simpa only [he, Option.getD_some] using h.2, ?_⟩
    apply (sq_le_sq₀ (norm_nonneg _) hτ).mp
    simpa only [← subdiagonalSq_fin H ⟨i, hi⟩] using hsmall

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- One scan visit computes an actual squared modulus and records its index when small. -/
def scanRound : Impl Op Tst := opsImpl% [N, i] (A, threshold) → (R) {
  run (PairScalar.normSq (Op := Op) (Tst := Tst)).body []
    (A[2 * (i * N + i + 1)], R);
  if (Has.inj CmpTst.le) [] (R[2], threshold) {
    call (Has.inj IndexOp.lit) [1] () → (R[3]);
    call (Has.inj IndexOp.lit) [i] () → (R[4])
  } else { skip }
}

/-- Inspect every subdiagonal entry, starting from a supplied flag/index state. -/
def scanLoop : Impl Op Tst := opsImpl% [N] (A, threshold) → (R) {
  for i < N - 1 {
    run (scanRound (Op := Op) (Tst := Tst)).body [N, i] (A, threshold, R)
  }
}

/-- Initialize flag/index and inspect every actual subdiagonal entry. -/
def scan : Impl Op Tst := opsImpl% [N] (A, threshold) → (R) {
  call (Has.inj IndexOp.lit) [0] () → (R[3]);
  call (Has.inj IndexOp.lit) [0] () → (R[4]);
  run (scanLoop (Op := Op) (Tst := Tst)).body [N] (A, threshold, R)
}

/-- One visit updates exactly the last-index specification using its actual scalar comparison.
The matrix and threshold have disjoint views from the five arithmetic/flag/index words. -/
theorem scanRound_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {a t r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {threshold : ℝ}
    (hk : k < n) (hH : HoldsMatrix a H m.store)
    (ht : m.store.get t.1 t.2 = some threshold) (hstate : ScanHolds H threshold k r m.store)
    (hl : m.Live [a, t, r]) (hroom : r.2 + 5 ≤ m.store.len r.1)
    (hA : Fp.Disj (Store.inBlock r.1 r.2 5)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hT : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock t.1 t.2 1)) :
    Writes .total I τ (scanRound (Op := Op) (Tst := Tst)).body
      (Env.frame [n + 1, k] [a, t, r]) (Store.inBlock r.1 r.2 5)
      (fun m' => m'.pos = m.pos ∧ ScanHolds H threshold (k + 1) r m'.store) m := by
  classical
  let z := H ⟨k + 1, by omega⟩ ⟨k, by omega⟩
  have hx := hH.get_re ⟨k + 1, by omega⟩ ⟨k, by omega⟩
  have hy := hH.get_im ⟨k + 1, by omega⟩ ⟨k, by omega⟩
  have hidx := Idx.add_lt_mul (show k < n + 1 by omega) (show k + 1 < n + 1 by omega)
  have hlocal : Fp.Disj (Store.inBlock a.1 (a.2 + 2 * (k * (n + 1) + k + 1)) 2)
      (Store.inBlock r.1 r.2 3) := hA.symm.mono (by fp_sub) (by fp_sub)
  have hsq : subdiagonalSq H k = z.re ^ 2 + z.im ^ 2 := by
    simp [subdiagonalSq, z, min_eq_left (show k + 1 ≤ n by omega),
      min_eq_left (show k ≤ n by omega)]
  have hw := PairScalar.normSq_writes (τ := τ) hS hE
    (x := (a.1, a.2 + 2 * (k * (n + 1) + k + 1))) (t := r)
    (by simpa [Nat.add_assoc] using hx) (by simpa [Nat.add_assoc] using hy)
    (by omega) hlocal
  unfold scanRound
  refine hw.frame_seq_le rfl rfl
    (by simpa [Mem.Live] using And.intro (hl a (by simp)) (hl r (by simp)))
    (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hNorm⟩
  have ht₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hT.mono (by fp_sub) le_rfl) ht
  have hflag := hfr₁.keep (Store.readsOnly_get _ _ _) (by disjoint) hstate.1
  have hindex := hfr₁.keep (Store.readsOnly_get _ _ _) (by disjoint) hstate.2
  have htest := hC.test_le (d := []) (x := (r.1, r.2 + 2)) (y := t) hNorm ht₁
  refine writes_ite rfl rfl htest ?_
  by_cases hsmall : subdiagonalSq H k ≤ threshold
  · have hsmall' : z.re ^ 2 + z.im ^ 2 ≤ threshold := hsq ▸ hsmall
    dsimp only [z] at hsmall'
    simp only [id_eq, decide_eq_true_eq]
    rw [if_pos hsmall']
    refine (writes_indexLit hL rfl rfl
      (by dsimp only; rw [hfr₁.len_eq]; omega)).seq_le (by fp_sub) ?_
    intro m₂ hfr₂ ⟨hp₂, hOne⟩
    refine (writes_indexLit hL rfl rfl (by dsimp only; rw [hfr₂.len_eq, hfr₁.len_eq]; omega)).mono
      (by fp_sub) ?_
    intro m₃ hfr₃ ⟨hp₃, hK⟩
    have hOne' := hfr₃.keep (Store.readsOnly_get _ _ _) (by disjoint) hOne
    have hlit (j : ℕ) : M.lit (j : ℚ) = (j : ℝ) := by simpa using hE.lit (j : ℚ)
    have hone : M.lit (1 : ℚ) = (1 : ℝ) := by simpa using hE.lit 1
    exact ⟨hp₃.trans (hp₂.trans hp₁), by
      simpa [ScanHolds, scanPrefix, hsmall, hlit, hone] using And.intro hOne' hK⟩
  · have hsmall' : ¬z.re ^ 2 + z.im ^ 2 ≤ threshold := hsq ▸ hsmall
    dsimp only [z] at hsmall'
    simp only [id_eq, decide_eq_true_eq]
    rw [if_neg hsmall']
    refine (Writes.skip (md := .total) (I := I) (τ := τ) ?_).mono bot_le (fun _ _ hp => hp)
    exact ⟨hp₁, by simpa [ScanHolds, scanPrefix, hsmall] using And.intro hflag hindex⟩

/-- The actual scan loop implements the mathematical prefix recurrence on every visit. -/
private theorem scanLoop_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a t r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {threshold : ℝ}
    (hH : HoldsMatrix a H m.store) (ht : m.store.get t.1 t.2 = some threshold)
    (hstate : ScanHolds H threshold 0 r m.store)
    (hl : m.Live [a, t, r]) (hroom : r.2 + 5 ≤ m.store.len r.1)
    (hA : Fp.Disj (Store.inBlock r.1 r.2 5)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hT : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock t.1 t.2 1)) :
    Writes .total I τ (scanLoop (Op := Op) (Tst := Tst)).body
      (Env.frame [n + 1] [a, t, r]) (Store.inBlock r.1 r.2 5)
      (fun m' => m'.pos = m.pos ∧ ScanHolds H threshold n r m'.store) m := by
  unfold scanLoop
  refine writes_loop rfl (fun _ => Store.inBlock r.1 r.2 5) (fun _ _ => le_rfl)
    (fun k m' => m'.pos = m.pos ∧ ScanHolds H threshold k r m'.store)
    ⟨rfl, hstate⟩ ?_
  intro k hk m' hfr ⟨hp, hs⟩
  have hH' := hH.of_eqOff hfr hA
  have ht' := hfr.keep (Store.readsOnly_get _ _ _) hT ht
  have hw := scanRound_writes (τ := τ) hS hE hL hC hk hH' ht' hs
    (hl.congr hfr.length_eq) (by rw [hfr.len_eq]; exact hroom) hA hT
  refine (hw.in_frame rfl rfl (hl.congr hfr.length_eq)).mono le_rfl ?_
  intro _ _ ⟨hp', hs'⟩
  exact ⟨hp'.trans hp, hs'⟩

/-- The full scalar scan initializes its own outputs and inspects every subdiagonal entry.
Its actual flag/index words equal the exact prefix specification; outputs need only capacity. -/
theorem scan_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a t r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {threshold : ℝ}
    (hH : HoldsMatrix a H m.store) (ht : m.store.get t.1 t.2 = some threshold)
    (hl : m.Live [a, t, r]) (hroom : r.2 + 5 ≤ m.store.len r.1)
    (hA : Fp.Disj (Store.inBlock r.1 r.2 5)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hT : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock t.1 t.2 1)) :
    Writes .total I τ (scan (Op := Op) (Tst := Tst)).body
      (Env.frame [n + 1] [a, t, r]) (Store.inBlock r.1 r.2 5)
      (fun m' => m'.pos = m.pos ∧ ScanHolds H threshold n r m'.store) m := by
  have hlit : M.lit (0 : ℚ) = (0 : ℝ) := by simpa using hE.lit 0
  unfold scan
  refine (writes_indexLit hL rfl rfl (by dsimp only; omega)).seq_le (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hFlag⟩
  refine (writes_indexLit hL rfl rfl (by dsimp only; rw [hfr₁.len_eq]; omega)).seq_le
    (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hIndex⟩
  have hFlag₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hFlag
  have hs : ScanHolds H threshold 0 r m₂.store := by
    simpa [ScanHolds, scanPrefix, hlit] using And.intro hFlag₂ hIndex
  have hfr := (hfr₁.trans' hfr₂).mono (by fp_sub : _ ≤ Store.inBlock r.1 r.2 5)
  have hH₂ := hH.of_eqOff hfr hA
  have ht₂ := hfr.keep (Store.readsOnly_get _ _ _) hT ht
  have hw := scanLoop_writes (τ := τ) hS hE hL hC hH₂ ht₂ hs
    (hl.congr hfr.length_eq) (by rw [hfr.len_eq]; exact hroom) hA hT
  refine (hw.in_frame rfl rfl (hl.congr hfr.length_eq)).mono le_rfl ?_
  intro _ _ ⟨hp₃, hs'⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hs'⟩

end NLAlib.ShiftedQR
