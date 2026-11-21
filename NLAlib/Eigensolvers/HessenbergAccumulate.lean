/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.HessenbergReduction

/-!
# Hessenberg reduction with the accumulated unitary

The reduction `NLAlib.hessenbergReduceLast` records its rotations in a slotted log; replaying the
log on the columns of a stored accumulator gives the reduction with the accumulated unitary,
`NLAlib.hessenbergReduceQ`. The recorded planes stay below the order, so the replay is within its
error bound, and the pair is a Hessenberg reducer stage of the dense Schur pipeline.

## Main definitions

* `NLAlib.hessenbergReduceQ`: the reduction with the accumulated unitary, `[N] (A, U) → (A, U)`.

## Main results

* `NLAlib.hessenbergReduceQ_hessenbergReducerContract`: the reduction with the accumulated
  unitary is a Hessenberg reducer stage (`NLAlib.Schur.HessenbergReducerContract`).
-/

@[expose] public section

open scoped Matrix
namespace NLAlib

open Ops ShiftedQR

/-- The tracked relation of the reduction with the accumulated unitary, from the replay bound on
the closed log of the reduction. -/
private theorem hessenbergReduceQ_tracked {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    {nmax : ℕ} (hnu : 200 * (nmax : ℝ) ^ 2 * u ≤ 1) {N : ℕ} (hN : N ≤ nmax)
    (A U U' : Matrix (Fin N) (Fin N) ℂ)
    (h : specNorm (U' - U * embedBlock 0 (givensLog N (slotEntries (N - 1)
      ((hessenbergReduceLastSlots M A).map some ++
        List.replicate (N - ((hessenbergReduceLastSlots M A).map some).length) none)))) ≤
      ((1 + 24 * u) ^ (N * (N - 1)) - 1) * specNorm U) :
    IsUpperHessenberg (hessenbergReduceLastWord M A) ∧
      IsTrackedUnitarySimilar (27 * (nmax : ℝ) ^ 2 * u) (50 * (nmax : ℝ) ^ 2 * u * specNorm A)
        U A U' (hessenbergReduceLastWord M A) := by
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hzero : M.lit 0 = 0 := by simpa using hM.lit 0
  have hN' : (N : ℝ) ≤ nmax := by exact_mod_cast hN
  rw [slotEntries_append_replicate_none, givensLog_slotEntries_map_some, embedBlock_zero_self]
    at h
  cases N with
  | zero =>
    refine ⟨fun i => i.elim0, 1, ⟨hasOrthonormalCols_one, 0, by rw [specNorm_zero]; positivity,
      Subsingleton.elim _ _⟩, ?_⟩
    rw [Subsingleton.elim (U' - U * 1) 0, specNorm_zero]
    positivity
  | succ n =>
    have hn : ((n : ℝ) + 1) ^ 2 ≤ (nmax : ℝ) ^ 2 := by push_cast at hN'; gcongr
    obtain ⟨hH, -, hBy⟩ := hessenbergReduceLast_isPerturbedUnitarySimilarBy hM hzero
      (by nlinarith) A
    refine ⟨hH, _, hBy.mono (by gcongr), h.trans (mul_le_mul_of_nonneg_right ?_
      (specNorm_nonneg U))⟩
    have hR : ((((n + 1) * (n + 1 - 1) : ℕ)) : ℝ) ≤ (nmax : ℝ) ^ 2 := by
      push_cast [Nat.add_sub_cancel]
      nlinarith
    refine (one_add_mul_pow_sub_one_le hu0 (by nlinarith)).trans ?_
    nlinarith

section Accumulate

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The bottom-up Hessenberg reduction with the accumulated unitary**: open a slotted log of $N$
slots of $N - 1$ entries (`NLAlib.slottedLogOpen`), reduce `A` recording the rotations
(`NLAlib.hessenbergReduceLast`), then replay them on the columns of `U`
(`NLAlib.givensReplayColumns`), so that `U` becomes $\mathbf{U}\mathbf{V}$ up to rounding with
$\mathbf{V}$ the unitary of the reduction. The interface is `[N] (A, U) → (A, U)`; the log is
scoped.
Algorithm: hessenberg-reduction -/
def hessenbergReduceQ : Stmt O Q := ops% [N] (A, U) → (A, U) {
  let Lg ← alloc (N * (1 + 5 * (N - 1)));
  run (slottedLogOpen (O := O) (Q := Q)) [N, N - 1] (Lg);
  run (hessenbergReduceLast (O := O) (Q := Q)) [N, N - 1, 0] (A, A, Lg);
  run (givensReplayColumns (O := O) (Q := Q)) [N, 0, 0, N, N, N - 1] (Lg, U, U)
}

/-- **The reduction with the accumulated unitary is a Hessenberg reducer**: on a scalar machine
with the standard model at $\boldsymbol{u}$, exact comparisons and `toNat`, index literals and
exact natural literals up to $N_{\max} \ge 1$, with $200N_{\max}^2\boldsymbol{u} \le 1$,
`NLAlib.hessenbergReduceQ` meets `NLAlib.Schur.HessenbergReducerContract` on the orders
$N \le N_{\max}$ with the relative accumulator error $27N_{\max}^2\boldsymbol{u}$ (the replay of
$N(N - 1)$ logged rotations, `NLAlib.givensReplayColumns_specNorm_sub_le` and
`NLAlib.one_add_mul_pow_sub_one_le`) and the backward error
$50N_{\max}^2\boldsymbol{u}\|\mathbf{A}\|_2$
(`NLAlib.hessenbergReduceLast_isPerturbedUnitarySimilarBy`). -/
theorem hessenbergReduceQ_hessenbergReducerContract {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hC : IsCmp id I) (hQ : IsToNat id I)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax) (h1 : 1 ≤ nmax)
    (hnu : 200 * (nmax : ℝ) ^ 2 * u ≤ 1) :
    Schur.HessenbergReducerContract (27 * (nmax : ℝ) ^ 2 * u) (50 * (nmax : ℝ) ^ 2 * u) nmax
      (hessenbergReduceQ (O := O) (Q := Q)) I := by
  intro N a uo τ μ A U hN ⟨hA, hU⟩ hl hd
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hn1 : (1 : ℝ) ≤ nmax := by exact_mod_cast h1
  have hu : u ≤ 1 / 100 := by nlinarith
  have hal : a.1 < μ.store.length := hl a (by simp)
  have hul : uo.1 < μ.store.length := hl uo (by simp)
  set Sl := hessenbergReduceLastSlots M A
  unfold hessenbergReduceQ
  change Writes .total I τ (Stmt.allocs [_] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [N * (1 + 5 * (N - 1))]) rfl
    (fun hBelow ⟨U', H, ⟨h₁, h₂⟩, h₃⟩ =>
      ⟨U', H, ⟨h₁.of_below hBelow hal, h₂.of_below hBelow hul⟩, h₃⟩) ?_
  intro s₁ hlen hlens hBelow
  set Lc := μ.store.length with hLc
  simp only [List.length_cons, List.length_nil] at hlen
  have hLg : s₁.len Lc = N * (1 + 5 * (N - 1)) := by simpa using hlens 0 (by simp)
  have hA₀ := hA.of_below hBelow hal
  have hU₀ := hU.of_below hBelow hul
  have hlive : ∀ {s : Store ℝ}, s.length = Lc + 1 → ∀ {p : ℕ},
      (⟨s, p⟩ : Mem ℝ).Live [a, uo, (Lc, 0)] := fun h => by simp [Mem.Live, h]; omega
  have hFp : Store.inBlock Lc 0 (N * (1 + 5 * (N - 1))) ≤
      Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock uo.1 uo.2 (2 * (N * N)) ⊔
        Fp.above Lc := fun b z h => Or.inr (h.1 ▸ le_rfl)
  refine (slottedLogOpen_writes (τ := τ) (μ := ⟨s₁, μ.pos⟩) (ns := N) (w := N - 1) (lg := (Lc, 0))
    hS hM (by simp [hLg])).frame_seq_le rfl rfl
    (by simp [Mem.Live]; omega) hFp ?_
  rintro μ₁ hfr₁ ⟨hp₁, hlog₁⟩
  have hdl : ∀ {b o n}, b < Lc → Fp.Disj (Store.inBlock b o n)
      (Store.inBlock Lc 0 (N * (1 + 5 * (N - 1)))) := fun hb => Fp.disj_inBlock_of_ne (by omega)
  refine (hessenbergReduceLast_writes_word (τ := τ) (m := μ₁) (L := []) hS hC hL hNat h1
    (by omega) hlog₁ (by simp) (by omega) (by simp [Mem.Live, hfr₁.length_eq]; omega)
    (hA₀.of_eqOff hfr₁ (hdl hal).symm) (hdl hal)).frame_seq_le rfl rfl
    (by simp [Mem.Live, hfr₁.length_eq]; omega)
    (sup_le (le_sup_left.trans le_sup_left) hFp) ?_
  rintro μ₂ hfr₂ ⟨hp₂, hH₂, hlog₂⟩
  have hlog₃ := hlog₂.close
  have hU₂ : HoldsMatrix uo U μ₂.store := (hU₀.of_eqOff hfr₁ (hdl hul).symm).of_eqOff hfr₂
    (Fp.disj_sup_left.mpr ⟨hd, (hdl hul).symm⟩)
  have hpl : ∀ e ∈ slotEntries (N - 1) ([] ++ Sl.map some ++
      List.replicate (N - ([] ++ Sl.map some).length) none), e.1 + 1 < N ∨ e = (0, 0, 0) := by
    intro e he
    rw [List.nil_append, slotEntries_append_replicate_none] at he
    simp only [slotEntries, List.mem_flatMap, List.mem_map] at he
    obtain ⟨_, ⟨es, hes, rfl⟩, he⟩ := he
    simp only [Option.map_some, Option.getD_some, padEntries, List.mem_append,
      List.mem_replicate] at he
    rcases he with he | ⟨-, rfl⟩
    · exact hessenbergReduceLastSlots_plane M A es hes e he
    · exact Or.inr rfl
  have hlo : slotEntries (N - 1) ([] ++ Sl.map some ++
      List.replicate (N - ([] ++ Sl.map some).length) none) = [] ∨ 0 + 1 < N := by
    by_cases h2 : 2 ≤ N
    · exact Or.inr (by omega)
    · refine Or.inl ?_
      have : Sl = [] := List.eq_nil_of_length_eq_zero (by
        rw [length_hessenbergReduceLastSlots]; omega)
      rw [this]
      simp [slotEntries]
  refine ((givensReplayColumns_specNorm_sub_le (τ := τ) (μ := μ₂) (lo := 0) (d := N) hS hM hu0
    hu hQ hC (by omega) hpl hlo hlog₃ (by simp [Sl, length_hessenbergReduceLastSlots]) hU₂
    (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq]; omega) (hdl hul).symm).in_frame rfl rfl
    (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq]; omega)).mono
    (le_sup_right.trans le_sup_left) ?_
  rintro μ₃ hfr₃ ⟨U', hU', hb⟩
  obtain ⟨hH, ht⟩ := hessenbergReduceQ_tracked hM hnu hN A U U' (by simpa using hb)
  exact ⟨U', _, ⟨hH₂.of_eqOff hfr₃ hd.symm, hU'⟩, hH, ht⟩

end Accumulate

end NLAlib
