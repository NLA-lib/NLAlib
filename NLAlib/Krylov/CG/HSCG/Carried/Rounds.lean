/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Exact
public import NLAlib.Krylov.CG.Math.Recurrence

/-!
# Successful early-exit exact CG rounds

Positive definiteness supplies every active division guard. The retained residual self-product
is tested before each round, so convergence stops the loop even when its cap exceeds the
initial Krylov grade. The theorem assumes an initialized stored CG state and establishes
successful total execution, including initially converged states and zero dimensions.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.rounds_writes` reaches the state at the smaller of cap and grade.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

private theorem StoresState.read_rho {dec : K → ℝ} {n : ℕ} {x r p v : ℕ × ℕ}
    {s : CGState ℝ (Fin n)} {μ : Mem K} (h : StoresState dec n x r p v s μ) :
    ∃ rr, μ.store.get v.1 v.2 = some rr ∧ dec rr = s.r ⬝ᵥ s.r := by
  obtain ⟨xs, rs, ps, rr, hr, he, hv⟩ := h
  obtain ⟨_, _, _, hr₁, hc₁⟩ := Mem.readBlocks_cons_eq_some.mp hr
  rw [← (List.cons.inj hc₁).2] at hr₁
  obtain ⟨_, _, _, hr₂, hc₂⟩ := Mem.readBlocks_cons_eq_some.mp hr₁
  rw [← (List.cons.inj hc₂).2] at hr₂
  obtain ⟨_, _, _, hr₃, hc₃⟩ := Mem.readBlocks_cons_eq_some.mp hr₂
  rw [← (List.cons.inj hc₃).2] at hr₃
  obtain ⟨_, _, hvread, _, hc₄⟩ := Mem.readBlocks_cons_eq_some.mp hr₃
  have hvread' : μ.store.readBlock v.1 v.2 1 = some [rr] :=
    (List.cons.inj hc₄).1.symm ▸ hvread
  refine ⟨rr, by simpa using Store.get_of_readBlock hvread' (j := 0) (by omega) rr, ?_⟩
  have hrvec : decv dec n rs = s.r := congrArg CGState.r he
  simpa only [hrvec] using hv

/-- From the initial state of the recurrence for `b` and `x₀`, with its retained residual
product, the loop returns the state at the earlier of the cap and exact convergence. -/
noncomputable def roundsSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : Fin n → ℝ) : Routine.Spec K :=
  spec% [m, cap] (xs, rs, ps, [v]) → (xs', rs', ps', [v'])
    requires m = n ∧ decodedState dec n xs rs ps = cgState A b x₀ 0 ∧
      dec v = decv dec n rs ⬝ᵥ decv dec n rs
    ensures decodedState dec n xs' rs' ps' =
        cgState A b x₀ (min cap (krylovGrade A (b - A *ᵥ x₀))) ∧
      dec v' = decv dec n rs' ⬝ᵥ decv dec n rs'

/-- The capped loop meets its specification for every cap: a zero retained residual product
exits before any division, and each active round is used by its judgment. -/
theorem roundsRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef) (b x₀ : Fin n → ℝ) :
    (roundsRoutine (Op := Op) (Tst := Tst)).Meets I (roundsSpec dec A b x₀) := by
  classical
  routine_intro [n', cap] (x, r, p, v) reads (xs, rs, ps, vs)
  obtain ⟨rr₀, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs)
  obtain ⟨hn, hst, hv⟩ := hpre
  obtain rfl : n = n' := hn.symm
  have hl₀ : m.Live [x, r, p, v] := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using hl
  have hz₀ : m.Room [x, r, p, v] [n, n, n, 1] := by
    simpa only [Mem.room_cons, Mem.room_nil, and_true] using hroom
  have hstep := stepRoutine_meets (Op := Op) (Tst := Tst) hS hM hB hA
  let grade := krylovGrade A (b - A *ᵥ x₀)
  let F := Fp.blocks [x, r, p, v] [n, n, n, 1]
  let Inv := fun i μ' => μ'.pos = m.pos ∧ i ≤ grade ∧
    StoresState dec n x r p v (cgState A b x₀ i) μ'
  refine ((writes_whileFuel rfl (fun _ => F) (fun _ _ => le_rfl) ⊥ Inv
    (fun μ' => μ'.pos = m.pos ∧ StoresState dec n x r p v (cgState A b x₀ (min cap grade)) μ')
    ⟨rfl, Nat.zero_le _, xs, rs, ps, rr₀, hr, hst, hv⟩ ?_ ?_).mono (by simp [F])
    (fun _ _ h => h)).mono le_rfl ?_
  · intro i hi μ' hfr ⟨hpos, hig, hstate⟩
    obtain ⟨rr, hrr, hrrd⟩ := hstate.read_rho
    refine ⟨_, (Interp.testAt_eq rfl rfl).trans (hCmp.test_isPos hrr), ?_⟩
    by_cases ha : 0 < dec rr
    · simp only [ha, decide_true, ite_true]
      have hrne : (cgState A b x₀ i).r ≠ 0 := by
        intro hrzero
        rw [hrzero, zero_dotProduct] at hrrd
        exact ha.ne' hrrd
      have hig' : i < grade := Nat.lt_of_not_ge fun h =>
        hrne ((hPos.cgState_r_eq_zero_iff b x₀ i).mpr h)
      have hl' : μ'.Live [x, r, p, v] := by simpa only [Mem.Live, hfr.length_eq] using hl₀
      have hz' : μ'.Room [x, r, p, v] [n, n, n, 1] := by
        simpa [Mem.Room, hfr.len_eq] using hz₀
      obtain ⟨xs₁, rs₁, ps₁, rr₁, hread₁, he₁, hv₁⟩ := hstate
      have hnb : Nonbreakdown A (decodedState dec n xs₁ rs₁ ps₁) := by
        rw [he₁]
        exact hPos.cgState_nonbreakdown b x₀ hig'
      refine (writes_frame rfl rfl ((μ'.live_append _ _).mpr ⟨hl', hl'⟩)
        (hstep [n] [x, r, p, v] τ μ' _ rfl rfl hl' (by routine_sep) hread₁
          ⟨rfl, hnb, hv₁⟩ hz')).mono le_rfl ?_
      rintro μ'' - ⟨hpos', ys, hys, hrel⟩
      routine_nf at hys
      split_reads hys as (xs₂, rs₂, ps₂, vs₂)
      obtain ⟨rr₂, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs₂)
      have hrel : decodedState dec n xs₂ rs₂ ps₂ = cgStep A (decodedState dec n xs₁ rs₁ ps₁) ∧
          dec rr₂ = decv dec n rs₂ ⬝ᵥ decv dec n rs₂ := hrel
      rw [he₁] at hrel
      exact ⟨hpos'.trans hpos, Nat.succ_le_of_lt hig', xs₂, rs₂, ps₂, rr₂, hys, hrel⟩
    · simp only [ha, decide_false, Bool.false_eq_true, ite_false]
      have hnonneg : 0 ≤ (cgState A b x₀ i).r ⬝ᵥ (cgState A b x₀ i).r :=
        Finset.sum_nonneg fun _ _ => mul_self_nonneg _
      have hrzero : (cgState A b x₀ i).r = 0 :=
        dotProduct_self_eq_zero.mp (by linarith)
      have hgi : grade ≤ i := (hPos.cgState_r_eq_zero_iff b x₀ i).mp hrzero
      have hmin : min cap grade = i := by omega
      exact Writes.skip ⟨hpos, hmin.symm ▸ hstate⟩
  · intro μ' _ ⟨hpos, hcap, hstate⟩
    exact Writes.skip ⟨hpos, (Nat.min_eq_left hcap).symm ▸ hstate⟩
  · rintro μ' - ⟨hpos, xs', rs', ps', rr', hread, he, hv'⟩
    exact ⟨hpos, [xs', rs', ps', [rr']], hread, he, hv'⟩

end NLAlib.Krylov.CG.HSCG.Carried
