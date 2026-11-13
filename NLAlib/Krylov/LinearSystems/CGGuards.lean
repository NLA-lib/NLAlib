/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGTridiagonal

/-!
# Mathematical guards in the conjugate-gradient recurrence

Positive curvature and legal terminal statuses follow from the SPD recurrence. These are
pure transition facts, independent of a stored representation or program evaluator.

## Main results

* `NLAlib.CGImplementation.zero_lt_dotProduct_mulVec_cgState_p` proves positive curvature.
* `NLAlib.CGImplementation.guarded_next_invariants` preserves recurrence and terminal status.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open scoped Matrix

/-- In an SPD exact CG trajectory a nonzero residual gives strictly positive curvature.
This justifies the actual guard without imposing a local execution or curvature premise. -/
theorem zero_lt_dotProduct_mulVec_cgState_p {N j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosDef) (b : Fin N → ℝ) (hr : (cgState A b 0 j).r ≠ 0) :
    0 < (cgState A b 0 j).p ⬝ᵥ (A *ᵥ (cgState A b 0 j).p) := by
  have h := hA.re_quadForm_pos (hA.cgState_p_ne_zero b 0 hr)
  simpa only [quadForm, star_trivial, RCLike.re_to_real] using h

/-- The guarded mathematical step preserves legal statuses and SPD recurrence correspondence,
including exact zero-residual continuation. It does not refer to a matrix access backend. -/
theorem guarded_next_invariants {N j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {v : CGState ℝ (Fin N)} {status : ℝ}
    (hstatus : status = 0 ∨ status = 1 ∨ status = -1)
    (hactive : status = 0 → v.r ≠ 0)
    (hexact : A.PosDef → v = cgState A b 0 j ∧ (status = 1 ↔ v.r = 0) ∧ status ≠ -1) :
    let μ := v.p ⬝ᵥ (A *ᵥ v.p)
    let next := if status = 0 then if 0 < μ then cgStep A v else v else v
    let flag : ℝ := if status = 0 then
      if 0 < μ then if next.r ⬝ᵥ next.r = 0 then 1 else 0 else -1 else status
    (flag = 0 ∨ flag = 1 ∨ flag = -1) ∧ (flag = 0 → next.r ≠ 0) ∧
      (A.PosDef → next = cgState A b 0 (j + 1) ∧ (flag = 1 ↔ next.r = 0) ∧ flag ≠ -1) := by
  classical
  dsimp only
  by_cases hs : status = 0
  · simp only [if_pos hs]
    by_cases hm : 0 < v.p ⬝ᵥ (A *ᵥ v.p)
    · simp only [if_pos hm]
      refine ⟨?_, ?_, ?_⟩
      · split_ifs <;> norm_num
      · intro hflag hr
        simp only [hr, dotProduct_zero] at hflag
        norm_num at hflag
      · intro hA
        obtain ⟨hv, _, _⟩ := hexact hA
        refine ⟨?_, ?_, ?_⟩
        · rw [hv]; rfl
        · by_cases hr : (cgStep A v).r = 0 <;> simp [hr]
        · split_ifs <;> norm_num
    · simp only [if_neg hm]
      refine ⟨by norm_num, by norm_num, ?_⟩
      intro hA
      obtain ⟨hv, _, _⟩ := hexact hA
      exact (hm (by simpa only [hv] using
        zero_lt_dotProduct_mulVec_cgState_p hA b (by simpa only [← hv] using hactive hs))).elim
  · simp only [if_neg hs]
    refine ⟨hstatus, hactive, ?_⟩
    intro hA
    obtain ⟨hv, hterm, hnot⟩ := hexact hA
    have hflag : status = 1 := by
      rcases hstatus with hz | h1 | hn
      · exact (hs hz).elim
      · exact h1
      · exact (hnot hn).elim
    have hr : (cgState A b 0 j).r = 0 := by rw [← hv]; exact hterm.mp hflag
    refine ⟨?_, hterm, hnot⟩
    rw [cgState_succ_eq_of_r_eq_zero A b 0 hr]
    exact hv

end NLAlib.CGImplementation
