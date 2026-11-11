/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.Alg
public import NLAlib.Krylov.CG.Reorth.Math
public import NLAlib.Ops.Blas.Decoded
public import NLAlib.Ops.Logic.Tactic

/-!
# Exact residual reorthogonalization

The stored basis can be rectangular and can contain zero columns. A zero decoded column
contributes no update, regardless of the machine's unconstrained division by zero. Thus the
exact sweep has a total certificate without assuming that its basis has full rank.

## Main results

* `NLAlib.Krylov.CG.Reorth.sweep_spec`: exact total execution of the stored sweep.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has Blas1Op Op]

/-- Decode a column of a basis stored consecutively by columns. -/
def column (dec : K → ℝ) (n : ℕ) (qs : List K) (j : ℕ) : Fin n → ℝ :=
  fun i => dec (vec qs (j * n + i))

/-- The residual is updated in place in a buffer different from the basis. -/
@[admNF] def SweepOperands : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun _ ins outs => ∃ Q r, ins = [Q, r] ∧ outs = [r] ∧ Q.1 ≠ r.1

/-- The residual output is the sequential mathematical projection sweep. -/
@[simps (attr := storeNF)]
noncomputable def sweepRel (dec : K → ℝ) : BlockRel K where
  nd := 2
  inLens d := [d.getD 1 0 * d.headD 0, d.headD 0]
  outLens d := [d.headD 0]
  rel d X _ Y := match X, Y with
    | [qs, rs], [rs'] => decv dec (d.headD 0) rs' =
        sweepVec (column dec (d.headD 0) qs) (decv dec (d.headD 0) rs) (d.getD 1 0)
    | _, _ => False

/-- Exact scalar and BLAS contracts implement the full sweep at all dimensions and ranks. -/
theorem sweep_spec {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec (fun _ => True) I) :
    (sweepImpl (Op := Op) (Tst := Tst)).Meets I .total ((sweepRel dec).spec SweepOperands) := by
  cert_intro [n, k] (Q, r) → (r') reads (qs, rs)
  obtain ⟨hr, hQr⟩ := hadm
  subst r'
  refine writes_alloc rfl fun s₁ hs₁ ht hBelow => ?_
  refine Writes.mono (writes_loop (N := k) rfl
    (fun _ => Store.inBlock r.1 r.2 n ⊔ Store.inBuf μ.store.length)
    (fun _ _ => le_rfl)
    (fun j m' => m'.pos = μ.pos ∧ ∃ vs, m'.store.readBlock r.1 r.2 n = some vs ∧
      decv dec n vs = sweepVec (column dec n qs) (decv dec n rs) j)
    ⟨rfl, rs, by kept, rfl⟩ fun j hj m₁ hfr ⟨hpos, vs, hvs, hvec⟩ => ?_)
      (by fp_sub) ?_
  · step hB.dot as m₂ hfr₂ ⟨hpos₂, num, hnum, hnumrel⟩
    step hB.dot as m₃ hfr₃ ⟨hpos₃, den, hden, hdenrel⟩
    step (hS .div) as m₄ hfr₄ ⟨hpos₄, c, hc, hcrel⟩
    step (hS .neg) as m₅ hfr₅ ⟨hpos₅, nc, hnc, hncrel⟩
    step hB.axpy as m₆ hfr₆ ⟨hpos₆, zs, hzs, hzrel⟩
    have hcol : decv dec n ((qs.drop (j * n)).take n) = column dec n qs j := by
      funext i
      exact congrArg dec (vec_drop_take i.isLt)
    have hnumd : dec num = column dec n qs j ⬝ᵥ decv dec n vs := by
      simpa only [hcol] using (dotExactRel_decoded (dec := dec) hnumrel)
    have hdend : dec den = column dec n qs j ⬝ᵥ column dec n qs j := by
      simpa only [hcol] using (dotExactRel_decoded (dec := dec) hdenrel)
    have hneg : dec nc = -dec c := hncrel ▸ hM.neg c
    have hout : decv dec n zs = projectOff (column dec n qs j) (decv dec n vs) := by
      by_cases hzero : column dec n qs j = 0
      · simpa [hcol, hzero, projectOff] using
          (axpyExactRel_decoded (dec := dec) hzrel)
      · have hd0 : dec den ≠ 0 := by
          rw [hdend]
          exact fun h => hzero (dotProduct_self_eq_zero.mp h)
        have hcd : dec c = (column dec n qs j ⬝ᵥ decv dec n vs) /
            (column dec n qs j ⬝ᵥ column dec n qs j) := by
          rw [← hcrel, hM.div num den hd0, hnumd, hdend]
        simpa [hcol, hneg, hcd, projectOff, sub_eq_add_neg, neg_smul] using
          (axpyExactRel_decoded (dec := dec) hzrel)
    exact ⟨by simp [hpos₆, hpos₅, hpos₄, hpos₃, hpos₂, hpos], zs, hzs,
      by rw [hout, hvec]; rfl⟩
  · intro m₁ hfr ⟨hpos, vs, hvs, hvec⟩ s₂ hs₂ hBelow₂
    exact ⟨by simpa using hpos, [vs], Mem.readBlocks_of_cons (by kept) rfl, hvec⟩

end NLAlib.Krylov.CG.Reorth
