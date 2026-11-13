/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Stability
public import NLAlib.Ops.Profiles.ContextLinearRounded
public import NLAlib.Ops.Logic.ContextLink
public import NLAlib.Ops.Certification
public import NLAlib.Matrix.FinitePrecision.StoredDense

/-!
# Rounded CG on actual stored dense matrix words

The fixed context transformation replaces every operator application by the actual scalar
dense loop. The standard scalar model proves its error; spectral and precision assumptions
then imply total CG execution and stability of the actual stored output.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.stored_solve_wp`: total stored rounded CG.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops
open scoped Matrix

/-- The stored rounded solver succeeds and preserves its physical numerical stability.
The matrix is decoded from protected raw words; its actual scalar matvec error follows from
`StdModel`. Mathematical input and precision assumptions exclude arithmetic breakdown. -/
theorem stored_solve_wp
    {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ} {u em E a a' : ℝ}
    {n cap cutoff : ℕ} {τ : Tape ℝ} {μ : Mem ℝ} {B X R P V : ℕ × ℕ}
    {bs xs : List ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u)
    (hB : IsBlas1 id (Blas.seq.err u) (fun _ => True) I) (hCmp : IsCmp id I)
    (context : List (ℕ × ℕ)) (index : Fin context.length) (raw : List ℝ)
    (hContext : ∀ z ∈ context, z.1 < cutoff) (hCutoff : cutoff ≤ μ.store.length)
    (hData : μ.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    (hAbove : ∀ z ∈ [B, X, R, P, V], cutoff ≤ z.1)
    (hMatvec : ScalarProducts.roundoff u n * Real.sqrt n ≤ em)
    (hAccuracy : Standard.Accuracy em u E (Blas.seq.err u) n)
    (hAT : (StoredOperator.denseMatrix n n raw)ᵀ = StoredOperator.denseMatrix n n raw)
    (ha : 0 < a)
    (hspec : spectrum ℝ (StoredOperator.denseMatrix n n raw) ⊆ Set.Icc a a')
    (hprec : 3 * E * a' ≤ a)
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * E * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hBX : B.1 ≠ X.1) (hBR : B.1 ≠ R.1) (hBP : B.1 ≠ P.1)
    (hBV : B.1 ≠ V.1) (hXR : X.1 ≠ R.1) (hXP : X.1 ≠ P.1)
    (hXV : X.1 ≠ V.1) (hRP : R.1 ≠ P.1) (hRV : R.1 ≠ V.1) (hPV : P.1 ≠ V.1)
    (hl : μ.Live [B, X, R, P, V]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hx : μ.store.readBlock X.1 X.2 n = some xs) (hx0 : decv id n xs = 0)
    (hz : μ.Room [X, R, P, V] [n, n, n, 1]) :
    Wp .total I τ
      ((solve (Op := Standard.Operation) (Tst := CmpTst)).linkContext context.length 2
        (ContextLinear.table context.length index))
      ((Env.frame [n, cap] [B, X, X, R, P, V]).withContext context 2)
      (fun μ' => μ'.pos = μ.pos ∧
        StableOutput id (StoredOperator.denseMatrix n n raw) (decv id n bs)
          E a a' cap X R P V μ') μ := by
  let A := StoredOperator.denseMatrix n n raw
  have hem : 0 ≤ em := le_trans (mul_nonneg (ScalarProducts.roundoff_nonneg hu n)
    (Real.sqrt_nonneg _)) hMatvec
  have herror : 0 ≤ em * specNorm A := mul_nonneg hem (specNorm_nonneg _)
  have hError (ys : List ℝ) :
      ‖WithLp.toLp 2 (A *ᵥ decv id n ys -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw ys)))‖ ≤
        (em * specNorm A) * ‖WithLp.toLp 2 (decv id n ys)‖ := by
    refine (hM.norm_mulVec_sub_rowWord_le hu n n raw ys).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMatvec (specNorm_nonneg A)) (norm_nonneg _)
  obtain ⟨hs, hb', hA, hc⟩ := ContextLinearRounded.guarded_laws hS hB hCmp
    context index μ.store raw herror hError hContext hData
  apply Wp.linkContext_of_guarded I _ context
    (ContextLinearRounded.relation M (Blas.seq.err u) A (em * specNorm A))
    (ContextLinearRounded.admissible (fun _ => True) n) _ cutoff μ.store
    (ContextLinearRounded.meets_guarded hS hB context index μ.store raw
      herror hError hContext hData)
    (by simp [Env.frame]) (Mem.ContextSnapshot.refl hCutoff)
    (Env.Above.frame (by
      intro z hz
      apply hAbove z
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢
      tauto) _) hContext
  obtain ⟨_, hd, haa, _⟩ := Standard.Scheme.sequential.errors_nonneg hu n
  have hue : u ≤ E := by linarith [hAccuracy.scalar, hAccuracy.nonneg]
  have hde : (Blas.seq.err u).dot n ≤ E := by linarith [hAccuracy.dot, hAccuracy.nonneg]
  have hr := runs_solve hs hM hb' trivial hA hc hAT ha hspec hu hd haa
    hAccuracy.matvec hue hde hAccuracy.axpy hAccuracy.small hprec hwindow
    (fun _ _ => 0) (τ := τ) hBX hBR hBP hBV hXR hXP hXV hRP hRV hPV hl hb hx hx0 hz
  exact hr.wp.mono fun _ h => ⟨h.1, h.2.stable ha hspec hwindow⟩

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
