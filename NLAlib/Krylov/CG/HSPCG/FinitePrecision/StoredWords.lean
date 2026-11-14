/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.StoredContext
public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.ZeroStart
public import NLAlib.Ops.Logic.ContextLink

/-!
# Rounded PCG on actual stored system and preconditioner words

The uniform context transformation supplies both actual matrix blocks to their scalar row
loops. The derived dense rounding law and fixed preconditioner action instantiate the total
rounded solver theorem. Literal-zero initialization consumes supplied uninitialized capacity.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.stored_zeroStart_wp`: total stored scalar-row PCG execution.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded

open Ops
open scoped Matrix

/-- Raw symmetric positive spectral windows and explicit scalar/cap precision ensure total
PCG execution with both operators implemented by actual dense scalar rows. The reference
matrices are the supplied raw blocks, and the preconditioner action is their actual word
kernel. There is no oracle-error, computed-trajectory or successful-execution callback. -/
theorem stored_zeroStart_wp
    {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ} {u E a a' p p' : ℝ}
    {n cap cutoff : ℕ} {τ : Tape ℝ} {μ : Mem ℝ} {B X R Z P : ℕ × ℕ}
    {bs : List ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u)
    (hB : IsBlas1 id (Blas.seq.err u) (fun _ => True) I)
    (hDot : I.IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn M) (OutApart (fun _ => True)))
    (hCmp : IsCmp id I)
    (context : List (ℕ × ℕ)) (systemIndex preconditionerIndex : Fin context.length)
    (rawA rawP : List ℝ)
    (hContext : ∀ z ∈ context, z.1 < cutoff) (hCutoff : cutoff ≤ μ.store.length)
    (hData : μ.store.readBlock context[systemIndex].1 context[systemIndex].2 (n * n) = some rawA)
    (hPrec : μ.store.readBlock context[preconditionerIndex].1
      context[preconditionerIndex].2 (n * n) = some rawP)
    (hAbove : ∀ z ∈ [B, X, R, Z, P], cutoff ≤ z.1)
    (hAccuracy : Standard.Accuracy (StoredContext.relativeError u n) u E (Blas.seq.err u) n)
    (hAT : (StoredOperator.denseMatrix n n rawA)ᵀ = StoredOperator.denseMatrix n n rawA)
    (hPT : (StoredOperator.denseMatrix n n rawP)ᵀ = StoredOperator.denseMatrix n n rawP)
    (ha : 0 < a) (hp : 0 < p)
    (hsA : spectrum ℝ (StoredOperator.denseMatrix n n rawA) ⊆ Set.Icc a a')
    (hsP : spectrum ℝ (StoredOperator.denseMatrix n n rawP) ⊆ Set.Icc p p')
    (hAp : 6 * E * a' ≤ a) (hPp : 6 * E * p' ≤ p)
    (hwindow : E * (1024 * (a' / a) * (p' / p)) ^ (cap + 1) ≤ 1 / 2)
    (hBX : B.1 ≠ X.1) (hBR : B.1 ≠ R.1) (hBZ : B.1 ≠ Z.1) (hBP : B.1 ≠ P.1)
    (hXR : X.1 ≠ R.1) (hXZ : X.1 ≠ Z.1) (hXP : X.1 ≠ P.1)
    (hRZ : R.1 ≠ Z.1) (hRP : R.1 ≠ P.1) (hZP : Z.1 ≠ P.1)
    (hl : μ.Live [B, X, R, Z, P]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [X, R, Z, P] [n, n, n, n]) :
    Wp .total I τ
      ((zeroStart (Op := Signature) (Tst := CmpTst)).linkContext context.length 2
        (StoredContext.table context.length systemIndex preconditionerIndex))
      ((Env.frame [n, cap] [B, X, X, R, Z, P]).withContext context 2)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ m ≤ cap, ∃ s rho,
        StoresState id n X R Z P s μ' ∧
        RunPrefix (StoredOperator.denseMatrix n n rawA)
          (StoredOperator.denseMatrix n n rawP) (StoredContext.oracle hM hu n rawP)
          (decv id n bs) E m s rho ∧ (m < cap → s.r = 0)) μ := by
  obtain ⟨hs, hb', ha', hp', hc⟩ := StoredContext.guarded_laws hM hu hS hB hCmp
    context systemIndex preconditionerIndex μ.store rawA rawP hContext hData hPrec
  have hdot := StoredContext.guarded_dot (e := Blas.seq.err u) (u := u) hDot
    context systemIndex preconditionerIndex cutoff μ.store n rawA rawP
  apply Wp.linkContext_of_guarded I _ context
    (StoredContext.relation M (Blas.seq.err u) u n rawA rawP)
    (StoredContext.admissible n) _ cutoff μ.store
    (StoredContext.guarded_meets hM hu hS hB context systemIndex preconditionerIndex
      μ.store rawA rawP hContext hData hPrec)
    (by simp [Env.frame]) (Mem.ContextSnapshot.refl hCutoff)
    (Env.Above.frame (by
      intro z hz
      apply hAbove z
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢
      tauto) _) hContext
  obtain ⟨_, hd, haa, _⟩ := Standard.Scheme.sequential.errors_nonneg hu n
  have hue : u ≤ E := by linarith [hAccuracy.scalar, hAccuracy.nonneg]
  have hde : (Blas.seq.err u).dot n ≤ E := by
    linarith [hAccuracy.dot, hAccuracy.nonneg]
  exact (zeroStart_writes hs hM hb' trivial ha' hp' hdot hc hAT hPT ha hp hsA hsP
    hu hd haa hAccuracy.matvec hue hde hAccuracy.axpy hAccuracy.small hAccuracy.matvec
    hAp hPp hwindow hBX hBR hBZ hBP hXR hXZ hXP hRZ hRP hZP hl hb hz).wp
      (fun _ _ h => h)

end NLAlib.Krylov.CG.HSPCG.Rounded
