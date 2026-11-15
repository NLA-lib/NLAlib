/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.WorklistRound

/-!
# Initialized exact worklist execution and backward error

The program builds its initial stack from literals and traverses the actual active ranges.
Global raw matrix and parameter assumptions supply every local quantitative hypothesis. The
result is an actual stored eigenvalue listing of a bounded perturbation of the raw input.
The caller provides reserved views for scratch; no initialized scratch or output is assumed.

## Main results

* `NLAlib.ShiftedQR.worklistSolve`: the computable initialized view implementation.
* `NLAlib.ShiftedQR.worklistSolve_writes`: total actual output and its backward error.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- Initialize a singleton range stack and process the actual worklist. The four output
views include reserved scratch supplied by an allocating caller. -/
def worklistSolve (D : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, F, M] (A, Params) → (St, Out, W, R) {
    run (stackInit (Op := O) (Tst := Q)).body [N, 0, N] (St);
    run (worklistLoop (worklistRound D)).body [N, m, k, F, M] (A, Params, St, Out, W, R)
  }

/-- The initialized exact worklist returns the actual stored roots of a perturbation of
norm at most $n\tau$, for an input matrix of order $n+1$. The input spectral separation,
conditioning and iteration/grid parameters imply all local progress and capacity guarantees.
The substituted decoupling theorem is about the fixed scalar implementation on one block. -/
theorem worklistSolve_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I)
    (hQ : IsToNat id I) (hC : IsCmp id I)
    {θ : ℝ} {K : KernelRoutines θ} (hK : IsEigenvalueKernels K I)
    (D : Impl O Q) (hD : DecouplingContract θ D I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m F M : ℕ} {a p stack out w r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ B α γ δ g : ℝ}
    (hG : WorklistGeometry (n + 1) a p stack out w r μ)
    (hHess : IsUpperHessenberg H) (hA : HoldsMatrix a H μ.store)
    (hGlobal : ShiftedQRHyps H B θ α γ δ g m F) (hτ : τ = δ * frobNorm H)
    (hM : M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hParams : μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ]) :
    Writes .total I tape (worklistSolve D).body
      (Env.frame [n + 1, m, 2 ^ m, F, M] [a, p, stack, out, w, r])
      (worklistFp (n + 1) a stack out w r)
      (fun μ' => μ'.pos = μ.pos ∧
        ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
          HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
          specNorm E ≤ (n : ℝ) * τ ∧
          (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)) μ := by
  have hδ : 0 < δ := by
    rcases hGlobal with ⟨_, _, _, _, _, _, _, _, hδ, _⟩
    exact hδ
  have hτ0 : 0 ≤ τ := by rw [hτ]; exact mul_nonneg hδ.le (frobNorm_nonneg _)
  have hSA : Fp.Disj (Store.inBlock stack.1 stack.2 (1 + 2 * (n + 1)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by
    simpa using hG.disj 2 0 (by omega)
  have hSP : Fp.Disj (Store.inBlock stack.1 stack.2 (1 + 2 * (n + 1)))
      (Store.inBlock p.1 p.2 5) := by simpa using hG.disj 2 1 (by omega)
  have hw := stackInit_writes (τ := tape) hL hQ hE (lo := 0) (size := n + 1)
    (Nat.zero_lt_succ n) (by simpa only [Nat.add_assoc] using hG.room.2.2.1)
  unfold worklistSolve
  refine hw.frame_seq_le rfl rfl (by simpa [Mem.Live] using hG.live stack (by simp))
    (by fp_sub [worklistFp]) ?_
  intro μ₁ hfr₁ ⟨hp₁, hSt₁⟩
  have hG₁ := hG.of_eqOff hfr₁
  have hA₁ := hA.of_eqOff hfr₁ hSA
  have hParams₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) hSP hParams
  have hInv := WorklistInv.init (out := out) (τ := τ) hHess hA₁ hSt₁
  have hloop := worklistLoop_writes (worklistRound D) (tape := tape)
    (m := m) (k := 2 ^ m) (F := F) (M := M) hC hG₁.live hInv
    (fun j _ μ' hfr hi count hc hpos => worklistRound_writes (tape := tape)
      hS hE hL hQ hK D hD (hG₁.of_eqOff hfr) hi hGlobal hτ hM
      (hfr.keep (Store.readsOnly_readBlock _ _ _ _) hG₁.disj_params hParams₁) hc hpos)
  refine (hloop.in_frame rfl rfl hG₁.live).mono le_rfl ?_
  intro μ₂ _ ⟨hp₂, j, hInv₂, hzero⟩
  obtain ⟨A, roots, ε, done, hDefl, _, hOut, hε⟩ := hInv₂.output hzero hτ0
  obtain ⟨E, hNorm, hRoots⟩ := hDefl.exists_roots_eq
  exact ⟨hp₂.trans hp₁, roots, E, hOut, hNorm.trans hε, hRoots⟩

end NLAlib.ShiftedQR
