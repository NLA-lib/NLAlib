/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.WorklistSolve
public import NLAlib.Eigensolvers.ShiftedQR.Constants

/-!
# Exact state and local iteration interface for capped decoupling

The state records an actual stored unitary conjugate, the original conditioning hypothesis,
its mathematical potential contraction while undecoupled, and the actual scalar scan result.
A substituted iteration is a fixed scalar implementation with its own local total word proof;
it is never an access-model operation.

## Main results

* `NLAlib.ShiftedQR.IterationContract`: the local scalar iteration proof interface.
* `NLAlib.ShiftedQR.DecoupleInv`: stored and mathematical state at an iteration boundary.
* `NLAlib.ShiftedQR.DecoupleInv.decoupled_at_cap`: quantitative hypotheses force decoupling.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

/-- The local total theorem of one fixed scalar shift-strategy iteration. Its actual Ritz
list specifies the mathematical accepted step stored back in the same work view. -/
def IterationContract {O Q : Type} (θ : ℝ) (Iter : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n m M : ℕ} {τ B α γ : ℝ} {w p c : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    IsUpperHessenberg H → 2 ^ m ≤ n → 0 ≤ τ → 0 ≤ B →
    M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊ → 0 < M →
    HoldsMatrix w H μ.store → μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ] →
    μ.store.readBlock c.1 c.2 2 = some [τ ^ 2, (1 - γ) ^ (2 * (2 ^ m))] →
    μ.Live [w, p, c, w] → w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock p.1 p.2 5 ⊔ Store.inBlock c.1 c.2 2) →
    Writes .total I tape Iter.body (Env.frame [n + 1, m, 2 ^ m, M] [w, p, c, w])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ss : List ℂ, ss.length = 2 ^ m ∧
        IsOptimalRitzValues θ H ss ∧ HoldsMatrix w (shqrAcceptStep τ B θ α γ m H ss) μ'.store) μ

/-- The actual matrix and scan at one capped iteration boundary. Potential contraction is
required only while the matrix remains undecoupled; a stopped matrix can be retained. -/
def DecoupleInv {n : ℕ} (H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (τ B _θ _α γ : ℝ) (m j : ℕ) (w r : ℕ × ℕ) (μ : Mem ℝ) : Prop :=
  ∃ (U H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), HasOrthonormalCols U ∧
    H = Uᴴ * H₀ * U ∧ IsUpperHessenberg H ∧
    (∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ), IsUnit V ∧
      H * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ B) ∧
    (¬IsDecoupledAbs τ H → hessenbergPotential (2 ^ m) H ≤
      (1 - γ) ^ j * hessenbergPotential (2 ^ m) H₀) ∧
    HoldsMatrix w H μ.store ∧ ScanHolds H (τ ^ 2) n r μ.store

/-- An initial scalar scan establishes the exact invariant at iteration zero. -/
theorem DecoupleInv.init {n m F : ℕ} {τ B θ α γ δ : ℝ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {w r : ℕ × ℕ} {μ : Mem ℝ}
    (hyp : RapidDecouplingHyps H τ B θ α γ δ m F) (hH : IsUpperHessenberg H)
    (hW : HoldsMatrix w H μ.store) (hR : ScanHolds H (τ ^ 2) n r μ.store) :
    DecoupleInv H τ B θ α γ m 0 w r μ := by
  exact ⟨1, H, hasOrthonormalCols_one, by simp, hH, hyp.1, fun _ => by simp, hW, hR⟩

/-- A decoupled matrix remains a valid state at the next iteration boundary without arithmetic. -/
theorem DecoupleInv.stopped {n m j : ℕ} {τ B θ α γ : ℝ}
    {H₀ H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {w r : ℕ × ℕ} {μ : Mem ℝ}
    (hU : HasOrthonormalCols U) (hH : H = Uᴴ * H₀ * U) (hHess : IsUpperHessenberg H)
    (hκ : ∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ), IsUnit V ∧
      H * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ B)
    (hdec : IsDecoupledAbs τ H) (hW : HoldsMatrix w H μ.store)
    (hR : ScanHolds H (τ ^ 2) n r μ.store) : DecoupleInv H₀ τ B θ α γ m (j + 1) w r μ :=
  ⟨U, H, hU, hH, hHess, hκ, fun hn => False.elim (hn hdec), hW, hR⟩

/-- At the quantitative cap, the actual stored matrix must already be decoupled. -/
theorem DecoupleInv.decoupled_at_cap {n m F : ℕ} {τ B θ α γ δ : ℝ}
    {H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {w r : ℕ × ℕ} {μ : Mem ℝ}
    (hyp : RapidDecouplingHyps H₀ τ B θ α γ δ m F) (hkn : 2 ^ m ≤ n)
    (h : DecoupleInv H₀ τ B θ α γ m F w r μ) :
    ∃ (U H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), HasOrthonormalCols U ∧
      H = Uᴴ * H₀ * U ∧ IsUpperHessenberg H ∧ IsDecoupledAbs τ H ∧
      HoldsMatrix w H μ.store ∧ ScanHolds H (τ ^ 2) n r μ.store := by
  obtain ⟨U, H, hU, hH, hHess, _, hψ, hW, hR⟩ := h
  have hdec : IsDecoupledAbs τ H := by
    by_contra hn
    have := hyp.iteration_lt hkn hn (hψ hn)
    omega
  exact ⟨U, H, hU, hH, hHess, hdec, hW, hR⟩

end NLAlib.ShiftedQR
