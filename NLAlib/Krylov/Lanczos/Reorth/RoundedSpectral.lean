/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.RoundedStability
public import NLAlib.Krylov.Lanczos.RoundedRitz
public import NLAlib.Krylov.FinitePrecision.LanczosReorthSpectral

/-!
# Spectral bounds for the actual rounded reorthogonalized prefix

The total actual output determines a leading admissible prefix. Under size-only fixed-point
and recurrence precision windows, its nonempty tridiagonal has the existing spectral bound.
The complete executed history, physical readback and first failed threshold are retained;
the selected prefix need not exhaust the actual executed rounds.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.Output.exists_spectral_prefix`: physical stored
  tridiagonal upper spectral bound for the actual admissible prefix, or its explicit empty boundary.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded

open Ops
open scoped Matrix

variable {K : Type} [Inhabited K] {dec : K → ℝ} {n cap : ℕ}
variable {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {em u E : ℝ}
variable {e : Blas1Err} {vs cs : List K}

/-- Under symmetry, explicit primitive/pass budgets and size-only fixed-point/recurrence
windows, the actual admissible prefix has the standard perturbed upper interlacing bound. Its
radius is one hundred times prefix length plus one, recurrence level, and operator norm.
An empty prefix retains the first failed strict threshold instead of assuming nonbreakdown.
[HornJohnson2013, Corollary 4.3.37] for exact interlacing; numerical transfer uses the existing
reorthogonalized run theorem. -/
theorem Output.exists_spectral_prefix {τ η c : ℝ}
    (h : Output dec A rhs em u E e cap vs cs) (hA : Aᵀ = A)
    (hp : Lanczos.Rounded.Precision em u E e n)
    (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 100)
    (hc₀ : 0 ≤ c) (hc : c ≤ 1 / 100)
    (hbudget : ∀ j < cap, (j + 1 + 1 : ℝ) * e.dot n * (1 + η) ^ 2 +
      ((1 + e.axpy) ^ (j + 1) - 1) *
        (1 + (j + 1 : ℝ) * (1 + e.dot n) * (1 + η) ^ 2) ≤ c)
    (hsmall : Real.sqrt (3 * ((cap : ℝ) + 1)) *
      (2 * (2 * c + 2 * (η + c) ^ 2 / τ + E)) ≤ η)
    (hrec : 2 * (2 * c + 2 * (η + c) ^ 2 / τ + E) + E + 3 * c ≤ 1 / 100) :
    ∃ done ≤ cap, ∃ z : Lanczos.Rounded.Values n, ∃ nus : ℕ → ℝ,
      History dec A rhs em u E e done z nus ∧ PackedOutput dec cap done z nus vs cs ∧
      (done < cap → (if done = 0 then z.initialNorm else z.beta done) = 0) ∧
      ∃ r ≤ done, (∀ j < r, τ * nus (j + 1) < z.beta (j + 1)) ∧
        (r < done → z.beta (r + 1) ≤ τ * nus (r + 1)) ∧
        (r = 0 ∨ ∃ L : LanczosReorthRun n r,
          L.H = A ∧ L.v = z.v ∧ L.α = z.alpha ∧ L.β = z.beta ∧ L.ν = nus ∧
          L.ε = E ∧ L.τ = τ ∧ L.η₀ = η ∧ L.ε₁ = 2 * c ∧ L.ε₂ = 3 * c ∧
          L.ε₃ = 2 * (η + c) ^ 2 ∧
          basisMatrix dec n vs r = L.toLanczosData.basis ∧
          tridiagonalMatrix dec cap cs r = L.toLanczosData.tridiagonal ∧
          ∀ i < r, eigenvalue (tridiagonalMatrix dec cap cs r) i ≤ eigenvalue A i +
            100 * ((r : ℝ) + 1) *
              (2 * (2 * c + 2 * (η + c) ^ 2 / τ + E) + E + 3 * c) * specNorm A) := by
  obtain ⟨done, hd, z, nus, hh, hpacked, hstop, r, hr, hadm, hrun, hfail⟩ :=
    h.exists_run_prefix hA hp hτ hη₀ hη hc₀ hc hbudget
  refine ⟨done, hd, z, nus, hh, hpacked, hstop, r, hr, hadm, hfail, ?_⟩
  rcases hrun with hz | ⟨L, hH, hv, ha, hb, hnu, hE, ht, he, h₁, h₂, h₃⟩
  · exact Or.inl hz
  · have hrc : r ≤ cap := hr.trans hd
    have hμ : L.orthLevel = 2 * (2 * c + 2 * (η + c) ^ 2 / τ + E) := by
      simp only [LanczosReorthRun.orthLevel, h₁, h₃, ht, hE]
    have hδ : L.recLevel = 2 * (2 * c + 2 * (η + c) ^ 2 / τ + E) + E + 3 * c := by
      simp only [LanczosReorthRun.recLevel, hμ, hE, h₂]
    have hwindow : Real.sqrt (3 * ((r : ℝ) + 1)) * L.orthLevel ≤ L.η₀ := by
      rw [he]
      calc
        _ ≤ Real.sqrt (3 * ((cap : ℝ) + 1)) * L.orthLevel := by
          apply mul_le_mul_of_nonneg_right _ L.orthLevel_nonneg
          apply Real.sqrt_le_sqrt
          gcongr
        _ ≤ η := by rwa [hμ]
    have hbmat := hpacked.toPackedOutput.basisMatrix_eq (D := L.toLanczosData) hrc hv
    have htmat := hpacked.toPackedOutput.tridiagonalMatrix_eq (D := L.toLanczosData) hrc ha hb
    refine Or.inr ⟨L, hH, hv, ha, hb, hnu, hE, ht, he, h₁, h₂, h₃, hbmat, htmat, ?_⟩
    intro i hi
    have hbound := L.eigenvalue_tridiagonal_le_add (by rwa [he]) hwindow
      (by rwa [hδ]) (by rwa [ht]) hi
    simpa only [← htmat, hH, LanczosReorthRun.backwardRadius, hδ] using hbound

end NLAlib.Krylov.Lanczos.Reorth.Rounded
