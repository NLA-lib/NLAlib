/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.RoundedAnalysis
public import NLAlib.Krylov.Lanczos.Reorth.RoundedPrefix
public import NLAlib.Krylov.FinitePrecision.LanczosReorthStep

/-!
# The actual admissible numerical run in rounded reorthogonalized output

The full solver output is unconditional under its primitive accuracy assumptions. Numerical
analysis selects the longest strictly tau-admissible prefix of that actual history. A positive
selected prefix is the existing `LanczosReorthRun`, tied to the stored basis and coefficients;
an empty prefix is represented separately. A next excluded computed step fails its strict test.
The program is unchanged and need not stop at the selected mathematical prefix.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.History.exists_run`: a positive admissible actual prefix.
* `NLAlib.Krylov.Lanczos.Reorth.Rounded.Output.exists_run_prefix`: the total prefix split.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded

open scoped Matrix

variable {K : Type} [Inhabited K] {dec : K → ℝ} {n : ℕ}
variable {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {em u E : ℝ} {e : Ops.Blas1Err}

/-- Actual local update, two-pass and normalization guarantees assemble the existing run for
any positive strictly admissible prefix. Its vectors and all three coefficient sequences are
exactly the final archived values. The first direction's unit bound is derived from the actual
first continuation guard, rather than assumed. -/
theorem History.exists_run {done r : ℕ} {z : Lanczos.Rounded.Values n} {nus : ℕ → ℝ}
    {τ η c : ℝ} (h : History dec A rhs em u E e done z nus)
    (hr : 0 < r) (hrd : r ≤ done) (hA : Aᵀ = A)
    (hp : Lanczos.Rounded.Precision em u E e n)
    (hτ : 0 < τ) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 100) (hc₀ : 0 ≤ c) (hc : c ≤ 1 / 100)
    (hadm : ∀ j < r, τ * nus (j + 1) < z.beta (j + 1))
    (hbudget : ∀ j < r, (j + 1 + 1 : ℝ) * e.dot n * (1 + η) ^ 2 +
      ((1 + e.axpy) ^ (j + 1) - 1) *
        (1 + (j + 1 : ℝ) * (1 + e.dot n) * (1 + η) ^ 2) ≤ c) :
    ∃ L : LanczosReorthRun n r, L.H = A ∧ L.v = z.v ∧ L.α = z.alpha ∧ L.β = z.beta ∧
      L.ν = nus ∧ L.ε = E ∧ L.τ = τ ∧ L.η₀ = η ∧ L.ε₁ = 2 * c ∧ L.ε₂ = 3 * c ∧
      L.ε₃ = 2 * (η + c) ^ 2 := by
  obtain ⟨hv₀, hb₀, hv₁⟩ := h.initial_data
  refine LanczosReorthImplementation.exists_run_of_steps hA hp.nonneg hp.small
    (by positivity) (by positivity) (by positivity) hr hv₀ hb₀
    (hv₁ (hr.trans_le hrd)) hτ hadm ?_
  intro j hj
  exact (h.local j (hj.trans_le hrd)).exists_roundedStep hp hη₀ hη hc (hbudget j hj)

/-- Every actual rounded output has a longest leading tau-admissible prefix. It is either
empty or an existing numerical reorthogonalized Lanczos run with the same stored values.
If another computed step follows it, that step's actual coupling is at most tau times its
saved raw norm. No successful-execution or future admissibility premise is assumed. -/
theorem Output.exists_run_prefix {cap : ℕ} {vs cs : List K} {τ η c : ℝ}
    (h : Output dec A rhs em u E e cap vs cs) (hA : Aᵀ = A)
    (hp : Lanczos.Rounded.Precision em u E e n)
    (hτ : 0 < τ) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 100) (hc₀ : 0 ≤ c) (hc : c ≤ 1 / 100)
    (hbudget : ∀ j < cap, (j + 1 + 1 : ℝ) * e.dot n * (1 + η) ^ 2 +
      ((1 + e.axpy) ^ (j + 1) - 1) *
        (1 + (j + 1 : ℝ) * (1 + e.dot n) * (1 + η) ^ 2) ≤ c) :
    ∃ done ≤ cap, ∃ z : Lanczos.Rounded.Values n, ∃ nus : ℕ → ℝ,
      History dec A rhs em u E e done z nus ∧ PackedOutput dec cap done z nus vs cs ∧
      (done < cap → (if done = 0 then z.initialNorm else z.beta done) = 0) ∧
      ∃ r ≤ done, (∀ j < r, τ * nus (j + 1) < z.beta (j + 1)) ∧
        (r = 0 ∨ ∃ L : LanczosReorthRun n r,
          L.H = A ∧ L.v = z.v ∧ L.α = z.alpha ∧ L.β = z.beta ∧ L.ν = nus ∧
          L.ε = E ∧ L.τ = τ ∧ L.η₀ = η ∧ L.ε₁ = 2 * c ∧ L.ε₂ = 3 * c ∧
          L.ε₃ = 2 * (η + c) ^ 2) ∧
        (r < done → z.beta (r + 1) ≤ τ * nus (r + 1)) := by
  obtain ⟨done, hd, z, nus, hh, hpack, hstop, r, hr, hadm, hfail⟩ :=
    h.exists_admissible_prefix τ
  refine ⟨done, hd, z, nus, hh, hpack, hstop, r, hr, hadm, ?_, hfail⟩
  by_cases hz : r = 0
  · exact Or.inl hz
  · exact Or.inr (hh.exists_run (Nat.pos_of_ne_zero hz) hr hA hp hτ hη₀ hη hc₀ hc hadm
      (fun j hj => hbudget j ((hj.trans_le hr).trans_le hd)))

end NLAlib.Krylov.Lanczos.Reorth.Rounded
