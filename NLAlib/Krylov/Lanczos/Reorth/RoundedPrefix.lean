/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.RoundedOutput
public import NLAlib.Krylov.FinitePrecision.LanczosReorthPrefix

/-!
# The actual longest admissible prefix of rounded reorthogonalized output

The solver always returns its complete actual history. Analysis selects its longest leading
strictly tau-admissible prefix from the physically stored coupling and saved raw norms. Zero
length is permitted; the next excluded computed step, when present, fails the strict test.
The program need not stop at this analysis prefix and its runtime guard is unchanged.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.Output.exists_admissible_prefix`: total prefix split.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded

variable {K : Type} [Inhabited K] {dec : K → ℝ} {n cap : ℕ}
variable {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {em u E : ℝ}
variable {e : Ops.Blas1Err} {vs cs : List K}

/-- Every actual output determines a leading strictly admissible prefix, possibly empty.
If it ends before the executed history, the next actual coupling is at most tau times its
saved raw norm. The complete history, packed values and runtime early-stop meaning are retained. -/
theorem Output.exists_admissible_prefix (h : Output dec A rhs em u E e cap vs cs) (τ : ℝ) :
    ∃ done ≤ cap, ∃ z : Lanczos.Rounded.Values n, ∃ nus : ℕ → ℝ,
      History dec A rhs em u E e done z nus ∧ PackedOutput dec cap done z nus vs cs ∧
      (done < cap → (if done = 0 then z.initialNorm else z.beta done) = 0) ∧
      ∃ r ≤ done, (∀ j < r, τ * nus (j + 1) < z.beta (j + 1)) ∧
        (r < done → z.beta (r + 1) ≤ τ * nus (r + 1)) := by
  obtain ⟨done, hd, z, nus, hhistory, hpacked, hstop⟩ := h
  refine ⟨done, hd, z, nus, hhistory, hpacked, hstop,
    reorthSteps τ (fun j => nus (j + 1)) z.beta done,
    reorthSteps_le .., ?_, ?_⟩
  · exact fun _ hj => mul_lt_beta_of_lt_reorthSteps τ (fun j => nus (j + 1)) z.beta done hj
  · exact beta_le_of_reorthSteps_lt τ (fun j => nus (j + 1)) z.beta done

end NLAlib.Krylov.Lanczos.Reorth.Rounded
