/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.OperationCount

/-!
# Scalar conjugate gradient in rounded arithmetic: one statement

The certificate `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.scalarCountedAlgorithm` is unfolded
here into one theorem about a run: it succeeds, it executes at most an explicit number of
instructions of the scalar model, and the iterate it leaves in memory satisfies an explicit
bound on its energy-norm error. Nothing is proved here beyond that unfolding.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.exec_scalarProgram_work_le_and_quadForm_le`:
  the statement.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored

open Ops
open scoped Matrix

variable {lower upper : (Fin 2 → ℕ) → ℝ}
variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}
  {supply : ∀ d, domain d → ∃ raw rhs : List ℝ,
    raw.length = d 0 * d 0 ∧ rhs.length = d 0 ∧ accepts lower upper d raw rhs}

/-- The matrix of an input: the `n × n` real matrix whose entries are the words of buffer `0`. -/
abbrev inputMatrix {d : Fin 2 → ℕ} (x : (problem lower upper domain admitted supply).Input d) :
    Matrix (Fin (d 0)) (Fin (d 0)) ℝ :=
  StoredProblem.matrix x

/-- The right-hand side of an input: the vector whose entries are the words of buffer `1`. -/
abbrev inputRhs {d : Fin 2 → ℕ} (x : (problem lower upper domain admitted supply).Input d) :
    Fin (d 0) → ℝ :=
  decv id (d 0) x.val.1.2

/-- **Scalar conjugate gradient in rounded arithmetic: termination, operation count and
energy-norm error.** Let $\mathbf{A} \in \mathbb{R}^{n \times n}$ be symmetric with spectrum in
$[a, a']$, $a > 0$, stored entry by entry, let $\mathbf{b} \in \mathbb{R}^n$ and let $k$ be the
iteration cap; write $\kappa = a'/a$. The program is Hestenes–Stiefel conjugate gradient from
$\mathbf{x}_0 = \mathbf{0}$ that keeps the residual self-product between rounds, with every
matrix-vector product and every vector operation written out as scalar loops. Its arithmetic is
any scalar machine in the standard model with unit roundoff $u$: each of $+, -, \times, /,
\sqrt{\cdot}$ returns the exact result times $1 + \delta$, $\lvert \delta \rvert \le u$, with no
overflow or underflow, and comparisons of stored numbers are exact. Let $E$ be an allowance
with $E \le 1/100$ that dominates the rounding of one scalar operation ($16 u \le E$), of one
dot product, vector update and scaling of length $n$, and of one row-by-row matrix-vector
product (`Standard.Accuracy`), and assume $3 E a' \le a$ and
$k^{2} \sqrt{k}\, E\, \kappa^{2} \le 10^{-5}$.

Then for every such input, every interpretation of the scalar operations that meets the
model, and every tape, the run succeeds, and

* it executes at most $33 n^{2} k + 157 n k + 242 k + 50 n + 127$ instructions (scalar
  operations, comparisons, index arithmetic, operand addressing, loop control and allocation,
  each of unit cost);
* it performs some number $m \le k$ of rounds and leaves in memory an iterate
  $\hat{\mathbf{x}}$, a residual vector $\hat{\mathbf{r}}$ and a direction; if $m < k$ then
  $\hat{\mathbf{r}} = \mathbf{0}$ exactly (the program stops before the cap only when the
  computed residual self-product is zero);
* for every solution $\mathbf{x}$ of $\mathbf{A}\mathbf{x} = \mathbf{b}$,
  $$(\mathbf{x} - \hat{\mathbf{x}})^{\mathsf{T}} \mathbf{A} (\mathbf{x} - \hat{\mathbf{x}})
  \le 4 \Bigl(\frac{\sqrt{2\kappa + 1} - 1}{\sqrt{2\kappa + 1} + 1}\Bigr)^{2m}
  \mathbf{x}^{\mathsf{T}} \mathbf{A} \mathbf{x} +
  \frac{12000\, m^{2} \sqrt{m}\, E\, \kappa\, a'\, \|\mathbf{b}\|^{2}}{a^{2}} +
  \frac{135\, m^{2} E\, \kappa\, \|\mathbf{b}\|^{2}}{a}.$$

The first term is the exact conjugate gradient rate at the condition number $2\kappa + 1$; the
other two are the accumulated rounding. The bound is in terms of the rounds $m$ actually
performed: reaching the cap is not a convergence claim. The count is an upper bound read off
the fixed program (`NLAlib.Ops.Program.countPoly`). The energy bound is
`NLAlib.CGRun.quadForm_sub_x_le_four_mul_pow_add` [Greenbaum1997SIMAX]; [StrakosTichy2002, §10]
for the run that the program executes.
Result: cg-scalar-rounded-operation-count-energy-error -/
theorem exec_scalarProgram_work_le_and_quadForm_le (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (em E : (Fin 2 → ℕ) → ℝ)
    (hMatvec : ∀ d, domain d → ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0) ≤ em d)
    (hAccuracy : ∀ d, domain d → Standard.Accuracy (em d) u (E d) (Blas.seq.err u) (d 0))
    (ha : ∀ d, domain d → 0 < lower d)
    (hprec : ∀ d, domain d → 3 * E d * upper d ≤ lower d)
    (hwindow : ∀ d, domain d → (d 1 : ℝ) ^ 2 * Real.sqrt (d 1) * E d *
      (upper d / lower d) ^ 2 ≤ 1 / 10 ^ 5)
    {d : Fin 2 → ℕ} (hd : domain d) (x : (problem lower upper domain admitted supply).Input d)
    (I : Interp ScalarOp CmpTst ℝ)
    (hI : (RoundedScalarBlas.model (problem lower upper domain admitted supply) M).contracts
      d x I) (τ : Tape ℝ) :
    ∃ st, exec scalarProgram I RoundedScalarBlas.resources
        (problem lower upper domain admitted supply).formats τ d
        ((problem lower upper domain admitted supply).initial d x) = some st ∧
      RoundedScalarBlas.resources.work st.cost ≤
        33 * d 0 ^ 2 * d 1 + 157 * d 0 * d 1 + 242 * d 1 + 50 * d 0 + 127 ∧
      ∃ m ≤ d 1, ∃ (s : CGState ℝ (Fin (d 0))) (rho : ℝ),
        StoresValues id (d 0) (2, 0) (3, 0) (4, 0) (5, 0) s rho st.mem ∧
        (m < d 1 → s.r = 0) ∧
        ∀ xs : Fin (d 0) → ℝ, inputMatrix x *ᵥ xs = inputRhs x →
          quadForm (inputMatrix x) (xs - s.x) ≤
            4 * ((Real.sqrt (2 * (upper d / lower d) + 1) - 1) /
              (Real.sqrt (2 * (upper d / lower d) + 1) + 1)) ^ (2 * m) *
                quadForm (inputMatrix x) xs +
            2 * ‖WithLp.toLp 2 (inputRhs x)‖ ^ 2 *
              (6000 * (m : ℝ) ^ 2 * Real.sqrt m * E d * (upper d / lower d) * upper d) /
                lower d ^ 2 +
            135 * (m : ℝ) ^ 2 * E d * (upper d / lower d) *
              (‖WithLp.toLp 2 (inputRhs x)‖ ^ 2 / lower d) := by
  obtain ⟨st, hr, -, -, hw, -, -, hg⟩ := (scalarCountedAlgorithm lower upper domain admitted
    supply M u hM hu em E hMatvec hAccuracy ha hprec hwindow).correct d hd x I hI τ
  refine ⟨st, hr, hw, ?_⟩
  have hout : StableOutput id (inputMatrix x) (inputRhs x) (E d) (lower d) (upper d) (d 1)
      (2, 0) (3, 0) (4, 0) (5, 0) st.mem := hg.2
  rcases hout with ⟨hzero, rho, hs⟩ | ⟨m, R, hm, hA, hb, hε, hs, hstop, hstab⟩
  · refine ⟨0, Nat.zero_le _, ⟨0, inputRhs x, inputRhs x⟩, rho, hs, fun h0 => ?_, fun xs _ => ?_⟩
    · rcases hzero with h | h
      · omega
      · exact h
    · have hsym : (inputMatrix x).IsHermitian := (Problem.withContext.extra_input x).1
      have hpd : (inputMatrix x).PosDef := hsym.posDef_iff_eigenvalue_pos.mpr fun i hi =>
        (ha d hd).trans_le
          (hsym.spectrum_subset_iff.mp (Problem.withContext.extra_input x).2 i hi).1
      have hq : 0 ≤ quadForm (inputMatrix x) xs := hpd.posSemidef.quadForm_nonneg xs
      simp only [sub_zero, pow_zero, mul_one, Nat.cast_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul, zero_div, add_zero]
      linarith
  · refine ⟨m, hm, ⟨R.x m, R.r m, R.p m⟩, R.ν m, hs, hstop, fun xs hxs => ?_⟩
    obtain ⟨-, -, -, -, -, hen, -⟩ := hstab
    have h := hen xs (by rw [hA, hb]; exact hxs) m le_rfl
    rw [hA, hb, hε, cgBackwardFactor_def, cgEnergyFactor_def] at h
    exact h

end NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored
