/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.Rounded.OperationCount
public import NLAlib.Krylov.Lanczos.Reorth.Rounded.Spectral

/-!
# Scalar Lanczos with full reorthogonalization in rounded arithmetic: one statement

The certificate `NLAlib.Krylov.Lanczos.Reorth.Rounded.Stored.Certification.scalarCountedAlgorithm`
is unfolded
here into one theorem about a run, joined with the orthogonality and the two-sided Ritz value
bounds of a reorthogonalized run (`NLAlib.LanczosReorthRun.specNorm_transpose_mul_self_sub_one_le`,
`NLAlib.LanczosReorthRun.eigenvalue_tridiagonal_le_add`,
`NLAlib.LanczosReorthRun.eigenvalue_sub_le_eigenvalue_tridiagonal`) for the output of that same
run. The numerical bounds hold on the longest leading prefix of steps without severe
cancellation in the reorthogonalization, which the statement reads off the stored output.

## Main results

* `exec_scalarProgram_work_le_and_spectral`, in the namespace
  `NLAlib.Krylov.Lanczos.Reorth.Rounded.Stored.Certification`: the statement.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded.Stored.Certification

open Ops
open scoped Matrix

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- **Scalar Lanczos with full reorthogonalization in rounded arithmetic: termination,
operation count, orthogonality and Ritz values.** Let
$\mathbf{A} \in \mathbb{R}^{n \times n}$ be symmetric, stored entry by entry, let
$\mathbf{b} \in \mathbb{R}^n$ and let $k$ be the iteration cap. The program is the Lanczos
recurrence started from $\mathbf{b}$ in which each new vector is orthogonalized twice against
all stored vectors (classical Gram–Schmidt, two passes) before it is normalized, with every
matrix-vector product and every vector operation written out as scalar loops. Its arithmetic
is any scalar machine in the standard model with unit roundoff $u$ (each of
$+, -, \times, /, \sqrt{\cdot}$ exact up to a factor $1 + \delta$, $\lvert\delta\rvert \le u$,
no overflow or underflow, exact comparisons), and $E \le 1/100$ is an allowance that dominates
the rounding of one scalar operation, of one dot product, vector update and scaling of length
$n$, and of one matrix-vector product (`Lanczos.Rounded.Precision`).

Then for every such input, every interpretation of the scalar operations that meets the model,
and every tape, the run succeeds, and

* it executes at most
  $33 n^{2} k + 92 n k^{2} + 152 k^{2} + 269 n k + 581 k + 58 n + 179$ instructions (scalar
  operations, comparisons, index arithmetic, operand addressing, loop control and allocation,
  each of unit cost);
* it performs some number $m \le k$ of steps and leaves in memory the vectors
  $\mathbf{v}_1, \dots, \mathbf{v}_{m+1}$, the coefficients $\alpha_j$, $\beta_j$ and, for each
  step, the norm $\nu_j$ of the new vector before reorthogonalization
  (`Lanczos.Reorth.Rounded.Output`); if $m < k$, the last computed $\beta_m$ (or the computed
  norm of $\mathbf{b}$) is exactly zero;
* for every threshold $0 < \tau \le 1$ and tolerances $0 \le \eta, c \le 1/100$ that satisfy the
  three conditions `hbudget`, `hsmall` and `hrec` below, let $r \le m$ be the number of leading
  steps with $\beta_j > \tau \nu_j$ (no severe cancellation), and
  $e = 100 (r + 1)\, \delta\, \|\mathbf{A}\|_2$ with
  $\delta = 2(2c + 2(\eta + c)^2/\tau + E) + E + 3c$. If $r \ge 1$, then with
  $\mathbf{V}_r = [\mathbf{v}_1, \dots, \mathbf{v}_r]$ and $\theta_0 \ge \dots \ge \theta_{r-1}$
  the eigenvalues of the stored tridiagonal matrix $\mathbf{T}_r$,
  $$\|\mathbf{V}_r^{\mathsf{T}} \mathbf{V}_r - \mathbf{I}\|_2 \le \eta, \qquad
  \lambda_{i + n - r}(\mathbf{A}) - e \le \theta_i \le \lambda_i(\mathbf{A}) + e
  \quad (i < r).$$

The conditions on $\tau$, $\eta$ and $c$ involve only $n$, $k$, $u$ and $E$: `hbudget` asks that
$c$ dominate the accumulated rounding of one two-pass orthogonalization against at most $k$
vectors, `hsmall` is the fixed-point condition
$\sqrt{3(k+1)}\,\cdot 2(2c + 2(\eta + c)^2/\tau + E) \le \eta$, and `hrec` is $\delta \le 1/100$.
The prefix $r$ may be shorter than the run, and is empty when the first step already has
$\beta_1 \le \tau \nu_1$; nothing is claimed beyond it. The count is an upper bound read off the
fixed program (`NLAlib.Ops.Program.countPoly`). Orthogonality:
[Paige1971, §6.1, (6.9)]; interlacing: [HornJohnson2013, Corollary 4.3.37] for the exact case.
Result: lanczos-reorth-scalar-rounded-operation-count-spectral -/
theorem exec_scalarProgram_work_le_and_spectral (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (E : (Fin 2 → ℕ) → ℝ)
    (hprec : ∀ d, domain d → Lanczos.Rounded.Precision
      (ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0)) u (E d) (Blas.seq.err u) (d 0))
    {d : Fin 2 → ℕ} (hd : domain d) (x : (problem domain admitted).Input d)
    (I : Interp ScalarOp CmpTst ℝ)
    (hI : (RoundedScalarBlas.model (problem domain admitted) M).contracts d x I) (τ : Tape ℝ) :
    ∃ st, Reference.Execution
        scalarProgram I RoundedScalarBlas.resources (problem domain admitted).formats τ d
        ((problem domain admitted).initial d x) st ∧
      RoundedScalarBlas.resources.work st.cost ≤
        33 * d 0 ^ 2 * d 1 + 92 * d 0 * d 1 ^ 2 + 152 * d 1 ^ 2 + 269 * d 0 * d 1 + 581 * d 1 +
          58 * d 0 + 179 ∧
      ∃ vs cs, st.mem.store.readBlock 2 0 ((d 1 + 1) * d 0) = some vs ∧
        st.mem.store.readBlock 3 0 (3 * d 1 + 2) = some cs ∧
        ∀ thr η c : ℝ, 0 < thr → thr ≤ 1 → 0 ≤ η → η ≤ 1 / 100 → 0 ≤ c → c ≤ 1 / 100 →
          (∀ j < d 1, (j + 1 + 1 : ℝ) * (Blas.seq.err u).dot (d 0) * (1 + η) ^ 2 +
            ((1 + (Blas.seq.err u).axpy) ^ (j + 1) - 1) *
              (1 + (j + 1 : ℝ) * (1 + (Blas.seq.err u).dot (d 0)) * (1 + η) ^ 2) ≤ c) →
          Real.sqrt (3 * ((d 1 : ℝ) + 1)) * (2 * (2 * c + 2 * (η + c) ^ 2 / thr + E d)) ≤ η →
          2 * (2 * c + 2 * (η + c) ^ 2 / thr + E d) + E d + 3 * c ≤ 1 / 100 →
          ∃ done ≤ d 1, ∃ z : Lanczos.Rounded.Values (d 0), ∃ nus : ℕ → ℝ,
            Lanczos.Reorth.Rounded.History id x.val.1.1
              x.val.1.2 (ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0)) u
              (E d) (Blas.seq.err u) done z nus ∧
            Lanczos.Reorth.Rounded.PackedOutput id (d 1) done z nus vs cs ∧
            (done < d 1 → (if done = 0 then z.initialNorm else z.beta done) = 0) ∧
            ∃ r ≤ done, (∀ j < r, thr * nus (j + 1) < z.beta (j + 1)) ∧
              (r < done → z.beta (r + 1) ≤ thr * nus (r + 1)) ∧
              (r = 0 ∨
                (specNorm ((Lanczos.basisMatrix id (d 0) vs r)ᵀ *
                    Lanczos.basisMatrix id (d 0) vs r - 1) ≤ η ∧
                  ∀ i < r,
                    eigenvalue x.val.1.1 (i + (d 0 - r)) -
                        100 * ((r : ℝ) + 1) *
                          (2 * (2 * c + 2 * (η + c) ^ 2 / thr + E d) + E d + 3 * c) *
                          specNorm x.val.1.1 ≤
                      eigenvalue (Lanczos.tridiagonalMatrix id (d 1) cs r) i ∧
                    eigenvalue (Lanczos.tridiagonalMatrix id (d 1) cs r) i ≤
                      eigenvalue x.val.1.1 i +
                        100 * ((r : ℝ) + 1) *
                          (2 * (2 * c + 2 * (η + c) ^ 2 / thr + E d) + E d + 3 * c) *
                          specNorm x.val.1.1)) := by
  obtain ⟨st, hr, -, -, hw, -, -, hg⟩ :=
    (scalarCountedAlgorithm M u hM hu E hprec).correct d hd x I hI τ
  obtain ⟨-, -, vs, cs, hvs, hcs, hout⟩ := hg
  refine ⟨st, hr, hw, vs, cs, hvs, hcs, ?_⟩
  intro thr η c hthr hthr₁ hη₀ hη hc₀ hc hbudget hsmall hrec
  have hA : x.val.1.1ᵀ = x.val.1.1 := by
    have h : x.val.1.1.IsHermitian := x.property.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  obtain ⟨done, hdone, z, nus, hh, hpacked, hstop, r, hrd, hadm, hfail, hrun⟩ :=
    hout.exists_spectral_prefix hA (hprec d hd) hthr hthr₁ hη₀ hη hc₀ hc hbudget hsmall hrec
  refine ⟨done, hdone, z, nus, hh, hpacked, hstop, r, hrd, hadm, hfail, ?_⟩
  rcases hrun with hz | ⟨L, hH, -, -, -, -, hE, ht, he, h₁, h₂, h₃, hbmat, htmat, hupper⟩
  · exact Or.inl hz
  · have hμ : L.orthLevel = 2 * (2 * c + 2 * (η + c) ^ 2 / thr + E d) := by
      simp only [LanczosReorthRun.orthLevel, h₁, h₃, ht, hE]
    have hδ : L.recLevel = 2 * (2 * c + 2 * (η + c) ^ 2 / thr + E d) + E d + 3 * c := by
      simp only [LanczosReorthRun.recLevel, hμ, hE, h₂]
    have hwindow : Real.sqrt (3 * ((r : ℝ) + 1)) * L.orthLevel ≤ L.η₀ := by
      rw [he]
      refine le_trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) L.orthLevel_nonneg)
        (by rwa [hμ])
      have hrc : (r : ℝ) ≤ (d 1 : ℝ) := by exact_mod_cast hrd.trans hdone
      linarith
    have horth := L.specNorm_transpose_mul_self_sub_one_le (by rwa [he]) hwindow
      (m := r) (by omega)
    have hbasis : LanczosReorthRun.basisOf L.v r = Lanczos.basisMatrix id (d 0) vs r :=
      hbmat.symm
    rw [hbasis, he] at horth
    refine Or.inr ⟨horth, fun i hi => ⟨?_, hupper i hi⟩⟩
    have hlower := L.eigenvalue_sub_le_eigenvalue_tridiagonal (by rwa [he]) hwindow
      (by rwa [hδ]) (by rwa [ht]) hi
    simpa only [← htmat, hH, LanczosReorthRun.backwardRadius, hδ] using hlower

end NLAlib.Krylov.Lanczos.Reorth.Rounded.Stored.Certification
