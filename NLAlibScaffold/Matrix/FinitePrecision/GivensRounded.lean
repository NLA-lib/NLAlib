/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Givens
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Ops.Blas.Pair

/-!
# Rounded Givens rotations

The complex Givens rotation of the pair $(u, v)$ has the coefficients $c = \bar u / r$,
$s = \bar v / r$ with $r = \sqrt{\lvert u\rvert^2 + \lvert v\rvert^2}$ (`NLAlib.givensCoeffs`).
On a machine with the standard model of rounded arithmetic at the unit roundoff $\boldsymbol{u}$
(`NLAlib.Ops.StdModel`, with a rounded square root) this file bounds

* the computed coefficients: each within $4\boldsymbol{u}$ of the exact ones, relatively
  (`NLAlib.Ops.StdModel.norm_roundedGivensCoeffs_sub_le`);
* the computed complex linear combination $c x + s y$ of word pairs, as the operation core
  computes it (`NLAlib.Ops.Pair.linearWords`): within $5\boldsymbol{u}(\lvert c\rvert\lvert x\rvert
  + \lvert s\rvert\lvert y\rvert)$ (`NLAlib.Ops.StdModel.norm_linearWords_sub_le`);
* a rotation of two rows (columns) of a matrix whose every column (row) pair is computed within
  $\eta$ of the exact rotation of the pair, relatively: within $2\eta\|\mathbf{A}\|_2$ in the
  spectral norm (`NLAlib.IsRoundedRowRotation.specNorm_sub_le`).

The last statement is the reusable rounded-kernel lemma: it turns a per-pair error, which is what
a program proof over a generic machine returns, into the spectral-norm error that
`NLAlib.IsPerturbedUnitarySimilar.of_specNorm_sub_le` consumes. Per two rows the error is
$O(\boldsymbol{u})\|\mathbf{A}\|_2$, so a sweep of $n$ rotations has backward error
$O(n\boldsymbol{u})$, better than the $32n^{3/2}\boldsymbol{u}$ of
[BanksGarzaVargasSrivastava2022, Lemma 3.5]. [Higham2002, Lemmas 19.7–19.8].

## Main definitions

* `NLAlib.roundedGivensCoeffs`: the coefficients computed by a machine, in the instruction order
  of the shifted QR program.
* `NLAlib.IsRoundedRowRotation`, `NLAlib.IsRoundedColRotation`: a rotation computed pairwise
  within a relative error.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Ops

/-- The Givens coefficients computed by the machine `M` from the pair $(u, v)$, in the order of
the instructions of the shifted QR program: the squared radius as
$(u_1^2 + u_2^2) + (v_1^2 + v_2^2)$, its rounded square root, and, unless it is zero, the
rounded quotients of the conjugated components (negation is exact). The zero radius gives the
literals $(1, 0)$. -/
noncomputable def roundedGivensCoeffs (M : Machine ℝ) (u v : ℂ) : ℂ × ℂ :=
  let r := M.sqrt (M.add (M.add (M.mul u.re u.re) (M.mul u.im u.im))
    (M.add (M.mul v.re v.re) (M.mul v.im v.im)))
  if r = 0 then (⟨M.lit 1, M.lit 0⟩, ⟨M.lit 0, M.lit 0⟩)
  else (⟨M.div u.re r, M.div (M.neg u.im) r⟩, ⟨M.div v.re r, M.div (M.neg v.im) r⟩)

/-- **Rounded Givens coefficients**: under the standard model with
$0 \le \boldsymbol{u} \le 1/100$, each computed coefficient is within $4\boldsymbol{u}$ of the
exact one, relatively: $\lvert\tilde c - c\rvert \le 4\boldsymbol{u}\lvert c\rvert$ and
$\lvert\tilde s - s\rvert \le 4\boldsymbol{u}\lvert s\rvert$. [Higham2002, Lemma 19.7]. -/
theorem Ops.StdModel.norm_roundedGivensCoeffs_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) (x y : ℂ) :
    ‖(roundedGivensCoeffs M x y).1 - (givensCoeffs x y).1‖ ≤ 4 * u * ‖(givensCoeffs x y).1‖ ∧
      ‖(roundedGivensCoeffs M x y).2 - (givensCoeffs x y).2‖ ≤
        4 * u * ‖(givensCoeffs x y).2‖ := by
  sorry

/-- **Rounded complex linear combination**: the pair computed by `NLAlib.Ops.Pair.linearWords`
from the pairs of $a, b, x, y$ is within $5\boldsymbol{u}(\lvert a\rvert\lvert x\rvert +
\lvert b\rvert\lvert y\rvert)$ of $a x + b y$, for $0 \le \boldsymbol{u} \le 1/100$
(each real component carries at most three roundings). [Higham2002, Lemma 3.5]. -/
theorem Ops.StdModel.norm_linearWords_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) (a b x y : ℂ) :
    ‖(⟨(Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).1,
        (Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).2⟩ : ℂ) -
        (a * x + b * y)‖ ≤ 5 * u * (‖a‖ * ‖x‖ + ‖b‖ * ‖y‖) := by
  sorry

variable {n : ℕ}

/-- `A'` is the rotation of the rows $i, j$ of `A` by the exact Givens rotation of the
coefficients $(c, s)$, computed within the relative error $\eta$ per column: the rows other than
$i, j$ are kept, and for every column $k$ the computed pair $(\mathbf{A}'_{ik}, \mathbf{A}'_{jk})$
is within $\eta\,\|(\mathbf{A}_{ik}, \mathbf{A}_{jk})\|$ of the rotated pair. -/
def IsRoundedRowRotation (η : ℝ) (i j : Fin n) (c s : ℂ) (A A' : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  (∀ r k, r ≠ i → r ≠ j → A' r k = A r k) ∧
    ∀ k, Real.sqrt (‖A' i k - (givens i j c s * A) i k‖ ^ 2 +
      ‖A' j k - (givens i j c s * A) j k‖ ^ 2) ≤ η * Real.sqrt (‖A i k‖ ^ 2 + ‖A j k‖ ^ 2)

/-- `A'` is the rotation of the columns $i, j$ of `A` by the conjugate transpose of the exact
Givens rotation of $(c, s)$, computed within the relative error $\eta$ per row. -/
def IsRoundedColRotation (η : ℝ) (i j : Fin n) (c s : ℂ) (A A' : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  (∀ r k, k ≠ i → k ≠ j → A' r k = A r k) ∧
    ∀ r, Real.sqrt (‖A' r i - (A * (givens i j c s)ᴴ) r i‖ ^ 2 +
      ‖A' r j - (A * (givens i j c s)ᴴ) r j‖ ^ 2) ≤ η * Real.sqrt (‖A r i‖ ^ 2 + ‖A r j‖ ^ 2)

/-- **A rotation of two rows computed pairwise has spectral-norm error $2\eta\|\mathbf{A}\|_2$**:
the error is supported on two rows, its Frobenius norm is at most $\eta$ times the Frobenius
norm of those rows, which is at most $\sqrt 2\,\|\mathbf{A}\|_2$. [Higham2002, Lemma 19.8]. -/
theorem IsRoundedRowRotation.specNorm_sub_le {η : ℝ} {i j : Fin n} {c s : ℂ}
    {A A' : Matrix (Fin n) (Fin n) ℂ} (h : IsRoundedRowRotation η i j c s A A') (hη : 0 ≤ η) :
    specNorm (A' - givens i j c s * A) ≤ 2 * η * specNorm A := by
  sorry

/-- **A rotation of two columns computed pairwise has spectral-norm error
$2\eta\|\mathbf{A}\|_2$.** [Higham2002, Lemma 19.8]. -/
theorem IsRoundedColRotation.specNorm_sub_le {η : ℝ} {i j : Fin n} {c s : ℂ}
    {A A' : Matrix (Fin n) (Fin n) ℂ} (h : IsRoundedColRotation η i j c s A A') (hη : 0 ≤ η) :
    specNorm (A' - A * (givens i j c s)ᴴ) ≤ 2 * η * specNorm A := by
  sorry

/-- **Rounded coefficients and rounded application**: rotating a pair by the computed
coefficients $(\tilde c, \tilde s)$ of $(u, v)$ with the rounded linear combination is within
$12\boldsymbol{u}$, relatively, of rotating it by the exact Givens rotation of $(u, v)$ (the
coefficient error contributes $4\sqrt 2\,\boldsymbol{u}$, the application $5\boldsymbol{u}$ up
to second order). The exact rotation is unitary, so the computed rotation of two rows is an
`NLAlib.IsRoundedRowRotation` with $\eta = 12\boldsymbol{u}$ for a unitary rotation.
[Higham2002, Lemmas 19.7–19.8]. -/
theorem Ops.StdModel.norm_rotatePair_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) (p q x y : ℂ) :
    ‖(⟨(Pair.linearWords M ((roundedGivensCoeffs M p q).1.re, (roundedGivensCoeffs M p q).1.im)
          ((roundedGivensCoeffs M p q).2.re, (roundedGivensCoeffs M p q).2.im)
          (x.re, x.im) (y.re, y.im)).1,
        (Pair.linearWords M ((roundedGivensCoeffs M p q).1.re, (roundedGivensCoeffs M p q).1.im)
          ((roundedGivensCoeffs M p q).2.re, (roundedGivensCoeffs M p q).2.im)
          (x.re, x.im) (y.re, y.im)).2⟩ : ℂ) -
        ((givensCoeffs p q).1 * x + (givensCoeffs p q).2 * y)‖ ≤
      12 * u * Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  sorry

end NLAlib
