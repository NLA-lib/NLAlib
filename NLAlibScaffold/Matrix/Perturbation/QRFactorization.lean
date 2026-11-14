/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Norms.Frobenius

/-!
# Perturbation of the QR factorization

For an invertible $\mathbf{M}$ with QR factorization $\mathbf{M} = \mathbf{Q}\mathbf{R}$
(positive diagonal) and a perturbation with $\eta = \|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_2 \le 1/4$,
the factors of $\mathbf{M} + \mathbf{E} = \widehat{\mathbf{Q}}\widehat{\mathbf{R}}$ satisfy
$\|\widehat{\mathbf{Q}} - \mathbf{Q}\|_{\mathsf F} \le
8\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_{\mathsf F}$ and
$\|\widehat{\mathbf{R}} - \mathbf{R}\|_{\mathsf F} \le 8\|\mathbf{M}^{-1}\|_2
\|\mathbf{R}\|_2\|\mathbf{E}\|_{\mathsf F}$ [Sun1991, Theorem 1.6], [ChangPaigeStewart1997].
[BanksGarzaVargasSrivastava2022, Lemma 3.7] states the bound on $\mathbf{R}$ with
$\|\mathbf{E}\|_2$; that form fails for large $n$ (the first-order term is an upper triangular
truncation, whose operator norm grows like $\log n$), so the Frobenius norm of $\mathbf{E}$ is
used here. The constants $8$ at $\eta \le 1/4$ are deliberately loose.

The last diagonal entry has a sharper, elementary bound that needs no factor perturbation:
$\mathbf{R}_{nn} = \|\mathbf{e}_n^{\mathsf T}\mathbf{M}^{-1}\|_2^{-1}$, so
$\widehat{\mathbf{R}}_{nn} / \mathbf{R}_{nn} \in [(1 + \eta)^{-1}, (1 - \eta)^{-1}]$.

## Main results

* `NLAlib.IsQR.frobNorm_sub_le_of_add`: the bound on the unitary factors.
* `NLAlib.IsQR.frobNorm_sub_triangular_le_of_add`: the bound on the triangular factors.
* `NLAlib.IsQR.last_le_of_add`, `NLAlib.IsQR.le_last_of_add`: the last diagonal entry.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {n : ℕ} {M E Q R Q' R' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}

/-- **Perturbation of the unitary QR factor**: for QR factorizations with positive diagonals of
$\mathbf{M}$ and $\mathbf{M} + \mathbf{E}$, $\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_2 \le 1/4$ gives
$\|\widehat{\mathbf{Q}} - \mathbf{Q}\|_{\mathsf F} \le
8\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_{\mathsf F}$.
[Sun1991, Theorem 1.6]; [BanksGarzaVargasSrivastava2022, Lemma 3.7]. -/
theorem IsQR.frobNorm_sub_le_of_add (hM : IsUnit M) (h : IsQR M Q R) (h' : IsQR (M + E) Q' R')
    (hR : ∀ i, 0 < R i i) (hR' : ∀ i, 0 < R' i i) (hη : specNorm M⁻¹ * specNorm E ≤ 1 / 4) :
    frobNorm (Q' - Q) ≤ 8 * specNorm M⁻¹ * frobNorm E := by
  sorry

/-- **Perturbation of the triangular QR factor**, in the Frobenius norm of the perturbation:
$\|\widehat{\mathbf{R}} - \mathbf{R}\|_{\mathsf F} \le 8\|\mathbf{M}^{-1}\|_2\|\mathbf{R}\|_2
\|\mathbf{E}\|_{\mathsf F}$. [Sun1991, Theorem 1.6]; [BanksGarzaVargasSrivastava2022, Lemma 3.7]
(stated there with $\|\mathbf{E}\|_2$, which fails for large $n$). -/
theorem IsQR.frobNorm_sub_triangular_le_of_add (hM : IsUnit M) (h : IsQR M Q R)
    (h' : IsQR (M + E) Q' R') (hR : ∀ i, 0 < R i i) (hR' : ∀ i, 0 < R' i i)
    (hη : specNorm M⁻¹ * specNorm E ≤ 1 / 4) :
    frobNorm (R' - R) ≤ 8 * specNorm M⁻¹ * specNorm R * frobNorm E := by
  sorry

/-- **The last diagonal entry under perturbation**, upper bound: with
$\eta = \|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_2 < 1$, $|\widehat{\mathbf{R}}_{nn}| \le
(1 - \eta)^{-1}\mathbf{R}_{nn}$, for any QR factorization of $\mathbf{M} + \mathbf{E}$ (no sign
normalization). Proof through
$\mathbf{R}_{nn} = \|\mathbf{e}_n^{\mathsf T}\mathbf{M}^{-1}\|^{-1}$. [Sun1991, Theorem 1.6]. -/
theorem IsQR.last_le_of_add (hM : IsUnit M) (h : IsQR M Q R) (h' : IsQR (M + E) Q' R')
    (hR : ∀ i, 0 < R i i) (hη : specNorm M⁻¹ * specNorm E < 1) :
    ‖R' (Fin.last n) (Fin.last n)‖ ≤
      (1 - specNorm M⁻¹ * specNorm E)⁻¹ * ‖R (Fin.last n) (Fin.last n)‖ := by
  sorry

/-- **The last diagonal entry under perturbation**, lower bound:
$(1 + \eta)^{-1}\mathbf{R}_{nn} \le \lvert\widehat{\mathbf{R}}_{nn}\rvert$.
[Sun1991, Theorem 1.6]. -/
theorem IsQR.le_last_of_add (hM : IsUnit M) (h : IsQR M Q R) (h' : IsQR (M + E) Q' R')
    (hR : ∀ i, 0 < R i i) (hη : specNorm M⁻¹ * specNorm E < 1) :
    (1 + specNorm M⁻¹ * specNorm E)⁻¹ * ‖R (Fin.last n) (Fin.last n)‖ ≤
      ‖R' (Fin.last n) (Fin.last n)‖ := by
  sorry

end NLAlib
