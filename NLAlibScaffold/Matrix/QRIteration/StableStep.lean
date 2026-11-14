/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.ShiftedQR
public import NLAlib.Matrix.Perturbation.UnitarySimilarity
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# Backward-stable implicit QR steps

A **backward-stable single-shift QR step** with error $\varepsilon$ from $(\mathbf{H}, s)$ outputs
an upper Hessenberg $\widehat{\mathbf{H}}'$ and an upper triangular $\widehat{\mathbf{R}}$ with one
unitary $\widehat{\mathbf{Q}}$ for which $\|\widehat{\mathbf{H}}' - \widehat{\mathbf{Q}}^{\mathsf H}
\mathbf{H}\widehat{\mathbf{Q}}\|_2 \le \varepsilon$ and $\|\mathbf{H} - s - \widehat{\mathbf{Q}}
\widehat{\mathbf{R}}\|_2 \le \varepsilon$ [BanksGarzaVargasSrivastava2022, Definition 3.4]. A
rounded Givens sweep is one with $\varepsilon = \nu\boldsymbol{u}(\|\mathbf{H}\|_2 + \lvert s
\rvert)$. The paper's base $\|\mathbf{H} - s\|_2$ is not met in floating point (adding back the
shift rounds the diagonal with error $\boldsymbol{u}\lvert s\rvert$, and an implementation that
conjugates $\mathbf{H}$ itself rounds relative to $\|\mathbf{H}\|_2$); every use of the definition
bounds the base by $(1 + C)\|\mathbf{H}\|_2$ for shifts in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$, so
the base $\|\mathbf{H}\|_2 + \lvert s\rvert$ loses nothing.

A degree $m$ step is a chain of $m$ single steps (`NLAlib.IsStableQRChain`). This file states
what the chain gives: the backward error of the composed similarity (Lemma 3.6, first part, in
the corrected form: the norms of the intermediate matrices grow), the backward error of the
factorization of the shift polynomial (Lemma 3.6, second part, under $m\nu\boldsymbol{u} \le
1/4$, which the paper omits), the forward error against the exact multishift step (Lemma 3.8, with
the precision hypothesis corrected and the phase of the last diagonal entry), the last diagonal
entry of the product of the triangular factors (Lemma 3.9, by a direct argument that needs only
$\kappa_V$, not $\kappa_V^2$), and the potential after a rounded step (Lemma 5.2, over the last
$k$ subdiagonals).

## Main definitions

* `NLAlib.IsStableQRStep`: Definition 3.4 with an absolute error.
* `NLAlib.IsStableQRChain`: a degree $m$ step as a chain of single steps.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- A **backward-stable single-shift QR step** with error $\varepsilon$: `H'` is upper Hessenberg,
`R` upper triangular, and one unitary $\widehat{\mathbf{Q}}$ has
$\|\mathbf{H}' - \widehat{\mathbf{Q}}^{\mathsf H}\mathbf{H}\widehat{\mathbf{Q}}\|_2 \le \varepsilon$
and $\|\mathbf{H} - s\mathbf{I} - \widehat{\mathbf{Q}}\mathbf{R}\|_2 \le \varepsilon$.
[BanksGarzaVargasSrivastava2022, Definition 3.4], with an absolute error. -/
def IsStableQRStep (ε : ℝ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ)
    (H' R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  IsUpperHessenberg H' ∧ R.IsUpperTriangular ∧
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols Q ∧
      specNorm (H' - Qᴴ * H * Q) ≤ ε ∧ specNorm (H - s • (1 : Matrix _ _ ℂ) - Q * R) ≤ ε

/-- A **degree $m$ backward-stable QR step** with the relative error $\nu\boldsymbol{u}$ (`x`):
single steps with the shifts of the list in order, each with error
$x(\|\mathbf{H}_\ell\|_2 + \lvert s_\ell\rvert)$ at its own input $\mathbf{H}_\ell$; the list of
triangular factors is in the order of the steps. -/
inductive IsStableQRChain (x : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →
      List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) → Prop
  /-- No shift: no step. -/
  | nil (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : IsStableQRChain x H [] H []
  /-- One stable step, then the rest of the chain. -/
  | cons {H H₁ H' R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s : ℂ} {ss : List ℂ}
      {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
      (h : IsStableQRStep (x * (specNorm H + ‖s‖)) H s H₁ R)
      (t : IsStableQRChain x H₁ ss H' Rs) : IsStableQRChain x H (s :: ss) H' (R :: Rs)

/-- A backward-stable single step is a perturbed unitary similarity with the same error. -/
theorem IsStableQRStep.isPerturbedUnitarySimilar {ε : ℝ} {H H' R : Matrix (Fin (n + 1))
    (Fin (n + 1)) ℂ} {s : ℂ} (h : IsStableQRStep ε H s H' R) :
    IsPerturbedUnitarySimilar H H' ε := by
  obtain ⟨-, -, Q, hQ, hH', -⟩ := h
  exact IsPerturbedUnitarySimilar.of_specNorm_sub_le hQ hH'

/-- **Backward error of a degree $m$ step, similarity part** (corrected
[BanksGarzaVargasSrivastava2022, Lemma 3.6]): for shifts in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$, the
output is a perturbed unitary similarity of the input with error
$(1 + C)\|\mathbf{H}\|_2((1 + x)^m - 1)$. The paper's $1.4m(1 + C)\|\mathbf{H}\|_2 x$ follows when
$m x \le 1/4$; without such a bound it is false, because the norms of the intermediate matrices
grow. -/
theorem IsStableQRChain.isPerturbedUnitarySimilar {x C : ℝ} {H H' : Matrix (Fin (n + 1))
    (Fin (n + 1)) ℂ} {ss : List ℂ} {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x H ss H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) :
    IsPerturbedUnitarySimilar H H' ((1 + C) * specNorm H * ((1 + x) ^ ss.length - 1)) := by
  sorry

/-- **Backward error of a degree $m$ step, factorization part** (corrected
[BanksGarzaVargasSrivastava2022, Lemma 3.6]): for shifts in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$ and
$m x \le 1/4$, one unitary $\widehat{\mathbf{Q}}$ has $\|p(\mathbf{H}) - \widehat{\mathbf{Q}}
\widehat{\mathbf{R}}_m \cdots \widehat{\mathbf{R}}_1\|_2 \le 4(2(1 + C)\|\mathbf{H}\|_2)^m x$, with
$p(z) = \prod_\ell (z - s_\ell)$. The paper assumes only $x \le 1/4$, under which the statement is
false (its induction confuses per-step and cumulative errors); $m x \le 1/4$ suffices. -/
theorem IsStableQRChain.exists_specNorm_aeval_sub_le {x C : ℝ} {H H' : Matrix (Fin (n + 1))
    (Fin (n + 1)) ℂ} {ss : List ℂ} {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x H ss H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hm : (ss.length : ℝ) * x ≤ 1 / 4) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols Q ∧
      specNorm (Polynomial.aeval H (shiftPoly ss) - Q * Rs.reverse.prod) ≤
        4 * (2 * (1 + C) * specNorm H) ^ ss.length * x := by
  sorry

/-- **Forward error of a degree $m$ step** (corrected [BanksGarzaVargasSrivastava2022,
Lemma 3.8]): let $\mathbf{H}\mathbf{V} = \mathbf{V}\mathbf{D}$ with $\kappa(\mathbf{V}) \le \kappa$,
every shift at distance at least $d > 0$ from every eigenvalue and in
$\mathbb{D}(0, C\|\mathbf{H}\|_2)$, $\mathbf{H} \ne 0$, and
$x \le (16\kappa)^{-1}(d / ((2 + 2C)\|\mathbf{H}\|_2))^m$ (the paper's hypothesis lacks the factor
$(2 + 2C)^{-m}$). Then for a diagonal unitary $\mathbf{D}$ (the phase of the last diagonal entry
of the computed triangular factor; the paper compares with the positive-diagonal QR factor
directly), $\|\mathbf{D}^{\mathsf H}\widehat{\mathbf{H}}'\mathbf{D} - \mathbf{H}'\|_{\mathsf F} \le
(66 + 2C)\kappa\|\mathbf{H}\|_2((2 + 2C)\|\mathbf{H}\|_2 / d)^m\sqrt{n + 1}\,x$, where
$\mathbf{H}'$ is the exact multishift step. $64$ is the QR perturbation term with the loose
constant $8$ (`NLAlib.IsQR.frobNorm_sub_le_of_add`); $2 + 2C$ absorbs the accumulated similarity
error, which the paper's $33$ covers only when $d \le \|\mathbf{H}\|_2$ (false for large $C$:
$\mathbf{H} = -\mathbf{I}_2$, $s = 200$). -/
theorem IsStableQRChain.exists_frobNorm_conj_sub_le {x C κ d : ℝ} {H H' V : Matrix (Fin (n + 1))
    (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x H ss H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C) (hd : 0 < d) (hH0 : H ≠ 0)
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ κ)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖)
    (hu : x ≤ (16 * κ)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ ss.length) :
    ∃ D : Fin (n + 1) → ℂ, (∀ i, ‖D i‖ = 1) ∧
      frobNorm ((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D - multiShiftedQRStep H ss) ≤
        (66 + 2 * C) * κ * specNorm H * ((2 + 2 * C) * specNorm H / d) ^ ss.length *
          Real.sqrt (n + 1) * x := by
  sorry

/-- **The last diagonal entries of the triangular factors** (corrected
[BanksGarzaVargasSrivastava2022, Lemma 3.9]): let $\mathbf{H}\mathbf{V} = \mathbf{V}\mathbf{D}$
with $\kappa(\mathbf{V}) \le \kappa$, $\mathbf{H} \ne 0$, every shift in
$\mathbb{D}(0, C\|\mathbf{H}\|_2)$ and at distance at least $d > 0$ from every eigenvalue, and
$x \le (8004\kappa)^{-1}(d / ((2 + 2C)\|\mathbf{H}\|_2))^m$, the product of the moduli of the last
diagonal entries is within $0.0006$, relatively, of
$\|\mathbf{e}_n^{\mathsf T}p(\mathbf{H})^{-1}\|_2^{-1} = \tau_p(\mathbf{H})^m$. The paper's route
through the perturbation of the whole factor needs $\kappa^2$ and $24000$; the direct route uses
$\mathbf{R}_{nn} = \|\mathbf{e}_n^{\mathsf T}\mathbf{M}^{-1}\|_2^{-1}$
(`NLAlib.IsQR.last_le_of_add`). The computed product of $m$ moduli adds a relative error
$O(m\boldsymbol{u})$, a separate scalar estimate. -/
theorem IsStableQRChain.abs_prod_last_sub_le {x C κ d : ℝ} {H H' V : Matrix (Fin (n + 1))
    (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x H ss H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C) (hd : 0 < d) (hH0 : H ≠ 0)
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ κ)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖)
    (hu : x ≤ (8004 * κ)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ ss.length) :
    |(Rs.map fun R => ‖R (Fin.last n) (Fin.last n)‖).prod -
        ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss))⁻¹ (Fin.last n))‖⁻¹| ≤
      0.0006 * ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss))⁻¹ (Fin.last n))‖⁻¹ := by
  sorry

/-- **The potential after a rounded step** (corrected [BanksGarzaVargasSrivastava2022,
Lemma 5.2]): if the computed $\widehat{\mathbf{H}}'$ is within $0.001\omega$ of the exact step
$\mathbf{H}'$ entrywise on the last $k$ subdiagonals, then either one of those last $k$
subdiagonals of $\widehat{\mathbf{H}}'$ is below $\omega$, or
$\psi_k(\widehat{\mathbf{H}}') \le 1.0011\,\psi_k(\mathbf{H}')$. The paper takes the product and
the case split over all $n - 1$ subdiagonals; then the first alternative is not a decoupling of
the bottom block, and the factor is $1.001^{(n-1)/k}$. -/
theorem potential_le_or_exists_lt_of_sub_le {k : ℕ} (hk : 0 < k) {ω : ℝ} (hω : 0 < ω)
    {H₁ H₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hclose : ∀ i : Fin n, n ≤ (i : ℕ) + k →
      ‖H₁ i.succ i.castSucc - H₂ i.succ i.castSucc‖ ≤ 0.001 * ω) :
    (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H₁ i.succ i.castSucc‖ < ω) ∨
      hessenbergPotential k H₁ ≤ 1.0011 * hessenbergPotential k H₂ := by
  sorry

end NLAlib
