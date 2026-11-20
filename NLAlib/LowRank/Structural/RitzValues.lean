/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Growth
public import NLAlib.LowRank.Structural.BlockKrylov
public import NLAlib.LowRank.Structural.Filter
public import NLAlib.Matrix.Spectral.CompressionSingularValues

/-!
# Singular values of filtered sketches and of block Krylov iteration

Deterministic lower bounds on the singular values of the randomized SVD at a filtered test
matrix, $\mathsf{rsvd}(\mathbf{A}, g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega})$, and of
randomized block Krylov iteration $\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)$: the squares
$\sigma_i(\cdot)^2$ of the singular values of the output (the Ritz values of
$\mathbf{A}\mathbf{A}^{\mathsf{H}}$ on the sketched space) are close to
$\sigma_i(\mathbf{A})^2$. The test matrix enters through a frame $\mathbf{Z}$ of right singular
vectors with $\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ of full row rank and the residual
$(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t)\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}$, as in the structural analysis of the randomized
SVD. There are two regimes: with a gap between a head index and a tail index $t$ the deficit is
the residual times a Chebyshev value in the relative gap; without a gap the deficit is
$\gamma\,\sigma_k^2$ plus the residual times a Chebyshev value in $\gamma$, for any
$\gamma \in (0, 1]$. These are the per-vector guarantees of [MuscoMusco2015], stated for singular
values.

## Main results

* `NLAlib.HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rsvd_cfc`,
  `NLAlib.HasOrthonormalCols.sq_sub_le_sq_singularValues_rsvd_cfc_of_le_singularValues`: a
  filtered sketch, gap form and cut form.
* `NLAlib.HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki`: block Krylov
  iteration, no gap.
* `NLAlib.HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki_singularGapRatio`,
  `NLAlib.HasOrthonormalCols.sum_sq_singularValues_sub_sq_singularValues_rbki_le`: block Krylov
  iteration with a gap, per index and summed.
* `NLAlib.HasOrthonormalCols.frobNorm_sub_truncatedSVD_rbki_sq_le_add_mul`: the Frobenius error
  of one truncated run.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n s : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype s]
  [DecidableEq m] [DecidableEq n] [DecidableEq s]

/-! ### Filters -/

omit [DecidableEq m] [DecidableEq n] in
/-- A Chebyshev filter of every degree, over $\Bbbk$: for a matrix $\mathbf{A}$, a head of
$r = h + 1$ singular values, a tail index $t \ge r$ and a degree $d$, there are a real
polynomial $f$ of degree at most $d$ and constants $c > 0$ and $a$ with
$\lvert f(\sigma_i^2) \rvert \ge c$ for $i < r$, $\lvert f \rvert \le a$ on $[0, \sigma_t^2]$,
and $(a/c)^2 \le 4e^{-8d\sqrt{\gamma}}$, where
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$ (zero when $\sigma_h = 0$). The statement
of `NLAlib.exists_degree_lt_div_sq_le_exp_singularGapRatio` for a matrix over any `RCLike` field
instead of a real matrix; it replaces that theorem, under its name, once it is proved. -/
theorem exists_degree_lt_div_sq_le_exp_singularGapRatio' (A : Matrix m n 𝕜) {h r t : ℕ}
    (hr : h + 1 = r) (hrt : r ≤ t) (d : ℕ) :
    ∃ f : ℝ[X], f.degree < (d + 1 : ℕ) ∧ ∃ c a : ℝ, 0 < c ∧
      (∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|) ∧
      (∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) ∧
      (a / c) ^ 2 ≤ 4 * Real.exp (-8 * (d : ℝ) * Real.sqrt (singularGapRatio A h t)) := sorry

/-! ### Filtered sketches -/

omit [DecidableEq m] in
/-- **Singular values of a filtered sketch, gap form**: let $g$ be a real function,
$\mathbf{Z}$ a frame (orthonormal columns) with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_t$ and
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
and $i < t$. If $\lvert g(\sigma_j(\mathbf{A})^2) \rvert \ge c > 0$ for $j \le i$ and
$\lvert g \rvert \le a$ on $[0, \sigma_t(\mathbf{A})^2]$, then
$$\sigma_i(\mathbf{A})^2 - \Bigl(\frac{a}{c}\Bigr)^2
\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t)\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2 \le
\sigma_i\bigl(\mathsf{rsvd}(\mathbf{A},
g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega})\bigr)^2\,.$$
It combines `IsStarProjection.sq_singularValues_sub_sq_specNorm_le` with the head capture
`NLAlib.singularValues_one_sub_rangeProjector_mul_mul_le` of the filtered range finder.
[MuscoMusco2015, Lemma 9]; property 1 there, for the Chebyshev filter and a Gaussian block with
probability $99/100$, here deterministic, for any filter, with the residual explicit. -/
theorem HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rsvd_cfc
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {t : ℕ}
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) {i : ℕ} (hi : i < t) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ j ≤ i, c ≤ |g (singularValues A j ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |g x| ≤ a) :
    singularValues A i ^ 2 -
        (a / c) ^ 2 * specNorm ((A - truncatedSVD A t) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rsvd A (cfc g (Aᴴ * A) * Ω)) i ^ 2 := sorry

omit [DecidableEq m] in
/-- **Singular values of a filtered sketch, cut form**: let $g$ be a real function,
$\mathbf{Z}$ a frame (orthonormal columns) whose range contains the row space of
$\llbracket\mathbf{A}\rrbracket_{i+1}$, that is
$\llbracket\mathbf{A}\rrbracket_{i+1}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} =
\llbracket\mathbf{A}\rrbracket_{i+1}$, with
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
and let $0 \le \tau \le \sigma_i(\mathbf{A})$ be a cut. If
$\lvert g(\sigma_j(\mathbf{A})^2) \rvert \ge c > 0$ for $j \le i$ and $\lvert g \rvert \le a$ on
$[0, \tau^2]$, then
$$\tau^2 - \Bigl(\frac{a}{c}\Bigr)^2
\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2 \le
\sigma_i\bigl(\mathsf{rsvd}(\mathbf{A},
g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega})\bigr)^2\,.$$
The filter need not separate $\sigma_i$ from the singular values just below it: everything above
the cut $\tau$ counts as head, and the bound is for $\tau^2$, not $\sigma_i^2$.
[MuscoMusco2015, Lemma 9]; property 2 there, with the cut at $\sigma_{k+1}$ times a fixed factor
and probability $99/100$, here deterministic with the cut as a parameter. -/
theorem HasOrthonormalCols.sq_sub_le_sq_singularValues_rsvd_cfc_of_le_singularValues
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {i : ℕ}
    (hAZ : truncatedSVD A (i + 1) * Z * Zᴴ = truncatedSVD A (i + 1)) {c a τ : ℝ} (hc : 0 < c)
    (hτ : 0 ≤ τ) (hτi : τ ≤ singularValues A i)
    (hhead : ∀ j ≤ i, c ≤ |g (singularValues A j ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (τ ^ 2), |g x| ≤ a) :
    τ ^ 2 - (a / c) ^ 2 * specNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rsvd A (cfc g (Aᴴ * A) * Ω)) i ^ 2 := sorry

/-! ### Block Krylov iteration -/

omit [DecidableEq m] in
/-- **Singular values of block Krylov iteration, no gap**: let $\mathbf{Z}$ be a frame
(orthonormal columns) with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$ and
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
$q \ge 1$ and $0 < \gamma \le 1$. Then for every $i < k$,
$$\sigma_i(\mathbf{A})^2 - \gamma\,\sigma_k(\mathbf{A})^2 -
4e^{-2\sqrt{2}(q-1)\sqrt{\gamma}}\,
\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2 \le
\sigma_i\bigl(\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\bigr)^2\,.$$
No gap in the spectrum is assumed; $\gamma$ is a free parameter.
[BakshiClarksonWoodruff2022, Lemma 3.1]; [MuscoMusco2015, Theorem 12]; there for a Gaussian block
of $k$ columns, with probability $99/100$, depth $O(\log(d/\gamma)/\sqrt{\gamma})$ and
unspecified constants, here deterministic for any block, with the residual explicit. -/
theorem HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {k : ℕ} (hAZ : A * Z * Zᴴ = truncatedSVD A k) {q : ℕ}
    (hq : 1 ≤ q) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) {i : ℕ} (hi : i < k) :
    singularValues A i ^ 2 - γ * singularValues A k ^ 2 -
        4 * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt γ) *
          specNorm ((A - truncatedSVD A k) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rbki A Ω q) i ^ 2 := sorry

omit [DecidableEq m] in
/-- **Singular values of block Krylov iteration with a gap, per index**: let $r = h + 1 \le t$,
let $\mathbf{Z}$ be a frame (orthonormal columns) with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_t$ and
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
$q \ge 1$, and $\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$
(`NLAlib.singularGapRatio`). Then for every $i < r$,
$$\sigma_i(\mathbf{A})^2 - 4e^{-8(q-1)\sqrt{\gamma}}\,
\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t)\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2 \le
\sigma_i\bigl(\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\bigr)^2\,.$$
[BakshiClarksonWoodruff2022, Lemma 3.2]; [MuscoMusco2015, Theorem 13]; there for a Gaussian block
with probability $99/100$, depth $O(\log(n/\gamma)/\sqrt{\gamma'})$ in the gap
$\gamma' = \min(1, \sigma_k/\sigma_{b+1} - 1)$ and unspecified constants, here deterministic,
with a head count $r$ that may be smaller than the tail index. -/
theorem HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki_singularGapRatio
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {h r t : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) {q : ℕ} (hq : 1 ≤ q) {i : ℕ} (hi : i < r) :
    singularValues A i ^ 2 -
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          specNorm ((A - truncatedSVD A t) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rbki A Ω q) i ^ 2 := sorry

omit [DecidableEq m] in
/-- **Singular values of block Krylov iteration with a gap, summed**: let $r = h + 1 \le t$,
let $\mathbf{Z}$ be a frame (orthonormal columns) with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_t$ and
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
$q \ge 1$, and $\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$
(`NLAlib.singularGapRatio`). Then
$$\sum_{i<r} \Bigl(\sigma_i(\mathbf{A})^2 -
\sigma_i\bigl(\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\bigr)^2\Bigr) \le
4e^{-8(q-1)\sqrt{\gamma}}\,
\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t)\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_{\mathsf{F}}^2\,.$$
The sum of the $r$ deficits is bounded by the Frobenius norm of the residual, with no factor
$r$: the per-index bound
`NLAlib.HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki_singularGapRatio`
summed over $i < r$ would give $r$ times the spectral norm.
[MuscoMusco2015, Lemma 9]; property 1 there, with probability $99/100$ and unspecified
constants. -/
theorem HasOrthonormalCols.sum_sq_singularValues_sub_sq_singularValues_rbki_le
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {h r t : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) {q : ℕ} (hq : 1 ≤ q) :
    ∑ i ∈ Finset.range r, (singularValues A i ^ 2 - singularValues (rbki A Ω q) i ^ 2) ≤
      4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
        frobNorm ((A - truncatedSVD A t) * Ω * pinv (Zᴴ * Ω)) ^ 2 := sorry

omit [DecidableEq m] in
/-- **The Frobenius error of one truncated run of block Krylov iteration, no gap**: let
$\mathbf{Z}$ be a frame (orthonormal columns) with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$ and
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
$q \ge 1$ and $0 < \gamma \le 1$. Then
$$\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\rrbracket_k
\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 +
k\gamma\,\sigma_k(\mathbf{A})^2 + 4k\,e^{-2\sqrt{2}(q-1)\sqrt{\gamma}}\,
\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2\,.$$
The sum over $i < k$ of
`NLAlib.HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki` in
`IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq`. The term $k\gamma\,\sigma_k^2$ is compared
with the optimal error only through $\sigma_k^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$, so this is not the
$(1 + \varepsilon)$ Frobenius bound of [MuscoMusco2015, Theorem 1] at depth
$O(\log d/\sqrt{\varepsilon})$. -/
theorem HasOrthonormalCols.frobNorm_sub_truncatedSVD_rbki_sq_le_add_mul
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {k : ℕ} (hAZ : A * Z * Zᴴ = truncatedSVD A k) {q : ℕ}
    (hq : 1 ≤ q) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    frobNorm (A - truncatedSVD (rbki A Ω q) k) ^ 2 ≤
      frobNorm (A - truncatedSVD A k) ^ 2 + k * γ * singularValues A k ^ 2 +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt γ) *
          specNorm ((A - truncatedSVD A k) * Ω * pinv (Zᴴ * Ω)) ^ 2 := sorry

end NLAlib
