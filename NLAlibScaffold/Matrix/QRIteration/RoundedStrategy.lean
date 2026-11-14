/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.Ritz
public import NLAlib.Matrix.QRIteration.Strategy
public import NLAlib.Matrix.QRIteration.Dichotomy
public import NLAlib.Matrix.Perturbation.UnitarySimilarity

/-!
# The shifting strategy with computed quantities

The shifting strategy $\mathrm{Sh}_{k,B}$ of [BanksGarzaVargasSrivastava2021] decides from exact
quantities: the norm $\|\mathbf{e}_n^{\mathsf T}p(\mathbf{H})\|$ (is a set of Ritz values
$\theta$-optimal?), the values $\tau_p(\mathbf{H})$ (which half of the Ritz values is promising?),
and the potential. In floating point each is computed with a small relative error
[BanksGarzaVargasSrivastava2022, §§4–6]. This file states the decisions with computed values as
mathematics, with the computed value a hypothesis "within a relative error of the exact one":

* the optimality test (`Optimal`, Lemma 4.5): a computed norm within $0.0009\,\theta^k\psi^k$
  decides between $\theta$-optimal and not $0.998^{1/k}\theta$-optimal;
* the dichotomy used by `Regularize` (Lemma 4.6, with the constant of Theorem 4.1 corrected,
  G10): forward-approximate Ritz values that are not optimal contain a shift whose degree $k$
  step decouples;
* `Find` with computed $\tau$ values (Lemma 5.1): the promising factor becomes
  $(1.01B)^{4\log_2 k / k}$;
* the while loop of `ShQR` (Lemma 6.4) as an abstract contraction: steps that each decouple or
  contract the potential, with backward errors that add.

The programs computing these values, and the precision under which the hypotheses hold, are in
the finite-precision shifted QR layer of `NLAlib/Eigensolvers/ShiftedQR`.

## Main definitions

* `NLAlib.findRitzWith`: `Find` with a supplied comparison value per half.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- **The optimality test with a computed norm, positive branch** (Optimal,
[BanksGarzaVargasSrivastava2022, Lemma 4.5]): if the computed value $t$ is within
$0.0009\,(\theta\psi_k)^k$ of $\|\mathbf{e}_n^{\mathsf T}p(\mathbf{H})\|$ and
$t < 0.999(\theta\psi_k)^k$, the shifts are $\theta$-optimal. -/
theorem isOptimalRitzValues_of_lt {θ t : ℝ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ}
    (ht : |t - ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss)) (Fin.last n))‖| ≤
      0.0009 * (θ * hessenbergPotential ss.length H) ^ ss.length)
    (hlt : t < 0.999 * (θ * hessenbergPotential ss.length H) ^ ss.length) :
    IsOptimalRitzValues θ H ss := by
  have h0 : 0 ≤ 0.0009 * (θ * hessenbergPotential ss.length H) ^ ss.length :=
    (abs_nonneg _).trans ht
  have hX : 0 ≤ (θ * hessenbergPotential ss.length H) ^ ss.length := by
    linarith
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  unfold IsOptimalRitzValues
  linarith

/-- **The optimality test with a computed norm, negative branch** (Optimal,
[BanksGarzaVargasSrivastava2022, Lemma 4.5]): if $t \ge 0.999(\theta\psi_k)^k$ with the same
accuracy, positive $\theta$ and potential, and at least one shift, the shifts are not
$0.998^{1/k}\theta$-optimal. -/
theorem not_isOptimalRitzValues_of_le {θ t : ℝ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ} (hθ : 0 < θ) (hψ : 0 < hessenbergPotential ss.length H) (hss : ss ≠ [])
    (ht : |t - ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss)) (Fin.last n))‖| ≤
      0.0009 * (θ * hessenbergPotential ss.length H) ^ ss.length)
    (hle : 0.999 * (θ * hessenbergPotential ss.length H) ^ ss.length ≤ t) :
    ¬IsOptimalRitzValues ((0.998 : ℝ) ^ ((ss.length : ℝ)⁻¹) * θ) H ss := by
  intro hopt
  unfold IsOptimalRitzValues at hopt
  have hk : ss.length ≠ 0 := by simpa using hss
  have hX : 0 < (θ * hessenbergPotential ss.length H) ^ ss.length :=
    pow_pos (mul_pos hθ hψ) _
  have hpow : ((0.998 : ℝ) ^ ((ss.length : ℝ)⁻¹) * θ * hessenbergPotential ss.length H) ^ ss.length
      = 0.998 * (θ * hessenbergPotential ss.length H) ^ ss.length := by
    rw [mul_assoc, mul_pow, Real.rpow_inv_natCast_pow (by norm_num) hk]
  rw [hpow] at hopt
  have h1 := (abs_le.mp ht).2
  linarith

/-- **Forward-approximate Ritz values that are not optimal contain a decoupling shift**
(the dichotomy as `Regularize` uses it, [BanksGarzaVargasSrivastava2022, Theorem 4.1 and
Lemma 4.6], with the forward accuracy
$\beta = \omega^2/(20 \cdot 101\,\Sigma)$ in place of $\omega^2/(16 \cdot 101\,\Sigma)$): let
$\mathbf{H}$ be upper Hessenberg, $\mathbf{H}\mathbf{V} = \mathbf{V}\mathbf{D}$ with
$\kappa(\mathbf{V}) \le B$, $B \ge 1$, eigenvalues at mutual distance at least
$2\omega^2/\Sigma$, $\|\mathbf{H}\|_2 \le \Sigma$, $\omega \le \psi_k(\mathbf{H})$ ($\mathbf{H}$
is $\omega$-unreduced at the bottom), the $k \ge 1$ shifts
within $\beta$ of the Ritz values in some order and no shift an eigenvalue, and
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, and $B^{2/k} \le 2$ (the choice of $k$).
If the shifts are not
$0.998^{1/k}\theta$-optimal, some shift $r$ has $\tau_{(z - r)^k}(\mathbf{H}) \le \omega / 2$,
i.e. $\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - r)^{-k}\| \ge (2/\omega)^k$. This is what the exact
dichotomy (`IsUpperHessenberg.isOptimalRitzValues_or_exists_mem_det_eq_zero_or_le`, constant
$\tfrac25$) gives; it suffices, since the forward error $\omega/2$ then reaches the threshold
$\le \omega$ that the loop and Deflate test. The sharp constant $\tfrac12 k^{-1/(2k)}$ would give
$2.08/\omega$. -/
theorem exists_mem_le_norm_inv_pow_of_not_isOptimalRitzValues {B S ω : ℝ} {k : ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ}
    (hH : IsUpperHessenberg H) (hk : 0 < k) (hkn : k ≤ n) (hB : 1 ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖) (hS : specNorm H ≤ S)
    (hψ : ω ≤ hessenbergPotential k H)
    (hss : List.Forall₂ (fun r ρ => ‖r - ρ‖ ≤ ω ^ 2 / (20 * 101 * S)) ss (ritzValues k H))
    (hne : ∀ r ∈ ss, ∀ i, e i ≠ r)
    (hopt : ¬IsOptimalRitzValues ((0.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹))) H ss) :
    ∃ r ∈ ss, (2 / ω) ^ k ≤
      ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖ := by
  set κ := pseudoConditionNumber V
  set Y := (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)
  set x := (2 * κ ^ 4) ^ ((2 * k : ℝ)⁻¹)
  set θ := (0.998 : ℝ) ^ ((k : ℝ)⁻¹) * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * Y)
  have hκ1 : 1 ≤ κ := one_le_pseudoConditionNumber hV.ne_zero
  have hθ : θ = 1.01 * Y := by
    simp only [θ]
    rw [Real.rpow_neg (by norm_num)]
    have : (0.998 : ℝ) ^ ((k : ℝ)⁻¹) ≠ 0 := by positivity
    field_simp
  have hx0 : 0 < x := by positivity
  have hxY : x ≤ Y := Real.rpow_le_rpow (by positivity) (by gcongr) (by positivity)
  have hxθ : x / θ ≤ 100 / 101 := by
    rw [hθ, div_le_iff₀ (by positivity)]
    linarith
  have hψH := hessenbergPotential_le_specNorm hk hkn H
  have hS0 : 0 < S := by linarith
  have hc : 1 / 200 ≤ (θ / x - 1) / 2 := by
    rw [le_div_iff₀ (by norm_num), le_sub_iff_add_le, le_div_iff₀ hx0, hθ]
    linarith
  have hβ : 0 < ω ^ 2 / (20 * 101 * S) := by positivity
  have hβΓ : ω ^ 2 / (20 * 101 * S) < (θ / x - 1) / 2 * (2 * ω ^ 2 / S) := by
    calc ω ^ 2 / (20 * 101 * S) < 1 / 200 * (2 * ω ^ 2 / S) := by
          rw [div_lt_iff₀ (by positivity)]
          field_simp
          nlinarith [pow_pos hω 2]
      _ ≤ _ := by gcongr
  rcases hH.isOptimalRitzValues_or_exists_mem_det_eq_zero_or_le hV hHV hk hkn hgap
      (hxY.trans_lt (by rw [hθ]; linarith [show 0 < Y by positivity]) : x < θ) hβ hβΓ
      (List.Forall₂.flip (hss.imp fun _ _ h => by rwa [norm_sub_rev] at h))
      with hopt' | ⟨r, hr, hdet | hle⟩
  · exact absurd hopt' hopt
  · exact absurd hdet (det_sub_smul_one_ne_zero_of_forall_ne hV hHV (hne r hr))
  refine ⟨r, hr, ?_⟩
  rw [aeval_shiftPoly_replicate, ← Matrix.inv_pow']
  set N := ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k)
    (Fin.last n))‖
  set β := ω ^ 2 / (20 * 101 * S)
  have hN0 : 0 ≤ N ^ ((k : ℝ)⁻¹) := by positivity
  have hκk : κ ^ ((2 : ℝ) / k) ≤ 2 :=
    (Real.rpow_le_rpow (by positivity) hκ (by positivity)).trans hBk
  have hβS : specNorm H + β ≤ 2 * S := by
    have : β ≤ S := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hlow : 2 * ω / 505 ≤ ω ^ 2 / 505 * N ^ ((k : ℝ)⁻¹) := by
    calc 2 * ω / 505 ≤ 2 / 5 * hessenbergPotential k H * (1 - x / θ) := by
          nlinarith
      _ ≤ _ := hle
      _ ≤ 2 * (2 * S) * β * N ^ ((k : ℝ)⁻¹) := by gcongr
      _ = _ := by
          simp only [β]
          field_simp
          ring
  have h2 : 2 / ω ≤ N ^ ((k : ℝ)⁻¹) := by
    rw [div_le_iff₀ hω]
    nlinarith
  calc (2 / ω) ^ k ≤ (N ^ ((k : ℝ)⁻¹)) ^ k := by gcongr
    _ = N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), inv_mul_cancel₀ (by positivity),
        Real.rpow_one]

/-- `Find` with supplied comparison values: `findRitzWith t m e ss` splits `ss` into its first
and second halves, keeps the half $h$ with the smaller value `t e h` (the first on a tie; `t e h`
stands for a computed $\tau_{p_h^e}(\mathbf{H})^{\deg}$, i.e. a computed
$\|\mathbf{e}_n^{\mathsf T}p_h(\mathbf{H})^{-e}\|^{-1}$), and recurses with exponent $2e$. With
the exact values it is `NLAlib.findRitz`. [BanksGarzaVargasSrivastava2022, §5]. -/
noncomputable def findRitzWith (t : ℕ → List ℂ → ℝ) : ℕ → ℕ → List ℂ → ℂ
  | 0, _, ss => ss.headD 0
  | m + 1, e, ss =>
    if t e (ss.take (ss.length / 2)) ≤ t e (ss.drop (ss.length / 2)) then
      findRitzWith t m (2 * e) (ss.take (ss.length / 2))
    else
      findRitzWith t m (2 * e) (ss.drop (ss.length / 2))

/-- The last row of an inverse power of a shift polynomial with no root at an eigenvalue is
nonzero. -/
private theorem norm_toLp_inv_aeval_pow_last_pos {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) (q : ℕ)
    {l : List ℂ} (hl : ∀ i, (shiftPoly l).eval (d i) ≠ 0) :
    0 < ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly l))⁻¹ ^ q) (Fin.last n))‖ := by
  have hA : (Polynomial.aeval H (shiftPoly l))⁻¹ ^ q =
      V * Matrix.diagonal (fun i => ((shiftPoly l).eval (d i))⁻¹ ^ q) * V⁻¹ := by
    rw [inv_aeval_eq_mul_diagonal_mul_inv hV hHV hl, mul_diagonal_mul_inv_pow hV]
    rfl
  have hle := sum_lastRowWeights_mul_sq_le hV (fun i => ((shiftPoly l).eval (d i))⁻¹ ^ q)
  have hX : 0 < ∑ i, lastRowWeights V i * ‖((shiftPoly l).eval (d i))⁻¹ ^ q‖ ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, 0 < lastRowWeights V i := by
      by_contra hc
      push Not at hc
      have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hc i
      rw [sum_lastRowWeights hV] at this
      norm_num at this
    exact Finset.sum_pos' (fun j _ => by have := lastRowWeights_nonneg V j; positivity)
      ⟨i, Finset.mem_univ _, mul_pos hi (by
        simp only [norm_pow, norm_inv]
        exact pow_pos (pow_pos (inv_pos.mpr (norm_pos_iff.mpr (hl i))) q) 2)⟩
  rw [hA]
  refine (norm_nonneg _).lt_of_ne fun h0 => ?_
  rw [← h0] at hle
  linarith

/-- One halving step with comparisons up to the factor $c$: the moment of the concatenation is
at most $c^2\kappa^4$ times the moment of the kept half, with doubled exponent. -/
private theorem sum_div_shiftPoly_append_le_of_le_mul
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) {a b h : List ℂ} (hd : ∀ i, ∀ s ∈ a ++ b, d i ≠ s)
    (hh : h = a ∨ h = b) (q : ℕ) {c : ℝ}
    (hmax : ∀ g ∈ [a, b],
      ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly g))⁻¹ ^ q) (Fin.last n))‖ ≤
        c * ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ q) (Fin.last n))‖) :
    ∑ i, lastRowWeights V i / ‖(shiftPoly (a ++ b)).eval (d i)‖ ^ q ≤
      c ^ 2 * pseudoConditionNumber V ^ 4 *
        ∑ i, lastRowWeights V i / ‖(shiftPoly h).eval (d i)‖ ^ (2 * q) := by
  have hne : ∀ l : List ℂ, (∀ i, ∀ s ∈ l, d i ≠ s) → ∀ i, (shiftPoly l).eval (d i) ≠ 0 :=
    fun _ hl i => eval_shiftPoly_ne_zero (hl i)
  have hna : ∀ i, (shiftPoly a).eval (d i) ≠ 0 :=
    hne a fun i s hs => hd i s (List.mem_append_left _ hs)
  have hnb : ∀ i, (shiftPoly b).eval (d i) ≠ 0 :=
    hne b fun i s hs => hd i s (List.mem_append_right _ hs)
  have hnh : ∀ i, (shiftPoly h).eval (d i) ≠ 0 := by
    rcases hh with rfl | rfl
    · exact hna
    · exact hnb
  -- the two-sided moment bounds
  have hsand : ∀ l : List ℂ, (∀ i, (shiftPoly l).eval (d i) ≠ 0) →
      ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly l))⁻¹ ^ q) (Fin.last n))‖ ^ 2 ≤
          pseudoConditionNumber V ^ 2 *
            ∑ i, lastRowWeights V i * ‖((shiftPoly l).eval (d i))⁻¹ ^ q‖ ^ 2 ∧
        ∑ i, lastRowWeights V i * ‖((shiftPoly l).eval (d i))⁻¹ ^ q‖ ^ 2 ≤
          pseudoConditionNumber V ^ 2 *
            ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly l))⁻¹ ^ q) (Fin.last n))‖ ^ 2 := by
    intro l hl
    have hA : (Polynomial.aeval H (shiftPoly l))⁻¹ ^ q =
        V * Matrix.diagonal (fun i => ((shiftPoly l).eval (d i))⁻¹ ^ q) * V⁻¹ := by
      rw [inv_aeval_eq_mul_diagonal_mul_inv hV hHV hl, mul_diagonal_mul_inv_pow hV]
      rfl
    rw [hA]
    exact ⟨norm_mul_diagonal_mul_inv_last_sq_le hV _, sum_lastRowWeights_mul_sq_le hV _⟩
  have hpt : ∀ i, lastRowWeights V i / ‖(shiftPoly (a ++ b)).eval (d i)‖ ^ q ≤
      lastRowWeights V i * (‖((shiftPoly a).eval (d i))⁻¹ ^ q‖ ^ 2 +
        ‖((shiftPoly b).eval (d i))⁻¹ ^ q‖ ^ 2) / 2 := by
    intro i
    rw [shiftPoly_append, Polynomial.eval_mul, norm_mul]
    simp only [norm_pow, norm_inv]
    have hw := lastRowWeights_nonneg V i
    set x := ‖(shiftPoly a).eval (d i)‖
    set y := ‖(shiftPoly b).eval (d i)‖
    have huv : ((x * y) ^ q)⁻¹ = (x⁻¹) ^ q * (y⁻¹) ^ q := by
      rw [mul_pow, mul_inv, inv_pow, inv_pow]
    have ham : (x⁻¹) ^ q * (y⁻¹) ^ q ≤ (((x⁻¹) ^ q) ^ 2 + ((y⁻¹) ^ q) ^ 2) / 2 := by
      nlinarith [sq_nonneg ((x⁻¹) ^ q - (y⁻¹) ^ q)]
    rw [div_eq_mul_inv, huv]
    nlinarith [mul_le_mul_of_nonneg_left ham hw]
  have hsumh : ∑ i, lastRowWeights V i / ‖(shiftPoly h).eval (d i)‖ ^ (2 * q) =
      ∑ i, lastRowWeights V i * ‖((shiftPoly h).eval (d i))⁻¹ ^ q‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_pow, norm_inv, ← pow_mul, inv_pow, div_eq_mul_inv, mul_comm 2 q]
  rw [hsumh]
  obtain ⟨hKh, hXh⟩ := hsand h hnh
  -- a moment of `g ∈ {a, b}` is at most `c²κ⁴` times the moment of `h`
  have hmom : ∀ g ∈ [a, b], (∀ i, (shiftPoly g).eval (d i) ≠ 0) →
      ∑ i, lastRowWeights V i * ‖((shiftPoly g).eval (d i))⁻¹ ^ q‖ ^ 2 ≤
        c ^ 2 * pseudoConditionNumber V ^ 4 *
          ∑ i, lastRowWeights V i * ‖((shiftPoly h).eval (d i))⁻¹ ^ q‖ ^ 2 := by
    intro g hg hng
    have hKg := (hsand g hng).2
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hmax g hg) 2
    calc _ ≤ _ := hKg
      _ ≤ pseudoConditionNumber V ^ 2 * (c * ‖WithLp.toLp 2
            (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ q) (Fin.last n))‖) ^ 2 := by gcongr
      _ ≤ pseudoConditionNumber V ^ 2 * (c ^ 2 * (pseudoConditionNumber V ^ 2 *
            ∑ i, lastRowWeights V i * ‖((shiftPoly h).eval (d i))⁻¹ ^ q‖ ^ 2)) := by
          rw [mul_pow]; gcongr
      _ = _ := by ring
  have hXa' := hmom a (by simp) hna
  have hXb' := hmom b (by simp) hnb
  calc ∑ i, lastRowWeights V i / ‖(shiftPoly (a ++ b)).eval (d i)‖ ^ q
      ≤ ∑ i, lastRowWeights V i * (‖((shiftPoly a).eval (d i))⁻¹ ^ q‖ ^ 2 +
          ‖((shiftPoly b).eval (d i))⁻¹ ^ q‖ ^ 2) / 2 := Finset.sum_le_sum fun i _ => hpt i
    _ = (∑ i, lastRowWeights V i * ‖((shiftPoly a).eval (d i))⁻¹ ^ q‖ ^ 2 +
          ∑ i, lastRowWeights V i * ‖((shiftPoly b).eval (d i))⁻¹ ^ q‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by linarith

/-- `NLAlib.findRitzWith` returns a member of a list of length $2^m$. -/
private theorem findRitzWith_mem (t : ℕ → List ℂ → ℝ) {m f : ℕ} {ss : List ℂ}
    (hss : ss.length = 2 ^ m) : findRitzWith t m f ss ∈ ss := by
  induction m generalizing f ss with
  | zero =>
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hss)
    simp [findRitzWith]
  | succ m ih =>
    have hlen : ss.length / 2 = 2 ^ m := by rw [hss, pow_succ]; omega
    rw [findRitzWith]
    split_ifs
    · exact List.mem_of_mem_take (ih (by rw [List.length_take, hlen, hss, pow_succ]; omega))
    · exact List.mem_of_mem_drop (ih (by rw [List.length_drop, hss, pow_succ]; omega))

/-- `NLAlib.findRitzWith` keeps the moment bound with the factor $c^2\kappa^4$ per level, where
$c = 1.0011/0.9989$ is the loss of one comparison of computed values. -/
private theorem sum_div_le_findRitzWith {t : ℕ → List ℂ → ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d)
    (ht : ∀ f (h : List ℂ), |t f h -
      ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ f) (Fin.last n))‖⁻¹| ≤
        0.0011 * ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ f) (Fin.last n))‖⁻¹)
    (m : ℕ) :
    ∀ (f : ℕ) (ss : List ℂ), ss.length = 2 ^ m → (∀ i, ∀ s ∈ ss, d i ≠ s) →
      ∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖ ^ f ≤
        ((1.0011 / 0.9989 : ℝ) ^ 2 * pseudoConditionNumber V ^ 4) ^ m *
          ∑ i, lastRowWeights V i / ‖d i - findRitzWith t m f ss‖ ^ (f * 2 ^ m) := by
  induction m with
  | zero =>
    intro f ss hlen hd
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hlen)
    simp [shiftPoly, findRitzWith]
  | succ j ih =>
    intro f ss hlen hd
    set a := ss.take (ss.length / 2)
    set b := ss.drop (ss.length / 2)
    have hhalf : ss.length / 2 = 2 ^ j := by
      rw [hlen, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have ha : a.length = 2 ^ j := by
      rw [List.length_take, hhalf, hlen]
      exact Nat.min_eq_left (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hb : b.length = 2 ^ j := by
      rw [List.length_drop, hhalf, hlen, pow_succ]
      omega
    have hdis : ∀ i, ∀ s ∈ a ++ b, d i ≠ s := by simpa only [a, b, List.take_append_drop] using hd
    have hpos : ∀ g ∈ [a, b],
        0 < ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly g))⁻¹ ^ f) (Fin.last n))‖ := by
      intro g hg
      refine norm_toLp_inv_aeval_pow_last_pos hV hHV f fun i => eval_shiftPoly_ne_zero ?_
      intro s hs
      rcases List.mem_pair.mp hg with rfl | rfl
      exacts [hdis i s (List.mem_append_left _ hs), hdis i s (List.mem_append_right _ hs)]
    -- one comparison of computed values loses at most the factor `c`
    have hcmp : ∀ g h : List ℂ, g ∈ [a, b] → h ∈ [a, b] → t f h ≤ t f g →
        ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly g))⁻¹ ^ f) (Fin.last n))‖ ≤
          1.0011 / 0.9989 *
            ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ f) (Fin.last n))‖ := by
      intro g h hg hh hle
      have hNg := hpos g hg
      have hNh := hpos h hh
      set Ng := ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly g))⁻¹ ^ f) (Fin.last n))‖
      set Nh := ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ f) (Fin.last n))‖
      have h1 := (abs_le.mp (ht f g)).2
      have h2 := (abs_le.mp (ht f h)).1
      have hineq : 0.9989 * Nh⁻¹ ≤ 1.0011 * Ng⁻¹ := by linarith
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
      have := mul_le_mul_of_nonneg_left hineq (mul_nonneg hNg.le hNh.le)
      field_simp at this
      linarith
    obtain ⟨h, hh, hlh, hfr, hmax⟩ : ∃ h : List ℂ, (h = a ∨ h = b) ∧ h.length = 2 ^ j ∧
        findRitzWith t (j + 1) f ss = findRitzWith t j (2 * f) h ∧ ∀ g ∈ [a, b],
          ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly g))⁻¹ ^ f) (Fin.last n))‖ ≤
            1.0011 / 0.9989 *
              ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ f) (Fin.last n))‖ := by
      by_cases hc : t f a ≤ t f b
      · refine ⟨a, Or.inl rfl, ha, by rw [findRitzWith, if_pos hc], fun g hg => ?_⟩
        rcases List.mem_pair.mp hg with rfl | rfl
        exacts [hcmp _ _ (by simp) (by simp) le_rfl, hcmp _ _ (by simp) (by simp) hc]
      · refine ⟨b, Or.inr rfl, hb, by rw [findRitzWith, if_neg hc], fun g hg => ?_⟩
        rcases List.mem_pair.mp hg with rfl | rfl
        exacts [hcmp _ _ (by simp) (by simp) (not_le.mp hc).le,
          hcmp _ _ (by simp) (by simp) le_rfl]
    have hih := ih (2 * f) h hlh fun i s hs =>
      hdis i s (by rcases hh with rfl | rfl <;> simp [hs])
    rw [show ∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖ ^ f =
        ∑ i, lastRowWeights V i / ‖(shiftPoly (a ++ b)).eval (d i)‖ ^ f by
      rw [List.take_append_drop], hfr, show f * 2 ^ (j + 1) = 2 * f * 2 ^ j by ring]
    calc _ ≤ _ := sum_div_shiftPoly_append_le_of_le_mul hV hHV hdis hh f hmax
      _ ≤ (1.0011 / 0.9989 : ℝ) ^ 2 * pseudoConditionNumber V ^ 4 *
          (((1.0011 / 0.9989 : ℝ) ^ 2 * pseudoConditionNumber V ^ 4) ^ j *
            ∑ i, lastRowWeights V i / ‖d i - findRitzWith t j (2 * f) h‖ ^ (2 * f * 2 ^ j)) :=
        mul_le_mul_of_nonneg_left hih (by positivity)
      _ = _ := by ring

/-- **`Find` with computed values is promising** ([BanksGarzaVargasSrivastava2022, Lemma 5.1]):
if every comparison value is within the relative error $0.0011$ of
$\|\mathbf{e}_n^{\mathsf T}p_h(\mathbf{H})^{-e}\|^{-1}$, then for $2^m$ shifts, none an
eigenvalue, and $\kappa(\mathbf{V}) \le B$, the result is
$(1.01B)^{4m/2^m}$-promising (the exact `Find` is $B^{4m/2^m}$-promising). -/
theorem isPromisingRitzValue_findRitzWith {B : ℝ} {m : ℕ} {t : ℕ → List ℂ → ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hlen : ss.length = 2 ^ m) (hne : ∀ r ∈ ss, ∀ i, e i ≠ r)
    (ht : ∀ f (h : List ℂ), |t f h -
      ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ f) (Fin.last n))‖⁻¹| ≤
        0.0011 * ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ f) (Fin.last n))‖⁻¹) :
    IsPromisingRitzValue ((1.01 * B) ^ ((4 * m : ℝ) / 2 ^ m)) V e ss (findRitzWith t m 1 ss) := by
  have hcard := sum_div_le_findRitzWith hV hHV ht m 1 ss hlen fun i s hs => hne s hs i
  simp only [pow_one, one_mul] at hcard
  have hS0 : 0 ≤ ∑ i, lastRowWeights V i / ‖e i - findRitzWith t m 1 ss‖ ^ 2 ^ m :=
    Finset.sum_nonneg fun i _ => div_nonneg (lastRowWeights_nonneg V i) (by positivity)
  have hκ0 := pseudoConditionNumber_nonneg V
  have hB0 : 0 ≤ B := hκ0.trans hκ
  refine ⟨findRitzWith_mem t hlen, ?_⟩
  rw [hlen]
  have hα : ((1.01 * B) ^ ((4 * m : ℝ) / 2 ^ m)) ^ (2 ^ m : ℕ) = ((1.01 * B) ^ 4) ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← pow_mul,
      ← Real.rpow_natCast (1.01 * B) (4 * m)]
    congr 1
    push_cast
    field_simp
  rw [hα]
  refine hcard.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ m) hS0)
  rw [mul_pow]
  gcongr
  norm_num

/-- The arithmetic of the averaging step over a covering of at most $9/\varepsilon^2$ shifts:
the weight bound with $t = 1/1.998$, the averaging and the moment bound at the chosen point give
$1 \le ((1 - \gamma)\psi)^k x$. -/
private theorem one_le_pow_mul_of_le_card_mul_sum_of_covers {k : ℕ}
    {B θ α ξ γ ψ ε R x P N f : ℝ} (hB : 0 < B) (hθ : 0 < θ) (hα : 0 < α) (hξ : 0 < ξ)
    (hγ1 : γ < 1) (hψ : 0 < ψ) (hx : 0 ≤ x) (hε0 : 0 < ε) (hR0 : 0 < R)
    (hε : ε ^ (2 * k) = ε ^ 2 * ((ξ * (1 - γ)) ^ k / (13 * B ^ 4 * (α * θ) ^ (2 * k))) ^ 2)
    (hRk : R ^ k ≤ 2.002 * B * (θ * α * ψ) ^ k)
    (hP : (1 - 1 / 1.998) ^ 2 * ξ ^ (2 * k) ≤ B ^ 4 * (α * θ) ^ (2 * k) * P)
    (hsle : P / (ε * R) ^ (2 * k) ≤ N * f) (hN : N ≤ 9 / ε ^ 2) (hf0 : 0 ≤ f)
    (hf : f ≤ B ^ 2 * x ^ 2) :
    1 ≤ ((1 - γ) * ψ) ^ k * x := by
  have h1 : P ≤ (9 / ε ^ 2) * (B ^ 2 * x ^ 2) * (ε * R) ^ (2 * k) := by
    calc P ≤ _ := (div_le_iff₀ (by positivity)).mp hsle
      _ ≤ _ := by gcongr
  have hR2 : (ε * R) ^ (2 * k) ≤ ε ^ 2 * ((ξ * (1 - γ)) ^ k / (13 * B ^ 4 * (α * θ) ^ (2 * k))) ^ 2
      * (2.002 * B * (θ * α * ψ) ^ k) ^ 2 := by
    rw [mul_pow ε R, hε, mul_comm 2 k, pow_mul R]
    gcongr
  have h2 : (1 - 1 / 1.998) ^ 2 * ξ ^ (2 * k) ≤
      9 * 2.002 ^ 2 / 169 * ξ ^ (2 * k) * (((1 - γ) * ψ) ^ k * x) ^ 2 := by
    calc (1 - 1 / 1.998) ^ 2 * ξ ^ (2 * k) ≤ B ^ 4 * (α * θ) ^ (2 * k) * P := hP
      _ ≤ B ^ 4 * (α * θ) ^ (2 * k) * ((9 / ε ^ 2) * (B ^ 2 * x ^ 2) *
          (ε ^ 2 * ((ξ * (1 - γ)) ^ k / (13 * B ^ 4 * (α * θ) ^ (2 * k))) ^ 2
            * (2.002 * B * (θ * α * ψ) ^ k) ^ 2)) := by gcongr; exact h1.trans (by gcongr)
      _ = _ := by
          simp only [mul_pow, ← pow_mul]
          field_simp
          ring
  have hy : 0 ≤ ((1 - γ) * ψ) ^ k * x := mul_nonneg (pow_nonneg (by nlinarith) _) hx
  have h3 : (1 - 1 / 1.998 : ℝ) ^ 2 ≤ 9 * 2.002 ^ 2 / 169 * (((1 - γ) * ψ) ^ k * x) ^ 2 :=
    le_of_mul_le_mul_right (by linarith [h2]) (by positivity : 0 < ξ ^ (2 * k))
  by_contra h
  have := pow_lt_one₀ hy (not_le.mp h) two_ne_zero
  nlinarith

/-- The spacing and radius of `NLAlib.exists_mem_le_norm_inv_pow_of_covers`: for $k \ge 2$,
$\varepsilon = b^{k/(k-1)}$ with $b = \xi(1-\gamma)/((13B^4)^{1/k}\alpha^2\theta^2) > 0$ is
positive with $\varepsilon^{2k} = \varepsilon^2(b^k)^2$, and
$\tilde R \le 2.002^{1/k}\theta\alpha B^{1/k}\psi$ gives
$\tilde R^k \le 2.002B(\theta\alpha\psi)^k$. -/
private theorem spacing_pow_and_radius_pow_le_of_covers {B θ α ξ γ ψ R ε : ℝ} {k : ℕ}
    (hk : 2 ≤ k) (hB : 0 < B) (hθ : 0 < θ) (hα : 0 < α) (hξ : 0 < ξ) (hγ1 : γ < 1)
    (hR0 : 0 ≤ R)
    (hRhi : R ≤ (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * ψ)
    (hε : ε = (ξ * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^
      ((k : ℝ) / (k - 1))) :
    0 < ε ∧ ε ^ (2 * k) = ε ^ 2 * ((ξ * (1 - γ)) ^ k / (13 * B ^ 4 * (α * θ) ^ (2 * k))) ^ 2 ∧
      R ^ k ≤ 2.002 * B * (θ * α * ψ) ^ k := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hγ' : 0 < 1 - γ := by linarith
  have hrpow : ∀ c : ℝ, 0 ≤ c → (c ^ ((k : ℝ)⁻¹)) ^ k = c := fun c hc => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc, inv_mul_cancel₀ hk0.ne', Real.rpow_one]
  set b := ξ * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2) with hb_def
  have hb0 : 0 < b := by positivity
  have hεk : ε ^ (k - 1) = b ^ k := by
    rw [hε, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le, Nat.cast_sub (by omega), Nat.cast_one,
      div_mul_cancel₀ _ (by linarith), Real.rpow_natCast]
  refine ⟨hε ▸ Real.rpow_pos_of_pos hb0 _, ?_, ?_⟩
  · have hbk : b ^ k = (ξ * (1 - γ)) ^ k / (13 * B ^ 4 * (α * θ) ^ (2 * k)) := by
      simp only [hb_def, div_pow, mul_pow, hrpow _ (by positivity : (0 : ℝ) ≤ 13 * B ^ 4)]
      ring
    rw [← hbk, ← hεk, ← pow_mul, ← pow_add]
    congr 1
    omega
  · refine (pow_le_pow_left₀ hR0 hRhi k).trans (le_of_eq ?_)
    simp only [mul_pow, hrpow _ (by norm_num : (0 : ℝ) ≤ 2.002), hrpow _ hB.le]
    ring

/-- **The exceptional shifts contain a contracting shift** (the deterministic core of `Exc`,
[BanksGarzaVargasSrivastava2022, Lemma 5.3], with the corrections of G13): let
$\mathbf{H}\mathbf{V} = \mathbf{V}\mathbf{D}$ with $\kappa(\mathbf{V}) \le B$, the $k \ge 2$ shifts
`ss` be $\theta$-optimal, none an eigenvalue, $r$ an $\alpha$-promising one with
$\tau_{(z - r)^k}(\mathbf{H}) \ge \xi\psi_k(\mathbf{H})$, $\psi_k(\mathbf{H}) > 0$, the radius
$\tilde R$ within $[1.998^{1/k}, 2.002^{1/k}]\,\theta\alpha B^{1/k}\psi_k(\mathbf{H})$
(the computed radius from $\tilde\psi$ within $0.001/k$, as the paper's
(eq:boundonpottilde); the paper's upper bound omits $2^{1/k}$, and a flat $1.001$ breaks the
constant $13$ for $k \ge 60$),
$\varepsilon = (\xi(1 - \gamma)/((13B^4)^{1/k}\alpha^2\theta^2))^{k/(k-1)} \le 1/2$, and $S$ a
set of at most $9/\varepsilon^2$ shifts covering $\mathbb{D}(r, \tilde R)$ at radius
$\varepsilon\tilde R$, none an eigenvalue. Then some $s \in S$ has
$\tau_{(z - s)^k}(\mathbf{H}) \le (1 - \gamma)\psi_k(\mathbf{H})$. The covering is of the disk
itself: the paper's intersection of the net with $\mathbb{D}(r, \tilde R)$ can drop the points
that cover its boundary, and its rounding budget $0.1\varepsilon\tilde R$ exceeds the covering
slack; the program covers $\mathbb{D}(r, (1 + \varepsilon)\tilde R)$ and rounds within
$0.005\varepsilon\tilde R$. Without "none an eigenvalue" the statement is false: for $r$ an
eigenvalue the stagnation hypothesis is vacuous (the inverse is Lean's $0$). -/
theorem exists_mem_le_norm_inv_pow_of_covers {B θ α ξ γ R ε : ℝ} {k : ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ} {r : ℂ}
    {S : Finset ℂ} (hk : 2 ≤ k) (hkn : k ≤ n) (hlen : ss.length = k)
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hopt : IsOptimalRitzValues θ H ss) (hr : IsPromisingRitzValue α V e ss r)
    (hd : ∀ i, ∀ s ∈ ss, e i ≠ s) (hψ : 0 < hessenbergPotential k H) (hγ : 0 < γ)
    (hγ1 : γ < 1) (hξ : 0 < ξ) (hθ : 1 ≤ θ) (hα : 1 ≤ α)
    (hτ : ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹
      (Fin.last n))‖ ≤ (ξ * hessenbergPotential k H)⁻¹ ^ k)
    (hRlo : (1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H ≤ R)
    (hRhi : R ≤ (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H)
    (hε : ε = (ξ * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^
      ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2)
    (hcover : ∀ z : ℂ, ‖z - r‖ ≤ R → ∃ s ∈ S, ‖z - s‖ ≤ ε * R)
    (hcard : (S.card : ℝ) ≤ 9 / ε ^ 2) (hne : ∀ s ∈ S, ∀ i, e i ≠ s) :
    ∃ s ∈ S, ((1 - γ) * hessenbergPotential k H)⁻¹ ^ k ≤
      ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly (List.replicate k s)))⁻¹ (Fin.last n))‖ := by
  subst hlen
  set k := ss.length with hk_def
  set ψ := hessenbergPotential k H with hψ_def
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hRlo
  obtain ⟨hε0, hε2k, hRk⟩ := spacing_pow_and_radius_pow_le_of_covers hk (by linarith)
    (by linarith) (by linarith) hξ hγ1 hR0.le hRhi hε
  -- stagnation of `r`
  have hstag : ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^
      k) (Fin.last n))‖ * (ξ * ψ) ^ k ≤ 1 := by
    rw [aeval_shiftPoly_replicate, ← Matrix.inv_pow', inv_pow] at hτ
    rwa [← le_div_iff₀ (by positivity), one_div]
  -- the weight on the disk, by Paley–Zygmund with `t = 1/1.998`
  set W := Finset.univ.filter (fun i => ‖e i - r‖ ≤ R) with hW_def
  have hP : (1 - 1 / 1.998) ^ 2 * ξ ^ (2 * k) ≤
      B ^ 4 * (α * θ) ^ (2 * k) * ∑ i ∈ W, lastRowWeights V i := by
    have h := hopt.sq_mul_pow_le_mul_sum_lastRowWeights_filter hV hHV hd hr (by linarith)
      (by linarith) hξ (by norm_num : (0 : ℝ) < 1 / 1.998) (by norm_num) hψ hstag
    refine h.trans ?_
    gcongr ?_ * _ * ?_
    · exact Finset.sum_nonneg fun i _ => lastRowWeights_nonneg V i
    · exact pow_le_pow_left₀ (pseudoConditionNumber_nonneg V) hκ 4
    · refine Finset.sum_le_sum_of_subset_of_nonneg (fun i => ?_)
        fun i _ _ => lastRowWeights_nonneg V i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hW_def]
      intro hi
      refine hi.trans (le_trans ?_ hRlo)
      rw [div_div_eq_mul_div, div_one,
        Real.mul_rpow (pseudoConditionNumber_nonneg V) (by norm_num)]
      calc α * θ * (pseudoConditionNumber V ^ (k : ℝ)⁻¹ * 1.998 ^ (k : ℝ)⁻¹) * ψ
          ≤ α * θ * (B ^ (k : ℝ)⁻¹ * 1.998 ^ (k : ℝ)⁻¹) * ψ := by gcongr
        _ = _ := by ring
  -- average over the covering
  have hcov : ∀ i ∈ W, ∃ s ∈ S, ‖e i - s‖ ≤ ε * R := fun i hi =>
    hcover _ (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hW_def] using hi)
  obtain ⟨i₀, hi₀⟩ : W.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, mul_zero] at hP
    have : 0 < (1 - 1 / 1.998 : ℝ) ^ 2 * ξ ^ (2 * k) := by positivity
    linarith
  obtain ⟨s, hs, hsle⟩ := exists_mem_sum_div_pow_le_card_mul_sum (k := 2 * k)
    (lastRowWeights_nonneg V) ⟨_, (hcov i₀ hi₀).choose_spec.1⟩
    (fun i s hs => hne s hs i) hcov
  refine ⟨s, hs, ?_⟩
  set x := ‖WithLp.toLp 2 (((H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k)
    (Fin.last n))‖ with hx_def
  have hf : ∑ i, lastRowWeights V i / ‖e i - s‖ ^ (2 * k) ≤ B ^ 2 * x ^ 2 :=
    (sum_lastRowWeights_div_pow_two_mul_le hV hHV (hne s hs) k).trans (by gcongr)
  have h1 := one_le_pow_mul_of_le_card_mul_sum_of_covers (by positivity) (by positivity)
    (by positivity) hξ hγ1 hψ (norm_nonneg _) hε0 hR0 hε2k hRk hP hsle hcard
    (Finset.sum_nonneg fun i _ => div_nonneg (lastRowWeights_nonneg V i) (by positivity)) hf
  rw [aeval_shiftPoly_replicate, ← Matrix.inv_pow', inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
  rwa [mul_comm] at h1

/-- **The while loop as a contraction with additive backward errors**
([BanksGarzaVargasSrivastava2022, Lemma 6.4], abstracted): let $\mathbf{H}_0, \dots,
\mathbf{H}_N$ be such that each step is a perturbed unitary similarity with error
$\varepsilon_j \ge 0$, and while $\mathbf{H}_j$ is not $\omega$-decoupled at the bottom (all of
its last $k$ subdiagonals exceed $\omega$, so $\psi_k(\mathbf{H}_j) > \omega$) the next step
either decouples or contracts the potential by $q < 1$. If $\psi_k(\mathbf{H}_0) \le \Sigma$ and
$q^N\Sigma \le \omega$, some $\mathbf{H}_j$, $j \le N$, is decoupled at the bottom, reached with
backward error $\sum_{i < j}\varepsilon_i$. -/
theorem exists_decoupled_of_contract {k N : ℕ} {q ω S : ℝ}
    (Hs : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ε : ℕ → ℝ) (hk : 0 < k) (hkn : k ≤ n)
    (hq : 0 ≤ q) (hq1 : q < 1) (hω : 0 < ω)
    (hstep : ∀ j < N, IsPerturbedUnitarySimilar (Hs j) (Hs (j + 1)) (ε j))
    (hcontract : ∀ j < N, (∀ i : Fin n, n ≤ (i : ℕ) + k → ω < ‖Hs j i.succ i.castSucc‖) →
      (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖Hs (j + 1) i.succ i.castSucc‖ ≤ ω) ∨
        hessenbergPotential k (Hs (j + 1)) ≤ q * hessenbergPotential k (Hs j))
    (hS : hessenbergPotential k (Hs 0) ≤ S) (hN : q ^ N * S ≤ ω) :
    ∃ j ≤ N, (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖Hs j i.succ i.castSucc‖ ≤ ω) ∧
      IsPerturbedUnitarySimilar (Hs 0) (Hs j) (∑ i ∈ Finset.range j, ε i) := by
  have back : ∀ j ≤ N, IsPerturbedUnitarySimilar (Hs 0) (Hs j) (∑ i ∈ Finset.range j, ε i) := by
    intro j
    induction j with
    | zero => intro _; simpa using IsPerturbedUnitarySimilar.refl (Hs 0)
    | succ j ih =>
      intro hj
      rw [Finset.sum_range_succ]
      exact (ih (by omega)).trans (hstep j (by omega))
  by_contra hcon
  have hnd : ∀ j ≤ N, ¬ ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖Hs j i.succ i.castSucc‖ ≤ ω :=
    fun j hj hd => hcon ⟨j, hj, hd, back j hj⟩
  have hpot : ∀ j ≤ N, hessenbergPotential k (Hs j) ≤ q ^ j * S := by
    intro j
    induction j with
    | zero => intro _; simpa using hS
    | succ j ih =>
      intro hj
      have hall : ∀ i : Fin n, n ≤ (i : ℕ) + k → ω < ‖Hs j i.succ i.castSucc‖ := fun i hi => by
        by_contra h
        exact hnd j (by omega) ⟨i, hi, not_lt.mp h⟩
      rcases hcontract j (by omega) hall with ⟨i, hi, hle⟩ | hpot'
      · exact absurd ⟨i, hi, hle⟩ (hnd (j + 1) hj)
      · calc hessenbergPotential k (Hs (j + 1)) ≤ q * hessenbergPotential k (Hs j) := hpot'
          _ ≤ q * (q ^ j * S) := mul_le_mul_of_nonneg_left (ih (by omega)) hq
          _ = q ^ (j + 1) * S := by ring
  -- when not decoupled at the bottom, the potential exceeds ω
  have hgt : ∀ j ≤ N, ω < hessenbergPotential k (Hs j) := by
    intro j hj
    have hall : ∀ i : Fin n, n ≤ (i : ℕ) + k → ω < ‖Hs j i.succ i.castSucc‖ := fun i hi => by
      by_contra h
      exact hnd j hj ⟨i, hi, not_lt.mp h⟩
    have hc1 : (Finset.univ.filter fun i : Fin n => n ≤ (i : ℕ) + k).card =
        (Finset.Ico (n - k) n).card := by
      refine Finset.card_nbij (fun i : Fin n => (i : ℕ)) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq, Finset.mem_Ico] at hi ⊢
        omega
      · intro a _ b _ hab
        exact Fin.ext hab
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_Ico] at hm
        refine ⟨⟨m, by omega⟩, ?_, rfl⟩
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq]
        omega
    have hcard : (Finset.univ.filter fun i : Fin n => n ≤ (i : ℕ) + k).card = k := by
      rw [hc1, Nat.card_Ico]; omega
    have hprod : ω ^ k < ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k),
        ‖Hs j i.succ i.castSucc‖ := by
      have hne : (Finset.univ.filter fun i : Fin n => n ≤ (i : ℕ) + k).Nonempty := by
        rw [← Finset.card_pos, hcard]; exact hk
      have := Finset.prod_lt_prod_of_nonempty (f := fun _ : Fin n => ω)
        (g := fun i : Fin n => ‖Hs j i.succ i.castSucc‖)
        (fun i _ => hω)
        (fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact hall i hi) hne
      rw [Finset.prod_const, hcard] at this
      exact this
    unfold hessenbergPotential
    calc ω = (ω ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hω.le hk.ne').symm
      _ < _ := Real.rpow_lt_rpow (by positivity) hprod (by positivity)
  have := hgt N le_rfl
  have := hpot N le_rfl
  linarith [hN]

end NLAlib
