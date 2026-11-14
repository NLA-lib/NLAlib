/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.Ritz
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
  sorry

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
  sorry

/-- **The exceptional shifts contain a contracting shift** (the deterministic core of `Exc`,
[BanksGarzaVargasSrivastava2022, Lemma 5.3], with the corrections of G13): let
$\mathbf{H}\mathbf{V} = \mathbf{V}\mathbf{D}$ with $\kappa(\mathbf{V}) \le B$, the $k \ge 2$ shifts
`ss` be $\theta$-optimal, $r$ an $\alpha$-promising one with
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
$0.005\varepsilon\tilde R$. -/
theorem exists_mem_le_norm_inv_pow_of_covers {B θ α ξ γ R ε : ℝ} {k : ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ} {r : ℂ}
    {S : Finset ℂ} (hk : 2 ≤ k) (hkn : k ≤ n) (hlen : ss.length = k)
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hopt : IsOptimalRitzValues θ H ss) (hr : IsPromisingRitzValue α V e ss r)
    (hψ : 0 < hessenbergPotential k H) (hγ : 0 < γ) (hγ1 : γ < 1) (hξ : 0 < ξ)
    (hθ : 1 ≤ θ) (hα : 1 ≤ α)
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
  sorry

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
