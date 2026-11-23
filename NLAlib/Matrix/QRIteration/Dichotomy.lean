/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.Ritz

/-!
# Forward-approximate Ritz values are optimal or decouple early

The exact-arithmetic dichotomy of [BanksGarzaVargasSrivastava2022, §4.1]. If shifts within
$\beta$ of the Ritz values fail to be $\theta$-optimal, then one of them is close to an
eigenvalue of large last-row weight, and the degree $k$ step with that shift has a large
$\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|$ (it decouples early). It is the
bridge from the forward-approximate Ritz values a small eigensolver computes to the
$\theta$-optimal ones the strategy needs; no arithmetic model is involved.

## Main results

* `NLAlib.sum_lastRowWeights_mul_norm_eval_sq_sub_le`: perturbing roots raises the weighted
  second moment only through weight near the roots.
* `NLAlib.IsUpperHessenberg.isOptimalRitzValues_or_exists_mem_det_eq_zero_or_le`: the dichotomy.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- Perturbing the shifts one by one: if each perturbed factor is at most $C f(s)$, the perturbed
shift polynomial is at most $C^k\prod f(s)$. -/
private theorem norm_eval_shiftPoly_le_of_forall₂ {β C : ℝ} (hC : 0 ≤ C) {f : ℂ → ℝ}
    (hf : ∀ s, 0 ≤ f s) {z : ℂ} {ss ss' : List ℂ}
    (h : List.Forall₂ (fun s s' => ‖s - s'‖ ≤ β) ss ss')
    (hpt : ∀ s ∈ ss, ∀ s', ‖s - s'‖ ≤ β → ‖z - s'‖ ≤ C * f s) :
    ‖(shiftPoly ss').eval z‖ ≤ C ^ ss.length * (ss.map f).prod := by
  induction h with
  | nil => simp [shiftPoly]
  | @cons a b l₁ l₂ hab _ ih =>
    have ih' := ih (fun s hs => hpt s (List.mem_cons_of_mem _ hs))
    have hp : 0 ≤ (l₁.map f).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
        exact hf s
    simp only [shiftPoly, List.map_cons, List.prod_cons, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_mul,
      List.length_cons] at ih' ⊢
    calc ‖z - b‖ * ‖Polynomial.eval z (l₂.map fun s => Polynomial.X - Polynomial.C s).prod‖
        ≤ (C * f a) * (C ^ l₁.length * (l₁.map f).prod) :=
          mul_le_mul (hpt a List.mem_cons_self b hab) ih' (norm_nonneg _)
            (mul_nonneg hC (hf a))
      _ = C ^ (l₁.length + 1) * (f a * (l₁.map f).prod) := by ring

/-- **Instability implies support**: let $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(
\mathbf{d})$ with $\mathbf{V}$ invertible and last-row weights $w$; let $c > 0$, $\beta \ge 0$,
and let `ss`, `ss'` be lists of $k$ shifts with
$\lvert s_i - s_i'\rvert \le \beta$ and $\lvert s_i\rvert \le \|\mathbf{H}\|_2$. With
$q = \prod_i (z - s_i)$, $q' = \prod_i (z - s_i')$,
$$\sum_i w_i\lvert q'(\mathbf{d}_i)\rvert^2 - (1 + 2c)^{2k}\sum_i w_i\lvert q(\mathbf{d}_i)
\rvert^2 \le \bigl(2(\|\mathbf{H}\|_2 + \beta)(1 + 2c)\bigr)^{2k}\sum_{i\,:\,\exists s \in
\mathrm{ss},\ \lvert\mathbf{d}_i - s\rvert \le \beta/(2c)} w_i\,.$$
[BanksGarzaVargasSrivastava2022, Lemma 4.2], there for $\Gamma$-separated eigenvalues and
$\beta \le c\Gamma$, which the pointwise bound does not need. -/
theorem sum_lastRowWeights_mul_norm_eval_sq_sub_le {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {c β : ℝ}
    (hc : 0 < c) (hβ : 0 ≤ β) {ss ss' : List ℂ}
    (hclose : List.Forall₂ (fun s s' => ‖s - s'‖ ≤ β) ss ss')
    (hss : ∀ s ∈ ss, ‖s‖ ≤ specNorm H) :
    ∑ i, lastRowWeights V i * ‖(shiftPoly ss').eval (d i)‖ ^ 2 -
        (1 + 2 * c) ^ (2 * ss.length) * ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2 ≤
      (2 * (specNorm H + β) * (1 + 2 * c)) ^ (2 * ss.length) *
        ∑ i ∈ Finset.univ.filter (fun i => ∃ s ∈ ss, ‖d i - s‖ ≤ β / (2 * c)),
          lastRowWeights V i := by
  set K := ss.length
  set M := 2 * (specNorm H + β)
  have hc1 : 1 ≤ (1 + 2 * c) ^ (2 * K) := one_le_pow₀ (by linarith)
  have hM : 0 ≤ M := by have := specNorm_nonneg H; positivity
  have hpt : ∀ i, lastRowWeights V i * ‖(shiftPoly ss').eval (d i)‖ ^ 2 ≤
      (1 + 2 * c) ^ (2 * K) * (lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2) +
        if ∃ s ∈ ss, ‖d i - s‖ ≤ β / (2 * c) then
          (M * (1 + 2 * c)) ^ (2 * K) * lastRowWeights V i else 0 := by
    intro i
    have hw := lastRowWeights_nonneg V i
    split_ifs with hS
    · have hle := norm_eval_shiftPoly_le_of_forall₂ hM (f := fun _ => 1) (fun _ => zero_le_one)
        (z := d i) hclose fun s hs s' hss' => by
          have h1 := norm_le_specNorm_of_mul_eq_mul_diagonal hV hHV i
          have h2 := hss s hs
          have h3 : ‖s'‖ ≤ ‖s‖ + β := by
            have := norm_sub_norm_le s' s
            rw [norm_sub_rev] at this
            linarith
          have h4 := norm_sub_le (d i) s'
          simp only [M, mul_one]
          linarith
      simp only [List.map_const', List.prod_replicate, one_pow, mul_one] at hle
      have hsq : ‖(shiftPoly ss').eval (d i)‖ ^ 2 ≤ M ^ (2 * K) := by
        rw [pow_mul']
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
      have hMc : M ^ (2 * K) ≤ (M * (1 + 2 * c)) ^ (2 * K) := by
        rw [mul_pow M (1 + 2 * c)]
        exact le_mul_of_one_le_right (by positivity) hc1
      have := mul_le_mul_of_nonneg_left (hsq.trans hMc) hw
      have : 0 ≤ (1 + 2 * c) ^ (2 * K) * (lastRowWeights V i *
          ‖(shiftPoly ss).eval (d i)‖ ^ 2) := by positivity
      linarith
    · push Not at hS
      have hle := norm_eval_shiftPoly_le_of_forall₂ (by linarith : (0 : ℝ) ≤ 1 + 2 * c)
        (f := fun s => ‖d i - s‖) (fun _ => norm_nonneg _) (z := d i) hclose
        fun s hs s' hss' => by
          have h1 := hS s hs
          have h2 : β ≤ 2 * c * ‖d i - s‖ := by
            rw [div_lt_iff₀ (by positivity)] at h1
            linarith
          have h3 : ‖d i - s'‖ ≤ ‖d i - s‖ + ‖s - s'‖ := by
            rw [← sub_add_sub_cancel (d i) s s']
            exact norm_add_le _ _
          nlinarith
      rw [← norm_eval_shiftPoly] at hle
      have hsq : ‖(shiftPoly ss').eval (d i)‖ ^ 2 ≤
          (1 + 2 * c) ^ (2 * K) * ‖(shiftPoly ss).eval (d i)‖ ^ 2 := by
        rw [pow_mul', ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
      have := mul_le_mul_of_nonneg_left hsq hw
      linarith
  calc ∑ i, lastRowWeights V i * ‖(shiftPoly ss').eval (d i)‖ ^ 2 -
        (1 + 2 * c) ^ (2 * K) * ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2
      ≤ ∑ i, (if ∃ s ∈ ss, ‖d i - s‖ ≤ β / (2 * c) then
          (M * (1 + 2 * c)) ^ (2 * K) * lastRowWeights V i else 0) := by
        rw [Finset.mul_sum, sub_le_iff_le_add, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => (hpt i).trans_eq (add_comm _ _)
    _ = _ := by rw [← Finset.sum_filter, Finset.mul_sum]

/-- A member of the first list of `List.Forall₂` has a partner in the second. -/
private theorem exists_mem_of_forall₂ {R : ℂ → ℂ → Prop} {l₁ l₂ : List ℂ}
    (h : List.Forall₂ R l₁ l₂) {a : ℂ} (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => simp at ha
  | @cons x y l₁ l₂ hxy _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, List.mem_cons_self, hxy⟩
    · obtain ⟨b, hb, hab⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

/-- $k \le (25/16)^k$, so $k^{1/(2k)} \le 5/4$. -/
private theorem natCast_le_pow_25_div_16 (k : ℕ) : (k : ℝ) ≤ (25 / 16 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k <;> norm_num
    · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
      rw [pow_succ]
      push_cast
      nlinarith

/-- Shifts that are not $\theta$-optimal put last-row weight near the Ritz values:
$\kappa^2\psi^{2k} < (2(\|\mathbf{H}\|_2 + \beta))^{2k}\sum_{i\ \text{near}} w_i$. -/
private theorem sq_mul_pow_lt_mul_sum_lastRowWeights_filter
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {d : Fin (n + 1) → ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {θ β c x : ℝ} (hθ0 : 0 < θ) (hc : 0 < c) (hβ : 0 ≤ β) (h2c : 1 + 2 * c = θ / x)
    (hx2k : x ^ (2 * k) = 2 * pseudoConditionNumber V ^ 4) (hκ1 : 1 ≤ pseudoConditionNumber V)
    {rs : List ℂ} (hclose : List.Forall₂ (fun ρ r => ‖ρ - r‖ ≤ β) (ritzValues k H) rs)
    (hopt : ¬IsOptimalRitzValues θ H rs) :
    pseudoConditionNumber V ^ 2 * hessenbergPotential k H ^ (2 * k) <
      (2 * (specNorm H + β)) ^ (2 * k) *
        ∑ i ∈ Finset.univ.filter (fun i => ∃ s ∈ ritzValues k H, ‖d i - s‖ ≤ β / (2 * c)),
          lastRowWeights V i := by
  set κ := pseudoConditionNumber V
  set ψ := hessenbergPotential k H
  set w := lastRowWeights V
  have hψ0 : 0 ≤ ψ := hessenbergPotential_nonneg _ _
  have hlenρ : (ritzValues k H).length = k := length_ritzValues k H
  have hlenr : rs.length = k := hclose.length_eq ▸ hlenρ
  have hA : θ ^ (2 * k) * ψ ^ (2 * k) <
      κ ^ 2 * ∑ i, w i * ‖(shiftPoly rs).eval (d i)‖ ^ 2 := by
    have h1 := norm_mul_diagonal_mul_inv_last_sq_le hV (fun i => (shiftPoly rs).eval (d i))
    rw [← aeval_eq_mul_diagonal_mul_inv hV hHV] at h1
    have h2 : (θ * ψ) ^ k < ‖WithLp.toLp 2 (Polynomial.aeval H (shiftPoly rs) (Fin.last n))‖ := by
      unfold IsOptimalRitzValues at hopt
      push Not at hopt
      rwa [hlenr] at hopt
    calc θ ^ (2 * k) * ψ ^ (2 * k) = ((θ * ψ) ^ k) ^ 2 := by ring
      _ < _ := pow_lt_pow_left₀ h2 (by positivity) two_ne_zero
      _ ≤ _ := h1
  have hB : ∑ i, w i * ‖(shiftPoly (ritzValues k H)).eval (d i)‖ ^ 2 ≤
      κ ^ 2 * ψ ^ (2 * k) := by
    have h1 := sum_lastRowWeights_mul_sq_le hV
      (fun i => (shiftPoly (ritzValues k H)).eval (d i))
    rw [← aeval_eq_mul_diagonal_mul_inv hV hHV, shiftPoly_ritzValues,
      hH.norm_aeval_charpoly_trailingBlock_eq hk hkn] at h1
    rw [shiftPoly_ritzValues]
    calc _ ≤ κ ^ 2 * (ψ ^ k) ^ 2 := h1
      _ = κ ^ 2 * ψ ^ (2 * k) := by rw [← pow_mul, mul_comm k 2]
  have hC := sum_lastRowWeights_mul_norm_eval_sq_sub_le hV hHV hc hβ hclose
    (fun s hs => norm_le_specNorm_of_mem_ritzValues (by omega) hs)
  have hK : 0 < 2 * κ ^ 4 := mul_pos two_pos (pow_pos (by linarith) 4)
  rw [hlenρ, h2c, mul_pow, div_pow, hx2k, div_mul_eq_mul_div, mul_div_assoc',
    div_mul_eq_mul_div, sub_le_iff_le_add, ← add_div, le_div_iff₀ hK] at hC
  have h3 := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ θ ^ (2 * k))
  have h4 := mul_lt_mul_of_pos_left hA (mul_pos two_pos (pow_pos (by linarith) 2) :
    (0 : ℝ) < 2 * κ ^ 2)
  have h5 : κ ^ 2 * θ ^ (2 * k) * ψ ^ (2 * k) < (2 * (specNorm H + β)) ^ (2 * k) *
      θ ^ (2 * k) * ∑ i ∈ Finset.univ.filter
        (fun i => ∃ s ∈ ritzValues k H, ‖d i - s‖ ≤ β / (2 * c)), w i := by
    linarith only [hC, h3, h4]
  have hθk : 0 < θ ^ (2 * k) := by positivity
  refine lt_of_mul_lt_mul_left ?_ hθk.le
  linarith only [h5]

/-- Pigeonhole: if the eigenvalues are $\Gamma$-separated and $\beta < c\Gamma$, each shift has
at most one eigenvalue within $\beta/(2c)$, so one eigenvalue near the shifts carries a
$1/k$ share of their weight. -/
private theorem exists_sum_lastRowWeights_filter_le_mul (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    {d : Fin (n + 1) → ℂ} {Γ c β : ℝ} (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hc : 0 < c)
    (hβc : β < c * Γ) {ss : List ℂ}
    (hS : (Finset.univ.filter (fun i => ∃ s ∈ ss, ‖d i - s‖ ≤ β / (2 * c))).Nonempty) :
    ∃ j, ∃ ρ ∈ ss, ‖d j - ρ‖ ≤ β / (2 * c) ∧
      ∑ i ∈ Finset.univ.filter (fun i => ∃ s ∈ ss, ‖d i - s‖ ≤ β / (2 * c)), lastRowWeights V i ≤
        ss.length * lastRowWeights V j := by
  set S := Finset.univ.filter (fun i => ∃ s ∈ ss, ‖d i - s‖ ≤ β / (2 * c))
  obtain ⟨j, hjS, hjmax⟩ := S.exists_max_image (lastRowWeights V) hS
  have hex : ∀ i ∈ S, ∃ s ∈ ss, ‖d i - s‖ ≤ β / (2 * c) :=
    fun i hi => (Finset.mem_filter.mp hi).2
  let f : Fin (n + 1) → ℂ := fun i =>
    if h : ∃ s ∈ ss, ‖d i - s‖ ≤ β / (2 * c) then h.choose else 0
  have hf : ∀ i ∈ S, f i ∈ ss ∧ ‖d i - f i‖ ≤ β / (2 * c) := fun i hi => by
    simp only [f, dif_pos (hex i hi)]
    exact (hex i hi).choose_spec
  have hcard : S.card ≤ ss.length := by
    refine (Finset.card_le_card_of_injOn f (by
      intro i hi
      exact List.mem_toFinset.mpr (hf i hi).1) ?_).trans (List.toFinset_card_le _)
    intro i₁ hi₁ i₂ hi₂ hfi
    by_contra hne
    have h1 := hgap i₁ i₂ hne
    have h2 : ‖d i₁ - d i₂‖ ≤ ‖d i₁ - f i₁‖ + ‖d i₂ - f i₂‖ := by
      rw [hfi, ← norm_neg (d i₂ - f i₂), ← sub_add_sub_cancel (d i₁) (f i₂) (d i₂)]
      exact (norm_add_le _ _).trans_eq (by rw [neg_sub])
    have h3 : β / (2 * c) + β / (2 * c) < Γ := by
      rw [← add_div, div_lt_iff₀ (by positivity)]
      linarith
    linarith [(hf i₁ hi₁).2, (hf i₂ hi₂).2]
  obtain ⟨ρ, hρ, hjρ⟩ := hex j hjS
  refine ⟨j, ρ, hρ, hjρ, ?_⟩
  calc ∑ i ∈ S, lastRowWeights V i ≤ ∑ _i ∈ S, lastRowWeights V j :=
        Finset.sum_le_sum fun i hi => hjmax i hi
    _ = S.card * lastRowWeights V j := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ss.length * lastRowWeights V j := by
      gcongr
      exact lastRowWeights_nonneg V j

/-- The final arithmetic of the dichotomy: from $\psi^{2k} < kM^{2k}N^2\delta^{2k}$ with
$M = 2(h + \beta)$, $\delta t = \beta$ and $k \le (5/4)^{2k}$, conclude
$\tfrac25\psi t \le \kappa^{2/k}(h + \beta)\beta N^{1/k}$ for $\kappa \ge 1$. -/
private theorem mul_le_rpow_mul_of_pow_lt {k : ℕ} (hk : 0 < k) {κ ψ N δ β h t : ℝ}
    (hκ1 : 1 ≤ κ) (hh : 0 ≤ h) (hβ : 0 ≤ β) (hN0 : 0 ≤ N) (hδ0 : 0 ≤ δ)
    (hδ : δ * t = β) (ht : 0 ≤ t)
    (h1 : ψ ^ (2 * k) < k * (2 * (h + β)) ^ (2 * k) * N ^ 2 * δ ^ (2 * k)) :
    2 / 5 * ψ * t ≤ κ ^ ((2 : ℝ) / k) * (h + β) * β * N ^ ((k : ℝ)⁻¹) := by
  have hM : 0 ≤ 2 * (h + β) := by positivity
  have hN' : (N ^ ((k : ℝ)⁻¹)) ^ (2 * k) = N ^ 2 := by
    rw [pow_mul', Real.rpow_inv_natCast_pow hN0 hk.ne']
  have hψlt : ψ < 5 / 4 * (2 * (h + β)) * δ * N ^ ((k : ℝ)⁻¹) := by
    have h3 : (k : ℝ) * (2 * (h + β)) ^ (2 * k) * N ^ 2 * δ ^ (2 * k) ≤
        (5 / 4 * (2 * (h + β)) * δ * N ^ ((k : ℝ)⁻¹)) ^ (2 * k) := by
      rw [mul_pow (5 / 4 * (2 * (h + β)) * δ) (N ^ ((k : ℝ)⁻¹)), mul_pow (5 / 4 * (2 * (h + β))) δ,
        mul_pow (5 / 4 : ℝ) (2 * (h + β)), hN', pow_mul (5 / 4 : ℝ),
        show ((5 : ℝ) / 4) ^ 2 = 25 / 16 by norm_num]
      have h0 : 0 ≤ (2 * (h + β)) ^ (2 * k) * N ^ 2 * δ ^ (2 * k) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right (natCast_le_pow_25_div_16 k) h0]
    exact lt_of_pow_lt_pow_left₀ (2 * k) (by positivity) (h1.trans_le h3)
  have hκk : 1 ≤ κ ^ ((2 : ℝ) / k) := Real.one_le_rpow hκ1 (by positivity)
  have hpos : 0 ≤ (h + β) * β * N ^ ((k : ℝ)⁻¹) := by positivity
  have h4 : 2 / 5 * ψ * t ≤ 2 / 5 * (5 / 4 * (2 * (h + β)) * δ * N ^ ((k : ℝ)⁻¹)) * t := by
    gcongr
  have h5 : 2 / 5 * (5 / 4 * (2 * (h + β)) * δ * N ^ ((k : ℝ)⁻¹)) * t =
      (h + β) * β * N ^ ((k : ℝ)⁻¹) := by
    rw [← hδ]
    ring
  nlinarith

/-- **The dichotomy for forward-approximate Ritz values**: let $\mathbf{H}$ be upper Hessenberg
with $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible,
$\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$, eigenvalues separated by $\Gamma$; let
$1 \le k \le n$, $x = (2\kappa^4)^{1/(2k)} < \theta$, $c = \tfrac12(\theta/x - 1)$,
$0 < \beta < c\Gamma$, and let `rs` be within $\beta$ of the Ritz values of order $k$, entry by
entry. Then `rs` is a set of $\theta$-optimal Ritz values, or some $r$ in `rs` is an eigenvalue,
or
$$\tfrac25\,\psi_k(\mathbf{H})\Bigl(1 - \frac x\theta\Bigr) \le \kappa^{2/k}(\|\mathbf{H}\|_2 +
\beta)\,\beta\,\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|^{1/k}$$
for some $r$ in `rs`. Adapted from [BanksGarzaVargasSrivastava2022, Theorem 4.1]: the constant
$\tfrac25$ bounds the factor $k^{-1/(2k)}/2$, and the strict $\beta < c\Gamma$ keeps two
eigenvalues from sharing a Ritz value.
Result: shifted-qr-ritz-dichotomy -/
theorem IsUpperHessenberg.isOptimalRitzValues_or_exists_mem_det_eq_zero_or_le
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {d : Fin (n + 1) → ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {Γ θ β : ℝ} (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖)
    (hθ : (2 * pseudoConditionNumber V ^ 4) ^ ((2 * k : ℝ)⁻¹) < θ) (hβ : 0 < β)
    (hβΓ : β < (θ / (2 * pseudoConditionNumber V ^ 4) ^ ((2 * k : ℝ)⁻¹) - 1) / 2 * Γ)
    {rs : List ℂ} (hclose : List.Forall₂ (fun ρ r => ‖ρ - r‖ ≤ β) (ritzValues k H) rs) :
    IsOptimalRitzValues θ H rs ∨ ∃ r ∈ rs,
      (H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0 ∨
        2 / 5 * hessenbergPotential k H *
            (1 - (2 * pseudoConditionNumber V ^ 4) ^ ((2 * k : ℝ)⁻¹) / θ) ≤
          pseudoConditionNumber V ^ ((2 : ℝ) / k) * (specNorm H + β) * β *
            ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k)
              (Fin.last n))‖ ^ ((k : ℝ)⁻¹) := by
  set κ := pseudoConditionNumber V
  set x := (2 * κ ^ 4) ^ ((2 * k : ℝ)⁻¹) with hx_def
  set ψ := hessenbergPotential k H
  set c := (θ / x - 1) / 2 with hc_def
  by_cases hopt : IsOptimalRitzValues θ H rs
  · exact Or.inl hopt
  right
  by_cases hdet : ∃ r ∈ rs, (H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0
  · obtain ⟨r, hr, h⟩ := hdet
    exact ⟨r, hr, Or.inl h⟩
  push Not at hdet
  have hκ1 : 1 ≤ κ := one_le_pseudoConditionNumber hV.ne_zero
  -- explicit terms: `positivity` on the `set` atom `κ` trips the norm extensions
  have hK : 0 < 2 * κ ^ 4 := mul_pos two_pos (pow_pos (by linarith) 4)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hK _
  have hθ0 : 0 < θ := hx0.trans hθ
  have hc : 0 < c := by
    have := (one_lt_div hx0).mpr hθ
    rw [hc_def]; linarith
  have hx2k : x ^ (2 * k) = 2 * κ ^ 4 := by
    rw [hx_def, show (2 * k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_inv_natCast_pow hK.le (by omega)
  have hψ0 : 0 ≤ ψ := hessenbergPotential_nonneg _ _
  -- the shifts `rs` are no eigenvalues
  have hdr : ∀ r ∈ rs, ∀ i, d i ≠ r := by
    intro r hr i hi
    apply hdet r hr
    have := aeval_eq_mul_diagonal_mul_inv hV hHV (Polynomial.X - Polynomial.C r)
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one] at this
    rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero, zero_mul]
  -- weight near the Ritz values, carried by one eigenvalue `d j` near some `r ∈ rs`
  have h2c : 1 + 2 * c = θ / x := by rw [hc_def]; ring
  have hW := sq_mul_pow_lt_mul_sum_lastRowWeights_filter hH hV hHV hk hkn hθ0 hc hβ.le h2c
    hx2k hκ1 hclose hopt
  have hSne : (Finset.univ.filter
      (fun i => ∃ s ∈ ritzValues k H, ‖d i - s‖ ≤ β / (2 * c))).Nonempty := by
    refine Finset.nonempty_of_sum_ne_zero (f := lastRowWeights V) fun h0 => ?_
    rw [h0, mul_zero] at hW
    exact absurd hW (not_lt.mpr (mul_nonneg (sq_nonneg κ) (pow_nonneg hψ0 _)))
  obtain ⟨j, ρ, hρ, hjρ, hWle⟩ := exists_sum_lastRowWeights_filter_le_mul V hgap hc hβΓ hSne
  rw [length_ritzValues] at hWle
  obtain ⟨r, hr, hρr⟩ := exists_mem_of_forall₂ hclose hρ
  refine ⟨r, hr, Or.inr ?_⟩
  set N := ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k)
    (Fin.last n))‖
  set δ := β / (2 * c) + β
  have hdj0 : 0 < ‖d j - r‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hdr r hr j))
  have hdj : ‖d j - r‖ ≤ δ := by
    have := norm_sub_le_norm_sub_add_norm_sub (d j) ρ r
    linarith only [this, hjρ, hρr]
  -- the weight of `d j` is at most `κ² N² δ^{2k}`
  have hwj : lastRowWeights V j ≤ κ ^ 2 * N ^ 2 * δ ^ (2 * k) := by
    have h2 := (Finset.single_le_sum (fun i _ => div_nonneg (lastRowWeights_nonneg V i)
      (by positivity)) (Finset.mem_univ j)).trans
      (sum_lastRowWeights_div_pow_two_mul_le hV hHV (fun i => hdr r hr i) k)
    rw [div_le_iff₀ (pow_pos hdj0 _)] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdj0.le hdj _)
      (mul_nonneg (sq_nonneg κ) (sq_nonneg N)))
  have hM : 0 ≤ 2 * (specNorm H + β) := by
    have := specNorm_nonneg H
    linarith only [this, hβ]
  have h1 : κ ^ 2 * ψ ^ (2 * k) <
      κ ^ 2 * (k * (2 * (specNorm H + β)) ^ (2 * k) * N ^ 2 * δ ^ (2 * k)) :=
    hW.trans_le ((mul_le_mul_of_nonneg_left (hWle.trans (mul_le_mul_of_nonneg_left hwj
      (Nat.cast_nonneg k))) (pow_nonneg hM (2 * k))).trans_eq (by ring))
  refine mul_le_rpow_mul_of_pow_lt hk hκ1 (specNorm_nonneg H) hβ.le (norm_nonneg _)
    (by positivity) ?_ ?_ (lt_of_mul_lt_mul_left h1 (sq_nonneg κ))
  · have hθx : θ - x ≠ 0 := (sub_pos.mpr hθ).ne'
    simp only [δ, hc_def]
    field_simp
    ring
  · have := (div_lt_one hθ0).mpr hθ
    linarith only [this]

end NLAlib
