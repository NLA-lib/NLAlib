/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.NewtonSchulzSign

/-!
# Accuracy of the rounded Newton–Schulz sign algorithm

The stopping test and the error of `NLAlib.newtonSchulzSign` on a `NLAlib.FloatMachine`
([Shah2024, Theorem 2.6]). The eigenvalues of the rounded iterates lie on perturbed scalar chains
(`NLAlib.IsNewtonSchulzChain`, `NLAlib/Matrix/Computation/NewtonSchulzSign.lean`); the test at the
computed threshold $\mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$ passes once they are within
$\varepsilon/(16n)$ of $\pm 1$, and an iterate that passes is within $2\varepsilon/3$ of its
sign. Two accuracy theorems: one charges every step the error $2\delta/s$ of the first
(the precision condition carries the step count), the other sums the step errors as a geometric
series while the least eigenvalue modulus grows by the factor $11/8$ of
`NLAlib.div_mul_abs_le_abs_newtonSchulz_of_abs_le`, so that the step count and the dimension factor
of the stopping test leave the binding condition.

## Main results

* `NLAlib.FloatMachine.IsArithAccurate.newtonSchulzTest_of_forall_mem_spectrum`: the test passes
  near $\pm 1$.
* `NLAlib.FloatMachine.IsArithAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le`,
  `FloatMachine.IsArithAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le_of_mul_le`:
  Theorem 2.6.
* `NLAlib.FloatMachine.IsArithAccurate.exists_le_newtonSchulzTest_iterate`: the stopping test
  passes within $N_0 + 1$ steps.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω : ℝ} {μ : ℕ → ℝ}
  {n : ℕ}

/-! ### Spectral helpers -/

private theorem cfc_sign_smul {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian)
    {c : ℝ} (hc : 0 < c) : cfc Real.sign (c • X) = cfc Real.sign X := by
  rw [← cfc_const_mul_id c X hX.isSelfAdjoint,
    ← cfc_comp' Real.sign (c * ·) X ((X.finite_real_spectrum.image _).continuousOn _)]
  congr 1
  funext x
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hc h)]
  · rw [mul_zero]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hc h)]

private theorem cfc_sq_sub_one {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) :
    cfc (fun x : ℝ => x ^ 2 - 1) X = X * X - 1 := by
  rw [cfc_sub (fun x : ℝ => x ^ 2) (fun _ => 1) X, cfc_pow_id X 2 hX.isSelfAdjoint,
    cfc_const_one ℝ X, sq]

private theorem abs_one_sub_sq_le_specNorm {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) {x : ℝ} (hx : x ∈ spectrum ℝ X) : |1 - x ^ 2| ≤ specNorm (X * X - 1) := by
  rw [← cfc_sq_sub_one hX]
  have hH : (cfc (fun x : ℝ => x ^ 2 - 1) X).IsHermitian := cfc_predicate _ X
  rw [abs_sub_comm]
  refine hH.abs_le_specNorm_of_mem_spectrum ?_
  rw [cfc_map_spectrum (fun x : ℝ => x ^ 2 - 1) X hX.isSelfAdjoint]
  exact ⟨x, hx, rfl⟩

private theorem specNorm_mul_self_sub_one_le {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ spectrum ℝ X, |1 - x ^ 2| ≤ c) :
    specNorm (X * X - 1) ≤ c := by
  rw [← cfc_sq_sub_one hX]
  exact hX.specNorm_cfc_le hc fun x hx => abs_sub_comm (x ^ 2) 1 ▸ h x hx

/-- A $k \times k$ matrix with entries of modulus at most $c$ has spectral norm at most $kc$. -/
private theorem specNorm_le_card_mul_of_norm_apply_le {k : ℕ}
    {X : Matrix (Fin k) (Fin k) ℂ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖X i j‖ ≤ c) :
    specNorm X ≤ k * c := by
  refine (specNorm_le_frobNorm X).trans ?_
  refine (pow_le_pow_iff_left₀ (frobNorm_nonneg X) (by positivity) two_ne_zero).mp ?_
  rw [frobNorm_sq_eq_sum]
  calc ∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ ∑ _i : Fin k, ∑ _j : Fin k, c ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (k * c) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### The stopping test -/

/-- The stored threshold $\mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$ is close to
$\varepsilon/(4n)$. -/
private theorem threshold_bounds (hM : M.IsArithAccurate dec u τ Ω μ) (hu₀ : 0 ≤ u)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F}
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1 / 2) (hu : 640 * n * u ≤ dec ε) :
    n * dec (M.div ε (M.ofNat (4 * n))) ≤ 13 / 50 * dec ε ∧
      dec ε / 5 ≤ n * dec (M.div ε (M.ofNat (4 * n))) := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc := hM.ofNat (4 * n) (by push_cast; rw [abs_of_nonneg (by positivity)]; linarith)
  push_cast at hc
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * n),
    max_eq_left (by nlinarith : τ ≤ 4 * n)] at hc
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
  set c := dec (M.ofNat (4 * n))
  have hu₁ : u ≤ 1 / 1280 := by nlinarith
  have hcpos : 0 < c := by nlinarith
  set q := dec ε / c with hqdef
  have hq : q * c = dec ε := div_mul_cancel₀ _ hcpos.ne'
  have hq₀ : 0 < q := div_pos hε hcpos
  have hq₁ : q ≤ 1 / 4 := by nlinarith
  have hd := hM.div ε (M.ofNat (4 * n)) hcpos.ne' (by rw [abs_of_pos hq₀]; linarith)
  rw [← hqdef, abs_of_pos hq₀] at hd
  have hd' : |q - dec (M.div ε (M.ofNat (4 * n)))| ≤ u * (q + τ) :=
    hd.trans (mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hu₀)
  obtain ⟨hd₁, hd₂⟩ := abs_le.mp hd'
  have hnτ : n * τ ≤ 1 / 2 := by linarith
  constructor <;> nlinarith [mul_nonneg hu₀ hq₀.le, mul_le_mul_of_nonneg_left hnτ hu₀]

/-- The computed test matrix $\mathrm{mm}(\mathbf{X}, \mathbf{X}) - \mathbf{I}$ is within
$2(8 + \mu(n))u$ of $\mathbf{X}^2 - \mathbf{I}$. -/
private theorem specNorm_mul_self_sub_one_sub_decodeMatrix_le
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₁ : τ ≤ 1) (hΩ : 9 ≤ Ω)
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10) :
    specNorm ((decodeMatrix dec X * decodeMatrix dec X - 1) -
      decodeMatrix dec (M.hermShift (M.mm X X) M.one)) ≤ 2 * (8 + μ n) * u := by
  set Xd := decodeMatrix dec X
  set P := decodeMatrix dec (M.mm X X)
  have hX₀ := specNorm_nonneg Xd
  have hsq : specNorm Xd * specNorm Xd ≤ 121 / 100 := by nlinarith
  have hE₁ : specNorm (Xd * Xd - P) ≤ μ n * u * (121 / 100) := by
    have h := hM.isMatMulErr.specNorm_mul_sub_le X X (le_trans hsq (by linarith))
    simp only [max_self] at h
    exact h.trans (mul_le_mul_of_nonneg_left (max_le hsq (by linarith)) (by positivity))
  have hPH : P.IsHermitian := hM.isMatMulErr.isHermitian_of_map_eq_conjTranspose X X hX.symm
  have hX₁ : specNorm (Xd * Xd - 1) ≤ 1 :=
    specNorm_mul_self_sub_one_le hX zero_le_one fun x hx => by
      have := (hX.abs_le_specNorm_of_mem_spectrum hx).trans hXn
      rw [abs_le]; constructor <;> nlinarith [abs_nonneg x, sq_abs x]
  have hP₁ : specNorm (P - 1) ≤ 2 := by
    have : P - 1 = (Xd * Xd - 1) - (Xd * Xd - P) := by abel
    rw [this]
    refine (specNorm_sub_le _ _).trans ?_
    nlinarith
  have hE₂ := hM.specNorm_sub_decodeMatrix_hermShift_le hu₀ hPH M.one
    (by rw [hM.dec_one, one_smul]; linarith)
  rw [hM.dec_one, one_smul] at hE₂
  have hE₂' : specNorm ((P - 1) - decodeMatrix dec (M.hermShift (M.mm X X) M.one)) ≤ 2 * u :=
    hE₂.trans (by nlinarith [mul_le_mul_of_nonneg_left (max_le hP₁ (by linarith : τ ≤ 2)) hu₀])
  have : (Xd * Xd - 1) - decodeMatrix dec (M.hermShift (M.mm X X) M.one) =
      (Xd * Xd - P) + ((P - 1) - decodeMatrix dec (M.hermShift (M.mm X X) M.one)) := by abel
  rw [this]
  refine (specNorm_add_le _ _).trans ?_
  nlinarith

private theorem newtonSchulzTest_eq_true_iff (hM : M.IsArithAccurate dec u τ Ω μ) (η : F)
    (X : Matrix (Fin n) (Fin n) (F × F)) :
    newtonSchulzTest M η X = true ↔ ∀ i j,
      |dec (M.hermShift (M.mm X X) M.one i j).1| ≤ dec η ∧
        |dec (M.hermShift (M.mm X X) M.one i j).2| ≤ dec η := by
  simp only [newtonSchulzTest, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.and_eq_true, hM.le_iff, hM.dec_neg, abs_le, and_assoc]

/-- The size condition $640n(8 + \mu(n))u \le \varepsilon \le 1/2$ bounds $640nu$ by
$\varepsilon$ and $u(8 + \mu(n))$ by $1/10$. -/
private theorem unitRoundoff_bounds {μn u ε : ℝ} (hn : 0 < n) (hμ : 0 ≤ μn) (hu₀ : 0 ≤ u)
    (hε₁ : ε ≤ 1 / 2) (hk : 640 * n * (8 + μn) * u ≤ ε) :
    640 * n * u ≤ ε ∧ u * (8 + μn) ≤ 1 / 10 := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · nlinarith [mul_nonneg hμ hu₀, mul_nonneg hu₀ (by positivity : (0 : ℝ) ≤ n)]
  · nlinarith [mul_nonneg hu₀ (by linarith : 0 ≤ 8 + μn)]

/-- If the test passes, the iterate is within `2ε/3` of its sign. -/
private theorem specNorm_sub_cfc_sign_le_of_newtonSchulzTest
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F} (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 1 / 2) (hk : 640 * n * (8 + μ n) * u ≤ dec ε)
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10)
    (htest : newtonSchulzTest M (M.div ε (M.ofNat (4 * n))) X = true) :
    specNorm (decodeMatrix dec X - cfc Real.sign (decodeMatrix dec X)) ≤ 2 / 3 * dec ε := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hun, hu⟩ := unitRoundoff_bounds hn hμ hu₀ hε₁ hk
  have hη := (threshold_bounds hM hu₀ hτ₀ hτ hΩ hn hε hε₁ hun).1
  set η := dec (M.div ε (M.ofNat (4 * n)))
  have hE := specNorm_mul_self_sub_one_sub_decodeMatrix_le hM hμ hu₀ hu (by nlinarith)
    (by linarith) hX hXn
  rw [newtonSchulzTest_eq_true_iff hM] at htest
  have hη₀ : 0 ≤ η := le_trans (abs_nonneg _) (htest ⟨0, hn⟩ ⟨0, hn⟩).1
  have hT := specNorm_le_card_mul_of_norm_apply_le
    (X := decodeMatrix dec (M.hermShift (M.mm X X) M.one)) (by positivity : 0 ≤ 2 * η)
    fun i j => (Complex.norm_le_abs_re_add_abs_im _).trans
      ((add_le_add (htest i j).1 (htest i j).2).trans_eq (two_mul η).symm)
  have hS : specNorm (decodeMatrix dec X * decodeMatrix dec X - 1) ≤ 2 / 3 * dec ε := by
    have := specNorm_add_le (decodeMatrix dec X * decodeMatrix dec X - 1 -
      decodeMatrix dec (M.hermShift (M.mm X X) M.one))
      (decodeMatrix dec (M.hermShift (M.mm X X) M.one))
    rw [sub_add_cancel] at this
    nlinarith [mul_nonneg hu₀ (by linarith : 0 ≤ 8 + μ n)]
  exact hX.specNorm_sub_cfc_sign_le (by positivity) fun x hx =>
    (abs_one_sub_sq_le_specNorm hX hx).trans hS

/-- The Newton–Schulz test passes near $\pm 1$: under `NLAlib.FloatMachine.IsArithAccurate` $u$
$\tau$ $\Omega$ with product constant $\mu$, $\mu(n) \ge 0$, $u \ge 0$, $0 \le \tau$,
$2n\tau \le 1$, $9(n + 1) \le \Omega$ and $n > 0$, for a stored $\varepsilon$ with
$0 < \varepsilon \le 1/2$ and $640n(8 + \mu(n))u \le \varepsilon$ (decoded values), and a stored
$\mathbf{X}$ with Hermitian decoding, $\|\mathbf{X}\|_2 \le 11/10$ and
$\lvert 1 - x^2 \rvert \le \varepsilon/(16n)$ for every eigenvalue $x$, the stopping test
`NLAlib.newtonSchulzTest` at the computed threshold $\mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$
passes. -/
theorem FloatMachine.IsArithAccurate.newtonSchulzTest_of_forall_mem_spectrum
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F} (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 1 / 2) (hk : 640 * n * (8 + μ n) * u ≤ dec ε)
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10)
    (h : ∀ x ∈ spectrum ℝ (decodeMatrix dec X), |1 - x ^ 2| ≤ dec ε / (16 * n)) :
    newtonSchulzTest M (M.div ε (M.ofNat (4 * n))) X = true := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hun, hu⟩ := unitRoundoff_bounds hn hμ hu₀ hε₁ hk
  have hη := (threshold_bounds hM hu₀ hτ₀ hτ hΩ hn hε hε₁ hun).2
  set η := dec (M.div ε (M.ofNat (4 * n)))
  have hE := specNorm_mul_self_sub_one_sub_decodeMatrix_le hM hμ hu₀ hu (by nlinarith)
    (by linarith) hX hXn
  have hS := specNorm_mul_self_sub_one_le hX (by positivity) h
  have hT : specNorm (decodeMatrix dec (M.hermShift (M.mm X X) M.one)) ≤
      dec ε / (16 * n) + 2 * (8 + μ n) * u := by
    have := specNorm_sub_le (decodeMatrix dec X * decodeMatrix dec X - 1)
      (decodeMatrix dec X * decodeMatrix dec X - 1 -
        decodeMatrix dec (M.hermShift (M.mm X X) M.one))
    rw [sub_sub_cancel] at this
    linarith
  have hη' : dec ε / (16 * n) + 2 * (8 + μ n) * u ≤ η := by
    rw [div_add' _ _ _ (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hu₀ (by linarith : 0 ≤ 8 + μ n)]
  rw [newtonSchulzTest_eq_true_iff hM]
  intro i j
  have hij := (norm_apply_le_specNorm _ i j).trans (hT.trans hη')
  exact ⟨(Complex.abs_re_le_norm _).trans hij, (Complex.abs_im_le_norm _).trans hij⟩

/-! ### The loop -/

/-- **The loop invariant**: from an iterate at step `k` whose eigenvalues lie on perturbed scalar
chains, the loop returns a matrix within `2ε/3` plus `2δ/s` per remaining step of the sign. -/
private theorem specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzLoop_le
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F} (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 1 / 2) (hk : 640 * n * (8 + μ n) * u ≤ dec ε) {s : ℝ} (hs : 0 < s)
    (hs₁ : s ≤ 1 / 2) (hδs : 20 * (4 * √(n : ℝ) * (8 + μ n) * u) ≤ s)
    (hδε : 10 * (4 * √(n : ℝ) * (8 + μ n) * u) ≤ dec ε / (16 * n)) (N k : ℕ)
    (X : Matrix (Fin n) (Fin n) (F × F)) (hX : (decodeMatrix dec X).IsHermitian)
    (hch : ∀ y ∈ spectrum ℝ (decodeMatrix dec X),
      IsNewtonSchulzChain s (4 * √(n : ℝ) * (8 + μ n) * u) y k)
    (hN : newtonSchulzSteps s (dec ε / (16 * n)) ≤ k + N) :
    specNorm (cfc Real.sign (decodeMatrix dec X) -
      decodeMatrix dec (newtonSchulzLoop M (M.div ε (M.ofNat (4 * n))) N X)) ≤
        2 / 3 * dec ε + max 0 (newtonSchulzSteps s (dec ε / (16 * n)) + 1 - k) *
          (2 * (4 * √(n : ℝ) * (8 + μ n) * u) / s) := by
  set δ := 4 * √(n : ℝ) * (8 + μ n) * u
  set N₀ := newtonSchulzSteps s (dec ε / (16 * n))
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ₀ : 0 ≤ δ := by positivity
  have hε' : 0 < dec ε / (16 * n) := by positivity
  have hε'₁ : dec ε / (16 * n) ≤ 3 / 80 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hε'₂ : dec ε / (16 * n) ≤ 2 / 3 * dec ε := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hXn : ∀ {j : ℕ} {Y : Matrix (Fin n) (Fin n) (F × F)}, (decodeMatrix dec Y).IsHermitian →
      (∀ y ∈ spectrum ℝ (decodeMatrix dec Y), IsNewtonSchulzChain s δ y j) →
        specNorm (decodeMatrix dec Y) ≤ 11 / 10 := fun hY hchY =>
    hY.specNorm_le_of_forall_mem_spectrum_abs_le (by norm_num) fun y hy =>
      (hchY y hy).abs_le (by linarith)
  induction N generalizing k X with
  | zero =>
    have hrest : 0 ≤ max 0 (N₀ + 1 - k) * (2 * δ / s) := by positivity
    have h := hX.specNorm_sub_cfc_sign_le hε'.le fun y hy =>
      (hch y hy).abs_one_sub_sq_le hs hδs hε' hδε hε'₁ (by simpa using hN)
    rw [newtonSchulzLoop, specNorm_sub_comm]
    linarith
  | succ N ih =>
    rw [newtonSchulzLoop]
    by_cases ht : newtonSchulzTest M (M.div ε (M.ofNat (4 * n))) X = true
    · rw [if_pos ht, specNorm_sub_comm]
      have hrest : 0 ≤ max 0 (N₀ + 1 - k) * (2 * δ / s) := by positivity
      have := specNorm_sub_cfc_sign_le_of_newtonSchulzTest hM hμ hu₀ hτ₀ hτ hΩ hn hε hε₁ hk hX
        (hXn hX hch) ht
      linarith
    · rw [if_neg ht]
      have hkN : (k : ℝ) < N₀ := by
        by_contra hk'
        exact ht (hM.newtonSchulzTest_of_forall_mem_spectrum hμ hu₀ hτ₀ hτ hΩ hn hε hε₁ hk hX
          (hXn hX hch) fun y hy =>
            (hch y hy).abs_one_sub_sq_le hs hδs hε' hδε hε'₁ (not_lt.mp hk'))
      obtain ⟨hchY, hstep⟩ :=
        hM.forall_isNewtonSchulzChain_and_specNorm_cfc_sign_sub_cfc_sign_le hμ hu₀
        (unitRoundoff_bounds hn hμ hu₀ hε₁ hk).2 hτ₀ hτ
        (by linarith) hs hs₁ hδs hX hch
      have hIH := ih (k + 1) (newtonSchulzRounded M X)
        (hM.isHermitian_decodeMatrix_newtonSchulzRounded X) hchY (by push_cast at hN ⊢; linarith)
      have htri := specNorm_add_le
        (cfc Real.sign (decodeMatrix dec X) -
          cfc Real.sign (decodeMatrix dec (newtonSchulzRounded M X)))
        (cfc Real.sign (decodeMatrix dec (newtonSchulzRounded M X)) - decodeMatrix dec
          (newtonSchulzLoop M (M.div ε (M.ofNat (4 * n))) N (newtonSchulzRounded M X)))
      rw [sub_add_sub_cancel] at htri
      push_cast at hIH
      rw [max_eq_right (by linarith)] at hIH ⊢
      linarith

/-! ### The start of the iteration -/

/-- The start $\mathbf{A}_0 = \mathrm{fl}(\mathbf{A}/b)$ of the iteration: if every eigenvalue of
the Hermitian $\mathbf{A}$ has modulus at least $a > 0$ and $\|\mathbf{A}\|_2 \le b$, then
$a \le b$, the eigenvalue moduli of $\mathbf{A}_0$ lie within $e = (\sqrt n + 1)u$ of
$[a/b, 1]$, and the rounding moves the sign by at most $2e/(a/b)$. -/
private theorem FloatMachine.IsArithAccurate.abs_mem_spectrum_hermScale_and_specNorm_cfc_sign_sub_le
    (hM : M.IsArithAccurate dec u τ Ω μ) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1)
    (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) {a : ℝ} {b : F} (ha : 0 < a)
    (hspec : ∀ x ∈ spectrum ℝ (decodeMatrix dec A), a ≤ |x|)
    (hb : specNorm (decodeMatrix dec A) ≤ dec b) :
    a ≤ dec b ∧ (∀ y ∈ spectrum ℝ (decodeMatrix dec (M.hermScale A b)),
      a / dec b - (√(n : ℝ) + 1) * u ≤ |y| ∧ |y| ≤ 1 + (√(n : ℝ) + 1) * u) ∧
    specNorm (cfc Real.sign (decodeMatrix dec A) -
      cfc Real.sign (decodeMatrix dec (M.hermScale A b))) ≤
        2 * ((√(n : ℝ) + 1) * u) / (a / dec b) := by
  set Ad := decodeMatrix dec A
  have hab : a ≤ dec b := by
    have hx := hA.eigenvalue_mem_spectrum (k := 0) (by simpa using hn)
    exact ((hspec _ hx).trans (hA.abs_le_specNorm_of_mem_spectrum hx)).trans hb
  have hb₀ : 0 < dec b := ha.trans_le hab
  have hA₀ : (decodeMatrix dec (M.hermScale A b)).IsHermitian :=
    hM.isHermitian_decodeMatrix_hermFrom _ _
  have hAs : ((dec b)⁻¹ • Ad).IsHermitian := hA.smul (IsSelfAdjoint.all _)
  have hAs₁ : specNorm ((dec b)⁻¹ • Ad) ≤ 1 :=
    hAs.specNorm_le_of_forall_mem_spectrum_abs_le zero_le_one fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hA.exists_mem_spectrum_eq_mul _ hy
      rw [abs_mul, abs_of_pos (inv_pos.mpr hb₀), inv_mul_le_one₀ hb₀]
      exact (hA.abs_le_specNorm_of_mem_spectrum hx).trans hb
  have hrx : ∀ x ∈ spectrum ℝ Ad, a / dec b ≤ |(dec b)⁻¹ * x| := fun x hx => by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hb₀), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hspec x hx) (inv_pos.mpr hb₀).le
  have he : specNorm ((dec b)⁻¹ • Ad - decodeMatrix dec (M.hermScale A b)) ≤
      (√(n : ℝ) + 1) * u := by
    refine (hM.specNorm_sub_decodeMatrix_hermScale_le hu₀ hτ₀ hA hb₀.ne'
      (by rw [abs_of_pos hb₀, div_le_iff₀ hb₀]; nlinarith [specNorm_nonneg Ad])).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hAs₁ (by positivity : (0 : ℝ) ≤ u * √(n : ℝ)),
      mul_le_mul_of_nonneg_left hτ hu₀]
  refine ⟨hab, fun y hy => ?_, ?_⟩
  · obtain ⟨w, hw, hwy⟩ := hAs.exists_mem_spectrum_abs_sub_le hA₀ hy
    have hw₁ := (hAs.abs_le_specNorm_of_mem_spectrum hw).trans hAs₁
    obtain ⟨x, hx, rfl⟩ := hA.exists_mem_spectrum_eq_mul _ hw
    have h₁ := abs_sub_abs_le_abs_sub ((dec b)⁻¹ * x) y
    have h₂ := abs_sub_abs_le_abs_sub y ((dec b)⁻¹ * x)
    rw [abs_sub_comm] at h₂
    constructor <;> linarith [hrx x hx, hwy.trans he]
  · have hsign := hAs.specNorm_cfc_sign_sub_cfc_sign_le hA₀ (div_pos ha hb₀) fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hA.exists_mem_spectrum_eq_mul _ hy
      exact hrx x hx
    rw [cfc_sign_smul hA (inv_pos.mpr hb₀)] at hsign
    exact hsign.trans (div_le_div_of_nonneg_right (by linarith) (div_pos ha hb₀).le)

/-- The size condition of Theorem 2.6 in terms of the step error
$\delta = 4\sqrt n(8 + \mu(n))u$ of Lemma 2.1. -/
private theorem stepError_bounds_of_mul_le (hn : 0 < n) {μn u r ε N₀ : ℝ} (hμ : 0 ≤ μn)
    (hu₀ : 0 ≤ u) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (hε : 0 < ε) (hε₁ : ε ≤ 1 / 2) (hN₀ : 0 ≤ N₀)
    (hu : 640 * n * √(n : ℝ) * (8 + μn) * (N₀ + 1) * u ≤ r * ε) :
    160 * n * (4 * √(n : ℝ) * (8 + μn) * u) ≤ r * ε ∧ 640 * n * (8 + μn) * u ≤ ε ∧
      20 * (4 * √(n : ℝ) * (8 + μn) * u) ≤ r / 2 ∧
      10 * (4 * √(n : ℝ) * (8 + μn) * u) ≤ ε / (16 * n) ∧
      (√(n : ℝ) + 1) * u ≤ 4 * √(n : ℝ) * (8 + μn) * u / 16 := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn₁
  have hδ₀ : 0 ≤ 4 * √(n : ℝ) * (8 + μn) * u := by positivity
  have hX : 0 ≤ n * (8 + μn) * u := by positivity
  have hrε : r * ε ≤ ε := mul_le_of_le_one_left hε.le hr₁
  have hrε₂ : r * ε ≤ r / 2 := by nlinarith
  have hK₁ : 160 * n * (4 * √(n : ℝ) * (8 + μn) * u) ≤ r * ε := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n) hδ₀]
  have hnδ := mul_le_mul_of_nonneg_right hn₁ hδ₀
  refine ⟨hK₁, by nlinarith [mul_le_mul_of_nonneg_left hsqn hX], by nlinarith,
    by rw [le_div_iff₀ (by positivity)]; nlinarith, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hsqn hu₀, mul_nonneg (mul_nonneg
    (Real.sqrt_nonneg (n : ℝ)) hμ) hu₀]

/-- **Accuracy of the Newton–Schulz sign algorithm** (Theorem 2.6): under the arithmetic contract
`NLAlib.FloatMachine.IsArithAccurate` $u$ $\tau$ $\Omega$ with product constant $\mu$,
$\mu(n) \ge 0$, $u \ge 0$, $0 \le \tau$, $2n\tau \le 1$ and $9(n + 1) \le \Omega$, let the
stored $\mathbf{A}$ have Hermitian decoding (written $\mathbf{A}$) with
$\|\mathbf{A}\|_2 \le b$ and every eigenvalue of modulus at least $a > 0$, for stored $b$ and
$\varepsilon$ with $0 < \varepsilon \le 1/2$ (decoded values). With $N_0 = N(a/(2b),
\varepsilon/(16n))$ (`NLAlib.newtonSchulzSteps`), if
$$640\, n^{3/2}\,(8 + \mu(n))\,(N_0 + 1)\,u \le \frac{a}{b}\,\varepsilon$$
and the step limit is at least $N_0$, then
$$\|\operatorname{sign}(\mathbf{A}) - \mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)\|_2 \le
\varepsilon \,,$$
$\mathsf{newtonSchulzSign}$ the algorithm `NLAlib.newtonSchulzSign`. [Shah2024, Theorem 2.6],
there with
$u \le (a/b)\varepsilon/(4\max(N n\mu_g(n, 1.1), n^2))$, $N = N(a/b, \varepsilon/(8n))$ and
the contour bound of Lemma 2.2; here the perturbation bound is dimension-free and the factor
$n^{3/2}$ comes from the Hermitian rounding and the stopping test.
Result: newton-schulz-sign-accuracy -/
theorem FloatMachine.IsArithAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) {a : ℝ} {b ε : F} (ha : 0 < a)
    (hspec : ∀ x ∈ spectrum ℝ (decodeMatrix dec A), a ≤ |x|)
    (hb : specNorm (decodeMatrix dec A) ≤ dec b) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1 / 2)
    (hu : 640 * n * √(n : ℝ) * (8 + μ n) *
      (newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) + 1) * u ≤ a / dec b * dec ε)
    {N : ℕ} (hN : newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) ≤ N) :
    specNorm (cfc Real.sign (decodeMatrix dec A) - decodeMatrix dec (newtonSchulzSign M ε b N A)) ≤
      dec ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim (_ - _) 0, specNorm_zero]
    exact hε.le
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hab, hA₀s, hsign⟩ :=
    hM.abs_mem_spectrum_hermScale_and_specNorm_cfc_sign_sub_le hu₀ hτ₀ hτ hΩ hn hA ha hspec hb
  have hb₀ : 0 < dec b := ha.trans_le hab
  set r := a / dec b with hr
  have hr₀ : 0 < r := div_pos ha hb₀
  have hr₁ : r ≤ 1 := (div_le_one hb₀).mpr hab
  have hs : a / (2 * dec b) = r / 2 := by rw [hr]; field_simp
  rw [hs] at hu hN
  set N₀ := newtonSchulzSteps (r / 2) (dec ε / (16 * n))
  have hN₀ : 0 ≤ N₀ := newtonSchulzSteps_nonneg (by positivity) (by linarith) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  set δ := 4 * √(n : ℝ) * (8 + μ n) * u
  have hδ₀ : 0 ≤ δ := by positivity
  have hK : 160 * n * δ * (N₀ + 1) ≤ r * dec ε := by linarith
  obtain ⟨hK₁, hk, hδs, hδε, he⟩ :=
    stepError_bounds_of_mul_le hn hμ hu₀ hr₀.le hr₁ hε hε₁ hN₀ hu
  have hloop := specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzLoop_le hM hμ hu₀ hτ₀ hτ hΩ hn hε
    hε₁ hk (by positivity) (by linarith) hδs hδε N 0 (M.hermScale A b)
    (hM.isHermitian_decodeMatrix_hermFrom _ _)
    (fun y hy => isNewtonSchulzChain_zero hδ₀ (by linarith [(hA₀s y hy).1])
      (by linarith [(hA₀s y hy).2])) (by simpa using hN)
  rw [Nat.cast_zero, sub_zero, max_eq_right (by linarith)] at hloop
  change _ ≤ 2 / 3 * dec ε + (N₀ + 1) * (2 * δ / (r / 2)) at hloop
  have htri := specNorm_add_le (cfc Real.sign (decodeMatrix dec A) - cfc Real.sign
    (decodeMatrix dec (M.hermScale A b))) (cfc Real.sign (decodeMatrix dec (M.hermScale A b)) -
      decodeMatrix dec (newtonSchulzSign M ε b N A))
  rw [sub_add_sub_cancel, newtonSchulzSign] at htri
  have h₁ : 2 * ((√(n : ℝ) + 1) * u) / r ≤ dec ε / 160 := by
    have := mul_nonneg (sub_nonneg.mpr hn₁) hδ₀
    rw [div_le_iff₀ hr₀]; linarith
  have h₂ : (N₀ + 1) * (2 * δ / (r / 2)) ≤ dec ε / 40 := by
    have := mul_nonneg (mul_nonneg (sub_nonneg.mpr hn₁) hδ₀) (by linarith : 0 ≤ N₀ + 1)
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; linarith
  exact htri.trans (by linarith [hsign.trans h₁])

/-- The step count $N(x, 0)$ is nonnegative (the logarithms of `0` are `0`). -/
private theorem newtonSchulzSteps_zero_nonneg (x : ℝ) : 0 ≤ newtonSchulzSteps x 0 := by
  have h : 0 ≤ Real.logb 2 (min |x| (1 / 2))⁻¹ := by
    rcases (le_min (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).eq_or_lt with h | h
    · rw [← h, inv_zero, Real.logb_zero]
    · exact Real.logb_nonneg one_lt_two
        ((one_le_inv₀ h).mpr ((min_le_right _ _).trans (by norm_num)))
  simp only [newtonSchulzSteps, inv_zero, Real.logb_zero, add_zero]
  linarith

/-- **The Newton–Schulz test passes within the step count**: under the arithmetic contract
`NLAlib.FloatMachine.IsArithAccurate` $u$ $\tau$ $\Omega$ with product constant $\mu$,
$\mu(n) \ge 0$, $u \ge 0$, $0 \le \tau$, $2n\tau \le 1$ and $9(n + 1) \le \Omega$, let the stored
$\mathbf{A}$ have Hermitian decoding (written $\mathbf{A}$) with $\|\mathbf{A}\|_2 \le b$ and every
eigenvalue of modulus at least $a > 0$, for stored $b$ and $\varepsilon$ with
$0 < \varepsilon \le 1/2$ (decoded values). With $N_0 = N(a/(2b), \varepsilon/(16n))$
(`NLAlib.newtonSchulzSteps`), if
$$640\, n^{3/2}\,(8 + \mu(n))\,(N_0 + 1)\,u \le \frac{a}{b}\,\varepsilon \,,$$
then the stopping test `NLAlib.newtonSchulzTest` at the computed threshold
$\mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$ passes at some iterate $k \le N_0 + 1$ of the rounded
step `NLAlib.newtonSchulzRounded` from the stored $\mathbf{A}/b$. [Shah2024, proof of
Theorem 2.6], where the iteration count is shown but not stated. -/
theorem FloatMachine.IsArithAccurate.exists_le_newtonSchulzTest_iterate
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) {a : ℝ} {b ε : F} (ha : 0 < a)
    (hspec : ∀ x ∈ spectrum ℝ (decodeMatrix dec A), a ≤ |x|)
    (hb : specNorm (decodeMatrix dec A) ≤ dec b) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1 / 2)
    (hu : 640 * n * √(n : ℝ) * (8 + μ n) *
      (newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) + 1) * u ≤ a / dec b * dec ε) :
    ∃ k : ℕ, (k : ℝ) ≤ newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) + 1 ∧
      newtonSchulzTest M (M.div ε (M.ofNat (4 * n)))
        ((newtonSchulzRounded M)^[k] (M.hermScale A b)) = true := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, ?_, by simp [newtonSchulzTest]⟩
    rw [Nat.cast_zero, mul_zero, div_zero]
    linarith [newtonSchulzSteps_zero_nonneg (a / (2 * dec b))]
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hab, hA₀s, -⟩ :=
    hM.abs_mem_spectrum_hermScale_and_specNorm_cfc_sign_sub_le hu₀ hτ₀ hτ hΩ hn hA ha hspec hb
  have hb₀ : 0 < dec b := ha.trans_le hab
  set r := a / dec b with hr
  have hr₀ : 0 < r := div_pos ha hb₀
  have hr₁ : r ≤ 1 := (div_le_one hb₀).mpr hab
  have hs : a / (2 * dec b) = r / 2 := by rw [hr]; field_simp
  rw [hs] at hu ⊢
  set N₀ := newtonSchulzSteps (r / 2) (dec ε / (16 * n))
  have hN₀ : 0 ≤ N₀ := newtonSchulzSteps_nonneg (by positivity) (by linarith) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  set δ := 4 * √(n : ℝ) * (8 + μ n) * u
  have hδ₀ : 0 ≤ δ := by positivity
  obtain ⟨-, hk, hδs, hδε, he⟩ :=
    stepError_bounds_of_mul_le hn hμ hu₀ hr₀.le hr₁ hε hε₁ hN₀ hu
  have hu₁ := (unitRoundoff_bounds hn hμ hu₀ hε₁ hk).2
  have hε' : 0 < dec ε / (16 * n) := by positivity
  have hε'₁ : dec ε / (16 * n) ≤ 3 / 80 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  -- every iterate lies on chains, and the test passes at `⌈N₀⌉`
  have hit : ∀ j, (decodeMatrix dec ((newtonSchulzRounded M)^[j] (M.hermScale A b))).IsHermitian ∧
      ∀ y ∈ spectrum ℝ (decodeMatrix dec ((newtonSchulzRounded M)^[j] (M.hermScale A b))),
        IsNewtonSchulzChain (r / 2) δ y j := by
    intro j
    induction j with
    | zero => exact ⟨hM.isHermitian_decodeMatrix_hermFrom _ _, fun y hy =>
        isNewtonSchulzChain_zero hδ₀ (by linarith [(hA₀s y hy).1]) (by linarith [(hA₀s y hy).2])⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨hM.isHermitian_decodeMatrix_newtonSchulzRounded _,
        (hM.forall_isNewtonSchulzChain_and_specNorm_cfc_sign_sub_cfc_sign_le hμ hu₀ hu₁ hτ₀ hτ
          (by linarith) (by positivity) (by linarith) hδs ih.1 ih.2).1⟩
  obtain ⟨hX, hch⟩ := hit ⌈N₀⌉₊
  refine ⟨⌈N₀⌉₊, (Nat.ceil_lt_add_one hN₀).le, ?_⟩
  exact hM.newtonSchulzTest_of_forall_mem_spectrum hμ hu₀ hτ₀ hτ hΩ hn hε hε₁ hk hX
    (hX.specNorm_le_of_forall_mem_spectrum_abs_le (by norm_num) fun y hy =>
      (hch y hy).abs_le (by linarith))
    fun y hy => (hch y hy).abs_one_sub_sq_le (by positivity) hδs hε' hδε hε'₁ (Nat.le_ceil _)

/-! ### Geometric growth of the least eigenvalue modulus -/

/-- For $t \le \lvert x \rvert \le 11/10$, $\lvert g(x) \rvert \ge \min(11t/8, 11/16)$. -/
private theorem min_le_abs_newtonSchulz {t x : ℝ} (ht : 0 ≤ t) (htx : t ≤ |x|)
    (hx : |x| ≤ 11 / 10) : min (11 / 8 * t) (11 / 16) ≤ |newtonSchulz x| := by
  have hx0 := abs_nonneg x
  have hg : |newtonSchulz x| = |x| * (3 - |x| ^ 2) / 2 := by
    unfold newtonSchulz
    rw [abs_div, abs_mul, sq_abs, abs_of_pos (by nlinarith [sq_abs x] : (0 : ℝ) < 3 - x ^ 2),
      abs_two]
  rw [hg]
  rcases le_or_gt |x| (1 / 2) with h | h
  · exact (min_le_left _ _).trans (by nlinarith)
  · have h₁ : 0 ≤ 11 / 4 - |x| ^ 2 - |x| / 2 := by nlinarith
    exact (min_le_right _ _).trans (by nlinarith [mul_nonneg (sub_nonneg.2 h.le) h₁])

/-- The potential $7\delta/t$ pays for one step at the new bound
$t' = \min(11t/8 - \delta, 1/2)$, up to $4\delta$. -/
private theorem nine_mul_div_min_le {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) (ht₁ : 12 * δ ≤ t)
    (ht₂ : t ≤ 1 / 2) : 9 * δ / min (11 / 8 * t - δ) (1 / 2) ≤ 7 * δ / t + 4 * δ := by
  rcases min_cases (11 / 8 * t - δ) (1 / 2 : ℝ) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · have hq : 9 * δ / (11 / 8 * t - δ) ≤ 7 * δ / t := by
      rw [div_le_div_iff₀ (by linarith) ht]
      nlinarith [mul_le_mul_of_nonneg_left ht₁ hδ]
    linarith
  · have : 14 * δ ≤ 7 * δ / t := by rw [le_div_iff₀ ht]; nlinarith
    linarith

/-- One rounded step keeps every eigenvalue on a perturbed scalar chain, raises the lower bound
`t` on the eigenvalue moduli to `min (11t/8 − δ) (1/2)`, and moves the sign by at most `2δ`
over the new bound, for `δ` the error of one step
(`NLAlib.FloatMachine.IsArithAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add`). -/
private theorem newtonSchulzRounded_chain_and_specNorm_le_add
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n)
    (hu₀ : 0 ≤ u) (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1)
    (hΩ : 9 ≤ Ω) {s t : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1 / 2)
    (hδ : 20 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) ≤ s) (ht : 0 < t)
    (ht₁ : 12 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) ≤ t) {k : ℕ}
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hch : ∀ y ∈ spectrum ℝ (decodeMatrix dec X),
      IsNewtonSchulzChain s ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) y k)
    (hXt : ∀ y ∈ spectrum ℝ (decodeMatrix dec X), t ≤ |y|) :
    (∀ z ∈ spectrum ℝ (decodeMatrix dec (newtonSchulzRounded M X)),
      IsNewtonSchulzChain s ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) z (k + 1) ∧
        min (11 / 8 * t - (4 * μ n + 10 + 10 * √(n : ℝ)) * u) (1 / 2) ≤ |z|) ∧
    specNorm (cfc Real.sign (decodeMatrix dec X) -
      cfc Real.sign (decodeMatrix dec (newtonSchulzRounded M X))) ≤
        2 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) /
          min (11 / 8 * t - (4 * μ n + 10 + 10 * √(n : ℝ)) * u) (1 / 2) := by
  set δ := (4 * μ n + 10 + 10 * √(n : ℝ)) * u
  set t' := min (11 / 8 * t - δ) (1 / 2)
  have hδ₀ : 0 ≤ δ := by positivity
  have ht' : 0 < t' := lt_min (by linarith) (by norm_num)
  have hY := hM.isHermitian_decodeMatrix_newtonSchulzRounded X
  have hgX : (cfc newtonSchulz (decodeMatrix dec X)).IsHermitian := cfc_predicate _ _
  have hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10 :=
    hX.specNorm_le_of_forall_mem_spectrum_abs_le (by norm_num) fun y hy =>
      (hch y hy).abs_le (by linarith)
  have herr : specNorm (cfc newtonSchulz (decodeMatrix dec X) -
      decodeMatrix dec (newtonSchulzRounded M X)) ≤ δ := by
    rw [hX.cfc_newtonSchulz]
    exact hM.specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add hμ hu₀ hu hτ₀ hτ hΩ hX hXn
  have ht'δ : t' ≤ min (11 / 8 * t) (11 / 16) - δ := by
    rcases min_cases (11 / 8 * t) (11 / 16 : ℝ) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (by linarith)
  have hchY : ∀ z ∈ spectrum ℝ (decodeMatrix dec (newtonSchulzRounded M X)),
      IsNewtonSchulzChain s δ z (k + 1) ∧ t' ≤ |z| := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hgX.exists_mem_spectrum_abs_sub_le hY hz
    rw [cfc_map_spectrum newtonSchulz (decodeMatrix dec X) hX.isSelfAdjoint
      ((decodeMatrix dec X).finite_real_spectrum.continuousOn _)] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    have hyz : |z - newtonSchulz y| ≤ δ := by rw [abs_sub_comm]; exact hwz.trans herr
    refine ⟨(hch y hy).succ hδ₀ hyz, ?_⟩
    have h₁ := min_le_abs_newtonSchulz ht.le (hXt y hy) ((hch y hy).abs_le (by linarith))
    have h₂ := abs_sub_abs_le_abs_sub (newtonSchulz y) z
    rw [abs_sub_comm (newtonSchulz y)] at h₂
    linarith
  refine ⟨hchY, ?_⟩
  have h3 : (11 / 10 : ℝ) < √3 := Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [← hX.cfc_sign_cfc_newtonSchulz fun y hy =>
    ⟨hs.trans_le ((hch y hy).le_abs hs₁ hδ), ((hch y hy).abs_le (by linarith)).trans_lt h3⟩,
    specNorm_sub_comm]
  refine (hY.specNorm_cfc_sign_sub_cfc_sign_le hgX ht' fun z hz => (hchY z hz).2).trans ?_
  rw [specNorm_sub_comm]
  gcongr

/-! ### The loop, with the step errors summed geometrically -/

/-- **The loop invariant**: from an iterate at step `k` whose eigenvalues lie on perturbed scalar
chains and have modulus at least `t`, the loop returns a matrix within `2ε/3 + 7δ/t` plus `4δ`
per remaining step of the sign. -/
private theorem specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzLoop_le_add
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F} (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 1 / 2) (hk : 640 * n * (8 + μ n) * u ≤ dec ε) {s : ℝ} (hs : 0 < s)
    (hs₁ : s ≤ 1 / 2) (hδs : 20 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) ≤ s)
    (hδε : 10 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) ≤ dec ε / (16 * n)) (N k : ℕ)
    (X : Matrix (Fin n) (Fin n) (F × F)) (hX : (decodeMatrix dec X).IsHermitian)
    (hch : ∀ y ∈ spectrum ℝ (decodeMatrix dec X),
      IsNewtonSchulzChain s ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) y k)
    {t : ℝ} (ht : 0 < t) (ht₁ : 12 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) ≤ t)
    (ht₂ : t ≤ 1 / 2) (hXt : ∀ y ∈ spectrum ℝ (decodeMatrix dec X), t ≤ |y|)
    (hN : newtonSchulzSteps s (dec ε / (16 * n)) ≤ k + N) :
    specNorm (cfc Real.sign (decodeMatrix dec X) -
      decodeMatrix dec (newtonSchulzLoop M (M.div ε (M.ofNat (4 * n))) N X)) ≤
        2 / 3 * dec ε + 7 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) / t +
          max 0 (newtonSchulzSteps s (dec ε / (16 * n)) + 1 - k) *
            (4 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u)) := by
  set δ := (4 * μ n + 10 + 10 * √(n : ℝ)) * u
  set N₀ := newtonSchulzSteps s (dec ε / (16 * n))
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ₀ : 0 ≤ δ := by positivity
  have hε' : 0 < dec ε / (16 * n) := by positivity
  have hε'₁ : dec ε / (16 * n) ≤ 3 / 80 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hXn : ∀ {j : ℕ} {Y : Matrix (Fin n) (Fin n) (F × F)}, (decodeMatrix dec Y).IsHermitian →
      (∀ y ∈ spectrum ℝ (decodeMatrix dec Y), IsNewtonSchulzChain s δ y j) →
        specNorm (decodeMatrix dec Y) ≤ 11 / 10 := fun hY hchY =>
    hY.specNorm_le_of_forall_mem_spectrum_abs_le (by norm_num) fun y hy =>
      (hchY y hy).abs_le (by linarith)
  induction N generalizing k X t with
  | zero =>
    have hrest : 0 ≤ max 0 (N₀ + 1 - k) * (4 * δ) := by positivity
    have hpot : 0 ≤ 7 * δ / t := by positivity
    have h := hX.specNorm_sub_cfc_sign_le hε'.le fun y hy =>
      (hch y hy).abs_one_sub_sq_le hs hδs hε' hδε hε'₁ (by simpa using hN)
    have hε'₂ : dec ε / (16 * n) ≤ 2 / 3 * dec ε := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    rw [newtonSchulzLoop, specNorm_sub_comm]
    linarith
  | succ N ih =>
    rw [newtonSchulzLoop]
    by_cases htest : newtonSchulzTest M (M.div ε (M.ofNat (4 * n))) X = true
    · rw [if_pos htest, specNorm_sub_comm]
      have hrest : 0 ≤ max 0 (N₀ + 1 - k) * (4 * δ) := by positivity
      have hpot : 0 ≤ 7 * δ / t := by positivity
      have := specNorm_sub_cfc_sign_le_of_newtonSchulzTest hM hμ hu₀ hτ₀ hτ hΩ hn hε hε₁ hk hX
        (hXn hX hch) htest
      linarith
    · rw [if_neg htest]
      have hkN : (k : ℝ) < N₀ := by
        by_contra hk'
        exact htest (hM.newtonSchulzTest_of_forall_mem_spectrum hμ hu₀ hτ₀ hτ hΩ hn hε hε₁ hk
          hX (hXn hX hch) fun y hy =>
            (hch y hy).abs_one_sub_sq_le hs hδs hε' hδε hε'₁ (not_lt.mp hk'))
      obtain ⟨hchY, hstep⟩ := newtonSchulzRounded_chain_and_specNorm_le_add hM hμ hu₀
        (unitRoundoff_bounds hn hμ hu₀ hε₁ hk).2 hτ₀ hτ (by linarith) hs hs₁ hδs ht ht₁ hX hch hXt
      have ht' : t ≤ min (11 / 8 * t - δ) (1 / 2) := le_min (by linarith) ht₂
      have hIH := ih (k := k + 1) (X := newtonSchulzRounded M X)
        (hX := hM.isHermitian_decodeMatrix_newtonSchulzRounded X)
        (hch := fun z hz => (hchY z hz).1) (ht := ht.trans_le ht') (ht₁ := ht₁.trans ht')
        (ht₂ := min_le_right _ _) (hXt := fun z hz => (hchY z hz).2)
        (hN := by push_cast at hN ⊢; linarith)
      have htri := specNorm_add_le
        (cfc Real.sign (decodeMatrix dec X) -
          cfc Real.sign (decodeMatrix dec (newtonSchulzRounded M X)))
        (cfc Real.sign (decodeMatrix dec (newtonSchulzRounded M X)) - decodeMatrix dec
          (newtonSchulzLoop M (M.div ε (M.ofNat (4 * n))) N (newtonSchulzRounded M X)))
      rw [sub_add_sub_cancel] at htri
      push_cast at hIH
      rw [max_eq_right (by linarith)] at hIH ⊢
      have hpot := nine_mul_div_min_le hδ₀ ht ht₁ ht₂
      have hsplit : 9 * δ / min (11 / 8 * t - δ) (1 / 2) =
          2 * δ / min (11 / 8 * t - δ) (1 / 2) + 7 * δ / min (11 / 8 * t - δ) (1 / 2) := by
        ring
      linarith

/-- The two size conditions of the geometric form of Theorem 2.6 in terms of the step error
$\delta = (4\mu(n) + 10 + 10\sqrt n)u$. -/
private theorem stepError_bounds (hn : 0 < n) {μn u r ε N₀ δ : ℝ} (hμ : 0 ≤ μn) (hu₀ : 0 ≤ u)
    (hr₀ : 0 ≤ r) (hε₁ : ε ≤ 1 / 2) (hN₀ : 0 ≤ N₀)
    (hδ : δ = (4 * μn + 10 + 10 * √(n : ℝ)) * u)
    (hu : 32 * (4 * μn + 10 + 10 * √(n : ℝ)) * u ≤ r * ε)
    (hstop : 640 * (n + N₀ + 1) * (4 * μn + 10 + 10 * √(n : ℝ)) * u ≤ ε) :
    32 * δ ≤ r * ε ∧ 640 * (N₀ + 1) * δ ≤ ε ∧ 640 * n * (8 + μn) * u ≤ ε ∧
      20 * δ ≤ r / 2 ∧ 10 * δ ≤ ε / (16 * n) ∧ (√(n : ℝ) + 1) * u ≤ δ / 10 := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqn : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hδ₀ : 0 ≤ δ := by rw [hδ]; positivity
  have h₁ : 32 * δ ≤ r * ε := by rw [hδ]; linarith
  have h₂ : 640 * (n + N₀ + 1) * δ ≤ ε := by rw [hδ]; linarith
  have h₃ : 640 * n * δ ≤ ε := by nlinarith [mul_nonneg (by linarith : 0 ≤ N₀ + 1) hδ₀]
  have h₄ : (8 + μn) * u ≤ δ := by
    rw [hδ]; nlinarith [mul_nonneg hμ hu₀, mul_nonneg hsqn hu₀]
  refine ⟨h₁, by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n) hδ₀], ?_,
    by nlinarith [mul_le_mul_of_nonneg_left hε₁ hr₀],
    by rw [le_div_iff₀ (by positivity)]; nlinarith, by rw [hδ]; nlinarith [mul_nonneg hμ hu₀]⟩
  nlinarith [mul_le_mul_of_nonneg_left h₄ (by positivity : (0 : ℝ) ≤ 640 * n)]

/-- The potential at the start bound $\min(r - \delta/10, 1/2)$ under
$32\delta \le r\varepsilon$. -/
private theorem seven_mul_div_min_le {δ r ε : ℝ} (hδ₀ : 0 ≤ δ) (hε : 0 < ε) (hε₁ : ε ≤ 1 / 2)
    (hδr : 32 * δ ≤ r * ε) (hr : 0 < r - δ / 10) :
    7 * δ / min (r - δ / 10) (1 / 2) ≤ ε / 4 + 14 * δ := by
  rcases min_cases (r - δ / 10) (1 / 2 : ℝ) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · rw [div_le_iff₀ hr]
    nlinarith [mul_nonneg hδ₀ hr.le, mul_nonneg hδ₀ hε.le]
  · rw [div_div_eq_mul_div, div_one]; linarith

/-- **Accuracy of the Newton–Schulz sign algorithm, step errors summed geometrically**
(Theorem 2.6): under the arithmetic contract `NLAlib.FloatMachine.IsArithAccurate` $u$ $\tau$
$\Omega$ with product constant $\mu$, $\mu(n) \ge 0$, $u \ge 0$, $0 \le \tau$, $2n\tau \le 1$ and
$9(n + 1) \le \Omega$, let the stored $\mathbf{A}$ have Hermitian decoding with
$\|\mathbf{A}\|_2 \le b$ and every eigenvalue of modulus at least $a > 0$, for stored $b$ and
$\varepsilon$ with $0 < \varepsilon \le 1/2$ (decoded values). With
$\nu = 4\mu(n) + 10 + 10\sqrt n$ and $N_0 = N(a/(2b), \varepsilon/(16n))$
(`NLAlib.newtonSchulzSteps`), if
$$32\,\nu u \le \frac ab\,\varepsilon \,, \qquad 640\,(n + N_0 + 1)\,\nu u \le \varepsilon$$
and the step limit is at least $N_0$, then `NLAlib.newtonSchulzSign` is within $\varepsilon$ of
$\operatorname{sign}\mathbf{A}$ in the spectral norm. Compared with
`NLAlib.FloatMachine.IsArithAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le`
($640n^{3/2}(8 + \mu(n))(N_0 + 1)u \le (a/b)\varepsilon$), the step count and the dimension
factor of the stopping test leave the binding condition: while the least eigenvalue modulus is at
most $1/2$ it grows by the factor $11/8$
(`NLAlib.div_mul_abs_le_abs_newtonSchulz_of_abs_le`), so the step errors form a geometric series.
[Shah2024, Theorem 2.6]. -/
theorem
    FloatMachine.IsArithAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le_of_mul_le
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) {a : ℝ} {b ε : F} (ha : 0 < a)
    (hspec : ∀ x ∈ spectrum ℝ (decodeMatrix dec A), a ≤ |x|)
    (hb : specNorm (decodeMatrix dec A) ≤ dec b) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1 / 2)
    (hu : 32 * (4 * μ n + 10 + 10 * √(n : ℝ)) * u ≤ a / dec b * dec ε)
    (hstop : 640 * (n + newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) + 1) *
      (4 * μ n + 10 + 10 * √(n : ℝ)) * u ≤ dec ε)
    {N : ℕ} (hN : newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) ≤ N) :
    specNorm (cfc Real.sign (decodeMatrix dec A) - decodeMatrix dec (newtonSchulzSign M ε b N A)) ≤
      dec ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim (_ - _) 0, specNorm_zero]
    exact hε.le
  obtain ⟨hab, hA₀s, hsign⟩ :=
    hM.abs_mem_spectrum_hermScale_and_specNorm_cfc_sign_sub_le hu₀ hτ₀ hτ hΩ hn hA ha hspec hb
  have hb₀ : 0 < dec b := ha.trans_le hab
  set r := a / dec b with hr
  have hr₀ : 0 < r := div_pos ha hb₀
  have hr₁ : r ≤ 1 := (div_le_one hb₀).mpr hab
  have hs : a / (2 * dec b) = r / 2 := by rw [hr]; field_simp
  rw [hs] at hstop hN
  set N₀ := newtonSchulzSteps (r / 2) (dec ε / (16 * n))
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN₀ : 0 ≤ N₀ := newtonSchulzSteps_nonneg (by positivity) (by linarith) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  -- the size conditions in terms of the step error `δ` of one step
  set δ := (4 * μ n + 10 + 10 * √(n : ℝ)) * u with hδdef
  have hδ₀ : 0 ≤ δ := by positivity
  obtain ⟨hδr, hδN, hk, hδs, hδε, hδu⟩ :=
    stepError_bounds hn hμ hu₀ hr₀.le hε₁ hN₀ hδdef hu hstop
  set t₀ := min (r - δ / 10) (1 / 2)
  have ht₀ : 0 < t₀ := lt_min (by linarith) (by norm_num)
  have hδ₁ : δ ≤ 1 / 40 := by linarith
  have hch₀ : ∀ y ∈ spectrum ℝ (decodeMatrix dec (M.hermScale A b)),
      IsNewtonSchulzChain (r / 2) δ y 0 ∧ t₀ ≤ |y| := fun y hy =>
    ⟨isNewtonSchulzChain_zero hδ₀ (by linarith [(hA₀s y hy).1]) (by linarith [(hA₀s y hy).2]),
      (min_le_left _ _).trans (by linarith [(hA₀s y hy).1])⟩
  have hloop := specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzLoop_le_add hM hμ hu₀ hτ₀ hτ hΩ
    hn hε hε₁ hk (by positivity) (by linarith) hδs hδε N 0 (M.hermScale A b)
    (hM.isHermitian_decodeMatrix_hermFrom _ _) (fun y hy => (hch₀ y hy).1) ht₀
    (le_min (by linarith) (by linarith)) (min_le_right _ _) (fun y hy => (hch₀ y hy).2)
    (by simpa using hN)
  rw [Nat.cast_zero, sub_zero, max_eq_right (by linarith)] at hloop
  have htri := specNorm_add_le (cfc Real.sign (decodeMatrix dec A) - cfc Real.sign
    (decodeMatrix dec (M.hermScale A b))) (cfc Real.sign (decodeMatrix dec (M.hermScale A b)) -
      decodeMatrix dec (newtonSchulzSign M ε b N A))
  rw [sub_add_sub_cancel, newtonSchulzSign] at htri
  have h₁ : 2 * ((√(n : ℝ) + 1) * u) / r ≤ dec ε / 160 := by
    rw [div_le_iff₀ hr₀]; linarith
  -- the potential at the start: `7δ/t₀ ≤ ε/4 + 14δ`
  have h₂ : 7 * δ / t₀ ≤ dec ε / 4 + 14 * δ := seven_mul_div_min_le hδ₀ hε hε₁ hδr (by linarith)
  have h₃ := mul_nonneg hN₀ hδ₀
  exact htri.trans (by linarith [hsign.trans h₁])

end NLAlib
