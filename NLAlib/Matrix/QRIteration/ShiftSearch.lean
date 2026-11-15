/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.Strategy

/-!
# The shift search of $\mathrm{Sh}_{k,B}$ as a program performs it

The strategy `NLAlib.shqrShift` picks a successful shift by classical choice and tests
success with the potential $\psi_k$, a $k$-th root. A program tries the candidates in order and
takes the first one that it **accepts**: the step with shift polynomial $(z - s)^k$ has a
subdiagonal entry of modulus at most an absolute threshold $\tau$, or reduces the product of the
squared moduli of the last $k$ subdiagonal entries by $(1 - \gamma)^{2k}$. Both tests use only
the arithmetic operations, and a success in the sense of `NLAlib.IsShiftSuccess` is accepted, so
the search succeeds whenever the strategy does
([BanksGarzaVargasSrivastava2021, §4.2], lines 1–4 of $\mathrm{Sh}_{k,B}$, which also try the
candidates in order and stop at the first success). The potential and the radius of the
exceptional disk for $k = 2^m$ are $m$ square roots of products, so the program computes them
with the square root of the model.

## Main definitions

* `NLAlib.IsDecoupledAbs`: a subdiagonal entry of modulus at most an absolute threshold.
* `NLAlib.subdiagNormSqProd`: the product of the squared moduli of the last $k$ subdiagonal
  entries.
* `NLAlib.IsShiftAccept`: the acceptance test of a shift.
* `NLAlib.shqrAcceptShift`, `NLAlib.shqrAcceptStep`: the first accepted candidate, and the
  step with it.

## Main results

* `NLAlib.shqrShift_mem`: the strategy's shift is a Ritz value or a candidate.
* `NLAlib.IsShiftSuccess.isShiftAccept`: a success is accepted.
* `NLAlib.IsUpperHessenberg.isShiftAccept_of_det_eq_zero`: an eigenvalue shift is accepted.
* `NLAlib.exists_unitary_multiShiftedQRStep`,
  `NLAlib.IsUpperHessenberg.isUpperHessenberg_shqrAcceptStep`: the step is a unitary similarity
  and keeps the Hessenberg form.
* `NLAlib.IsUpperHessenberg.exists_mem_isShiftAccept`,
  `NLAlib.IsUpperHessenberg.isShiftAccept_shqrAcceptShift`: some candidate is accepted, and the
  search returns an accepted one.
* `NLAlib.hessenbergPotential_le_of_isShiftAccept`: acceptance without decoupling reduces the
  potential.
* `NLAlib.IsUpperHessenberg.isDecoupledAbs_or_hessenbergPotential_shqrAcceptStep_le`: one
  iteration of the search.
* `NLAlib.isDecoupledAbs_of_hessenbergPotential_le_pow`: a potential reduced long enough gives
  the absolute decoupling.
* `NLAlib.hessenbergPotential_two_pow_eq`, `NLAlib.exceptionalRadius_two_pow_eq`: the potential
  and the radius by square roots.
* `NLAlib.isDecoupledAbs_iff_normSq`: the decoupling test on squared real and imaginary parts.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- A square matrix is **decoupled at the absolute threshold** $\tau$ if some subdiagonal entry
has modulus at most $\tau$: $\lvert\mathbf{H}_{i+1,i}\rvert \le \tau$ for some $i < n$. With
$\tau = \delta\|\mathbf{H}_0\|_2$ this is `NLAlib.IsDecoupled` $\delta$ relative to the norm of
the starting matrix, which the shifted QR step keeps. -/
def IsDecoupledAbs (τ : ℝ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  ∃ i : Fin n, ‖H i.succ i.castSucc‖ ≤ τ

/-- The **product of the squared moduli of the last $k$ subdiagonal entries**,
$\prod_{n - k \le i < n}\lvert\mathbf{H}_{i+1,i}\rvert^2$, so that
$\psi_k(\mathbf{H})^{2k}$ is this product (`NLAlib.hessenbergPotential`). -/
noncomputable def subdiagNormSqProd (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), ‖H i.succ i.castSucc‖ ^ 2

/-- A shift $s$ is **accepted** at the threshold $\tau$, rate $\gamma$ and degree $k$ if the
degree $k$ step $\widehat{\mathbf{H}}$ with shift polynomial $(z - s)^k$ is decoupled at the
threshold $\tau$, or reduces the product of the last $k$ squared subdiagonal moduli by
$(1 - \gamma)^{2k}$. A test with the arithmetic operations only; for $\gamma \le 1$ the second
clause is $\psi_k(\widehat{\mathbf{H}}) \le (1 - \gamma)\psi_k(\mathbf{H})$. -/
def IsShiftAccept (τ γ : ℝ) (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ) :
    Prop :=
  IsDecoupledAbs τ (multiShiftedQRStep H (List.replicate k s)) ∨
    subdiagNormSqProd k (multiShiftedQRStep H (List.replicate k s)) ≤
      (1 - γ) ^ (2 * k) * subdiagNormSqProd k H

open Classical in
/-- The **first accepted shift** of the search, $k = 2^m$: the first of the Ritz values `ss`,
then the candidates `NLAlib.shqrCandidates` (the promising Ritz value and the exceptional
shifts), that `NLAlib.IsShiftAccept` accepts; the promising Ritz value if none is (which the
convergence theorem excludes). [BanksGarzaVargasSrivastava2021, §4.2], with the candidates tried
in order. -/
noncomputable def shqrAcceptShift (τ B θ α γ : ℝ) (m : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) : ℂ :=
  ((ss ++ shqrCandidates B θ α γ m H ss).find? fun s =>
    decide (IsShiftAccept τ γ (2 ^ m) H s)).getD (findRitz H m 1 ss)

/-- One **iteration of the search**, $k = 2^m$: the degree $k$ QR step with shift polynomial
$(z - s)^k$, $s$ the first accepted shift `NLAlib.shqrAcceptShift`. -/
noncomputable def shqrAcceptStep (τ B θ α γ : ℝ) (m : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  multiShiftedQRStep H (List.replicate (2 ^ m) (shqrAcceptShift τ B θ α γ m H ss))

/-- A shift that is an eigenvalue is accepted: for $\mathbf{H}$ upper Hessenberg of order
$n + 1 \ge 2$, $k \ge 1$ and $\tau \ge 0$, if $\det(\mathbf{H} - s\mathbf{I}) = 0$ the step
with shift polynomial $(z - s)^k$ is reduced, so $s$ is accepted. -/
theorem IsUpperHessenberg.isShiftAccept_of_det_eq_zero {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (hn : 0 < n) {k : ℕ} (hk : 0 < k) {τ : ℝ} (hτ : 0 ≤ τ) (γ : ℝ)
    {s : ℂ} (hs : (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0) :
    IsShiftAccept τ γ k H s := by
  have hdet : (Polynomial.aeval H (shiftPoly (List.replicate k s))).det = 0 := by
    rw [aeval_shiftPoly_replicate, Matrix.det_pow, hs, zero_pow hk.ne']
  obtain ⟨i, hi⟩ := hH.isDecoupled_zero_multiShiftedQRStep_of_det_eq_zero hn hdet
  exact Or.inl ⟨i, hi.trans (by rw [zero_mul]; exact hτ)⟩

/-- The multi-shift QR step is a unitary similarity: $\mathsf{multiShiftedQRStep}(\mathbf{H},
\mathrm{ss}) = \mathbf{U}^{\mathsf{H}}\mathbf{H}\mathbf{U}$ for a unitary $\mathbf{U}$ (the
product of the unitary factors of the single steps). -/
theorem exists_unitary_multiShiftedQRStep (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) :
    ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols U ∧
      multiShiftedQRStep H ss = Uᴴ * H * U := by
  induction ss generalizing H with
  | nil => exact ⟨1, hasOrthonormalCols_one, by simp [multiShiftedQRStep]⟩
  | cons s ss ih =>
    obtain ⟨U, hU, hstep⟩ := ih (shiftedQRStep H s)
    have hQ := hasOrthonormalCols_givensHessenbergQ
      (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
    set Q := givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) with hQdef
    refine ⟨Q * U, ?_, ?_⟩
    · exact hQ.mul hU
    · change multiShiftedQRStep (shiftedQRStep H s) ss = _
      rw [hstep, shiftedQRStep, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc, hQdef]

/-- An iteration of the search keeps the Hessenberg form. -/
theorem IsUpperHessenberg.isUpperHessenberg_shqrAcceptStep
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (τ B θ α γ : ℝ)
    (m : ℕ) (ss : List ℂ) : IsUpperHessenberg (shqrAcceptStep τ B θ α γ m H ss) :=
  hH.isUpperHessenberg_multiShiftedQRStep _

/-- The shift of $\mathrm{Sh}_{k,B}$ is one of the Ritz values or one of the candidates:
`NLAlib.shqrShift` lies in `ss ++ NLAlib.shqrCandidates`. -/
theorem shqrShift_mem (B θ α γ : ℝ) (m : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) :
    shqrShift B θ α γ m H ss ∈ ss ++ shqrCandidates B θ α γ m H ss := by
  unfold shqrShift
  split_ifs with h h'
  · exact List.mem_append_left _ h.choose_spec.1
  · exact List.mem_append_right _ h'.choose_spec.1
  · exact List.mem_append_right _ (List.mem_cons_self ..)

/-- A successful shift is accepted: for $\tau \ge 0$, $\gamma \le 1$ and $k \ge 1$, a shift
with `NLAlib.IsShiftSuccess` (the step is reduced or reduces $\psi_k$ by $1 - \gamma$) satisfies
`NLAlib.IsShiftAccept`. -/
theorem IsShiftSuccess.isShiftAccept {τ γ : ℝ} {k : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {s : ℂ} (h : IsShiftSuccess γ k H s) (hτ : 0 ≤ τ) (_hγ : γ ≤ 1) (hk : 0 < k) :
    IsShiftAccept τ γ k H s := by
  rcases h with h | h
  · obtain ⟨i, hi⟩ := h
    exact Or.inl ⟨i, hi.trans (by rw [zero_mul]; exact hτ)⟩
  refine Or.inr ?_
  have key : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      subdiagNormSqProd k X = hessenbergPotential k X ^ (2 * k) := by
    intro X
    rw [mul_comm, pow_mul, hessenbergPotential_pow hk, subdiagNormSqProd, Finset.prod_pow]
  rw [key, key, ← mul_pow]
  exact pow_le_pow_left₀ (hessenbergPotential_nonneg _ _) h _

/-- **Some candidate is accepted**: let $\mathbf{H}$ upper Hessenberg with
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible and
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$; $k = 2^m$ with $m \ge 1$ and $k \le n$; `ss` a
list of $k$ $\theta$-optimal Ritz values, $\theta \ge 1$; $\alpha \ge 1$ with
$B^{4m} \le \alpha^k$; $0 < \gamma < 1$ and $\tau \ge 0$. Then some Ritz value in
`ss` or some candidate of `NLAlib.shqrCandidates` is accepted.
[BanksGarzaVargasSrivastava2021, Theorem 1.6, proof]. -/
theorem IsUpperHessenberg.exists_mem_isShiftAccept
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {d : Fin (n + 1) → ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {B θ α γ : ℝ}
    (hB : pseudoConditionNumber V ≤ B) {m : ℕ} (hm : 1 ≤ m) (hmn : 2 ^ m ≤ n) {ss : List ℂ}
    (hlen : ss.length = 2 ^ m) (hss : IsOptimalRitzValues θ H ss) (hθ : 1 ≤ θ) (hα1 : 1 ≤ α)
    (hα : B ^ (4 * m) ≤ α ^ 2 ^ m) (hγ0 : 0 < γ) (hγ1 : γ < 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ s ∈ ss ++ shqrCandidates B θ α γ m H ss, IsShiftAccept τ γ (2 ^ m) H s := by
  have hsucc : IsShiftSuccess γ (2 ^ m) H (shqrShift B θ α γ m H ss) :=
    hH.isDecoupled_zero_shqrStep_or_hessenbergPotential_le hV hHV hB hm hmn hlen hss hθ hα1 hα
      hγ0 hγ1
  exact ⟨_, shqrShift_mem B θ α γ m H ss, hsucc.isShiftAccept hτ hγ1.le (by positivity)⟩

/-- The search returns an accepted shift: let $\mathbf{H}$ upper Hessenberg with
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible and
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$; $k = 2^m$ with $m \ge 1$ and $k \le n$; `ss` a
list of $k$ $\theta$-optimal Ritz values, $\theta \ge 1$; $\alpha \ge 1$ with
$B^{4m} \le \alpha^k$; $0 < \gamma < 1$ and $\tau \ge 0$. Then the first accepted
shift `NLAlib.shqrAcceptShift` is accepted. -/
theorem IsUpperHessenberg.isShiftAccept_shqrAcceptShift
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {d : Fin (n + 1) → ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {B θ α γ : ℝ}
    (hB : pseudoConditionNumber V ≤ B) {m : ℕ} (hm : 1 ≤ m) (hmn : 2 ^ m ≤ n) {ss : List ℂ}
    (hlen : ss.length = 2 ^ m) (hss : IsOptimalRitzValues θ H ss) (hθ : 1 ≤ θ) (hα1 : 1 ≤ α)
    (hα : B ^ (4 * m) ≤ α ^ 2 ^ m) (hγ0 : 0 < γ) (hγ1 : γ < 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsShiftAccept τ γ (2 ^ m) H (shqrAcceptShift τ B θ α γ m H ss) := by
  classical
  obtain ⟨s, hs, hacc⟩ := hH.exists_mem_isShiftAccept hV hHV hB hm hmn hlen hss hθ hα1 hα hγ0
    hγ1 hτ
  have hsome : ((ss ++ shqrCandidates B θ α γ m H ss).find?
      fun s => decide (IsShiftAccept τ γ (2 ^ m) H s)).isSome :=
    List.find?_isSome.mpr ⟨s, hs, decide_eq_true hacc⟩
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
  unfold shqrAcceptShift
  rw [ht, Option.getD_some]
  simpa using List.find?_some ht

/-- Acceptance without decoupling reduces the potential: if $s$ is accepted and the step
$\widehat{\mathbf{H}}$ is not decoupled at $\tau$, then
$\psi_k(\widehat{\mathbf{H}}) \le (1 - \gamma)\psi_k(\mathbf{H})$, for $k \ge 1$ and
$\gamma \le 1$. -/
theorem hessenbergPotential_le_of_isShiftAccept {τ γ : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s : ℂ} (h : IsShiftAccept τ γ k H s)
    (hdec : ¬IsDecoupledAbs τ (multiShiftedQRStep H (List.replicate k s))) (hγ : γ ≤ 1)
    (hk : 0 < k) :
    hessenbergPotential k (multiShiftedQRStep H (List.replicate k s)) ≤
      (1 - γ) * hessenbergPotential k H := by
  rcases h with h | h
  · exact absurd h hdec
  have key : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      subdiagNormSqProd k X = hessenbergPotential k X ^ (2 * k) := by
    intro X
    rw [mul_comm, pow_mul, hessenbergPotential_pow hk, subdiagNormSqProd, Finset.prod_pow]
  have h1 : 0 ≤ (1 - γ) * hessenbergPotential k H :=
    mul_nonneg (by linarith) (hessenbergPotential_nonneg _ _)
  rw [key, key, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (hessenbergPotential_nonneg _ _) h1 (by omega)).mp h

/-- **One iteration of the search**: let $\mathbf{H}$ upper Hessenberg with
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible and
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$; $k = 2^m$ with $m \ge 1$ and $k \le n$; `ss` a
list of $k$ $\theta$-optimal Ritz values, $\theta \ge 1$; $\alpha \ge 1$ with
$B^{4m} \le \alpha^k$; $0 < \gamma < 1$ and $\tau \ge 0$. Then the step
$\widehat{\mathbf{H}}$ = `NLAlib.shqrAcceptStep` is decoupled at $\tau$ or has
$\psi_k(\widehat{\mathbf{H}}) \le (1 - \gamma)\psi_k(\mathbf{H})$.
[BanksGarzaVargasSrivastava2021, Theorem 1.6, proof of rapid convergence]. -/
theorem IsUpperHessenberg.isDecoupledAbs_or_hessenbergPotential_shqrAcceptStep_le
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {d : Fin (n + 1) → ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {B θ α γ : ℝ}
    (hB : pseudoConditionNumber V ≤ B) {m : ℕ} (hm : 1 ≤ m) (hmn : 2 ^ m ≤ n) {ss : List ℂ}
    (hlen : ss.length = 2 ^ m) (hss : IsOptimalRitzValues θ H ss) (hθ : 1 ≤ θ) (hα1 : 1 ≤ α)
    (hα : B ^ (4 * m) ≤ α ^ 2 ^ m) (hγ0 : 0 < γ) (hγ1 : γ < 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsDecoupledAbs τ (shqrAcceptStep τ B θ α γ m H ss) ∨
      hessenbergPotential (2 ^ m) (shqrAcceptStep τ B θ α γ m H ss) ≤
        (1 - γ) * hessenbergPotential (2 ^ m) H := by
  have hacc := hH.isShiftAccept_shqrAcceptShift hV hHV hB hm hmn hlen hss hθ hα1 hα hγ0 hγ1 hτ
  by_cases hdec : IsDecoupledAbs τ (shqrAcceptStep τ B θ α γ m H ss)
  · exact Or.inl hdec
  exact Or.inr (hessenbergPotential_le_of_isShiftAccept hacc hdec hγ1.le (by positivity))

/-- **A potential reduced long enough decouples**: if
$\psi_k(\mathbf{H}) \le (1 - \gamma)^{t}\psi_k(\mathbf{H}_0)$ with
$t \ge \lceil\log(1/\delta)/\log(1/(1 - \gamma))\rceil$, $\|\mathbf{H}\|_2 = \|\mathbf{H}_0\|_2$
and $\delta\|\mathbf{H}_0\|_2 \le \tau$, then $\mathbf{H}$ is decoupled at the threshold $\tau$
($0 < \delta$, $0 < \gamma < 1$, $1 \le k \le n$). The counting step of
[BanksGarzaVargasSrivastava2021, Theorem 1.6, item 1], as in
`NLAlib.IsUpperHessenberg.exists_le_isDecoupled_shqrIterate`. -/
theorem isDecoupledAbs_of_hessenbergPotential_le_pow
    {H H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k T : ℕ} (hk : 0 < k) (hkn : k ≤ n) {γ δ τ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hδ : 0 < δ)
    (hT : ⌈Real.log (1 / δ) / Real.log (1 / (1 - γ))⌉₊ ≤ T)
    (hψ : hessenbergPotential k H ≤ (1 - γ) ^ T * hessenbergPotential k H₀)
    (hτ : δ * specNorm H₀ ≤ τ) :
    IsDecoupledAbs τ H := by
  have hL : 0 < Real.log (1 / (1 - γ)) :=
    Real.log_pos (by rw [one_div, one_lt_inv₀ (by linarith)]; linarith)
  have hx : Real.log (1 / δ) / Real.log (1 / (1 - γ)) ≤ (T : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hT)
  have hlog : Real.log (1 / δ) ≤ (T : ℝ) * Real.log (1 / (1 - γ)) :=
    (div_le_iff₀ hL).mp hx
  have hT1 : (1 - γ) ^ T ≤ δ := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv] at hlog
    rw [← Real.log_le_log_iff (pow_pos (by linarith) _) hδ, Real.log_pow]
    linarith
  have hψ0 : 0 ≤ hessenbergPotential k H₀ := hessenbergPotential_nonneg _ _
  have hψ0' : 0 ≤ hessenbergPotential k H := hessenbergPotential_nonneg _ _
  have hle : hessenbergPotential k H ≤ τ :=
    calc hessenbergPotential k H ≤ (1 - γ) ^ T * hessenbergPotential k H₀ := hψ
      _ ≤ δ * specNorm H₀ :=
        mul_le_mul hT1 (hessenbergPotential_le_specNorm hk hkn H₀) hψ0 hδ.le
      _ ≤ τ := hτ
  have hcard : (Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)).card = k := by
    rw [← Finset.card_map Fin.valEmbedding,
      show (Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)).map Fin.valEmbedding =
        Finset.Ico (n - k) n by
          ext m
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.valEmbedding_apply, Finset.mem_Ico]
          exact ⟨by rintro ⟨i, hi, rfl⟩; exact ⟨by omega, i.isLt⟩,
            fun ⟨h1, h2⟩ => ⟨⟨m, h2⟩, by change n ≤ m + k; omega, rfl⟩⟩,
      Nat.card_Ico]
    omega
  have hne : (Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; exact hk)
  -- some last subdiagonal entry is at most the geometric mean `ψ`
  obtain ⟨i, hi, hia⟩ : ∃ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k),
      ‖H i.succ i.castSucc‖ ≤ hessenbergPotential k H := by
    by_contra hcon
    push Not at hcon
    have hpow := hessenbergPotential_pow hk H
    rcases hψ0'.eq_or_lt with h0 | hpos
    · rw [← h0, zero_pow hk.ne'] at hpow
      have := Finset.prod_pos fun i hi => lt_of_le_of_lt hψ0' (hcon i hi)
      linarith
    · have := Finset.prod_lt_prod_of_nonempty (fun _ _ => hpos) (fun i hi => hcon i hi) hne
      rw [Finset.prod_const, hcard, ← hpow] at this
      exact lt_irrefl _ this
  exact ⟨i, hia.trans hle⟩

/-- **The fuel of the decoupling loop** (the link from rapid decoupling to the loop's fuel
obligation): an iterate $\mathbf{H}_j$ that still fails the decoupling test while
$\psi_k(\mathbf{H}_j) \le (1 - \gamma)^j\psi_k(\mathbf{H}_0)$ has
$j < \lceil\log(1/\delta)/\log(1/(1 - \gamma))\rceil$, so a loop with fuel $F + 1 \ge T + 1$
never runs out. The contrapositive of `NLAlib.isDecoupledAbs_of_hessenbergPotential_le_pow`. -/
theorem lt_of_not_isDecoupledAbs_of_hessenbergPotential_le_pow
    {H H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k j : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {γ δ τ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hδ : 0 < δ)
    (hψ : hessenbergPotential k H ≤ (1 - γ) ^ j * hessenbergPotential k H₀)
    (hτ : δ * specNorm H₀ ≤ τ) (hdec : ¬IsDecoupledAbs τ H) :
    j < ⌈Real.log (1 / δ) / Real.log (1 / (1 - γ))⌉₊ := by
  by_contra h
  exact hdec (isDecoupledAbs_of_hessenbergPotential_le_pow hk hkn hγ0 hγ1 hδ (not_lt.mp h) hψ hτ)

/-- The exceptional spacing is positive for parameters at least $1$ and $\gamma < 1$, so the grid
resolution $M = \lceil\sqrt2/\varepsilon\rceil$ is at least $1$ (the grid divides by $M$). -/
theorem one_le_ceil_sqrt_two_div_exceptionalSpacing {B θ α γ : ℝ} (hB : 1 ≤ B) (hθ : 1 ≤ θ)
    (hα : 1 ≤ α) (hγ : γ < 1) (m : ℕ) :
    1 ≤ ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊ := by
  have hB0 : 0 < B := by linarith
  have hθ0 : 0 < θ := by linarith
  have hα0 : 0 < α := by linarith
  have hρ : 0 < (1 - γ) ^ 2 := by
    have : 0 < 1 - γ := by linarith
    positivity
  have hbase : 0 < (1 - γ) ^ 2 / ((14 * B ^ 4) ^ (((2 ^ m : ℕ) : ℝ)⁻¹) * α ^ 2 * θ ^ 2) := by
    positivity
  have hε : 0 < exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2) :=
    Real.rpow_pos_of_pos hbase _
  exact Nat.one_le_ceil_iff.mpr (div_pos (Real.sqrt_pos.mpr two_pos) hε)

/-- `m` square roots of a nonnegative number are its power $x^{1/2^m}$. -/
private lemma sqrt_iterate_eq_rpow {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    Real.sqrt^[m] x = x ^ (((2 ^ m : ℕ) : ℝ)⁻¹) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    congr 1
    push_cast
    ring

/-- The potential for $k = 2^m$ by square roots:
$\psi_{2^m}(\mathbf{H}) = \sqrt{\cdot}^{[m]}\bigl(\sqrt{\textstyle\prod_{n - k \le i < n}
\lvert\mathbf{H}_{i+1,i}\rvert^2}\bigr)$, $m$ square roots of the square root of the product of
the squared moduli. -/
theorem hessenbergPotential_two_pow_eq (m : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    hessenbergPotential (2 ^ m) H = Real.sqrt^[m] (Real.sqrt (subdiagNormSqProd (2 ^ m) H)) := by
  have hQ : 0 ≤ ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + 2 ^ m),
      ‖H i.succ i.castSucc‖ :=
    Finset.prod_nonneg fun i _ => norm_nonneg _
  rw [subdiagNormSqProd, Finset.prod_pow, Real.sqrt_sq hQ, sqrt_iterate_eq_rpow hQ,
    hessenbergPotential]

/-- `m` square roots of a nonnegative number are its power $x^{1/2^m}$ (a copy of the helper
for the potential, so that this declaration uses only its own helpers). -/
private lemma sqrt_iterate_rpow_of_nonneg {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    Real.sqrt^[m] x = x ^ (((2 ^ m : ℕ) : ℝ)⁻¹) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    congr 1
    push_cast
    ring

/-- Square roots are multiplicative on nonnegative numbers: $\sqrt{\cdot}^{[m]}(ab) =
\sqrt{\cdot}^{[m]}(a)\sqrt{\cdot}^{[m]}(b)$. -/
private lemma sqrt_iterate_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) :
    Real.sqrt^[m] (a * b) = Real.sqrt^[m] a * Real.sqrt^[m] b := by
  rw [sqrt_iterate_rpow_of_nonneg (mul_nonneg ha hb), sqrt_iterate_rpow_of_nonneg ha,
    sqrt_iterate_rpow_of_nonneg hb, Real.mul_rpow ha hb]

/-- The radius of the exceptional disk for $k = 2^m$ by square roots: for $B \ge 0$,
$(2B)^{1/k}\theta\alpha\psi_k(\mathbf{H}) = \sqrt{\cdot}^{[m]}\bigl(2B\sqrt{\textstyle\prod
\lvert\mathbf{H}_{i+1,i}\rvert^2}\bigr)\,\theta\alpha$ (`NLAlib.exceptionalRadius`). -/
theorem exceptionalRadius_two_pow_eq {B : ℝ} (hB : 0 ≤ B) (θ α : ℝ) (m : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    exceptionalRadius (2 ^ m) B θ α (hessenbergPotential (2 ^ m) H) =
      Real.sqrt^[m] (2 * B * Real.sqrt (subdiagNormSqProd (2 ^ m) H)) * θ * α := by
  have h2B : 0 ≤ 2 * B := by linarith
  have hs : 0 ≤ Real.sqrt (subdiagNormSqProd (2 ^ m) H) := Real.sqrt_nonneg _
  rw [exceptionalRadius, hessenbergPotential_two_pow_eq, sqrt_iterate_mul h2B hs,
    sqrt_iterate_rpow_of_nonneg h2B]
  ring

/-- The **decoupling test on squared parts**: for $\tau \ge 0$, $\mathbf{H}$ is decoupled at the
threshold $\tau$ if and only if some subdiagonal entry $z$ has
$(\operatorname{Re} z)^2 + (\operatorname{Im} z)^2 \le \tau^2$, a test with the arithmetic
operations only. -/
theorem isDecoupledAbs_iff_normSq {τ : ℝ} (hτ : 0 ≤ τ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    IsDecoupledAbs τ H ↔
      ∃ i : Fin n, (H i.succ i.castSucc).re ^ 2 + (H i.succ i.castSucc).im ^ 2 ≤ τ ^ 2 := by
  unfold IsDecoupledAbs
  refine exists_congr fun i => ?_
  have key : Complex.normSq (H i.succ i.castSucc) =
      (H i.succ i.castSucc).re ^ 2 + (H i.succ i.castSucc).im ^ 2 := by
    rw [Complex.normSq_apply]
    ring
  rw [← sq_le_sq₀ (norm_nonneg _) hτ, Complex.sq_norm, key]

open Classical in
/-- **The first accepted shift in three phases**, as the program searches: the first accepted
Ritz value; else the promising Ritz value $r$ = `NLAlib.findRitz` if accepted; else the first
accepted point of the square grid about $r$; else $r$. `List.find?_append` on
`ss ++ r :: squareGrid …`. -/
theorem shqrAcceptShift_eq_three_phase (τ B θ α γ : ℝ) (m : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) :
    shqrAcceptShift τ B θ α γ m H ss =
      ((ss.find? fun s => decide (IsShiftAccept τ γ (2 ^ m) H s)).getD
        (if IsShiftAccept τ γ (2 ^ m) H (findRitz H m 1 ss) then findRitz H m 1 ss else
          ((squareGrid (findRitz H m 1 ss)
              (exceptionalRadius (2 ^ m) B θ α (hessenbergPotential (2 ^ m) H))
              (exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2))).find?
            fun s => decide (IsShiftAccept τ γ (2 ^ m) H s)).getD (findRitz H m 1 ss))) := by
  rw [shqrAcceptShift, shqrCandidates, List.find?_append, List.find?_cons]
  cases ss.find? (fun s => decide (IsShiftAccept τ γ (2 ^ m) H s)) with
  | some s => simp
  | none =>
    by_cases hr : IsShiftAccept τ γ (2 ^ m) H (findRitz H m 1 ss) <;> simp [hr]

/-- The product of the last $k$ squared subdiagonal moduli as a product over the range of the
corresponding natural range. -/
theorem subdiagNormSqProd_eq_prod_range {n : ℕ} (k : ℕ) (hkn : k ≤ n)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    subdiagNormSqProd k H = ∏ t ∈ Finset.range k, if h : n - k + t < n then
      ‖H (⟨n - k + t, h⟩ : Fin n).succ (⟨n - k + t, h⟩ : Fin n).castSucc‖ ^ 2 else 1 := by
  unfold subdiagNormSqProd
  refine Finset.prod_bij (fun a _ => (a : ℕ) - (n - k)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_range]
    omega
  · intro a ha a' ha' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
    exact Fin.ext (by omega)
  · intro t ht
    simp only [Finset.mem_range] at ht
    exact ⟨⟨n - k + t, by omega⟩,
      by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, by simp⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have e : (⟨n - k + ((a : ℕ) - (n - k)), by omega⟩ : Fin n) = a := Fin.ext (by simp; omega)
    rw [dif_pos (by omega), e]

/-- A rejected positive-degree shift of a nontrivial Hessenberg matrix is nonsingular.
This supplies the inverse-domain premise to subsequent Ritz-value search computations. -/
theorem IsUpperHessenberg.det_sub_smul_one_ne_zero_of_not_isShiftAccept
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H)
    (hn : 0 < n) {k : ℕ} (hk : 0 < k) {τ γ : ℝ} (hτ : 0 ≤ τ) {s : ℂ}
    (ha : ¬IsShiftAccept τ γ k H s) :
    (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det ≠ 0 :=
  fun hdet => ha (hH.isShiftAccept_of_det_eq_zero hn hk hτ γ hdet)

open Classical in
/-- A wholly rejected list of positive-degree shifts has no eigenvalue shifts. This derives
every inverse-domain premise of the later promising-Ritz search from mathematical rejection. -/
theorem IsUpperHessenberg.det_sub_smul_one_ne_zero_of_find_none
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H)
    (hn : 0 < n) {k : ℕ} (hk : 0 < k) {τ γ : ℝ} (hτ : 0 ≤ τ) {ss : List ℂ}
    (hNone : ss.find? (fun s => decide (IsShiftAccept τ γ k H s)) = none) :
    ∀ s ∈ ss, (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det ≠ 0 := by
  intro s hs hdet
  have ha := hH.isShiftAccept_of_det_eq_zero hn hk hτ γ hdet
  have hNo := List.find?_eq_none.mp hNone s hs
  exact hNo (by simpa only [decide_eq_true_eq] using ha)

end NLAlib
