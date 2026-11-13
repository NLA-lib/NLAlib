/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.EntrywiseRounding
public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Norms.Compare
public import NLAlib.Matrix.Spectral.LeastSingularValue

/-!
# Deflation: an orthonormal basis of the range of a near-low-rank matrix

`NLAlib.deflate M r P G` returns the first $r$ columns of the $\mathbf{Q}$ factor of the
machine's QR factorization of $\mathrm{mm}(\mathbf{P}, \widetilde{\mathbf{G}})$, where
$\widetilde{\mathbf{G}}$ is the stored version (the machine's normal sampler, entrywise) of an
ideal sample $\mathbf{G}$ ([Shah2024, Algorithm 2]). For $\mathbf{P}$ close to a matrix of rank
$r$ and $\mathbf{G}$ a standard complex Gaussian matrix the output is, with high probability,
close to an orthonormal basis of the range ([Shah2024, Theorem 3.3]). It is the randomized range
finder without oversampling, as in [BanksGarzaVargasKulkarniSrivastava2020], here with a
Gaussian rather than a Haar test matrix. The definition is computable and written over a
`NLAlib.FloatMachine`.

## Main definitions

* `NLAlib.deflate`.

## Main results

* `NLAlib.HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le`,
  `NLAlib.HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le_sqrt_two_mul`: a basis
  that spans nearly the range of a frame is near a rotation of the frame (the three inequalities of
  [Shah2024], and the orthogonal Procrustes rotation with constant $\sqrt2$).
* `NLAlib.FloatMachine.IsArithAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le`,
  `FloatMachine.IsArithAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le`:
  the deterministic bound, with the roundings charged at the accuracy or at $1/16$ of it.

The Gaussian tail is in `NLAlib/Eigensolvers/RandomizedDeflation.lean`.
-/

@[expose] public section

namespace NLAlib

/-- **Randomized deflation** $\mathsf{deflate}(\mathbf{P}, r)$ with ideal sample $\mathbf{G}$, on
the machine `M`: the first $r$ columns of $\mathbf{Q}$, where $(\mathbf{Q}, \mathbf{R}) =
\mathrm{qr}(\mathrm{mm}(\mathbf{P}, \widetilde{\mathbf{G}}))$ and $\widetilde{\mathbf{G}}$ is
$\mathbf{G}$ with every entry replaced by its stored version $\mathrm{normal}(\mathbf{G}_{i,j})$.
Junk value: the columns beyond the $n$-th are stored zeros when $r > n$. In pseudo-code:

```text
deflate(P, r; G):                  P n×n, G an ideal n×n Gaussian sample
  G̃ ← normal(G)                                  each entry stored by the normal sampler
  (Q, R) ← qr(P·G̃)                               the machine's product and QR
  return the first r columns of Q                (zero columns beyond the n-th)
```

[Shah2024, Algorithm 2].
Algorithm: deflate -/
def deflate {F Su Sg : Type*} (M : FloatMachine F Su Sg) {n : ℕ} (r : ℕ)
    (P : Matrix (Fin n) (Fin n) (F × F)) (G : Matrix (Fin n) (Fin n) Sg) :
    Matrix (Fin n) (Fin r) (F × F) :=
  Matrix.of fun i j =>
    if h : (j : ℕ) < n then (M.qr (M.mm P (G.map M.normal))).1 i ⟨j, h⟩ else (M.zero, M.zero)

/-- For an admitted rank, deflation is exactly the requested leading columns of the actual
QR result. There is no fallback column in this range. -/
theorem deflate_eq_submatrix {F Su Sg : Type*} (M : FloatMachine F Su Sg) {n r : ℕ}
    (hr : r ≤ n) (P : Matrix (Fin n) (Fin n) (F × F)) (G : Matrix (Fin n) (Fin n) Sg) :
    deflate M r P G =
      (M.qr (M.mm P (G.map M.normal))).1.submatrix id (Fin.castLE hr) := by
  funext i j
  simp only [deflate, Matrix.of_apply, Matrix.submatrix_apply, dif_pos (j.isLt.trans_le hr)]
  rfl

section DeterministicAccuracy

open scoped Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m r : Type*} [Fintype m] [Fintype r] [DecidableEq r]

/-- The reverse triangle inequality for two matrices at one vector. -/
private theorem abs_norm_mulVec_sub_norm_mulVec_le {p q : Type*} [Fintype p] [Fintype q]
    (X Y : Matrix p q 𝕜) (x : q → 𝕜) :
    |‖WithLp.toLp 2 (X *ᵥ x)‖ - ‖WithLp.toLp 2 (Y *ᵥ x)‖| ≤
      specNorm (X - Y) * ‖WithLp.toLp 2 x‖ :=
  (abs_norm_sub_norm_le _ _).trans <| by
    rw [← WithLp.toLp_sub, ← Matrix.sub_mulVec]; exact norm_toLp_mulVec_le _ _

open scoped MatrixOrder in
/-- A square matrix that is an $a$-near isometry, $a < 1$, is within $a$ of its polar factor. -/
private theorem exists_hasOrthonormalCols_specNorm_sub_le_of_abs_norm_mulVec_sub_le
    {B : Matrix r r 𝕜} {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1)
    (hB : ∀ x, |‖WithLp.toLp 2 (B *ᵥ x)‖ - ‖WithLp.toLp 2 x‖| ≤ a * ‖WithLp.toLp 2 x‖) :
    ∃ W : Matrix r r 𝕜, HasOrthonormalCols W ∧ specNorm (W - B) ≤ a := by
  have hlo : ∀ x, (1 - a) * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (B *ᵥ x)‖ := fun x => by
    have := (abs_le.mp (hB x)).1; linarith
  have hinj : Function.Injective B.mulVec := by
    intro x y hxy
    have h := hlo (x - y)
    rw [Matrix.mulVec_sub, hxy, sub_self, WithLp.toLp_zero, norm_zero] at h
    have h0 : ‖WithLp.toLp 2 (x - y)‖ = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right h (by linarith)) (norm_nonneg _)
    rw [norm_eq_zero, WithLp.toLp_eq_zero] at h0
    exact sub_eq_zero.mp h0
  have hB1 : specNorm B ≤ 1 + a := by
    rw [specNorm_le_iff (by linarith)]
    intro x; have := (abs_le.mp (hB x)).2; linarith
  set H := CFC.sqrt (Bᴴ * B)
  have hS : H.IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hW := hasOrthonormalCols_polarFactor_iff.mpr hinj
  refine ⟨polarFactor B, hW, ?_⟩
  have heq : polarFactor B - B = polarFactor B * -(H - 1) := by
    rw [neg_sub, Matrix.mul_sub, Matrix.mul_one,
      show polarFactor B * H = B from polarFactor_mul_sqrt B]
  have hH : specNorm (H - 1) ≤ a := by
    rcases isEmpty_or_nonempty r with hr | hr
    · rw [Subsingleton.elim (H - 1) 0, specNorm_zero]
      exact ha0
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := r))
    have hsub : H - 1 = H + (-1 : ℝ) • (1 : Matrix r r 𝕜) := by
      rw [neg_one_smul, sub_eq_add_neg]
    have hσ : ∀ i ≤ k, |eigenvalue (H - 1) i| ≤ a := fun i hi => by
      rw [hsub, hS.eigenvalue_add_smul_one (-1) (by omega),
        eigenvalue_sqrt_conjTranspose_mul_self B (by omega)]
      have h1 := (singularValues_le_specNorm B i).trans hB1
      have h2 := (le_singularValues_last B hk.symm hlo).trans (singularValues_antitone B hi)
      rw [abs_le]; constructor <;> linarith
    rw [(hS.sub Matrix.isHermitian_one).specNorm_eq_max hk.symm]
    exact max_le (hσ 0 (Nat.zero_le _)) (hσ k le_rfl)
  rw [heq]
  calc _ ≤ specNorm (polarFactor B) * specNorm (-(H - 1)) := specNorm_mul_le _ _
    _ ≤ 1 * a := by
      rw [specNorm_neg]
      exact mul_le_mul hW.specNorm_le_one hH (specNorm_nonneg _) zero_le_one
    _ = a := one_mul a

/-- **A near-basis close to a frame up to a change of basis is close to a rotation of it**: let
$\mathbf{U}, \mathbf{Q}' \in \Bbbk^{m \times r}$ have orthonormal columns, and
$\mathbf{Q}_1 \in \Bbbk^{m \times r}$, $\mathbf{C} \in \Bbbk^{r \times r}$ satisfy
$\|\mathbf{Q}_1 - \mathbf{Q}'\|_2 \le \nu$ and $\|\mathbf{U} - \mathbf{Q}_1\mathbf{C}\|_2 \le
\delta$ with $\nu \le \delta \le 1/5$. Then there is a unitary $\mathbf{W}$ with
$$\|\mathbf{U}\mathbf{W} - \mathbf{Q}_1\|_2 \le 6\delta \,.$$
[Shah2024, proof of Theorem 3.3]: the three inequalities there, which avoid the square-root loss
of the earlier deflation analysis cited in the module docstring. -/
theorem HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le {U Q' Q₁ : Matrix m r 𝕜}
    (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q') {C : Matrix r r 𝕜} {ν δ : ℝ}
    (hν : specNorm (Q₁ - Q') ≤ ν) (hδ : specNorm (U - Q₁ * C) ≤ δ) (hνδ : ν ≤ δ)
    (hδ₅ : δ ≤ 1 / 5) :
    ∃ W : Matrix r r 𝕜, HasOrthonormalCols W ∧ specNorm (U * W - Q₁) ≤ 6 * δ := by
  classical
  have hδ0 : 0 ≤ δ := (specNorm_nonneg _).trans hδ
  have hQ₁ : ∀ x, |‖WithLp.toLp 2 (Q₁ *ᵥ x)‖ - ‖WithLp.toLp 2 x‖| ≤
      ν * ‖WithLp.toLp 2 x‖ := fun x => by
    have h := abs_norm_mulVec_sub_norm_mulVec_le Q₁ Q' x
    rw [hQ'.norm_toLp_mulVec] at h
    exact h.trans (by gcongr)
  have hC : ∀ x, ‖WithLp.toLp 2 x‖ ≤ 3 / 2 * ‖WithLp.toLp 2 (C *ᵥ x)‖ := fun x => by
    have h := abs_norm_mulVec_sub_norm_mulVec_le U (Q₁ * C) x
    rw [hU.norm_toLp_mulVec, ← Matrix.mulVec_mulVec] at h
    have h1 := (abs_le.mp h).2
    have h2 := (abs_le.mp (hQ₁ (C *ᵥ x))).2
    have hx := norm_nonneg (WithLp.toLp 2 x)
    have hCx := norm_nonneg (WithLp.toLp 2 (C *ᵥ x))
    nlinarith [mul_le_mul_of_nonneg_right hδ hx, mul_le_mul_of_nonneg_right hνδ hCx,
      mul_nonneg (sub_nonneg.mpr hδ₅) hx, mul_nonneg (sub_nonneg.mpr hδ₅) hCx]
  have hCsurj : Function.Surjective C.mulVec := by
    refine Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp ?_)
    intro x y hxy
    have h := hC (x - y)
    rw [Matrix.mulVec_sub, hxy, sub_self] at h
    simp only [WithLp.toLp_zero, norm_zero, mul_zero] at h
    have h0 : ‖WithLp.toLp 2 (x - y)‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [norm_eq_zero, WithLp.toLp_eq_zero] at h0
    exact sub_eq_zero.mp h0
  set D := Q₁ - U * (Uᴴ * Q₁)
  have hDC : D * C = (1 - U * Uᴴ) * (Q₁ * C - U) := by
    simp only [D, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc,
      hU.conjTranspose_mul_self, Matrix.mul_one]
    abel
  have hD : specNorm D ≤ 3 / 2 * δ := by
    rw [specNorm_le_iff (by positivity)]
    intro y
    obtain ⟨x, rfl⟩ := hCsurj y
    rw [Matrix.mulVec_mulVec, hDC, ← Matrix.mulVec_mulVec]
    refine (hU.isStarProjection_mul_conjTranspose.one_sub.norm_toLp_mulVec_le _).trans ?_
    refine (norm_toLp_mulVec_le _ _).trans ?_
    rw [specNorm_sub_comm]
    have := hC x
    calc _ ≤ δ * ‖WithLp.toLp 2 x‖ := by gcongr
      _ ≤ _ := by nlinarith
  obtain ⟨W, hW, hWB⟩ := exists_hasOrthonormalCols_specNorm_sub_le_of_abs_norm_mulVec_sub_le
    (B := Uᴴ * Q₁) (a := 5 / 2 * δ) (by positivity) (by linarith) fun x => by
      have h := abs_norm_mulVec_sub_norm_mulVec_le Q₁ (U * (Uᴴ * Q₁)) x
      rw [← Matrix.mulVec_mulVec, hU.norm_toLp_mulVec] at h
      have h1 := h.trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
      have h2 := hQ₁ x
      have hx := norm_nonneg (WithLp.toLp 2 x)
      rw [abs_le] at h1 h2 ⊢
      constructor <;> nlinarith
  refine ⟨W, hW, ?_⟩
  have heq : U * W - Q₁ = U * (W - Uᴴ * Q₁) - D := by
    simp only [D, Matrix.mul_sub]; abel
  rw [heq]
  calc _ ≤ specNorm (U * (W - Uᴴ * Q₁)) + specNorm D := specNorm_sub_le _ _
    _ ≤ 5 / 2 * δ + 3 / 2 * δ := by rw [hU.specNorm_mul_left]; exact add_le_add hWB hD
    _ ≤ 6 * δ := by linarith

/-- The key identity: for $\mathbf{Q} = \mathbf{U}\mathbf{W} - \mathbf{Q}'$ with orthonormal
columns, $\mathbf{Q}^{\mathsf H}\mathbf{Q} = \mathbf{W}^{\mathsf H}(\mathbf{W} - \mathbf{T}) +
(\mathbf{W} - \mathbf{T})^{\mathsf H}\mathbf{W}$ where $\mathbf{T} = \mathbf{U}^{\mathsf H}
\mathbf{Q}'$. -/
private theorem conjTranspose_mul_self_sub_eq {U Q' : Matrix m r 𝕜} {W : Matrix r r 𝕜}
    (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q') (hW : HasOrthonormalCols W) :
    (U * W - Q')ᴴ * (U * W - Q') = Wᴴ * (W - Uᴴ * Q') + (W - Uᴴ * Q')ᴴ * W := by
  rw [hasOrthonormalCols_iff] at hU hQ' hW
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul, hQ', hW]
  abel

/-- $s^2 \le 2\delta^2$ with $s, \delta \ge 0$ gives $s \le \sqrt2\,\delta$. -/
private theorem le_sqrt_two_mul_of_sq_le {s δ : ℝ} (hδ : 0 ≤ δ) (hs : 0 ≤ s)
    (h : s ^ 2 ≤ 2 * δ ^ 2) : s ≤ √2 * δ := by
  rw [← Real.sqrt_sq hs, ← Real.sqrt_sq hδ, ← Real.sqrt_mul zero_le_two]
  exact Real.sqrt_le_sqrt h

open scoped MatrixOrder in
/-- For $\delta \ge 1$ the bound is trivial: the polar factor $\mathbf{V}$ of
$\mathbf{U}^{\mathsf H}\mathbf{Q}'$ gives
$\|\mathbf{U}\mathbf{V} - \mathbf{Q}'\|_2^2 \le 2 \le 2\delta^2$. -/
private theorem exists_hasOrthonormalCols_specNorm_mul_sub_le_of_one_le {U Q' : Matrix m r 𝕜}
    (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q') {δ : ℝ} (h1 : 1 ≤ δ) :
    ∃ W : Matrix r r 𝕜, HasOrthonormalCols W ∧ specNorm (U * W - Q') ≤ √2 * δ := by
  obtain ⟨V, hV, hVT⟩ := exists_hasOrthonormalCols_mul_sqrt_eq (Uᴴ * Q') le_rfl
  have hP0 := CFC.sqrt_nonneg ((Uᴴ * Q')ᴴ * (Uᴴ * Q'))
  set P := CFC.sqrt ((Uᴴ * Q')ᴴ * (Uᴴ * Q'))
  have h1' : Vᴴ * (Uᴴ * Q') = P := by
    rw [← hVT, ← Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.one_mul]
  have h2 : (Uᴴ * Q')ᴴ * V = P := by
    rw [← hVT, Matrix.conjTranspose_mul, Matrix.mul_assoc, hV.conjTranspose_mul_self,
      Matrix.mul_one, show Pᴴ = P from hP0.isSelfAdjoint]
  have hle : (U * V - Q')ᴴ * (U * V - Q') ≤ (2 : ℝ) • (1 : Matrix r r 𝕜) := by
    have e : (2 : ℝ) • (1 : Matrix r r 𝕜) - (U * V - Q')ᴴ * (U * V - Q') = P + P := by
      rw [conjTranspose_mul_self_sub_eq hU hQ' hV, Matrix.mul_sub, Matrix.conjTranspose_sub,
        Matrix.sub_mul, hV.conjTranspose_mul_self, h1', h2, two_smul]
      abel
    exact sub_nonneg.mp (e ▸ add_nonneg hP0 hP0)
  have hn := (specNorm_sq_le_iff_conjTranspose_mul_self_le (by norm_num : (0 : ℝ) ≤ 2)).mpr hle
  exact ⟨V, hV, le_sqrt_two_mul_of_sq_le (by linarith) (specNorm_nonneg _) (by nlinarith)⟩

/-- For $\delta < 1$: $\mathbf{Q}'^{\mathsf H}\mathbf{U}$ is a $\delta^2$-near isometry, so it is
within $\delta^2$ of a unitary $\mathbf{W}_0$, and $\mathbf{W} = \mathbf{W}_0^{\mathsf H}$ has
$\|\mathbf{U}\mathbf{W} - \mathbf{Q}'\|_2^2 \le 2\delta^2$. -/
private theorem exists_hasOrthonormalCols_specNorm_mul_sub_le_of_lt_one {U Q' : Matrix m r 𝕜}
    (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q') {C : Matrix r r 𝕜} {δ : ℝ}
    (hδ : specNorm (U - Q' * C) ≤ δ) (h1 : δ < 1) :
    ∃ W : Matrix r r 𝕜, HasOrthonormalCols W ∧ specNorm (U * W - Q') ≤ √2 * δ := by
  classical
  have hδ0 : 0 ≤ δ := (specNorm_nonneg _).trans hδ
  have hpy : ∀ y : r → 𝕜, ‖WithLp.toLp 2 y‖ ^ 2 =
      ‖WithLp.toLp 2 ((Q'ᴴ * U) *ᵥ y)‖ ^ 2 +
        ‖WithLp.toLp 2 ((1 - Q' * Q'ᴴ) *ᵥ (U *ᵥ y))‖ ^ 2 := fun y => by
    have h := (hQ'.isStarProjection_mul_conjTranspose).norm_toLp_sq_eq_add (U *ᵥ y)
    rw [hU.norm_toLp_mulVec] at h
    rw [h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      hQ'.norm_toLp_mulVec]
  have hF : (1 - Q' * Q'ᴴ) * Q' = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hQ'.conjTranspose_mul_self,
      Matrix.mul_one, sub_self]
  have hmat : (1 - Q' * Q'ᴴ) * U = (1 - Q' * Q'ᴴ) * (U - Q' * C) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc (1 - Q' * Q'ᴴ) Q' C, hF, Matrix.zero_mul, sub_zero]
  have hEb : ∀ y : r → 𝕜,
      ‖WithLp.toLp 2 ((1 - Q' * Q'ᴴ) *ᵥ (U *ᵥ y))‖ ≤ δ * ‖WithLp.toLp 2 y‖ := fun y =>
    calc _ = ‖WithLp.toLp 2 ((1 - Q' * Q'ᴴ) *ᵥ ((U - Q' * C) *ᵥ y))‖ := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]
      _ ≤ ‖WithLp.toLp 2 ((U - Q' * C) *ᵥ y)‖ :=
          hQ'.isStarProjection_mul_conjTranspose.one_sub.norm_toLp_mulVec_le _
      _ ≤ specNorm (U - Q' * C) * ‖WithLp.toLp 2 y‖ := norm_toLp_mulVec_le _ _
      _ ≤ δ * ‖WithLp.toLp 2 y‖ := mul_le_mul_of_nonneg_right hδ (norm_nonneg _)
  have hB : ∀ y : r → 𝕜, |‖WithLp.toLp 2 ((Q'ᴴ * U) *ᵥ y)‖ - ‖WithLp.toLp 2 y‖| ≤
      δ ^ 2 * ‖WithLp.toLp 2 y‖ := by
    intro y
    have hp := hpy y
    have he := hEb y
    have he0 := norm_nonneg (WithLp.toLp 2 ((1 - Q' * Q'ᴴ) *ᵥ (U *ᵥ y)))
    have hn := norm_nonneg (WithLp.toLp 2 y)
    have hs := norm_nonneg (WithLp.toLp 2 ((Q'ᴴ * U) *ᵥ y))
    generalize ‖WithLp.toLp 2 ((Q'ᴴ * U) *ᵥ y)‖ = s at *
    generalize ‖WithLp.toLp 2 ((1 - Q' * Q'ᴴ) *ᵥ (U *ᵥ y))‖ = e at *
    generalize ‖WithLp.toLp 2 y‖ = n at *
    have hd0 : 0 ≤ 1 - δ ^ 2 := by nlinarith
    have hlo2 : ((1 - δ ^ 2) * n) ^ 2 ≤ s ^ 2 := by
      nlinarith [mul_le_mul he he he0 (mul_nonneg hδ0 hn),
        mul_nonneg (mul_nonneg hd0 (sq_nonneg δ)) (sq_nonneg n)]
    have hlo := (pow_le_pow_iff_left₀ (mul_nonneg hd0 hn) hs two_ne_zero).mp hlo2
    have hup2 : s ^ 2 ≤ n ^ 2 := by nlinarith [sq_nonneg e]
    have hup := (pow_le_pow_iff_left₀ hs hn two_ne_zero).mp hup2
    rw [abs_le]; constructor <;> nlinarith
  obtain ⟨W0, hW0, hW0S⟩ := exists_hasOrthonormalCols_specNorm_sub_le_of_abs_norm_mulVec_sub_le
    (B := Q'ᴴ * U) (a := δ ^ 2) (sq_nonneg δ) (by nlinarith) hB
  have hW : HasOrthonormalCols W0ᴴ := hW0.conjTranspose_of_card_eq rfl
  have hD : specNorm (W0ᴴ - Uᴴ * Q') ≤ δ ^ 2 := by
    rw [show Uᴴ * Q' = (Q'ᴴ * U)ᴴ by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose],
      ← Matrix.conjTranspose_sub, specNorm_conjTranspose]
    exact hW0S
  have hWn : specNorm W0ᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hW0.specNorm_le_one
  have hn2 : specNorm ((U * W0ᴴ - Q')ᴴ * (U * W0ᴴ - Q')) ≤ 2 * δ ^ 2 := by
    rw [conjTranspose_mul_self_sub_eq hU hQ' hW]
    refine (specNorm_add_le _ _).trans ?_
    have hWn' : specNorm (W0ᴴ)ᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hWn
    have hDh : specNorm (W0ᴴ - Uᴴ * Q')ᴴ ≤ δ ^ 2 := by rw [specNorm_conjTranspose]; exact hD
    have h1 := (specNorm_mul_le _ _).trans (mul_le_mul hWn' hD (specNorm_nonneg _) zero_le_one)
    have h2 := (specNorm_mul_le _ _).trans (mul_le_mul hDh hWn (specNorm_nonneg _) (sq_nonneg δ))
    linarith
  rw [specNorm_conjTranspose_mul_self] at hn2
  exact ⟨W0ᴴ, hW, le_sqrt_two_mul_of_sq_le hδ0 (specNorm_nonneg _) hn2⟩

/-- **Orthonormal bases close up to a rotation, with constant $\sqrt2$**: if
$\mathbf{U}, \mathbf{Q}'$ have orthonormal columns and $\|\mathbf{U} - \mathbf{Q}'\mathbf{C}\|_2
\le \delta$ for some $\mathbf{C}$, there is a unitary $\mathbf{W}$ with $\|\mathbf{U}\mathbf{W} -
\mathbf{Q}'\|_2 \le \sqrt2\,\delta$. The orthogonal Procrustes rotation: for canonical angles
$\theta_i$ the optimum is $\max_i 2\sin(\theta_i/2)$ [StewartSun1990, Chapter I.5]. -/
theorem HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le_sqrt_two_mul
    {U Q' : Matrix m r 𝕜} (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q')
    {C : Matrix r r 𝕜} {δ : ℝ} (hδ : specNorm (U - Q' * C) ≤ δ) :
    ∃ W : Matrix r r 𝕜, HasOrthonormalCols W ∧ specNorm (U * W - Q') ≤ √2 * δ := by
  classical
  rcases lt_or_ge δ 1 with h1 | h1
  · exact exists_hasOrthonormalCols_specNorm_mul_sub_le_of_lt_one hU hQ' hδ h1
  · exact exists_hasOrthonormalCols_specNorm_mul_sub_le_of_one_le hU hQ' h1

/-- The first $r$ columns of $\mathbf{Q}\mathbf{R}$, $\mathbf{R}$ upper trapezoidal, are
$\mathbf{Q}_1\mathbf{R}_{11}$. -/
private theorem submatrix_mul_castLE_of_isUpperTrapezoidal {n r : ℕ} (hr : r ≤ n)
    (Q R : Matrix (Fin n) (Fin n) ℂ) (hR : IsUpperTrapezoidal R) :
    (Q * R).submatrix id (Fin.castLE hr) =
      Q.submatrix id (Fin.castLE hr) * R.submatrix (Fin.castLE hr) (Fin.castLE hr) := by
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ ?_ fun _ => rfl
  intro k hk
  have hkr : r ≤ (k : ℕ) := by
    by_contra h
    exact hk ⟨⟨k, by omega⟩, rfl⟩
  rw [hR k (Fin.castLE hr j) (by simp; omega), mul_zero]

/-- The decoded output of `NLAlib.deflate` is the first $r$ columns of the decoded $\mathbf{Q}$. -/
private theorem decodeMatrix_deflate {F : Type*} (M : FloatMachine F ℝ ℂ) (dec : F → ℝ)
    {n r : ℕ} (hr : r ≤ n) (A' : Matrix (Fin n) (Fin n) (F × F))
    (G : Matrix (Fin n) (Fin n) ℂ) :
    decodeMatrix dec (deflate M r A' G) =
      ((M.qr (M.mm A' (G.map M.normal))).1.map (decodeComplex dec)).submatrix id
        (Fin.castLE hr) := by
  ext i j
  simp [decodeMatrix, deflate, lt_of_lt_of_le j.2 hr, Fin.castLE]

/-- The error of the stored sample: $\|\mathbf{G} - \widetilde{\mathbf{G}}\|_2 \le
2\sqrt n\,c_{\mathrm N}u\|\mathbf{G}\|_2$. -/
private theorem specNorm_sub_map_normal_le {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ}
    (hnormal : IsNormalSampler (decodeComplex dec) u cN τ Ω M.normal) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (hcu : 0 ≤ cN * u) (hτN : τ * √(n : ℝ) ≤ specNorm G)
    (hΩG : specNorm G ≤ Ω) :
    specNorm (G - (G.map M.normal).map (decodeComplex dec)) ≤
      2 * (√(n : ℝ) * cN * u) * specNorm G := by
  set g := specNorm G
  set E := G - (G.map M.normal).map (decodeComplex dec)
  have hent : ∀ i j, ‖E i j‖ ^ 2 ≤ (cN * u) ^ 2 * (‖G i j‖ ^ 2 + max τ 0 ^ 2) := by
    intro i j
    have h := hnormal (G i j) ((norm_apply_le_specNorm G i j).trans hΩG)
    have hmx : max ‖G i j‖ τ ^ 2 ≤ ‖G i j‖ ^ 2 + max τ 0 ^ 2 := by
      rcases le_total ‖G i j‖ τ with h1 | h1
      · rw [max_eq_right h1, max_eq_left ((norm_nonneg _).trans h1)]
        nlinarith [sq_nonneg ‖G i j‖]
      · rw [max_eq_left h1]; nlinarith [sq_nonneg (max τ 0)]
    have hE : E i j = G i j - decodeComplex dec (M.normal (G i j)) := rfl
    rw [hE]
    calc ‖_‖ ^ 2 ≤ (cN * u * max ‖G i j‖ τ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = (cN * u) ^ 2 * max ‖G i j‖ τ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmx (sq_nonneg _)
  have hτ' : max τ 0 ^ 2 * n ≤ g ^ 2 := by
    have h1 : max τ 0 * √(n : ℝ) ≤ g := by
      rw [max_mul_of_nonneg _ _ (Real.sqrt_nonneg _), zero_mul]
      exact max_le hτN (specNorm_nonneg _)
    have h2 := pow_le_pow_left₀ (mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)) h1 2
    rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at h2
  have hfG := frobNorm_sq_le_card_mul_specNorm_sq G
  rw [Fintype.card_fin] at hfG
  have hfE : frobNorm E ^ 2 ≤ (cN * u) ^ 2 * (2 * n * g ^ 2) := by
    rw [frobNorm_sq_eq_sum]
    calc ∑ i, ∑ j, ‖E i j‖ ^ 2
        ≤ ∑ i, ∑ j, (cN * u) ^ 2 * (‖G i j‖ ^ 2 + max τ 0 ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
      _ = (cN * u) ^ 2 * (frobNorm G ^ 2 + n * n * max τ 0 ^ 2) := by
          rw [frobNorm_sq_eq_sum]
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
  refine (specNorm_le_frobNorm E).trans ((sq_le_sq₀ (frobNorm_nonneg _) ?_).1 ?_)
  · have := specNorm_nonneg G
    have := Real.sqrt_nonneg (n : ℝ)
    have : 0 ≤ √(n : ℝ) * cN * u := by rw [mul_assoc]; positivity
    positivity
  · have hsq : (2 * (√(n : ℝ) * cN * u) * g) ^ 2 = 4 * n * (cN * u) ^ 2 * g ^ 2 := by
      rw [show 2 * (√(n : ℝ) * cN * u) * g = 2 * √(n : ℝ) * (cN * u) * g by ring, mul_pow,
        mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    rw [hsq]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (cN * u)) (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
      (sq_nonneg g)]

/-- The rounding budget of `NLAlib.deflate`: $4q + 4c + 2a \le \beta \le 1/5$ gives
$c \le 1/20$, $a \le 1/10$ and $2c + a(1 + 2c) + q(1 + a)(1 + 2c) \le \tfrac35\beta$. -/
private theorem deflate_arith_budget {β c a q : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hbud : 4 * q + 4 * c + 2 * a ≤ β) (hβ5 : β ≤ 1 / 5) :
    c ≤ 1 / 20 ∧ a ≤ 1 / 10 ∧
      2 * c + a * (1 + 2 * c) + q * ((1 + a) * (1 + 2 * c)) ≤ 3 / 5 * β := by
  have hc' : c ≤ 1 / 20 := by linarith
  have ha' : a ≤ 1 / 10 := by linarith
  refine ⟨hc', ha', ?_⟩
  nlinarith [mul_nonneg ha hc, mul_nonneg hq hc, mul_nonneg hq ha, mul_nonneg (mul_nonneg hq ha) hc]

/-- The arithmetic giving $m \ge 1$ and $\beta \le 1/5$. -/
private theorem deflate_arith_one_le {s β g si kk mval : ℝ} (hs : 0 ≤ s) (hβ0 : 0 ≤ β)
    (hg : 0 ≤ g) (hsi : 0 ≤ si) (hkk : 0 ≤ kk) (hssi : 1 ≤ s * si) (hgk : 1 ≤ g * kk)
    (hmv : mval = (s + β + 1) * (g * kk * si)) (hmβ : mval * β ≤ 1 / 5) :
    1 ≤ s * (g * kk * si) ∧ β ≤ 1 / 5 := by
  have hX : 1 ≤ s * (g * kk * si) := by
    have h := mul_le_mul hssi hgk zero_le_one (mul_nonneg hs hsi)
    nlinarith
  have hX0 : 0 ≤ g * kk * si := mul_nonneg (mul_nonneg hg hkk) hsi
  have hm1 : 1 ≤ mval := by
    rw [hmv]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ β + 1) hX0]
  exact ⟨hX, by nlinarith⟩

/-- The arithmetic of the range conditions. -/
private theorem deflate_arith_range {s β g c a : ℝ} (hs : 0 ≤ s) (hβ0 : 0 ≤ β) (hg : 0 ≤ g)
    (hc : 0 ≤ c) (hc5 : c ≤ 1 / 20) (ha5 : a ≤ 1 / 10) :
    (1 + a) * ((s + β) * ((1 + 2 * c) * g)) ≤ 2 * (s + β) * g := by
  have h1 : (1 + a) * (1 + 2 * c) ≤ 2 := by nlinarith
  have h2 : 0 ≤ (s + β) * g := mul_nonneg (by linarith) hg
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]

/-- The arithmetic of the final bound: $\delta = m\beta - q/6$ dominates the bound on
$\|\mathbf{Z}\mathbf{K}^{-1}\mathbf{S}^{-1}\|_2$. -/
private theorem deflate_arith_delta {s β g si kk q : ℝ} (hβ0 : 0 ≤ β) (hg : 0 ≤ g)
    (hsi : 0 ≤ si) (hkk : 0 ≤ kk) (hX : 1 ≤ s * (g * kk * si)) (hq4 : q ≤ β / 4) :
    g * (β + 3 / 5 * (s + β) * β) * kk * si ≤ (s + β + 1) * (g * kk * si) * β - q / 6 := by
  have hX0 : 0 ≤ g * kk * si := mul_nonneg (mul_nonneg hg hkk) hsi
  have hXβ : β ≤ (s + β) * (g * kk * si) * β := by nlinarith [mul_nonneg hβ0 hX0]
  nlinarith

/-- The arithmetic of the final bound: $\sqrt2$ times the bound on
$\|\mathbf{Z}\mathbf{K}^{-1}\mathbf{S}^{-1}\|_2$, plus $q$, is at most $\tfrac32 m\beta$. -/
private theorem deflate_arith_sqrt_two {s β g si kk q : ℝ} (hβ0 : 0 ≤ β) (hg : 0 ≤ g)
    (hsi : 0 ≤ si) (hkk : 0 ≤ kk) (hs : 0 ≤ s) (hX : 1 ≤ s * (g * kk * si)) (hq : q ≤ β / 64) :
    √2 * (g * (β + (s + β) * β / 16) * kk * si) + q ≤
      3 / 2 * ((1 + 2 * β + s / 8) * (g * kk * si)) * β := by
  have hX0 : 0 ≤ g * kk * si := mul_nonneg (mul_nonneg hg hkk) hsi
  have h2 : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hY : 0 ≤ g * (β + (s + β) * β / 16) * kk * si := by
    have : 0 ≤ β + (s + β) * β / 16 := by positivity
    have := mul_nonneg this hX0
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right h2 hY
  nlinarith [mul_nonneg hβ0 hX0, mul_nonneg (mul_nonneg hβ0 hβ0) hX0, mul_nonneg hs hX0]

/-- Under the contract, $\mu_{\mathrm{QR}}(n)u \ge 0$: the QR error bound of the zero matrix. -/
private theorem FloatMachine.IsArithAccurate.qrConst_mul_nonneg {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsArithAccurate dec u τ Ω μM) (hqr : IsQRErr (decodeComplex dec) u τ Ω μQ M.qr) (n : ℕ)
    (hΩ : 0 ≤ Ω) : 0 ≤ μQ n * u := by
  have hz : (Matrix.of fun (_ : Fin n) (_ : Fin n) => (M.zero, M.zero)).map
      (decodeComplex dec) = 0 := by
    ext i j; apply Complex.ext <;> simp [decodeComplex, hM.dec_zero]
  obtain ⟨_, Q0, _, hQ0, _⟩ := hqr
    (Matrix.of fun (_ : Fin n) (_ : Fin n) => (M.zero, M.zero))
    (by rw [hz, specNorm_zero]; exact hΩ)
  rw [max_self] at hQ0
  exact (specNorm_nonneg _).trans hQ0

/-- Under the contract, $c_{\mathrm N}u \ge 0$ once the normal sampler is applied to a nonzero
entry in range. -/
private theorem IsNormalSampler.normalConst_mul_nonneg {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    (hnormal : IsNormalSampler (decodeComplex dec) u cN τ Ω M.normal) {n : ℕ}
    {G : Matrix (Fin n) (Fin n) ℂ} (hG : G ≠ 0)
    (hΩG : specNorm G ≤ Ω) : 0 ≤ cN * u := by
  by_contra hneg
  replace hneg := not_le.mp hneg
  apply hG
  ext i j
  by_contra hij
  have h := hnormal (G i j) ((norm_apply_le_specNorm G i j).trans hΩG)
  have hpos : 0 < max ‖G i j‖ τ := lt_max_of_lt_left (norm_pos_iff.mpr hij)
  have := mul_neg_of_neg_of_pos hneg hpos
  linarith [norm_nonneg (G i j - decodeComplex dec (M.normal (G i j)))]

/-- The computed product and QR factorization of `NLAlib.deflate`: with the sampler, product and
QR roundings $c = \sqrt n\,c_{\mathrm N}u \le 1/20$, $a = \mu_{\mathrm{MM}}(n)u \le 1/10$ and
$q = \mu_{\mathrm{QR}}(n)u$ within the budget $2c + a(1 + 2c) + q(1 + a)(1 + 2c) \le \kappa\beta$,
an exact factorization $\mathbf{Q}'\mathbf{R}$, $\mathbf{R}$ upper trapezoidal, is within
$\|\mathbf{G}\|_2(\beta + \kappa(s + \beta)\beta)$ of $\mathbf{A}\mathbf{G}$, with
$\mathbf{Q}'$ within $\mu_{\mathrm{QR}}(n)u$ of the computed $\mathbf{Q}$. -/
private theorem FloatMachine.IsArithAccurate.exists_specNorm_mul_sub_mul_qr_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β s : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsArithAccurate dec u τ Ω μM) (hqr : IsQRErr (decodeComplex dec) u τ Ω μQ M.qr)
    (hnormal : IsNormalSampler (decodeComplex dec) u cN τ Ω M.normal) {n : ℕ}
    {A G : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hs0 : 0 ≤ s) (hβ0 : 0 ≤ β)
    (hAle : specNorm A ≤ s) (hβ : specNorm (A - decodeMatrix dec A') ≤ β)
    (hcu : 0 ≤ cN * u) (hq0 : 0 ≤ μQ n * u) (ha0 : 0 ≤ μM n * u)
    (hc5 : √(n : ℝ) * cN * u ≤ 1 / 20) (ha5 : μM n * u ≤ 1 / 10) {κ : ℝ}
    (hbr : 2 * (√(n : ℝ) * cN * u) + μM n * u * (1 + 2 * (√(n : ℝ) * cN * u)) +
      μQ n * u * ((1 + μM n * u) * (1 + 2 * (√(n : ℝ) * cN * u))) ≤ κ * β)
    (hτ : τ ≤ s * specNorm G) (hτN : τ * √(n : ℝ) ≤ specNorm G)
    (hΩ : 2 * (s + β) * specNorm G ≤ Ω) (hΩG : specNorm G ≤ Ω) :
    ∃ Q' R : Matrix (Fin n) (Fin n) ℂ, HasOrthonormalCols Q' ∧ IsUpperTrapezoidal R ∧
      specNorm (Q' - (M.qr (M.mm A' (G.map M.normal))).1.map (decodeComplex dec)) ≤ μQ n * u ∧
      specNorm (A * G - Q' * R) ≤ specNorm G * (β + κ * (s + β) * β) := by
  set g := specNorm G with hg_def
  have hg0 : 0 ≤ g := specNorm_nonneg _
  set c := √(n : ℝ) * cN * u with hc_def
  set q := μQ n * u with hq_def
  set a := μM n * u with ha_def
  have hc0 : 0 ≤ c := by rw [hc_def, mul_assoc]; exact mul_nonneg (Real.sqrt_nonneg _) hcu
  -- the stored sample
  set At := A'.map (decodeComplex dec) with hAt_def
  set Gs := G.map M.normal with hGs_def
  set Gt := Gs.map (decodeComplex dec) with hGt_def
  have hβ' : specNorm (A - At) ≤ β := hβ
  have hEG : specNorm (G - Gt) ≤ 2 * c * g :=
    specNorm_sub_map_normal_le hnormal G hcu hτN hΩG
  have hAtle : specNorm At ≤ s + β := by
    calc specNorm At = specNorm (A - (A - At)) := by rw [sub_sub_cancel]
      _ ≤ specNorm A + specNorm (A - At) := specNorm_sub_le _ _
      _ ≤ s + β := add_le_add hAle hβ'
  have hGtle : specNorm Gt ≤ (1 + 2 * c) * g := by
    calc specNorm Gt = specNorm (G - (G - Gt)) := by rw [sub_sub_cancel]
      _ ≤ g + specNorm (G - Gt) := specNorm_sub_le _ _
      _ ≤ g + 2 * c * g := add_le_add le_rfl hEG
      _ = (1 + 2 * c) * g := by ring
  set P := (s + β) * ((1 + 2 * c) * g) with hP_def
  have hP0 : 0 ≤ P := by positivity
  have hprod : specNorm At * specNorm Gt ≤ P :=
    mul_le_mul hAtle hGtle (specNorm_nonneg _) (by linarith)
  have hτP : τ ≤ P := by
    refine hτ.trans ?_
    rw [hP_def]
    have h1 : g ≤ (1 + 2 * c) * g := le_mul_of_one_le_left hg0 (by linarith)
    calc s * g ≤ s * ((1 + 2 * c) * g) := mul_le_mul_of_nonneg_left h1 hs0
      _ ≤ (s + β) * ((1 + 2 * c) * g) :=
        mul_le_mul_of_nonneg_right (by linarith) (hg0.trans h1)
  have hP2 : (1 + a) * P ≤ 2 * (s + β) * g := deflate_arith_range hs0 hβ0 hg0 hc0 hc5 ha5
  have hPa : P ≤ (1 + a) * P := le_mul_of_one_le_left hP0 (by linarith)
  -- the product
  set Ms := M.mm A' Gs with hMs_def
  set Mt := Ms.map (decodeComplex dec) with hMt_def
  have hMM : specNorm (At * Gt - Mt) ≤ a * P := by
    have h := hM.isMatMulErr.specNorm_mul_sub_le A' Gs (by linarith)
    rw [max_self, max_self] at h
    exact h.trans (mul_le_mul_of_nonneg_left (max_le hprod hτP) ha0)
  have hMtle : specNorm Mt ≤ (1 + a) * P := by
    calc specNorm Mt = specNorm (At * Gt - (At * Gt - Mt)) := by rw [sub_sub_cancel]
      _ ≤ specNorm (At * Gt) + specNorm (At * Gt - Mt) := specNorm_sub_le _ _
      _ ≤ P + a * P := add_le_add ((specNorm_mul_le _ _).trans hprod) hMM
      _ = (1 + a) * P := by ring
  -- the QR factorization
  obtain ⟨hR, Q', hQ', hQQ, hMQR⟩ := hqr Ms (hMtle.trans (hP2.trans hΩ))
  rw [max_self] at hQQ hMQR
  set Qb := (M.qr Ms).1.map (decodeComplex dec) with hQb_def
  set Rb := (M.qr Ms).2.map (decodeComplex dec) with hRb_def
  have hQR : specNorm (Mt - Q' * Rb) ≤ q * ((1 + a) * P) :=
    hMQR.trans (mul_le_mul_of_nonneg_left (max_le hMtle (hτP.trans hPa)) hq0)
  -- the total error
  set T := A * G - Q' * Rb with hT_def
  have hT : specNorm T ≤ g * (β + κ * (s + β) * β) := by
    have heq : T = (A - At) * G + At * (G - Gt) + (At * Gt - Mt) + (Mt - Q' * Rb) := by
      rw [hT_def, Matrix.sub_mul, Matrix.mul_sub]; abel
    have h1 : specNorm ((A - At) * G) ≤ β * g :=
      (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hβ' hg0)
    have h2 : specNorm (At * (G - Gt)) ≤ (s + β) * (2 * c * g) :=
      (specNorm_mul_le _ _).trans (mul_le_mul hAtle hEG (specNorm_nonneg _) (by linarith))
    have hsum : β * g + (s + β) * (2 * c * g) + a * P + q * ((1 + a) * P) ≤
        g * (β + κ * (s + β) * β) := by
      have hsg : 0 ≤ (s + β) * g := mul_nonneg (by linarith) hg0
      rw [hP_def]; nlinarith [mul_le_mul_of_nonneg_left hbr hsg]
    refine le_trans ?_ hsum
    rw [heq]
    refine (specNorm_add_le _ _).trans ?_
    refine add_le_add ((specNorm_add_le _ _).trans ?_) hQR
    exact add_le_add ((specNorm_add_le _ _).trans (add_le_add h1 h2)) hMM
  exact ⟨Q', Rb, hQ', hR, hQQ, hT⟩

/-- The first $r$ columns $\mathbf{Q}'_1$ of an exact factorization $\mathbf{Q}'\mathbf{R}$ near
$\mathbf{A}\mathbf{G}$, $\mathbf{A} = \mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$, span nearly the
range of $\mathbf{U}$: $\|\mathbf{U} - \mathbf{Q}'_1\mathbf{C}\|_2 \le \delta$ for some
$\mathbf{C}$. -/
private theorem exists_specNorm_sub_submatrix_mul_le {n r : ℕ} (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S)
    {A G Q' R : Matrix (Fin n) (Fin n) ℂ} (hA : A = U * S * Vᴴ)
    (hG : IsUnit (Vᴴ * G.submatrix id (Fin.castLE hr))) (hR : IsUpperTrapezoidal R) {δ : ℝ}
    (hδ : specNorm (A * G - Q' * R) * specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹ *
      specNorm S⁻¹ ≤ δ) :
    ∃ C, specNorm (U - Q'.submatrix id (Fin.castLE hr) * C) ≤ δ := by
  set e := Fin.castLE hr
  set K := Vᴴ * G.submatrix id e with hK_def
  set T := A * G - Q' * R with hT_def
  have hAG₁ : A * G.submatrix id e = Q'.submatrix id e * R.submatrix e e + T.submatrix id e := by
    rw [← submatrix_mul_castLE_of_isUpperTrapezoidal hr Q' R hR]
    ext i j
    simp only [hT_def, Matrix.add_apply, Matrix.submatrix_apply, id, Matrix.sub_apply,
      Matrix.mul_apply]
    ring
  have hUeq : U - Q'.submatrix id e * (R.submatrix e e * K⁻¹ * S⁻¹) =
      T.submatrix id e * K⁻¹ * S⁻¹ := by
    have hU' : U = A * G.submatrix id e * K⁻¹ * S⁻¹ := by
      calc U = U * S * K * K⁻¹ * S⁻¹ := by
            rw [Matrix.mul_nonsing_inv_cancel_right K _ ((Matrix.isUnit_iff_isUnit_det K).mp hG),
              Matrix.mul_nonsing_inv_cancel_right S _ ((Matrix.isUnit_iff_isUnit_det S).mp hS)]
        _ = A * G.submatrix id e * K⁻¹ * S⁻¹ := by rw [hA, hK_def]; simp only [Matrix.mul_assoc]
    rw [hU', hAG₁]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    abel
  refine ⟨R.submatrix e e * K⁻¹ * S⁻¹, ?_⟩
  rw [hUeq]
  refine ((specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _)
    (specNorm_nonneg _))).trans (le_trans ?_ hδ)
  gcongr
  exact specNorm_submatrix_le T Function.injective_id (Fin.castLE_injective hr)

/-- A rotation of $\mathbf{U}$ within $x$ of the first $r$ columns of $\mathbf{Q}'$ is within
$x + q$ of those of $\mathbf{Q}$, for $\|\mathbf{Q}' - \mathbf{Q}\|_2 \le q$. -/
private theorem specNorm_mul_sub_submatrix_le_add {n r : ℕ} (hr : r ≤ n)
    {U : Matrix (Fin n) (Fin r) ℂ} {W : Matrix (Fin r) (Fin r) ℂ} {Q' Q : Matrix (Fin n) (Fin n) ℂ}
    {x q : ℝ} (hW : specNorm (U * W - Q'.submatrix id (Fin.castLE hr)) ≤ x)
    (hQ : specNorm (Q' - Q) ≤ q) :
    specNorm (U * W - Q.submatrix id (Fin.castLE hr)) ≤ x + q := by
  rw [← sub_add_sub_cancel _ (Q'.submatrix id (Fin.castLE hr))]
  refine (specNorm_add_le _ _).trans (add_le_add hW ?_)
  exact (specNorm_submatrix_le (Q' - Q) Function.injective_id (Fin.castLE_injective hr)).trans hQ

/-- The norms entering the factor $m$ of `NLAlib.deflate`: $\|\mathbf{A}\|_2 \le \|\mathbf{S}\|_2$,
$1 \le \|\mathbf{S}\|_2\|\mathbf{S}^{-1}\|_2$ and
$1 \le \|\mathbf{G}\|_2\|(\mathbf{V}^{\mathsf H}\mathbf{G}_1)^{-1}\|_2$. -/
private theorem specNorm_le_and_one_le_and_one_le {n r : ℕ} (hr : r ≤ n) (hr1 : 0 < r)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A G : Matrix (Fin n) (Fin n) ℂ}
    (hA : A = U * S * Vᴴ) (hG : IsUnit (Vᴴ * G.submatrix id (Fin.castLE hr))) :
    specNorm A ≤ specNorm S ∧ 1 ≤ specNorm S * specNorm S⁻¹ ∧
      1 ≤ specNorm G * specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹ := by
  have : Nonempty (Fin r) := ⟨⟨0, hr1⟩⟩
  set K := Vᴴ * G.submatrix id (Fin.castLE hr)
  have hKG : specNorm K ≤ specNorm G := (hV.specNorm_conjTranspose_mul_le _).trans
    (specNorm_submatrix_le G Function.injective_id (Fin.castLE_injective hr))
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]
    refine (specNorm_mul_le _ _).trans ?_
    rw [hU.specNorm_mul_left, specNorm_conjTranspose]
    exact mul_le_of_le_one_right (specNorm_nonneg _) hV.specNorm_le_one
  · calc (1 : ℝ) = specNorm (S * S⁻¹) := by
          rw [Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hS), specNorm_one]
      _ ≤ _ := specNorm_mul_le _ _
  · calc (1 : ℝ) = specNorm (K * K⁻¹) := by
          rw [Matrix.mul_nonsing_inv K ((Matrix.isUnit_iff_isUnit_det K).mp hG), specNorm_one]
      _ ≤ specNorm K * specNorm K⁻¹ := specNorm_mul_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hKG (specNorm_nonneg _)

/-- **Deterministic accuracy of randomized deflation** (Theorem 3.3, deterministic half): under
the arithmetic contract `NLAlib.FloatMachine.IsArithAccurate` $u$ $\tau$ $\Omega$ with product
constant $\mu_{\mathrm{MM}}$, with the QR routine meeting `NLAlib.IsQRErr` with constant
$\mu_{\mathrm{QR}}$ and the normal sampler meeting `NLAlib.IsNormalSampler` with constant
$c_{\mathrm N}$ (at $u$, $\tau$, $\Omega$, through the decoding), let
$\mu_{\mathrm{MM}}(n) \ge 0$, $u \ge 0$, $r \le n$, $\mathbf{U}, \mathbf{V} \in
\mathbb{C}^{n \times r}$ have orthonormal columns,
$\mathbf{S} \in \mathbb{C}^{r \times r}$ be invertible, $\mathbf{A} =
\mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$, $\widetilde{\mathbf{A}}$ stored with
$\|\mathbf{A} - \bar{\widetilde{\mathbf{A}}}\|_2 \le \beta$, and $\mathbf{G}$ have
$\mathbf{V}^{\mathsf{H}}\mathbf{G}_1$ invertible, $\mathbf{G}_1$ its first $r$ columns. With
$m = (\|\mathbf{S}\|_2 + \beta + 1)\|\mathbf{S}^{-1}\|_2\|\mathbf{G}\|_2
\|(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}\|_2$, if $m\beta \le 1/5$,
$(4\mu_{\mathrm{QR}}(n) + 4\sqrt n\,c_{\mathrm N} + 2\mu_{\mathrm{MM}}(n))u \le \beta$,
$\tau \le \|\mathbf{S}\|_2\|\mathbf{G}\|_2$, $\sqrt n\,\tau \le \|\mathbf{G}\|_2$ (the floor of the
normal sampler, absorbed into a factor $2$) and $2(\|\mathbf{S}\|_2 + \beta)\|\mathbf{G}\|_2 \le
\Omega$, $\|\mathbf{G}\|_2 \le \Omega$ (so the normal sampler's contract covers every entry), then
there is a unitary $\mathbf{W}$ with $$\|\mathbf{U}\mathbf{W} -
\mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le 6m\beta \,,$$ $\mathsf{deflate}$ the decoded
output of `NLAlib.deflate` with ideal sample $\mathbf{G}$. [Shah2024, Theorem 3.3], there for
$\mathbf{S}$ the diagonal of singular values and with the probability folded in.
Result: deflate-accuracy-deterministic -/
theorem FloatMachine.IsArithAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β mval : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsArithAccurate dec u τ Ω μM) (hqr : IsQRErr (decodeComplex dec) u τ Ω μQ M.qr)
    (hnormal : IsNormalSampler (decodeComplex dec) u cN τ Ω M.normal)
    {n r : ℕ} (hμM : 0 ≤ μM n) (hu₀ : 0 ≤ u) (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A G : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β)
    (hG : IsUnit (Vᴴ * G.submatrix id (Fin.castLE hr)))
    (hm : mval = (specNorm S + β + 1) * specNorm S⁻¹ * specNorm G *
      specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹)
    (hmβ : mval * β ≤ 1 / 5) (hu : (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β)
    (hτ : τ ≤ specNorm S * specNorm G) (hτN : τ * √(n : ℝ) ≤ specNorm G)
    (hΩ : 2 * (specNorm S + β) * specNorm G ≤ Ω) (hΩG : specNorm G ≤ Ω) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' G)) ≤ 6 * mval * β := by
  classical
  have hβ0 : 0 ≤ β := (specNorm_nonneg _).trans hβ
  have hm0 : 0 ≤ mval := by
    rw [hm]
    have := specNorm_nonneg S
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (specNorm_nonneg _))
      (specNorm_nonneg _)) (specNorm_nonneg _)
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · refine ⟨1, hasOrthonormalCols_one, ?_⟩
    rw [Subsingleton.elim (U * 1 - _) 0, specNorm_zero]
    have := mul_nonneg hm0 hβ0
    linarith
  obtain ⟨hAle, hssi, hgk⟩ := specNorm_le_and_one_le_and_one_le hr hr1 hU hV hS hA hG
  set s := specNorm S
  set g := specNorm G with hg_def
  set si := specNorm S⁻¹
  set kk := specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹
  have hg0 : 0 ≤ g := specNorm_nonneg _
  have hkk0 : 0 ≤ kk := specNorm_nonneg _
  have hsi0 : 0 ≤ si := specNorm_nonneg _
  have hmv : mval = (s + β + 1) * (g * kk * si) := by rw [hm]; ring
  obtain ⟨hX, hβ5⟩ := deflate_arith_one_le (specNorm_nonneg _) hβ0 hg0 hsi0 hkk0 hssi hgk hmv hmβ
  have hgne : g ≠ 0 := by intro h; rw [h, zero_mul] at hgk; linarith
  have hcu : 0 ≤ cN * u :=
    hnormal.normalConst_mul_nonneg (fun h => hgne (by rw [hg_def, h, specNorm_zero])) hΩG
  have hq0 := hM.qrConst_mul_nonneg hqr n (hg0.trans hΩG)
  have hc0 := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hcu
  have ha0 : 0 ≤ μM n * u := mul_nonneg hμM hu₀
  have hbud : 4 * (μQ n * u) + 4 * (√(n : ℝ) * cN * u) + 2 * (μM n * u) ≤ β := by linarith
  obtain ⟨hc5, ha5, hbr⟩ := deflate_arith_budget (by rwa [mul_assoc]) ha0 hq0 hbud hβ5
  obtain ⟨Q', R, hQ', hR, hQQ, hT⟩ := hM.exists_specNorm_mul_sub_mul_qr_le hqr hnormal
    (specNorm_nonneg _) hβ0 hAle hβ hcu hq0 ha0 hc5 ha5 hbr hτ hτN hΩ hΩG
  obtain ⟨C, hC⟩ := exists_specNorm_sub_submatrix_mul_le hr hS hA hG hR
    (δ := mval * β - μQ n * u / 6) (by
      rw [hmv]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT hkk0) hsi0).trans
        (deflate_arith_delta hβ0 hg0 hsi0 hkk0 hX (by linarith)))
  have hQ'₁ : HasOrthonormalCols (Q'.submatrix id (Fin.castLE hr)) :=
    hQ'.submatrix (Equiv.refl _) (Fin.castLE_injective hr)
  obtain ⟨W, hW, hUW⟩ := hU.exists_hasOrthonormalCols_specNorm_mul_sub_le hQ'₁ (ν := 0)
    (by rw [sub_self, specNorm_zero]) hC ((specNorm_nonneg _).trans hC) (by linarith)
  refine ⟨W, hW, ?_⟩
  rw [decodeMatrix_deflate M dec hr A' G]
  exact (specNorm_mul_sub_submatrix_le_add hr hUW hQQ).trans_eq (by ring)

/-- **Deterministic accuracy of randomized deflation, roundings charged at $\beta/16$**
(Theorem 3.3, deterministic half): under the arithmetic contract
`NLAlib.FloatMachine.IsArithAccurate` $u$ $\tau$ $\Omega$ with product constant
$\mu_{\mathrm{MM}}$, with the QR routine meeting `NLAlib.IsQRErr` with constant
$\mu_{\mathrm{QR}}$ and the normal sampler meeting `NLAlib.IsNormalSampler` with constant
$c_{\mathrm N}$ (at $u$, $\tau$, $\Omega$, through the decoding), let
$\mu_{\mathrm{MM}}(n) \ge 0$, $u \ge 0$, $r \le n$, $\mathbf{U}, \mathbf{V} \in
\mathbb{C}^{n \times r}$ have orthonormal columns, $\mathbf{S} \in \mathbb{C}^{r \times r}$ be
invertible, $\mathbf{A} = \mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$, $\widetilde{\mathbf{A}}$
stored with $\|\mathbf{A} - \bar{\widetilde{\mathbf{A}}}\|_2 \le \beta$, and $\mathbf{G}$ have
$\mathbf{V}^{\mathsf{H}}\mathbf{G}_1$ invertible, $\mathbf{G}_1$ its first $r$ columns. With
$m = (1 + 2\beta + \|\mathbf{S}\|_2/8)\|\mathbf{S}^{-1}\|_2\|\mathbf{G}\|_2
\|(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}\|_2$, if $m\beta \le 1/64$,
$16(4\mu_{\mathrm{QR}}(n) + 4\sqrt n\,c_{\mathrm N} + 2\mu_{\mathrm{MM}}(n))u \le \beta$,
$\tau \le \|\mathbf{S}\|_2\|\mathbf{G}\|_2$, $\sqrt n\,\tau \le \|\mathbf{G}\|_2$ and
$2(\|\mathbf{S}\|_2 + \beta)\|\mathbf{G}\|_2 \le \Omega$, $\|\mathbf{G}\|_2 \le \Omega$, then there
is a unitary $\mathbf{W}$ with
$$\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le
\tfrac32 m\beta \,.$$
Compared with
`NLAlib.FloatMachine.IsArithAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le`
($6m\beta$ with the factor $\|\mathbf{S}\|_2 + \beta + 1$), the Procrustes rotation
(`NLAlib.HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le_sqrt_two_mul`) and the
smaller rounding charge improve the constant. [Shah2024, Theorem 3.3]. -/
theorem
    FloatMachine.IsArithAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β mval : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsArithAccurate dec u τ Ω μM) (hqr : IsQRErr (decodeComplex dec) u τ Ω μQ M.qr)
    (hnormal : IsNormalSampler (decodeComplex dec) u cN τ Ω M.normal)
    {n r : ℕ} (hμM : 0 ≤ μM n) (hu₀ : 0 ≤ u) (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A G : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β)
    (hG : IsUnit (Vᴴ * G.submatrix id (Fin.castLE hr)))
    (hm : mval = (1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * specNorm G *
      specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹)
    (hmβ : mval * β ≤ 1 / 64) (hu : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β)
    (hτ : τ ≤ specNorm S * specNorm G) (hτN : τ * √(n : ℝ) ≤ specNorm G)
    (hΩ : 2 * (specNorm S + β) * specNorm G ≤ Ω) (hΩG : specNorm G ≤ Ω) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' G)) ≤ 3 / 2 * mval * β := by
  classical
  have hβ0 : 0 ≤ β := (specNorm_nonneg _).trans hβ
  have hm0 : 0 ≤ mval := by
    rw [hm]
    have := specNorm_nonneg S
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (specNorm_nonneg _))
      (specNorm_nonneg _)) (specNorm_nonneg _)
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · refine ⟨1, hasOrthonormalCols_one, ?_⟩
    rw [Subsingleton.elim (U * 1 - _) 0, specNorm_zero]
    have := mul_nonneg hm0 hβ0
    linarith
  obtain ⟨hAle, hssi, hgk⟩ := specNorm_le_and_one_le_and_one_le hr hr1 hU hV hS hA hG
  set s := specNorm S
  set g := specNorm G with hg_def
  set si := specNorm S⁻¹
  set kk := specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹
  have hs0 : 0 ≤ s := specNorm_nonneg _
  have hg0 : 0 ≤ g := specNorm_nonneg _
  have hkk0 : 0 ≤ kk := specNorm_nonneg _
  have hsi0 : 0 ≤ si := specNorm_nonneg _
  have hmv : mval = (1 + 2 * β + s / 8) * (g * kk * si) := by rw [hm]; ring
  have hX0 : 0 ≤ g * kk * si := by positivity
  have hX : 1 ≤ s * (g * kk * si) := by
    have h := mul_le_mul hssi hgk zero_le_one (mul_nonneg hs0 hsi0)
    nlinarith
  have hβ8 : β ≤ 1 / 8 := by
    have : 1 / 8 ≤ mval := by rw [hmv]; nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + 2 * β) hX0]
    nlinarith
  have hgne : g ≠ 0 := by intro h; rw [h, zero_mul] at hgk; linarith
  have hcu : 0 ≤ cN * u :=
    hnormal.normalConst_mul_nonneg (fun h => hgne (by rw [hg_def, h, specNorm_zero])) hΩG
  have hq0 := hM.qrConst_mul_nonneg hqr n (hg0.trans hΩG)
  have hc0 := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hcu
  have ha0 : 0 ≤ μM n * u := mul_nonneg hμM hu₀
  have hbud : 4 * (μQ n * u) + 4 * (√(n : ℝ) * cN * u) + 2 * (μM n * u) ≤ β / 16 := by
    linarith
  obtain ⟨hc5, ha5, hbr⟩ := deflate_arith_budget (by rwa [mul_assoc]) ha0 hq0 hbud (by linarith)
  obtain ⟨Q', R, hQ', hR, hQQ, hT⟩ := hM.exists_specNorm_mul_sub_mul_qr_le hqr hnormal hs0 hβ0
    hAle hβ hcu hq0 ha0 hc5 ha5 (hbr.trans (by linarith : 3 / 5 * (β / 16) ≤ 1 / 16 * β)) hτ hτN
    hΩ hΩG
  obtain ⟨C, hC⟩ := exists_specNorm_sub_submatrix_mul_le hr hS hA hG hR le_rfl
  have hQ'₁ : HasOrthonormalCols (Q'.submatrix id (Fin.castLE hr)) :=
    hQ'.submatrix (Equiv.refl _) (Fin.castLE_injective hr)
  obtain ⟨W, hW, hUW⟩ := hU.exists_hasOrthonormalCols_specNorm_mul_sub_le_sqrt_two_mul hQ'₁ hC
  refine ⟨W, hW, ?_⟩
  rw [decodeMatrix_deflate M dec hr A' G]
  refine (specNorm_mul_sub_submatrix_le_add hr hUW hQQ).trans (le_trans ?_
    ((deflate_arith_sqrt_two (q := μQ n * u) hβ0 hg0 hsi0 hkk0 hs0 hX (by linarith)).trans
      (by rw [hmv])))
  gcongr
  linarith [hT]

end DeterministicAccuracy

open scoped Matrix in
/-- A square matrix whose action is bounded below by $x > 0$,
$x\|\mathbf{z}\| \le \|\mathbf{M}\mathbf{z}\|$ for every $\mathbf{z}$, is a unit with
$\|\mathbf{M}^{-1}\|_2 \le 1/x$. No printed source needed: injectivity, then the bound applied
to $\mathbf{M}^{-1}\mathbf{y}$. -/
theorem isUnit_and_specNorm_inv_le_of_forall_mul_norm_le {r : ℕ}
    {M : Matrix (Fin r) (Fin r) ℂ}
    {x : ℝ} (hx : 0 < x)
    (h : ∀ z : Fin r → ℂ, x * ‖WithLp.toLp 2 z‖ ≤ ‖WithLp.toLp 2 (M *ᵥ z)‖) :
    IsUnit M ∧ specNorm M⁻¹ ≤ 1 / x := by
  have hinj : Function.Injective M.mulVec := by
    intro a b hab
    have h0 : x * ‖WithLp.toLp 2 (a - b)‖ ≤ 0 := by
      have := h (a - b)
      rw [Matrix.mulVec_sub, hab, sub_self] at this
      simpa using this
    have hn : ‖WithLp.toLp 2 (a - b)‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (WithLp.toLp 2 (a - b))]) (norm_nonneg _)
    simpa [sub_eq_zero] using hn
  have hU : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  refine ⟨hU, (specNorm_le_iff (by positivity)).2 fun y => ?_⟩
  have h1 := h (M⁻¹ *ᵥ y)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hU),
    Matrix.one_mulVec] at h1
  rw [one_div_mul_eq_div, le_div_iff₀ hx]
  linarith [mul_comm x ‖WithLp.toLp 2 (M⁻¹ *ᵥ y)‖]

end NLAlib
