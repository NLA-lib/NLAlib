/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.Inverse
public import NLAlib.Matrix.QRIteration.HessenbergDeflation
public import NLAlib.Matrix.Spectral.Diagonalizable
public import NLAlib.Matrix.Spectral.Gershgorin

/-!
# The eigenvector condition number of deflated blocks

The convergence theorem of the shifted QR iteration
(`NLAlib.IsUpperHessenberg.exists_le_isDecoupled_shqrIterate`) needs a bound $B$ on the
eigenvector condition number $\kappa_V$ of the matrix it runs on. After a deflation the iteration
runs on diagonal blocks of a perturbed, unitarily similar matrix, so the bound must pass to them.
Two facts give it under an eigenvalue gap ([BanksGarzaVargasSrivastava2022, Lemmas 6.1 and
6.2]):

* a small perturbation of a diagonalizable matrix with distinct eigenvalues keeps them distinct
  and at most doubles $\kappa_V$ (Lemma 6.1 there; the eigenvector perturbation of
  [BanksGarzaVargasKulkarniSrivastava2020, Proposition 1.1]);
* each diagonal block of a diagonalizable block upper triangular matrix has an eigenvector
  matrix with $\kappa_V$ at most that of the whole (Lemma 6.2 there). Its proof claims that every
  eigenvector matrix is block triangular, which is false when two blocks share an eigenvalue (gap
  G15 of `docs/design/Eigensolvers-ShiftedQR-Ops.md`); the statement is true in general, by the
  Cholesky argument recorded in `docs/design/Eigensolvers-ShiftedQR-Ops.md`, §G15: with
  $\mathbf{V}^{-\mathsf H}\mathbf{V}^{-1} = \mathbf{R}^{\mathsf H}\mathbf{R}$, the matrix
  $\mathbf{R}\mathbf{M}\mathbf{R}^{-1}$ is normal and block triangular, hence block diagonal.

## Main results

* `IsStarNormal.apply_eq_zero_of_blockTriangular`: a normal block triangular matrix is block
  diagonal.
* `Matrix.BlockTriangular.exists_pseudoConditionNumber_subBlock_le`: the diagonal blocks.
* `NLAlib.exists_pseudoConditionNumber_add_le`: the perturbation.
* `NLAlib.DeflationInv.exists_pseudoConditionNumber_subBlock_le`: every active block of
  deflation.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- The label of an index in a range of a partition is the start of that range. -/
private theorem rangeLabel_eq_of_mem {N : ℕ} {rs : List (ℕ × ℕ)}
    (hrs : IsRangePartition N rs) {r : ℕ × ℕ} (hr : r ∈ rs) {k : Fin N} (hk₁ : r.1 ≤ (k : ℕ))
    (hk₂ : (k : ℕ) < r.1 + r.2) : rangeLabel rs k = r.1 := by
  unfold rangeLabel
  cases hf : rs.find? (fun r => (r.1 ≤ (k : ℕ) ∧ (k : ℕ) < r.1 + r.2 : Bool)) with
  | none => exact absurd (List.find?_eq_none.mp hf r hr) (by simp [hk₁, hk₂])
  | some r₀ =>
    have h₀ := List.find?_some hf
    simp only [decide_eq_true_eq] at h₀
    have := (hrs.2.2 k k.2).unique ⟨List.mem_of_find?_eq_some hf, h₀⟩ ⟨hr, hk₁, hk₂⟩
    simp [this]

/-- On a partition into ranges the label is monotone in the index. -/
private theorem rangeLabel_le_of_le {N : ℕ} {rs : List (ℕ × ℕ)} (hrs : IsRangePartition N rs)
    {i j : Fin N} (h : i ≤ j) : rangeLabel rs i ≤ rangeLabel rs j := by
  obtain ⟨ri, ⟨hri, hi₁, hi₂⟩, -⟩ := hrs.2.2 i i.2
  obtain ⟨rj, ⟨hrj, hj₁, hj₂⟩, -⟩ := hrs.2.2 j j.2
  have hij : (i : ℕ) ≤ j := h
  rw [rangeLabel_eq_of_mem hrs hri hi₁ hi₂, rangeLabel_eq_of_mem hrs hrj hj₁ hj₂]
  by_contra hlt
  have := (hrs.2.2 ri.1 (by omega)).unique ⟨hri, le_rfl, by omega⟩ ⟨hrj, by omega, by omega⟩
  rw [this] at hlt
  exact hlt le_rfl

/-- The indices with the label of a range of a partition are those of its block. -/
private theorem rangeLabel_eq_iff_mem_range {rs : List (ℕ × ℕ)}
    (hrs : IsRangePartition (n + 1) rs) {r : ℕ × ℕ} (hr : r ∈ rs) (k : Fin (n + 1)) :
    rangeLabel rs k = r.1 ↔ k ∈ Set.range (blockIndex n r) := by
  have hrv := hrs.2.1 r hr
  have hidx : ∀ a : Fin r.2, (blockIndex n r a : ℕ) = r.1 + a := fun a => by
    simp only [blockIndex]; omega
  refine ⟨fun hk => ?_, ?_⟩
  · obtain ⟨r', ⟨hr', h₁, h₂⟩, -⟩ := hrs.2.2 k k.2
    have hr'v := hrs.2.1 r' hr'
    rw [rangeLabel_eq_of_mem hrs hr' h₁ h₂] at hk
    have : r' = r := (hrs.2.2 r.1 (by omega)).unique ⟨hr', by omega, by omega⟩
      ⟨hr, le_rfl, by omega⟩
    subst this
    exact ⟨⟨k - r'.1, by omega⟩, Fin.ext (by rw [hidx]; simp; omega)⟩
  · rintro ⟨a, rfl⟩
    exact rangeLabel_eq_of_mem hrs hr (by rw [hidx]; omega) (by rw [hidx]; omega)

/-- The block of a range of a partition is read at injective indices. -/
private theorem blockIndex_injective {rs : List (ℕ × ℕ)} (hrs : IsRangePartition (n + 1) rs)
    {r : ℕ × ℕ} (hr : r ∈ rs) : Function.Injective (blockIndex n r) := by
  have hrv := hrs.2.1 r hr
  intro a b hab
  have := congrArg Fin.val hab
  simp only [blockIndex] at this
  exact Fin.ext (by omega)

/-- The diagonal block of a product of block triangular matrices, read on the indices of one
label, is the product of the diagonal blocks. -/
private theorem submatrix_mul_of_blockTriangular {m ι : Type*} [Fintype m] [Fintype ι]
    {b : m → ℕ} {X Y : Matrix m m ℂ} (hX : X.BlockTriangular b) (hY : Y.BlockTriangular b)
    {e : ι → m} (he : Function.Injective e) {a : ℕ} (hea : ∀ k, b k = a ↔ k ∈ Set.range e) :
    (X * Y).submatrix e e = X.submatrix e e * Y.submatrix e e := by
  classical
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hi : b (e i) = a := (hea _).2 ⟨i, rfl⟩
  have hj : b (e j) = a := (hea _).2 ⟨j, rfl⟩
  rw [← Finset.sum_image (f := fun k => X (e i) k * Y k (e j)) (fun x _ y _ h => he h)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
  have hka : b k ≠ a := fun h => by
    obtain ⟨c, rfl⟩ := (hea k).1 h
    exact hk (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  rcases hka.lt_or_gt with h | h
  · rw [hX (hi ▸ h), zero_mul]
  · rw [hY (hj ▸ h), mul_zero]

open Polynomial in
/-- Interpolation: a polynomial takes prescribed values on a finite set of nodes. -/
private theorem exists_forall_eval_eq (s : Finset ℂ) (v : ℂ → ℂ) :
    ∃ p : ℂ[X], ∀ z ∈ s, p.eval z = v z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨p, hp⟩ := ih
    set w : ℂ[X] := ∏ z ∈ s, (X - C z)
    have hw : w.eval a ≠ 0 := by
      rw [eval_prod, Finset.prod_ne_zero_iff]
      intro z hz
      rw [eval_sub, eval_X, eval_C, sub_ne_zero]
      rintro rfl
      exact ha hz
    refine ⟨p + C ((v a - p.eval a) / w.eval a) * w, fun z hz => ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simp only [eval_add, eval_mul, eval_C]
      field_simp
      ring
    · have : w.eval z = 0 := by
        rw [eval_prod]
        exact Finset.prod_eq_zero hz (by simp)
      simp [this, hp z hz]

open Polynomial in
/-- A polynomial with real values on the entries of `d`, inverted on them by a second one. -/
private theorem exists_eval_comp_eq {ι : Type*} [Finite ι] (d : ι → ℂ) :
    ∃ p q : ℂ[X], (∀ i, star (p.eval (d i)) = p.eval (d i)) ∧ ∀ i, q.eval (p.eval (d i)) = d i := by
  classical
  have := Fintype.ofFinite ι
  set T := Finset.univ.image d
  let g : ℂ → ℂ := fun z => if h : z ∈ T then ((T.equivFin ⟨z, h⟩ : ℕ) : ℂ) else 0
  have hT : ∀ i, d i ∈ T := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hg : ∀ i j, g (d i) = g (d j) → d i = d j := fun i j h => by
    simp only [g, dif_pos (hT i), dif_pos (hT j), Nat.cast_inj, Fin.val_inj] at h
    exact congrArg Subtype.val (T.equivFin.injective h)
  obtain ⟨p, hp⟩ := exists_forall_eval_eq T g
  obtain ⟨q, hq⟩ := exists_forall_eval_eq (T.image g) fun w =>
    if h : ∃ i, g (d i) = w then d h.choose else 0
  refine ⟨p, q, fun i => ?_, fun i => ?_⟩
  · rw [hp _ (hT i)]
    simp only [g, dif_pos (hT i)]
    exact Complex.conj_natCast _
  · have h : ∃ j, g (d j) = g (d i) := ⟨i, rfl⟩
    rw [hp _ (hT i), hq _ (Finset.mem_image_of_mem _ (hT i)), dif_pos h]
    exact hg _ _ h.choose_spec

open Polynomial in
/-- A polynomial of a diagonal matrix is diagonal. -/
private theorem aeval_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (p : ℂ[X]) :
    aeval (Matrix.diagonal d) p = Matrix.diagonal fun i => p.eval (d i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, eval_add, Matrix.diagonal_add]
  | monomial k a =>
    simp [aeval_monomial, Matrix.diagonal_pow, Matrix.algebraMap_eq_diagonal]

open Polynomial in
/-- A polynomial commutes with a unitary similarity. -/
private theorem aeval_mul_mul_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Matrix ι ι ℂ} (hW : HasOrthonormalCols W) (A : Matrix ι ι ℂ) (p : ℂ[X]) :
    aeval (W * A * Wᴴ) p = W * aeval A p * Wᴴ := by
  have hpow : ∀ k : ℕ, (W * A * Wᴴ) ^ k = W * A ^ k * Wᴴ := fun k => by
    induction k with
    | zero => simp [hW.mul_conjTranspose_self]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Wᴴ W, hW.conjTranspose_mul_self, Matrix.one_mul]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, hpow, ← Algebra.smul_def, ← Algebra.smul_def,
      Matrix.mul_smul, Matrix.smul_mul]

open Polynomial in
/-- On the indices of one label, a polynomial of a block triangular matrix has as diagonal block
the polynomial of the diagonal block. -/
private theorem submatrix_aeval_of_blockTriangular {m ι : Type*} [Fintype m] [Fintype ι]
    [DecidableEq m] [DecidableEq ι] {b : m → ℕ} {X : Matrix m m ℂ} (hX : X.BlockTriangular b)
    {e : ι → m} (he : Function.Injective e) {a : ℕ} (hea : ∀ k, b k = a ↔ k ∈ Set.range e)
    (p : ℂ[X]) : (aeval X p).submatrix e e = aeval (X.submatrix e e) p := by
  have hpow : ∀ k : ℕ, (X ^ k).submatrix e e = X.submatrix e e ^ k := fun k => by
    induction k with
    | zero => simp [Matrix.submatrix_one _ he]
    | succ k ih =>
      rw [pow_succ, submatrix_mul_of_blockTriangular (hX.pow k) hX he hea, ih, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, ← hp, ← hq]; rfl
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, ← hpow]; rfl

open scoped ComplexOrder in
/-- The Cholesky factor of $\mathbf{V}^{-\mathsf H}\mathbf{V}^{-1}$: an invertible $\mathbf{V}$
is $\mathbf{R}^{-1}\mathbf{W}$ with $\mathbf{R}$ upper triangular and $\mathbf{W}$ unitary. -/
private theorem exists_upperTriangular_mul_hasOrthonormalCols
    {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hV : IsUnit V) :
    ∃ R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, (∀ i j, j < i → R i j = 0) ∧
      HasOrthonormalCols (R * V) := by
  have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hG : ((V⁻¹)ᴴ * V⁻¹).PosDef := Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_nonsing_inv_iff.mpr hV))
  have hL := hG.isCholesky_choleskyLower
  refine ⟨(choleskyLower ((V⁻¹)ᴴ * V⁻¹))ᴴ, fun i j hij => ?_, ?_⟩
  · rw [Matrix.conjTranspose_apply, hL.isLowerTriangular hij, star_zero]
  · rw [hasOrthonormalCols_iff]
    calc _ = Vᴴ * (choleskyLower ((V⁻¹)ᴴ * V⁻¹) * (choleskyLower ((V⁻¹)ᴴ * V⁻¹))ᴴ) * V := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
      _ = (V⁻¹ * V)ᴴ * (V⁻¹ * V) := by
          rw [← hL.eq_mul_conjTranspose]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.conjTranspose_one, Matrix.mul_one]

/-- **The condition of the diagonal blocks of a block triangular matrix**: let $\mathbf{M}$ be
block upper triangular for a partition `rs` of the indices into ranges, with
$\mathbf{M}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ and $\mathbf{V}$ invertible.
Then the diagonal block of every range has an invertible eigenvector matrix $\mathbf{V}_r$ with
$\|\mathbf{V}_r\|_2\|\mathbf{V}_r^{-1}\|_2 \le \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$; no
hypothesis on the eigenvalues. [BanksGarzaVargasSrivastava2022, Lemma 6.2], whose proof has gap
G15; the proof here: Cholesky $\mathbf{V}^{-\mathsf H}\mathbf{V}^{-1} = \mathbf{R}^{\mathsf H}
\mathbf{R}$, $\mathbf{W} = \mathbf{R}\mathbf{V}$ unitary, $\mathbf{N} = \mathbf{R}\mathbf{M}
\mathbf{R}^{-1}$ normal and block triangular, hence block diagonal
(`IsStarNormal.apply_eq_zero_of_blockTriangular`); $\mathbf{N}_{rr} = \mathbf{U}_r\mathbf{D}_r
\mathbf{U}_r^{\mathsf H}$ and $\mathbf{V}_r = \mathbf{R}_{rr}^{-1}\mathbf{U}_r$ with
$\kappa(\mathbf{V}_r) = \kappa(\mathbf{R}_{rr}) \le \kappa(\mathbf{R}) = \kappa(\mathbf{V})$. -/
theorem _root_.Matrix.BlockTriangular.exists_pseudoConditionNumber_subBlock_le
    {M V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {rs : List (ℕ × ℕ)}
    (hM : M.BlockTriangular (rangeLabel rs)) (hrs : IsRangePartition (n + 1) rs)
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hMV : M * V = V * Matrix.diagonal d)
    {r : ℕ × ℕ} (hr : r ∈ rs) :
    ∃ (Vr : Matrix (Fin r.2) (Fin r.2) ℂ) (dr : Fin r.2 → ℂ), IsUnit Vr ∧
      subBlock M r * Vr = Vr * Matrix.diagonal dr ∧
      pseudoConditionNumber Vr ≤ pseudoConditionNumber V := by
  obtain ⟨R, hRu, hW⟩ := exists_upperTriangular_mul_hasOrthonormalCols hV
  set W := R * V
  have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hW₁ : Wᴴ * W = 1 := hasOrthonormalCols_iff.mp hW
  have hW₂ : W * Wᴴ = 1 := mul_eq_one_comm.mp hW₁
  have hRW : W * V⁻¹ = R := by rw [Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  have hRinv : R * (V * Wᴴ) = 1 := by rw [← Matrix.mul_assoc, hW₂]
  have hRi : R⁻¹ = V * Wᴴ := Matrix.inv_eq_right_inv hRinv
  have hRdet : IsUnit R.det := Matrix.isUnit_det_of_right_inverse hRinv
  have : Invertible R := Matrix.invertibleOfIsUnitDet R hRdet
  -- `N = R M R⁻¹ = W D Wᴴ` is block triangular
  have hN : R * M * R⁻¹ = W * Matrix.diagonal d * Wᴴ := by
    rw [hRi, ← hRW, Matrix.mul_assoc (W * V⁻¹) M, ← Matrix.mul_assoc M V, hMV,
      Matrix.mul_assoc V, Matrix.mul_assoc W V⁻¹, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]
    exact (Matrix.mul_assoc _ _ _).symm
  have hRb : R.BlockTriangular (rangeLabel rs) := fun i j hij =>
    hRu i j (lt_of_not_ge fun h => hij.not_ge (rangeLabel_le_of_le hrs h))
  have hRib := Matrix.blockTriangular_inv_of_blockTriangular hRb
  have hNb := (hRb.mul hM).mul hRib
  have he := blockIndex_injective hrs hr
  have hea := rangeLabel_eq_iff_mem_range hrs hr
  set e := blockIndex n r
  -- a Hermitian polynomial `p(N)` of which `N` is a polynomial `q`
  obtain ⟨p, q, hp, hq⟩ := exists_eval_comp_eq d
  have hK : (Polynomial.aeval (R * M * R⁻¹) p).IsHermitian := by
    rw [hN, aeval_mul_mul_conjTranspose hW, aeval_diagonal]
    exact Matrix.isHermitian_mul_mul_conjTranspose _
      (Matrix.isHermitian_diagonal_of_self_adjoint _ (funext hp))
  set Nr := (R * M * R⁻¹).submatrix e e
  have hKr : (Polynomial.aeval Nr p).IsHermitian := by
    rw [← submatrix_aeval_of_blockTriangular hNb he hea]
    exact hK.submatrix e
  have hNr : Nr = Polynomial.aeval (Polynomial.aeval Nr p) q := by
    rw [← Polynomial.aeval_comp, ← submatrix_aeval_of_blockTriangular hNb he hea, hN,
      aeval_mul_mul_conjTranspose hW, aeval_diagonal]
    simp only [Polynomial.eval_comp, hq]
    exact congrArg (fun X => X.submatrix e e) hN
  obtain ⟨U, hU₁, l, hl⟩ : ∃ U : Matrix (Fin r.2) (Fin r.2) ℂ, Uᴴ * U = 1 ∧
      ∃ l : Fin r.2 → ℂ, Polynomial.aeval Nr p = U * Matrix.diagonal l * Uᴴ := by
    refine ⟨hKr.eigenvectorUnitary, Unitary.star_mul_self_of_mem hKr.eigenvectorUnitary.2,
      RCLike.ofReal ∘ hKr.eigenvalues, ?_⟩
    conv_lhs => rw [hKr.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hU₂ : U * Uᴴ = 1 := mul_eq_one_comm.mp hU₁
  have hNU : Nr = U * Matrix.diagonal (fun i => q.eval (l i)) * Uᴴ := by
    rw [hNr, hl, aeval_mul_mul_conjTranspose hU₁, aeval_diagonal]
  -- the blocks of `R` and `R⁻¹` on the range `r`
  have hRr : R⁻¹.submatrix e e * R.submatrix e e = 1 := by
    rw [← submatrix_mul_of_blockTriangular hRib hRb he hea, Matrix.nonsing_inv_mul _ hRdet,
      Matrix.submatrix_one _ he]
  have hRr' := mul_eq_one_comm.mp hRr
  have hMr : Nr = R.submatrix e e * subBlock M r * R⁻¹.submatrix e e := by
    rw [show Nr = (R * M * R⁻¹).submatrix e e from rfl,
      submatrix_mul_of_blockTriangular (hRb.mul hM) hRib he hea,
      submatrix_mul_of_blockTriangular hRb hM he hea]
    rfl
  set Rr := R.submatrix e e
  set Rir := R⁻¹.submatrix e e
  have h₁ : ∀ X, Rr * (Rir * X) = X := fun X => by rw [← Matrix.mul_assoc, hRr', Matrix.one_mul]
  have h₀ : ∀ X, Rir * (Rr * X) = X := fun X => by rw [← Matrix.mul_assoc, hRr, Matrix.one_mul]
  have hVr : Uᴴ * Rr * (Rir * U) = 1 := by rw [Matrix.mul_assoc, h₁, hU₁]
  have hVu : IsUnit (Rir * U) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hVr)
  have hUh : HasOrthonormalCols Uᴴ := by
    rw [hasOrthonormalCols_iff, Matrix.conjTranspose_conjTranspose, hU₂]
  refine ⟨Rir * U, fun i => q.eval (l i), hVu, ?_, ?_⟩
  · have hM' : subBlock M r = Rir * Nr * Rr := by
      simp only [hMr, Matrix.mul_assoc, hRr, Matrix.mul_one, h₀]
    rw [hM', hNU]
    simp only [Matrix.mul_assoc, h₁, hU₁, Matrix.mul_one]
  · rw [pseudoConditionNumber_of_isUnit hVu, pseudoConditionNumber_of_isUnit hV,
      Matrix.inv_eq_left_inv hVr, hUh.specNorm_mul_left,
      ← Matrix.conjTranspose_conjTranspose U, hUh.specNorm_mul_conjTranspose_right]
    have hRn : specNorm R = specNorm V⁻¹ := by rw [← hRW, hW.specNorm_mul_left]
    have hRin : specNorm R⁻¹ = specNorm V := by rw [hRi, hW.specNorm_mul_conjTranspose_right]
    exact mul_le_mul (hRin ▸ specNorm_submatrix_le _ he he)
      (hRn ▸ specNorm_submatrix_le _ he he) (specNorm_nonneg _) (specNorm_nonneg _)

/-- The arithmetic of the eigenvector bound: if $x(g - r - s) \le s$ with
$s \le g/(16N)$, $r \le g/16$, $N \ge 1$ and $x \ge 0$, then $x \le 1/(14N)$. -/
private theorem le_one_div_of_mul_sub_le {x s r g N : ℝ} (hx : 0 ≤ x) (hg : 0 < g)
    (hN : 1 ≤ N) (hs : s ≤ g / (16 * N)) (hr : r ≤ g / 16) (h : x * (g - r - s) ≤ s) :
    x ≤ 1 / (14 * N) := by
  have hs' : s * (16 * N) ≤ g := by rwa [le_div_iff₀ (by positivity)] at hs
  have h16 : 16 * s ≤ g := by nlinarith
  have h1 : x * (7 * g) ≤ 8 * s := by nlinarith [mul_le_mul_of_nonneg_left hr hx]
  have h2 : x * (14 * N) * g ≤ 1 * g := by
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 2 * N)]
  rw [le_div_iff₀ (by positivity), mul_comm]
  linarith [le_of_mul_le_mul_right h2 hg]

/-- The similar perturbation is small: $\|\mathbf{V}^{-1}\mathbf{E}\mathbf{V}\|_2 \le
\kappa(\mathbf{V})\|\mathbf{E}\|_2 \le g/(16(n + 1))$ when $\kappa(\mathbf{V}) \le B$,
$B \ge 1$ and $\|\mathbf{E}\|_2 \le g/(16(n + 1)B)$. -/
private theorem specNorm_inv_mul_mul_le {V E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hV : IsUnit V) {B g : ℝ} (hB : pseudoConditionNumber V ≤ B) (hB1 : 1 ≤ B)
    (hE : specNorm E ≤ g / (16 * (n + 1) * B)) :
    specNorm (V⁻¹ * E * V) ≤ g / (16 * (n + 1)) := by
  have h1 : specNorm (V⁻¹ * E * V) ≤ pseudoConditionNumber V * specNorm E := by
    rw [pseudoConditionNumber_of_isUnit hV]
    calc specNorm (V⁻¹ * E * V) ≤ specNorm V⁻¹ * specNorm E * specNorm V :=
          (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _)
            (specNorm_nonneg _))
      _ = specNorm V * specNorm V⁻¹ * specNorm E := by ring
  calc specNorm (V⁻¹ * E * V) ≤ B * (g / (16 * (n + 1) * B)) :=
        h1.trans (mul_le_mul hB hE (specNorm_nonneg _) (by linarith))
    _ = g / (16 * (n + 1)) := by field_simp

/-- A matrix $\mathbf{Z}$ whose columns have norm at most $1/(14(n + 1))$ has
$\|\mathbf{Z}\|_2 \le 1/14$. -/
private theorem specNorm_le_one_div_fourteen {Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h : ∀ i, ‖WithLp.toLp 2 (Z.col i)‖ ≤ 1 / (14 * (n + 1))) : specNorm Z ≤ 1 / 14 := by
  refine (specNorm_le_frobNorm Z).trans
    ((frobNorm_le_sqrt_card_mul_of_forall_norm_toLp_col_le h).trans ?_)
  rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  have hN : (0 : ℝ) ≤ n := n.cast_nonneg
  have hs : √((n : ℝ) + 1) ≤ n + 1 := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  calc √((n : ℝ) + 1) * (1 / (14 * (n + 1))) ≤ (n + 1) * (1 / (14 * (n + 1))) := by gcongr
    _ = 1 / 14 := by field_simp

/-- **The condition under a small perturbation**: let $\mathbf{A}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$, and eigenvalues separated by $g > 0$:
$\lvert\mathbf{d}_i - \mathbf{d}_j\rvert \ge g$ for $i \ne j$. If $\|\mathbf{E}\|_2 \le
g/(16(n + 1)B)$, then $\mathbf{A} + \mathbf{E}$ has distinct eigenvalues and an invertible
eigenvector matrix $\mathbf{V}'$ with $\|\mathbf{V}'\|_2\|\mathbf{V}'^{-1}\|_2 \le 2B$.
[BanksGarzaVargasSrivastava2022, Lemma 6.1]; the eigenvectors of
$\operatorname{diag}(\mathbf{d}) + \mathbf{V}^{-1}\mathbf{E}\mathbf{V}$ by Gershgorin's theorem
with counting. -/
theorem exists_pseudoConditionNumber_add_le {A V E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d) {B g : ℝ}
    (hB : pseudoConditionNumber V ≤ B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖) (hE : specNorm E ≤ g / (16 * (n + 1) * B)) :
    ∃ (V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d' : Fin (n + 1) → ℂ), IsUnit V' ∧
      (A + E) * V' = V' * Matrix.diagonal d' ∧ Function.Injective d' ∧
      pseudoConditionNumber V' ≤ 2 * B := by
  have hN : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hB
  set F := V⁻¹ * E * V with hFdef
  have hF := specNorm_inv_mul_mul_le hV hB hB1 hE
  have hr : (Fintype.card (Fin (n + 1)) : ℝ) * specNorm F ≤ g / 16 := by
    rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    calc ((n : ℝ) + 1) * specNorm F ≤ (n + 1) * (g / (16 * (n + 1))) := by gcongr
      _ = g / 16 := by field_simp
  choose μ z hzi hμ hz hzn using fun i =>
    exists_mulVec_single_add_eq_smul_of_two_mul_card_mul_specNorm_lt (F := F)
      (fun j hj => hgap i j (Ne.symm hj)) (by linarith : 2 * _ < g)
  set Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun j i => z i j with hZdef
  have hcol : ∀ i, (1 + Z).col i = Pi.single i 1 + z i := fun i => by
    ext j
    simp [Z, Matrix.one_apply, Pi.single_apply]
  have hW : (Matrix.diagonal d + F) * (1 + Z) = (1 + Z) * Matrix.diagonal μ :=
    mul_eq_mul_diagonal_iff.mpr fun i => by rw [hcol]; exact hz i
  have hZ : specNorm Z ≤ 1 / 14 := specNorm_le_one_div_fourteen fun i =>
    le_one_div_of_mul_sub_le (norm_nonneg _) hg hN hF hr (hzn i)
  have hZ1 : specNorm Z < 1 := by linarith
  have hU := isUnit_one_add_of_specNorm_lt_one hZ1
  have hκ : pseudoConditionNumber (1 + Z) ≤ 2 :=
    (pseudoConditionNumber_one_add_le hZ1).trans (by rw [div_le_iff₀ (by linarith)]; linarith)
  have hAE : (A + E) * V = V * (Matrix.diagonal d + F) := by
    rw [Matrix.add_mul, hAV, Matrix.mul_add, hFdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det V).mp hV), Matrix.one_mul]
  refine ⟨V * (1 + Z), μ, hV.mul hU, ?_, fun i j hij => ?_, ?_⟩
  · rw [← Matrix.mul_assoc, hAE, Matrix.mul_assoc, hW, Matrix.mul_assoc]
  · by_contra hne
    have h3 : ‖d i - d j‖ ≤ ‖μ j - d j‖ + ‖μ i - d i‖ := by
      calc ‖d i - d j‖ = ‖(μ j - d j) - (μ i - d i)‖ := by rw [hij]; ring_nf
        _ ≤ ‖μ j - d j‖ + ‖μ i - d i‖ := norm_sub_le _ _
    linarith [hgap i j hne, hμ i, hμ j]
  · calc pseudoConditionNumber (V * (1 + Z))
        ≤ pseudoConditionNumber V * pseudoConditionNumber (1 + Z) :=
          pseudoConditionNumber_mul_le hV hU
      _ ≤ B * 2 := mul_le_mul hB hκ (pseudoConditionNumber_nonneg _) (by linarith)
      _ = 2 * B := mul_comm _ _

/-- **The condition of every active block of deflation**: under the invariant
`NLAlib.DeflationInv` with perturbation bound $\varepsilon$, if
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$, eigenvalues separated by $g > 0$ and
$\varepsilon \le g/(16(n + 1)B)$, then every active block of $\mathbf{A}$ has an invertible
eigenvector matrix with $\|\mathbf{V}_r\|_2\|\mathbf{V}_r^{-1}\|_2 \le 2B$: the hypothesis of the
convergence theorem holds on every block the algorithm iterates on.
[BanksGarzaVargasSrivastava2022, §6], proof of Theorem 6.3, in exact arithmetic. -/
theorem DeflationInv.exists_pseudoConditionNumber_subBlock_le
    {H A V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ} {active done : List (ℕ × ℕ)}
    {out : Fin (n + 1) → ℂ} (h : DeflationInv H ε active done A out) {d : Fin (n + 1) → ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {B g : ℝ}
    (hB : pseudoConditionNumber V ≤ B) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hε : ε ≤ g / (16 * (n + 1) * B)) {r : ℕ × ℕ} (hr : r ∈ active) :
    ∃ (Vr : Matrix (Fin r.2) (Fin r.2) ℂ) (dr : Fin r.2 → ℂ), IsUnit Vr ∧
      subBlock A r * Vr = Vr * Matrix.diagonal dr ∧ pseudoConditionNumber Vr ≤ 2 * B := by
  obtain ⟨M, U, E, hUU, hE, rfl, hpart, hbt, hact, -⟩ := h
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hUU
  obtain ⟨V', d', hV', hV'd, -, hκ⟩ := exists_pseudoConditionNumber_add_le hV hHV hB hg hgap
    (hE.trans hε)
  have hQ : HasOrthonormalCols Uᴴ := by
    rw [HasOrthonormalCols, Matrix.conjTranspose_conjTranspose, hUU']
  have hUu : IsUnit Uᴴ := ⟨⟨Uᴴ, U, hUU, hUU'⟩, rfl⟩
  obtain ⟨Vr, dr, hVr, hMr, hκr⟩ := Matrix.BlockTriangular.exists_pseudoConditionNumber_subBlock_le
    hbt hpart (V := Uᴴ * V') (d := d') (hUu.mul hV')
    (by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU', Matrix.one_mul,
      Matrix.mul_assoc Uᴴ, hV'd, ← Matrix.mul_assoc]) (List.mem_append_left _ hr)
  rw [← (hact r hr).1]
  refine ⟨Vr, dr, hVr, hMr, hκr.trans ?_⟩
  rw [hQ.pseudoConditionNumber_mul_left]
  exact hκ

end NLAlib
