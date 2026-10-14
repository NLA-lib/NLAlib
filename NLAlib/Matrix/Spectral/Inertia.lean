/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Interlacing
public import NLAlib.Matrix.Spectral.SingularValues
public import NLAlib.Matrix.Spectral.Weyl

/-!
# Inertia of Hermitian matrices

The inertia of a Hermitian matrix is the triple of the numbers of its positive, negative and zero
eigenvalues. `NLAlib.inertiaPos A` and `NLAlib.inertiaNeg A` count the positive and negative
`eigenvalue A i`. The positive index is the largest dimension of a subspace on which the form is
positive definite, Sylvester's law says congruence preserves both indices, and Ostrowski's theorem
quantifies how far congruence moves each eigenvalue. Block matrices, Schur complements and the
count of eigenvalues by the pivots of elimination are in
`NLAlib.Matrix.Spectral.InertiaElimination`.

## Main definitions

* `NLAlib.inertiaPos`, `NLAlib.inertiaNeg`.

## Main results

* `Matrix.IsHermitian.le_inertiaPos_iff_exists_posDef`: the variational characterisation.
* `Matrix.IsHermitian.inertiaPos_conjTranspose_mul_mul`,
  `Matrix.IsHermitian.inertiaNeg_conjTranspose_mul_mul`: Sylvester's law of inertia.
* `Matrix.IsHermitian.exists_eigenvalue_conjTranspose_mul_mul_eq_mul`: Ostrowski's theorem.
* `Matrix.IsHermitian.eigenvalue_add_le_of_inertiaPos`: the inertia form of low-rank interlacing.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The **positive index of inertia**: the number of positive eigenvalues.
[HornJohnson2013, Definition 4.5.6]. Port of `NLAlib.inertiaPos`, there over `ℝ` through the
signature of the quadratic form. For a matrix that is not Hermitian the value is `0`, since
`eigenvalue` is then zero. -/
noncomputable def inertiaPos (A : Matrix n n 𝕜) : ℕ :=
  ((Finset.range (Fintype.card n)).filter fun i => 0 < eigenvalue A i).card

/-- The **negative index of inertia**: the number of negative eigenvalues; `0` for a matrix that
is not Hermitian. Port of `NLAlib.inertiaNeg`. -/
noncomputable def inertiaNeg (A : Matrix n n 𝕜) : ℕ :=
  ((Finset.range (Fintype.card n)).filter fun i => eigenvalue A i < 0).card

/-- Counting an initial segment: for a predicate that is downward closed below `N`, the number of
`i < N` satisfying it exceeds `k` exactly when `k < N` satisfies it. -/
private theorem lt_card_filter_range_iff {N : ℕ} {p : ℕ → Prop} [DecidablePred p]
    (hp : ∀ i j, i ≤ j → j < N → p j → p i) {k : ℕ} :
    k < ((Finset.range N).filter p).card ↔ k < N ∧ p k := by
  constructor
  · intro h
    by_contra hk
    have hsub : (Finset.range N).filter p ⊆ Finset.range k := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      rw [Finset.mem_range]
      by_contra hik
      exact hk ⟨lt_of_le_of_lt (not_lt.mp hik) hi.1, hp k i (not_lt.mp hik) hi.1 hi.2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega
  · rintro ⟨hkN, hpk⟩
    have hsub : Finset.range (k + 1) ⊆ (Finset.range N).filter p := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp i k (by omega) hkN hpk⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega

/-- The positive index exceeds `k` exactly when `k` is a valid index and the `k`-th eigenvalue
is positive. This is how a statement about `inertiaPos` is turned into one about
`eigenvalue`. -/
theorem _root_.Matrix.IsHermitian.lt_inertiaPos_iff {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : ℕ} : k < inertiaPos A ↔ k < Fintype.card n ∧ 0 < eigenvalue A k :=
  lt_card_filter_range_iff fun _ _ hij hj h => h.trans_le (hA.eigenvalue_le_eigenvalue hij hj)

/-- A count of eigenvalues is a count of the entries of any relabelling of them. -/
private theorem card_filter_range_eigenvalue {r : Type*} [Fintype r] {A : Matrix n n 𝕜}
    {d : r → ℝ} (e : r ≃ Fin (Fintype.card n)) (he : ∀ i, d i = eigenvalue A (e i))
    (P : ℝ → Prop) [DecidablePred P] :
    ((Finset.range (Fintype.card n)).filter fun i => P (eigenvalue A i)).card =
      (Finset.univ.filter fun i => P (d i)).card := by
  symm
  refine Finset.card_bij (fun i _ => (e i : ℕ)) (fun i hi => ?_) (fun i _ j _ hij => ?_)
    fun b hb => ?_
  · rw [Finset.mem_filter] at hi
    rw [Finset.mem_filter, Finset.mem_range, ← he]
    exact ⟨(e i).isLt, hi.2⟩
  · exact e.injective (Fin.ext hij)
  · rw [Finset.mem_filter, Finset.mem_range] at hb
    refine ⟨e.symm ⟨b, hb.1⟩, ?_, by rw [Equiv.apply_symm_apply]⟩
    rw [Finset.mem_filter, he, Equiv.apply_symm_apply]
    exact ⟨Finset.mem_univ _, hb.2⟩

/-- The positive and negative indices of a Hermitian matrix add up to its rank.
Port of `NLAlib.inertiaPos_add_inertiaNeg_eq_rank`. -/
theorem _root_.Matrix.IsHermitian.inertiaPos_add_inertiaNeg {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : inertiaPos A + inertiaNeg A = A.rank := by
  rw [hA.rank_eq_card_eigenvalue_ne_zero, inertiaPos, inertiaNeg,
    ← Finset.card_union_of_disjoint, ← Finset.filter_or]
  · exact congrArg Finset.card (Finset.filter_congr fun i _ => by
      rw [ne_comm, ne_iff_lt_or_gt])
  · exact Finset.disjoint_filter.mpr fun i _ h1 h2 => lt_asymm h1 h2

/-- The eigenvalues of a real diagonal matrix are its diagonal entries in some order. -/
private theorem exists_equiv_eq_eigenvalue_diagonal [DecidableEq n] (d : n → ℝ) :
    ∃ e : n ≃ Fin (Fintype.card n),
      ∀ i, d i = eigenvalue (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) (e i) :=
  exists_equiv_eq_eigenvalue_of_eq_mul_diagonal_mul_conjTranspose
    (U := (1 : Matrix n n 𝕜)) hasOrthonormalCols_one rfl
    (by rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one])

/-- The positive index of a real diagonal matrix. Port of `NLAlib.inertiaPos_diagonal`. -/
theorem inertiaPos_diagonal [DecidableEq n] (d : n → ℝ) :
    inertiaPos (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) =
      (Finset.univ.filter fun i => 0 < d i).card := by
  obtain ⟨e, he⟩ := exists_equiv_eq_eigenvalue_diagonal (𝕜 := 𝕜) d
  exact card_filter_range_eigenvalue e he fun x => 0 < x

/-- The negative index of a real diagonal matrix. Port of `NLAlib.inertiaNeg_diagonal`. -/
theorem inertiaNeg_diagonal [DecidableEq n] (d : n → ℝ) :
    inertiaNeg (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) =
      (Finset.univ.filter fun i => d i < 0).card := by
  obtain ⟨e, he⟩ := exists_equiv_eq_eigenvalue_diagonal (𝕜 := 𝕜) d
  exact card_filter_range_eigenvalue e he fun x => x < 0

/-- The negative index of `A` is the positive index of `-A`. -/
theorem inertiaNeg_eq_inertiaPos_neg (A : Matrix n n 𝕜) : inertiaNeg A = inertiaPos (-A) := by
  have key : ∀ i ∈ Finset.range (Fintype.card n),
      eigenvalue (-A) (Fintype.card n - 1 - i) = -eigenvalue A i := fun i hi =>
    eigenvalue_neg A (by have := Finset.mem_range.mp hi; omega)
  have key' : ∀ i ∈ Finset.range (Fintype.card n),
      eigenvalue (-A) i = -eigenvalue A (Fintype.card n - 1 - i) := fun i hi =>
    eigenvalue_neg A (by have := Finset.mem_range.mp hi; omega)
  refine Finset.card_bij' (fun i _ => Fintype.card n - 1 - i) (fun i _ => Fintype.card n - 1 - i)
    (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) fun i hi => ?_
  · rw [Finset.mem_filter] at hi ⊢
    rw [key i hi.1]
    exact ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hi.1; omega),
      neg_pos.mpr hi.2⟩
  · rw [Finset.mem_filter] at hi ⊢
    rw [key' i hi.1] at hi
    exact ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hi.1; omega),
      neg_pos.mp hi.2⟩
  · have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    omega
  · have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    omega

/-- A Hermitian matrix is positive definite exactly when its positive index is its size. -/
theorem _root_.Matrix.IsHermitian.posDef_iff_inertiaPos_eq_card {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A.PosDef ↔ inertiaPos A = Fintype.card n := by
  rw [hA.posDef_iff_eigenvalue_pos, inertiaPos]
  conv_rhs => rhs; rw [← Finset.card_range (Fintype.card n)]
  rw [Finset.card_filter_eq_iff]
  simp only [Finset.mem_range]

/-- A Hermitian matrix is positive semidefinite exactly when its negative index vanishes. -/
theorem _root_.Matrix.IsHermitian.posSemidef_iff_inertiaNeg_eq_zero {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A.PosSemidef ↔ inertiaNeg A = 0 := by
  rw [hA.posSemidef_iff_eigenvalue_nonneg, inertiaNeg, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  refine ⟨fun h i _ => not_lt.mpr (h i), fun h k => ?_⟩
  by_cases hk : k < Fintype.card n
  · exact not_lt.mp (h (Finset.mem_range.mpr hk))
  · exact (eigenvalue_of_card_le A (not_lt.mp hk)).ge

/-! ### The variational characterisation -/

/-- A strict Courant–Fischer bound on a subspace: if the form of `A` exceeds `c` on the nonzero
vectors of a subspace of dimension at least `k + 1`, then `k` is a valid index and
`c < λ_k(A)`. -/
private theorem lt_eigenvalue_of_forall_mem {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    (S : Submodule 𝕜 (n → 𝕜)) (hS : k + 1 ≤ Module.finrank 𝕜 S) {c : ℝ}
    (h : ∀ x ∈ S, x ≠ 0 → c * ‖WithLp.toLp 2 x‖ ^ 2 < RCLike.re (quadForm A x)) :
    k < Fintype.card n ∧ c < eigenvalue A k := by
  have hk : k < Fintype.card n := by
    have := Submodule.finrank_le S
    rw [Module.finrank_fintype_fun_eq_card] at this
    omega
  refine ⟨hk, ?_⟩
  obtain ⟨W, hW, hWle⟩ := hA.exists_submodule_le_eigenvalue_mul hk
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq S W
  have hsup := Submodule.finrank_le (S ⊔ W)
  rw [Module.finrank_fintype_fun_eq_card] at hsup
  have hpos : 0 < Module.finrank 𝕜 ↥(S ⊓ W) := by omega
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hxne : x ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
  have hn : 0 < ‖WithLp.toLp 2 x‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hxne)) 2
  exact lt_of_mul_lt_mul_right ((h x hx.1 hxne).trans_le (hWle x hx.2)) hn.le

omit [Fintype n] in
/-- The range of a matrix with injective action has the dimension of its domain. -/
private theorem finrank_range_mulVecLin_of_injective {p : Type*} [Fintype p] {W : Matrix n p 𝕜}
    (hW : Function.Injective W.mulVec) :
    Module.finrank 𝕜 (LinearMap.range W.mulVecLin) = Fintype.card p := by
  rw [LinearMap.finrank_range_of_inj (f := W.mulVecLin) hW, Module.finrank_fintype_fun_eq_card]

/-- A matrix on whose range the form of `A` is positive definite has at most `inertiaPos A`
columns. -/
private theorem card_le_inertiaPos_of_posDef {p : Type*} [Fintype p] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {W : Matrix n p 𝕜} (h : (Wᴴ * A * W).PosDef) :
    Fintype.card p ≤ inertiaPos A := by
  rcases Nat.eq_zero_or_pos (Fintype.card p) with h0 | h0
  · rw [h0]
    exact Nat.zero_le _
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0.ne'
  have hpos : ∀ y : p → 𝕜, y ≠ 0 → 0 < RCLike.re (quadForm A (W *ᵥ y)) := fun y hy => by
    rw [← quadForm_conjTranspose_mul_mul]
    exact h.re_quadForm_pos hy
  have hinj : Function.Injective W.mulVec := by
    refine (injective_iff_map_eq_zero W.mulVecLin).mpr fun y hy => ?_
    by_contra hy0
    have := hpos y hy0
    rw [show W *ᵥ y = 0 from hy, quadForm_zero_right, map_zero] at this
    exact lt_irrefl _ this
  have hfin := finrank_range_mulVecLin_of_injective hinj
  rw [hk]
  refine hA.lt_inertiaPos_iff.mpr (lt_eigenvalue_of_forall_mem hA _ (hfin ▸ hk.ge) ?_)
  rintro x ⟨y, rfl⟩ hx
  rw [zero_mul]
  exact hpos y fun hy => hx (by rw [hy]; exact map_zero _)

/-- **The positive index is the largest dimension of a subspace on which the form is positive
definite.** [HornJohnson2013, Theorem 4.5.8 context]. -/
theorem _root_.Matrix.IsHermitian.le_inertiaPos_iff_exists_posDef
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ} :
    k ≤ inertiaPos A ↔
      ∃ V : Matrix n (Fin k) 𝕜, HasOrthonormalCols V ∧ (Vᴴ * A * V).PosDef := by
  classical
  constructor
  · intro hk
    have hkN : k ≤ Fintype.card n :=
      hk.trans ((Finset.card_filter_le _ _).trans_eq (Finset.card_range _))
    obtain ⟨U, hU, hAU⟩ := hA.exists_mul_eq_mul_diagonal
    refine ⟨U.submatrix id (Fin.castLE hkN),
      hU.submatrix (Equiv.refl n) (Fin.castLE_injective hkN), ?_⟩
    have h1 : (U.submatrix id (Fin.castLE hkN))ᴴ * A * U.submatrix id (Fin.castLE hkN) =
        Matrix.diagonal fun i : Fin k => ((eigenvalue A i : ℝ) : 𝕜) := by
      have h2 : A * U.submatrix id (Fin.castLE hkN) =
          (U * Matrix.diagonal fun i : Fin (Fintype.card n) =>
            ((eigenvalue A i : ℝ) : 𝕜)).submatrix id (Fin.castLE hkN) := by
        rw [← hAU]
        exact (Matrix.submatrix_mul A U id id (Fin.castLE hkN) Function.bijective_id).symm
      rw [Matrix.mul_assoc, h2, Matrix.conjTranspose_submatrix,
        ← Matrix.submatrix_mul _ _ (Fin.castLE hkN) id (Fin.castLE hkN) Function.bijective_id,
        hU.conjTranspose_mul_cancel_left,
        Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hkN)]
      rfl
    rw [h1, Matrix.posDef_diagonal_iff]
    intro i
    exact RCLike.ofReal_pos.mpr (hA.lt_inertiaPos_iff.mp (i.isLt.trans_le hk)).2
  · rintro ⟨V, -, hV⟩
    simpa only [Fintype.card_fin] using card_le_inertiaPos_of_posDef hA hV

/-! ### Sylvester's law -/

/-- A congruence by any matrix does not increase the positive index.
Port of `NLAlib.card_eigenvalues₀_pos_congruence_le`. -/
theorem _root_.Matrix.IsHermitian.inertiaPos_conjTranspose_mul_mul_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (S : Matrix n m 𝕜) : inertiaPos (Sᴴ * A * S) ≤ inertiaPos A := by
  obtain ⟨V, -, hV⟩ :=
    (Matrix.isHermitian_conjTranspose_mul_mul S hA).le_inertiaPos_iff_exists_posDef.mp le_rfl
  have h : ((S * V)ᴴ * A * (S * V)).PosDef := by
    rw [Matrix.conjTranspose_mul]
    simpa only [Matrix.mul_assoc] using hV
  simpa only [Fintype.card_fin] using card_le_inertiaPos_of_posDef hA h

/-- A congruence by any matrix does not increase the negative index.
Port of `NLAlib.card_eigenvalues₀_neg_congruence_le`. -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_conjTranspose_mul_mul_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (S : Matrix n m 𝕜) : inertiaNeg (Sᴴ * A * S) ≤ inertiaNeg A := by
  rw [inertiaNeg_eq_inertiaPos_neg, inertiaNeg_eq_inertiaPos_neg A, ← Matrix.neg_mul,
    ← Matrix.mul_neg]
  exact hA.neg.inertiaPos_conjTranspose_mul_mul_le S

/-- **Sylvester's law of inertia**, positive index: congruence by an invertible matrix preserves
the number of positive eigenvalues. [HornJohnson2013, Theorem 4.5.8].
Port of `NLAlib.inertiaPos_transpose_mul_mul`, there over `ℝ`.
Result: sylvester-inertia -/
theorem _root_.Matrix.IsHermitian.inertiaPos_conjTranspose_mul_mul [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {S : Matrix n n 𝕜} (hS : IsUnit S.det) : inertiaPos (Sᴴ * A * S) = inertiaPos A := by
  refine le_antisymm (hA.inertiaPos_conjTranspose_mul_mul_le S) ?_
  have h := (Matrix.isHermitian_conjTranspose_mul_mul S hA).inertiaPos_conjTranspose_mul_mul_le S⁻¹
  have hS' : IsUnit Sᴴ.det := by rw [Matrix.det_conjTranspose]; exact hS.star
  rwa [Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hS, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hS', Matrix.one_mul] at h

/-- **Sylvester's law of inertia**, negative index.
Port of `NLAlib.inertiaNeg_transpose_mul_mul`, there over `ℝ`.
Result: sylvester-inertia -/
theorem _root_.Matrix.IsHermitian.inertiaNeg_conjTranspose_mul_mul [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {S : Matrix n n 𝕜} (hS : IsUnit S.det) : inertiaNeg (Sᴴ * A * S) = inertiaNeg A := by
  rw [inertiaNeg_eq_inertiaPos_neg, inertiaNeg_eq_inertiaPos_neg A, ← Matrix.neg_mul,
    ← Matrix.mul_neg]
  exact hA.neg.inertiaPos_conjTranspose_mul_mul hS

/-! ### Ostrowski's theorem -/

/-- Congruence keeps a zero eigenvalue in its place: if `λ_k(B) = 0` then `λ_k(Sᴴ B S) = 0`,
for any square `S`. -/
private theorem eigenvalue_conjTranspose_mul_mul_eq_zero {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    (S : Matrix n n 𝕜) {k : ℕ} (hk : k < Fintype.card n) (h0 : eigenvalue B k = 0) :
    eigenvalue (Sᴴ * B * S) k = 0 := by
  have hM := Matrix.isHermitian_conjTranspose_mul_mul S hB
  refine le_antisymm ?_ ?_
  · by_contra hpos
    have h1 := hM.lt_inertiaPos_iff.mpr ⟨hk, not_le.mp hpos⟩
    have h2 := hB.lt_inertiaPos_iff.mp (h1.trans_le (hB.inertiaPos_conjTranspose_mul_mul_le S))
    exact h2.2.ne' h0
  · obtain ⟨j, hj⟩ : ∃ j, j + k + 1 = Fintype.card n := ⟨Fintype.card n - 1 - k, by omega⟩
    by_contra hneg
    have h3 : 0 < eigenvalue (-(Sᴴ * B * S)) j := by
      rw [eigenvalue_neg _ hj]
      exact neg_pos.mpr (not_le.mp hneg)
    have h1 := hM.neg.lt_inertiaPos_iff.mpr ⟨by omega, h3⟩
    rw [← Matrix.neg_mul, ← Matrix.mul_neg] at h1
    have h2 := hB.neg.lt_inertiaPos_iff.mp
      (h1.trans_le (hB.neg.inertiaPos_conjTranspose_mul_mul_le S))
    rw [eigenvalue_neg _ hj, h0, neg_zero] at h2
    exact lt_irrefl _ h2.2

/-- The form of `Sᴴ (A - a • 1) S + c • 1` in terms of that of `Sᴴ A S`. -/
private theorem re_quadForm_conjTranspose_mul_sub_mul_add [DecidableEq n] (A S : Matrix n n 𝕜)
    (a c : ℝ) (z : n → 𝕜) :
    RCLike.re (quadForm (Sᴴ * (A - a • (1 : Matrix n n 𝕜)) * S + c • (1 : Matrix n n 𝕜)) z) =
      RCLike.re (quadForm (Sᴴ * A * S) z) - a * ‖WithLp.toLp 2 (S *ᵥ z)‖ ^ 2 +
        c * ‖WithLp.toLp 2 z‖ ^ 2 := by
  rw [quadForm_add_left, map_add, re_quadForm_real_smul_one, quadForm_conjTranspose_mul_mul,
    quadForm_sub_left, map_sub, re_quadForm_real_smul_one, quadForm_conjTranspose_mul_mul]

/-- A lower bound on `λ_k(Sᴴ A S)` from a lower bound on `λ_k(A) ‖S z‖ ^ 2`. -/
private theorem le_eigenvalue_conjTranspose_mul_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (S : Matrix n n 𝕜) {k : ℕ} (hk : k < Fintype.card n) {c : ℝ}
    (h : ∀ z, c * ‖WithLp.toLp 2 z‖ ^ 2 ≤ eigenvalue A k * ‖WithLp.toLp 2 (S *ᵥ z)‖ ^ 2) :
    c ≤ eigenvalue (Sᴴ * A * S) k := by
  classical
  have hB : (A - eigenvalue A k • (1 : Matrix n n 𝕜)).IsHermitian :=
    hA.sub (isHermitian_real_smul_one _)
  have hM := Matrix.isHermitian_conjTranspose_mul_mul S hB
  have h0 : eigenvalue (A - eigenvalue A k • (1 : Matrix n n 𝕜)) k = 0 := by
    rw [sub_eq_add_neg, ← neg_smul, hA.eigenvalue_add_smul_one _ hk, add_neg_cancel]
  have hle : Sᴴ * (A - eigenvalue A k • (1 : Matrix n n 𝕜)) * S + c • (1 : Matrix n n 𝕜) ≤
      Sᴴ * A * S := by
    rw [(hM.add (isHermitian_real_smul_one c)).le_iff_re_quadForm_le
      (Matrix.isHermitian_conjTranspose_mul_mul S hA)]
    intro z
    rw [re_quadForm_conjTranspose_mul_sub_mul_add]
    linarith [h z]
  have h1 := eigenvalue_le_eigenvalue_of_le hle (hM.add (isHermitian_real_smul_one c)) k
  rwa [hM.eigenvalue_add_smul_one c hk, eigenvalue_conjTranspose_mul_mul_eq_zero hB S hk h0,
    zero_add] at h1

/-- An upper bound on `λ_k(Sᴴ A S)` from an upper bound on `λ_k(A) ‖S z‖ ^ 2`. -/
private theorem eigenvalue_conjTranspose_mul_mul_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (S : Matrix n n 𝕜) {k : ℕ} (hk : k < Fintype.card n) {c : ℝ}
    (h : ∀ z, eigenvalue A k * ‖WithLp.toLp 2 (S *ᵥ z)‖ ^ 2 ≤ c * ‖WithLp.toLp 2 z‖ ^ 2) :
    eigenvalue (Sᴴ * A * S) k ≤ c := by
  classical
  have hB : (A - eigenvalue A k • (1 : Matrix n n 𝕜)).IsHermitian :=
    hA.sub (isHermitian_real_smul_one _)
  have hM := Matrix.isHermitian_conjTranspose_mul_mul S hB
  have h0 : eigenvalue (A - eigenvalue A k • (1 : Matrix n n 𝕜)) k = 0 := by
    rw [sub_eq_add_neg, ← neg_smul, hA.eigenvalue_add_smul_one _ hk, add_neg_cancel]
  have hle : Sᴴ * A * S ≤
      Sᴴ * (A - eigenvalue A k • (1 : Matrix n n 𝕜)) * S + c • (1 : Matrix n n 𝕜) := by
    rw [(Matrix.isHermitian_conjTranspose_mul_mul S hA).le_iff_re_quadForm_le
      (hM.add (isHermitian_real_smul_one c))]
    intro z
    rw [re_quadForm_conjTranspose_mul_sub_mul_add]
    linarith [h z]
  have h1 := eigenvalue_le_eigenvalue_of_le hle (Matrix.isHermitian_conjTranspose_mul_mul S hA) k
  rwa [hM.eigenvalue_add_smul_one c hk, eigenvalue_conjTranspose_mul_mul_eq_zero hB S hk h0,
    zero_add] at h1

/-- **Ostrowski's theorem.** Congruence by `S` multiplies each eigenvalue by a factor between
the squares of the smallest and largest singular values of `S`.
[HornJohnson2013, Theorem 4.5.9]. Port of `NLAlib.exists_eigenvalues₀_congruence_scale`.
Result: ostrowski -/
theorem _root_.Matrix.IsHermitian.exists_eigenvalue_conjTranspose_mul_mul_eq_mul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (S : Matrix n n 𝕜) {k j : ℕ} (hk : k < Fintype.card n) (hj : j + 1 = Fintype.card n) :
    ∃ θ : ℝ, singularValues S j ^ 2 ≤ θ ∧ θ ≤ specNorm S ^ 2 ∧
      eigenvalue (Sᴴ * A * S) k = θ * eigenvalue A k := by
  have hlo : ∀ z : n → 𝕜, singularValues S j ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 ≤
      ‖WithLp.toLp 2 (S *ᵥ z)‖ ^ 2 := fun z => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (singularValues_nonneg S j) (norm_nonneg _))
      (singularValues_last_mul_norm_le S hj z) 2
  have hup : ∀ z : n → 𝕜, ‖WithLp.toLp 2 (S *ᵥ z)‖ ^ 2 ≤
      specNorm S ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 := fun z => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_toLp_mulVec_le S z) 2
  have hσ : singularValues S j ^ 2 ≤ specNorm S ^ 2 :=
    pow_le_pow_left₀ (singularValues_nonneg S j) (singularValues_le_specNorm S j) 2
  rcases lt_trichotomy (eigenvalue A k) 0 with hneg | hzero | hpos
  · have h1 := le_eigenvalue_conjTranspose_mul_mul hA S hk
      (c := eigenvalue A k * specNorm S ^ 2) fun z => by
        rw [mul_assoc]
        exact mul_le_mul_of_nonpos_left (hup z) hneg.le
    have h2 := eigenvalue_conjTranspose_mul_mul_le hA S hk
      (c := eigenvalue A k * singularValues S j ^ 2) fun z => by
        rw [mul_assoc]
        exact mul_le_mul_of_nonpos_left (hlo z) hneg.le
    refine ⟨eigenvalue (Sᴴ * A * S) k / eigenvalue A k, ?_, ?_, ?_⟩
    · rw [le_div_iff_of_neg hneg]
      linarith
    · rw [div_le_iff_of_neg hneg]
      linarith
    · rw [div_mul_cancel₀ _ hneg.ne]
  · have h1 := le_eigenvalue_conjTranspose_mul_mul hA S hk (c := 0) fun z => by
      rw [hzero, zero_mul, zero_mul]
    have h2 := eigenvalue_conjTranspose_mul_mul_le hA S hk (c := 0) fun z => by
      rw [hzero, zero_mul, zero_mul]
    exact ⟨singularValues S j ^ 2, le_rfl, hσ, by rw [hzero, mul_zero, le_antisymm h2 h1]⟩
  · have h1 := le_eigenvalue_conjTranspose_mul_mul hA S hk
      (c := eigenvalue A k * singularValues S j ^ 2) fun z => by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hlo z) hpos.le
    have h2 := eigenvalue_conjTranspose_mul_mul_le hA S hk
      (c := eigenvalue A k * specNorm S ^ 2) fun z => by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hup z) hpos.le
    refine ⟨eigenvalue (Sᴴ * A * S) k / eigenvalue A k, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ hpos]
      linarith
    · rw [div_le_iff₀ hpos]
      linarith
    · rw [div_mul_cancel₀ _ hpos.ne']

/-! ### Inertia and interlacing -/

/-- **Adding a Hermitian matrix with `p` positive eigenvalues moves each eigenvalue up by at most
`p` places**: `λ_{i+p}(A + B) ≤ λ_i(A)` with `p = inertiaPos B`, for `i + p` below the size.
[HornJohnson2013, Corollary 4.3.5].
Port of `NLAlib.eigenvalues₀_add_le_of_card_pos`. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_add_le_of_inertiaPos
    {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {i : ℕ} (hi : i + inertiaPos B < Fintype.card n) :
    eigenvalue (A + B) (i + inertiaPos B) ≤ eigenvalue A i := by
  have h1 := eigenvalue_add_le hA hB hi
  have h2 : eigenvalue B (inertiaPos B) ≤ 0 := by
    by_contra h
    exact lt_irrefl _ (hB.lt_inertiaPos_iff.mpr ⟨by omega, not_le.mp h⟩)
  linarith

/-- Adding a Hermitian matrix with `q` negative eigenvalues moves each eigenvalue down by at most
`q` places: `λ_{i+q}(A) ≤ λ_i(A + B)` with `q = inertiaNeg B`, for `i + q` below the size.
Port of `NLAlib.eigenvalues₀_le_add_of_card_neg`. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_le_eigenvalue_add_of_inertiaNeg
    {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {i : ℕ} (hi : i + inertiaNeg B < Fintype.card n) :
    eigenvalue A (i + inertiaNeg B) ≤ eigenvalue (A + B) i := by
  rw [inertiaNeg_eq_inertiaPos_neg] at hi ⊢
  have h := (hA.add hB).eigenvalue_add_le_of_inertiaPos hB.neg hi
  rwa [add_neg_cancel_right] at h

/-- **A strict Courant–Fischer bound from below**: if the form of `A` exceeds `c` on a subspace
of dimension `k + 1`, then `c < λ_k(A)`.
Port of `NLAlib.lt_eigenvalues₀_of_forall_mem`. -/
theorem _root_.Matrix.IsHermitian.lt_eigenvalue_of_posDef_conjTranspose_mul_mul_sub
    {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} {V : Matrix n (Fin (k + 1)) 𝕜} (hV : HasOrthonormalCols V)
    {c : ℝ} (h : (Vᴴ * A * V - c • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜)).PosDef) :
    c < eigenvalue A k := by
  have hfin := finrank_range_mulVecLin_of_injective hV.mulVec_injective
  rw [Fintype.card_fin] at hfin
  refine (lt_eigenvalue_of_forall_mem hA _ hfin.ge ?_).2
  rintro x ⟨y, rfl⟩ hx
  have hy : y ≠ 0 := fun hy => hx (by rw [hy]; exact map_zero _)
  have h1 := h.re_quadForm_pos hy
  rw [quadForm_sub_left, map_sub, re_quadForm_real_smul_one, quadForm_conjTranspose_mul_mul,
    sub_pos] at h1
  rwa [Matrix.mulVecLin_apply, hV.norm_toLp_mulVec]

end NLAlib
