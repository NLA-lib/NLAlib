/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.RCLike.Basic

/-!
# Rank inequalities for matrices over a field

Facts about `Matrix.rank` that Mathlib does not yet have. Upstream candidates for
`Mathlib.LinearAlgebra.Matrix.Rank`.

Sylvester's and Frobenius's inequalities are stated additively, with no truncated subtraction,
so that `omega` and `linarith` can use them.

## Main results

* `Matrix.rank_eq_zero`: a matrix over a field has rank zero exactly when it is zero.
* `Matrix.rank_add_le`: subadditivity of rank.
* `Matrix.rank_add_rank_le_card_add_rank_mul`: Sylvester's rank inequality.
* `Matrix.rank_mul_add_rank_mul_le`: Frobenius's rank inequality.
* `Matrix.rank_fromBlocks_zero₁₂_zero₂₁`: rank of a block diagonal matrix.
* `Matrix.rank_fromBlocks₁₁`: rank additivity of the Schur complement.
* `Matrix.rank_fromCols_replicateCol_eq_iff`: the Rouché–Capelli solvability criterion.
* `Matrix.finrank_ker_toBlock_eq_finrank_ker_inv_toBlock_not`: complementary nullities.
* `Matrix.rank_mul_eq_iff_injOn`: $\mathbf{S}$ keeps the rank of $\mathbf{X}$ iff it is injective
  on $\operatorname{range}\mathbf{X}$; `Matrix.range_conjTranspose_mul_eq_of_rank_eq`:
  it then keeps the row space.
* `Matrix.rank_mul_of_snoc_eq_rank_of_snoc`: $\mathbf{B}$ keeps the rank of
  $[\mathbf{U}\;\mathbf{x}]$ when it keeps that of $\mathbf{U}$ and either $\mathbf{x}$ lies in
  the column span of $\mathbf{U}$ or $\mathbf{B}\mathbf{x}$ lies outside that of
  $\mathbf{B}\mathbf{U}$.
* `Submodule.finrank_map_add_finrank_inf_ker`: rank–nullity for a linear map restricted to a
  submodule.
* `Submodule.finrank_prod`: the dimension of a product of submodules.
-/

@[expose] public section

/-- **Rank–nullity for the restriction of a linear map to a submodule**: the dimension of the
image of $S$ under $f$ plus the dimension of $S \cap \ker f$ is the dimension of $S$. Upstream
candidate for `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`.
[HornJohnson2013, (0.2.3.1)]. -/
theorem Submodule.finrank_map_add_finrank_inf_ker {K E F : Type*} [DivisionRing K]
    [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F] (f : E →ₗ[K] F)
    (S : Submodule K E) [FiniteDimensional K S] :
    Module.finrank K (S.map f) + Module.finrank K (S ⊓ LinearMap.ker f : Submodule K E) =
      Module.finrank K S := by
  have h := (f.domRestrict S).finrank_range_add_finrank_ker
  rwa [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq,
    Submodule.map_comap_subtype] at h

/-- The dimension of a product of submodules is the sum of the dimensions. Upstream candidate for
`Mathlib.LinearAlgebra.Dimension.Constructions`, next to `Module.finrank_prod`. -/
theorem Submodule.finrank_prod {K E F : Type*} [DivisionRing K] [AddCommGroup E]
    [Module K E] [AddCommGroup F] [Module K F] (p : Submodule K E) (q : Submodule K F)
    [FiniteDimensional K p] [FiniteDimensional K q] :
    Module.finrank K (p.prod q) = Module.finrank K p + Module.finrank K q := by
  rw [← Module.finrank_prod, ← LinearMap.finrank_range_of_inj
    (f := p.subtype.prodMap q.subtype) (p.injective_subtype.prodMap q.injective_subtype),
    LinearMap.range_prodMap, Submodule.range_subtype, Submodule.range_subtype]

/-- Two subspaces $S, W$ of $K^n$ meet in dimension at least the sum of their dimensions minus
$\lvert n \rvert$, stated additively: $\dim S + \dim W \le \lvert n \rvert + \dim(S \cap W)$.
A consequence of
`Submodule.finrank_sup_add_finrank_inf_eq`, in the form dimension counts with `omega` use.
Upstream candidate for `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`. -/
theorem Submodule.finrank_add_finrank_le_card_add_finrank_inf {K n : Type*} [DivisionRing K]
    [Fintype n] (S W : Submodule K (n → K)) :
    Module.finrank K S + Module.finrank K W ≤
      Fintype.card n + Module.finrank K (S ⊓ W : Submodule K (n → K)) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq S W
  have hs := (S ⊔ W).finrank_le
  rw [Module.finrank_fintype_fun_eq_card] at hs
  lia

namespace Matrix

variable {K : Type*} [Field K] {l m n p : Type*} [Fintype n]

/-- **Rank–nullity for a matrix**: the dimension of the kernel of
$\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ plus the rank of $\mathbf{A}$ is the number of columns
$\lvert n \rvert$. The matrix may be rectangular. This is
`LinearMap.finrank_range_add_finrank_ker` for `A.mulVecLin`, in terms of `Matrix.rank`.
[HornJohnson2013, (0.2.3.1)]. -/
theorem finrank_ker_add_rank (A : Matrix m n K) :
    Module.finrank K (LinearMap.ker A.mulVecLin) + A.rank = Fintype.card n := by
  have h := A.mulVecLin.finrank_range_add_finrank_ker
  rwa [Module.finrank_fintype_fun_eq_card, add_comm] at h

/-- A matrix over a field has rank zero exactly when it is the zero matrix. -/
@[simp]
theorem rank_eq_zero {A : Matrix m n K} : A.rank = 0 ↔ A = 0 := by
  classical
  rw [rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot, ← toLin'_apply',
    LinearEquiv.map_eq_zero_iff]

/-- **Subadditivity of rank.** The rank of a sum is at most the sum of the ranks:
$\operatorname{rank}(\mathbf{A} + \mathbf{B}) \le \operatorname{rank} \mathbf{A} +
\operatorname{rank} \mathbf{B}$.
[HornJohnson2013, §0.4.5]; stated there for complex matrices, here over any field and any finite
index types.
Result: rank-inequalities -/
theorem rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [rank, rank, rank, mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Negating a matrix does not change its rank. -/
@[simp]
theorem rank_neg (A : Matrix m n K) : (-A).rank = A.rank := by
  rw [← neg_one_smul K A, rank_smul_of_mem_nonZeroDivisors A isUnit_one.neg.mem_nonZeroDivisors]

/-- The rank of a difference is at most the sum of the ranks. -/
theorem rank_sub_le (A B : Matrix m n K) : (A - B).rank ≤ A.rank + B.rank := by
  rw [sub_eq_add_neg, ← rank_neg B]
  exact rank_add_le A (-B)

/-- **Sylvester's rank inequality.** For $\mathbf{A}$ with column index $n$ and $\mathbf{B}$ with
row index $n$,
$\operatorname{rank} \mathbf{A} + \operatorname{rank} \mathbf{B}
\le \lvert n \rvert + \operatorname{rank}(\mathbf{A}\mathbf{B})$.
[HornJohnson2013, §0.4.5]; stated there as
$\operatorname{rank} \mathbf{A} + \operatorname{rank} \mathbf{B} - n
\le \operatorname{rank}(\mathbf{A}\mathbf{B})$, here additively and over any field.
Result: sylvester-rank-inequality, rank-inequalities -/
theorem rank_add_rank_le_card_add_rank_mul [Fintype p] (A : Matrix m n K) (B : Matrix n p K) :
    A.rank + B.rank ≤ Fintype.card n + (A * B).rank := by
  have hB := Submodule.finrank_map_add_finrank_inf_ker A.mulVecLin (LinearMap.range B.mulVecLin)
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  have hle : Module.finrank K
      (LinearMap.range B.mulVecLin ⊓ LinearMap.ker A.mulVecLin : Submodule K (n → K)) ≤
      Module.finrank K (LinearMap.ker A.mulVecLin) := Submodule.finrank_mono inf_le_right
  rw [← LinearMap.range_comp, ← mulVecLin_mul] at hB
  rw [Module.finrank_fintype_fun_eq_card] at hA
  rw [rank, rank, rank]
  lia

/-- **Frobenius's rank inequality.**
$\operatorname{rank}(\mathbf{A}\mathbf{B}) + \operatorname{rank}(\mathbf{B}\mathbf{C})
\le \operatorname{rank} \mathbf{B} + \operatorname{rank}(\mathbf{A}\mathbf{B}\mathbf{C})$.
[HornJohnson2013, §0.4.5]; here over any field and any finite index types.
Result: frobenius-rank-inequality, rank-inequalities -/
theorem rank_mul_add_rank_mul_le [Fintype m] [Fintype p] (A : Matrix l m K) (B : Matrix m n K)
    (C : Matrix n p K) : (A * B).rank + (B * C).rank ≤ B.rank + (A * B * C).rank := by
  have hB := Submodule.finrank_map_add_finrank_inf_ker A.mulVecLin (LinearMap.range B.mulVecLin)
  have hBC := Submodule.finrank_map_add_finrank_inf_ker A.mulVecLin
    (LinearMap.range (B * C).mulVecLin)
  have hle := Submodule.finrank_mono (inf_le_inf_right (LinearMap.ker A.mulVecLin)
    (mulVecLin_mul B C ▸ LinearMap.range_comp_le_range C.mulVecLin B.mulVecLin))
  rw [← LinearMap.range_comp, ← mulVecLin_mul] at hB hBC
  rw [Matrix.mul_assoc, rank, rank, rank, rank]
  lia

/-- The rank of a block diagonal matrix is the sum of the ranks of its blocks. The blocks may be
rectangular:
$\operatorname{rank} \begin{bmatrix} \mathbf{A} & \mathbf{0} \\ \mathbf{0} & \mathbf{D}
\end{bmatrix} = \operatorname{rank} \mathbf{A} + \operatorname{rank} \mathbf{D}$. -/
theorem rank_fromBlocks_zero₁₂_zero₂₁ [Fintype m] (A : Matrix l m K) (D : Matrix p n K) :
    (fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  have h : (fromBlocks A 0 0 D).mulVecLin =
      (LinearEquiv.sumArrowLequivProdArrow l p K K).symm.toLinearMap ∘ₗ
        A.mulVecLin.prodMap D.mulVecLin ∘ₗ
          (LinearEquiv.sumArrowLequivProdArrow m n K K).toLinearMap := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [mulVecLin_apply, fromBlocks_mulVec, zero_mulVec, add_zero, zero_add]
    rfl
  rw [rank, rank, rank, h, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, LinearEquiv.finrank_map_eq, LinearMap.range_prodMap,
    Submodule.finrank_prod]

/-- **Rank additivity of the Schur complement.** With an invertible leading block
$\mathbf{A}$ indexed by $m$,
$$\operatorname{rank} \begin{bmatrix} \mathbf{A} & \mathbf{B} \\ \mathbf{C} & \mathbf{D}
\end{bmatrix}
= \lvert m \rvert + \operatorname{rank}(\mathbf{D} - \mathbf{C}\mathbf{A}^{-1}\mathbf{B}) \,.$$
The trailing blocks may be rectangular.
[HornJohnson2013, §0.8.5]; here over any field.
Result: schur-complement-rank -/
theorem rank_fromBlocks₁₁ [Finite l] [Fintype m] [DecidableEq m] (A : Matrix m m K)
    (B : Matrix m n K) (C : Matrix l m K) (D : Matrix l n K) [Invertible A] :
    (fromBlocks A B C D).rank = Fintype.card m + (D - C * ⅟A * B).rank := by
  classical
  cases nonempty_fintype l
  have hL : IsUnit (fromBlocks (1 : Matrix m m K) 0 (C * ⅟A) (1 : Matrix l l K)).det := by simp
  have hU : IsUnit (fromBlocks (1 : Matrix m m K) (⅟A * B) 0 (1 : Matrix n n K)).det := by simp
  rw [fromBlocks_eq_of_invertible₁₁ A B C D, rank_mul_eq_left_of_isUnit_det _ _ hU,
    rank_mul_eq_right_of_isUnit_det _ _ hL, rank_fromBlocks_zero₁₂_zero₂₁,
    rank_of_isUnit A (isUnit_of_invertible A)]

/-- **Rouché–Capelli.** Adjoining the column $\mathbf{b}$ to $\mathbf{A}$ leaves the rank
unchanged exactly when $\mathbf{A}\mathbf{x} = \mathbf{b}$ has a solution.
[HornJohnson2013, §0.4.2].
Result: rouche-capelli -/
theorem rank_fromCols_replicateCol_eq_iff (A : Matrix m n K) (b : m → K) :
    (fromCols A (replicateCol Unit b)).rank = A.rank ↔ ∃ x, A *ᵥ x = b := by
  have hcol : (fromCols A (replicateCol Unit b)).col = Sum.elim A.col fun _ ↦ b := by
    ext (j | j) i <;> rfl
  rw [rank_eq_finrank_span_cols, rank_eq_finrank_span_cols, hcol, Set.Sum.elim_range,
    Set.range_const, Submodule.span_union, ← range_mulVecLin]
  change _ ↔ b ∈ LinearMap.range A.mulVecLin
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Submodule.eq_of_le_of_finrank_eq le_sup_left h.symm]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self b)
  · rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr h)]

/-- If $\mathbf{P}\mathbf{X} + \mathbf{Q}\mathbf{Y} = \mathbf{0}$ and
$\mathbf{R}\mathbf{X} + \mathbf{S}\mathbf{Y} = \mathbf{I}$, then $\mathbf{Y}$ maps the kernel of
$\mathbf{X}$ injectively into the kernel of $\mathbf{Q}$. -/
private theorem finrank_ker_mulVecLin_le_of_mul_add_mul {a a' b d : Type*} [Fintype a]
    [Fintype a'] [Fintype b] [DecidableEq b] {X : Matrix a b K} {Y : Matrix a' b K}
    {P : Matrix d a K} {Q : Matrix d a' K} {R : Matrix b a K} {S : Matrix b a' K}
    (h₀ : P * X + Q * Y = 0) (h₁ : R * X + S * Y = 1) :
    Module.finrank K (LinearMap.ker X.mulVecLin) ≤
      Module.finrank K (LinearMap.ker Q.mulVecLin) := by
  have hmaps : ∀ x ∈ LinearMap.ker X.mulVecLin, Y.mulVecLin x ∈ LinearMap.ker Q.mulVecLin := by
    intro x hx
    rw [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
    simpa [add_mulVec, ← mulVec_mulVec, hx] using congrArg (· *ᵥ x) h₀
  refine LinearMap.finrank_le_finrank_of_injective (f := Y.mulVecLin.restrict hmaps)
    ((injective_iff_map_eq_zero _).mpr fun x hx ↦ Subtype.ext ?_)
  have hX : X *ᵥ (x : b → K) = 0 := x.2
  have hY : Y *ᵥ (x : b → K) = 0 := congrArg Subtype.val hx
  simpa [add_mulVec, ← mulVec_mulVec, hX, hY] using (congrArg (· *ᵥ (x : b → K)) h₁).symm

/-- **Complementary nullities.** For an invertible $\mathbf{A}$ and sets of indices $r$ (rows) and
$c$ (columns), the block of $\mathbf{A}$ on rows $r$ and columns $c$ and the block of
$\mathbf{A}^{-1}$ on rows outside $c$ and columns outside $r$ have kernels of the same dimension.
The blocks need not be square.
[HornJohnson2013, §0.7.5]; here over any field.
Result: complementary-nullities -/
theorem finrank_ker_toBlock_eq_finrank_ker_inv_toBlock_not [DecidableEq n] (A : Matrix n n K)
    (hA : IsUnit A) (r c : n → Prop) [DecidablePred r] [DecidablePred c] :
    Module.finrank K (LinearMap.ker (A.toBlock r c).mulVecLin) =
      Module.finrank K
        (LinearMap.ker (A⁻¹.toBlock (fun i => ¬ c i) (fun i => ¬ r i)).mulVecLin) := by
  have hA' := (isUnit_iff_isUnit_det A).mp hA
  have hAB : A * A⁻¹ = 1 := mul_nonsing_inv A hA'
  have hBA : A⁻¹ * A = 1 := nonsing_inv_mul A hA'
  refine le_antisymm
    (finrank_ker_mulVecLin_le_of_mul_add_mul (Y := A.toBlock (¬ r ·) c)
      (P := A⁻¹.toBlock (¬ c ·) r) (R := A⁻¹.toBlock c r) (S := A⁻¹.toBlock c (¬ r ·)) ?_ ?_)
    (finrank_ker_mulVecLin_le_of_mul_add_mul (Y := A⁻¹.toBlock c (¬ r ·))
      (P := A.toBlock r (¬ c ·)) (R := A.toBlock (¬ r ·) (¬ c ·)) (S := A.toBlock (¬ r ·) c) ?_ ?_)
  · rw [← toBlock_mul_eq_add, hBA, toBlock_one_disjoint]
    exact disjoint_compl_left
  · rw [← toBlock_mul_eq_add, hBA, toBlock_one_self]
  · rw [add_comm, ← toBlock_mul_eq_add, hAB, toBlock_one_disjoint]
    exact disjoint_compl_right
  · rw [add_comm, ← toBlock_mul_eq_add, hAB, toBlock_one_self]

/-- **Law of complementary nullities.** The rank form, stated additively: the rank of the block of
$\mathbf{A}$ on rows $r$ and columns $c$, plus the number of indices outside $r$, equals the rank
of the complementary block of $\mathbf{A}^{-1}$ (rows outside $c$, columns outside $r$) plus the
number of indices in $c$.
[HornJohnson2013, §0.7.5].
Result: complementary-nullities -/
theorem rank_toBlock_add_card_eq_rank_inv_toBlock_not_add_card [DecidableEq n] (A : Matrix n n K)
    (hA : IsUnit A) (r c : n → Prop) [DecidablePred r] [DecidablePred c] :
    (A.toBlock r c).rank + Fintype.card {j // ¬ r j} =
      (A⁻¹.toBlock (fun i => ¬ c i) (fun i => ¬ r i)).rank + Fintype.card {j // c j} := by
  have h₁ := (A.toBlock r c).mulVecLin.finrank_range_add_finrank_ker
  have h₂ := (A⁻¹.toBlock (fun i => ¬ c i) (fun i => ¬ r i)).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at h₁ h₂
  have h := finrank_ker_toBlock_eq_finrank_ker_inv_toBlock_not A hA r c
  rw [rank, rank]
  lia


/-! ### Sketches that keep the rank -/

section KeepRank

variable {k r : Type*} [Fintype m] [Fintype r]

omit [Fintype n] in
/-- The rank interface: the sketch $\mathbf{S}$ keeps the rank of $\mathbf{X}$,
$\operatorname{rank}(\mathbf{S}\mathbf{X}) = \operatorname{rank}\mathbf{X}$, exactly when it is
injective on $\operatorname{range}\mathbf{X}$. This is the form `NLAlib.IsSubspaceInjection.injOn`
concludes, and the hypothesis of the oblique projector `NLAlib.obliqueProjector X S`. -/
theorem rank_mul_eq_iff_injOn {S : Matrix k m K} {X : Matrix m r K} :
    (S * X).rank = X.rank ↔ Set.InjOn S.mulVec (LinearMap.range X.mulVecLin) := by
  set V := LinearMap.range X.mulVecLin
  set g := S.mulVecLin.domRestrict V
  have hr : LinearMap.range g = LinearMap.range (S * X).mulVecLin := by
    rw [LinearMap.range_domRestrict, Matrix.mulVecLin_mul, LinearMap.range_comp]
  have hn := LinearMap.finrank_range_add_finrank_ker g
  rw [hr] at hn
  have hinj : Set.InjOn S.mulVec V ↔ Function.Injective g := by
    constructor
    · intro h a b hab
      exact Subtype.ext (h a.2 b.2 (by simpa [g] using hab))
    · intro h a ha b hb hab
      exact congrArg Subtype.val (@h ⟨a, ha⟩ ⟨b, hb⟩ (by simpa [g] using hab))
  rw [hinj, ← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  change Module.finrank K (LinearMap.range (S * X).mulVecLin) = Module.finrank K V ↔ _
  omega

end KeepRank

section Snoc

/-- Adding a vector outside a finite-dimensional subspace raises its finrank by one. -/
private lemma finrank_sup_span_singleton_of_notMem {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] {p : Submodule K V} [FiniteDimensional K p] {v : V}
    (hv : v ∉ p) : Module.finrank K ↥(p ⊔ K ∙ v) = Module.finrank K p + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ p.zero_mem)
  have hinf : p ⊓ K ∙ v = ⊥ :=
    (Submodule.disjoint_span_singleton' hv0).mpr hv |>.eq_bot
  have := Submodule.finrank_sup_add_finrank_inf_eq p (K ∙ v)
  rw [hinf, finrank_bot, finrank_span_singleton hv0] at this
  omega

/-- Rank step of general position: let $\mathbf{B} \in \Bbbk^{k \times d}$ preserve the rank
of $\mathbf{U} \in \Bbbk^{d \times i}$, $\operatorname{rank}(\mathbf{B}\mathbf{U}) =
\operatorname{rank}\mathbf{U}$, and append a column $\mathbf{x}$. If $\mathbf{x}$ lies in the
column span of $\mathbf{U}$, or $\mathbf{B}\mathbf{x}$ does not lie in the column span of
$\mathbf{B}\mathbf{U}$, then $\mathbf{B}$ preserves the rank of $[\mathbf{U}\;\mathbf{x}]$. -/
theorem rank_mul_of_snoc_eq_rank_of_snoc {𝕜 : Type*} [Field 𝕜] {d k : Type*} [Fintype d] {i : ℕ}
    (B : Matrix k d 𝕜) (U : Matrix d (Fin i) 𝕜) (x : d → 𝕜)
    (hU : (B * U).rank = U.rank)
    (hx : x ∈ Submodule.span 𝕜 (Set.range Uᵀ) ∨ B *ᵥ x ∉ Submodule.span 𝕜 (Set.range (B * U)ᵀ)) :
    (B * Matrix.of fun r => Fin.snoc (α := fun _ => 𝕜) (U r) (x r)).rank =
      (Matrix.of fun r => Fin.snoc (α := fun _ => 𝕜) (U r) (x r)).rank := by
  set M : Matrix d (Fin (i + 1)) 𝕜 := Matrix.of fun r => Fin.snoc (α := fun _ => 𝕜) (U r) (x r)
  have hcolBU : Set.range (B * U).col = Matrix.mulVecLin B '' Set.range U.col := by
    rw [← Set.range_comp]
    congr 1
  have hMcol : M.col = Fin.snoc U.col x := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [Fin.snoc_last]; funext r; simp [M]
    · rw [Fin.snoc_castSucc]; funext r; simp [M]
  have hcolM : Set.range M.col = insert x (Set.range U.col) := by
    rw [hMcol, Fin.range_snoc]
  have hcolBM : Set.range (B * M).col = insert (B *ᵥ x) (Set.range (B * U).col) := by
    have : (B * M).col = Fin.snoc (B * U).col (B *ᵥ x) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last]; funext r; simp [M, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      · rw [Fin.snoc_castSucc]; funext r; simp [M, Matrix.mul_apply]
    rw [this, Fin.range_snoc]
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols] at hU ⊢
  rw [hcolBM, hcolM, Submodule.span_insert, Submodule.span_insert]
  change x ∈ Submodule.span 𝕜 (Set.range U.col) ∨
    B *ᵥ x ∉ Submodule.span 𝕜 (Set.range (B * U).col) at hx
  rw [hcolBU, Submodule.span_image] at hU hx ⊢
  have hW : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range U.col)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  generalize Submodule.span 𝕜 (Set.range U.col) = W at hU hx hW ⊢
  have hBx : B *ᵥ x = B.mulVecLin x := rfl
  rw [hBx] at hx ⊢
  rcases em (x ∈ W) with h | h
  · rw [sup_eq_right.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr h),
      sup_eq_right.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr
        (Submodule.mem_map_of_mem h)), hU]
  · have h' : B.mulVecLin x ∉ W.map B.mulVecLin := hx.resolve_left h
    rw [sup_comm, finrank_sup_span_singleton_of_notMem h',
      sup_comm, finrank_sup_span_singleton_of_notMem h, hU]

end Snoc

section RCLike

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {k r : Type*} [Fintype k] [Fintype m] [Fintype r]

omit [Fintype n] in
/-- A sketch $\mathbf{S}$ that keeps the rank of $\mathbf{X}$,
$\operatorname{rank}(\mathbf{S}\mathbf{X}) = \operatorname{rank}\mathbf{X}$, keeps its row space:
$$\operatorname{range}(\mathbf{S}\mathbf{X})^{\mathsf{H}} =
\operatorname{range}\mathbf{X}^{\mathsf{H}}\,.$$ -/
theorem range_conjTranspose_mul_eq_of_rank_eq {S : Matrix k m 𝕜} {X : Matrix m r 𝕜}
    (h : (S * X).rank = X.rank) :
    LinearMap.range (S * X)ᴴ.mulVecLin = LinearMap.range Xᴴ.mulVecLin := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [conjTranspose_mul, mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · change (S * X)ᴴ.rank = Xᴴ.rank
    rw [rank_conjTranspose, rank_conjTranspose, h]

end RCLike

end Matrix
