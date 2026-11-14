/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import NLAlib.ForMathlib.Data.Matrix.Mul
public import NLAlib.Krylov.Basic.Space
public import NLAlib.Matrix.Basic.Projector
public import NLAlib.Matrix.Functions.Polynomial

/-!
# Block Krylov matrices and block Krylov spaces

The block Krylov matrix $\mathbf{K}_q(\mathbf{A}, \mathbf{B}) =
[\mathbf{B}, \mathbf{A}\mathbf{B}, \dots, \mathbf{A}^{q-1}\mathbf{B}]$ of a square $\mathbf{A}$ and
a starting block $\mathbf{B} \in \Bbbk^{n \times p}$, with columns indexed by `Fin q × p`
(block $j$, column $c$ of $\mathbf{A}^j\mathbf{B}$), and its column space, the block Krylov space
$\mathcal{K}_q(\mathbf{A}, \mathbf{B})$. Its vectors are the sums
$\sum_c f_c(\mathbf{A})\mathbf{b}_c$ over the columns $\mathbf{b}_c$ of $\mathbf{B}$, one polynomial
of degree less than $q$ per column; in particular the range of $f(\mathbf{A})\mathbf{B}$ lies in it
for every polynomial of degree less than $q$, which is the only Krylov fact the analysis of
randomized block Krylov iteration uses.

The vector Krylov API (`NLAlib.krylovMatrix`, `NLAlib.krylovSpace`) is separate; the bridges say
that the one-column block objects are the
vector ones and that a block Krylov space is the supremum of the vector Krylov spaces of its
columns.

The index $q$ counts blocks: $\mathcal{K}_0 = \{\mathbf{0}\}$, $\mathcal{K}_1$ is the range of
$\mathbf{B}$.

## Main definitions

* `NLAlib.blockKrylovMatrix`: the block Krylov matrix, columns indexed by `Fin q × p`.
* `NLAlib.blockKrylovSpace`: its column space.

## Main results

* `NLAlib.blockKrylovMatrix_replicateCol`, `NLAlib.blockKrylovSpace_replicateCol`: one column is the
  vector case.
* `NLAlib.blockKrylovSpace_eq_iSup_krylovSpace`: the supremum of the column Krylov spaces.
* `NLAlib.blockKrylovSpace_mono`, `NLAlib.blockKrylovSpace_succ`,
  `NLAlib.mulVec_mem_blockKrylovSpace_succ`: nesting, one block per step,
  $\mathbf{A}\mathcal{K}_q \subseteq \mathcal{K}_{q+1}$.
* `NLAlib.blockKrylovSpace_add_smul_one`: shift invariance.
* `NLAlib.blockKrylovMatrix_mul_mul`, `NLAlib.blockKrylovSpace_mul_mul`: the change of variables
  $\mathcal{K}_q(\mathbf{C}\mathbf{D}, \mathbf{C}\mathbf{B}) =
  \mathbf{C}\,\mathcal{K}_q(\mathbf{D}\mathbf{C}, \mathbf{B})$ for rectangular $\mathbf{C}$,
  $\mathbf{D}$.
* `NLAlib.mem_blockKrylovSpace_iff`, `NLAlib.exists_aeval_mul_eq_blockKrylovMatrix_mul`,
  `NLAlib.range_aeval_mul_le_blockKrylovSpace`: the polynomial description.
* `NLAlib.exists_sum_eval_sq_mul_norm_sq_le_norm_sub_mulVec_sq`.
* `NLAlib.blockKrylovSpace_le_of_range_le`,
  `NLAlib.sup_sup_map_mulVecLin_le_blockKrylovSpace_add_two`: the depth count of the Krylov
  coupling.
* `NLAlib.blockKrylovSpace_blockKrylovMatrix`: the block Krylov space of a block Krylov matrix,
  $\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{K}_{s+1}(\mathbf{A}, \mathbf{B})) =
  \mathcal{K}_{s+q+1}(\mathbf{A}, \mathbf{B})$.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq n]


omit [Fintype p] in
/-- The **block Krylov matrix** $\mathbf{K}_q(\mathbf{A}, \mathbf{B}) =
[\mathbf{B}, \mathbf{A}\mathbf{B}, \dots, \mathbf{A}^{q-1}\mathbf{B}]$: the column indexed by
$(j, c)$ is column $c$ of $\mathbf{A}^j\mathbf{B}$, for $j < q$. For $q = 0$ it has no columns.
[Saad2003, §6.12]; [TroppWebber2023, §5.3]. -/
def blockKrylovMatrix (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) : Matrix n (Fin q × p) 𝕜 :=
  Matrix.of fun i jc => (A ^ (jc.1 : ℕ) * B) i jc.2

omit [Fintype p] in
/-- The column $(j, c)$ of the block Krylov matrix is column $c$ of $\mathbf{A}^j\mathbf{B}$. -/
@[simp]
theorem blockKrylovMatrix_apply (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) {q : ℕ} (i : n) (j : Fin q)
    (c : p) : blockKrylovMatrix A B q i (j, c) = (A ^ (j : ℕ) * B) i c :=
  rfl

/-- The **block Krylov space** $\mathcal{K}_q(\mathbf{A}, \mathbf{B}) =
\operatorname{range}[\mathbf{B}, \mathbf{A}\mathbf{B}, \dots, \mathbf{A}^{q-1}\mathbf{B}]$, the
column space of `blockKrylovMatrix A B q`; $\mathcal{K}_0 = \{\mathbf{0}\}$.
[Saad2003, §6.12]; [TroppWebber2023, §5.3]. -/
def blockKrylovSpace (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) : Submodule 𝕜 (n → 𝕜) :=
  LinearMap.range (blockKrylovMatrix A B q).mulVecLin

/-- The block Krylov space is the span of the vectors $\mathbf{A}^j\mathbf{b}_c$, $j < q$. -/
private theorem blockKrylovSpace_eq_span (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovSpace A B q =
      Submodule.span 𝕜 (Set.range fun jc : Fin q × p => A ^ (jc.1 : ℕ) *ᵥ B.col jc.2) := by
  rw [blockKrylovSpace, Matrix.range_mulVecLin]
  rfl

/-- The vector $\mathbf{A}^j\mathbf{b}_c$ lies in $\mathcal{K}_q(\mathbf{A}, \mathbf{B})$ for
$j < q$. -/
private theorem pow_mulVec_col_mem_blockKrylovSpace (A : Matrix n n 𝕜) (B : Matrix n p 𝕜)
    {q j : ℕ} (hj : j < q) (c : p) : A ^ j *ᵥ B.col c ∈ blockKrylovSpace A B q := by
  rw [blockKrylovSpace_eq_span]
  exact Submodule.subset_span ⟨(⟨j, hj⟩, c), rfl⟩

/-! ### Bridges to the vector Krylov API -/

/-- One column is the vector case: the block Krylov matrix of the one-column block
$\mathbf{b}$ is the vector Krylov matrix, with its columns reindexed by `Fin q × Unit`. -/
theorem blockKrylovMatrix_replicateCol (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    blockKrylovMatrix A (Matrix.replicateCol Unit b) q =
      (krylovMatrix A b q).submatrix id Prod.fst := by
  rfl

/-- The block Krylov space of a one-column block is the vector Krylov space:
$\mathcal{K}_q(\mathbf{A}, [\mathbf{b}]) = \mathcal{K}_q(\mathbf{A}, \mathbf{b})$. -/
theorem blockKrylovSpace_replicateCol (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    blockKrylovSpace A (Matrix.replicateCol Unit b) q = krylovSpace A b q := by
  rw [blockKrylovSpace_eq_span, krylovSpace_eq_span]
  exact congrArg _ (Prod.fst_surjective.range_comp fun j : Fin q => A ^ (j : ℕ) *ᵥ b)

/-- A block Krylov space is the sum of the Krylov spaces of its columns:
$\mathcal{K}_q(\mathbf{A}, \mathbf{B}) = \sum_c \mathcal{K}_q(\mathbf{A}, \mathbf{b}_c)$, with
$\mathbf{b}_c$ the columns of $\mathbf{B}$. Every vector Krylov bound transfers to block methods
through it. -/
theorem blockKrylovSpace_eq_iSup_krylovSpace (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovSpace A B q = ⨆ c, krylovSpace A (B.col c) q := by
  refine le_antisymm ?_ (iSup_le fun c => ?_)
  · rw [blockKrylovSpace_eq_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨j, c⟩, rfl⟩
    exact le_iSup (fun c => krylovSpace A (B.col c) q) c (pow_mulVec_mem_krylovSpace A _ j.isLt)
  · rw [krylovSpace_eq_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact pow_mulVec_col_mem_blockKrylovSpace A B j.isLt c

/-- The Krylov space of each column lies in the block Krylov space:
$\mathcal{K}_q(\mathbf{A}, \mathbf{b}_c) \subseteq \mathcal{K}_q(\mathbf{A}, \mathbf{B})$. -/
theorem krylovSpace_col_le_blockKrylovSpace (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ)
    (c : p) : krylovSpace A (B.col c) q ≤ blockKrylovSpace A B q := by
  rw [blockKrylovSpace_eq_iSup_krylovSpace]
  exact le_iSup (fun c => krylovSpace A (B.col c) q) c

/-! ### Structure -/

omit [Fintype p] in
/-- The first $q$ blocks of a longer block Krylov matrix form the shorter one. -/
theorem blockKrylovMatrix_submatrix_castLE (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) {q q' : ℕ}
    (h : q ≤ q') :
    (blockKrylovMatrix A B q').submatrix id (Prod.map (Fin.castLE h) id) =
      blockKrylovMatrix A B q := by
  rfl

/-- The block Krylov spaces increase with $q$. -/
theorem blockKrylovSpace_mono (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) :
    Monotone (blockKrylovSpace A B) := by
  intro q q' h
  rw [blockKrylovSpace_eq_span A B q]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨j, c⟩, rfl⟩
  exact pow_mulVec_col_mem_blockKrylovSpace A B (j.isLt.trans_le h) c

/-- The empty block Krylov space. -/
@[simp]
theorem blockKrylovSpace_zero (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) :
    blockKrylovSpace A B 0 = ⊥ := by
  rw [blockKrylovSpace_eq_span, Set.range_eq_empty, Submodule.span_empty]

/-- One block: $\mathcal{K}_1(\mathbf{A}, \mathbf{B}) = \operatorname{range}\mathbf{B}$. -/
theorem blockKrylovSpace_one (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) :
    blockKrylovSpace A B 1 = LinearMap.range B.mulVecLin := by
  rw [blockKrylovSpace_eq_span, Matrix.range_mulVecLin]
  have h : (fun jc : Fin 1 × p => A ^ (jc.1 : ℕ) *ᵥ B.col jc.2) = B.col ∘ Prod.snd := by
    funext ⟨j, c⟩
    rw [Fin.fin_one_eq_zero j, Fin.val_zero, pow_zero, Matrix.one_mulVec]
    rfl
  rw [h, Prod.snd_surjective.range_comp]

/-- One step adds one block: $\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{B}) =
\mathcal{K}_q(\mathbf{A}, \mathbf{B}) + \operatorname{range}(\mathbf{A}^q\mathbf{B})$. -/
theorem blockKrylovSpace_succ (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovSpace A B (q + 1) =
      blockKrylovSpace A B q ⊔ LinearMap.range (A ^ q * B).mulVecLin := by
  rw [blockKrylovSpace_eq_span, blockKrylovSpace_eq_span, Matrix.range_mulVecLin,
    ← Submodule.span_union]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_union, Prod.exists]
  constructor
  · rintro ⟨i, c, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl ⟨j, c, rfl⟩
    · exact Or.inr ⟨c, rfl⟩
  · rintro (⟨i, c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨i.castSucc, c, rfl⟩
    · exact ⟨Fin.last q, c, rfl⟩

/-- $\mathbf{A}\mathcal{K}_q(\mathbf{A}, \mathbf{B}) \subseteq \mathcal{K}_{q+1}(\mathbf{A},
\mathbf{B})$, the invariance a block Arnoldi relation rests on. -/
theorem mulVec_mem_blockKrylovSpace_succ {A : Matrix n n 𝕜} {B : Matrix n p 𝕜} {q : ℕ}
    {x : n → 𝕜} (hx : x ∈ blockKrylovSpace A B q) : A *ᵥ x ∈ blockKrylovSpace A B (q + 1) := by
  have hle : blockKrylovSpace A B q ≤ (blockKrylovSpace A B (q + 1)).comap A.mulVecLin := by
    rw [blockKrylovSpace_eq_span A B q]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨j, c⟩, rfl⟩
    change A *ᵥ (A ^ (j : ℕ) *ᵥ B.col c) ∈ blockKrylovSpace A B (q + 1)
    rw [Matrix.mulVec_mulVec, ← pow_succ']
    exact pow_mulVec_col_mem_blockKrylovSpace A B (Nat.succ_lt_succ j.isLt) c
  exact hle hx

/-- Shift invariance: $\mathcal{K}_q(\mathbf{A} + s\mathbf{I}, \mathbf{B}) =
\mathcal{K}_q(\mathbf{A}, \mathbf{B})$ for every real shift $s$. -/
theorem blockKrylovSpace_add_smul_one (A : Matrix n n 𝕜) (s : ℝ) (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovSpace (A + s • (1 : Matrix n n 𝕜)) B q = blockKrylovSpace A B q := by
  simp_rw [blockKrylovSpace_eq_iSup_krylovSpace, krylovSpace_add_smul_one]

omit [Fintype p] in
/-- **Block Krylov matrices under a change of variables**, for rectangular
$\mathbf{C} \in \Bbbk^{m \times n}$ and $\mathbf{D} \in \Bbbk^{n \times m}$:
$$\mathbf{K}_q(\mathbf{C}\mathbf{D}, \mathbf{C}\mathbf{B}) =
\mathbf{C}\,\mathbf{K}_q(\mathbf{D}\mathbf{C}, \mathbf{B})\,,$$
since $(\mathbf{C}\mathbf{D})^j\mathbf{C} = \mathbf{C}(\mathbf{D}\mathbf{C})^j$. At
$\mathbf{C} = \mathbf{A}$, $\mathbf{D} = \mathbf{A}^{\mathsf{H}}$ it is
$\mathbf{K}_q(\mathbf{A}\mathbf{A}^{\mathsf{H}}, \mathbf{A}\mathbf{\Omega}) =
\mathbf{A}\,\mathbf{K}_q(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{\Omega})$.
[TroppWebber2023, §5.3]. -/
theorem blockKrylovMatrix_mul_mul [DecidableEq m] (C : Matrix m n 𝕜) (D : Matrix n m 𝕜)
    (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovMatrix (C * D) (C * B) q = C * blockKrylovMatrix (D * C) B q := by
  ext i ⟨j, c⟩
  rw [blockKrylovMatrix_apply, ← Matrix.mul_assoc, Matrix.mul_pow_mul, Matrix.mul_assoc]
  rfl

/-- **Block Krylov spaces under a change of variables**:
$\mathcal{K}_q(\mathbf{C}\mathbf{D}, \mathbf{C}\mathbf{B}) =
\mathbf{C}\,\mathcal{K}_q(\mathbf{D}\mathbf{C}, \mathbf{B})$.
[TroppWebber2023, §5.3]. -/
theorem blockKrylovSpace_mul_mul [DecidableEq m] (C : Matrix m n 𝕜) (D : Matrix n m 𝕜)
    (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovSpace (C * D) (C * B) q = (blockKrylovSpace (D * C) B q).map C.mulVecLin := by
  rw [blockKrylovSpace, blockKrylovSpace, blockKrylovMatrix_mul_mul, Matrix.mulVecLin_mul,
    LinearMap.range_comp]

/-- The block Krylov matrix has rank at most the number of its columns,
$\operatorname{rank}\mathbf{K}_q(\mathbf{A}, \mathbf{B}) \le q\,\lvert p \rvert$. -/
theorem rank_blockKrylovMatrix_le (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) :
    (blockKrylovMatrix A B q).rank ≤ q * Fintype.card p := by
  simpa using (blockKrylovMatrix A B q).rank_le_card_width

/-! ### Polynomials -/

/-- **The polynomial description of the block Krylov space**: $\mathbf{x} \in
\mathcal{K}_q(\mathbf{A}, \mathbf{B})$ exactly when
$\mathbf{x} = \sum_c f_c(\mathbf{A})\mathbf{b}_c$ for polynomials $f_c \in \Bbbk[X]$ of degree
less than $q$, one per column $\mathbf{b}_c$ of $\mathbf{B}$. [Saad2003, §6.12]. -/
theorem mem_blockKrylovSpace_iff {A : Matrix n n 𝕜} {B : Matrix n p 𝕜} {q : ℕ} {x : n → 𝕜} :
    x ∈ blockKrylovSpace A B q ↔
      ∃ f : p → 𝕜[X], (∀ c, (f c).degree < q) ∧ ∑ c, aeval A (f c) *ᵥ B.col c = x := by
  constructor
  · intro hx
    have hx' : x ∈ ⨆ c ∈ Finset.univ, krylovSpace A (B.col c) q := by
      simpa [blockKrylovSpace_eq_iSup_krylovSpace] using hx
    obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ x).1 hx'
    choose f hf using fun c => mem_krylovSpace_iff.1 (μ c).2
    exact ⟨f, fun c => (hf c).1, Finset.sum_congr rfl fun c _ => (hf c).2⟩
  · rintro ⟨f, hf, rfl⟩
    exact Submodule.sum_mem _ fun c _ => krylovSpace_col_le_blockKrylovSpace A B q c
      (mem_krylovSpace_iff.2 ⟨f c, hf c, rfl⟩)

/-- A polynomial filter of degree less than $q$, with coefficients in any subfield, applied to the
block is a block Krylov combination: $f(\mathbf{A})\mathbf{B} = \mathbf{K}_q(\mathbf{A},
\mathbf{B})\,\mathbf{C}$ for some coefficient matrix $\mathbf{C}$. -/
theorem exists_aeval_mul_eq_blockKrylovMatrix_mul {R : Type*} [CommSemiring R] [Algebra R 𝕜]
    (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) {q : ℕ} {f : R[X]} (hf : f.degree < q) :
    ∃ C : Matrix (Fin q × p) p 𝕜, aeval A f * B = blockKrylovMatrix A B q * C := by
  choose v hv using fun c => krylovSpace_col_le_blockKrylovSpace A B q c
    (aeval_mulVec_mem_krylovSpace A (B.col c) hf)
  refine ⟨Matrix.of fun jc c => v c jc, ?_⟩
  ext i c
  exact (congrFun (hv c) i).symm

/-- **The range of a polynomial filter lies in the block Krylov space**: for $\deg f < q$,
$\operatorname{range}(f(\mathbf{A})\mathbf{B}) \subseteq \mathcal{K}_q(\mathbf{A}, \mathbf{B})$.
[TroppWebber2023, §9.3 (proof)]. -/
theorem range_aeval_mul_le_blockKrylovSpace {R : Type*} [CommSemiring R] [Algebra R 𝕜]
    (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) {q : ℕ} {f : R[X]} (hf : f.degree < q) :
    LinearMap.range (aeval A f * B).mulVecLin ≤ blockKrylovSpace A B q := by
  obtain ⟨C, hC⟩ := exists_aeval_mul_eq_blockKrylovMatrix_mul A B hf
  rw [hC, Matrix.mulVecLin_mul, LinearMap.range_comp]
  exact LinearMap.map_le_range

/-- The range of a filtered sketch lies in that of the block Krylov sketch: for $\deg f < q$ and
any left factor $\mathbf{C}$,
$\operatorname{range}(\mathbf{C}f(\mathbf{A})\mathbf{B}) \subseteq
\operatorname{range}(\mathbf{C}\mathbf{K}_q(\mathbf{A}, \mathbf{B}))$. -/
theorem range_mul_aeval_mul_le_range_mul_blockKrylovMatrix {R : Type*} [CommSemiring R]
    [Algebra R 𝕜] {l : Type*} (C : Matrix l n 𝕜) (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) {q : ℕ}
    {f : R[X]} (hf : f.degree < q) :
    LinearMap.range (C * aeval A f * B).mulVecLin ≤
      LinearMap.range (C * blockKrylovMatrix A B q).mulVecLin := by
  obtain ⟨D, hD⟩ := exists_aeval_mul_eq_blockKrylovMatrix_mul A B hf
  exact range_le_iff_exists_mul.mpr ⟨D, by rw [Matrix.mul_assoc, hD, Matrix.mul_assoc]⟩

end NLAlib

open Polynomial
open scoped Matrix

namespace NLAlib

/-- One level of the residual: if $\mathbf{w} = r\mathbf{g} - \mathbf{G}\mathbf{y}$, then $r^2$
times the squared norm of the part of $\mathbf{g}$ orthogonal to the columns of $\mathbf{G}$ is at
most $\|\mathbf{w}\|^2$. -/
private lemma norm_sq_mul_le_norm_sq_of_residual {m c : Type*} [Fintype m] [DecidableEq m]
    [Fintype c] (G : Matrix m c ℝ) (g w : m → ℝ) (r : ℝ) (y : c → ℝ)
    (hw : ∀ i, w i = r * g i - ∑ j, y j * G i j) :
    r ^ 2 * ‖WithLp.toLp 2 ((1 - rangeProjector G) *ᵥ g)‖ ^ 2 ≤ ‖WithLp.toLp 2 w‖ ^ 2 := by
  have hGy : (1 - rangeProjector G) *ᵥ (G *ᵥ y) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, rangeProjector_mulVec_mulVec, sub_self]
  have hwv : w = r • g - G *ᵥ y := by
    funext i
    simp [hw i, Matrix.mulVec, dotProduct, mul_comm]
  have hw' : (1 - rangeProjector G) *ᵥ w = r • ((1 - rangeProjector G) *ᵥ g) := by
    rw [hwv, Matrix.mulVec_sub, hGy, sub_zero, Matrix.mulVec_smul]
  have hsc : ∀ v : m → ℝ, ‖WithLp.toLp 2 (r • v)‖ ^ 2 = r ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 := by
    intro v
    rw [WithLp.toLp_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hpy := (isStarProjection_rangeProjector G).norm_toLp_sq_eq_add w
  rw [← hsc, ← hw']
  linarith [sq_nonneg ‖WithLp.toLp 2 (rangeProjector G *ᵥ w)‖]

/-- **Level decomposition of a Krylov residual**: let
$\mathbf{D} = \operatorname{diag}(\mathbf{d})$, $\mathbf{g} \in \mathbb{R}^n$ and
$\mathbf{G} \in \mathbb{R}^{n \times c}$. For every $\mathbf{x}$ in
$\mathcal{K}_s(\mathbf{D}, [\mathbf{g}, \mathbf{G}])$ there is a real $r$ with $\deg r \le s$ and
$r(0) = 1$ such that
$$\sum_{t} r(t)^2\,\bigl\|(\mathbf{I} - \mathbf{P}_{\mathbf{G}_t})\,\mathbf{g}_t\bigr\|^2 \le
\|\mathbf{g} - \mathbf{D}\mathbf{x}\|^2 \,,$$
the sum over the distinct values $t$ of $\mathbf{d}$, with $\mathbf{g}_t$, $\mathbf{G}_t$ the rows
$\{i : d_i = t\}$ of $\mathbf{g}$, $\mathbf{G}$ and $\mathbf{P}_{\mathbf{G}_t}$ the projector onto
the range of $\mathbf{G}_t$.
[Shamir2026, Section 3.3]; there in the proof of Theorem 1, with $r = 1 - p_0$. -/
theorem exists_sum_eval_sq_mul_norm_sq_le_norm_sub_mulVec_sq {n c : Type*} [Fintype n]
    [DecidableEq n] [Fintype c] (d g : n → ℝ) (G : Matrix n c ℝ) {s : ℕ} {x : n → ℝ}
    (hx : x ∈ blockKrylovSpace (Matrix.diagonal d)
      (Matrix.fromCols (Matrix.replicateCol Unit g) G) s) :
    ∃ r : ℝ[X], r.degree ≤ s ∧ r.eval 0 = 1 ∧
      ∑ t ∈ Finset.univ.image d, r.eval t ^ 2 *
          ‖WithLp.toLp 2 ((1 - rangeProjector (G.submatrix (Subtype.val : {i // d i = t} → n) id))
            *ᵥ fun i => g i.1)‖ ^ 2 ≤
        ‖WithLp.toLp 2 (g - Matrix.diagonal d *ᵥ x)‖ ^ 2 := by
  obtain ⟨f, hf, hsum⟩ := mem_blockKrylovSpace_iff.1 hx
  have hxi : ∀ i, x i = (f (Sum.inl ())).eval (d i) * g i +
      ∑ j, (f (Sum.inr j)).eval (d i) * G i j := by
    intro i
    rw [← hsum]
    simp [Fintype.sum_sum_type, aeval_diagonal_self, Matrix.mulVec_diagonal]
  have hdeg : (1 - X * f (Sum.inl ())).degree ≤ (s : WithBot ℕ) := by
    refine (degree_sub_le _ _).trans (max_le ?_ ?_)
    · simp
    · rw [degree_mul, degree_X, add_comm]
      have h := hf (Sum.inl ())
      rcases hd : (f (Sum.inl ())).degree with _ | k
      · exact le_trans (le_of_eq (WithBot.bot_add _)) bot_le
      · rw [hd] at h
        have hk : k < s := WithBot.coe_lt_coe.mp h
        exact WithBot.coe_le_coe.mpr (Nat.succ_le_of_lt hk)
  have hres : ∀ i, (g - Matrix.diagonal d *ᵥ x) i = (1 - X * f (Sum.inl ())).eval (d i) * g i -
      ∑ j, (X * f (Sum.inr j)).eval (d i) * G i j := by
    intro i
    rw [Pi.sub_apply, Matrix.mulVec_diagonal, hxi i]
    simp only [eval_sub, eval_mul, eval_X, eval_one, Finset.mul_sum, sub_mul, one_mul, mul_add]
    simp only [mul_assoc]
    ring
  refine ⟨1 - X * f (Sum.inl ()), hdeg, by simp, ?_⟩
  rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_fiberwise_of_maps_to (g := d)
    (t := Finset.univ.image d) (fun i _ => Finset.mem_image_of_mem d (Finset.mem_univ i))]
  refine Finset.sum_le_sum fun t _ => ?_
  have hfib := norm_sq_mul_le_norm_sq_of_residual
    (G.submatrix (Subtype.val : {i // d i = t} → n) id) (fun i => g i.1)
    (fun i => (g - Matrix.diagonal d *ᵥ x) i.1) ((1 - X * f (Sum.inl ())).eval t)
    (fun j => (X * f (Sum.inr j)).eval t)
    (fun i => by simp only [hres i.1, i.2, Matrix.submatrix_apply, id_eq])
  refine hfib.trans (le_of_eq ?_)
  rw [EuclideanSpace.real_norm_sq_eq]
  exact (Finset.sum_subtype (Finset.univ.filter fun i => d i = t) (by simp)
    (fun i => (WithLp.toLp 2 (g - Matrix.diagonal d *ᵥ x)).ofLp i ^ 2)).symm

/-- A block Krylov space depends on its starting block only through the range: if the range of
$\mathbf{B}$ lies in that of $\mathbf{B}'$, then $\mathcal{K}_q(\mathbf{A}, \mathbf{B}) \subseteq
\mathcal{K}_q(\mathbf{A}, \mathbf{B}')$ for every $q$. -/
theorem blockKrylovSpace_le_of_range_le {𝕜 : Type*} [RCLike 𝕜] {n p p' : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [Fintype p'] {A : Matrix n n 𝕜} {B : Matrix n p 𝕜}
    {B' : Matrix n p' 𝕜} (h : LinearMap.range B.mulVecLin ≤ LinearMap.range B'.mulVecLin)
    (q : ℕ) : blockKrylovSpace A B q ≤ blockKrylovSpace A B' q := by
  classical
  rw [blockKrylovSpace_eq_iSup_krylovSpace]
  refine iSup_le fun c => ?_
  intro x hx
  obtain ⟨f, hf, rfl⟩ := mem_krylovSpace_iff.1 hx
  have hc : B.col c ∈ LinearMap.range B'.mulVecLin := h (by
    refine ⟨Pi.single c 1, ?_⟩
    rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_single_one B c])
  obtain ⟨y, hy⟩ := hc
  rw [Matrix.mulVecLin_apply] at hy
  have hsum : B' *ᵥ y = ∑ c', y c' • B'.col c' := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  refine mem_blockKrylovSpace_iff.2 ⟨fun c' => y c' • f, fun c' => ?_, ?_⟩
  · exact (Polynomial.degree_smul_le _ _).trans_lt hf
  · rw [← hy, hsum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [map_smul, Matrix.smul_mulVec, Matrix.mulVec_smul]

/-- One pass raises the Krylov depth by one: if a subspace $\mathcal{L}$ lies in
$\mathcal{K}_{s+1}(\mathbf{A}, \mathbf{B})$ and $\mathcal{V} \subseteq \mathcal{L} +
\operatorname{range}\mathbf{B}$, then
$$\mathcal{L} + \mathcal{V} + \mathbf{A}\mathcal{V} \subseteq \mathcal{K}_{s+2}(\mathbf{A},
\mathbf{B}) \,.$$
The depth count of the Krylov coupling: $\mathcal{L}$ is what the earlier passes revealed,
$\mathcal{V}$ the rotated queries of the next pass and $\mathbf{A}\mathcal{V}$ their products. -/
theorem sup_sup_map_mulVecLin_le_blockKrylovSpace_add_two {𝕜 : Type*} [RCLike 𝕜] {n p : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] {A : Matrix n n 𝕜} {B : Matrix n p 𝕜} {s : ℕ}
    {L V : Submodule 𝕜 (n → 𝕜)} (hL : L ≤ blockKrylovSpace A B (s + 1))
    (hV : V ≤ L ⊔ LinearMap.range B.mulVecLin) :
    L ⊔ V ⊔ V.map A.mulVecLin ≤ blockKrylovSpace A B (s + 2) := by
  have h1 : blockKrylovSpace A B (s + 1) ≤ blockKrylovSpace A B (s + 2) :=
    blockKrylovSpace_mono A B (by omega)
  have hB : LinearMap.range B.mulVecLin ≤ blockKrylovSpace A B (s + 1) := by
    rw [← blockKrylovSpace_one A B]
    exact blockKrylovSpace_mono A B (by omega)
  have hV' : V ≤ blockKrylovSpace A B (s + 1) := hV.trans (sup_le hL hB)
  refine sup_le (sup_le (hL.trans h1) (hV'.trans h1)) ?_
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  exact mulVec_mem_blockKrylovSpace_succ (hV' hx)

/-- **The block Krylov space of a block Krylov matrix**: starting from the block
$\mathbf{K}_{s+1}(\mathbf{A}, \mathbf{B}) = [\mathbf{B}, \mathbf{A}\mathbf{B}, \dots,
\mathbf{A}^{s}\mathbf{B}]$ and taking $q + 1$ blocks gives the block Krylov space of
$\mathbf{B}$ with $s + q + 1$ blocks,
$$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{K}_{s+1}(\mathbf{A}, \mathbf{B})) =
\mathcal{K}_{s+q+1}(\mathbf{A}, \mathbf{B})\,,$$
for every $s, q \ge 0$: a block method with block $\mathbf{B}$ and depth $s + q + 1$ is the
same method with the simulated block $\mathbf{K}_{s+1}(\mathbf{A}, \mathbf{B})$ and depth
$q + 1$. With no block on either side the identity fails ($\mathcal{K}_{q}(\mathbf{A},
\mathbf{K}_0) = \{\mathbf{0}\}$). -/
theorem blockKrylovSpace_blockKrylovMatrix {𝕜 : Type*} [RCLike 𝕜] {n p : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (s q : ℕ) :
    blockKrylovSpace A (blockKrylovMatrix A B (s + 1)) (q + 1) =
      blockKrylovSpace A B (s + q + 1) := by
  refine le_antisymm ?_ ?_
  · rw [blockKrylovSpace_eq_span A (blockKrylovMatrix A B (s + 1))]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨i, j, c⟩, rfl⟩
    have h : A ^ (i : ℕ) *ᵥ (blockKrylovMatrix A B (s + 1)).col (j, c) =
        A ^ ((i : ℕ) + (j : ℕ)) *ᵥ B.col c := by
      rw [pow_add, ← Matrix.mulVec_mulVec]
      rfl
    change A ^ (i : ℕ) *ᵥ (blockKrylovMatrix A B (s + 1)).col (j, c) ∈
      blockKrylovSpace A B (s + q + 1)
    rw [h]
    exact pow_mulVec_col_mem_blockKrylovSpace A B (by omega) c
  · rw [blockKrylovSpace_eq_span A B]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨k, c⟩, rfl⟩
    obtain ⟨i, j, hi, hj, hij⟩ : ∃ i j, i < q + 1 ∧ j < s + 1 ∧ i + j = (k : ℕ) := by
      rcases le_total (k : ℕ) q with h | h
      · exact ⟨k, 0, by omega, by omega, by omega⟩
      · exact ⟨q, k - q, by omega, by omega, by omega⟩
    change A ^ (k : ℕ) *ᵥ B.col c ∈ blockKrylovSpace A (blockKrylovMatrix A B (s + 1)) (q + 1)
    rw [← hij, pow_add, ← Matrix.mulVec_mulVec]
    exact pow_mulVec_col_mem_blockKrylovSpace A (blockKrylovMatrix A B (s + 1)) hi (⟨j, hj⟩, c)

end NLAlib
