/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.BandGolubKahanRun
public import NLAlib.Krylov.GolubKahan.Band.Alg

/-!
# The stored blocks of the block Golub–Kahan program are a run of the process

The program `NLAlib.Krylov.GolubKahan.Band.solve` stores its coefficients packed by block column:
block column $j$ of the left coefficients is a $(jb + b) \times b$ matrix and block column $j$ of
the right coefficients a $((j+1)b + b) \times b$ matrix. The pure relations
`NLAlib.IsBlockGolubKahan` and `NLAlib.IsBlockGolubKahanErr` speak of the global matrices
$\mathbf{R}$ ($qb \times qb$) and $\mathbf{S}$ ($(q+1)b \times qb$), zero below the written part of
every block column. This file assembles the packed block columns into the global matrices and
shows that the postcondition of the program, the stored-run predicates, gives the pure
relations. The theorems about the process then hold of the stored output.

Conventions. The start block of a stored run is an extension of the prefix of zero blocks of
$\mathbf{V}$, as in the pure relations. A stored rounded run bounds the error of a computed
product column by column, $\|\mathbf{A}\mathbf{x}_c - \mathbf{w}_c\| \le \delta\|\mathbf{x}_c\|$,
the form delivered by one product per column; it is the product clause of
`NLAlib.IsBlockGolubKahanErr` for every $\varepsilon_{\mathrm{mv}}$ with
$\delta \le \varepsilon_{\mathrm{mv}}\|\mathbf{A}\|_2$. Design:
`docs/design/LowRank-BlockLanczos.md` §4.1–4.3.

## Main definitions

* `NLAlib.Krylov.GolubKahan.Band.coefEntry`, `NLAlib.Krylov.GolubKahan.Band.assembleCoef`: the
  global coefficient matrix of packed block columns, zero outside the written part.
* `NLAlib.Krylov.GolubKahan.Band.assembleLeft`, `NLAlib.Krylov.GolubKahan.Band.assembleRight`: the
  global matrices $\mathbf{R}$ and $\mathbf{S}$ of a stored run.

## Main results

* `NLAlib.Krylov.GolubKahan.Band.blockCols_assembleCoef_apply`,
  `NLAlib.Krylov.GolubKahan.Band.blockRowPrefix_blockCols_assembleCoef`,
  `NLAlib.Krylov.GolubKahan.Band.blockRows_blockCols_assembleCoef`,
  `NLAlib.Krylov.GolubKahan.Band.blockCols_assembleCoef_apply_eq_zero`: the block columns of the
  assembled matrix are the packed ones.
* `NLAlib.Krylov.GolubKahan.Band.norm_col_sub_mul_le_of_norm_mulVec_col_sub_le`: the product
  error of a stored run in the form of the pure relation.
* `NLAlib.Krylov.GolubKahan.Band.IsExactStoredRun.isBlockGolubKahan`,
  `NLAlib.Krylov.GolubKahan.Band.IsRoundedStoredRun.isBlockGolubKahanErr`: the two bridges.
* `NLAlib.Krylov.GolubKahan.Band.IsExactStoredRun.mul_conjTranspose_mul_conjTranspose_eq_rsvd`,
  `NLAlib.Krylov.GolubKahan.Band.StoredOut.mul_conjTranspose_mul_conjTranspose_eq_rsvd`: the
  stored factors of an exact run are the randomized SVD approximation at the block Krylov matrix.
* `NLAlib.Krylov.GolubKahan.Band.IsRoundedStoredRun.frobNorm_gramDefect_left_le`,
  `NLAlib.Krylov.GolubKahan.Band.IsRoundedStoredRun.frobNorm_gramDefect_right_le`: orthogonality
  of the stored bases of a rounded run.
* `NLAlib.Krylov.GolubKahan.Band.IsRoundedStoredRun.specNorm_sub_mul_transpose_mul_transpose_le`,
  `NLAlib.Krylov.GolubKahan.Band.IsRoundedStoredRun.frobNorm_sub_mul_transpose_mul_transpose_le`:
  the forward bound for the stored factors of a rounded run.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.GolubKahan.Band

open Ops

/-! ### Assembly of the packed coefficients -/

section Assemble

variable {𝕜 : Type} [RCLike 𝕜] {p : ℕ → ℕ}

/-- The entry in row $i$ and column $c$ of block column $j$ of packed coefficients, where block
column $j$ is a matrix $\mathbf{C}_j$ with $p_j b + b$ rows and $b$ columns: the entry of
$\mathbf{C}_j$ if $i < p_j b + b$ and $c < b$, and zero otherwise. -/
def coefEntry (b : ℕ) (C : (j : ℕ) → Matrix (Fin (p j * b + b)) (Fin b) 𝕜) (j i c : ℕ) : 𝕜 :=
  if h : i < p j * b + b ∧ c < b then C j ⟨i, h.1⟩ ⟨c, h.2⟩ else 0

/-- **The global coefficient matrix of packed block columns.** Block column $j$ of the packed
coefficients is a matrix $\mathbf{C}_j$ with $p_j b + b$ rows and $b$ columns. The assembled
matrix with $M$ rows and $N$ columns has, in its column $d = jb + c$ with $c < b$, the column $c$
of $\mathbf{C}_j$ in its first $p_j b + b$ rows and zero below. -/
def assembleCoef (b : ℕ) (C : (j : ℕ) → Matrix (Fin (p j * b + b)) (Fin b) 𝕜) {M N : ℕ} :
    Matrix (Fin M) (Fin N) 𝕜 :=
  Matrix.of fun i d => coefEntry b C ((d : ℕ) / b) i ((d : ℕ) % b)

/-- The global coefficient matrix $\mathbf{R}$ ($qb \times qb$) of the left steps of a stored
run: its block column $j$ is the packed $(jb + b) \times b$ block $\mathbf{R}_j$ in the rows
$0, \dots, jb + b - 1$ and zero below. -/
def assembleLeft (b q : ℕ) (R : (j : ℕ) → Matrix (Fin (j * b + b)) (Fin b) 𝕜) :
    Matrix (Fin (q * b)) (Fin (q * b)) 𝕜 :=
  assembleCoef b R

/-- The global coefficient matrix $\mathbf{S}$ ($(q+1)b \times qb$) of the right steps of a
stored run: its block column $j$ is the packed $((j+1)b + b) \times b$ block $\mathbf{S}_j$ in
the rows $0, \dots, (j+1)b + b - 1$ and zero below. -/
def assembleRight (b q : ℕ) (S : (j : ℕ) → Matrix (Fin ((j + 1) * b + b)) (Fin b) 𝕜) :
    Matrix (Fin ((q + 1) * b)) (Fin (q * b)) 𝕜 :=
  assembleCoef b S

variable {b M q j : ℕ}

/-- Block column $j < q$ of the assembled coefficient matrix with $qb$ columns is the packed
block column $j$, extended by zero: its entry $(i, c)$ is the entry $(i, c)$ of $\mathbf{C}_j$
if $i < p_j b + b$ and zero otherwise. -/
theorem blockCols_assembleCoef_apply (C : (j : ℕ) → Matrix (Fin (p j * b + b)) (Fin b) 𝕜)
    (hj : j < q) (i : Fin M) (c : Fin b) :
    blockCols b (assembleCoef b C : Matrix (Fin M) (Fin (q * b)) 𝕜) j i c =
      coefEntry b C j i c := by
  have hb : 0 < b := c.pos
  have hd : j * b + (c : ℕ) < q * b :=
    calc j * b + (c : ℕ) < j * b + b := Nat.add_lt_add_left c.isLt _
      _ = (j + 1) * b := (Nat.succ_mul j b).symm
      _ ≤ q * b := Nat.mul_le_mul_right b hj
  have hdiv : (j * b + (c : ℕ)) / b = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt c.isLt, Nat.zero_add]
  have hmod : (j * b + (c : ℕ)) % b = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt c.isLt]
  simp only [blockCols, assembleCoef, Matrix.of_apply, dif_pos hd, hdiv, hmod]

/-- The first $p_j$ row blocks of block column $j < q$ of the assembled coefficient matrix are
the upper part of the packed block column $\mathbf{C}_j$, the coefficients against the old
columns, if the assembled matrix has at least $p_j b$ rows. -/
theorem blockRowPrefix_blockCols_assembleCoef
    (C : (j : ℕ) → Matrix (Fin (p j * b + b)) (Fin b) 𝕜) (hj : j < q) (hM : p j * b ≤ M) :
    blockRowPrefix b (blockCols b (assembleCoef b C : Matrix (Fin M) (Fin (q * b)) 𝕜) j) (p j) =
      coefTop (C j) := by
  ext r c
  have hr : (r : ℕ) < M := lt_of_lt_of_le r.isLt hM
  have hr' : (r : ℕ) < p j * b + b ∧ (c : ℕ) < b := ⟨Nat.lt_add_right b r.isLt, c.isLt⟩
  simp only [blockRowPrefix, Matrix.of_apply, dif_pos hr, blockCols_assembleCoef_apply C hj,
    coefEntry, dif_pos hr', coefTop, Matrix.submatrix_apply, id_eq]
  rfl

/-- Row block $p_j$ of block column $j < q$ of the assembled coefficient matrix is the lower
part of the packed block column $\mathbf{C}_j$, the coefficients against the new columns, if the
assembled matrix has at least $p_j b + b$ rows. -/
theorem blockRows_blockCols_assembleCoef
    (C : (j : ℕ) → Matrix (Fin (p j * b + b)) (Fin b) 𝕜) (hj : j < q) (hM : p j * b + b ≤ M) :
    blockRows b (blockCols b (assembleCoef b C : Matrix (Fin M) (Fin (q * b)) 𝕜) j) (p j) =
      coefBot (C j) := by
  ext r c
  have hr : p j * b + (r : ℕ) < M := lt_of_lt_of_le (Nat.add_lt_add_left r.isLt _) hM
  have hr' : p j * b + (r : ℕ) < p j * b + b ∧ (c : ℕ) < b :=
    ⟨Nat.add_lt_add_left r.isLt _, c.isLt⟩
  simp only [blockRows, Matrix.of_apply, dif_pos hr, blockCols_assembleCoef_apply C hj,
    coefEntry, dif_pos hr', coefBot, Matrix.submatrix_apply, id_eq]
  rfl

/-- Block column $j < q$ of the assembled coefficient matrix is zero below the written part: its
entry $(i, c)$ is zero for $i \ge p_j b + b$. -/
theorem blockCols_assembleCoef_apply_eq_zero
    (C : (j : ℕ) → Matrix (Fin (p j * b + b)) (Fin b) 𝕜) (hj : j < q) (i : Fin M) (c : Fin b)
    (hi : p j * b + b ≤ (i : ℕ)) :
    blockCols b (assembleCoef b C : Matrix (Fin M) (Fin (q * b)) 𝕜) j i c = 0 := by
  rw [blockCols_assembleCoef_apply C hj, coefEntry, dif_neg fun h => absurd h.1 (Nat.not_lt.2 hi)]

end Assemble

/-! ### The product error -/

/-- The product error of a stored run in the form of the pure relation. If every column
$\mathbf{w}_c$ of $\mathbf{W}$ satisfies $\|\mathbf{A}\mathbf{x}_c - \mathbf{w}_c\| \le
\delta\|\mathbf{x}_c\|$, with $\mathbf{x}_c$ the column $c$ of $\mathbf{X}$, and
$\delta \le \delta_1$, then $\|(\mathbf{W} - \mathbf{A}\mathbf{X})\mathbf{e}_c\| \le
\delta_1\|\mathbf{X}\mathbf{e}_c\|$ for every column $c$. -/
theorem norm_col_sub_mul_le_of_norm_mulVec_col_sub_le {m n b : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {X : Matrix (Fin n) (Fin b) ℝ} {W : Matrix (Fin m) (Fin b) ℝ} {δ δ₁ : ℝ}
    (h : ∀ c, ‖WithLp.toLp 2 (A *ᵥ X.col c - W.col c)‖ ≤ δ * ‖WithLp.toLp 2 (X.col c)‖)
    (hδ : δ ≤ δ₁) (c : Fin b) :
    ‖WithLp.toLp 2 ((W - A * X).col c)‖ ≤ δ₁ * ‖WithLp.toLp 2 (X.col c)‖ := by
  have hc : (W - A * X).col c = -(A *ᵥ X.col c - W.col c) := by
    ext i
    simp only [Matrix.col_apply, Matrix.sub_apply, Pi.neg_apply, Pi.sub_apply, neg_sub]
    rfl
  rw [hc, WithLp.toLp_neg, norm_neg]
  exact (h c).trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))

/-! ### The bridges -/

variable {m n b q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {Ω : Matrix (Fin n) (Fin b) ℝ}
  {U : Matrix (Fin m) (Fin (q * b)) ℝ} {V : Matrix (Fin n) (Fin ((q + 1) * b)) ℝ}
  {G : Matrix (Fin b) (Fin b) ℝ} {R : (j : ℕ) → Matrix (Fin (j * b + b)) (Fin b) ℝ}
  {S : (j : ℕ) → Matrix (Fin ((j + 1) * b + b)) (Fin b) ℝ}

/-- **The stored blocks of an exact run are a run of the process.** If the bases $\mathbf{U}$,
$\mathbf{V}$, the start coefficients $\mathbf{G}$ and the packed coefficient block columns
$\mathbf{R}_j$, $\mathbf{S}_j$ are the stored blocks of an exact run for $\mathbf{A}$ from
$\mathbf{\Omega}$, then $\mathbf{U}$, $\mathbf{V}$, $\mathbf{G}$ and the assembled global
matrices $\mathbf{R}$, $\mathbf{S}$ are related to $\mathbf{A}$, $\mathbf{\Omega}$, $q$ by block
Golub–Kahan bidiagonalization with full reorthogonalization in exact arithmetic. -/
theorem IsExactStoredRun.isBlockGolubKahan (h : IsExactStoredRun A b q Ω U V G R S) :
    IsBlockGolubKahan A Ω q U V G (assembleLeft b q R) (assembleRight b q S) := by
  refine ⟨h.start, fun j hj => ?_, fun j hj => ?_, fun j hj i c hi => ?_, fun j hj i c hi => ?_⟩
  · obtain ⟨W, hW, hE⟩ := h.left j hj
    have hW' : W = A * blockCols b V j := hW
    rw [assembleLeft, blockRowPrefix_blockCols_assembleCoef R hj (Nat.mul_le_mul_right b hj.le),
      blockRows_blockCols_assembleCoef R hj
        ((Nat.succ_mul j b).symm.trans_le (Nat.mul_le_mul_right b hj)), ← hW']
    exact hE
  · obtain ⟨W, hW, hE⟩ := h.right j hj
    have hW' : W = Aᴴ * blockCols b U j := hW
    rw [assembleRight,
      blockRowPrefix_blockCols_assembleCoef S hj (Nat.mul_le_mul_right b (by omega)),
      blockRows_blockCols_assembleCoef S hj
        ((Nat.succ_mul (j + 1) b).symm.trans_le (Nat.mul_le_mul_right b (by omega))), ← hW']
    exact hE
  · exact blockCols_assembleCoef_apply_eq_zero R hj i c ((Nat.succ_mul j b).ge.trans hi)
  · exact blockCols_assembleCoef_apply_eq_zero S hj i c ((Nat.succ_mul (j + 1) b).ge.trans hi)

/-- **The stored blocks of a rounded run are a rounded run of the process.** If the bases
$\mathbf{U}$, $\mathbf{V}$, the start coefficients $\mathbf{G}$ and the packed coefficient block
columns $\mathbf{R}_j$, $\mathbf{S}_j$ are the stored blocks of a rounded run for $\mathbf{A}$
from $\mathbf{\Omega}$ with product allowances $\delta$, $\delta'$ and extension parameters
$(\eta_0, \mu, \varepsilon)$, and $\delta, \delta' \le \varepsilon_{\mathrm{mv}}\|\mathbf{A}\|_2$,
then $\mathbf{U}$, $\mathbf{V}$, $\mathbf{G}$ and the assembled global matrices $\mathbf{R}$,
$\mathbf{S}$ are related to $\mathbf{A}$, $\mathbf{\Omega}$, $q$ by the rounded process with
parameters $(\eta_0, \mu, \varepsilon)$ and $\varepsilon_{\mathrm{mv}}$. -/
theorem IsRoundedStoredRun.isBlockGolubKahanErr {δ δ' η₀ μ ε εmv : ℝ}
    (h : IsRoundedStoredRun A δ δ' η₀ μ ε b q Ω U V G R S) (hδ : δ ≤ εmv * specNorm A)
    (hδ' : δ' ≤ εmv * specNorm A) :
    IsBlockGolubKahanErr η₀ μ ε εmv A Ω q U V G (assembleLeft b q R) (assembleRight b q S) := by
  refine ⟨h.start, fun j hj => ?_, fun j hj => ?_, fun j hj i c hi => ?_, fun j hj i c hi => ?_⟩
  · obtain ⟨W, hW, hE⟩ := h.left j hj
    refine ⟨W, norm_col_sub_mul_le_of_norm_mulVec_col_sub_le hW hδ, ?_⟩
    rw [assembleLeft, blockRowPrefix_blockCols_assembleCoef R hj (Nat.mul_le_mul_right b hj.le),
      blockRows_blockCols_assembleCoef R hj
        ((Nat.succ_mul j b).symm.trans_le (Nat.mul_le_mul_right b hj))]
    exact hE
  · obtain ⟨W, hW, hE⟩ := h.right j hj
    have hW' : ∀ c, ‖WithLp.toLp 2 (Aᵀ *ᵥ (blockCols b U j).col c - W.col c)‖ ≤
        δ' * ‖WithLp.toLp 2 ((blockCols b U j).col c)‖ := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hW
    refine ⟨W, norm_col_sub_mul_le_of_norm_mulVec_col_sub_le hW' hδ', ?_⟩
    rw [assembleRight,
      blockRowPrefix_blockCols_assembleCoef S hj (Nat.mul_le_mul_right b (by omega)),
      blockRows_blockCols_assembleCoef S hj
        ((Nat.succ_mul (j + 1) b).symm.trans_le (Nat.mul_le_mul_right b (by omega)))]
    exact hE
  · exact blockCols_assembleCoef_apply_eq_zero R hj i c ((Nat.succ_mul j b).ge.trans hi)
  · exact blockCols_assembleCoef_apply_eq_zero S hj i c ((Nat.succ_mul (j + 1) b).ge.trans hi)

/-! ### The stored output of an exact run -/

/-- The stored factors of an exact run are the randomized SVD approximation at the block Krylov
matrix: if $\mathbf{U}$, $\mathbf{V}$ and the packed coefficient block columns $\mathbf{S}_j$ are
stored blocks of an exact run for $\mathbf{A}$ from $\mathbf{\Omega}$, and $\mathbf{S}$ is the
assembled $(q+1)b \times qb$ matrix, then
$$\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}} =
\mathsf{rsvd}(\mathbf{A}, \mathbf{K}_q), \qquad
\mathbf{K}_q = [\mathbf{\Omega}, \mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}, \dots,
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{q-1}\mathbf{\Omega}],$$
for every $\mathbf{A}$ and $\mathbf{\Omega}$ and every exact orthogonalization scheme. -/
theorem IsExactStoredRun.mul_conjTranspose_mul_conjTranspose_eq_rsvd
    (h : IsExactStoredRun A b q Ω U V G R S) :
    U * (assembleRight b q S)ᴴ * Vᴴ = rsvd A (blockKrylovMatrix (Aᴴ * A) Ω q) :=
  h.isBlockGolubKahan.mul_conjTranspose_mul_conjTranspose_eq_rsvd

/-- The output words of the program under the exact contracts decode to the randomized SVD
approximation at the block Krylov matrix. If the tape window `ω` and the words `us`, `vs`, `gs`,
`rs`, `ss` of the five output blocks decode to an exact run for $\mathbf{A}$, with
$\mathbf{\Omega}$, $\mathbf{U}$, $\mathbf{V}$ the decoded `ω`, `us`, `vs` and $\mathbf{S}$
assembled from the packed block columns decoded from `ss`, then
$\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}} = \mathsf{rsvd}(\mathbf{A},
[\mathbf{\Omega}, \mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}, \dots,
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{q-1}\mathbf{\Omega}])$. -/
theorem StoredOut.mul_conjTranspose_mul_conjTranspose_eq_rsvd {K : Type} [Inhabited K]
    {dec : K → ℝ} {ω us vs gs rs ss : List K}
    (h : StoredOut dec m n b q (IsExactStoredRun A b q) ω us vs gs rs ss) :
    decodeMatrix dec m (q * b) us *
        (assembleRight b q fun j =>
          decodeMatrix dec ((j + 1) * b + b) b (ss.drop (coefOffsetS b j)))ᴴ *
        (decodeMatrix dec n ((q + 1) * b) vs)ᴴ =
      rsvd A (blockKrylovMatrix (Aᴴ * A) (decodeMatrix dec n b ω) q) :=
  IsExactStoredRun.mul_conjTranspose_mul_conjTranspose_eq_rsvd h

/-! ### The stored output of a rounded run -/

section Rounded

variable {δ δ' η₀ μ ε εmv : ℝ}

/-- Orthogonality of the stored left basis of a rounded run on its nonzero columns. Let
$\mathbf{U}$ ($qb$ columns) be the left basis of a stored rounded run with extension parameters
$(\eta_0, \mu, \varepsilon)$ and $\mathbf{D} = \mathbf{U}^{\mathsf{T}}\mathbf{U} -
\operatorname{diag}(\mathbf{s})$ its Gram defect on the support ($s_c = 0$ at a zero column,
$s_c = 1$ otherwise). If $\mu \ge 0$ and $\sqrt{3qb}\,\mu \le \eta_0$ then
$\|\mathbf{D}\|_{\mathsf{F}} \le \sqrt{3qb}\,\mu$, for all product allowances. -/
theorem IsRoundedStoredRun.frobNorm_gramDefect_left_le
    (h : IsRoundedStoredRun A δ δ' η₀ μ ε b q Ω U V G R S) (hμ : 0 ≤ μ)
    (hw : Real.sqrt (3 * q * b) * μ ≤ η₀) :
    frobNorm (gramDefect U) ≤ Real.sqrt (3 * q * b) * μ := by
  choose P _ hE using h.left
  have h0 := frobNorm_gramDefect_le_of_blocks U (fun j => if hj : j < q then P j hj else 0)
    (fun j => coefTop (R j)) (fun j => coefBot (R j)) hμ hw
    (fun j hj => by simp only [dif_pos hj]; exact hE j hj) (le_refl q)
  rwa [blockPrefix_self] at h0

/-- Orthogonality of the stored right basis of a rounded run on its nonzero columns. Let
$\mathbf{V}$ ($(q+1)b$ columns) be the right basis of a stored rounded run with extension
parameters $(\eta_0, \mu, \varepsilon)$ and $\mathbf{D} = \mathbf{V}^{\mathsf{T}}\mathbf{V} -
\operatorname{diag}(\mathbf{s})$ its Gram defect on the support ($s_c = 0$ at a zero column,
$s_c = 1$ otherwise). If $\mu \ge 0$ and $\sqrt{3(q+1)b}\,\mu \le \eta_0$ then
$\|\mathbf{D}\|_{\mathsf{F}} \le \sqrt{3(q+1)b}\,\mu$, for all product allowances. -/
theorem IsRoundedStoredRun.frobNorm_gramDefect_right_le
    (h : IsRoundedStoredRun A δ δ' η₀ μ ε b q Ω U V G R S) (hμ : 0 ≤ μ)
    (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) :
    frobNorm (gramDefect V) ≤ Real.sqrt (3 * (q + 1 : ℕ) * b) * μ := by
  choose P _ hE using h.right
  have h0 := frobNorm_gramDefect_le_of_blocks (q := q + 1) V
    (fun j => match j with
      | 0 => Ω
      | j + 1 => if hj : j < q then P j hj else 0)
    (fun j => match j with
      | 0 => 0
      | j + 1 => coefTop (S j))
    (fun j => match j with
      | 0 => G
      | j + 1 => coefBot (S j))
    hμ hw (fun j hj => by
      rcases j with _ | j
      · exact h.start
      · simp only [dif_pos (Nat.lt_of_succ_lt_succ hj)]
        exact hE j (Nat.lt_of_succ_lt_succ hj)) (le_refl (q + 1))
  rwa [blockPrefix_self] at h0

/-- The forward bound for the stored factors of a rounded run, in the spectral norm. Let
$\mathbf{U}$, $\mathbf{V}$ and the packed coefficient block columns $\mathbf{S}_j$ be stored
blocks of a rounded run of $q$ steps with block width $b$ for $\mathbf{A}$, with product
allowances $\delta, \delta' \le \varepsilon_{\mathrm{mv}}\|\mathbf{A}\|_2$ and extension
parameters $(\eta_0, \mu, \varepsilon)$, let $\mathbf{S}$ be the assembled $(q+1)b \times qb$
matrix and $\mathbf{P}_{\mathbf{U}}$ the orthogonal projector onto the range of $\mathbf{U}$. If
$\mu, \varepsilon, \varepsilon_{\mathrm{mv}} \ge 0$ and $\sqrt{3(q+1)b}\,\mu \le \eta_0$ then
$$\|\mathbf{A} - \mathbf{U}\mathbf{S}^{\mathsf{T}}\mathbf{V}^{\mathsf{T}}\|_2 \le
\|(\mathbf{I} - \mathbf{P}_{\mathbf{U}})\mathbf{A}\|_2 + \Bigl(\sqrt{3qb}\,\mu +
\sqrt{1 + \eta_0}\,\bigl(\varepsilon_{\mathrm{mv}} + \varepsilon(1 + \varepsilon_{\mathrm{mv}})
\bigr)\sqrt{qb(1 + \eta_0)}\Bigr)\|\mathbf{A}\|_2.$$ -/
theorem IsRoundedStoredRun.specNorm_sub_mul_transpose_mul_transpose_le
    (h : IsRoundedStoredRun A δ δ' η₀ μ ε b q Ω U V G R S) (hδ : δ ≤ εmv * specNorm A)
    (hδ' : δ' ≤ εmv * specNorm A) (hμ : 0 ≤ μ) (hε : 0 ≤ ε) (hmv : 0 ≤ εmv)
    (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) :
    specNorm (A - U * (assembleRight b q S)ᵀ * Vᵀ) ≤ specNorm ((1 - rangeProjector U) * A) +
      (Real.sqrt (3 * q * b) * μ + Real.sqrt (1 + η₀) *
        ((εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)))) * specNorm A :=
  (h.isBlockGolubKahanErr hδ hδ').specNorm_sub_mul_transpose_mul_transpose_le hμ hε hmv hw

/-- The forward bound for the stored factors of a rounded run, in the Frobenius norm. Let
$\mathbf{U}$, $\mathbf{V}$ and the packed coefficient block columns $\mathbf{S}_j$ be stored
blocks of a rounded run of $q$ steps with block width $b$ for $\mathbf{A}$, with product
allowances $\delta, \delta' \le \varepsilon_{\mathrm{mv}}\|\mathbf{A}\|_2$ and extension
parameters $(\eta_0, \mu, \varepsilon)$, let $\mathbf{S}$ be the assembled $(q+1)b \times qb$
matrix and $\mathbf{P}_{\mathbf{U}}$ the orthogonal projector onto the range of $\mathbf{U}$. If
$\mu, \varepsilon, \varepsilon_{\mathrm{mv}} \ge 0$ and $\sqrt{3(q+1)b}\,\mu \le \eta_0$ then
$$\|\mathbf{A} - \mathbf{U}\mathbf{S}^{\mathsf{T}}\mathbf{V}^{\mathsf{T}}\|_{\mathsf{F}} \le
\|(\mathbf{I} - \mathbf{P}_{\mathbf{U}})\mathbf{A}\|_{\mathsf{F}} + \Bigl(\sqrt{3qb}\,\mu +
\sqrt{1 + \eta_0}\,\bigl(\varepsilon_{\mathrm{mv}} + \varepsilon(1 + \varepsilon_{\mathrm{mv}})
\bigr)\sqrt{qb(1 + \eta_0)}\Bigr)\|\mathbf{A}\|_2.$$ -/
theorem IsRoundedStoredRun.frobNorm_sub_mul_transpose_mul_transpose_le
    (h : IsRoundedStoredRun A δ δ' η₀ μ ε b q Ω U V G R S) (hδ : δ ≤ εmv * specNorm A)
    (hδ' : δ' ≤ εmv * specNorm A) (hμ : 0 ≤ μ) (hε : 0 ≤ ε) (hmv : 0 ≤ εmv)
    (hw : Real.sqrt (3 * (q + 1 : ℕ) * b) * μ ≤ η₀) :
    frobNorm (A - U * (assembleRight b q S)ᵀ * Vᵀ) ≤ frobNorm ((1 - rangeProjector U) * A) +
      (Real.sqrt (3 * q * b) * μ + Real.sqrt (1 + η₀) *
        ((εmv + ε * (1 + εmv)) * Real.sqrt (q * b * (1 + η₀)))) * specNorm A :=
  (h.isBlockGolubKahanErr hδ hδ').frobNorm_sub_mul_transpose_mul_transpose_le hμ hε hmv hw

end Rounded

end NLAlib.Krylov.GolubKahan.Band
