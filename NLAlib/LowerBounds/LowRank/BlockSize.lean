/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Structural.BlockKrylov

/-!
# Block Krylov iteration cannot resolve multiplicities above the block size

Randomized block Krylov iteration $\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)$ with a block
$\mathbf{\Omega}$ of $b$ columns sees each eigenspace of
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$ only through the $b$ projected columns of
$\mathbf{\Omega}$: the projection of $\mathbf{H}^j\mathbf{\Omega}$ onto the eigenspace of
$\lambda$ is $\lambda^j$ times that of $\mathbf{\Omega}$. So if a singular value $\sigma$ of
$\mathbf{A}$ has multiplicity $b + k + 1$, a subspace of dimension $k + 1$ of its right singular
vectors is orthogonal to the block Krylov space for every depth $q$ and every block, and
$\sigma_k(\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)) \ge \sigma$. In particular a
singular value $\sigma_i > \sigma_r$ of multiplicity above $b$ keeps the spectral error at
$\sigma_i$, above the optimum $\sigma_r$ of rank $r$, at every depth: for a block size below the
target rank some gap hypothesis among the leading singular values is necessary. The bound says
nothing about suboptimality when $\sigma_i = \sigma_r$ (for $\mathbf{A} = \mathbf{I}$ the error
of every method of rank below $\lvert n \rvert$ is $1$).

## Main results

* `NLAlib.singularValues_le_singularValues_sub_rbki_of_singularValues_eq`: every singular value.
* `NLAlib.singularValues_le_specNorm_sub_rbki_of_singularValues_eq`: the spectral norm.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
  [DecidableEq n]

/-- The error of block Krylov iteration acts as $\mathbf{A}$ on eigenvectors orthogonal to the
block: for a matrix $\mathbf{A}$ over $\Bbbk$, a block $\mathbf{\Omega}$, a depth $q$, a scalar
$c$ and a vector $\mathbf{w}$ with
$\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{w} = c\,\mathbf{w}$ and
$\mathbf{\Omega}^{\mathsf{H}}\mathbf{w} = \mathbf{0}$,
$$(\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q))\mathbf{w} =
\mathbf{A}\mathbf{w}\,.$$
The vector $\mathbf{w}$ is orthogonal to every column of the block Krylov matrix, so
$\mathbf{A}\mathbf{w}$ is orthogonal to the range onto which the iteration projects. -/
theorem sub_rbki_mulVec_of_mulVec_eq_smul (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (q : ℕ)
    {w : n → 𝕜} {c : 𝕜} (hw : (Aᴴ * A) *ᵥ w = c • w) (hΩ : Ωᴴ *ᵥ w = 0) :
    (A - rbki A Ω q) *ᵥ w = A *ᵥ w := by
  classical
  have hpow : ∀ j : ℕ, ((Aᴴ * A) ^ j) *ᵥ w = c ^ j • w := fun j => by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ, mul_comm]
  have hK : (blockKrylovMatrix (Aᴴ * A) Ω q)ᴴ *ᵥ w = 0 := by
    ext ⟨j, p⟩
    have h1 : ((blockKrylovMatrix (Aᴴ * A) Ω q)ᴴ *ᵥ w) (j, p) =
        (((Aᴴ * A) ^ (j : ℕ) * Ω)ᴴ *ᵥ w) p := rfl
    rw [h1, Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec, hpow, Matrix.mulVec_smul, hΩ,
      smul_zero]
    rfl
  have hP : rangeProjector (A * blockKrylovMatrix (Aᴴ * A) Ω q) *ᵥ (A *ᵥ w) = 0 := by
    rw [rangeProjector_mulVec_eq_zero_iff, Matrix.conjTranspose_mul, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, hK, smul_zero]
  rw [Matrix.sub_mulVec, rbki, rsvd, ← Matrix.mulVec_mulVec, hP, sub_zero]

omit [DecidableEq n] in
/-- A right singular vector is scaled by its singular value: for a matrix $\mathbf{A}$ over
$\Bbbk$, a real $s \ge 0$ and a vector $\mathbf{w}$ with
$\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{w} = s^2\mathbf{w}$,
$$\|\mathbf{A}\mathbf{w}\|_2 = s\,\|\mathbf{w}\|_2\,.$$ -/
theorem norm_toLp_mulVec_of_conjTranspose_mul_self_mulVec_eq_smul (A : Matrix m n 𝕜)
    {w : n → 𝕜} {s : ℝ} (hs : 0 ≤ s) (hw : (Aᴴ * A) *ᵥ w = ((s ^ 2 : ℝ) : 𝕜) • w) :
    ‖WithLp.toLp 2 (A *ᵥ w)‖ = s * ‖WithLp.toLp 2 w‖ := by
  have h := quadForm_conjTranspose_mul_self A w
  rw [quadForm_def, hw, dotProduct_smul, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq,
    smul_eq_mul, ← RCLike.ofReal_mul, RCLike.ofReal_inj, ← mul_pow] at h
  exact (sq_eq_sq₀ (by positivity) (by positivity)).1 h.symm

/-- **Necessity of a gap for block Krylov iteration, every singular value**: for a matrix
$\mathbf{A}$ over $\Bbbk$ with singular values $\sigma_0 \ge \sigma_1 \ge \dots$, any block
$\mathbf{\Omega}$ with $b$ columns, and indices $i$, $k$ with $\sigma_i = \sigma_{i+b+k}$, for
every depth $q$,
$$\sigma_i(\mathbf{A}) \le
\sigma_k\bigl(\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\bigr)\,.$$
The block is arbitrary (no law, no rank condition) and $\sigma_i = 0$ is allowed, where the bound
is trivial. The eigenspace of $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ for $\sigma_i^2 > 0$ has
dimension at least $b + k + 1$ and meets the orthogonal complement of the block Krylov space in
dimension at least $k + 1$; there $\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)$
acts as $\mathbf{A}$, which scales norms by $\sigma_i$.
No printed source.
Result: rbki-multiplicity-lower-bound -/
theorem singularValues_le_singularValues_sub_rbki_of_singularValues_eq (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) (q : ℕ) {i k : ℕ}
    (h : singularValues A i = singularValues A (i + Fintype.card l + k)) :
    singularValues A i ≤ singularValues (A - rbki A Ω q) k := by
  rcases (singularValues_nonneg A i).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact singularValues_nonneg _ _
  set N := i + Fintype.card l + k with hN
  have hNn : N + 1 ≤ Fintype.card n := by
    have h1 : N < A.rank := (singularValues_pos_iff A).1 (h ▸ hpos)
    have := A.rank_le_card_width
    omega
  obtain ⟨Z, -, hZ, -, -, -, hAZ, -, -⟩ :=
    exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A hNn
  let e : Fin (Fintype.card l + k + 1) → Fin (N + 1) := fun j => ⟨i + j, by omega⟩
  have he : Function.Injective e := fun a b hab => by
    have := congrArg Fin.val hab
    exact Fin.ext (by simpa [e] using this)
  set W := Z.submatrix id e with hWdef
  have hW : HasOrthonormalCols W := hZ.submatrix (Equiv.refl _) he
  have hσ : ∀ j : Fin (Fintype.card l + k + 1), singularValues A (i + j) = singularValues A i :=
    fun j => le_antisymm (singularValues_antitone A (Nat.le_add_right i j))
      (h.le.trans (singularValues_antitone A (by omega)))
  have hAW : Aᴴ * A * W = ((singularValues A i ^ 2 : ℝ) : 𝕜) • W := by
    ext x j
    have h1 := congrFun (congrFun hAZ x) (e j)
    simp only [Matrix.mul_diagonal] at h1
    rw [Matrix.smul_apply, smul_eq_mul, mul_comm, ← hσ j]
    exact h1
  set T := (Ωᴴ * W).mulVecLin
  have hker : k + 1 ≤ Module.finrank 𝕜 (LinearMap.ker T) := by
    have h1 := T.finrank_range_add_finrank_ker
    have h2 : Module.finrank 𝕜 (LinearMap.range T) ≤ Fintype.card l :=
      (Submodule.finrank_le _).trans (by rw [Module.finrank_pi])
    rw [Module.finrank_pi, Fintype.card_fin] at h1
    omega
  have hinj : Function.Injective W.mulVecLin := hW.mulVec_injective
  refine le_singularValues_of_forall_mem _ ((LinearMap.ker T).map W.mulVecLin) ?_ fun x hx => ?_
  · rwa [(Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm]
  · obtain ⟨y, hy, rfl⟩ := hx
    have hy' : Ωᴴ *ᵥ (W *ᵥ y) = 0 := by
      rw [Matrix.mulVec_mulVec]
      exact hy
    have hw : (Aᴴ * A) *ᵥ (W *ᵥ y) = ((singularValues A i ^ 2 : ℝ) : 𝕜) • (W *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hAW, Matrix.smul_mulVec]
    rw [Matrix.mulVecLin_apply, sub_rbki_mulVec_of_mulVec_eq_smul A Ω q hw hy',
      norm_toLp_mulVec_of_conjTranspose_mul_self_mulVec_eq_smul A hpos.le hw]

/-- **Necessity of a gap for block Krylov iteration, spectral norm**: for a matrix $\mathbf{A}$ over
$\Bbbk$ with singular values $\sigma_0 \ge \sigma_1 \ge \dots$, any block $\mathbf{\Omega}$ with
$b$ columns, and an index $i$ with $\sigma_i = \sigma_{i+b}$ (the singular value $\sigma_i$ has
multiplicity above the block size), for every depth $q$,
$$\sigma_i(\mathbf{A}) \le \|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\|_2\,.$$
When $\sigma_i > \sigma_r$ the error stays above the optimal rank-$r$ error $\sigma_r$ at every
depth.
No printed source.
Result: rbki-multiplicity-lower-bound -/
theorem singularValues_le_specNorm_sub_rbki_of_singularValues_eq (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) (q : ℕ) {i : ℕ}
    (h : singularValues A i = singularValues A (i + Fintype.card l)) :
    singularValues A i ≤ specNorm (A - rbki A Ω q) := by
  rw [← singularValues_zero_eq_specNorm]
  exact singularValues_le_singularValues_sub_rbki_of_singularValues_eq A Ω q (k := 0) h

end NLAlib
