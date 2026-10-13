/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Topology.Instances.Matrix

/-!
# Positive semidefinite matrices: entries, trace pairing, limits

Facts about `Matrix.PosSemidef` over an `RCLike` field that Mathlib does not yet have. Upstream
candidates for `Mathlib.Analysis.Matrix.PosDef` and `Mathlib.Analysis.Matrix.Order`.

## Main results

* `Matrix.PosSemidef.col_eq_zero_of_apply_self_eq_zero`: a zero diagonal entry forces a zero
  column; `Matrix.PosSemidef.row_eq_zero_of_apply_self_eq_zero` for the row.
* `Matrix.PosSemidef.norm_apply_sq_le`: `‖A i j‖ ^ 2 ≤ re (A i i) * re (A j j)`.
* `Matrix.PosSemidef.trace_mul_nonneg`, `Matrix.PosSemidef.trace_mul_eq_zero_iff`,
  `Matrix.IsHermitian.posSemidef_iff_trace_mul_nonneg`: the positive semidefinite cone is
  self-dual under the trace pairing.
* `Matrix.isClosed_setOf_posSemidef`: the positive semidefinite matrices form a closed set, and
  `Matrix.instOrderClosedTopology` makes the Loewner order closed in the `MatrixOrder` scope.
* `Matrix.closure_setOf_posDef`: the positive definite matrices are dense in the positive
  semidefinite ones.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Topology

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### Entries -/

/-- The `2 × 2` case of `Matrix.PosSemidef.norm_apply_sq_le`: the determinant is nonnegative. -/
private theorem PosSemidef.norm_apply_sq_le_aux {B : Matrix (Fin 2) (Fin 2) 𝕜}
    (hB : B.PosSemidef) : ‖B 0 1‖ ^ 2 ≤ RCLike.re (B 0 0) * RCLike.re (B 1 1) := by
  have hdet := hB.det_nonneg
  rw [det_fin_two, ← hB.isHermitian.apply 1 0, ← hB.isHermitian.coe_re_apply_self 0,
    ← hB.isHermitian.coe_re_apply_self 1, RCLike.star_def, RCLike.mul_conj] at hdet
  have h : (0 : 𝕜) ≤ ((RCLike.re (B 0 0) * RCLike.re (B 1 1) - ‖B 0 1‖ ^ 2 : ℝ) : 𝕜) := by
    push_cast
    exact hdet
  exact sub_nonneg.mp (RCLike.ofReal_nonneg.mp h)

omit [Fintype n] in
/-- A zero diagonal entry of a positive semidefinite matrix forces the whole column to vanish.
[HornJohnson2013, Observation 7.1.10].
Port of `NLAlib.apply_eq_zero_of_posSemidef_of_apply_self_eq_zero`. -/
theorem PosSemidef.col_eq_zero_of_apply_self_eq_zero {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    {i : n} (h : A i i = 0) : A.col i = 0 := by
  ext j
  have hji := (hA.submatrix ![j, i]).norm_apply_sq_le_aux
  simp only [submatrix_apply, cons_val_zero, cons_val_one] at hji
  rw [h, map_zero, mul_zero] at hji
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hji (sq_nonneg _)))

omit [Fintype n] in
/-- A zero diagonal entry of a positive semidefinite matrix forces the whole row to vanish.
[HornJohnson2013, Observation 7.1.10].
Port of `NLAlib.apply_eq_zero_of_posSemidef_of_apply_self_eq_zero'`. -/
theorem PosSemidef.row_eq_zero_of_apply_self_eq_zero {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    {i : n} (h : A i i = 0) : A.row i = 0 := by
  ext j
  have hj : A j i = 0 := congr_fun (hA.col_eq_zero_of_apply_self_eq_zero h) j
  rw [row_apply, ← hA.isHermitian.apply i j, hj, star_zero, Pi.zero_apply]

omit [Fintype n] in
/-- Every entry of a positive semidefinite matrix is dominated by the two diagonal entries in
its row and column: `‖A i j‖ ^ 2 ≤ re (A i i) * re (A j j)`, the nonnegativity of a `2 × 2`
principal minor.
[HornJohnson2013, Observation 7.1.10]. -/
theorem PosSemidef.norm_apply_sq_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) (i j : n) :
    ‖A i j‖ ^ 2 ≤ RCLike.re (A i i) * RCLike.re (A j j) :=
  (hA.submatrix ![i, j]).norm_apply_sq_le_aux

omit [Fintype n] in
/-- The arithmetic-mean form of `Matrix.PosSemidef.norm_apply_sq_le`:
`2 * ‖A i j‖ ≤ re (A i i) + re (A j j)`.
[HornJohnson2013, Observation 7.1.10]; the printed consequence `|aᵢⱼ| ≤ aᵢᵢ + aⱼⱼ` is weaker by a
factor of two. Port of `NLAlib.abs_apply_le_apply_self_add_apply_self`, there over `ℝ` and
without the factor. -/
theorem PosSemidef.two_mul_norm_apply_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) (i j : n) :
    2 * ‖A i j‖ ≤ RCLike.re (A i i) + RCLike.re (A j j) := by
  have hi : 0 ≤ RCLike.re (A i i) := (RCLike.nonneg_iff.mp hA.diag_nonneg).1
  have hj : 0 ≤ RCLike.re (A j j) := (RCLike.nonneg_iff.mp hA.diag_nonneg).1
  refine (sq_le_sq₀ (by positivity) (add_nonneg hi hj)).mp ?_
  nlinarith [hA.norm_apply_sq_le i j, sq_nonneg (RCLike.re (A i i) - RCLike.re (A j j))]

/-! ### Trace -/

/-- The trace of a Hermitian matrix is real: it is the coercion of its real part. -/
theorem IsHermitian.coe_re_trace {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (RCLike.re A.trace : 𝕜) = A.trace := by
  rw [← RCLike.conj_eq_iff_re, ← RCLike.star_def, ← trace_conjTranspose, hA.eq]

/-- The real part of the trace of a positive semidefinite matrix is nonnegative.
Port of `NLAlib.re_trace_nonneg_of_posSemidef`. -/
theorem PosSemidef.re_trace_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    0 ≤ RCLike.re A.trace :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

/-- A positive semidefinite matrix whose trace has zero real part is zero.
Port of `NLAlib.re_trace_eq_zero_iff_of_posSemidef`. -/
theorem PosSemidef.re_trace_eq_zero_iff {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    RCLike.re A.trace = 0 ↔ A = 0 := by
  rw [← hA.trace_eq_zero_iff, ← hA.isHermitian.coe_re_trace, RCLike.ofReal_eq_zero,
    RCLike.ofReal_re]

/-- The trace of a product of two positive semidefinite matrices is nonnegative.
[HornJohnson2013, Theorem 7.5.4]. Port of `NLAlib.trace_mul_nonneg_of_posSemidef`.
Result: psd-cone-self-dual -/
theorem PosSemidef.trace_mul_nonneg {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, star_eq_conjTranspose]
  exact (hA.mul_mul_conjTranspose_same C).trace_nonneg

/-- For positive semidefinite `A` and `B`, the trace pairing vanishes exactly when the product
does. [HornJohnson2013, Theorem 7.5.4]. Port of `NLAlib.trace_mul_eq_zero_iff_of_posSemidef`.
Result: psd-cone-self-dual -/
theorem PosSemidef.trace_mul_eq_zero_iff {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : (A * B).trace = 0 ↔ A * B = 0 := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, trace_zero]⟩
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨D, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  simp only [star_eq_conjTranspose] at h ⊢
  have h' : ((C * Dᴴ)ᴴ * (C * Dᴴ)).trace = 0 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, trace_mul_comm]
    simpa only [Matrix.mul_assoc] using h
  rw [trace_conjTranspose_mul_self_eq_zero_iff] at h'
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, h', Matrix.zero_mul, Matrix.mul_zero]

/-- **Self-duality of the positive semidefinite cone.** A Hermitian matrix is positive
semidefinite exactly when its trace pairing with every positive semidefinite matrix is
nonnegative. [HornJohnson2013, Theorem 7.5.4]. Port of `NLAlib.posSemidef_iff_trace_mul_nonneg`.
Result: psd-cone-self-dual -/
theorem IsHermitian.posSemidef_iff_trace_mul_nonneg {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ B : Matrix n n 𝕜, B.PosSemidef → 0 ≤ (A * B).trace := by
  refine ⟨fun hA B hB ↦ hA.trace_mul_nonneg hB, fun h ↦ .of_dotProduct_mulVec_nonneg hA fun x ↦ ?_⟩
  simpa only [mul_vecMulVec, trace_vecMulVec, dotProduct_comm] using
    h (vecMulVec x (star x)) (posSemidef_vecMulVec_self_star x)

/-- The trace pairing with a positive semidefinite matrix is monotone in the Loewner order.
[HornJohnson2013, Theorem 7.5.4]. Port of `NLAlib.trace_mul_le_trace_mul_of_posSemidef`.
Result: psd-cone-self-dual -/
theorem PosSemidef.trace_mul_le_trace_mul {A B C : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hBC : B ≤ C) : (A * B).trace ≤ (A * C).trace := by
  simpa only [Matrix.mul_sub, trace_sub, sub_nonneg] using hA.trace_mul_nonneg (le_iff.mp hBC)

/-! ### Limits -/

omit [Fintype n] in
/-- The positive semidefinite matrices form a closed subset of `Matrix n n 𝕜`. -/
theorem isClosed_setOf_posSemidef : IsClosed {A : Matrix n n 𝕜 | A.PosSemidef} := by
  simp only [PosSemidef, IsHermitian, Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_iInter fun x ↦ ?_)
  refine isClosed_le continuous_const ?_
  simp only [Finsupp.sum]
  fun_prop

omit [Fintype n] in
/-- The Loewner order on `Matrix n n 𝕜` is closed. An instance in the `MatrixOrder` scope, so
that `le_of_tendsto`, `sum_le_hasSum` and the other order-topology lemmas apply to matrices. -/
theorem instOrderClosedTopology : OrderClosedTopology (Matrix n n 𝕜) where
  isClosed_le' := isClosed_setOf_posSemidef.preimage (continuous_snd.sub continuous_fst)

scoped[MatrixOrder] attribute [instance] Matrix.instOrderClosedTopology

omit [Fintype n] in
/-- A limit of positive semidefinite matrices is positive semidefinite.
Port of `NLAlib.posSemidef_of_tendsto`, there over `ℝ`. -/
theorem PosSemidef.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → Matrix n n 𝕜}
    {A : Matrix n n 𝕜} (hF : ∀ᶠ i in l, (F i).PosSemidef) (hA : Filter.Tendsto F l (𝓝 A)) :
    A.PosSemidef :=
  isClosed_setOf_posSemidef.mem_of_tendsto hA hF

omit [Fintype n] in
/-- A convergent sum of positive semidefinite matrices is positive semidefinite, with no
countability assumption on the index. Port of `NLAlib.posSemidef_of_hasSum`, there over `ℝ`. -/
theorem PosSemidef.of_hasSum {ι : Type*} {F : ι → Matrix n n 𝕜} {A : Matrix n n 𝕜}
    (hF : ∀ i, (F i).PosSemidef) (hA : HasSum F A) : A.PosSemidef :=
  .of_tendsto (.of_forall fun s ↦ posSemidef_sum s fun i _ ↦ hF i) hA

omit [Fintype n] in
/-- The positive definite matrices are dense in the positive semidefinite ones: the closure of
the positive definite set is the positive semidefinite set. [HornJohnson2013, §7.1]. -/
theorem closure_setOf_posDef :
    closure {A : Matrix n n 𝕜 | A.PosDef} = {A : Matrix n n 𝕜 | A.PosSemidef} := by
  classical
  refine (closure_minimal (fun _ ↦ PosDef.posSemidef) isClosed_setOf_posSemidef).antisymm
    fun A hA ↦ ?_
  have h : Filter.Tendsto (fun ε : ℝ ↦ A + ε • (1 : Matrix n n 𝕜)) (𝓝[>] 0) (𝓝 A) := by
    have hc : Continuous fun ε : ℝ ↦ A + ε • (1 : Matrix n n 𝕜) := by fun_prop
    simpa only [zero_smul, add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact PosDef.posSemidef_add hA (PosDef.one.smul hε)

omit [Fintype n] in
/-- A continuous inequality that holds on the positive definite matrices extends to the positive
semidefinite ones. The standard device for removing an invertibility hypothesis.
Port of `NLAlib.le_of_posSemidef_of_continuous_of_forall_posDef`, there over `ℝ`. -/
theorem PosSemidef.le_of_forall_posDef_le {f g : Matrix n n 𝕜 → ℝ} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ M : Matrix n n 𝕜, M.PosDef → f M ≤ g M) {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : f A ≤ g A :=
  closure_minimal h (isClosed_le hf hg) (closure_setOf_posDef.superset hA)

end Matrix
