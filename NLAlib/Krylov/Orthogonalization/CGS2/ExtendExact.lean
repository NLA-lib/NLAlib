/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Orthogonalization.CGS2.ExtendDecode
public import NLAlib.Krylov.Orthogonalization.CGS2.ExtendLoop
public import NLAlib.Matrix.Factorizations.BasisExtensionContract
public import NLAlib.Matrix.Factorizations.CGS2.BasisExtension

/-!
# The exact contract of the column-wise two-pass Gram–Schmidt extension

In exact arithmetic, the implementation `NLAlib.CGS2.cgs2ExtendImpl` with the threshold $0$
meets the exact contract `NLAlib.Ops.exactExtendRel` of a basis extension, for an arbitrary
stored basis: with the threshold $0$ the deflation test drops exactly the columns whose reduced
vector is zero, which is the zero guard of rank-revealing Gram–Schmidt. The mathematics is
`NLAlib.isBasisExtension_of_two_passes`. Design: `docs/design/LowRank-BlockLanczos.md` §3.5,
statement E4 of §5.

## Main results

* `NLAlib.CGS2.colOut_exact`, `NLAlib.CGS2.exact_column`,
  `NLAlib.CGS2.isBasisExtension_of_colsDone`: the words of the exact rounds, decoded, give an
  exact extension.
* `NLAlib.CGS2.meets_nrm2RelOf_exact`, `NLAlib.CGS2.meets_scalRelOf_exact`,
  `NLAlib.CGS2.meets_axpyRel_zero`: the exact contracts in the form used by a round.
* `NLAlib.CGS2.cgs2Extend_exact_spec`: the implementation with the threshold $0$ meets the exact
  contract of a basis extension in exact arithmetic.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.CGS2

open Ops Krylov.Lanczos.Reorth

variable {K Op Tst : Type} [Inhabited K]

/-- One exact round, decoded. With exact arithmetic, an exact norm and an exact scaling,
the words of a round `NLAlib.CGS2.ColOut` at the threshold $0$ decode to two exact classical
passes against the $j$ stored columns $\mathbf{V}$:
$\mathbf{w}_1 = \mathbf{w} - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w}$,
$\mathbf{w}_2 = \mathbf{w}_1 - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w}_1$, the first $j$
coefficients $\mathbf{V}^{\mathsf{T}}\mathbf{w} + \mathbf{V}^{\mathsf{T}}\mathbf{w}_1$, zero
coefficients after row $j$, the diagonal coefficient $\lVert\mathbf{w}_2\rVert$ and the new
column $\lVert\mathbf{w}_2\rVert^{-1}\mathbf{w}_2$ (zero when $\mathbf{w}_2 = \mathbf{0}$). -/
theorem colOut_exact {M : Machine K} {dec : K → ℝ} {n j r : ℕ} {vs wc w₂ cc qc : List K}
    (hM : ExactModel dec M)
    (h : ColOut M dec 0 0 (fun x v => dec v = √(∑ i ∈ Finset.range n, dec (x i) ^ 2))
      (fun a x z => dec a ≠ 0 → ∀ i < n, dec (z i) = dec (x i) / dec a) 0 n j r vs wc w₂ cc
      qc) :
    ∃ w₁ : Fin n → ℝ,
      w₁ = decv dec n wc -
        decodeMatrix dec n j vs *ᵥ ((decodeMatrix dec n j vs)ᵀ *ᵥ decv dec n wc) ∧
      decv dec n w₂ = w₁ - decodeMatrix dec n j vs *ᵥ ((decodeMatrix dec n j vs)ᵀ *ᵥ w₁) ∧
      (∀ i : Fin j, dec (vec cc i) = ((decodeMatrix dec n j vs)ᵀ *ᵥ decv dec n wc) i +
        ((decodeMatrix dec n j vs)ᵀ *ᵥ w₁) i) ∧
      (∀ i, j < i → i < r → dec (vec cc i) = 0) ∧
      dec (vec cc j) = ‖WithLp.toLp 2 (decv dec n w₂)‖ ∧
      decv dec n qc = (‖WithLp.toLp 2 (decv dec n w₂)‖⁻¹ : ℝ) • decv dec n w₂ := by
  obtain ⟨ν₀, β, mid, h₁, h₂, -, hp₁, hp₂, hnβ, hadd, hzero, hbr⟩ := h
  have hcoef : ∀ {xs ys hs : List K}, PassOut dec 0 0 n j vs xs ys hs → ∀ i : Fin j,
      dec (vec hs i) = ((decodeMatrix dec n j vs)ᵀ *ᵥ decv dec n xs) i := by
    intro xs ys hs hp i
    have hd := hp.dot i i.isLt
    unfold IsDotErr at hd
    rw [zero_mul] at hd
    rw [sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd (abs_nonneg _))), Finset.sum_range]
    change ∑ l : Fin n, dec (vec vs (↑i * n + ↑l)) * dec (vec xs ↑l) =
      ∑ l : Fin n, (decodeMatrix dec n j vs)ᵀ i l * decv dec n xs l
    exact Finset.sum_congr rfl fun l _ => by
      rw [Matrix.transpose_apply, decodeMatrix_apply]
      rfl
  have hupd : ∀ {xs ys hs : List K}, PassOut dec 0 0 n j vs xs ys hs →
      decv dec n ys = decv dec n xs -
        decodeMatrix dec n j vs *ᵥ ((decodeMatrix dec n j vs)ᵀ *ᵥ decv dec n xs) := by
    intro xs ys hs hp
    have e : (decodeMatrix dec n j vs)ᵀ *ᵥ decv dec n xs = fun i : Fin j => dec (vec hs i) :=
      funext fun i => (hcoef hp i).symm
    rw [e]
    funext l
    have hb := hp.abs_sub_le (le_refl (0 : ℝ)) l
    rw [add_zero, one_pow, sub_self, zero_mul] at hb
    change dec (vec ys l) = dec (vec xs l) -
      ∑ i : Fin j, decodeMatrix dec n j vs l i * dec (vec hs i)
    rw [sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))), Finset.sum_range]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [decodeMatrix_apply, mul_comm]
  have hβn : dec β = ‖WithLp.toLp 2 (decv dec n w₂)‖ := by
    rw [hnβ, EuclideanSpace.norm_eq, Finset.sum_range]
    refine congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => ?_)
    change dec (vec w₂ i) ^ 2 = ‖dec (vec w₂ i)‖ ^ 2
    rw [Real.norm_eq_abs, sq_abs]
  have ht : dec (M.mul (M.lit 0) ν₀) = 0 := by
    rw [hM.mul, hM.lit, Rat.cast_zero, zero_mul]
  have hz0 : dec (M.lit 0) = 0 := by rw [hM.lit, Rat.cast_zero]
  have key : dec (vec cc j) = dec β ∧ decv dec n qc = (dec β)⁻¹ • decv dec n w₂ := by
    rcases hbr with ⟨hle, hcc, hq⟩ | ⟨hgt, hcc, hsc⟩
    · have hβ0 : dec β = 0 := le_antisymm (ht ▸ hle) (hβn ▸ norm_nonneg _)
      refine ⟨by rw [hcc, hz0, hβ0], ?_⟩
      rw [hβ0, inv_zero, zero_smul]
      funext i
      change dec (vec qc i) = 0
      rw [hq i i.isLt, hz0]
    · have hβne : dec β ≠ 0 := fun h0 => hgt (by rw [ht, h0])
      refine ⟨by rw [hcc], ?_⟩
      funext i
      change dec (vec qc i) = (dec β)⁻¹ * dec (vec w₂ i)
      rw [hsc hβne i i.isLt, div_eq_inv_mul]
  refine ⟨decv dec n mid, hupd hp₁, hupd hp₂, fun i => ?_, fun i h1 h2 => ?_, ?_, ?_⟩
  · rw [hadd i i.isLt, hM.add, hcoef hp₁ i, hcoef hp₂ i]
  · rw [hzero i h1 h2, hz0]
  · rw [← hβn]
    exact key.1
  · rw [← hβn]
    exact key.2

/-- Column `c` of the exact scheme. For the decoded basis $\mathbf{Q}$, block $\mathbf{W}$,
new block $\mathbf{Q}'$ and coefficients $\mathbf{C}$ of the exact rounds, and the two passes
$\mathbf{W}_1 = \mathbf{W} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{W} -
\mathbf{Q}'\operatorname{su}(\mathbf{Q}'^{\mathsf{H}}\mathbf{W})$,
$\mathbf{W}_2 = \mathbf{W}_1 - \mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{W}_1 -
\mathbf{Q}'\operatorname{su}(\mathbf{Q}'^{\mathsf{H}}\mathbf{W}_1)$: column $c$ of
$\mathbf{Q}'$ is the normalized column $c$ of $\mathbf{W}_2$, the upper coefficients are those
of $\mathbf{Q}^{\mathsf{H}}\mathbf{W} + \mathbf{Q}^{\mathsf{H}}\mathbf{W}_1$, and the lower
coefficients are those of the two strictly upper triangular parts plus the diagonal of the
norms of the columns of $\mathbf{W}_2$. -/
theorem exact_column {M : Machine K} {dec : K → ℝ} {n k b : ℕ} {qs ws qn wd cs : List K}
    (hM : ExactModel dec M) (hqs : qs.length = k * n)
    (hdone : ColsDone M dec 0 0 (fun x v => dec v = √(∑ i ∈ Finset.range n, dec (x i) ^ 2))
      (fun a x z => dec a ≠ 0 → ∀ i < n, dec (z i) = dec (x i) / dec a) 0 n k b qs ws b qn wd
      cs)
    {Q : Matrix (Fin n) (Fin k) ℝ} {W Q' W₁ W₂ : Matrix (Fin n) (Fin b) ℝ}
    {C : Matrix (Fin (k + b)) (Fin b) ℝ} (hQ : Q = decodeMatrix dec n k qs)
    (hW : W = decodeMatrix dec n b ws) (hQ' : Q' = decodeMatrix dec n b qn)
    (hC : C = decodeMatrix dec (k + b) b cs)
    (hW₁ : W₁ = W - Q * (Qᴴ * W) - Q' * strictUpper (Q'ᴴ * W))
    (hW₂ : W₂ = W₁ - Q * (Qᴴ * W₁) - Q' * strictUpper (Q'ᴴ * W₁)) (c : Fin b) :
    Q'.col c = (‖WithLp.toLp 2 (W₂.col c)‖⁻¹ : ℝ) • W₂.col c ∧
      (∀ i : Fin k, coefTop C i c = (Qᴴ * W) i c + (Qᴴ * W₁) i c) ∧
      ∀ c' : Fin b, coefBot C c' c = strictUpper (Q'ᴴ * W) c' c +
        strictUpper (Q'ᴴ * W₁) c' c +
          Matrix.diagonal (fun c => ‖WithLp.toLp 2 (W₂.col c)‖) c' c := by
  subst hQ hW hQ' hC
  have hcb := c.isLt
  obtain ⟨w₁, hw₁, hw₂, hadd, hzero, hdiag, hq⟩ := colOut_exact hM (hdone c c.isLt)
  rw [← submatrix_fromCols_colsBefore hqs c] at hw₁ hw₂ hadd
  rw [decv_drop_take ws c, storedCol_mulVec] at hw₁
  rw [storedCol_mulVec, decv_drop_take wd c] at hw₂
  have hmul : ∀ {κ : Type} [Fintype κ] (X : Matrix (Fin n) κ ℝ)
      (A : Matrix (Fin n) (Fin b) ℝ) (i : κ), (Xᴴ * A) i c = (Xᵀ *ᵥ A.col c) i :=
    fun X A i => by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      rfl
  have hw₁' : w₁ = W₁.col c := by
    rw [hW₁, col_sub_mul_conjTranspose_mul_sub_mul_strictUpper,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hw₁
  have hw₂' : (decodeMatrix dec n b wd).col c = W₂.col c := by
    rw [hW₂, col_sub_mul_conjTranspose_mul_sub_mul_strictUpper,
      Matrix.conjTranspose_eq_transpose_of_trivial, ← hw₁']
    exact hw₂
  rw [decv_drop_take wd c] at hdiag hq
  rw [decv_drop_take qn c] at hq
  rw [decv_drop_take ws c] at hadd
  refine ⟨?_, fun i => ?_, fun c' => ?_⟩
  · rw [← hw₂']
    exact hq
  · have hi := i.isLt
    rw [hmul, hmul, ← transpose_mulVec_storedCol_inl _ (colsBefore _ c) c.isLt.le _ hi,
      ← transpose_mulVec_storedCol_inl _ (colsBefore _ c) c.isLt.le _ hi, ← hw₁']
    exact (dec_vec_coef cs c (by omega)).symm.trans (hadd ⟨i, by omega⟩)
  · have hc' := c'.isLt
    rcases lt_trichotomy c' c with h | rfl | h
    · have hlt := Fin.lt_def.mp h
      simp only [strictUpper, Matrix.of_apply, if_pos h, Matrix.diagonal_apply_ne _ h.ne,
        add_zero]
      rw [hmul, hmul, ← transpose_mulVec_storedCol_inr _ _ c _ h,
        ← transpose_mulVec_storedCol_inr _ _ c _ h, ← hw₁']
      exact (dec_vec_coef cs c (by omega)).symm.trans (hadd ⟨k + c', by omega⟩)
    · simp only [strictUpper, Matrix.of_apply, if_neg (lt_irrefl _), Matrix.diagonal_apply_eq,
        zero_add]
      rw [← hw₂']
      exact (dec_vec_coef cs c' (by omega)).symm.trans hdiag
    · have hlt := Fin.lt_def.mp h
      simp only [strictUpper, Matrix.of_apply, if_neg (lt_asymm h),
        Matrix.diagonal_apply_ne _ h.ne', add_zero]
      exact (dec_vec_coef cs c (by omega)).symm.trans (hzero (k + c') (by omega) (by omega))

/-- The exact columns give an exact extension. The relations `NLAlib.CGS2.ColsDone` of the
$b$ columns in exact arithmetic at the threshold $0$, for basis words of $k$ columns of length
$n$, imply that the decoded basis, block, new block and coefficients satisfy
`NLAlib.IsBasisExtension`. -/
theorem isBasisExtension_of_colsDone {M : Machine K} {dec : K → ℝ} {n k b : ℕ}
    {qs ws qn wd cs : List K} (hM : ExactModel dec M) (hqs : qs.length = k * n)
    (hdone : ColsDone M dec 0 0 (fun x v => dec v = √(∑ i ∈ Finset.range n, dec (x i) ^ 2))
      (fun a x z => dec a ≠ 0 → ∀ i < n, dec (z i) = dec (x i) / dec a) 0 n k b qs ws b qn wd
      cs) :
    IsBasisExtension (decodeMatrix dec n k qs) (decodeMatrix dec n b ws)
      (decodeMatrix dec n b qn) (coefTop (decodeMatrix dec (k + b) b cs))
      (coefBot (decodeMatrix dec (k + b) b cs)) := by
  obtain ⟨W₁, hW₁⟩ : ∃ W₁, W₁ = decodeMatrix dec n b ws -
      decodeMatrix dec n k qs * ((decodeMatrix dec n k qs)ᴴ * decodeMatrix dec n b ws) -
      decodeMatrix dec n b qn *
        strictUpper ((decodeMatrix dec n b qn)ᴴ * decodeMatrix dec n b ws) := ⟨_, rfl⟩
  obtain ⟨W₂, hW₂⟩ : ∃ W₂, W₂ = W₁ -
      decodeMatrix dec n k qs * ((decodeMatrix dec n k qs)ᴴ * W₁) -
      decodeMatrix dec n b qn * strictUpper ((decodeMatrix dec n b qn)ᴴ * W₁) := ⟨_, rfl⟩
  have hcol := exact_column hM hqs hdone rfl rfl rfl rfl hW₁ hW₂
  have key := isBasisExtension_of_two_passes (𝕜 := ℝ) rfl rfl hW₁ rfl rfl hW₂
    fun c => (hcol c).1
  have hTop : coefTop (decodeMatrix dec (k + b) b cs) =
      (decodeMatrix dec n k qs)ᴴ * decodeMatrix dec n b ws +
        (decodeMatrix dec n k qs)ᴴ * W₁ := by
    ext i c
    exact (hcol c).2.1 i
  have hBot : coefBot (decodeMatrix dec (k + b) b cs) =
      strictUpper ((decodeMatrix dec n b qn)ᴴ * decodeMatrix dec n b ws) +
        strictUpper ((decodeMatrix dec n b qn)ᴴ * W₁) +
        Matrix.diagonal fun c => ‖WithLp.toLp 2 (W₂.col c)‖ := by
    ext c' c
    exact (hcol c).2.2 c'
  rw [hTop, hBot]
  exact key

variable [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

omit [Has ScalarOp Op] [Has CmpTst Tst] in
/-- The exact norm contract, in the form used by a round. -/
theorem meets_nrm2RelOf_exact {dec : K → ℝ} {ok : ℕ → Prop} {I : Interp Op Tst K}
    (h : I.Meets .total (Has.inj Blas1Op.nrm2) ((nrm2ExactRel dec).spec (OutApart ok))) :
    I.Meets .total (Has.inj Blas1Op.nrm2)
      ((nrm2RelOf fun n x v => dec v = √(∑ i ∈ Finset.range n, dec (x i) ^ 2)).spec
        (OutApart ok)) := by
  refine h.mono (fun _ _ _ _ _ hp => hp) ?_
  intro d ins outs τ m m' _ hpost
  obtain ⟨X, hread, hroom, Y, hlen, hrel, hm⟩ := hpost
  refine ⟨X, hread, hroom, Y, hlen, ?_, hm⟩
  simp only [nrm2ExactRel_rel] at hrel
  split at hrel
  · exact hrel
  · contradiction

omit [Has ScalarOp Op] [Has CmpTst Tst] in
/-- The exact scaling contract, in the form used by a round. -/
theorem meets_scalRelOf_exact {dec : K → ℝ} {ok : ℕ → Prop} {I : Interp Op Tst K}
    (h : I.Meets .total (Has.inj Blas1Op.scal) ((scalExactRel dec).spec (InPlace ok))) :
    I.Meets .total (Has.inj Blas1Op.scal)
      ((scalRelOf fun n a x z => dec a ≠ 0 → ∀ i < n, dec (z i) = dec (x i) / dec a).spec
        (InPlace ok)) := by
  refine h.mono (fun _ _ _ _ _ hp => hp) ?_
  intro d ins outs τ m m' _ hpost
  obtain ⟨X, hread, hroom, Y, hlen, hrel, hm⟩ := hpost
  refine ⟨X, hread, hroom, Y, hlen, ?_, hm⟩
  simp only [scalExactRel_rel] at hrel
  split at hrel
  · exact hrel
  · contradiction

omit [Has ScalarOp Op] [Has CmpTst Tst] in
/-- An exact update satisfies the relative-error contract with zero error. -/
theorem meets_axpyRel_zero {dec : K → ℝ} {ok : ℕ → Prop} {I : Interp Op Tst K}
    (h : I.Meets .total (Has.inj Blas1Op.axpy) ((axpyExactRel dec).spec (InPlace ok))) :
    I.Meets .total (Has.inj Blas1Op.axpy) ((axpyRel dec 0).spec (InPlace ok)) := by
  refine h.mono (fun _ _ _ _ _ hp => hp) ?_
  intro d ins outs τ m m' _ hpost
  obtain ⟨X, hread, hroom, Y, hlen, hrel, hm⟩ := hpost
  refine ⟨X, hread, hroom, Y, hlen, ?_, hm⟩
  simp only [axpyExactRel_rel] at hrel
  split at hrel
  · simpa [axpyRel, IsAxpyErr, sub_eq_zero] using hrel
  · contradiction

/-- **Exact column-wise two-pass classical Gram–Schmidt meets the exact contract of a basis
extension.** Under exact scalar arithmetic, exact level-1 operations at every length and exact
comparisons, the implementation with the deflation threshold $0$ runs on all admitted operands
of `NLAlib.Ops.OrthOp.extend` and the decoded basis $\mathbf{Q}$, block $\mathbf{W}$, new block
$\mathbf{Q}'$ and coefficients $\mathbf{H}$, $\mathbf{R}$ satisfy `NLAlib.IsBasisExtension`. The
stored basis is arbitrary: it may have zero columns and need not be orthonormal on its
support. -/
theorem cgs2Extend_exact_spec {M : Machine K} {dec : K → ℝ} {okB : ℕ → Prop}
    {I : Interp Op Tst K} (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec okB I) (hok : ∀ n, okB n) (hCmp : IsCmp dec I) :
    (cgs2ExtendImpl (Op := Op) (Tst := Tst) 0).Triple I .total
      ((exactExtendRel dec).spec ExtendOperands) := by
  have ops : ColOps M dec (fun _ => 0) 0
      (fun n x v => dec v = √(∑ i ∈ Finset.range n, dec (x i) ^ 2))
      (fun n a x z => dec a ≠ 0 → ∀ i < n, dec (z i) = dec (x i) / dec a) okB I :=
    ⟨hS, hB.dot_zero, meets_axpyRel_zero hB.axpy, hM.neg, meets_nrm2RelOf_exact hB.nrm2,
      meets_scalRelOf_exact hB.scal, hB.copy, hCmp⟩
  exact cgs2Extend_triple_of ops (fun n _ _ _ => hok n)
    fun n k b qs ws qn wd cs _ hqs _ _ _ _ hdone => isBasisExtension_of_colsDone hM hqs hdone

end NLAlib.CGS2
