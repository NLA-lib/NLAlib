/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.Ritz

/-!
# The binary search for a promising Ritz value by row solves

The binary search `NLAlib.findRitz` compares the last rows
$\mathbf{e}_n^{\mathsf{H}}p_h(\mathbf{H})^{-e}$ of inverse powers of the shift polynomials of the
two halves of the Ritz values ([BanksGarzaVargasSrivastava2021, §4.3], $\mathrm{Find}$). A
program computes such a row without forming an inverse: it multiplies the row vector
$\mathbf{e}_n^{\mathsf{H}}$ on the right by $(\mathbf{H} - s\mathbf{I})^{-1}$, once for each
shift of the half and each of the $e$ powers, and each such product is one Givens QR of the
Hessenberg matrix $\mathbf{H} - s\mathbf{I}$, a forward substitution with the triangular factor
and the rotations applied to the row in reverse order.

## Main definitions

* `NLAlib.rowForwardSubstState`, `NLAlib.rowForwardSubst`: the forward substitution
  $\mathbf{y}^{\mathsf{T}}\mathbf{R} = \mathbf{v}^{\mathsf{T}}$ column by column.

## Main results

* `NLAlib.inv_aeval_shiftPoly_pow_apply_last`: the last row of the inverse power as successive
  row solves.
* `NLAlib.rowForwardSubst_eq`: the forward substitution solves the triangular system.
* `NLAlib.vecMul_inv_eq_givens`: a row solve by Givens QR.
* `NLAlib.vecMul_conjTranspose_givensHessenbergQ_eq_foldl`: the adjoint of the unitary factor
  as the rotations in reverse order.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- Commuting matrices have commuting inverses. -/
private lemma commute_inv_inv_matrix {a b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h : Commute a b) : Commute a⁻¹ b⁻¹ := by
  change a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹
  rw [← Matrix.mul_inv_rev, ← h.eq, Matrix.mul_inv_rev]

/-- The inverse of the value of a shift polynomial is the product of the inverse shifts, in the
order of `ss` (the factors commute). -/
private lemma inv_aeval_shiftPoly_eq_prod (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) :
    (Polynomial.aeval H (shiftPoly ss))⁻¹ =
      (ss.map fun s => (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹).prod := by
  induction ss with
  | nil => simp [shiftPoly]
  | cons s ss ih =>
    have hsh : shiftPoly (s :: ss) = (Polynomial.X - Polynomial.C s) * shiftPoly ss := by
      simp [shiftPoly]
    have hX : Polynomial.aeval H (Polynomial.X - Polynomial.C s) =
        H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
      simp [Algebra.algebraMap_eq_smul_one]
    have hHq : Commute H (Polynomial.aeval H (shiftPoly ss)) := by
      generalize shiftPoly ss = q
      induction q using Polynomial.induction_on with
      | C a => rw [Polynomial.aeval_C]; exact (Algebra.commutes a H).symm
      | add p q hp hq => rw [map_add]; exact hp.add_right hq
      | monomial k a ih =>
        rw [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
        exact Commute.mul_right (show Commute H (algebraMap ℂ _ a) from
          (Algebra.commutes a H).symm) ((Commute.refl H).pow_right (k + 1))
    have hc : Commute (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
        (Polynomial.aeval H (shiftPoly ss)) :=
      hHq.sub_left ((Commute.one_left _).smul_left s)
    have hc' := commute_inv_inv_matrix hc
    rw [hsh, map_mul, hX, Matrix.mul_inv_rev, ih, List.map_cons, List.prod_cons]
    rw [ih] at hc'
    exact hc'.eq.symm

/-- The last row of an inverse power of a shift polynomial by successive row solves:
$\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})^{-e}$, $p(z) = \prod_{s \in \mathrm{ss}}(z - s)$, is
$\mathbf{e}_n^{\mathsf{H}}$ multiplied on the right by $(\mathbf{H} - s\mathbf{I})^{-1}$ for each
shift of `ss`, repeated $e$ times. The factors commute; with a singular factor both sides are
$\mathbf{0}$ for $e \ge 1$ (Lean's inverse of a singular matrix is $\mathbf{0}$).
[BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem inv_aeval_shiftPoly_pow_apply_last (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (e : ℕ) :
    ((Polynomial.aeval H (shiftPoly ss))⁻¹ ^ e) (Fin.last n) =
      (List.replicate e ss).flatten.foldl
        (fun v s => v ᵥ* (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹)
        (Pi.single (Fin.last n) 1) := by
  have hrow : ∀ (M N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)),
      (M * N) i = M i ᵥ* N :=
    fun _ _ _ => rfl
  have hprod : ∀ (l : List ℂ) (w : Fin (n + 1) → ℂ),
      w ᵥ* (l.map fun s => (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹).prod =
        l.foldl (fun v s => v ᵥ* (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹) w := by
    intro l
    induction l with
    | nil => intro w; simp
    | cons s l ih => intro w; rw [List.map_cons, List.prod_cons, ← Matrix.vecMul_vecMul, ih,
        List.foldl_cons]
  rw [inv_aeval_shiftPoly_eq_prod]
  induction e with
  | zero =>
    simp only [pow_zero, List.replicate_zero, List.flatten_nil, List.foldl_nil]
    funext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  | succ e ih =>
    rw [pow_succ, hrow, ih, hprod, List.replicate_succ', List.flatten_append, List.foldl_append]
    simp

/-- The state of the **forward substitution** for $\mathbf{y}^{\mathsf{T}}\mathbf{R} =
\mathbf{v}^{\mathsf{T}}$ after $k$ columns: coordinates $j < k$ are
$y_j = (v_j - \sum_{i < j} y_i R_{ij})/R_{jj}$, the others $0$. -/
noncomputable def rowForwardSubstState {d : ℕ} (R : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    ℕ → Fin d → ℂ
  | 0 => 0
  | k + 1 => fun j =>
    if (j : ℕ) = k then
      (v j - ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < k),
        rowForwardSubstState R v k i * R i j) / R j j
    else rowForwardSubstState R v k j

/-- The **forward substitution** $\mathbf{y}$ with $\mathbf{y}^{\mathsf{T}}\mathbf{R} =
\mathbf{v}^{\mathsf{T}}$ for an upper triangular $\mathbf{R}$ with nonzero diagonal: all $d$
columns of `NLAlib.rowForwardSubstState`. [GolubVanLoan2013, §3.1.2]. -/
noncomputable def rowForwardSubst {d : ℕ} (R : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    Fin d → ℂ :=
  rowForwardSubstState R v d

/-- The state of the forward substitution after `k` columns: its coordinates from `k` on vanish,
and the row product $\mathbf{y}^{\mathsf{T}}\mathbf{R}$ agrees with $\mathbf{v}^{\mathsf{T}}$ in
the first `k` columns. -/
private lemma rowForwardSubstState_spec {d : ℕ} {R : Matrix (Fin d) (Fin d) ℂ}
    (hR : R.IsUpperTriangular) (hdiag : ∀ i, R i i ≠ 0) (v : Fin d → ℂ) (k : ℕ) (hk : k ≤ d) :
    (∀ i : Fin d, k ≤ (i : ℕ) → rowForwardSubstState R v k i = 0) ∧
      ∀ j : Fin d, (j : ℕ) < k → (rowForwardSubstState R v k ᵥ* R) j = v j := by
  induction k with
  | zero => exact ⟨fun i _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨hsupp, hcol⟩ := ih (Nat.le_of_succ_le hk)
    have hk' : k < d := hk
    obtain ⟨kf, hkf⟩ : ∃ kf : Fin d, (kf : ℕ) = k := ⟨⟨k, hk'⟩, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (v kf - ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < k),
        rowForwardSubstState R v k i * R i kf) / R kf kf := ⟨_, rfl⟩
    have hsk : rowForwardSubstState R v k kf = 0 := hsupp kf (by omega)
    have hN : rowForwardSubstState R v (k + 1) =
        rowForwardSubstState R v k + Pi.single kf c := by
      funext i
      by_cases h : i = kf
      · subst h
        simp [rowForwardSubstState, hkf, hsk, hc]
      · have h' : (i : ℕ) ≠ k := fun e => h (Fin.ext (e.trans hkf.symm))
        simp [rowForwardSubstState, h', h]
    have hvec : rowForwardSubstState R v (k + 1) ᵥ* R =
        rowForwardSubstState R v k ᵥ* R + fun j => c * R kf j := by
      rw [hN, Matrix.add_vecMul, Matrix.single_vecMul]
      rfl
    have hT : (rowForwardSubstState R v k ᵥ* R) kf =
        ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < k),
          rowForwardSubstState R v k i * R i kf := by
      simp only [Matrix.vecMul, dotProduct]
      refine (Finset.sum_filter_of_ne ?_).symm
      intro i _ h
      by_contra hi
      exact h (by rw [hsupp i (not_lt.mp hi), zero_mul])
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · have hne : i ≠ kf := by rintro rfl; omega
      rw [hN, Pi.add_apply, hsupp i (by omega), Pi.single_apply, if_neg hne, add_zero]
    · rw [hvec, Pi.add_apply]
      rcases Nat.lt_or_ge (j : ℕ) k with hjk | hjk
      · have hRj : R kf j = 0 := hR (show j < kf from by rw [Fin.lt_def]; omega)
        rw [hRj, mul_zero, add_zero]
        exact hcol j hjk
      · have hjkf : j = kf := Fin.ext (by rw [hkf]; omega)
        rw [hjkf, hT, hc, div_mul_cancel₀ _ (hdiag kf)]
        ring

/-- The forward substitution solves the triangular system: for $\mathbf{R}$ upper triangular
with nonzero diagonal, `NLAlib.rowForwardSubst` $\mathbf{R}$ $\mathbf{v}$ is
$\mathbf{v}^{\mathsf{T}}\mathbf{R}^{-1}$. -/
theorem rowForwardSubst_eq {d : ℕ} {R : Matrix (Fin d) (Fin d) ℂ} (hR : R.IsUpperTriangular)
    (hdiag : ∀ i, R i i ≠ 0) (v : Fin d → ℂ) :
    rowForwardSubst R v = v ᵥ* R⁻¹ := by
  have hdet : IsUnit R.det := by
    rw [Matrix.det_of_isUpperTriangular hR]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i)
  have hy := (rowForwardSubstState_spec hR hdiag v d le_rfl).2
  unfold rowForwardSubst
  generalize rowForwardSubstState R v d = y at hy ⊢
  have hy' : y ᵥ* R = v := funext fun j => hy j j.isLt
  subst hy'
  rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv R hdet, Matrix.vecMul_one]

/-- A row solve by Givens QR: with $\mathbf{H} = \mathbf{Q}\mathbf{R}$ the Givens QR
(`NLAlib.givensHessenbergQ`, `NLAlib.givensHessenbergR`),
$\mathbf{v}^{\mathsf{T}}\mathbf{H}^{-1} = (\mathbf{v}^{\mathsf{T}}\mathbf{R}^{-1})
\mathbf{Q}^{\mathsf{H}}$ (both sides $\mathbf{0}$ when $\mathbf{H}$ is singular).
[GolubVanLoan2013, §5.2.5]. -/
theorem vecMul_inv_eq_givens (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (v : Fin (n + 1) → ℂ) :
    v ᵥ* H⁻¹ = (v ᵥ* (givensHessenbergR H)⁻¹) ᵥ* (givensHessenbergQ H)ᴴ := by
  have hfac : givensHessenbergQ H * givensHessenbergR H = H :=
    givensHessenbergState_fst_mul_snd H _
  have hQi : (givensHessenbergQ H)⁻¹ = (givensHessenbergQ H)ᴴ :=
    Matrix.inv_eq_left_inv (hasOrthonormalCols_givensHessenbergState_fst H _).conjTranspose_mul_self
  have hinv : H⁻¹ = (givensHessenbergR H)⁻¹ * (givensHessenbergQ H)ᴴ := by
    rw [← hQi, ← Matrix.mul_inv_rev, hfac]
  rw [hinv, Matrix.vecMul_vecMul]

/-- The adjoint of the accumulated factor after $k$ steps, as the rotations of steps `k - 1`
down to `0` applied to the row vector. -/
private lemma vecMul_conjTranspose_givensHessenbergState_eq_foldl {m p : ℕ}
    (H : Matrix (Fin m) (Fin p) ℂ) (k : ℕ) (v : Fin m → ℂ) :
    v ᵥ* (givensHessenbergState H k).1ᴴ =
      (List.range k).reverse.foldl
        (fun w j => w ᵥ* givensHessenbergStep (givensHessenbergState H j).2 j) v := by
  induction k generalizing v with
  | zero => simp [givensHessenbergState]
  | succ k ih =>
    have hstate : (givensHessenbergState H (k + 1)).1ᴴ =
        givensHessenbergStep (givensHessenbergState H k).2 k * (givensHessenbergState H k).1ᴴ := by
      rw [show (givensHessenbergState H (k + 1)).1 = (givensHessenbergState H k).1 *
          (givensHessenbergStep (givensHessenbergState H k).2 k)ᴴ from rfl,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [hstate, ← Matrix.vecMul_vecMul, ih, List.range_succ, List.reverse_append,
      List.foldl_append]
    simp

/-- The adjoint of the unitary factor of Givens QR as the rotations in reverse order:
$\mathbf{v}^{\mathsf{T}}\mathbf{Q}^{\mathsf{H}} = \mathbf{v}^{\mathsf{T}}\mathbf{G}_{p-1}\cdots
\mathbf{G}_0$, with $\mathbf{G}_k$ the rotation of step $k$ (`NLAlib.givensHessenbergStep` of
the state `NLAlib.givensHessenbergState` after $k$ steps). -/
theorem vecMul_conjTranspose_givensHessenbergQ_eq_foldl {m p : ℕ}
    (H : Matrix (Fin m) (Fin p) ℂ) (v : Fin m → ℂ) :
    v ᵥ* (givensHessenbergQ H)ᴴ =
      (List.range p).reverse.foldl
        (fun w k => w ᵥ* givensHessenbergStep (givensHessenbergState H k).2 k) v :=
  vecMul_conjTranspose_givensHessenbergState_eq_foldl H p v

end NLAlib
