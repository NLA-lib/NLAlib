/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Givens
public import NLAlib.Matrix.Factorizations.Hessenberg

/-!
# Givens QR of an upper Hessenberg matrix

The step-indexed Givens QR `NLAlib.givensHessenbergState` of `Givens.lean`, applied to an upper
Hessenberg matrix $\mathbf{H}$, produces a thin QR factorization: after the $p$ steps the rotated
matrix is upper trapezoidal, and its leading square block is the triangular factor. For a
tridiagonal input the triangular factor has three diagonals. The pivots are nonzero exactly when
$\mathbf{H}$ has full column rank, and the leading $(k+1) \times k$ block of the state is the
Givens QR of the leading block of $\mathbf{H}$, so step $k$ solves the leading least-squares
problem by back substitution and its residual is the modulus of entry $k$ of the rotated first
coordinate vector. GMRES and MINRES consume this progressive form.

These results live in their own file because `IsUpperHessenberg` is defined in
`Hessenberg.lean`, which imports `Givens.lean`.

## Main results

* `NLAlib.isUpperTrapezoidal_givensHessenbergR`, `NLAlib.isQR_givensHessenberg`: Givens QR of an
  upper Hessenberg matrix is a thin QR factorization.
* `NLAlib.givensHessenbergR_apply_eq_zero_of_add_two_lt`: three diagonals for a tridiagonal input.
* `NLAlib.forall_givensHessenbergR_apply_self_ne_zero_iff`: nonzero pivots iff full column rank.
* `NLAlib.isUpperHessenberg_givensHessenbergQ`: the unitary factor is upper Hessenberg, for
  every input.
* `NLAlib.givensHessenbergState_snd_apply_of_eq_add_one`,
  `NLAlib.givensHessenbergState_fst_mulVec_apply_eq_zero_of_le`: rows and coordinates the early
  steps leave untouched.
* `NLAlib.pinv_submatrix_mulVec_single_eq_backSubst`,
  `NLAlib.norm_sub_mulVec_pinv_submatrix_mulVec_single_eq`: the progressive least-squares form
  and its residual.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

section GivensHessenbergQR

variable {m p : ℕ}

/-- After $k$ steps of Givens QR of an upper Hessenberg matrix, the first $k$ columns vanish
below the diagonal and the others below the first subdiagonal. -/
private theorem givensHessenbergState_snd_apply_eq_zero {H : Matrix (Fin m) (Fin p) 𝕜}
    (hH : IsUpperHessenberg H) (k : ℕ) (i : Fin m) (j : Fin p) (hji : (j : ℕ) < i)
    (hj : (j : ℕ) < k ∨ (j : ℕ) + 1 < i) : (givensHessenbergState H k).2 i j = 0 := by
  induction k generalizing i j with
  | zero => exact hH i j (hj.resolve_left (Nat.not_lt_zero _))
  | succ k ih =>
    change (givensHessenbergStep (givensHessenbergState H k).2 k *
      (givensHessenbergState H k).2) i j = 0
    rcases lt_or_ge (j : ℕ) k with hjk | hjk
    · rw [givensHessenbergStep_mul_apply_of_apply_eq_zero _ _
        (fun a ha => ih a j (by omega) (Or.inl hjk))]
      exact ih i j hji (Or.inl hjk)
    by_cases hi : (i : ℕ) = k + 1
    · have hjk' : (j : ℕ) = k := by omega
      have hm : k + 1 < m := by omega
      have hp : k < p := by omega
      rw [show i = ⟨k + 1, hm⟩ from Fin.ext hi, show j = ⟨k, hp⟩ from Fin.ext hjk',
        givensHessenbergStep, dif_pos ⟨hm, hp⟩]
      exact givensOf_mulVec_apply_right (Fin.ne_of_val_ne (Nat.succ_ne_self k).symm) _
    · rw [givensHessenbergStep_mul_apply_of_ne _ _ (by omega) hi]
      exact ih i j hji (Or.inr (by omega))

/-- **Givens QR of an upper Hessenberg matrix is upper trapezoidal**: for an upper Hessenberg
matrix $\mathbf{H}$, the triangular factor $\mathsf{givensHessenbergR}(\mathbf{H})$ of its Givens
QR is upper trapezoidal. [GolubVanLoan2013, §5.2.5]. -/
theorem isUpperTrapezoidal_givensHessenbergR {H : Matrix (Fin m) (Fin p) 𝕜}
    (hH : IsUpperHessenberg H) : IsUpperTrapezoidal (givensHessenbergR H) := by
  exact fun i j hji => givensHessenbergState_snd_apply_eq_zero hH p i j hji (Or.inl j.2)

/-- **Givens QR gives the thin QR factorization** of a tall upper Hessenberg matrix.
[GolubVanLoan2013, Algorithm 5.2.4].
Result: givens-qr -/
theorem isQR_givensHessenberg {H : Matrix (Fin m) (Fin p) 𝕜} (hH : IsUpperHessenberg H)
    (h : p ≤ m) :
    IsQR H ((givensHessenbergQ H).submatrix id (Fin.castLE h))
      ((givensHessenbergR H).submatrix (Fin.castLE h) id) := by
  exact HasOrthonormalCols.isQR_submatrix_castLE (hasOrthonormalCols_givensHessenbergState_fst H p)
    (isUpperTrapezoidal_givensHessenbergR hH) (givensHessenbergState_fst_mul_snd H p).symm h

/-- The band of the triangularised matrix for $\mathbf{H}^{\mathsf{H}}$ upper Hessenberg: after
$k$ steps, $\mathbf{W}_{i,j} = 0$ for $j > i + 2$, and for $j > i + 1$ in the rows $i \ge k$ not
yet rotated. -/
private theorem givensHessenbergState_snd_apply_eq_zero_of_add_two_lt
    {H : Matrix (Fin m) (Fin p) 𝕜} (hH' : IsUpperHessenberg Hᴴ) (k : ℕ) :
    (∀ (i : Fin m) (j : Fin p), (i : ℕ) + 2 < j → (givensHessenbergState H k).2 i j = 0) ∧
      ∀ (i : Fin m) (j : Fin p), k ≤ (i : ℕ) → (i : ℕ) + 1 < j →
        (givensHessenbergState H k).2 i j = 0 := by
  induction k with
  | zero =>
    have h0 : ∀ (i : Fin m) (j : Fin p), (i : ℕ) + 1 < j → H i j = 0 := fun i j hij => by
      have h := hH' j i hij
      rwa [Matrix.conjTranspose_apply, star_eq_zero] at h
    exact ⟨fun i j hij => h0 i j (by omega), fun i j _ hij => h0 i j hij⟩
  | succ k ih =>
    have hgoal : ∀ (i : Fin m) (j : Fin p),
        ((i : ℕ) + 2 < j ∨ (k + 1 ≤ (i : ℕ) ∧ (i : ℕ) + 1 < j)) →
          (givensHessenbergState H (k + 1)).2 i j = 0 := by
      intro i j hij
      change (givensHessenbergStep (givensHessenbergState H k).2 k *
        (givensHessenbergState H k).2) i j = 0
      by_cases hi : (i : ℕ) = k ∨ (i : ℕ) = k + 1
      · rw [givensHessenbergStep_mul_apply_of_apply_eq_zero _ _
          (fun a ha => ih.2 a j (by omega) (by omega))]
        exact ih.2 i j (by omega) (by omega)
      · push Not at hi
        rw [givensHessenbergStep_mul_apply_of_ne _ _ hi.1 hi.2]
        rcases hij with hij | hij
        · exact ih.1 i j hij
        · exact ih.2 i j (by omega) hij.2
    exact ⟨fun i j hij => hgoal i j (Or.inl hij), fun i j hki hij => hgoal i j (Or.inr ⟨hki, hij⟩)⟩

/-- **The tridiagonal case**: if $\mathbf{H}^{\mathsf{H}}$ is upper Hessenberg, in particular
for a rectangular tridiagonal matrix (as $\underline{\mathbf{T}}_q$ in MINRES), the factor
$\mathbf{R}$ has only three nonzero diagonals: $\mathbf{R}_{i,j} = 0$ for $j > i + 2$.
[PaigeSaunders1975, (5.5)]; there in transposed form: the LQ factorization by plane rotations of
the symmetric tridiagonal Lanczos matrix has a lower triangular factor with three nonzero
diagonals. -/
theorem givensHessenbergR_apply_eq_zero_of_add_two_lt {H : Matrix (Fin m) (Fin p) 𝕜}
    (hH' : IsUpperHessenberg Hᴴ) {i : Fin m} {j : Fin p}
    (hij : (i : ℕ) + 2 < j) : givensHessenbergR H i j = 0 := by
  exact (givensHessenbergState_snd_apply_eq_zero_of_add_two_lt hH' p).1 i j hij

/-- Nonzero pivots exactly at full column rank: for upper Hessenberg $\mathbf{H}$ with
$p \le m$, the diagonal of $\mathbf{R}$ has no zero iff $\mathbf{H}$ has full column rank. -/
theorem forall_givensHessenbergR_apply_self_ne_zero_iff {H : Matrix (Fin m) (Fin p) 𝕜}
    (hH : IsUpperHessenberg H) (h : p ≤ m) :
    (∀ i : Fin p, givensHessenbergR H (Fin.castLE h i) i ≠ 0) ↔ Function.Injective H.mulVec := by
  exact (isQR_givensHessenberg hH h).injective_mulVec_iff.symm

/-- A rotation in a plane of the leading coordinates acts on the leading coordinates as the
rotation of the leading block. -/
private theorem givens_mulVec_castLE {r s : ℕ} (h : r ≤ s) {i j : Fin r} (hij : i ≠ j)
    (c d : 𝕜) (x : Fin s → 𝕜) (a : Fin r) :
    (givens (Fin.castLE h i) (Fin.castLE h j) c d *ᵥ x) (Fin.castLE h a) =
      (givens i j c d *ᵥ (x ∘ Fin.castLE h)) a := by
  have hinj := Fin.castLE_injective h
  have hij' : Fin.castLE h i ≠ Fin.castLE h j := hinj.ne hij
  by_cases hai : a = i
  · subst hai
    rw [givens_mulVec_apply_left hij', givens_mulVec_apply_left hij]
    rfl
  by_cases haj : a = j
  · subst haj
    rw [givens_mulVec_apply_right hij', givens_mulVec_apply_right hij]
    rfl
  · rw [givens_mulVec_apply_of_ne (hinj.ne hai) (hinj.ne haj), givens_mulVec_apply_of_ne hai haj]
    rfl

/-- **Givens QR restricts to leading blocks**: for $j \le k$, the first $j$ steps of Givens QR of
$\mathbf{H}$ restricted to the leading $(k + 1) \times k$ block are the first $j$ steps of Givens
QR of that block (the rotations of steps $j < k$ act on rows $j, j + 1 \le k$ with coefficients
from the block), and so is the rotated $\mathbf{e}_0$ on its first $k + 1$ entries. -/
private theorem givensHessenbergState_castLE {q : ℕ} (H : Matrix (Fin (q + 1)) (Fin q) 𝕜)
    {k : ℕ} (hk : k ≤ q) {j : ℕ} (hj : j ≤ k) :
    (∀ (a : Fin (k + 1)) (b : Fin k),
      (givensHessenbergState H j).2 (Fin.castLE (Nat.succ_le_succ hk) a) (Fin.castLE hk b) =
        (givensHessenbergState
          (H.submatrix (Fin.castLE (Nat.succ_le_succ hk)) (Fin.castLE hk)) j).2 a b) ∧
      ∀ a : Fin (k + 1),
        ((givensHessenbergState H j).1ᴴ *ᵥ Pi.single 0 1) (Fin.castLE (Nat.succ_le_succ hk) a) =
          ((givensHessenbergState
            (H.submatrix (Fin.castLE (Nat.succ_le_succ hk)) (Fin.castLE hk)) j).1ᴴ *ᵥ
              Pi.single 0 1) a := by
  set Hk := H.submatrix (Fin.castLE (Nat.succ_le_succ hk)) (Fin.castLE hk) with hHk
  induction j with
  | zero =>
    refine ⟨fun a b => rfl, fun a => ?_⟩
    simp only [givensHessenbergState, Matrix.conjTranspose_one, Matrix.one_mulVec,
      Pi.single_apply, Fin.ext_iff, Fin.val_castLE, Fin.val_zero]
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hjk : j < k := by omega
    set W := (givensHessenbergState H j).2
    set W' := (givensHessenbergState Hk j).2
    have e1 : W ⟨j, by omega⟩ ⟨j, by omega⟩ = W' ⟨j, by omega⟩ ⟨j, hjk⟩ :=
      ih1 ⟨j, by omega⟩ ⟨j, hjk⟩
    have e2 : W ⟨j + 1, by omega⟩ ⟨j, by omega⟩ = W' ⟨j + 1, by omega⟩ ⟨j, hjk⟩ :=
      ih1 ⟨j + 1, by omega⟩ ⟨j, hjk⟩
    have hG : givensHessenbergStep W j =
        givens (Fin.castLE (Nat.succ_le_succ hk) ⟨j, by omega⟩)
          (Fin.castLE (Nat.succ_le_succ hk) ⟨j + 1, by omega⟩)
          (givensCoeffs (W' ⟨j, by omega⟩ ⟨j, hjk⟩) (W' ⟨j + 1, by omega⟩ ⟨j, hjk⟩)).1
          (givensCoeffs (W' ⟨j, by omega⟩ ⟨j, hjk⟩) (W' ⟨j + 1, by omega⟩ ⟨j, hjk⟩)).2 := by
      rw [givensHessenbergStep_of_lt W (by omega) (by omega) (by omega), e1, e2]
      rfl
    have hG' := givensHessenbergStep_of_lt W' (k := j) (by omega) (by omega) hjk
    have hne : (⟨j, by omega⟩ : Fin (k + 1)) ≠ ⟨j + 1, by omega⟩ :=
      Fin.ne_of_val_ne (Nat.succ_ne_self j).symm
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · change (givensHessenbergStep W j * W) _ _ = (givensHessenbergStep W' j * W') a b
      rw [hG, hG']
      refine (givens_mulVec_castLE (Nat.succ_le_succ hk) hne _ _
        (fun l => W l (Fin.castLE hk b)) a).trans ?_
      congr 1
      funext l
      exact ih1 l b
    · rw [show (givensHessenbergState H (j + 1)).1 =
          (givensHessenbergState H j).1 * (givensHessenbergStep W j)ᴴ from rfl,
        show (givensHessenbergState Hk (j + 1)).1 =
          (givensHessenbergState Hk j).1 * (givensHessenbergStep W' j)ᴴ from rfl,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hG,
        hG', givens_mulVec_castLE (Nat.succ_le_succ hk) hne]
      congr 1
      funext l
      exact ih2 l

/-- The leading block of an upper Hessenberg matrix is upper Hessenberg, and its least-squares
solution with right-hand side $\mathbf{e}_0$ is back substitution with its own Givens QR. -/
private theorem pinv_mulVec_single_eq_backSubst_givensHessenberg {k : ℕ}
    {H : Matrix (Fin (k + 1)) (Fin k) 𝕜} (hH : IsUpperHessenberg H)
    (hHk : Function.Injective H.mulVec) :
    pinv H *ᵥ Pi.single 0 1 =
      backSubst ((givensHessenbergR H).submatrix (Fin.castLE (Nat.le_succ k)) id)
        (((givensHessenbergQ H).submatrix id (Fin.castLE (Nat.le_succ k)))ᴴ *ᵥ Pi.single 0 1) ∧
      ∀ i, (givensHessenbergR H).submatrix (Fin.castLE (Nat.le_succ k)) id i i ≠ 0 := by
  have hQR := isQR_givensHessenberg hH (Nat.le_succ k)
  have hR := hQR.injective_mulVec_iff.mp hHk
  exact ⟨((isLeastSquaresSolution_iff_eq_pinv_mulVec hHk).mp
    (hQR.isLeastSquaresSolution_backSubst hR _)).symm, hR⟩

/-- **The progressive form: step $k$ solves the leading least-squares problem.** For an upper
Hessenberg $(q + 1) \times q$ matrix $\mathbf{H}$ and $k \le q$, if the leading
$(k + 1) \times k$ block has full column rank (a hypothesis on the input, equivalent to nonzero
pivots by `forall_givensHessenbergR_apply_self_ne_zero_iff`), the least-squares solution
$\mathbf{H}_k^{+}\mathbf{e}_0$ of the leading $(k + 1) \times k$ block is back substitution with
the leading $k \times k$ block of the rotated matrix and the first $k$ entries of the rotated
$\mathbf{e}_0$. Later steps do not change these blocks, so the problems of all sizes are solved
along the way. [Saad2003, §6.5.3]. -/
theorem pinv_submatrix_mulVec_single_eq_backSubst {q : ℕ} {H : Matrix (Fin (q + 1)) (Fin q) 𝕜}
    (hH : IsUpperHessenberg H) {k : ℕ} (hk : k ≤ q) (hk₁ : k + 1 ≤ q + 1)
    (hHk : Function.Injective (H.submatrix (Fin.castLE hk₁) (Fin.castLE hk)).mulVec) :
    pinv (H.submatrix (Fin.castLE hk₁) (Fin.castLE hk)) *ᵥ Pi.single 0 1 =
      backSubst ((givensHessenbergState H k).2.submatrix (fun i => Fin.castLE hk₁ i.castSucc)
          (Fin.castLE hk))
        (fun i => ((givensHessenbergState H k).1ᴴ *ᵥ Pi.single 0 1)
          (Fin.castLE hk₁ i.castSucc)) := by
  obtain ⟨h1, h2⟩ := givensHessenbergState_castLE H hk le_rfl
  have hHkH : IsUpperHessenberg (H.submatrix (Fin.castLE hk₁) (Fin.castLE hk)) :=
    fun i j hij => hH _ _ hij
  rw [(pinv_mulVec_single_eq_backSubst_givensHessenberg hHkH hHk).1]
  congr 1
  · ext a b
    exact (h1 (Fin.castLE (Nat.le_succ k) a) b).symm
  · funext a
    exact (h2 (Fin.castLE (Nat.le_succ k) a)).symm

/-- **The progressive residual**: under the full-rank hypothesis of
`pinv_submatrix_mulVec_single_eq_backSubst`, the least-squares residual of the leading block is
the modulus of entry $k$ of the rotated $\mathbf{e}_0$. This is the residual estimate of GMRES
and MINRES, read off without forming the iterate. [Saad2003, Proposition 6.9]. -/
theorem norm_sub_mulVec_pinv_submatrix_mulVec_single_eq {q : ℕ}
    {H : Matrix (Fin (q + 1)) (Fin q) 𝕜} (hH : IsUpperHessenberg H) {k : ℕ} (hk : k ≤ q)
    (hk₁ : k + 1 ≤ q + 1)
    (hHk : Function.Injective (H.submatrix (Fin.castLE hk₁) (Fin.castLE hk)).mulVec) :
    ‖WithLp.toLp 2 (Pi.single 0 1 - H.submatrix (Fin.castLE hk₁) (Fin.castLE hk)
        *ᵥ (pinv (H.submatrix (Fin.castLE hk₁) (Fin.castLE hk)) *ᵥ Pi.single 0 1))‖ =
      ‖((givensHessenbergState H k).1ᴴ *ᵥ Pi.single 0 1) (Fin.castLE hk₁ (Fin.last k))‖ := by
  set Hk := H.submatrix (Fin.castLE hk₁) (Fin.castLE hk) with hHk_def
  have hHkH : IsUpperHessenberg Hk := fun i j hij => hH _ _ hij
  obtain ⟨hx, hR⟩ := pinv_mulVec_single_eq_backSubst_givensHessenberg hHkH hHk
  set Q' := (givensHessenbergState Hk k).1
  set W' := (givensHessenbergState Hk k).2
  generalize pinv Hk *ᵥ Pi.single 0 1 = x at hx ⊢
  have hQ' : HasOrthonormalCols Q' := hasOrthonormalCols_givensHessenbergState_fst Hk k
  have hRx := mulVec_backSubst (isQR_givensHessenberg hHkH (Nat.le_succ k)).isUpperTriangular hR
    (((givensHessenbergQ Hk).submatrix id (Fin.castLE (Nat.le_succ k)))ᴴ *ᵥ Pi.single 0 1)
  rw [← hx] at hRx
  have hsplit : Q'ᴴ *ᵥ Pi.single 0 1 - W' *ᵥ x =
      Pi.single (Fin.last k) ((Q'ᴴ *ᵥ Pi.single 0 1) (Fin.last k)) := by
    funext a
    rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
    · rw [Pi.sub_apply, Pi.single_eq_of_ne (Fin.castSucc_ne_last i), sub_eq_zero]
      exact (congrFun hRx i).symm
    · rw [Pi.sub_apply, Pi.single_eq_same, sub_eq_self]
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [show W' (Fin.last k) b = 0 from
        isUpperTrapezoidal_givensHessenbergR hHkH (Fin.last k) b b.2, zero_mul]
  have hv : Pi.single 0 1 - Hk *ᵥ x =
      Q' *ᵥ Pi.single (Fin.last k) ((Q'ᴴ *ᵥ Pi.single 0 1) (Fin.last k)) := by
    rw [← hsplit, Matrix.mulVec_sub, Matrix.mulVec_mulVec (M := Q') (N := Q'ᴴ),
      hQ'.mul_conjTranspose_self, Matrix.one_mulVec, Matrix.mulVec_mulVec (M := Q') (N := W'),
      givensHessenbergState_fst_mul_snd]
  rw [hv, hQ'.norm_toLp_mulVec, PiLp.toLp_single, PiLp.norm_single,
    ← (givensHessenbergState_castLE H hk le_rfl).2 (Fin.last k)]

/-! ### The unitary factor is Hessenberg -/

/-- Step $k$ of Givens QR left-multiplies the conjugate transpose of the accumulated factor. -/
private theorem conjTranspose_givensHessenbergState_fst_succ (H : Matrix (Fin m) (Fin p) 𝕜)
    (k : ℕ) :
    ((givensHessenbergState H (k + 1)).1)ᴴ =
      givensHessenbergStep (givensHessenbergState H k).2 k * ((givensHessenbergState H k).1)ᴴ := by
  rw [show (givensHessenbergState H (k + 1)).1 = (givensHessenbergState H k).1 *
      (givensHessenbergStep (givensHessenbergState H k).2 k)ᴴ from rfl,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Invariant of the conjugate transpose of the accumulated factor after $k$ steps: its rows
above $k$ vanish beyond the superdiagonal, its row $k$ vanishes beyond column $k$, and its rows
from $k + 1$ on are unit vectors. -/
private theorem conjTranspose_givensHessenbergState_fst_invariant (H : Matrix (Fin m) (Fin p) 𝕜)
    (k : ℕ) :
    (∀ a b : Fin m, (a : ℕ) < k → (a : ℕ) + 1 < b →
      ((givensHessenbergState H k).1)ᴴ a b = 0) ∧
    (∀ a b : Fin m, (a : ℕ) = k → k < (b : ℕ) → ((givensHessenbergState H k).1)ᴴ a b = 0) ∧
    (∀ a b : Fin m, k + 1 ≤ (a : ℕ) →
      ((givensHessenbergState H k).1)ᴴ a b = if a = b then 1 else 0) := by
  induction k with
  | zero =>
    simp only [givensHessenbergState, Matrix.conjTranspose_one]
    refine ⟨fun a b h => absurd h (Nat.not_lt_zero _), fun a b _ hb => ?_, fun a b _ => rfl⟩
    exact Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega))
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [conjTranspose_givensHessenbergState_fst_succ]
    -- rows `k` and `k + 1` both vanish beyond column `k + 1`
    have hzero : ∀ b : Fin m, k + 1 < (b : ℕ) → ∀ c : Fin m,
        ((c : ℕ) = k ∨ (c : ℕ) = k + 1) → ((givensHessenbergState H k).1)ᴴ c b = 0 := by
      intro b hb c hc
      rcases hc with hc | hc
      · exact h2 c b hc (by omega)
      · rw [h3 c b (by omega), if_neg]
        intro h
        subst h
        omega
    refine ⟨fun a b ha hab => ?_, fun a b ha hab => ?_, fun a b ha => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha' | ha'
      · rw [givensHessenbergStep_mul_apply_of_ne (k := k) (a := a) _ _ (by omega) (by omega)]
        exact h1 a b ha' hab
      · rw [givensHessenbergStep_mul_apply_of_apply_eq_zero _ _ (b := b)
          (fun c hc => hzero b (by omega) c hc)]
        exact hzero b (by omega) a (Or.inl ha')
    · rw [givensHessenbergStep_mul_apply_of_apply_eq_zero _ _ (b := b)
        (fun c hc => hzero b hab c hc)]
      exact hzero b hab a (Or.inr ha)
    · rw [givensHessenbergStep_mul_apply_of_ne (k := k) (a := a) _ _ (by omega) (by omega)]
      exact h3 a b (by omega)

/-- **The unitary factor of Givens QR is upper Hessenberg**: for every
$\mathbf{H} \in \Bbbk^{m \times p}$, the factor $\mathbf{G}_0^{\mathsf{H}} \cdots
\mathbf{G}_{p-1}^{\mathsf{H}}$ (`NLAlib.givensHessenbergQ`), a product of rotations in the planes
$(k, k+1)$ in increasing order, vanishes below the first subdiagonal. No hypothesis on
$\mathbf{H}$: the planes, not the coefficients, give the pattern. [GolubVanLoan2013, §5.2.5]. -/
theorem isUpperHessenberg_givensHessenbergQ (H : Matrix (Fin m) (Fin p) 𝕜) :
    IsUpperHessenberg (givensHessenbergQ H) := by
  intro i j hij
  have h := conjTranspose_givensHessenbergState_fst_invariant H p
  have hT : ((givensHessenbergState H p).1)ᴴ j i = 0 := by
    rcases lt_trichotomy (j : ℕ) p with hjp | hjp | hjp
    · exact h.1 j i hjp hij
    · exact h.2.1 j i hjp (by omega)
    · rw [h.2.2 j i (by omega), if_neg]
      intro hji
      subst hji
      omega
  rw [Matrix.conjTranspose_apply, star_eq_zero] at hT
  exact hT

/-! ### The unitary factor and the untouched rows -/

/-- The unitary factor of Givens QR has orthonormal columns. -/
theorem hasOrthonormalCols_givensHessenbergQ (H : Matrix (Fin m) (Fin p) 𝕜) :
    HasOrthonormalCols (givensHessenbergQ H) :=
  hasOrthonormalCols_givensHessenbergState_fst _ _

/-- The first $j \le i$ steps of Givens QR leave row $i + 1$ of the input alone. -/
theorem givensHessenbergState_snd_apply_of_eq_add_one (A : Matrix (Fin m) (Fin p) 𝕜) {i j : ℕ}
    (hj : j ≤ i) {a : Fin m} (ha : (a : ℕ) = i + 1) (b : Fin p) :
    (givensHessenbergState A j).2 a b = A a b := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [givensHessenbergState_succ_snd, givensHessenbergStep_mul_apply_of_ne _ _ (by omega)
      (by omega)]
    exact ih (by omega)

/-- The first $j \le i$ steps of Givens QR keep the coordinates up to $i$ of a vector zero: if
$\mathbf{v}_a = 0$ for $a \le i$, then so is $(\mathbf{S}_j^{\mathsf{H}}\mathbf{v})_a$, with
$\mathbf{S}_j$ the accumulated unitary factor after $j$ steps. -/
theorem givensHessenbergState_fst_mulVec_apply_eq_zero_of_le (A : Matrix (Fin m) (Fin p) 𝕜)
    {v : Fin m → 𝕜} {i : ℕ} (hv : ∀ a : Fin m, (a : ℕ) ≤ i → v a = 0) {j : ℕ} (hj : j ≤ i)
    (a : Fin m) (ha : (a : ℕ) ≤ i) : ((givensHessenbergState A j).1ᴴ *ᵥ v) a = 0 := by
  induction j generalizing a with
  | zero =>
    simp only [givensHessenbergState, Matrix.conjTranspose_one, Matrix.one_mulVec]
    exact hv a ha
  | succ j ih =>
    rw [conjTranspose_givensHessenbergState_succ_fst_mulVec]
    exact (givensHessenbergStep_mul_apply_of_apply_eq_zero _
      (Matrix.of fun i (_ : Unit) => ((givensHessenbergState A j).1ᴴ *ᵥ v) i) (b := ())
      (fun a' ha' => ih (by omega) a' (by omega)) a).trans (ih (by omega) a ha)

end GivensHessenbergQR

end NLAlib
