/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.GivensLog

/-!
# Replay of slotted Givens logs

A replay recomputes the coefficients of each valid entry of a slotted log from its stored inputs and
applies the rotations to the rows or the columns of another matrix (`NLAlib.givensReplayRows`,
`NLAlib.givensReplayColumns`); on every tape each replayed rotation moves its operand by at most
$24\boldsymbol{u}$ times its norm from the exact product, so the replay is within
$(1 + 24\boldsymbol{u})^{R} - 1$ of the exact unitary of the log.

## Main definitions

* `NLAlib.givensReplayRows`, `NLAlib.givensReplayColumns`: replay the valid slots.

## Main results

* `NLAlib.givensReplayColumns_specNorm_sub_le`, `NLAlib.givensReplayRows_specNorm_sub_le`: the
  replay is within $(1 + 24\boldsymbol{u})^{R} - 1$ of the exact product, on every tape.
* `NLAlib.one_add_mul_pow_sub_one_le`: from the identity, within
  $27R\boldsymbol{u}$ when $24R\boldsymbol{u} \le 1/8$.
* `NLAlib.givensReplayRows_writes_word`, `NLAlib.givensReplayColumns_writes_word`: the words of a
  replay on a range.
* `NLAlib.givensReplayColumns_specNorm_sub_le_if`: the column replay on any machine, with its
  error bound under the standard model.
-/

@[expose] public section

namespace NLAlib

open Ops
open scoped Matrix

/-! ### Replay -/

section Replay

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **Replay a log with a rotation routine** `Rot` of interface `[ld, k, j0, nc] (A, C, S, T) → (A)`
(planes $k, k + 1$, a range $j_0, \dots, j_0 + n_c - 1$): for the valid slots in order (`ns`
slots of `w` entries), recompute each entry's coefficients and call `Rot` at the plane
`lo + r`. The plane is read with the bound `ld`. `[ld, lo, j0, nc, ns, w] (Lg, A) → (A)`. -/
def givensReplayWith (Rot : Stmt O Q) : Stmt O Q :=
    ops% [ld, lo, j0, nc, ns, w] (Lg, A) → (A) {
  let Cf ← alloc 4;
  let T ← alloc 10;
  for s < ns {
    if (Has.inj CmpTst.isPos) [] (Lg[s * (1 + 5 * w)]) {
      for i < w {
        let r ← index (Has.inj IdxTst.toNat) (Lg[s * (1 + 5 * w) + 1 + 5 * i]) ≤ ld;
        run (coefficients (Op := O) (Tst := Q)) []
          (Lg[s * (1 + 5 * w) + 2 + 5 * i], Lg[s * (1 + 5 * w) + 4 + 5 * i], Cf, Cf[2]);
        run Rot [ld, lo + r, j0, nc] (A, Cf, Cf[2], T, A)
      }
    } else { skip }
  }
}

/-- **Replay a log on rows**: rotate the rows `lo + r, lo + r + 1` of `A` over the columns
`j0, …, j0 + nc - 1` (`NLAlib.rotateRowsOn`). `[ld, lo, j0, nc, ns, w] (Lg, A) → (A)`. -/
def givensReplayRows : Stmt O Q := givensReplayWith (rotateRowsOn (Op := O) (Tst := Q))

/-- **Replay a log on columns** (right multiplication by the computed adjoint rotations) over the
rows `i0, …, i0 + nr - 1` (`NLAlib.rotateColumnsOn`). `[ld, lo, i0, nr, ns, w] (Lg, A) → (A)`. -/
def givensReplayColumns : Stmt O Q := givensReplayWith (rotateColumnsOn (Op := O) (Tst := Q))

end Replay

/-! ### The replayed words and their error -/

section ReplayWords

/-- A product of square matrices with orthonormal columns has orthonormal columns. -/
theorem hasOrthonormalCols_list_prod {n : ℕ} (l : List (Matrix (Fin n) (Fin n) ℂ))
    (h : ∀ U ∈ l, HasOrthonormalCols U) : HasOrthonormalCols l.prod := by
  induction l with
  | nil => exact hasOrthonormalCols_one
  | cons U l ih =>
    rw [List.prod_cons]
    exact (h U (by simp)).mul (ih fun V hV => h V (by simp [hV]))

/-- Errors along right multiplications by unitaries add up relatively: if each step $f$
moves $\mathbf{Y}$ to within $\eta\|\mathbf{Y}\|_2$ of $\mathbf{Y}\mathbf{U}_a$, $\mathbf{U}_a$
unitary, then $k$ steps from $\mathbf{X}$ end within $((1 + \eta)^k - 1)\|\mathbf{X}\|_2$ of
$\mathbf{X}\mathbf{U}_{a_1}\cdots\mathbf{U}_{a_k}$. -/
theorem specNorm_foldl_sub_mul_prod_le {α : Type*} {n : ℕ}
    (f : Matrix (Fin n) (Fin n) ℂ → α → Matrix (Fin n) (Fin n) ℂ)
    (U : α → Matrix (Fin n) (Fin n) ℂ) {η : ℝ} (hη : 0 ≤ η) (as : List α)
    (hU : ∀ a ∈ as, HasOrthonormalCols (U a))
    (hf : ∀ a ∈ as, ∀ Y, specNorm (f Y a - Y * U a) ≤ η * specNorm Y)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    specNorm (as.foldl f X - X * (as.map U).prod) ≤ ((1 + η) ^ as.length - 1) * specNorm X := by
  induction as using List.reverseRecOn with
  | nil => simp
  | append_singleton as a ih =>
    have ih := ih (fun b hb => hU b (by simp [hb])) (fun b hb => hf b (by simp [hb]))
    set Y := as.foldl f X
    set P := (as.map U).prod
    have ha := hf a (by simp) Y
    have hY : specNorm Y ≤ specNorm X + ((1 + η) ^ as.length - 1) * specNorm X := by
      have e : Y = (Y - X * P) + X * P := by abel
      have := specNorm_add_le (Y - X * P) (X * P)
      rw [← e] at this
      have hP : HasOrthonormalCols P := hasOrthonormalCols_list_prod _ fun V hV => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hV
        exact hU b (by simp [hb])
      rw [hP.specNorm_mul_right] at this
      linarith
    have e : f Y a - X * (P * U a) = (f Y a - Y * U a) + (Y - X * P) * U a := by
      rw [Matrix.sub_mul, Matrix.mul_assoc]; abel
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append, List.map_cons,
      List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, Matrix.mul_one,
      List.length_append, List.length_singleton]
    rw [e]
    refine (specNorm_add_le _ _).trans ?_
    rw [(hU a (by simp)).specNorm_mul_right]
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hY hη, specNorm_nonneg X]

/-- Errors along left multiplications by unitaries add up relatively: the mirror of
`NLAlib.specNorm_foldl_sub_mul_prod_le`, each step within $\eta\|\mathbf{Y}\|_2$ of
$\mathbf{U}_a^{\mathsf H}\mathbf{Y}$. -/
theorem specNorm_foldl_sub_prod_mul_le {α : Type*} {n : ℕ}
    (f : Matrix (Fin n) (Fin n) ℂ → α → Matrix (Fin n) (Fin n) ℂ)
    (U : α → Matrix (Fin n) (Fin n) ℂ) {η : ℝ} (hη : 0 ≤ η) (as : List α)
    (hU : ∀ a ∈ as, HasOrthonormalCols (U a))
    (hf : ∀ a ∈ as, ∀ Y, specNorm (f Y a - (U a)ᴴ * Y) ≤ η * specNorm Y)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    specNorm (as.foldl f X - ((as.map U).prod)ᴴ * X) ≤
      ((1 + η) ^ as.length - 1) * specNorm X := by
  have hg := specNorm_foldl_sub_mul_prod_le (fun Y a => (f Yᴴ a)ᴴ) U hη as hU (fun a ha Y => by
    have e : (f Yᴴ a)ᴴ - Y * U a = (f Yᴴ a - (U a)ᴴ * Yᴴ)ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    rw [e, specNorm_conjTranspose, ← specNorm_conjTranspose Y]
    exact hf a ha Yᴴ) Xᴴ
  have hfold : ∀ (bs : List α) (Z : Matrix (Fin n) (Fin n) ℂ),
      bs.foldl (fun Y a => (f Yᴴ a)ᴴ) Zᴴ = (bs.foldl f Z)ᴴ := by
    intro bs
    induction bs with
    | nil => intro Z; rfl
    | cons b bs ih => intro Z; simp only [List.foldl_cons, Matrix.conjTranspose_conjTranspose, ih]
  rw [hfold, specNorm_conjTranspose] at hg
  have e : (as.foldl f X)ᴴ - Xᴴ * (as.map U).prod = (as.foldl f X - ((as.map U).prod)ᴴ * X)ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rwa [e, specNorm_conjTranspose] at hg

/-- One replayed entry on the columns, as the machine computes it: the coefficients rounded from
$(p, q)$, then the machine rotation of the columns $lo + r, lo + r + 1$ over the rows
$i_0, \dots, i_0 + n_r - 1$; nothing out of range. -/
noncomputable def replayColumnStep (M : Machine ℝ) {N : ℕ} (lo i0 nr : ℕ)
    (X : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) : Matrix (Fin N) (Fin N) ℂ :=
  if h : lo + e.1 + 1 < N then
    machineColRotationOn M ⟨lo + e.1, by omega⟩ ⟨lo + e.1 + 1, h⟩
      (roundedGivensCoeffs M e.2.1 e.2.2).1 (roundedGivensCoeffs M e.2.1 e.2.2).2 i0 nr X
  else X

/-- One replayed entry on the rows $lo + r, lo + r + 1$ over the columns
$j_0, \dots, j_0 + n_c - 1$, as the machine computes it; nothing out of range. -/
noncomputable def replayRowStep (M : Machine ℝ) {N : ℕ} (lo j0 nc : ℕ)
    (X : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) : Matrix (Fin N) (Fin N) ℂ :=
  if h : lo + e.1 + 1 < N then
    machineRowRotationOn M ⟨lo + e.1, by omega⟩ ⟨lo + e.1 + 1, h⟩
      (roundedGivensCoeffs M e.2.1 e.2.2).1 (roundedGivensCoeffs M e.2.1 e.2.2).2 j0 nc X
  else X

/-- The embedded rotation of an entry inside the block, or of the zero fill, is the Givens
rotation of the shifted plane. -/
theorem embedBlock_givensAt_eq_givens {N lo d : ℕ} (hN : lo + d ≤ N) {e : GivensEntry}
    (he : lo + e.1 + 1 < N) (he' : e.1 + 1 < d ∨ e = (0, 0, 0)) :
    embedBlock (N := N) lo (givensAt d e) = givens (⟨lo + e.1, by omega⟩ : Fin N)
      ⟨lo + e.1 + 1, he⟩ (givensCoeffs e.2.1 e.2.2).1 (givensCoeffs e.2.1 e.2.2).2 := by
  rcases he' with he' | rfl
  · rw [embedBlock_givensAt hN he']
    simp only [givensAt, dif_pos (show lo + e.1 + 1 < N from he)]
  · rw [givensAt_zero, embedBlock_one]
    simp [givensCoeffs, givens]

/-- The embedded unitary of a log is the product of the embedded adjoint rotations. -/
theorem prod_map_embedBlock_givensAt {N lo d : ℕ} (hN : lo + d ≤ N) (es : List GivensEntry) :
    (es.map fun e => (embedBlock (N := N) lo (givensAt d e))ᴴ).prod =
      embedBlock lo (givensLog d es) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    rw [List.map_cons, List.prod_cons, ih, embedBlock_conjTranspose, ← embedBlock_mul hN]
    rfl

/-- The column replay of one entry is within $24\boldsymbol{u}\|\mathbf{Y}\|_2$ of the product by
the embedded exact adjoint rotation. [Higham2002, Lemma 19.8]. -/
theorem specNorm_replayColumnStep_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) {N lo d : ℕ} (hN : lo + d ≤ N) {e : GivensEntry}
    (he : lo + e.1 + 1 < N) (he' : e.1 + 1 < d ∨ e = (0, 0, 0)) (Y : Matrix (Fin N) (Fin N) ℂ) :
    specNorm (replayColumnStep M lo 0 N Y e - Y * (embedBlock lo (givensAt d e))ᴴ) ≤
      24 * u * specNorm Y := by
  have hij : (⟨lo + e.1, by omega⟩ : Fin N) ≠ ⟨lo + e.1 + 1, he⟩ := Fin.ne_of_val_ne (by simp)
  have hon : replayColumnStep M lo 0 N Y e = machineColRotation M (⟨lo + e.1, by omega⟩ : Fin N)
      ⟨lo + e.1 + 1, he⟩
      (roundedGivensCoeffs M e.2.1 e.2.2).1 (roundedGivensCoeffs M e.2.1 e.2.2).2 Y := by
    ext r t
    simp [replayColumnStep, he, machineColRotationOn]
  rw [hon, embedBlock_givensAt_eq_givens hN he he']
  have h := (isRoundedColRotation_machineColRotation hM hu0 hu hij e.2.1 e.2.2 Y).specNorm_sub_le
    (by positivity)
  linarith

/-- The row replay of one entry over all columns is within $24\boldsymbol{u}\|\mathbf{Y}\|_2$ of
the product by the embedded exact rotation. [Higham2002, Lemma 19.8]. -/
theorem specNorm_replayRowStep_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) {N lo d : ℕ} (hN : lo + d ≤ N) {e : GivensEntry}
    (he : lo + e.1 + 1 < N) (he' : e.1 + 1 < d ∨ e = (0, 0, 0)) (Y : Matrix (Fin N) (Fin N) ℂ) :
    specNorm (replayRowStep M lo 0 N Y e - embedBlock lo (givensAt d e) * Y) ≤
      24 * u * specNorm Y := by
  have hij : (⟨lo + e.1, by omega⟩ : Fin N) ≠ ⟨lo + e.1 + 1, he⟩ := Fin.ne_of_val_ne (by simp)
  have hon : replayRowStep M lo 0 N Y e = machineRowRotation M (⟨lo + e.1, by omega⟩ : Fin N)
      ⟨lo + e.1 + 1, he⟩
      (roundedGivensCoeffs M e.2.1 e.2.2).1 (roundedGivensCoeffs M e.2.1 e.2.2).2 Y := by
    ext r t
    simp [replayRowStep, he, machineRowRotationOn]
  rw [hon, embedBlock_givensAt_eq_givens hN he he']
  have h := (isRoundedRowRotation_machineRowRotation hM hu0 hu hij e.2.1 e.2.2 Y).specNorm_sub_le
    (by positivity)
  linarith

/-- The column replay of a log on the machine is within
$((1 + 24\boldsymbol{u})^{R} - 1)\|\mathbf{X}\|_2$ of $\mathbf{X}\widetilde{\mathbf{V}}$, $R$ the
number of entries and $\widetilde{\mathbf{V}}$ the log's unitary on $[lo, lo + d)$; every entry
is inside the block or the zero fill, with its two columns in range. -/
theorem specNorm_foldl_replayColumnStep_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) {N lo d : ℕ} (hN : lo + d ≤ N) (es : List GivensEntry)
    (hes : ∀ e ∈ es, lo + e.1 + 1 < N ∧ (e.1 + 1 < d ∨ e = (0, 0, 0)))
    (X : Matrix (Fin N) (Fin N) ℂ) :
    specNorm (es.foldl (replayColumnStep M lo 0 N) X - X * embedBlock lo (givensLog d es)) ≤
      ((1 + 24 * u) ^ es.length - 1) * specNorm X := by
  rw [← prod_map_embedBlock_givensAt hN]
  refine specNorm_foldl_sub_mul_prod_le _ _ (by positivity) es (fun e he => ?_)
    (fun e he Y => specNorm_replayColumnStep_sub_le hM hu0 hu hN (hes e he).1 (hes e he).2 Y) X
  rw [embedBlock_givensAt_eq_givens hN (hes e he).1 (hes e he).2]
  exact (hasOrthonormalCols_givens (Fin.ne_of_val_ne (by simp))
    (norm_givensCoeffs_fst_sq_add _ _)).conjTranspose

/-- The row replay of a log over all columns on the machine is within
$((1 + 24\boldsymbol{u})^{R} - 1)\|\mathbf{X}\|_2$ of
$\widetilde{\mathbf{V}}^{\mathsf H}\mathbf{X}$, under the conditions of
`NLAlib.specNorm_foldl_replayColumnStep_sub_le`. -/
theorem specNorm_foldl_replayRowStep_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) {N lo d : ℕ} (hN : lo + d ≤ N) (es : List GivensEntry)
    (hes : ∀ e ∈ es, lo + e.1 + 1 < N ∧ (e.1 + 1 < d ∨ e = (0, 0, 0)))
    (X : Matrix (Fin N) (Fin N) ℂ) :
    specNorm (es.foldl (replayRowStep M lo 0 N) X - (embedBlock lo (givensLog d es))ᴴ * X) ≤
      ((1 + 24 * u) ^ es.length - 1) * specNorm X := by
  rw [← prod_map_embedBlock_givensAt hN]
  refine specNorm_foldl_sub_prod_mul_le _ _ (by positivity) es (fun e he => ?_)
    (fun e he Y => by
      rw [Matrix.conjTranspose_conjTranspose]
      exact specNorm_replayRowStep_sub_le hM hu0 hu hN (hes e he).1 (hes e he).2 Y) X
  rw [embedBlock_givensAt_eq_givens hN (hes e he).1 (hes e he).2]
  exact (hasOrthonormalCols_givens (Fin.ne_of_val_ne (by simp))
    (norm_givensCoeffs_fst_sq_add _ _)).conjTranspose

/-- The diagonal projection on the columns $j_0, \dots, j_0 + n_c - 1$. -/
noncomputable def colMask (N j0 nc : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun t => if j0 ≤ (t : ℕ) ∧ (t : ℕ) < j0 + nc then 1 else 0

/-- The column mask is an orthogonal projection. -/
theorem isStarProjection_colMask (N j0 nc : ℕ) : IsStarProjection (colMask N j0 nc) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, colMask, Matrix.diagonal_mul_diagonal]
    congr 1; funext t
    by_cases h : j0 ≤ (t : ℕ) ∧ (t : ℕ) < j0 + nc
    · rw [if_pos h, mul_one]
    · rw [if_neg h, mul_zero]
  · rw [IsSelfAdjoint, colMask, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext t
    by_cases h : j0 ≤ (t : ℕ) ∧ (t : ℕ) < j0 + nc
    · simp only [Pi.star_apply, if_pos h, star_one]
    · simp only [Pi.star_apply, if_neg h, star_zero]

/-- A row replay on a column range, masked to the range, is the replay over all columns of the
masked matrix: the machine rotation acts column by column and keeps zero columns. -/
theorem replayRowStep_mul_colMask {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) {N : ℕ}
    (lo j0 nc : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) :
    replayRowStep M lo j0 nc X e * colMask N j0 nc =
      replayRowStep M lo 0 N (X * colMask N j0 nc) e := by
  ext a t
  by_cases h : lo + e.1 + 1 < N
  · simp only [replayRowStep, dif_pos h, colMask, Matrix.mul_diagonal, machineRowRotationOn,
      Matrix.of_apply, machineRowRotation]
    by_cases ht : j0 ≤ (t : ℕ) ∧ (t : ℕ) < j0 + nc
    · simp [ht]
    · simp only [ht, if_false, mul_zero, Nat.zero_le, zero_add, t.isLt, and_self, if_true]
      split_ifs <;> simp [linearComplex_zero_zero hM]
  · simp [replayRowStep, h]

/-- A row replay on a column range keeps the other columns. -/
theorem replayRowStep_apply_of_not_mem {M : Machine ℝ} {N : ℕ} {lo j0 nc : ℕ}
    (X : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) (i t : Fin N)
    (ht : ¬(j0 ≤ (t : ℕ) ∧ (t : ℕ) < j0 + nc)) : replayRowStep M lo j0 nc X e i t = X i t := by
  unfold replayRowStep
  split_ifs
  · simp [machineRowRotationOn, ht]
  · rfl

/-- The masked row replay of a log is the full row replay of the masked matrix. -/
theorem foldl_replayRowStep_mul_colMask {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) {N : ℕ}
    (lo j0 nc : ℕ) (es : List GivensEntry) (X : Matrix (Fin N) (Fin N) ℂ) :
    es.foldl (replayRowStep M lo j0 nc) X * colMask N j0 nc =
      es.foldl (replayRowStep M lo 0 N) (X * colMask N j0 nc) := by
  induction es generalizing X with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons, ih, replayRowStep_mul_colMask hM]

/-- The row replay of a log on a column range keeps the other columns. -/
theorem foldl_replayRowStep_apply_of_not_mem {M : Machine ℝ} {N : ℕ} {lo j0 nc : ℕ}
    (es : List GivensEntry) (X : Matrix (Fin N) (Fin N) ℂ) (i t : Fin N)
    (ht : ¬(j0 ≤ (t : ℕ) ∧ (t : ℕ) < j0 + nc)) :
    es.foldl (replayRowStep M lo j0 nc) X i t = X i t := by
  induction es generalizing X with
  | nil => rfl
  | cons e es ih => rw [List.foldl_cons, ih, replayRowStep_apply_of_not_mem _ _ _ _ ht]

end ReplayWords

section ReplaySpecs

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]
  [Inhabited ℝ]

/-- The replay of one entry, as it appears in `NLAlib.givensReplayWith`: the plane read with the
bound `ld`, the coefficients, the rotation. -/
private def replayEntryStmt (Rot : Stmt O Q) : Stmt O Q :=
  Stmt.bindIdx (Has.inj IdxTst.toNat)
    [{ buf := 0, off := IExp.var 6 + IExp.var 9 * (IExp.const 1 + IExp.const 5 * IExp.var 5) +
      IExp.const 1 + IExp.const 5 * IExp.var 10 }]
    (IExp.var 0)
    ((Stmt.frame []
        [{ buf := 0, off := IExp.var 6 + IExp.var 9 * (IExp.const 1 + IExp.const 5 * IExp.var 5) +
            IExp.const 2 + IExp.const 5 * IExp.var 10 },
          { buf := 0, off := IExp.var 6 + IExp.var 9 * (IExp.const 1 + IExp.const 5 * IExp.var 5) +
            IExp.const 4 + IExp.const 5 * IExp.var 10 },
          { buf := 3, off := IExp.const 0 }, { buf := 3, off := IExp.const 2 }]
        (coefficients (Op := O) (Tst := Q))).seq
      (Stmt.frame [IExp.var 0, IExp.var 1 + IExp.var 11, IExp.var 2, IExp.var 3]
        [{ buf := 1, off := IExp.var 7 }, { buf := 3, off := IExp.const 0 },
          { buf := 3, off := IExp.const 2 }, { buf := 4, off := IExp.const 0 },
          { buf := 1, off := IExp.var 7 }]
        Rot))

omit [Has IndexOp O] [Inhabited ℝ] in
/-- The replay of one entry whose two planes are in range stores the rotation word of the
coefficients rounded from the entry.
A step in the proof of `NLAlib.givensReplayWith_writes_word`. -/
private theorem replayEntryStmt_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hQ : IsToNat id I) (hC : IsCmp id I) {Rot : Stmt O Q}
    {N lo j0 nc ns w : ℕ} {lg x : ℕ × ℕ}
    {rotWord : ℕ → ℂ → ℂ → Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hRot : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {k : ℕ} {c s t : ℕ × ℕ} {Y : Matrix (Fin N) (Fin N) ℂ}
      {cv sv : ℂ}, k + 1 < N → HoldsMatrix x Y μ.store →
      μ.store.readBlock c.1 c.2 2 = some [cv.re, cv.im] →
      μ.store.readBlock s.1 s.2 2 = some [sv.re, sv.im] →
      Fp.Disj (Store.inBlock x.1 x.2 (2 * (N * N))) (Store.inBlock c.1 c.2 2) →
      Fp.Disj (Store.inBlock x.1 x.2 (2 * (N * N))) (Store.inBlock s.1 s.2 2) →
      t.1 ≠ x.1 → t.1 ≠ c.1 → t.1 ≠ s.1 → t.2 + 10 ≤ μ.store.len t.1 →
      Writes .total I τ Rot (Env.frame [N, k, j0, nc] [x, c, s, t, x])
        (Store.inBlock x.1 x.2 (2 * (N * N)) ⊔ Store.inBlock t.1 t.2 10)
        (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix x (rotWord k cv sv Y) μ'.store) μ)
    {ρ : Env} {sl i Lc : ℕ} (hidx : ρ.idx = [N, lo, j0, nc, ns, w, lg.2, x.2, x.2, sl, i])
    (hbuf : ρ.buf = [lg.1, x.1, x.1, Lc, Lc + 1]) {e : GivensEntry} (he : lo + e.1 + 1 < N)
    {τ : Tape ℝ} {μ : Mem ℝ}
    (hw : μ.store.readBlock lg.1 (lg.2 + sl * (1 + 5 * w) + 1 + 5 * i) 5 = some (entryWords e))
    {Y : Matrix (Fin N) (Fin N) ℂ} (hY : HoldsMatrix x Y μ.store) (hlen : μ.store.length = Lc + 2)
    (hL0 : μ.store.len Lc = 4) (hL1 : μ.store.len (Lc + 1) = 10) (hxL : x.1 < Lc) :
    Writes .total I τ (replayEntryStmt Rot) ρ
      (Store.inBlock x.1 x.2 (2 * (N * N)) ⊔ Store.inBlock Lc 0 4 ⊔ Store.inBlock (Lc + 1) 0 10)
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix x (rotWord (lo + e.1)
        (roundedGivensCoeffs Mch e.2.1 e.2.2).1 (roundedGivensCoeffs Mch e.2.1 e.2.2).2 Y)
          μ'.store) μ := by
  set o := lg.2 + sl * (1 + 5 * w) + 1 + 5 * i with ho
  have hg (k : ℕ) (hk : k < 5) : μ.store.get lg.1 (o + k) = some ((entryWords e).getD k 0) :=
    Store.get_of_readBlock hw hk 0
  have hXC : Fp.Disj (Store.inBlock x.1 x.2 (2 * (N * N))) (Store.inBlock Lc 0 4) :=
    Fp.disj_inBlock_of_ne (by omega)
  have hcs : Fp.Disj (Store.inBlock Lc 0 2) (Store.inBlock Lc 2 2) := Fp.disj_inBlock_of_le le_rfl
  have h1 : Store.inBlock Lc 0 2 ≤ Store.inBlock Lc 0 4 := Fp.inBlock_le_inBlock le_rfl (by omega)
  have h2 : Store.inBlock Lc 2 2 ≤ Store.inBlock Lc 0 4 :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hc4 : Fp.blocks [(Lc, 0), (Lc, 2)] [2, 2] ≤ Store.inBlock Lc 0 4 := by
    simpa only [Fp.blocks, sup_bot_eq] using sup_le h1 h2
  have hgl : lg.1 < Lc + 2 := hlen ▸ Store.lt_length_of_get (hg 0 (by omega))
  unfold replayEntryStmt
  refine writes_bindIdx_of_decode_nat hQ (x := (lg.1, o + 0)) (w := (e.1 : ℝ)) (B := N)
    (by simp [Operand.eval, hidx, hbuf, IExp.eval, ho]) (by simp [IExp.eval, hidx])
    (by simpa [entryWords] using hg 0 (by omega)) rfl (by omega) ?_
  refine (coefficients_writes_word (τ := τ) (a := (lg.1, o + 1)) (b := (lg.1, o + 3))
    (c := (Lc, 0)) (s := (Lc, 2)) (u := e.2.1) (v := e.2.2) hS hC hcs
    (by simpa [entryWords] using hg 1 (by omega)) (by simpa [entryWords] using hg 2 (by omega))
    (by simpa [entryWords] using hg 3 (by omega)) (by simpa [entryWords] using hg 4 (by omega))
    (by simp [hL0]) (by simp [hL0])).frame_seq_le rfl
    (by simp [Operand.evalList, Operand.eval, Env.pushIdx, hidx, hbuf, IExp.eval, ho]; omega)
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> simp only [hlen] <;> omega)
    (hc4.trans (le_sup_right.trans le_sup_left)) ?_
  rintro μ₁ hfr₁ ⟨hp₁, hcs₁⟩
  have hc₁ := (Mem.readBlocks_cons_iff.mp hcs₁).1
  have hs₁ := (Mem.readBlocks_cons_iff.mp (Mem.readBlocks_cons_iff.mp hcs₁).2).1
  refine ((hRot (τ := τ) (k := lo + e.1) (t := (Lc + 1, 0)) he
    (hY.of_eqOff hfr₁ (hXC.symm.mono hc4 le_rfl)) hc₁ hs₁
    (hXC.mono le_rfl (Fp.inBlock_le_inBlock le_rfl (by omega)))
    (hXC.mono le_rfl (Fp.inBlock_le_inBlock (by omega) (by omega))) (by simp; omega)
    (by simp) (by simp) (by simp [hfr₁.len_eq, hL1])).in_frame
    (by simp [IExp.evalList, IExp.eval, Env.pushIdx, hidx])
    (by simp [Operand.evalList, Operand.eval, Env.pushIdx, hidx, hbuf, IExp.eval])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp only [hfr₁.length_eq, hlen] <;>
          omega)).mono
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right) ?_
  rintro μ₂ - ⟨hp₂, hY₂⟩
  exact ⟨hp₂.trans hp₁, hY₂⟩

omit [Has IndexOp O] [Inhabited ℝ] in
/-- A replay with any rotation routine stores the replayed word: if `Rot` at the plane $k$
stores `rotWord k c s` of the matrix for the coefficients $(c, s)$, the replay of a closed log
whose entries have their two planes in range stores the left fold of `rotWord` over the valid
entries, with the coefficients rounded from each entry.
Shared by the trees of `NLAlib.givensReplayRows`, `NLAlib.givensReplayColumns`. -/
theorem givensReplayWith_writes_word {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hQ : IsToNat id I) (hC : IsCmp id I) {Rot : Stmt O Q}
    {N lo j0 nc ns w : ℕ} {lg x : ℕ × ℕ}
    (rotWord : ℕ → ℂ → ℂ → Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ)
    (hRot : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {k : ℕ} {c s t : ℕ × ℕ} {Y : Matrix (Fin N) (Fin N) ℂ}
      {cv sv : ℂ}, k + 1 < N → HoldsMatrix x Y μ.store →
      μ.store.readBlock c.1 c.2 2 = some [cv.re, cv.im] →
      μ.store.readBlock s.1 s.2 2 = some [sv.re, sv.im] →
      Fp.Disj (Store.inBlock x.1 x.2 (2 * (N * N))) (Store.inBlock c.1 c.2 2) →
      Fp.Disj (Store.inBlock x.1 x.2 (2 * (N * N))) (Store.inBlock s.1 s.2 2) →
      t.1 ≠ x.1 → t.1 ≠ c.1 → t.1 ≠ s.1 → t.2 + 10 ≤ μ.store.len t.1 →
      Writes .total I τ Rot (Env.frame [N, k, j0, nc] [x, c, s, t, x])
        (Store.inBlock x.1 x.2 (2 * (N * N)) ⊔ Store.inBlock t.1 t.2 10)
        (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix x (rotWord k cv sv Y) μ'.store) μ)
    {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hrow : ∀ e ∈ slotEntries w L, lo + e.1 + 1 < N) {X : Matrix (Fin N) (Fin N) ℂ}
    {τ : Tape ℝ} {μ : Mem ℝ}
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hX : HoldsMatrix x X μ.store) (hl : μ.Live [lg, x])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock x.1 x.2 (2 * (N * N)))) :
    Writes .total I τ (givensReplayWith Rot)
      (Env.frame [N, lo, j0, nc, ns, w] [lg, x, x]) (Store.inBlock x.1 x.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix x ((slotEntries w L).foldl (fun Y e =>
        rotWord (lo + e.1) (roundedGivensCoeffs Mch e.2.1 e.2.2).1
          (roundedGivensCoeffs Mch e.2.1 e.2.2).2 Y) X) μ'.store) μ := by
  set F := fun (Y : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) => rotWord (lo + e.1)
    (roundedGivensCoeffs Mch e.2.1 e.2.2).1 (roundedGivensCoeffs Mch e.2.1 e.2.2).2 Y with hF
  have hxl : x.1 < μ.store.length := hl x (by simp)
  have hgl : lg.1 < μ.store.length := hl lg (by simp)
  unfold givensReplayWith
  change Writes .total I τ (Stmt.allocs [.const 4, .const 10] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [4, 10]) rfl
    (fun hBelow ⟨hp, hW⟩ => ⟨hp, hW.of_below hBelow hxl⟩) ?_
  intro s₁ hlen₁ hlens hBelow
  set Lc := μ.store.length with hLc
  simp only [List.length_cons, List.length_nil] at hlen₁
  set G := Store.inBlock x.1 x.2 (2 * (N * N)) ⊔ Store.inBlock Lc 0 4 ⊔
    Store.inBlock (Lc + 1) 0 10 with hG
  set St : List GivensEntry → Mem ℝ → Prop := fun es μ' => μ'.pos = μ.pos ∧
    μ'.store.length = Lc + 2 ∧ μ'.store.len Lc = 4 ∧ μ'.store.len (Lc + 1) = 10 ∧
    HoldsMatrix x (es.foldl F X) μ'.store ∧ HoldsSlottedLog lg ns w L P μ'.store with hSt
  have hGL : Fp.Disj G (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hd.symm, Fp.disj_inBlock_of_ne (by omega)⟩,
      Fp.disj_inBlock_of_ne (by omega)⟩
  have hstart : St [] ⟨s₁, μ.pos⟩ :=
    ⟨rfl, by omega, by simpa using hlens 0 (by simp), by simpa using hlens 1 (by simp),
      hX.of_below hBelow hxl, hlog.of_below hBelow hgl⟩
  have hGle : G ≤ Store.inBlock x.1 x.2 (2 * (N * N)) ⊔ Fp.above Lc := by
    rintro b z ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (h.1 ▸ le_rfl)
    · exact Or.inr (h.1 ▸ Nat.le_succ Lc)
  refine (writes_loop (N := ns) rfl (fun _ => G) (fun _ _ => le_rfl)
    (fun k μ' => St (slotEntries w (L.take k)) μ') (by simpa [slotEntries] using hstart)
    ?_).mono hGle ?_
  · intro k hk μ' _ ⟨hp, hlen', hL0, hL1, hW, hlog'⟩
    obtain ⟨v, hv, hm⟩ := hlog'.2.2.1 k (by omega)
    have htake : L.take (k + 1) = L.take k ++ [L[k]'(by omega)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
    refine writes_ite (a := [(lg.1, lg.2 + k * (1 + 5 * w))]) rfl
      (by simp [Operand.evalList, Operand.eval, Env.pushIdx, Env.frame, IExp.eval])
      (hC.test_isPos (x := (lg.1, lg.2 + k * (1 + 5 * w))) hv) ?_
    split at hm
    · next hn =>
      rw [if_neg (by simpa using hm)]
      have hW' : HoldsMatrix x ((slotEntries w (L.take (k + 1))).foldl F X) μ'.store := by
        rwa [htake, slotEntries_append, hn, slotEntries_none, List.append_nil]
      exact (Writes.skip (P := fun μ'' => St (slotEntries w (L.take (k + 1))) μ'')
        ⟨hp, hlen', hL0, hL1, hW', hlog'⟩).mono bot_le fun _ _ h => h
    · next es hn =>
      rw [if_pos (by simpa using hm.1)]
      refine (writes_loop (N := w) rfl (fun _ => G) (fun _ _ => le_rfl)
        (fun i μ'' => St (slotEntries w (L.take k) ++ (padEntries w es).take i) μ'')
        (by simpa using (⟨hp, hlen', hL0, hL1, hW, hlog'⟩ : St _ μ')) ?_).mono le_rfl ?_
      · intro i hi μ'' _ ⟨hp'', hlen'', hL0'', hL1'', hW'', hlog''⟩
        obtain ⟨hi', hwd⟩ := hlog''.readBlock_entry (j := k) (by omega) hn hi
        have he : lo + ((padEntries w es)[i]'hi').1 + 1 < N := hrow _ (by
          rw [slotEntries, List.mem_flatMap]
          exact ⟨some es, hn ▸ List.getElem_mem (by omega), by simp [List.getElem_mem]⟩)
        refine (replayEntryStmt_writes hS hQ hC hRot (N := N) (lo := lo) (j0 := j0) (nc := nc)
          (ns := ns) (w := w) (lg := lg) (x := x) (sl := k) (i := i) (Lc := Lc)
          (by simp [Env.pushIdx, Env.frame]) (by simp [Env.pushIdx, Env.frame, List.range_succ])
          he hwd hW''
          hlen'' hL0'' hL1'' hxl).mono le_rfl ?_
        rintro μ₃ hfr₃ ⟨hp₃, hW₃⟩
        refine ⟨hp₃.trans hp'', by rw [hfr₃.length_eq, hlen''], by rw [hfr₃.len_eq, hL0''],
          by rw [hfr₃.len_eq, hL1''], ?_, hfr₃.keep (readsOnly_holdsSlottedLog _ _ _ _ _) hGL
          hlog''⟩
        rw [List.take_add_one, List.getElem?_eq_getElem hi', ← List.append_assoc,
          List.foldl_append]
        exact hW₃
      · rintro μ₃ - ⟨hp₃, hlen₃, hL0₃, hL1₃, hW₃, hlog₃⟩
        refine ⟨hp₃, hlen₃, hL0₃, hL1₃, ?_, hlog₃⟩
        have hpl : (padEntries w es).length = w := by
          have := hm.2.1; simp [padEntries]; omega
        rw [htake, slotEntries_append, hn, slotEntries_some, List.foldl_append]
        simpa [List.take_of_length_le (le_of_eq hpl)] using hW₃
  · rintro μ' - ⟨hp, -, -, -, hW, -⟩
    exact ⟨hp, by simpa [List.take_of_length_le (le_of_eq hlen)] using hW⟩

omit [Inhabited ℝ] in
/-- The entries of a log inside a block, or the zero fill when the rows `lo, lo + 1` exist, have
their two planes in range. -/
theorem slotEntries_planes {N lo d w : ℕ} {L : List (Option (List GivensEntry))}
    (hN : lo + d ≤ N) (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d ∨ e = (0, 0, 0))
    (hlo : slotEntries w L = [] ∨ lo + 1 < N) :
    ∀ e ∈ slotEntries w L, lo + e.1 + 1 < N ∧ (e.1 + 1 < d ∨ e = (0, 0, 0)) := by
  intro e he
  refine ⟨?_, hpl e he⟩
  rcases hpl e he with h | rfl
  · omega
  · rcases hlo with h | h
    · rw [h] at he; simp at he
    · simpa using h

omit [Has IndexOp O] [Inhabited ℝ] in
/-- **The column replay on every tape**: the stored matrix moves from $\mathbf{X}$ to within
$((1 + 24\boldsymbol{u})^{m} - 1)\|\mathbf{X}\|_2$ of $\mathbf{X}\widetilde{\mathbf{V}}$, where
$\widetilde{\mathbf{V}}$ acts by the log's unitary on the range $[lo, lo + d)$ and $m$ is the
capacity $ns \cdot w$ (each replayed rotation, padding included, costs at most
$24\boldsymbol{u}$; [Higham2002, Lemma 19.8]). Needs only exact naturals up to the order. -/
theorem givensReplayColumns_specNorm_sub_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hQ : IsToNat id I) (hC : IsCmp id I) {N lo d ns w : ℕ} (hN : lo + d ≤ N)
    {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d ∨ e = (0, 0, 0))
    (hlo : slotEntries w L = [] ∨ lo + 1 < N) {lg x : ℕ × ℕ}
    {X : Matrix (Fin N) (Fin N) ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hX : HoldsMatrix x X μ.store) (hl : μ.Live [lg, x])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock x.1 x.2 (2 * (N * N)))) :
    Writes .total I τ (givensReplayColumns (O := O) (Q := Q))
      (Env.frame [N, lo, 0, N, ns, w] [lg, x, x]) (Store.inBlock x.1 x.2 (2 * (N * N)))
      (fun μ' => ∃ X' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix x X' μ'.store ∧
        specNorm (X' - X * embedBlock lo (givensLog d (slotEntries w L))) ≤
          ((1 + 24 * u) ^ (ns * w) - 1) * specNorm X) μ := by
  have hes := slotEntries_planes hN hpl hlo
  refine (givensReplayWith_writes_word hS hQ hC (fun k cv sv Y => if h : k + 1 < N then
      machineColRotationOn Mch ⟨k, by omega⟩ ⟨k + 1, h⟩ cv sv 0 N Y else Y)
    (fun hk hY hc hs hca hsa hta htc hts ht => by
      simpa only [dif_pos hk] using rotateColumnsOn_writes_word hS hk (by omega) hY hc hs hca
        hsa hta htc hts ht) (fun e he => (hes e he).1) hlog hlen hX hl hd).mono le_rfl ?_
  rintro μ' - ⟨-, hW⟩
  refine ⟨_, hW, ?_⟩
  have e : (fun (Y : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) =>
      (fun k cv sv Y => if h : k + 1 < N then
        machineColRotationOn Mch ⟨k, by omega⟩ ⟨k + 1, h⟩ cv sv 0 N Y else Y)
        (lo + e.1) (roundedGivensCoeffs Mch e.2.1 e.2.2).1 (roundedGivensCoeffs Mch e.2.1 e.2.2).2
        Y) = replayColumnStep Mch lo 0 N := rfl
  rw [e]
  refine (specNorm_foldl_replayColumnStep_sub_le hM hu0 hu hN _ hes X).trans
    (mul_le_mul_of_nonneg_right ?_ (specNorm_nonneg X))
  gcongr
  · linarith
  · exact hlen ▸ hlog.length_slotEntries_le

omit [Has IndexOp O] [Inhabited ℝ] in
/-- **The row replay on a column range on every tape**: the columns outside
$[j_0, j_0 + n_c)$ are kept and, on the range, the stored matrix is within
$((1 + 24\boldsymbol{u})^{ns\,w} - 1)\|\mathbf{X}\|_2$ of $\widetilde{\mathbf{V}}^{\mathsf H}
\mathbf{X}$. -/
theorem givensReplayRows_specNorm_sub_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hQ : IsToNat id I) (hC : IsCmp id I) {N lo d j0 nc ns w : ℕ} (hN : lo + d ≤ N)
    (hj : j0 + nc ≤ N) {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d ∨ e = (0, 0, 0))
    (hlo : slotEntries w L = [] ∨ lo + 1 < N) {lg x : ℕ × ℕ}
    {X : Matrix (Fin N) (Fin N) ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hX : HoldsMatrix x X μ.store) (hl : μ.Live [lg, x])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock x.1 x.2 (2 * (N * N)))) :
    Writes .total I τ (givensReplayRows (O := O) (Q := Q))
      (Env.frame [N, lo, j0, nc, ns, w] [lg, x, x]) (Store.inBlock x.1 x.2 (2 * (N * N)))
      (fun μ' => ∃ X' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix x X' μ'.store ∧
        (∀ i j : Fin N, ¬(j0 ≤ (j : ℕ) ∧ (j : ℕ) < j0 + nc) → X' i j = X i j) ∧
        specNorm (Matrix.of fun i j : Fin N => if j0 ≤ (j : ℕ) ∧ (j : ℕ) < j0 + nc then
          (X' - (embedBlock lo (givensLog d (slotEntries w L)))ᴴ * X :
            Matrix (Fin N) (Fin N) ℂ) i j else 0) ≤
          ((1 + 24 * u) ^ (ns * w) - 1) * specNorm X) μ := by
  have hes := slotEntries_planes hN hpl hlo
  refine (givensReplayWith_writes_word hS hQ hC (fun k cv sv Y => if h : k + 1 < N then
      machineRowRotationOn Mch ⟨k, by omega⟩ ⟨k + 1, h⟩ cv sv j0 nc Y else Y)
    (fun hk hY hc hs hca hsa hta htc hts ht => by
      simpa only [dif_pos hk] using rotateRowsOn_writes_word hS hk hj hY hc hs hca
        hsa hta htc hts ht) (fun e he => (hes e he).1) hlog hlen hX hl hd).mono le_rfl ?_
  rintro μ' - ⟨-, hW⟩
  have e : (fun (Y : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) =>
      (fun k cv sv Y => if h : k + 1 < N then
        machineRowRotationOn Mch ⟨k, by omega⟩ ⟨k + 1, h⟩ cv sv j0 nc Y else Y)
        (lo + e.1) (roundedGivensCoeffs Mch e.2.1 e.2.2).1 (roundedGivensCoeffs Mch e.2.1 e.2.2).2
        Y) = replayRowStep Mch lo j0 nc := rfl
  rw [e] at hW
  refine ⟨_, hW, fun i t ht => foldl_replayRowStep_apply_of_not_mem _ _ _ _ ht, ?_⟩
  set V := embedBlock (N := N) lo (givensLog d (slotEntries w L))
  have hD := isStarProjection_colMask N j0 nc
  have hm : (Matrix.of fun i j : Fin N => if j0 ≤ (j : ℕ) ∧ (j : ℕ) < j0 + nc then
      ((slotEntries w L).foldl (replayRowStep Mch lo j0 nc) X - Vᴴ * X) i j else 0) =
      (slotEntries w L).foldl (replayRowStep Mch lo 0 N) (X * colMask N j0 nc) -
        Vᴴ * (X * colMask N j0 nc) := by
    rw [← foldl_replayRowStep_mul_colMask hM, ← Matrix.mul_assoc, ← Matrix.sub_mul]
    ext i j
    simp [colMask, Matrix.mul_diagonal]
  rw [hm]
  refine (specNorm_foldl_replayRowStep_sub_le hM hu0 hu hN _ hes _).trans ?_
  have hpow : (1 + 24 * u) ^ (slotEntries w L).length ≤ (1 + 24 * u) ^ (ns * w) :=
    pow_le_pow_right₀ (by linarith) (hlen ▸ hlog.length_slotEntries_le)
  have h1 : (1 : ℝ) ≤ (1 + 24 * u) ^ (slotEntries w L).length := one_le_pow₀ (by linarith)
  have hXD := hD.specNorm_mul_right_le X
  nlinarith [specNorm_nonneg (X * colMask N j0 nc)]

omit [Inhabited ℝ] in
/-- **The accumulated product from the identity**: with $24R\boldsymbol{u} \le 1/8$,
$(1 + 24\boldsymbol{u})^R - 1 \le 27R\boldsymbol{u}$. -/
theorem one_add_mul_pow_sub_one_le {u : ℝ} {R : ℕ} (hu : 0 ≤ u) (hR : 24 * R * u ≤ 1 / 8) :
    (1 + 24 * u) ^ R - 1 ≤ 27 * R * u := by
  have h := one_add_pow_sub_one_le (x := 24 * u) (n := R) (by positivity) (by nlinarith)
  have hR : 0 ≤ (R : ℝ) * (24 * u) := by positivity
  nlinarith

end ReplaySpecs


/-! ### The words of a replay on a range -/

section ReplayRange


variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has IndexOp O] in
/-- **The words of a row replay**: on a scalar machine with exact `toNat` and comparisons and
every tape, the replay of a closed log whose entries have their two rows `lo + r, lo + r + 1`
in range, on the columns $j_0, \dots, j_0 + n_c - 1$ of the matrix at `x`, writes only the matrix
and stores the left fold of `NLAlib.replayRowStep` over the valid entries.
Shared by the trees of `NLAlib.ShiftedQR.roundedAbort`, `NLAlib.ShiftedQR.roundedDecoupleUpdate`. -/
theorem givensReplayRows_writes_word {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hQ : IsToNat id I) (hC : IsCmp id I) {N lo j0 nc ns w : ℕ}
    (hj : j0 + nc ≤ N) {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hrow : ∀ e ∈ slotEntries w L, lo + e.1 + 1 < N) {lg x : ℕ × ℕ}
    {X : Matrix (Fin N) (Fin N) ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hX : HoldsMatrix x X μ.store) (hl : μ.Live [lg, x])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock x.1 x.2 (2 * (N * N)))) :
    Writes .total I τ (givensReplayRows (O := O) (Q := Q))
      (Env.frame [N, lo, j0, nc, ns, w] [lg, x, x]) (Store.inBlock x.1 x.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos ∧
        HoldsMatrix x ((slotEntries w L).foldl (replayRowStep Mch lo j0 nc) X) μ'.store) μ :=
  givensReplayWith_writes_word hS hQ hC (fun k cv sv Y => if h : k + 1 < N then
      machineRowRotationOn Mch ⟨k, by omega⟩ ⟨k + 1, h⟩ cv sv j0 nc Y else Y)
    (fun hk hY hc hs hca hsa hta htc hts ht => by
      simpa only [dif_pos hk] using rotateRowsOn_writes_word hS hk hj hY hc hs hca
        hsa hta htc hts ht) hrow hlog hlen hX hl hd

omit [Has IndexOp O] in
/-- **The words of a column replay**: as `NLAlib.givensReplayRows_writes_word`, on the rows
$i_0, \dots, i_0 + n_r - 1$, the replay stores the left fold of `NLAlib.replayColumnStep`.
Shared by the trees of `NLAlib.hessenbergReduceQ`, `NLAlib.ShiftedQR.roundedAbort`,
`NLAlib.ShiftedQR.roundedDecoupleUpdate` and 1 more. -/
theorem givensReplayColumns_writes_word {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hQ : IsToNat id I) (hC : IsCmp id I) {N lo i0 nr ns w : ℕ}
    (hi : i0 + nr ≤ N) {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hrow : ∀ e ∈ slotEntries w L, lo + e.1 + 1 < N) {lg x : ℕ × ℕ}
    {X : Matrix (Fin N) (Fin N) ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hX : HoldsMatrix x X μ.store) (hl : μ.Live [lg, x])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock x.1 x.2 (2 * (N * N)))) :
    Writes .total I τ (givensReplayColumns (O := O) (Q := Q))
      (Env.frame [N, lo, i0, nr, ns, w] [lg, x, x]) (Store.inBlock x.1 x.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos ∧
        HoldsMatrix x ((slotEntries w L).foldl (replayColumnStep Mch lo i0 nr) X) μ'.store) μ :=
  givensReplayWith_writes_word hS hQ hC (fun k cv sv Y => if h : k + 1 < N then
      machineColRotationOn Mch ⟨k, by omega⟩ ⟨k + 1, h⟩ cv sv i0 nr Y else Y)
    (fun hk hY hc hs hca hsa hta htc hts ht => by
      simpa only [dif_pos hk] using rotateColumnsOn_writes_word hS hk hi hY hc hs hca
        hsa hta htc hts ht) hrow hlog hlen hX hl hd

omit [Has IndexOp O] in
/-- The column replay on every tape, its bound under a condition: as
`NLAlib.givensReplayColumns_specNorm_sub_le`, but on any scalar machine: the run is total, writes
only the matrix and leaves a matrix stored, and if `C` (which gives the standard model at
$\boldsymbol{u} \le 1/100$) the stored matrix is within
$((1 + 24\boldsymbol{u})^{n_s w} - 1)\|\mathbf{X}\|_2$ of $\mathbf{X}\widetilde{\mathbf{V}}$. -/
theorem givensReplayColumns_specNorm_sub_le_if {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) {C : Prop} (hC' : C → StdModel u id Mch ∧ u ≤ 1 / 100)
    (hQ : IsToNat id I) (hC : IsCmp id I) {N lo d ns w : ℕ} (hN : lo + d ≤ N)
    {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d ∨ e = (0, 0, 0))
    (hlo : slotEntries w L = [] ∨ lo + 1 < N) {lg x : ℕ × ℕ}
    {X : Matrix (Fin N) (Fin N) ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hX : HoldsMatrix x X μ.store) (hl : μ.Live [lg, x])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock x.1 x.2 (2 * (N * N)))) :
    Writes .total I τ (givensReplayColumns (O := O) (Q := Q))
      (Env.frame [N, lo, 0, N, ns, w] [lg, x, x]) (Store.inBlock x.1 x.2 (2 * (N * N)))
      (fun μ' => ∃ X' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix x X' μ'.store ∧
        (C → specNorm (X' - X * embedBlock lo (givensLog d (slotEntries w L))) ≤
          ((1 + 24 * u) ^ (ns * w) - 1) * specNorm X)) μ := by
  by_cases hc : C
  · have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using (hC' hc).1.lit 1)
    exact (givensReplayColumns_specNorm_sub_le hS (hC' hc).1 hu0 (hC' hc).2 hQ hC hN hpl hlo hlog
      hlen hX hl hd).mono le_rfl fun _ _ ⟨X', hX', hb⟩ => ⟨X', hX', fun _ => hb⟩
  · exact (givensReplayColumns_writes_word hS hQ hC (lo := lo) (i0 := 0) (nr := N) (by omega)
      (fun e he => (slotEntries_planes hN hpl hlo e he).1) hlog hlen hX hl hd).mono le_rfl
      fun _ _ ⟨_, hX'⟩ => ⟨_, hX', fun h => absurd h hc⟩

end ReplayRange

end NLAlib
