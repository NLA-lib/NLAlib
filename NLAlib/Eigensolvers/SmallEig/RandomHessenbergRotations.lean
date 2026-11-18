/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedModuli
public import NLAlib.Eigensolvers.HessenbergReduction
public import NLAlib.Eigensolvers.SmallEig.Draws
public import NLAlib.Matrix.FinitePrecision.GivensLogSlots
public import NLAlib.Matrix.Perturbation.EigenvalueBackward
public import NLAlib.Matrix.QRIteration.EigenvectorWeights
public import NLAlib.Ops.Logic.Probabilistic
public import NLAlib.RandomMatrix.Gaussian.Complex.LeastSingularValue
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlib.RandomMatrix.Gaussian.Tape

/-!
# The rotations of the random Hessenberg form

The first half of `RHess` ([BanksGarzaVargasSrivastava2025, §5]): the $N - 1$ rounded Givens
rotations that take $\mathbf{e}_N$ to the drawn direction $\mathbf{g}$, on both sides of the
matrix. On a machine with the standard model they are a unitary similarity up to
$((1 + 50\boldsymbol{u})^{N-1} - 1)\|\mathbf{A}\|_2$, and the last column of the unitary factor is
a unit multiple of a vector within a small distance of $\mathbf{g}/\|\mathbf{g}\|$: the phase of the
paper's reflector (its erratum P3) is explicit here.

## Main definitions

* `NLAlib.SmallEig.pairVector`, `NLAlib.SmallEig.rotateToStepWord`,
  `NLAlib.SmallEig.rhessWord`: the words the program stores.
* `NLAlib.SmallEig.vecRot`, `NLAlib.SmallEig.RotInv`: the rounded rotation of a vector and the
  invariant of the rotations.

## Main results

* `NLAlib.SmallEig.rotInv_fold`: the invariant after all rotations.
* `NLAlib.SmallEig.rhess_matrix_bound`, `NLAlib.SmallEig.rhess_phase`: the backward error of
  `RHess` and the phase of its last column.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

/-- `omega` after reducing the projections of literal pairs. -/
local macro "pomega" : tactic => `(tactic| ((try dsimp only) <;> omega))

/-- The complex vector of $2N$ real words, $(x_{2i} + i x_{2i+1})_{i < N}$. -/
def pairVector (x : ℕ → ℝ) (N : ℕ) : Fin N → ℂ := fun i => ⟨x (2 * i), x (2 * i + 1)⟩

/-- One rotation of `NLAlib.SmallEig.rhess` on a machine: the rounded coefficients of
$(\bar g_{j+1}, -\bar g_j)$, the rounded rotation of the entries $j, j + 1$ of $\mathbf{g}$, and of
the rows, then the columns, $j, j + 1$ of $\mathbf{A}$; the identity when $j + 1 \ge N$. -/
noncomputable def rotateToStepWord (M : Machine ℝ) {N : ℕ} (j : ℕ)
    (Ag : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ)) : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) :=
  if h : j + 1 < N then
    let i : Fin N := ⟨j, by omega⟩
    let k : Fin N := ⟨j + 1, h⟩
    let cs := roundedGivensCoeffs M ⟨(Ag.2 k).re, M.neg (Ag.2 k).im⟩
      ⟨M.neg (Ag.2 i).re, (Ag.2 i).im⟩
    (machineColRotation M i k cs.1 cs.2 (machineRowRotation M i k cs.1 cs.2 Ag.1),
      fun r => if r = i then linearComplex M cs.1 cs.2 (Ag.2 i) (Ag.2 k)
        else if r = k then
          linearComplex M ⟨M.neg cs.2.re, cs.2.im⟩ ⟨cs.1.re, M.neg cs.1.im⟩ (Ag.2 i) (Ag.2 k)
        else Ag.2 r)
  else Ag

/-- The matrix stored by `NLAlib.SmallEig.rhess` on the machine `M` from the matrix $\mathbf{A}$
and the $2N$ drawn words $x$: the $N - 1$ steps `NLAlib.SmallEig.rotateToStepWord` from
$(\mathbf{A}, \mathbf{g})$, then `NLAlib.hessenbergReduceLastWord`. -/
noncomputable def rhessWord (M : Machine ℝ) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (x : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  hessenbergReduceLastWord M
    ((List.range (N - 1)).foldl (fun Ag j => rotateToStepWord M j Ag) (A, pairVector x N)).1

/-- The log entry of one rotation of `NLAlib.SmallEig.rhess` on a machine: the plane $j$ and the
inputs $(\bar g_{j+1}, -\bar g_j)$ of the coefficients, as the machine forms them; the padding
entry $(0, 0, 0)$ when $j + 1 \ge N$. -/
noncomputable def rotateToStepEntry (M : Machine ℝ) {N : ℕ} (j : ℕ)
    (Ag : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ)) : GivensEntry :=
  if h : j + 1 < N then
    (j, ⟨(Ag.2 ⟨j + 1, h⟩).re, M.neg (Ag.2 ⟨j + 1, h⟩).im⟩,
      ⟨M.neg (Ag.2 ⟨j, by omega⟩).re, (Ag.2 ⟨j, by omega⟩).im⟩)
  else (0, 0, 0)

/-- The log entries of the first $k$ rotations of `NLAlib.SmallEig.rhess` from
$(\mathbf{A}, \mathbf{g})$. -/
noncomputable def rotateToEntries (M : Machine ℝ) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (g : Fin N → ℂ) (k : ℕ) : List GivensEntry :=
  (List.range k).map fun j =>
    rotateToStepEntry M j ((List.range j).foldl (fun Ag j => rotateToStepWord M j Ag) (A, g))

/-- The slots that `NLAlib.SmallEig.rhess` records on the machine `M` from $\mathbf{A}$ and the
drawn words $x$: the $N - 1$ rotations of the vector in one slot, then the slots of the reduction
(`NLAlib.hessenbergReduceLastSlots`). -/
noncomputable def rhessSlots (M : Machine ℝ) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (x : ℕ → ℝ) : List (List GivensEntry) :=
  rotateToEntries M A (pairVector x N) (N - 1) :: hessenbergReduceLastSlots M
    ((List.range (N - 1)).foldl (fun Ag j => rotateToStepWord M j Ag) (A, pairVector x N)).1

/-- One more rotation appends its entry. -/
theorem rotateToEntries_succ (M : Machine ℝ) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (g : Fin N → ℂ) (k : ℕ) :
    rotateToEntries M A g (k + 1) = rotateToEntries M A g k ++
      [rotateToStepEntry M k ((List.range k).foldl (fun Ag j => rotateToStepWord M j Ag) (A, g))] :=
  by simp [rotateToEntries, List.range_succ]

/-- The slots of `NLAlib.SmallEig.rhess`: $N - 1$ of them for $N \ge 2$, every entry with its
plane below $N - 1$ once padded. -/
theorem rhessSlots_spec (M : Machine ℝ) {N : ℕ} (hN : 2 ≤ N) (A : Matrix (Fin N) (Fin N) ℂ)
    (x : ℕ → ℝ) (w : ℕ) :
    (rhessSlots M A x).length = N - 1 ∧
      ∀ e ∈ slotEntries w ((rhessSlots M A x).map some), e.1 + 1 < N := by
  refine ⟨by simp [rhessSlots, length_hessenbergReduceLastSlots]; omega, fun e he => ?_⟩
  simp only [slotEntries, List.mem_flatMap, List.mem_map] at he
  obtain ⟨_, ⟨es, hes, rfl⟩, he⟩ := he
  simp only [Option.map_some, Option.getD_some] at he
  refine padEntries_planes (by omega) (fun e he => ?_) e he
  rcases List.mem_cons.mp hes with rfl | hes
  · simp only [rotateToEntries, List.mem_map, List.mem_range] at he
    obtain ⟨j, hj, rfl⟩ := he
    unfold rotateToStepEntry
    split_ifs with h
    · exact h
    · change 0 + 1 < N; omega
  · rcases hessenbergReduceLastSlots_plane M _ es hes e he with h | rfl
    exacts [h, by change 0 + 1 < N; omega]

section BackwardError

variable {M : Machine ℝ} {u : ℝ}

/-- One rounded round, rows then columns, within $50\boldsymbol{u}\|\mathbf{Z}\|_2$ of the exact
conjugation, for $0 \le \boldsymbol{u} \le 1/288$. -/
private theorem specNorm_rowCol_sub_le (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 288)
    {N : ℕ} {i j : Fin N} (hij : i ≠ j) (p q : ℂ) (Z : Matrix (Fin N) (Fin N) ℂ) :
    specNorm (machineColRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2
        (machineRowRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2 Z) -
      givens i j (givensCoeffs p q).1 (givensCoeffs p q).2 * Z *
        (givens i j (givensCoeffs p q).1 (givensCoeffs p q).2)ᴴ) ≤ 50 * u * specNorm Z := by
  have hu100 : u ≤ 1 / 100 := by linarith
  set G := givens i j (givensCoeffs p q).1 (givensCoeffs p q).2
  have hG : HasOrthonormalCols G :=
    hasOrthonormalCols_givens hij (norm_givensCoeffs_fst_sq_add p q)
  set Z₁ := machineRowRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2 Z
  set Z₂ := machineColRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2 Z₁
  have h1 := (isRoundedRowRotation_machineRowRotation hM hu hu100 hij p q Z).specNorm_sub_le
    (by positivity)
  have h2 := (isRoundedColRotation_machineColRotation hM hu hu100 hij p q Z₁).specNorm_sub_le
    (by positivity)
  have hZ₁ : specNorm Z₁ ≤ (1 + 24 * u) * specNorm Z := by
    have e : Z₁ = G * Z + (Z₁ - G * Z) := by abel
    have := specNorm_add_le (G * Z) (Z₁ - G * Z)
    rw [← e, hG.specNorm_mul_left] at this
    linarith
  have e : Z₂ - G * Z * Gᴴ = (Z₂ - Z₁ * Gᴴ) + (Z₁ - G * Z) * Gᴴ := by
    rw [Matrix.sub_mul]
    abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [hG.specNorm_mul_conjTranspose_right]
  have hZ : 0 ≤ specNorm Z := specNorm_nonneg Z
  nlinarith [mul_le_mul_of_nonneg_left hZ₁ (by positivity : (0 : ℝ) ≤ 2 * (12 * u)),
    mul_nonneg (mul_nonneg hu hZ) (by linarith : (0 : ℝ) ≤ 2 - 576 * u)]

/-- The rounded rotation of the entries $i, k$ of a vector, as `NLAlib.SmallEig.rhess` computes
it. -/
noncomputable def vecRot (M : Machine ℝ) {N : ℕ} (i k : Fin N) (cs : ℂ × ℂ)
    (v : Fin N → ℂ) : Fin N → ℂ :=
  fun r => if r = i then linearComplex M cs.1 cs.2 (v i) (v k)
    else if r = k then linearComplex M ⟨M.neg cs.2.re, cs.2.im⟩ ⟨cs.1.re, M.neg cs.1.im⟩ (v i) (v k)
    else v r

/-- The rounded rotation of two entries of a vector is within $12\boldsymbol{u}$ of the exact
one, on those entries, and keeps the others. -/
private theorem vecRot_sub_le (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) {N : ℕ}
    {i k : Fin N} (hik : i ≠ k) (p q : ℂ) (v : Fin N → ℂ) :
    √(‖vecRot M i k (roundedGivensCoeffs M p q) v i -
        (givens i k (givensCoeffs p q).1 (givensCoeffs p q).2 *ᵥ v) i‖ ^ 2 +
      ‖vecRot M i k (roundedGivensCoeffs M p q) v k -
        (givens i k (givensCoeffs p q).1 (givensCoeffs p q).2 *ᵥ v) k‖ ^ 2) ≤
      12 * u * √(‖v i‖ ^ 2 + ‖v k‖ ^ 2) := by
  let X : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun r _ => v r
  have h := (isRoundedRowRotation_machineRowRotation hM hu hu' hik p q X).2 i
  have e1 : ∀ r, (givens i k (givensCoeffs p q).1 (givensCoeffs p q).2 * X) r i =
      (givens i k (givensCoeffs p q).1 (givensCoeffs p q).2 *ᵥ v) r := fun r => by
    simp [X, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [e1, e1] at h
  simpa [X, machineRowRotation, vecRot, Ne.symm hik] using h

/-- The Euclidean norm of a vector supported on two entries. -/
private theorem norm_toLp_eq_of_support {N : ℕ} {i k : Fin N} (hik : i ≠ k) {w : Fin N → ℂ}
    (hw : ∀ r, r ≠ i → r ≠ k → w r = 0) :
    ‖WithLp.toLp 2 w‖ = √(‖w i‖ ^ 2 + ‖w k‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_eq_add i k hik fun r hr => by simp [hw r hr.1 hr.2]]

/-- Two entries have joint norm at most the Euclidean norm. -/
private theorem sqrt_norm_sq_add_le_norm_toLp {N : ℕ} {i k : Fin N} (hik : i ≠ k)
    (w : Fin N → ℂ) : √(‖w i‖ ^ 2 + ‖w k‖ ^ 2) ≤ ‖WithLp.toLp 2 w‖ := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i, k})
    (f := fun r => ‖w r‖ ^ 2) fun _ _ _ => sq_nonneg _
  simpa [Finset.sum_pair hik] using h

/-- The invariant of the rotations of `RHess` after $k$ steps from $(\mathbf{A}, \mathbf{g})$
with the unitary $\mathbf{U}$: $\mathbf{B}$ within
$((1 + 50\boldsymbol{u})^k - 1)\|\mathbf{A}\|_2$ of $\mathbf{U}\mathbf{A}\mathbf{U}^{\mathsf{H}}$, $\mathbf{v}$ within
$((1 + 12\boldsymbol{u})^k - 1)\|\mathbf{g}\|$ of $\mathbf{U}\mathbf{g}$, and the first $k$ entries
of $\mathbf{v}$ at most $12\boldsymbol{u}(1 + 12\boldsymbol{u})^k\|\mathbf{g}\|$. -/
def RotInv (u : ℝ) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (g : Fin N → ℂ) (k : ℕ)
    (Bv : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ)) (U : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  HasOrthonormalCols U ∧
    specNorm (Bv.1 - U * A * Uᴴ) ≤ ((1 + 50 * u) ^ k - 1) * specNorm A ∧
    ‖WithLp.toLp 2 (Bv.2 - U *ᵥ g)‖ ≤ ((1 + 12 * u) ^ k - 1) * ‖WithLp.toLp 2 g‖ ∧
    ∀ r : Fin N, (r : ℕ) < k → ‖Bv.2 r‖ ≤ 12 * u * (1 + 12 * u) ^ k * ‖WithLp.toLp 2 g‖

/-- The step of `NLAlib.SmallEig.rotateToStepWord` on a machine with the standard model. -/
private theorem rotateToStepWord_eq (hM : StdModel u id M) {N j : ℕ} (hj : j + 1 < N)
    (B : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    rotateToStepWord M j (B, v) =
      (machineColRotation M ⟨j, by omega⟩ ⟨j + 1, hj⟩
        (roundedGivensCoeffs M (star (v ⟨j + 1, hj⟩)) (-star (v ⟨j, by omega⟩))).1
        (roundedGivensCoeffs M (star (v ⟨j + 1, hj⟩)) (-star (v ⟨j, by omega⟩))).2
        (machineRowRotation M ⟨j, by omega⟩ ⟨j + 1, hj⟩
          (roundedGivensCoeffs M (star (v ⟨j + 1, hj⟩)) (-star (v ⟨j, by omega⟩))).1
          (roundedGivensCoeffs M (star (v ⟨j + 1, hj⟩)) (-star (v ⟨j, by omega⟩))).2 B),
        vecRot M ⟨j, by omega⟩ ⟨j + 1, hj⟩
          (roundedGivensCoeffs M (star (v ⟨j + 1, hj⟩)) (-star (v ⟨j, by omega⟩))) v) := by
  have hn (x : ℝ) : M.neg x = -x := hM.neg x
  have e1 : (⟨(v ⟨j + 1, hj⟩).re, M.neg (v ⟨j + 1, hj⟩).im⟩ : ℂ) = star (v ⟨j + 1, hj⟩) := by
    apply Complex.ext <;> simp [hn]
  have e2 : (⟨M.neg (v ⟨j, by omega⟩).re, (v ⟨j, by omega⟩).im⟩ : ℂ) =
      -star (v ⟨j, by omega⟩) := by
    apply Complex.ext <;> simp [hn]
  simp only [rotateToStepWord, dif_pos hj, e1, e2]
  rfl

/-- The matrix half of a rotation step of `RHess`: a step within $50\boldsymbol{u}\|\mathbf{B}\|_2$
of $\mathbf{G}\mathbf{B}\mathbf{G}^{\mathsf{H}}$ adds one factor $1 + 50\boldsymbol{u}$. -/
private theorem rotInv_matrix_step {N j : ℕ} {A B B' U G : Matrix (Fin N) (Fin N) ℂ}
    (hU : HasOrthonormalCols U) (hG : HasOrthonormalCols G)
    (hB : specNorm (B - U * A * Uᴴ) ≤ ((1 + 50 * u) ^ j - 1) * specNorm A) (hu : 0 ≤ u)
    (hrc : specNorm (B' - G * B * Gᴴ) ≤ 50 * u * specNorm B) :
    specNorm (B' - G * U * A * (G * U)ᴴ) ≤ ((1 + 50 * u) ^ (j + 1) - 1) * specNorm A := by
  have hAU : specNorm (U * A * Uᴴ) = specNorm A := by
    have := hU.conjTranspose.specNorm_conjTranspose_mul_mul A
    rwa [Matrix.conjTranspose_conjTranspose] at this
  have hBn : specNorm B ≤ (1 + 50 * u) ^ j * specNorm A := by
    have e : B = (B - U * A * Uᴴ) + U * A * Uᴴ := by abel
    have := specNorm_add_le (B - U * A * Uᴴ) (U * A * Uᴴ)
    rw [← e, hAU] at this
    linarith
  have e : B' - G * U * A * (G * U)ᴴ = (B' - G * B * Gᴴ) + G * (B - U * A * Uᴴ) * Gᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [hG.specNorm_mul_conjTranspose_right, hG.specNorm_mul_left, pow_succ]
  nlinarith [mul_le_mul_of_nonneg_left hBn (by positivity : (0 : ℝ) ≤ 50 * u)]

/-- The exact rotation of the entry of a step of `RHess` is the rotation the step rounds. -/
private theorem givensAt_rotateToStepEntry (hM : StdModel u id M) {N j : ℕ} (hj : j + 1 < N)
    (B : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    givensAt N (rotateToStepEntry M j (B, v)) =
      givens (⟨j, by omega⟩ : Fin N) ⟨j + 1, hj⟩
        (givensCoeffs (star (v ⟨j + 1, hj⟩)) (-star (v ⟨j, by omega⟩))).1
        (givensCoeffs (star (v ⟨j + 1, hj⟩)) (-star (v ⟨j, by omega⟩))).2 := by
  have hn (x : ℝ) : M.neg x = -x := hM.neg x
  have e1 : (⟨(v ⟨j + 1, hj⟩).re, M.neg (v ⟨j + 1, hj⟩).im⟩ : ℂ) = star (v ⟨j + 1, hj⟩) := by
    apply Complex.ext <;> simp [hn]
  have e2 : (⟨M.neg (v ⟨j, by omega⟩).re, (v ⟨j, by omega⟩).im⟩ : ℂ) =
      -star (v ⟨j, by omega⟩) := by
    apply Complex.ext <;> simp [hn]
  simp only [rotateToStepEntry, dif_pos hj, givensAt, e1, e2]

/-- One rotation of `RHess` keeps the invariant, with one more step and the exact rotation of its
entry. -/
private theorem rotInv_step (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 288) {N j : ℕ}
    (hj : j + 1 < N) {A : Matrix (Fin N) (Fin N) ℂ} {g : Fin N → ℂ}
    {X : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ)} {U : Matrix (Fin N) (Fin N) ℂ}
    (h : RotInv u A g j X U) :
    RotInv u A g (j + 1) (rotateToStepWord M j X) (givensAt N (rotateToStepEntry M j X) * U) := by
  obtain ⟨B, v⟩ := X
  obtain ⟨hU, hB, hv, hz⟩ := h
  dsimp only at hB hv hz
  rw [givensAt_rotateToStepEntry hM hj, rotateToStepWord_eq hM hj]
  set i : Fin N := ⟨j, by omega⟩
  set k : Fin N := ⟨j + 1, hj⟩
  have hik : i ≠ k := Fin.ne_of_val_ne (by simp [i, k])
  set p := star (v k)
  set q := -star (v i)
  set G := givens i k (givensCoeffs p q).1 (givensCoeffs p q).2
  have hG : HasOrthonormalCols G := hasOrthonormalCols_givens hik (norm_givensCoeffs_fst_sq_add _ _)
  have hgn : ‖WithLp.toLp 2 (U *ᵥ g)‖ = ‖WithLp.toLp 2 g‖ := hU.norm_toLp_mulVec g
  have hvn : ‖WithLp.toLp 2 v‖ ≤ (1 + 12 * u) ^ j * ‖WithLp.toLp 2 g‖ := by
    have e : v = (v - U *ᵥ g) + U *ᵥ g := by abel
    have := norm_add_le (WithLp.toLp 2 (v - U *ᵥ g)) (WithLp.toLp 2 (U *ᵥ g))
    rw [← WithLp.toLp_add, ← e, hgn] at this
    linarith
  have hpair := vecRot_sub_le hM hu (by linarith) hik p q v
  set v' := vecRot M i k (roundedGivensCoeffs M p q) v
  have hsupp : ∀ r, r ≠ i → r ≠ k → (v' - G *ᵥ v) r = 0 := fun r h1 h2 => by
    simp [v', vecRot, h1, h2, G, givens_mulVec_apply_of_ne h1 h2]
  have hvv : ‖WithLp.toLp 2 (v' - G *ᵥ v)‖ ≤ 12 * u * ((1 + 12 * u) ^ j * ‖WithLp.toLp 2 g‖) := by
    rw [norm_toLp_eq_of_support hik hsupp]
    have hp' : √(‖(v' - G *ᵥ v) i‖ ^ 2 + ‖(v' - G *ᵥ v) k‖ ^ 2) ≤
        12 * u * √(‖v i‖ ^ 2 + ‖v k‖ ^ 2) := by simpa using hpair
    exact hp'.trans (mul_le_mul_of_nonneg_left
      ((sqrt_norm_sq_add_le_norm_toLp hik v).trans hvn) (by positivity))
  refine ⟨hasOrthonormalCols_iff.mpr ((hG.conjTranspose_mul_mul U U).trans
    (hasOrthonormalCols_iff.mp hU)), ?_, ?_, fun r hr => ?_⟩
  · dsimp only
    exact rotInv_matrix_step hU hG hB hu (specNorm_rowCol_sub_le hM hu hu' hik p q B)
  · dsimp only
    have e : v' - (G * U) *ᵥ g = (v' - G *ᵥ v) + G *ᵥ (v - U *ᵥ g) := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      abel
    rw [e, WithLp.toLp_add]
    refine (norm_add_le _ _).trans ?_
    rw [hG.norm_toLp_mulVec, pow_succ]
    nlinarith [hvv, hv, norm_nonneg (WithLp.toLp 2 g)]
  · dsimp only
    have hg0 : 0 ≤ ‖WithLp.toLp 2 g‖ := norm_nonneg _
    have hmono : 12 * u * (1 + 12 * u) ^ j * ‖WithLp.toLp 2 g‖ ≤
        12 * u * (1 + 12 * u) ^ (j + 1) * ‖WithLp.toLp 2 g‖ := by
      rw [pow_succ]
      have : 0 ≤ 12 * u * (1 + 12 * u) ^ j * ‖WithLp.toLp 2 g‖ := by positivity
      nlinarith
    by_cases hri : r = i
    · subst hri
      have h0 : (G *ᵥ v) i = 0 := by
        have hz0 := congrArg star (neg_star_givensCoeffs_snd_mul_add p q)
        simp only [p, q, star_add, star_mul', star_neg, star_star, star_zero] at hz0
        rw [givens_mulVec_apply_left hik]
        linear_combination -hz0
      have hle : ‖v' i‖ ≤ ‖WithLp.toLp 2 (v' - G *ᵥ v)‖ := by
        have := PiLp.norm_apply_le (WithLp.toLp 2 (v' - G *ᵥ v)) i
        simpa [h0] using this
      exact (hle.trans hvv).trans (le_of_eq_of_le (by ring) hmono)
    · have hrj : (r : ℕ) < j := by
        have : (r : ℕ) ≠ j := fun h => hri (Fin.ext h)
        omega
      have hrk : r ≠ k := Fin.ne_of_val_ne (by simp only [ne_eq, k]; pomega)
      have : v' r = v r := by simp [v', vecRot, hri, hrk]
      rw [this]
      exact (hz r hrj).trans hmono

/-- The rotations of `RHess` keep the invariant, with the unitary of their log entries
(`NLAlib.SmallEig.rotateToEntries`). -/
theorem rotInv_fold (hM : StdModel u id M) (hu : 0 ≤ u) {N : ℕ}
    (hu' : 2 ≤ N → u ≤ 1 / 288) (A : Matrix (Fin N) (Fin N) ℂ) (g : Fin N → ℂ) :
    ∀ k ≤ N - 1, RotInv u A g k
      ((List.range k).foldl (fun Ag j => rotateToStepWord M j Ag) (A, g))
      (givensLog N (rotateToEntries M A g k))ᴴ
  | 0, _ => by
    have e : rotateToEntries M A g 0 = [] := rfl
    simp only [e, givensLog_nil, Matrix.conjTranspose_one]
    exact ⟨hasOrthonormalCols_one, by simp, by simp, fun r hr => absurd hr (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    have h := rotInv_step hM hu (hu' (by omega)) (by omega)
      (rotInv_fold hM hu hu' A g k (by omega))
    rw [rotateToEntries_succ, givensLog_append, Matrix.conjTranspose_mul]
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simpa [givensLog] using h

/-- **A phase for the last coordinate vector**: if $\|\mathbf{w}\| = R > 0$ and the entries of
$\mathbf{w}$ other than the last have joint norm at most $\delta R$ with $0 \le \delta < 1$, there
is $\lvert c\rvert = 1$ with $\|\mathbf{e}_{n+1} - (c/R)\mathbf{w}\| \le \sqrt2\,\delta$. -/
private theorem exists_phase_norm_sub_le {n : ℕ} (w : Fin (n + 1) → ℂ) {R δ : ℝ} (hR : 0 < R)
    (hw : ‖WithLp.toLp 2 w‖ = R) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (hoff : ∑ i : Fin n, ‖w i.castSucc‖ ^ 2 ≤ (δ * R) ^ 2) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ‖WithLp.toLp 2 (Pi.single (Fin.last n) 1 - (c * ((R⁻¹ : ℝ) : ℂ)) • w)‖ ≤ √2 * δ := by
  set a := w (Fin.last n)
  have hsum : ∑ i : Fin n, ‖w i.castSucc‖ ^ 2 + ‖a‖ ^ 2 = R ^ 2 := by
    rw [← hw, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  have ha2 : (1 - δ ^ 2) * R ^ 2 ≤ ‖a‖ ^ 2 := by nlinarith
  have ha : 0 < ‖a‖ := by
    have h0 : 0 < (1 - δ ^ 2) * R ^ 2 := by
      have : δ ^ 2 < 1 := by nlinarith
      have : 0 < 1 - δ ^ 2 := by linarith
      positivity
    by_contra hle
    have : ‖a‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
    rw [this] at ha2
    linarith
  set c := star a / (‖a‖ : ℂ)
  refine ⟨c, ?_, ?_⟩
  · rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self ha.ne']
  have hca : c * a = (‖a‖ : ℂ) := by
    simp only [c]
    rw [div_mul_eq_mul_div, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
      pow_two, Complex.ofReal_mul, mul_div_assoc, div_self (by exact_mod_cast ha.ne'), mul_one]
  set ρ := ‖a‖ / R
  have hρ1 : ρ ≤ 1 := by
    rw [div_le_one hR]
    have : 0 ≤ ∑ i : Fin n, ‖w i.castSucc‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [norm_nonneg a]
  set z : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1 - (c * ((R⁻¹ : ℝ) : ℂ)) • w
  have hc1 : ‖c‖ = 1 := by
    rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self ha.ne']
  have h1 : ∀ i : Fin n, ‖z i.castSucc‖ = ‖w i.castSucc‖ / R := fun i => by
    simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne (Fin.castSucc_ne_last i), zero_sub, norm_neg, norm_mul, hc1,
      Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), one_mul]
    rw [div_eq_inv_mul]
  have h2 : z (Fin.last n) = ((1 - ρ : ℝ) : ℂ) := by
    simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]
    rw [mul_comm c, mul_assoc, hca]
    push_cast
    simp only [ρ]
    push_cast
    ring
  have hzsq : ‖WithLp.toLp 2 z‖ ^ 2 = (∑ i : Fin n, ‖w i.castSucc‖ ^ 2) / R ^ 2 + (1 - ρ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
    simp only [h1, h2, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
      Finset.sum_div]
  have hoffR : (∑ i : Fin n, ‖w i.castSucc‖ ^ 2) / R ^ 2 = 1 - ρ ^ 2 := by
    simp only [ρ]
    field_simp
    linarith
  have hδR : (∑ i : Fin n, ‖w i.castSucc‖ ^ 2) / R ^ 2 ≤ δ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [hzsq, mul_pow, Real.sq_sqrt (by norm_num)]
  have hρ0 : 0 ≤ ρ := by positivity
  nlinarith

/-- The matrix bound of `RHess`: the reduction's error on top of the rotations' error. -/
theorem rhess_matrix_bound {n : ℕ} {A B U Q' H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q')
    (hB : specNorm (B - U * A * Uᴴ) ≤ ((1 + 50 * u) ^ n - 1) * specNorm A)
    (hE : specNorm (H - Q'ᴴ * B * Q') ≤ 50 * ((n : ℝ) + 1) ^ 2 * u * specNorm B)
    (hu : 0 ≤ u) (hNu : ((n : ℝ) + 1) * u ≤ 1 / 100) :
    specNorm (H - (Uᴴ * Q')ᴴ * A * (Uᴴ * Q')) ≤ 200 * ((n : ℝ) + 1) ^ 2 * u * specNorm A := by
  have hgrow : (1 + 50 * u) ^ n - 1 ≤ 2 * n * (50 * u) := by
    linarith [one_add_pow_le_one_add_two_mul (u := 50 * u) (N := n) (by positivity)
      (by nlinarith)]
  have hAU : specNorm (U * A * Uᴴ) = specNorm A := by
    have := hU.conjTranspose.specNorm_conjTranspose_mul_mul A
    rwa [Matrix.conjTranspose_conjTranspose] at this
  have hA0 := specNorm_nonneg A
  have hB' : specNorm (B - U * A * Uᴴ) ≤ 100 * n * u * specNorm A := by
    refine hB.trans ?_
    nlinarith [mul_le_mul_of_nonneg_right hgrow hA0]
  have hBn : specNorm B ≤ 2 * specNorm A := by
    have e : B = (B - U * A * Uᴴ) + U * A * Uᴴ := by abel
    have := specNorm_add_le (B - U * A * Uᴴ) (U * A * Uᴴ)
    rw [← e, hAU] at this
    nlinarith
  have e : H - (Uᴴ * Q')ᴴ * A * (Uᴴ * Q') = (H - Q'ᴴ * B * Q') + Q'ᴴ * (B - U * A * Uᴴ) * Q' := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc]
    abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [hQ'.specNorm_conjTranspose_mul_mul]
  have hn2 : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hBn (by positivity : (0 : ℝ) ≤ 50 * ((n : ℝ) + 1) ^ 2 * u),
    mul_le_mul_of_nonneg_right hn2 (mul_nonneg hu hA0)]

/-- The direction bound of `RHess`: the last column of $\mathbf{U}^{\mathsf{H}}$ is within
$60(n + 1)\boldsymbol{u}$ of a phase of $\mathbf{g}/\|\mathbf{g}\|$. -/
theorem rhess_phase {n : ℕ} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {g v : Fin (n + 1) → ℂ} (hU : HasOrthonormalCols U) (hg : g ≠ 0)
    (hv : ‖WithLp.toLp 2 (v - U *ᵥ g)‖ ≤ ((1 + 12 * u) ^ n - 1) * ‖WithLp.toLp 2 g‖)
    (hz : ∀ r : Fin (n + 1), (r : ℕ) < n → ‖v r‖ ≤ 12 * u * (1 + 12 * u) ^ n * ‖WithLp.toLp 2 g‖)
    (hu : 0 ≤ u) (hNu : ((n : ℝ) + 1) * u ≤ 1 / 100) (hnu : (n : ℝ) * u ≤ 1 / 100) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖WithLp.toLp 2 (Uᴴ *ᵥ Pi.single (Fin.last n) 1 -
      (c * ((‖WithLp.toLp 2 g‖⁻¹ : ℝ) : ℂ)) • g)‖ ≤ 60 * ((n : ℝ) + 1) * u := by
  set R := ‖WithLp.toLp 2 g‖
  have hR : 0 < R := norm_pos_iff.mpr (fun h => hg (by simpa using congrArg WithLp.ofLp h))
  set w := U *ᵥ g
  have hw : ‖WithLp.toLp 2 w‖ = R := hU.norm_toLp_mulVec g
  have hgrow : (1 + 12 * u) ^ n - 1 ≤ 2 * n * (12 * u) := by
    linarith [one_add_pow_le_one_add_two_mul (u := 12 * u) (N := n) (by positivity)
      (by nlinarith)]
  have hP : (1 + 12 * u) ^ n ≤ 1 + 24 * n * u := by linarith
  have hδ : (39 * ((n : ℝ) + 1) * u) < 1 := by nlinarith
  -- the entries of `w` other than the last
  have hoff : ∑ i : Fin n, ‖w i.castSucc‖ ^ 2 ≤ (39 * ((n : ℝ) + 1) * u * R) ^ 2 := by
    set e : Fin (n + 1) → ℂ := Pi.single (Fin.last n) (v (Fin.last n))
    have h1 : ‖WithLp.toLp 2 (v - e)‖ ≤ 15 * ((n : ℝ) + 1) * u * R := by
      have hvi : ∀ i : Fin n, ‖v i.castSucc‖ ≤ 15 * u * R := fun i => by
        refine (hz i.castSucc (by simp)).trans ?_
        nlinarith [mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 12 * u * R),
          mul_le_mul_of_nonneg_left hnu (by positivity : (0 : ℝ) ≤ u * R)]
      refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
      have hl : (v - e) (Fin.last n) = 0 := by simp [e]
      have hc : ∀ i : Fin n, (v - e) i.castSucc = v i.castSucc := fun i => by
        simp [e]
      simp only [hl, hc, norm_zero]
      have hs : ∑ i : Fin n, ‖v i.castSucc‖ ^ 2 ≤ n * (15 * u * R) ^ 2 := by
        calc ∑ i : Fin n, ‖v i.castSucc‖ ^ 2 ≤ ∑ _i : Fin n, (15 * u * R) ^ 2 :=
              Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hvi i) 2
          _ = n * (15 * u * R) ^ 2 := by simp
      have hn2 : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      have e1 : (15 * ((n : ℝ) + 1) * u * R) ^ 2 = ((n : ℝ) + 1) ^ 2 * (15 * u * R) ^ 2 := by ring
      rw [e1]
      nlinarith [mul_le_mul_of_nonneg_right hn2 (sq_nonneg (15 * u * R))]
    have h2 : ‖WithLp.toLp 2 (w - e)‖ ≤ 39 * ((n : ℝ) + 1) * u * R := by
      have e2 : w - e = (v - e) - (v - w) := by abel
      rw [e2, WithLp.toLp_sub]
      refine (norm_sub_le _ _).trans ?_
      nlinarith [hv, mul_le_mul_of_nonneg_right hgrow hR.le]
    have h3 : ∑ i : Fin n, ‖w i.castSucc‖ ^ 2 ≤ ‖WithLp.toLp 2 (w - e)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
      have : ∀ i : Fin n, (w - e) i.castSucc = w i.castSucc := fun i => by
        simp [e]
      simp only [this]
      exact le_add_of_nonneg_right (by positivity)
    exact h3.trans (pow_le_pow_left₀ (norm_nonneg _) h2 2)
  obtain ⟨c, hc, hcz⟩ := exists_phase_norm_sub_le w hR hw (by positivity) hδ hoff
  refine ⟨c, hc, ?_⟩
  have hgw : g = Uᴴ *ᵥ w := by
    rw [show w = U *ᵥ g from rfl, Matrix.mulVec_mulVec, hasOrthonormalCols_iff.mp hU,
      Matrix.one_mulVec]
  have e3 : Uᴴ *ᵥ Pi.single (Fin.last n) 1 - (c * ((R⁻¹ : ℝ) : ℂ)) • g =
      Uᴴ *ᵥ (Pi.single (Fin.last n) 1 - (c * ((R⁻¹ : ℝ) : ℂ)) • w) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ← hgw]
  rw [e3, hU.conjTranspose.norm_toLp_mulVec]
  refine hcz.trans ?_
  have hs2 : √2 ≤ 1.42 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  nlinarith [mul_le_mul_of_nonneg_right hs2 (by positivity : (0 : ℝ) ≤ 39 * ((n : ℝ) + 1) * u)]

end BackwardError

end NLAlib.SmallEig
