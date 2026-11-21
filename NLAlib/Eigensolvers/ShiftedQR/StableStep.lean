/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Hessenberg
public import NLAlib.Eigensolvers.ShiftedQR.MultiStep
public import NLAlib.Eigensolvers.ShiftedQR.SweepOutput
public import NLAlib.Eigensolvers.ShiftedQR.Backward
public import NLAlib.Matrix.QRIteration.StableStep
public import NLAlib.Matrix.FinitePrecision.GivensLog

/-!
# The rounded shifted QR step as a backward-stable step

[BanksGarzaVargasSrivastava2022, Definition 3.4] asks of an implicit QR step two inequalities
with **one** unitary $\widehat{\mathbf{Q}}$: the output is close to
$\widehat{\mathbf{Q}}^{\mathsf H}\mathbf{H}\widehat{\mathbf{Q}}$, and $\mathbf{H} - s$ is close to
$\widehat{\mathbf{Q}}\widehat{\mathbf{R}}$ with $\widehat{\mathbf{R}}$ upper triangular; the
output is upper Hessenberg and the last diagonal entry of $\widehat{\mathbf{R}}$ is returned (it
drives the computed potential). The scalar Givens step returns only the conjugated matrix, and in
floating point its output is Hessenberg only up to rounding. This file assembles the step that meets
the definition: the shift initialization, the sweep that also copies the last working diagonal entry
(`NLAlib.ShiftedQR.sweepWithDiag`), and a pass that zeroes the entries below the subdiagonal
(`NLAlib.ShiftedQR.clearBelowSubdiagonal`). A degree $k$ step repeats it in place with the $k$
shifts of a stored list.
The error base is $\|\mathbf{H}\|_2 + \lvert s\rvert$, not the paper's $\|\mathbf{H} - s\|_2$
(adding the shift back rounds the diagonal with error $\boldsymbol{u}\lvert s\rvert$). The
constant $300(n+1)^2$ covers the rounds, the shift initialization, the triangular part kept of the
working matrix (its rounded entries below the diagonal are dropped) and the zeroing pass, whose
error is bounded entrywise and so costs a factor $\sqrt{n+1}$ in the spectral norm; the paper has
$32n^{3/2}$.

## Main definitions

* `NLAlib.ShiftedQR.stepWithDiag`, `NLAlib.ShiftedQR.stepWithDiagInPlace`,
  `NLAlib.ShiftedQR.multiStepStable`: the programs. Each records its rotations, as the entries
  $(r, p, q)$ of the coefficient inputs, in a slotted log (`NLAlib.HoldsSlottedLog`), so that the
  step's unitary is the exact unitary of its log (`NLAlib.givensLog`).

## Main results

* `NLAlib.ShiftedQR.stepWithDiag_writes_of_inv`: the memory of the step, with any property of
  the rounds (`NLAlib.ShiftedQR.KeptByRound`).
* `NLAlib.ShiftedQR.stepWithDiag_isStableQRStep`,
  `NLAlib.ShiftedQR.stepWithDiagInPlace_isStableQRStep`: one rounded step is a backward-stable
  step by the unitary of its log.

Termination on any matrix is in `NLAlib.Eigensolvers.ShiftedQR.StableStepTermination`.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- **One shifted QR step with its last triangular diagonal entry and a Hessenberg output, recording
its rotations**: initialize a working copy $\mathbf{H} - s$ and the output $\mathbf{H}$; for the
rounds $r < n - 1$, record the entry $(r, \mathbf{W}_{r,r}, \mathbf{W}_{r+1,r})$ (the inputs of the
round's coefficients) as entry $i_0 + r$ of slot $j$ of the slotted log `Lg` of slot width $w$
(`NLAlib.slottedLogWrite`), then run the round (`NLAlib.ShiftedQR.round`: the coefficients, the
rotation of the working rows, the conjugation of the output); copy the last working diagonal entry
to `Dg`; zero the output below its subdiagonal. The interface is
`[n, w, j, i0] (A, S) → (Z, Dg, Lg)`; the working matrix and the four coefficient words are
scoped. The exact unitary of the recorded entries is the step's $\widehat{\mathbf{Q}}$. -/
def stepWithDiag : Stmt Op Tst := ops% [n, w, j, i0] (A, S) → (Z, Dg, Lg) {
  let W ← alloc (2 * (n * n));
  let Cf ← alloc 4;
  run (initializeState (Op := Op) (Tst := Tst)) [n] (A, S, W, Z);
  for r < n - 1 {
    run (slottedLogWrite (O := Op) (Q := Tst)) [w, j, i0 + r, r]
      (W[2 * (r * n + r)], W[2 * (r * n + r + 1)], Lg);
    run (round (Op := Op) (Tst := Tst)) [n, r] (W, Z, Cf, W, Z)
  };
  run (copyLastDiagonal (Op := Op) (Tst := Tst)) [n] (W, Dg);
  run (clearBelowSubdiagonal (Op := Op) (Tst := Tst)) [n] (Z)
}

/-- The step in place: run `NLAlib.ShiftedQR.stepWithDiag` into the scratch matrix `T`, then copy
it back to `A`. The interface is `[n, w, j, i0] (A, S, T) → (A, Dg, Lg)`. -/
def stepWithDiagInPlace : Stmt Op Tst := ops% [n, w, j, i0] (A, S, T) → (A, Dg, Lg) {
  run (stepWithDiag (Op := Op) (Tst := Tst)) [n, w, j, i0] (A, S, T, Dg, Lg);
  run (unaryMap (Has.inj ScalarOp.copy)) [2 * (n * n)] (T, A)
}

/-- **The degree $k$ rounded step, recording its rotations**: $k$ steps in place with the shifts
`S[2t]`, the last triangular diagonal entry of step $t$ written to `Ds[2t]`, the $n - 1$ rotations
of step $t$ recorded as the entries $t(n - 1), \dots, t(n - 1) + n - 2$ of slot $j$ of the slotted
log `Lg` of slot width $w \ge k(n - 1)$. The interface is `[n, k, w, j] (A, S) → (A, Ds, Lg)`; the
scratch matrix is scoped. -/
def multiStepStable : Stmt Op Tst := ops% [n, k, w, j] (A, S) → (A, Ds, Lg) {
  let T ← alloc (2 * (n * n));
  for t < k {
    run (stepWithDiagInPlace (Op := Op) (Tst := Tst)) [n, w, j, t * (n - 1)]
      (A, S[2 * t], T, A, Ds[2 * t], Lg)
  }
}

/-! ### The rounded sweep, round by round -/

section SweepMath

variable {n : ℕ}

/-- The entries of `X` at the positions $(i, t)$ with $t < k$ and $t < i$ (strictly below the
diagonal in the first $k$ columns); zero elsewhere. -/
private def lowerMask (k : ℕ) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i t => if (t : ℕ) < k ∧ (t : ℕ) < i then X i t else 0

/-- A mask has spectral norm at most the Frobenius norm of the masked matrix. -/
private theorem specNorm_lowerMask_le (k : ℕ) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    specNorm (lowerMask k X) ≤ frobNorm X := by
  refine (specNorm_le_frobNorm _).trans ?_
  refine (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 ?_
  rw [frobNorm_sq_eq_sum, frobNorm_sq_eq_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun t _ => ?_
  simp only [lowerMask, Matrix.of_apply]
  split_ifs
  · exact le_rfl
  · simp

/-- The invariant of the rounded sweep after `k` rounds, from the shifted matrix `W₀` and the
output `H`. With $\mathbf{P}$ the product of the exact rotations so far: $\mathbf{P}$ is unitary,
vanishes beyond its superdiagonal and is the identity below row $k$; the working matrix
$\mathbf{W}$ is triangular in its first $k$ columns up to the rounding residuals `J`, and
Hessenberg in the others; $\mathbf{P}^{\mathsf H}\mathbf{W}$ is within $25k\boldsymbol{u}
\|\mathbf{W}_0\|_2$ of $\mathbf{W}_0$, `J` is as small, and $\mathbf{P}^{\mathsf H}\mathbf{Z}
\mathbf{P}$ is within $50k\boldsymbol{u}\|\mathbf{H}\|_2$ of $\mathbf{H}$. -/
private def RoundedSweepInv (u : ℝ) (k : ℕ) (H W₀ P W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Prop :=
  ∃ J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols P ∧
    (∀ a b : Fin (n + 1), (a : ℕ) + 1 < b → P a b = 0) ∧
    (∀ a b : Fin (n + 1), k + 1 ≤ (a : ℕ) → P a b = if a = b then 1 else 0) ∧
    (∀ i t : Fin (n + 1), ¬((t : ℕ) < k ∧ (t : ℕ) < i) → J i t = 0) ∧
    (∀ i t : Fin (n + 1), (t : ℕ) < k → (t : ℕ) < i → W i t = J i t) ∧
    (∀ i t : Fin (n + 1), k ≤ (t : ℕ) → (t : ℕ) + 1 < i → W i t = 0) ∧
    specNorm (Pᴴ * W - W₀) ≤ 25 * k * u * specNorm W₀ ∧
    specNorm J ≤ 25 * k * u * specNorm W₀ ∧
    specNorm (Pᴴ * Z * P - H) ≤ 50 * k * u * specNorm H

/-- The rotation of round `k` keeps the pattern of the accumulated factor: zero beyond the
superdiagonal, and the identity below row $k + 1$. -/
private theorem givensHessenbergStep_mul_pattern {k : ℕ}
    (W P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (h1 : ∀ a b : Fin (n + 1), (a : ℕ) + 1 < b → P a b = 0)
    (h2 : ∀ a b : Fin (n + 1), k + 1 ≤ (a : ℕ) → P a b = if a = b then 1 else 0) :
    (∀ a b : Fin (n + 1), (a : ℕ) + 1 < b → (givensHessenbergStep W k * P) a b = 0) ∧
    (∀ a b : Fin (n + 1), k + 1 + 1 ≤ (a : ℕ) →
      (givensHessenbergStep W k * P) a b = if a = b then 1 else 0) := by
  refine ⟨fun a b hab => ?_, fun a b ha => ?_⟩
  · by_cases ha : (a : ℕ) = k ∨ (a : ℕ) = k + 1
    · have hz : ∀ c : Fin (n + 1), ((c : ℕ) = k ∨ (c : ℕ) = k + 1) → P c b = 0 := by
        rintro c (hc | hc)
        · exact h1 c b (by omega)
        · rw [h2 c b (by omega), if_neg]
          rintro rfl
          omega
      rw [givensHessenbergStep_mul_apply_of_apply_eq_zero W P hz a]
      exact h1 a b hab
    · push Not at ha
      rw [givensHessenbergStep_mul_apply_of_ne W P ha.1 ha.2]
      exact h1 a b hab
  · rw [givensHessenbergStep_mul_apply_of_ne W P (by omega) (by omega)]
    exact h2 a b (by omega)

/-- The rotation of round `k` zeroes the entry $(k + 1, k)$ of the working matrix. -/
private theorem givensHessenbergStep_mul_apply_succ {k : ℕ} (hk : k < n)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (givensHessenbergStep W k * W) ⟨k + 1, by omega⟩ ⟨k, by omega⟩ = 0 := by
  have hij : (⟨k, by omega⟩ : Fin (n + 1)) ≠ ⟨k + 1, by omega⟩ :=
    Fin.ne_of_val_ne (Nat.succ_ne_self k).symm
  rw [givensHessenbergStep_of_lt W (by omega) (by omega) (by omega), givens_mul_apply_right hij]
  exact neg_star_givensCoeffs_snd_mul_add _ _

/-- The residual pattern after round `k`: if `W'` agrees with `W` off the rows $k, k + 1$, then
`J' = G J + lowerMask (k + 1) (W' - G W)` carries the residuals of the first $k + 1$ columns,
with `G` the exact rotation of the round. -/
private theorem residual_pattern_succ {k : ℕ} (hk : k < n)
    {W W' J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hW' : ∀ r t : Fin (n + 1), (r : ℕ) ≠ k → (r : ℕ) ≠ k + 1 → W' r t = W r t)
    (ha : ∀ i t : Fin (n + 1), ¬((t : ℕ) < k ∧ (t : ℕ) < i) → J i t = 0)
    (hb : ∀ i t : Fin (n + 1), (t : ℕ) < k → (t : ℕ) < i → W i t = J i t)
    (hc : ∀ i t : Fin (n + 1), k ≤ (t : ℕ) → (t : ℕ) + 1 < i → W i t = 0) :
    (∀ i t : Fin (n + 1), ¬((t : ℕ) < k + 1 ∧ (t : ℕ) < i) →
      (givensHessenbergStep W k * J + lowerMask (k + 1) (W' - givensHessenbergStep W k * W))
        i t = 0) ∧
    (∀ i t : Fin (n + 1), (t : ℕ) < k + 1 → (t : ℕ) < i → W' i t =
      (givensHessenbergStep W k * J + lowerMask (k + 1) (W' - givensHessenbergStep W k * W))
        i t) ∧
    (∀ i t : Fin (n + 1), k + 1 ≤ (t : ℕ) → (t : ℕ) + 1 < i → W' i t = 0) := by
  set G := givensHessenbergStep W k
  refine ⟨fun i t hit => ?_, fun i t ht hti => ?_, fun i t ht hti => ?_⟩
  · rw [Matrix.add_apply]
    simp only [lowerMask, Matrix.of_apply, if_neg hit, add_zero]
    by_cases hi : (i : ℕ) = k ∨ (i : ℕ) = k + 1
    · have hz : ∀ c : Fin (n + 1), ((c : ℕ) = k ∨ (c : ℕ) = k + 1) → J c t = 0 :=
        fun c _ => ha c t (by omega)
      rw [givensHessenbergStep_mul_apply_of_apply_eq_zero W J hz i]
      exact ha i t (by omega)
    · push Not at hi
      rw [givensHessenbergStep_mul_apply_of_ne W J hi.1 hi.2]
      exact ha i t (by omega)
  · -- the rotation of `W - J` vanishes at the residual positions of the round
    have hX : (G * (W - J)) i t = 0 := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | ht'
      · have hz : ∀ c : Fin (n + 1), ((c : ℕ) = k ∨ (c : ℕ) = k + 1) → (W - J) c t = 0 :=
          fun c hc => by rw [Matrix.sub_apply, hb c t ht' (by omega), sub_self]
        rw [givensHessenbergStep_mul_apply_of_apply_eq_zero W _ hz i, Matrix.sub_apply,
          hb i t ht' hti, sub_self]
      · have hJk : ∀ c : Fin (n + 1), J c t = 0 := fun c => ha c t (by omega)
        by_cases hi : (i : ℕ) = k + 1
        · have hk1 : k + 1 < n + 1 := by omega
          have hk0 : k < n + 1 := by omega
          rw [show i = ⟨k + 1, hk1⟩ from Fin.ext hi, show t = ⟨k, hk0⟩ from Fin.ext ht']
          rw [show t = ⟨k, hk0⟩ from Fin.ext ht'] at hJk
          rw [Matrix.mul_sub, Matrix.sub_apply, givensHessenbergStep_mul_apply_succ hk W,
            givensHessenbergStep_mul_apply_of_apply_eq_zero W J (fun c _ => hJk c), hJk,
            sub_zero]
        · rw [givensHessenbergStep_mul_apply_of_ne W _ (by omega) hi, Matrix.sub_apply,
            hc i t (by omega) (by omega), hJk i, sub_self]
    have hG : (G * W) i t = (G * J) i t := by
      rw [Matrix.mul_sub, Matrix.sub_apply, sub_eq_zero] at hX
      exact hX
    simp only [Matrix.add_apply, lowerMask, Matrix.of_apply, if_pos (And.intro ht hti),
      Matrix.sub_apply, hG]
    ring
  · rw [hW' i t (by omega) (by omega)]
    exact hc i t (by omega) hti

/-- The bounds of one round: the working matrix and the output move by the rounding errors
of the round, carried back through the accumulated factor. -/
private theorem roundedSweep_norms_succ {u A h : ℝ} (hu : 0 ≤ u) {k : ℕ}
    (hku : (k : ℝ) * u ≤ 1 / 2500) {P G W W' J W₀ Z Z' H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hP : HasOrthonormalCols P) (hG : HasOrthonormalCols G) (hA : specNorm W₀ = A)
    (hh : specNorm H = h)
    (hEW : specNorm (Pᴴ * W - W₀) ≤ 25 * k * u * A) (hJ : specNorm J ≤ 25 * k * u * A)
    (hEZ : specNorm (Pᴴ * Z * P - H) ≤ 50 * k * u * h)
    (hF : frobNorm (W' - G * W) ≤ 24 * u * specNorm W)
    (hZ' : specNorm (Z' - G * Z * Gᴴ) ≤ 49 * u * specNorm Z) :
    specNorm ((G * P)ᴴ * W' - W₀) ≤ 25 * ((k + 1 : ℕ) : ℝ) * u * A ∧
      specNorm (G * J + lowerMask (k + 1) (W' - G * W)) ≤ 25 * ((k + 1 : ℕ) : ℝ) * u * A ∧
      specNorm ((G * P)ᴴ * Z' * (G * P) - H) ≤ 50 * ((k + 1 : ℕ) : ℝ) * u * h := by
  have hA0 : 0 ≤ A := hA ▸ specNorm_nonneg _
  have hh0 : 0 ≤ h := hh ▸ specNorm_nonneg _
  have hGP : HasOrthonormalCols (G * P)ᴴ := (hG.mul hP).conjTranspose
  have hGG : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Gᴴ * (G * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hG.conjTranspose_mul_self, Matrix.one_mul]
  have hnorm : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      specNorm ((G * P)ᴴ * X * (G * P)) = specNorm X := fun X => by
    rw [Matrix.mul_assoc, hGP.specNorm_mul_left, ← Matrix.conjTranspose_conjTranspose (G * P),
      hGP.specNorm_mul_conjTranspose_right]
  have hWn : specNorm W ≤ A + 25 * k * u * A := by
    have h1 := specNorm_add_le W₀ (Pᴴ * W - W₀)
    rw [add_sub_cancel, hP.conjTranspose.specNorm_mul_left, hA] at h1
    linarith
  have hZn : specNorm Z ≤ h + 50 * k * u * h := by
    have h1 := specNorm_add_le H (Pᴴ * Z * P - H)
    have hZP : specNorm (Z * P) = specNorm Z := by
      simpa using hP.conjTranspose.specNorm_mul_conjTranspose_right Z
    have hPZP : specNorm (Pᴴ * Z * P) = specNorm Z := by
      rw [Matrix.mul_assoc, hP.conjTranspose.specNorm_mul_left, hZP]
    rw [add_sub_cancel, hPZP, hh] at h1
    linarith
  have hFs := (specNorm_le_frobNorm _).trans hF
  have kW : 24 * u * specNorm W ≤ 25 * u * A := by
    nlinarith [mul_nonneg (mul_nonneg hu hA0) (show 0 ≤ 1 - 600 * (k * u) by linarith)]
  have kZ : 49 * u * specNorm Z ≤ 50 * u * h := by
    nlinarith [mul_nonneg (mul_nonneg hu hh0) (show 0 ≤ 1 - 2450 * (k * u) by linarith)]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · have e : (G * P)ᴴ * W' - W₀ = (Pᴴ * W - W₀) + (G * P)ᴴ * (W' - G * W) := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.mul_assoc Pᴴ Gᴴ (G * W), hGG]
      abel
    rw [e]
    refine (specNorm_add_le _ _).trans ?_
    rw [hGP.specNorm_mul_left]
    linarith
  · refine (specNorm_add_le _ _).trans ?_
    rw [hG.specNorm_mul_left]
    linarith [specNorm_lowerMask_le (k + 1) (W' - G * W)]
  · have e : (G * P)ᴴ * Z' * (G * P) - H =
        (Pᴴ * Z * P - H) + (G * P)ᴴ * (Z' - G * Z * Gᴴ) * (G * P) := by
      have e1 : (G * P)ᴴ * (G * Z * Gᴴ) * (G * P) = Pᴴ * Z * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hGG]
      rw [Matrix.mul_sub, Matrix.sub_mul, e1]
      abel
    rw [e]
    refine (specNorm_add_le _ _).trans ?_
    rw [hnorm]
    linarith

/-- **One rounded round keeps the invariant of the sweep**: rotating the rows $k, k + 1$ of the
working matrix and conjugating the output by the coefficients computed from its column $k$ moves
the invariant from $k$ to $k + 1$ rounds. -/
private theorem roundedSweepInv_succ {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) {k : ℕ} (hk : k < n)
    {H W₀ P W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {cv sv : ℂ}
    (hcs : roundedGivensCoeffs M (W ⟨k, by omega⟩ ⟨k, by omega⟩)
      (W ⟨k + 1, by omega⟩ ⟨k, by omega⟩) = (cv, sv))
    (h : RoundedSweepInv u k H W₀ P W Z) :
    RoundedSweepInv u (k + 1) H W₀ (givensHessenbergStep W k * P)
      (machineRowRotation M ⟨k, by omega⟩ ⟨k + 1, by omega⟩ cv sv W)
      (machineColRotation M ⟨k, by omega⟩ ⟨k + 1, by omega⟩ cv sv
        (machineRowRotation M ⟨k, by omega⟩ ⟨k + 1, by omega⟩ cv sv Z)) := by
  obtain ⟨J, hP, hP1, hP2, ha, hb, hc, hEW, hJ, hEZ⟩ := h
  have hij : (⟨k, by omega⟩ : Fin (n + 1)) ≠ ⟨k + 1, by omega⟩ :=
    Fin.ne_of_val_ne (Nat.succ_ne_self k).symm
  have hGg := givensHessenbergStep_of_lt W (k := k) (by omega) (by omega) (by omega)
  have hku : (k : ℝ) * u ≤ 1 / 2500 := by
    have : (k : ℝ) ≤ n + 1 := by exact_mod_cast (by omega : k ≤ n + 1)
    nlinarith
  have hrot := isRoundedRowRotation_machineRowRotation hM hu (by nlinarith) hij
    (W ⟨k, by omega⟩ ⟨k, by omega⟩) (W ⟨k + 1, by omega⟩ ⟨k, by omega⟩) W
  rw [hcs] at hrot
  have hF := hrot.frobNorm_sub_le (by positivity)
  have hZ' := specNorm_machineColRotation_sub_le hM hu (by nlinarith) hij
    (W ⟨k, by omega⟩ ⟨k, by omega⟩) (W ⟨k + 1, by omega⟩ ⟨k, by omega⟩) Z
  rw [hcs] at hZ'
  rw [← hGg] at hF hZ'
  obtain ⟨hQ1, hQ2⟩ := givensHessenbergStep_mul_pattern W P hP1 hP2
  obtain ⟨ha', hb', hc'⟩ := residual_pattern_succ hk
    (fun r t hr hr' => hrot.1 r t (Fin.ne_of_val_ne hr) (Fin.ne_of_val_ne hr')) ha hb hc
  obtain ⟨n1, n2, n3⟩ := roundedSweep_norms_succ hu hku hP
    (hasOrthonormalCols_givensHessenbergStep W k) rfl rfl hEW hJ hEZ
    (by linarith) hZ'
  exact ⟨_, (hasOrthonormalCols_givensHessenbergStep W k).mul hP, hQ1, hQ2, ha', hb', hc',
    n1, n2, n3⟩

/-- Before the first round: the factor is the identity and there are no residuals. -/
private theorem roundedSweepInv_zero {u : ℝ} {H W₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hW : IsUpperHessenberg W₀) : RoundedSweepInv u 0 H W₀ 1 W₀ H := by
  refine ⟨0, hasOrthonormalCols_one, fun a b hab => Matrix.one_apply_ne ?_,
    fun a b _ => Matrix.one_apply, fun _ _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _),
    fun i t _ hti => hW i t hti, ?_, ?_, ?_⟩
  · rintro rfl
    omega
  all_goals simp

/-- The machine shift of an upper Hessenberg matrix is upper Hessenberg: only the diagonal is
changed. -/
private theorem isUpperHessenberg_machineShiftedPrefix {M : Machine ℝ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (s : ℂ) (k : ℕ) :
    IsUpperHessenberg (machineShiftedPrefix M H s k) := by
  intro i j hij
  have hne : i ≠ j := fun h => by subst h; omega
  simp only [ShiftedQR.machineShiftedPrefix, Matrix.of_apply, hne, false_and, if_false]
  exact hH i j hij

/-- A complex number rounded componentwise with relative error $\boldsymbol{u}$ is within
$\boldsymbol{u}\lvert z\rvert$ of $z$. -/
private theorem norm_sub_le_of_abs_re_im {u : ℝ} {w z : ℂ} (hre : |w.re - z.re| ≤ u * |z.re|)
    (him : |w.im - z.im| ≤ u * |z.im|) (hu : 0 ≤ u) : ‖w - z‖ ≤ u * ‖z‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hu (norm_nonneg _))).1 ?_
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  have h1 := pow_le_pow_left₀ (abs_nonneg _) hre 2
  have h2 := pow_le_pow_left₀ (abs_nonneg _) him 2
  rw [sq_abs, mul_pow, sq_abs] at h1 h2
  nlinarith

/-- The rounded shift: on a machine with the standard model, subtracting the shift from the
diagonal moves $\mathbf{H} - s\mathbf{I}$ by at most $\boldsymbol{u}(\|\mathbf{H}\|_2 + \lvert
s\rvert)$ in the spectral norm (the error is diagonal). -/
theorem specNorm_machineShiftedPrefix_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hu : 0 ≤ u) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ) :
    specNorm (machineShiftedPrefix M H s (n + 1) - (H - s • (1 : Matrix _ _ ℂ))) ≤
      u * (specNorm H + ‖s‖) := by
  have e : machineShiftedPrefix M H s (n + 1) - (H - s • (1 : Matrix _ _ ℂ)) =
      Matrix.diagonal fun i =>
        (⟨M.sub (H i i).re s.re, M.sub (H i i).im s.im⟩ : ℂ) - (H i i - s) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [ShiftedQR.machineShiftedPrefix, Matrix.sub_apply, Matrix.of_apply,
        Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        true_and, if_pos i.isLt]
    · simp [ShiftedQR.machineShiftedPrefix, hij, Matrix.one_apply_ne hij]
  rw [e]
  refine specNorm_diagonal_le (by positivity) fun i => ?_
  have h1 := hM.sub (H i i).re s.re
  have h2 := hM.sub (H i i).im s.im
  simp only [id] at h1 h2
  refine (norm_sub_le_of_abs_re_im (z := H i i - s) (by simpa using h1) (by simpa using h2)
    hu).trans (mul_le_mul_of_nonneg_left ?_ hu)
  exact (norm_sub_le _ _).trans (add_le_add_left (norm_apply_le_specNorm H i i) _)

/-- The numbers of the final bound: with $a = \|\mathbf{H}\|_2 + \lvert s\rvert$, a factorization
error $d \le \boldsymbol{u}a(1 + 100n)$ and a similarity error $e \le 50n\boldsymbol{u}a$ fit in
$300(n+1)^2\boldsymbol{u}a$, also after the factor $\sqrt{n+1}$ of the zeroed part. -/
private theorem roundedSweep_budget {u a d e : ℝ} (hua : 0 ≤ u * a)
    (hd : d ≤ u * a + 100 * n * (u * a)) (he : e ≤ 50 * n * (u * a)) :
    d ≤ 300 * (n + 1) ^ 2 * u * a ∧ d + √(n + 1 : ℝ) * (d + e) ≤ 300 * (n + 1) ^ 2 * u * a := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsq : √(n + 1 : ℝ) ≤ n + 1 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hde : 0 ≤ u * a + 150 * n * (u * a) := by positivity
  have hde' : d + e ≤ u * a + 150 * n * (u * a) := by linarith
  have hs0 : 0 ≤ √(n + 1 : ℝ) := Real.sqrt_nonneg _
  have : √(n + 1 : ℝ) * (d + e) ≤ (n + 1) * (u * a + 150 * n * (u * a)) := by
    by_cases hp : 0 ≤ d + e
    · exact mul_le_mul hsq hde' hp (by positivity)
    · push Not at hp
      nlinarith
  constructor <;> nlinarith [mul_nonneg hn hua, mul_nonneg (mul_nonneg hn hn) hua]

/-- **The invariant after the last round is a backward-stable step**: with $\mathbf{Q} =
\mathbf{P}^{\mathsf H}$ and $\mathbf{R} = \mathbf{W} - \mathbf{J}$ (the working matrix without its
rounding residuals, upper triangular, with the stored last diagonal entry), the output with its
fill deleted is a stable step from $(\mathbf{H}, s)$ when the shifted matrix $\mathbf{W}_0$ is
within $\boldsymbol{u}(\|\mathbf{H}\|_2 + \lvert s\rvert)$ of $\mathbf{H} - s\mathbf{I}$. -/
private theorem RoundedSweepInv.exists_isStableQRStep {u : ℝ} (hu : 0 ≤ u)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) {H W₀ P W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s : ℂ}
    (h : RoundedSweepInv u n H W₀ P W Z)
    (hW₀ : specNorm (W₀ - (H - s • (1 : Matrix _ _ ℂ))) ≤ u * (specNorm H + ‖s‖)) :
    ∃ R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsStableQRStepBy Pᴴ (300 * (n + 1) ^ 2 * u * (specNorm H + ‖s‖)) H s
        (upperHessenbergPart Z) R ∧
        R (Fin.last n) (Fin.last n) = W (Fin.last n) (Fin.last n) := by
  obtain ⟨J, hP, hP1, -, ha, hb, -, hEW, hJ, hEZ⟩ := h
  set a := specNorm H + ‖s‖
  have hu1 : u ≤ 1 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hh : specNorm H ≤ a := le_add_of_nonneg_right (norm_nonneg s)
  have hA : specNorm W₀ ≤ 2 * a := by
    have h1 := specNorm_add_le (H - s • (1 : Matrix _ _ ℂ)) (W₀ - (H - s • 1))
    have h2 := specNorm_sub_le H (s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
    rw [specNorm_smul, specNorm_one, mul_one] at h2
    rw [add_sub_cancel] at h1
    nlinarith [mul_le_mul_of_nonneg_right hu1 (add_nonneg (specNorm_nonneg H) (norm_nonneg s))]
  have hua : 0 ≤ u * a := mul_nonneg hu (add_nonneg (specNorm_nonneg H) (norm_nonneg s))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hD : specNorm (H - s • (1 : Matrix _ _ ℂ) - Pᴴ * (W - J)) ≤ u * a + 100 * n * (u * a) := by
    have e : H - s • (1 : Matrix _ _ ℂ) - Pᴴ * (W - J) =
        -(W₀ - (H - s • 1)) - (Pᴴ * W - W₀) + Pᴴ * J := by
      rw [Matrix.mul_sub]; abel
    rw [e]
    refine (specNorm_add_le _ _).trans ?_
    rw [hP.conjTranspose.specNorm_mul_left]
    have t1 : specNorm (-(W₀ - (H - s • 1)) - (Pᴴ * W - W₀)) ≤
        u * a + 25 * n * u * specNorm W₀ :=
      (specNorm_sub_le _ _).trans (add_le_add (by rw [specNorm_neg]; exact hW₀) hEW)
    refine (add_le_add t1 hJ).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 25 * n * u)]
  have hE : specNorm (Pᴴ * Z * Pᴴᴴ - H) ≤ 50 * n * (u * a) := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hEZ.trans (by nlinarith [mul_le_mul_of_nonneg_left hh (by positivity :
      (0 : ℝ) ≤ 50 * n * u)])
  obtain ⟨hb1, hb2⟩ := roundedSweep_budget (d := u * a + 100 * n * (u * a))
    (e := 50 * n * (u * a)) hua le_rfl le_rfl
  refine ⟨W - J, hP.conjTranspose.isStableQRStepBy_upperHessenbergPart (fun i j hij => ?_)
    (fun i t hti => ?_) hD hE hb1 hb2, ?_⟩
  · rw [Matrix.conjTranspose_apply, hP1 j i hij, star_zero]
  · have hti' : (t : ℕ) < i := hti
    rw [Matrix.sub_apply, hb i t (by omega) hti', sub_self]
  · rw [Matrix.sub_apply, ha (Fin.last n) (Fin.last n) (by simp), sub_zero]

end SweepMath

/-- The exact rotation of round `k` is the rotation of its log entry
$(k, \mathbf{W}_{k,k}, \mathbf{W}_{k+1,k})$. -/
private theorem givensHessenbergStep_eq_givensAt {n k : ℕ} (hk : k < n)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    givensHessenbergStep W k =
      givensAt (n + 1) (k, W ⟨k, by omega⟩ ⟨k, by omega⟩, W ⟨k + 1, by omega⟩ ⟨k, by omega⟩) := by
  rw [givensHessenbergStep_of_lt W (by omega) (by omega) (by omega), givensAt,
    dif_pos (by simpa using hk)]

/-- The invariant of the recording loop after `r` rounds: `r` entries appended to the pending
slot of the log, and a property `Inv` of the round, the entries, the working matrix at `wv` and the
output at `zv`. -/
private def StepLoopInv {n : ℕ}
    (Inv : ℕ → List GivensEntry → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop)
    (wv zv lg : ℕ × ℕ) (ns w : ℕ) (L : List (Option (List GivensEntry))) (P : List GivensEntry)
    (r : ℕ) (s : Store ℝ) : Prop :=
  ∃ es : List GivensEntry, es.length = r ∧ (∀ e ∈ es, e.1 + 1 < n + 1) ∧
    HoldsSlottedLog lg ns w L (P ++ es) s ∧
      ∃ W Z, Inv r es W Z ∧ HoldsMatrix wv W s ∧ HoldsMatrix zv Z s

/-- A property of the recording loop of `NLAlib.ShiftedQR.stepWithDiag` is kept by round `r`:
from the entries `es`, the working matrix $\mathbf{W}$ and the output $\mathbf{Z}$, it holds after
appending the entry
$(r, \mathbf{W}_{r,r}, \mathbf{W}_{r+1,r})$ and the machine round
(`NLAlib.machineRowRotation`, `NLAlib.machineColRotation`) by the rounded coefficients. -/
def KeptByRound (M : Machine ℝ) {n : ℕ} (Inv : ℕ → List GivensEntry →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop)
    (r : ℕ) : Prop :=
  ∀ (hr : r < n) (es : List GivensEntry) (W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    Inv r es W Z →
    Inv (r + 1) (es ++ [(r, W ⟨r, by omega⟩ ⟨r, by omega⟩, W ⟨r + 1, by omega⟩ ⟨r, by omega⟩)])
      (machineRowRotation M ⟨r, by omega⟩ ⟨r + 1, by omega⟩
        (roundedGivensCoeffs M (W ⟨r, by omega⟩ ⟨r, by omega⟩)
          (W ⟨r + 1, by omega⟩ ⟨r, by omega⟩)).1
        (roundedGivensCoeffs M (W ⟨r, by omega⟩ ⟨r, by omega⟩)
          (W ⟨r + 1, by omega⟩ ⟨r, by omega⟩)).2 W)
      (machineColRotation M ⟨r, by omega⟩ ⟨r + 1, by omega⟩
        (roundedGivensCoeffs M (W ⟨r, by omega⟩ ⟨r, by omega⟩)
          (W ⟨r + 1, by omega⟩ ⟨r, by omega⟩)).1
        (roundedGivensCoeffs M (W ⟨r, by omega⟩ ⟨r, by omega⟩)
          (W ⟨r + 1, by omega⟩ ⟨r, by omega⟩)).2
        (machineRowRotation M ⟨r, by omega⟩ ⟨r + 1, by omega⟩
          (roundedGivensCoeffs M (W ⟨r, by omega⟩ ⟨r, by omega⟩)
            (W ⟨r + 1, by omega⟩ ⟨r, by omega⟩)).1
          (roundedGivensCoeffs M (W ⟨r, by omega⟩ ⟨r, by omega⟩)
            (W ⟨r + 1, by omega⟩ ⟨r, by omega⟩)).2 Z))

/-- **One recorded round**: writing the entry of round `r` to the log and running the round keeps
the invariant of the recording loop. -/
private theorem logRound_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hCmp : IsCmp id I)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {n r : ℕ} (hr : r < n) (hn : n ≤ nmax)
    {Inv : ℕ → List GivensEntry → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop} (hInv : KeptByRound M Inv r)
    {wv zv cf lg pw qw : ℕ × ℕ}
    {ns w : ℕ} {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    {ds₁ ds₂ : List IExp} {as₁ as₂ : List Operand}
    (hpw : pw = (wv.1, wv.2 + 2 * (r * (n + 1) + r)))
    (hqw : qw = (wv.1, wv.2 + 2 * (r * (n + 1) + r + 1)))
    (hd₁ : IExp.evalList ρ.idx ds₁ = some [w, L.length, P.length + r, r])
    (ha₁ : Operand.evalList ρ as₁ = some [pw, qw, lg])
    (hd₂ : IExp.evalList ρ.idx ds₂ = some [n + 1, r])
    (ha₂ : Operand.evalList ρ as₂ = some [wv, zv, cf, wv, zv])
    (hj : L.length < ns) (hw : P.length + n ≤ w) (hc : cf.2 + 4 ≤ m.store.len cf.1)
    (hwz : Fp.Disj (Store.inBlock wv.1 wv.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock zv.1 zv.2 (2 * ((n + 1) * (n + 1)))))
    (hwc : Fp.Disj (Store.inBlock wv.1 wv.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4))
    (hzc : Fp.Disj (Store.inBlock zv.1 zv.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4))
    (hlw : lg.1 ≠ wv.1)
    (hlF : Fp.Disj (Store.inBlock wv.1 wv.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock zv.1 zv.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4)
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))))
    (hl : m.Live [wv, zv, cf, lg]) (h : StepLoopInv Inv wv zv lg ns w L P r m.store) :
    Writes .total I τ (.seq (.frame ds₁ as₁ (slottedLogWrite (O := Op) (Q := Tst)))
        (.frame ds₂ as₂ (round (Op := Op) (Tst := Tst)))) ρ
      (Store.inBlock wv.1 wv.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock zv.1 zv.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧ StepLoopInv Inv wv zv lg ns w L P (r + 1) m'.store) m := by
  subst hpw hqw
  obtain ⟨es, hes, hpl, hlog, W, Z, hinv, hW, hZ⟩ := h
  have hlen : (P ++ es).length = P.length + r := by simp [hes]
  rw [← hlen] at hd₁
  have hlive : m.Live [(wv.1, wv.2 + 2 * (r * (n + 1) + r)),
      (wv.1, wv.2 + 2 * (r * (n + 1) + r + 1)), lg] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.1, hl.2.2.2⟩
  have hp : m.store.readBlock wv.1 (wv.2 + 2 * (r * (n + 1) + r)) 2 =
      some [(W ⟨r, by omega⟩ ⟨r, by omega⟩).re, (W ⟨r, by omega⟩ ⟨r, by omega⟩).im] :=
    hW.read_entry ⟨r, by omega⟩ ⟨r, by omega⟩
  have hq : m.store.readBlock wv.1 (wv.2 + 2 * (r * (n + 1) + r + 1)) 2 =
      some [(W ⟨r + 1, by omega⟩ ⟨r, by omega⟩).re, (W ⟨r + 1, by omega⟩ ⟨r, by omega⟩).im] :=
    hW.read_entry ⟨r + 1, by omega⟩ ⟨r, by omega⟩
  have hPw : (P ++ es).length < w := by omega
  have hlog' := slottedLogWrite_writes (O := Op) (Q := Tst) (τ := τ) hS hL hNat (r := r)
    (pw := (wv.1, wv.2 + 2 * (r * (n + 1) + r))) (qw := (wv.1, wv.2 + 2 * (r * (n + 1) + r + 1)))
    (by omega) hlog hj hPw hp hq
    (Fp.disj_sup_right.mpr ⟨Fp.disj_inBlock_of_ne hlw, Fp.disj_inBlock_of_ne hlw⟩)
  refine hlog'.frame_seq_le hd₁ ha₁ hlive le_sup_right ?_
  rintro m₁ hfr₁ ⟨hp₁, hlog₁⟩
  have hround := round_writes_word (τ := τ) (m := m₁) (n := n + 1) (k := r) hS hCmp
    (by omega)
    (cv := (roundedGivensCoeffs M (W ⟨r, by omega⟩ ⟨r, by omega⟩)
      (W ⟨r + 1, by omega⟩ ⟨r, by omega⟩)).1)
    (sv := (roundedGivensCoeffs M (W ⟨r, by omega⟩ ⟨r, by omega⟩)
      (W ⟨r + 1, by omega⟩ ⟨r, by omega⟩)).2) rfl
    (hW.of_eqOff hfr₁ (hlF.mono (le_sup_left.trans le_sup_left) le_rfl).symm)
    (hZ.of_eqOff hfr₁ (hlF.mono (le_sup_right.trans le_sup_left) le_rfl).symm)
    (by rw [hfr₁.len_eq]; exact hc) hwz hwc hzc
  refine (hround.in_frame hd₂ ha₂ ((hl.congr hfr₁.length_eq).mono (by simp))).mono
    le_sup_left ?_
  rintro m₂ hfr₂ ⟨hp₂, hW₂, hZ₂⟩
  refine ⟨hp₂.trans hp₁, es ++ [(r, W ⟨r, by omega⟩ ⟨r, by omega⟩,
    W ⟨r + 1, by omega⟩ ⟨r, by omega⟩)], by simp [hes], ?_, ?_, _, _, ?_, hW₂, hZ₂⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hpl e he
    · rw [List.mem_singleton.mp he]; omega
  · rw [← List.append_assoc]
    exact hfr₂.keep (readsOnly_holdsSlottedLog _ _ _ _ _) hlF hlog₁
  · exact hInv hr es W Z hinv

/-- **The recording loop keeps its invariant**: the $n$ recorded rounds from the invariant before
the first round end in the invariant after the last. -/
private theorem stepLoop_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hCmp : IsCmp id I)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {n : ℕ} (hn : n ≤ nmax)
    {Inv : ℕ → List GivensEntry → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop} (hInv : ∀ r, KeptByRound M Inv r)
    {wv zv cf lg : ℕ × ℕ} {pw qw : ℕ → ℕ × ℕ}
    {ns w : ℕ} {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    {ne : IExp} {ds₁ ds₂ : List IExp} {as₁ as₂ : List Operand}
    (hne : ne.eval ρ.idx = some n)
    (hpw : ∀ r, pw r = (wv.1, wv.2 + 2 * (r * (n + 1) + r)))
    (hqw : ∀ r, qw r = (wv.1, wv.2 + 2 * (r * (n + 1) + r + 1)))
    (hd₁ : ∀ r, IExp.evalList (ρ.pushIdx r).idx ds₁ = some [w, L.length, P.length + r, r])
    (ha₁ : ∀ r, Operand.evalList (ρ.pushIdx r) as₁ = some [pw r, qw r, lg])
    (hd₂ : ∀ r, IExp.evalList (ρ.pushIdx r).idx ds₂ = some [n + 1, r])
    (ha₂ : ∀ r, Operand.evalList (ρ.pushIdx r) as₂ = some [wv, zv, cf, wv, zv])
    (hj : L.length < ns) (hw : P.length + n ≤ w) (hc : cf.2 + 4 ≤ m.store.len cf.1)
    (hwz : Fp.Disj (Store.inBlock wv.1 wv.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock zv.1 zv.2 (2 * ((n + 1) * (n + 1)))))
    (hwc : Fp.Disj (Store.inBlock wv.1 wv.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4))
    (hzc : Fp.Disj (Store.inBlock zv.1 zv.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4))
    (hlw : lg.1 ≠ wv.1)
    (hlF : Fp.Disj (Store.inBlock wv.1 wv.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock zv.1 zv.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4)
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))))
    (hl : m.Live [wv, zv, cf, lg]) (h0 : StepLoopInv Inv wv zv lg ns w L P 0 m.store) :
    Writes .total I τ (.loop ne (.seq (.frame ds₁ as₁ (slottedLogWrite (O := Op) (Q := Tst)))
        (.frame ds₂ as₂ (round (Op := Op) (Tst := Tst))))) ρ
      (Store.inBlock wv.1 wv.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock zv.1 zv.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧ StepLoopInv Inv wv zv lg ns w L P n m'.store) m := by
  refine writes_loop hne (fun _ => _) (fun _ _ => le_rfl)
    (fun r μ => μ.pos = m.pos ∧ StepLoopInv Inv wv zv lg ns w L P r μ.store) ⟨rfl, h0⟩ ?_
  intro r hr μ hfr ⟨hp, h⟩
  refine (logRound_writes hS hCmp hL hNat hr hn (hInv r) (hpw r) (hqw r) (hd₁ r) (ha₁ r)
    (hd₂ r) (ha₂ r) hj hw (by rw [hfr.len_eq]; exact hc) hwz hwc hzc hlw hlF
    (hl.congr hfr.length_eq) h).mono le_rfl ?_
  rintro μ' - ⟨hp', h'⟩
  exact ⟨hp'.trans hp, h'⟩

omit [Has IndexOp Op] [Has CmpTst Tst] in
/-- **The end of the step**: after the recording loop, copying the last working diagonal entry
and zeroing the output below its subdiagonal keep the log and the invariant. -/
private theorem stepTail_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hzero : M.lit 0 = 0) {n : ℕ} {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ}
    {Inv : ℕ → List GivensEntry → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop}
    {wv z dg lg : ℕ × ℕ} {ns w : ℕ} {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    {ds₁ ds₂ : List IExp} {as₁ as₂ : List Operand}
    (hd₁ : IExp.evalList ρ.idx ds₁ = some [n + 1]) (ha₁ : Operand.evalList ρ as₁ = some [wv, dg])
    (hd₂ : IExp.evalList ρ.idx ds₂ = some [n + 1]) (ha₂ : Operand.evalList ρ as₂ = some [z])
    (hl : m.Live [wv, dg, z]) (hd : dg.2 + 2 ≤ m.store.len dg.1)
    (hwd : Fp.Disj (Store.inBlock wv.1 wv.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock dg.1 dg.2 2))
    (hzd : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock dg.1 dg.2 2))
    (hLz : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hLd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) (Store.inBlock dg.1 dg.2 2))
    (h : StepLoopInv Inv wv z lg ns w L P n m.store) :
    Writes .total I τ (.seq (.frame ds₁ as₁ (copyLastDiagonal (Op := Op) (Tst := Tst)))
        (.frame ds₂ as₂ (clearBelowSubdiagonal (Op := Op) (Tst := Tst)))) ρ
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2)
      (fun m' => m'.pos = m.pos ∧ ∃ es : List GivensEntry, es.length = n ∧
        (∀ e ∈ es, e.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w L (P ++ es) m'.store ∧
        ∃ W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Inv n es W Z ∧
          HoldsMatrix z (upperHessenbergPart Z) m'.store ∧
          m'.store.readBlock dg.1 dg.2 2 =
            some [(W (Fin.last n) (Fin.last n)).re, (W (Fin.last n) (Fin.last n)).im]) m := by
  obtain ⟨es, hes, hpl, hlog, W, Z, hinv, hW, hZ⟩ := h
  refine (copyLastDiagonal_writes (τ := τ) hS hW hd hwd).frame_seq_le hd₁ ha₁
    (hl.mono (by simp)) le_sup_right ?_
  rintro m₃ hfr₃ ⟨hp₃, hD₃⟩
  have hl₃ : m₃.Live [z] := (hl.congr hfr₃.length_eq).mono (by simp)
  refine ((clearBelowSubdiagonal_writes (τ := τ) hS hzero (n := n + 1) hl₃
    (hZ.of_eqOff hfr₃ hzd.symm)).in_frame hd₂ ha₂ hl₃).mono le_sup_left ?_
  rintro m₄ hfr₄ ⟨hp₄, hZ₄, -⟩
  exact ⟨hp₄.trans hp₃, es, hes, hpl,
    hfr₄.keep (readsOnly_holdsSlottedLog _ _ _ _ _) hLz.symm
      (hfr₃.keep (readsOnly_holdsSlottedLog _ _ _ _ _) hLd.symm hlog),
    W, Z, hinv, hZ₄, hfr₄.keep (Store.readsOnly_readBlock _ _ _ _) hzd hD₃⟩

/-- The memory of the step: on a scalar machine with exact comparisons and the literal $0$
exact, if a property `Inv` of the rounds (`NLAlib.ShiftedQR.KeptByRound`) holds of the machine
shift (`NLAlib.ShiftedQR.machineShiftedPrefix`) and $\mathbf{H}$, then `stepWithDiag` appends $n$
entries with planes below $n$ to the pending slot of the log, and ends with a working matrix and an
output satisfying `Inv` after $n$ rounds: the output with its fill deleted
(`NLAlib.upperHessenbergPart`) at `z`, the last working diagonal entry at `dg`. -/
theorem stepWithDiag_writes_of_inv {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hzero : M.lit 0 = 0) (hCmp : IsCmp id I)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s z dg lg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} (hn : n ≤ nmax)
    {ns w : ℕ} {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hlog : HoldsSlottedLog lg ns w L P m.store) (hj : L.length < ns) (hw : P.length + n ≤ w)
    (hl : m.Live [a, s, z, dg, lg]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (hd : dg.2 + 2 ≤ m.store.len dg.1)
    (haz : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hsz : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hzd : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock dg.1 dg.2 2))
    (hlgd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 2 ⊔
        Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2))
    {Inv : ℕ → List GivensEntry → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop} (hInv : ∀ r, KeptByRound M Inv r)
    (h0 : Inv 0 [] (machineShiftedPrefix M H shift (n + 1)) H) :
    Writes .total I τ stepWithDiag
      (Env.frame [n + 1, w, L.length, P.length] [a, s, z, dg, lg])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧ ∃ es : List GivensEntry, es.length = n ∧
        (∀ e ∈ es, e.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w L (P ++ es) m'.store ∧
        ∃ W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Inv n es W Z ∧
          HoldsMatrix z (upperHessenbergPart Z) m'.store ∧
          m'.store.readBlock dg.1 dg.2 2 =
            some [(W (Fin.last n) (Fin.last n)).re, (W (Fin.last n) (Fin.last n)).im]) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length ∧ z.1 < m.store.length ∧
      dg.1 < m.store.length ∧ lg.1 < m.store.length := by simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0), .const 4] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [2 * ((n + 1) * (n + 1)), 4]) rfl
    (fun hBelow ⟨hp, es, h1, h2, hlog', W, Z, hI, hZ, hD⟩ => ⟨hp, es, h1, h2,
      hlog'.of_below hBelow hlive.2.2.2.2, W, Z, hI, hZ.of_below hBelow hlive.2.2.1,
      hBelow.readBlock_of hlive.2.2.2.1 hD⟩) ?_
  intro store hlen hlens hBelow
  let wv : ℕ × ℕ := (m.store.length, 0)
  let cf : ℕ × ℕ := (m.store.length + 1, 0)
  have hw' : store.len wv.1 = 2 * ((n + 1) * (n + 1)) := by simpa [wv] using hlens 0 (by simp)
  have hcf : store.len cf.1 = 4 := by simpa [cf] using hlens 1 (by simp)
  set N2 := 2 * ((n + 1) * (n + 1))
  have hne : ∀ {b o k : ℕ} {b' o' k' : ℕ}, b ≠ b' →
      Fp.Disj (Store.inBlock b o k) (Store.inBlock b' o' k') := fun h => Fp.disj_inBlock_of_ne h
  have hwz : Fp.Disj (Store.inBlock wv.1 wv.2 N2) (Store.inBlock z.1 z.2 N2) :=
    hne (by dsimp [wv]; omega)
  have hwc : Fp.Disj (Store.inBlock wv.1 wv.2 N2) (Store.inBlock cf.1 cf.2 4) :=
    hne (by dsimp [wv, cf]; omega)
  have hzc : Fp.Disj (Store.inBlock z.1 z.2 N2) (Store.inBlock cf.1 cf.2 4) :=
    hne (by dsimp [cf]; omega)
  have hLz : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) (Store.inBlock z.1 z.2 N2) :=
    hlgd.mono le_rfl (le_sup_right.trans le_sup_left)
  have hLd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) (Store.inBlock dg.1 dg.2 2) :=
    hlgd.mono le_rfl le_sup_right
  have hlF : Fp.Disj (Store.inBlock wv.1 wv.2 N2 ⊔ Store.inBlock z.1 z.2 N2 ⊔
      Store.inBlock cf.1 cf.2 4) (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hne (by dsimp [wv]; omega), hLz.symm⟩,
      hne (by dsimp [cf]; omega)⟩
  have hinit := initializeState_writes_word (τ := τ) (m := ⟨store, m.pos⟩)
    (a := a) (s := s) (w := wv) (z := z) hS
    (by simp [Mem.Live, wv, hlen]; omega) (hA.of_below hBelow hlive.1)
    ((hBelow.readBlock hlive.2.1 _ _).trans hs)
    (by dsimp [wv]; simpa only [Nat.zero_add] using hw'.ge)
    (by rw [(hBelow z.1 hlive.2.2.1).1]; exact hz) (hne (by dsimp [wv]; omega)) haz
    (hne (by dsimp [wv]; omega)) hsz hwz
  have hZF : Store.inBlock z.1 z.2 N2 ≤ Store.inBlock z.1 z.2 N2 ⊔ Store.inBlock dg.1 dg.2 2 ⊔
      Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) ⊔ Fp.above m.store.length :=
    le_sup_left.trans (le_sup_left.trans le_sup_left)
  refine hinit.frame_seq_le rfl rfl (by simp [Mem.Live, wv, hlen]; omega)
    (sup_le (Fp.inBlock_le_sup_above le_rfl) hZF) ?_
  intro m₁ hfr₁ ⟨hp₁, hW₁, hZ₁⟩
  have hlog₁ := hfr₁.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
    (Fp.disj_sup_left.mpr ⟨hne (by dsimp [wv]; omega), hLz.symm⟩)
    (hlog.of_below hBelow hlive.2.2.2.2)
  have hFl : Store.inBlock wv.1 wv.2 N2 ⊔ Store.inBlock z.1 z.2 N2 ⊔ Store.inBlock cf.1 cf.2 4 ⊔
      Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) ≤ Store.inBlock z.1 z.2 N2 ⊔
        Store.inBlock dg.1 dg.2 2 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) ⊔
          Fp.above m.store.length :=
    sup_le (sup_le (sup_le (Fp.inBlock_le_sup_above le_rfl) hZF)
      (Fp.inBlock_le_sup_above (Nat.le_succ _))) (le_sup_right.trans le_sup_left)
  refine Writes.seq_le (P := fun m' => m'.pos = m₁.pos ∧ StepLoopInv Inv wv z lg
    ns w L P n m'.store) ?_ hFl ?_
  · exact stepLoop_writes (τ := τ) (m := m₁) (wv := wv) (cf := cf) (n := n)
      (pw := fun r => (m.store.length, 2 * (r * (n + 1) + r)))
      (qw := fun r => (m.store.length, 2 * (r * (n + 1) + r + 1))) hS hCmp hL hNat hn hInv
      rfl (fun r => by simp [wv]) (fun r => by simp [wv]) (fun r => rfl) (fun r => rfl)
      (fun r => rfl) (fun r => rfl) hj hw
      (by rw [hfr₁.len_eq]; dsimp [cf]; simpa only [Nat.zero_add] using hcf.ge) hwz hwc hzc
      (by dsimp [wv]; omega) hlF (by simp [Mem.Live, wv, cf, hfr₁.length_eq, hlen]; omega)
      ⟨[], rfl, by simp, by simpa using hlog₁, _, _, h0, hW₁, hZ₁⟩
  rintro m₂ hfr₂ ⟨hp₂, h₂⟩
  refine (stepTail_writes hS hzero rfl rfl rfl rfl
    (by simp [Mem.Live, wv, hfr₂.length_eq, hfr₁.length_eq, hlen]; omega)
    (by rw [hfr₂.len_eq, hfr₁.len_eq, (hBelow dg.1 hlive.2.2.2.1).1]; exact hd)
    (hne (by dsimp [wv]; omega)) hzd hLz hLd h₂).mono
    (sup_le hZF (le_sup_right.trans (le_sup_left.trans le_sup_left))) ?_
  rintro m₃ - ⟨hp₃, h₃⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), h₃⟩


/-- **The rounded single shifted QR step is backward stable by its recorded unitary**
([BanksGarzaVargasSrivastava2022, Lemma 3.5], with the error base $\|\mathbf{H}\|_2 + \lvert
s\rvert$ for the paper's $\|\mathbf{H} - s\|_2$, which rounding does not meet, and the constant
$300(n+1)^2$ for the paper's $32n^{3/2}$): on a machine with the standard model at the unit
roundoff $\boldsymbol{u} \ge 0$ with $(n+1)\boldsymbol{u} \le 1/2500$, from an upper Hessenberg
$\mathbf{H}$ of order $n + 1$ and a shift $s$, the program `stepWithDiag` appends $n$ entries
$e_1, \dots, e_n$ (planes below $n$) to the pending slot of the log and stores an
$\widehat{\mathbf{H}}'$ and the last diagonal entry of an $\widehat{\mathbf{R}}$ such that
$(\widehat{\mathbf{H}}', \widehat{\mathbf{R}})$ is a backward-stable QR step of $(\mathbf{H}, s)$
by the exact unitary `givensLog (n + 1) es` of the entries, with error
$300(n+1)^2\boldsymbol{u}(\|\mathbf{H}\|_2 + \lvert s\rvert)$. The planes are written as exact
naturals (`hNat`, up to $n_{\max} \ge n$). The output matrix is disjoint from the input matrix, the
shift and the diagonal pair; the log from all of them. -/
theorem stepWithDiag_isStableQRStep {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hCmp : IsCmp id I)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s z dg lg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} (hH : IsUpperHessenberg H)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hn : n ≤ nmax)
    {ns w : ℕ} {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hlog : HoldsSlottedLog lg ns w L P m.store) (hj : L.length < ns) (hw : P.length + n ≤ w)
    (hl : m.Live [a, s, z, dg, lg]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (hd : dg.2 + 2 ≤ m.store.len dg.1)
    (haz : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hsz : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hzd : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock dg.1 dg.2 2))
    (hlgd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 2 ⊔
        Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2)) :
    Writes .total I τ stepWithDiag
      (Env.frame [n + 1, w, L.length, P.length] [a, s, z, dg, lg])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧ ∃ es : List GivensEntry, es.length = n ∧
        (∀ e ∈ es, e.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w L (P ++ es) m'.store ∧
        ∃ H' R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          IsStableQRStepBy (givensLog (n + 1) es) (300 * (n + 1) ^ 2 * u * (specNorm H + ‖shift‖))
            H shift H' R ∧
          HoldsMatrix z H' m'.store ∧
          m'.store.readBlock dg.1 dg.2 2 =
            some [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im]) m := by
  refine (stepWithDiag_writes_of_inv hS (by simpa using hM.lit 0) hCmp hL hNat hn hlog hj hw hl hA
    hs hz hd haz hsz hzd hlgd (Inv := fun r es W Z => RoundedSweepInv u r H
      (machineShiftedPrefix M H shift (n + 1)) (givensLog (n + 1) es)ᴴ W Z)
    (fun r hr es W Z h => ?_) ?_).mono le_rfl ?_
  · dsimp only
    rw [conjTranspose_givensLog_concat, ← givensHessenbergStep_eq_givensAt hr]
    exact roundedSweepInv_succ hM hu hnu hr rfl h
  · rw [givensLog_nil, Matrix.conjTranspose_one]
    exact roundedSweepInv_zero (isUpperHessenberg_machineShiftedPrefix hH shift _)
  · rintro m' - ⟨hp, es, hes, hpl, hlog', W, Z, hinv, hZ, hD⟩
    obtain ⟨R, hR, hRl⟩ := hinv.exists_isStableQRStep hu hnu
      (specNorm_machineShiftedPrefix_sub_le hM hu H shift)
    rw [Matrix.conjTranspose_conjTranspose] at hR
    exact ⟨hp, es, hes, hpl, hlog', upperHessenbergPart Z, R, hR, hZ, by rw [hRl]; exact hD⟩

/-- **The rounded single shifted QR step in place is backward stable by its recorded unitary**
([BanksGarzaVargasSrivastava2022, Lemma 3.5], with the error base $\|\mathbf{H}\|_2 + \lvert
s\rvert$ for the paper's $\|\mathbf{H} - s\|_2$ and the constant $300(n+1)^2$ for the paper's
$32n^{3/2}$): `NLAlib.ShiftedQR.stepWithDiag_isStableQRStep` for `stepWithDiagInPlace`, which
replaces an upper Hessenberg $\mathbf{H}$ by the step. The scratch matrix is disjoint from the
matrix, the shift and the diagonal pair; the matrix is disjoint from the pair; the log from all of
them. -/
theorem stepWithDiagInPlace_isStableQRStep {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hCmp : IsCmp id I)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s t dg lg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} (hH : IsUpperHessenberg H)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hn : n ≤ nmax)
    {ns w : ℕ} {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hlog : HoldsSlottedLog lg ns w L P m.store) (hj : L.length < ns) (hw : P.length + n ≤ w)
    (hl : m.Live [a, s, t, dg, lg]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (ht : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hd : dg.2 + 2 ≤ m.store.len dg.1)
    (hat : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hst : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock dg.1 dg.2 2))
    (had : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock dg.1 dg.2 2))
    (hlgd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 2 ⊔
        Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2)) :
    Writes .total I τ stepWithDiagInPlace
      (Env.frame [n + 1, w, L.length, P.length] [a, s, t, a, dg, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧ ∃ es : List GivensEntry, es.length = n ∧
        (∀ e ∈ es, e.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w L (P ++ es) m'.store ∧
        ∃ H' R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          IsStableQRStepBy (givensLog (n + 1) es) (300 * (n + 1) ^ 2 * u * (specNorm H + ‖shift‖))
            H shift H' R ∧
          HoldsMatrix a H' m'.store ∧
          m'.store.readBlock dg.1 dg.2 2 =
            some [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im]) m := by
  have hlen := Store.le_len_of_readBlock hA (by positivity)
  have hstep := stepWithDiag_isStableQRStep (τ := τ) hS hM hu hCmp hL hNat hH hnu hn hlog hj hw
    hl hA hs ht hd hat hst htd hlgd
  refine hstep.frame_seq_le rfl rfl hl
    (sup_le (sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)) le_sup_right) ?_
  intro m₁ hfr ⟨hp, es, hes, hpl, hlog₁, H', R, hR, hT, hD⟩
  have hcopy := copyMatrix_writes (τ := τ) hS hT (by rw [hfr.len_eq]; exact hlen) hat.symm
  refine (hcopy.in_frame rfl rfl ((hl.congr hfr.length_eq).mono (by simp))).mono
    (le_sup_left.trans (le_sup_left.trans le_sup_left)) ?_
  intro m₂ hfr₂ ⟨hp₂, hA₂⟩
  exact ⟨hp₂.trans hp, es, hes, hpl, hfr₂.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
    (hlgd.mono le_rfl (le_sup_left.trans (le_sup_left.trans le_sup_left))).symm hlog₁,
    H', R, hR, hA₂, hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) had hD⟩

end NLAlib.ShiftedQR
