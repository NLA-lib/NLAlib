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
  `NLAlib.ShiftedQR.multiStepStable`: the programs.

## Main results

* `NLAlib.ShiftedQR.stepWithDiag_writes_of_sweep`: the memory of the step, from any proved
  sweep.
* `NLAlib.ShiftedQR.stepWithDiag_isStableQRStep`,
  `NLAlib.ShiftedQR.stepWithDiagInPlace_isStableQRStep`: one rounded step is a backward-stable
  step.
* `NLAlib.ShiftedQR.multiStepStable_isStableQRChain`: the degree $k$ step is a stable chain.

Termination on any matrix is in `NLAlib.Eigensolvers.ShiftedQR.StableStepTermination`.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- **One shifted QR step with its last triangular diagonal entry and a Hessenberg output**:
initialize a working copy $\mathbf{H} - s$ and the output $\mathbf{H}$, run the Givens sweep that
also copies the last working diagonal entry to `Dg`, and zero the output below its subdiagonal.
The interface is `[n] (A, S) → (Z, Dg)`; the working matrix and the four coefficient words are
scoped. -/
def stepWithDiag : Impl Op Tst := opsImpl% [n] (A, S) → (Z, Dg) {
  let W ← alloc (2 * (n * n));
  let Cf ← alloc 4;
  run (initializeState (Op := Op) (Tst := Tst)).body [n] (A, S, W, Z);
  run (sweepWithDiag (Op := Op) (Tst := Tst)).body [n] (W, Z, Cf, W, Z, Dg);
  run (clearBelowSubdiagonal (Op := Op) (Tst := Tst)).body [n] (Z)
}

/-- The step in place: run `NLAlib.ShiftedQR.stepWithDiag` into the scratch matrix `T`, then copy
it back to `A`. The interface is `[n] (A, S, T) → (A, Dg)`. -/
def stepWithDiagInPlace : Impl Op Tst := opsImpl% [n] (A, S, T) → (A, Dg) {
  run (stepWithDiag (Op := Op) (Tst := Tst)).body [n] (A, S, T, Dg);
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (n * n)] (T, A)
}

/-- **The degree $k$ rounded step**: $k$ steps in place with the shifts `S[2j]`, the last
triangular diagonal entry of step $j$ written to `Ds[2j]`. The interface is
`[n, k] (A, S) → (A, Ds)`; the scratch matrix is scoped. -/
def multiStepStable : Impl Op Tst := opsImpl% [n, k] (A, S) → (A, Ds) {
  let T ← alloc (2 * (n * n));
  for j < k {
    run (stepWithDiagInPlace (Op := Op) (Tst := Tst)).body [n] (A, S[2 * j], T, A, Ds[2 * j])
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
private def RoundedSweepInv (u : ℝ) (k : ℕ) (H W₀ W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Prop :=
  ∃ P J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols P ∧
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
    {H W₀ W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {cv sv : ℂ}
    (hcs : roundedGivensCoeffs M (W ⟨k, by omega⟩ ⟨k, by omega⟩)
      (W ⟨k + 1, by omega⟩ ⟨k, by omega⟩) = (cv, sv))
    (h : RoundedSweepInv u k H W₀ W Z) :
    RoundedSweepInv u (k + 1) H W₀
      (machineRowRotation M ⟨k, by omega⟩ ⟨k + 1, by omega⟩ cv sv W)
      (machineColRotation M ⟨k, by omega⟩ ⟨k + 1, by omega⟩ cv sv
        (machineRowRotation M ⟨k, by omega⟩ ⟨k + 1, by omega⟩ cv sv Z)) := by
  obtain ⟨P, J, hP, hP1, hP2, ha, hb, hc, hEW, hJ, hEZ⟩ := h
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
  exact ⟨_, _, (hasOrthonormalCols_givensHessenbergStep W k).mul hP, hQ1, hQ2, ha', hb', hc',
    n1, n2, n3⟩

/-- Before the first round: the factor is the identity and there are no residuals. -/
private theorem roundedSweepInv_zero {u : ℝ} {H W₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hW : IsUpperHessenberg W₀) : RoundedSweepInv u 0 H W₀ W₀ H := by
  refine ⟨1, 0, hasOrthonormalCols_one, fun a b hab => Matrix.one_apply_ne ?_,
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
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) {H W₀ W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s : ℂ}
    (h : RoundedSweepInv u n H W₀ W Z)
    (hW₀ : specNorm (W₀ - (H - s • (1 : Matrix _ _ ℂ))) ≤ u * (specNorm H + ‖s‖)) :
    ∃ R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsStableQRStep (300 * (n + 1) ^ 2 * u * (specNorm H + ‖s‖)) H s (upperHessenbergPart Z) R ∧
        R (Fin.last n) (Fin.last n) = W (Fin.last n) (Fin.last n) := by
  obtain ⟨P, J, hP, hP1, -, ha, hb, -, hEW, hJ, hEZ⟩ := h
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
  refine ⟨W - J, isStableQRStep_upperHessenbergPart hP.conjTranspose (fun i j hij => ?_)
    (fun i t hti => ?_) hD hE hb1 hb2, ?_⟩
  · rw [Matrix.conjTranspose_apply, hP1 j i hij, star_zero]
  · have hti' : (t : ℕ) < i := hti
    rw [Matrix.sub_apply, hb i t (by omega) hti', sub_self]
  · rw [Matrix.sub_apply, ha (Fin.last n) (Fin.last n) (by simp), sub_zero]

end SweepMath

/-- **The rounded sweep keeps its invariant**: on a machine with the standard model at
$\boldsymbol{u} \ge 0$ with $(n+1)\boldsymbol{u} \le 1/2500$, the $n$ rounds of the sweep from an
upper Hessenberg working matrix $\mathbf{W}_0$ and an output $\mathbf{H}$ end in the invariant of
$n$ rounds. -/
private theorem sweep_writes_roundedSweepInv {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {w z cf : ℕ × ℕ}
    {H W₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hW₀ : IsUpperHessenberg W₀) (hW : HoldsMatrix w W₀ m.store) (hH : HoldsMatrix z H m.store)
    (hc : cf.2 + 4 ≤ m.store.len cf.1)
    (hwz : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hwc : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4))
    (hzc : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4))
    (hl : m.Live [w, z, cf, w, z]) :
    Writes .total I τ sweep.body (Env.frame [n + 1] [w, z, cf, w, z])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4)
      (fun m' => m'.pos = m.pos ∧ ∃ W Z, RoundedSweepInv u n H W₀ W Z ∧
        HoldsMatrix w W m'.store ∧ HoldsMatrix z Z m'.store) m := by
  unfold sweep
  refine writes_loop (N := n) rfl (fun _ => _) (fun _ _ => le_rfl)
    (fun k m' => m'.pos = m.pos ∧ ∃ W Z, RoundedSweepInv u k H W₀ W Z ∧
      HoldsMatrix w W m'.store ∧ HoldsMatrix z Z m'.store)
    ⟨rfl, W₀, H, roundedSweepInv_zero hW₀, hW, hH⟩ ?_
  intro k hk m' hfr ⟨hp, W, Z, hinv, hW', hZ'⟩
  have hround := round_writes_word (τ := τ) (m := m') (n := n + 1) (k := k) hS hCmp
    (by omega)
    (cv := (roundedGivensCoeffs M (W ⟨k, by omega⟩ ⟨k, by omega⟩)
      (W ⟨k + 1, by omega⟩ ⟨k, by omega⟩)).1)
    (sv := (roundedGivensCoeffs M (W ⟨k, by omega⟩ ⟨k, by omega⟩)
      (W ⟨k + 1, by omega⟩ ⟨k, by omega⟩)).2) rfl hW' hZ'
    (by rw [hfr.len_eq]; exact hc) hwz hwc hzc
  refine (hround.in_frame rfl rfl (hl.congr hfr.length_eq)).mono le_rfl ?_
  intro m'' _ ⟨hp', hW'', hZ''⟩
  exact ⟨hp'.trans hp, _, _, roundedSweepInv_succ hM hu hnu hk rfl hinv, hW'', hZ''⟩

/-- The memory of the step with its diagonal entry: initialization stores the machine shift
(`NLAlib.ShiftedQR.machineShiftedPrefix`) in a fresh working matrix and the raw matrix in the
output; if every run of the sweep from such a state ends with a working matrix and an output
related by `P`, the step ends with such a pair, the output with its fill deleted
(`NLAlib.upperHessenbergPart`) and the last working diagonal entry stored. The working matrix
and the coefficient words are scoped; the output and the diagonal pair are given capacity. -/
theorem stepWithDiag_writes_of_sweep {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hzero : M.lit 0 = 0) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ}
    {a s z dg : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop}
    (hl : m.Live [a, s, z, dg]) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (hd : dg.2 + 2 ≤ m.store.len dg.1)
    (haz : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hsz : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hzd : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock dg.1 dg.2 2))
    (hsweep : ∀ (m₁ : Mem ℝ) (w cf : ℕ × ℕ),
      HoldsMatrix w (machineShiftedPrefix M H shift (n + 1)) m₁.store →
      HoldsMatrix z H m₁.store → cf.2 + 4 ≤ m₁.store.len cf.1 →
      Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))) →
      Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock cf.1 cf.2 4) →
      Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock cf.1 cf.2 4) →
      m₁.Live [w, z, cf, w, z] →
      Writes .total I τ sweep.body (Env.frame [n + 1] [w, z, cf, w, z])
        (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4)
        (fun m' => m'.pos = m₁.pos ∧ ∃ W Z, P W Z ∧
          HoldsMatrix w W m'.store ∧ HoldsMatrix z Z m'.store) m₁) :
    Writes .total I τ stepWithDiag.body (Env.frame [n + 1] [a, s, z, dg])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2)
      (fun m' => m'.pos = m.pos ∧ ∃ W Z, P W Z ∧
        HoldsMatrix z (upperHessenbergPart Z) m'.store ∧
        m'.store.readBlock dg.1 dg.2 2 =
          some [(W (Fin.last n) (Fin.last n)).re, (W (Fin.last n) (Fin.last n)).im]) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length ∧ z.1 < m.store.length ∧
      dg.1 < m.store.length := by simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0), .const 4] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [2 * ((n + 1) * (n + 1)), 4]) rfl
    (fun hBelow ⟨hp, W, Z, hP, hZ, hD⟩ => ⟨hp, W, Z, hP, hZ.of_below hBelow hlive.2.2.1,
      hBelow.readBlock_of hlive.2.2.2 hD⟩) ?_
  intro store hlen hlens hBelow
  let w : ℕ × ℕ := (m.store.length, 0)
  let cf : ℕ × ℕ := (m.store.length + 1, 0)
  have hw : store.len w.1 = 2 * ((n + 1) * (n + 1)) := by
    simpa [w] using hlens 0 (by simp)
  have hcf : store.len cf.1 = 4 := by
    simpa [cf] using hlens 1 (by simp)
  have haw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_inBlock_of_ne (by dsimp [w]; omega)
  have hsw : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_inBlock_of_ne (by dsimp [w]; omega)
  have hwz : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_inBlock_of_ne (by dsimp [w]; omega)
  have hwc : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4) :=
    Fp.disj_inBlock_of_ne (by dsimp [w, cf]; omega)
  have hzc : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4) :=
    Fp.disj_inBlock_of_ne (by dsimp [cf]; omega)
  have hfd : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4)
      (Store.inBlock dg.1 dg.2 2) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (by dsimp [w]; omega), hzd⟩,
      Fp.disj_inBlock_of_ne (by dsimp [cf]; omega)⟩
  have hinit := initializeState_writes_word (τ := τ) (m := ⟨store, m.pos⟩)
    (a := a) (s := s) (w := w) (z := z) hS
    (by simp [Mem.Live, w, hlen]; omega) (hH.of_below hBelow hlive.1)
    ((hBelow.readBlock hlive.2.1 _ _).trans hs)
    (by dsimp [w]; simpa only [Nat.zero_add] using hw.ge)
    (by rw [(hBelow z.1 hlive.2.2.1).1]; exact hz) haw haz hsw hsz hwz
  refine hinit.frame_seq_le rfl rfl
    (by simp [Mem.Live, w, hlen]; omega)
    (sup_le (Fp.inBlock_le_sup_above le_rfl) (le_sup_left.trans le_sup_left)) ?_
  intro m₁ hfr₁ ⟨hp₁, hW₁, hZ₁⟩
  have hl₁ : m₁.Live [w, z, cf, w, z, dg] := by
    simp [Mem.Live, w, cf, hfr₁.length_eq, hlen]; omega
  have hsweep₁ := sweepWithDiag_writes_of_sweep (P := P) hS hl₁
    (by rw [hfr₁.len_eq, (hBelow dg.1 hlive.2.2.2).1]; exact hd) hfd
    (hsweep m₁ w cf hW₁ hZ₁
      (by rw [hfr₁.len_eq]; dsimp [cf]; simpa only [Nat.zero_add] using hcf.ge)
      hwz hwc hzc (hl₁.mono (by simp)))
  refine hsweep₁.frame_seq_le rfl rfl hl₁
    (sup_le (sup_le (sup_le (Fp.inBlock_le_sup_above le_rfl)
      (le_sup_left.trans le_sup_left)) (Fp.inBlock_le_sup_above (by dsimp [cf]; omega)))
      (le_sup_right.trans le_sup_left)) ?_
  intro m₂ hfr₂ ⟨hp₂, W, Z, hP, _, hZ₂, hD₂⟩
  have hclear := clearBelowSubdiagonal_writes (τ := τ) hS hzero (n := n + 1) (a := z)
    (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq, hlen]; omega) hZ₂
    (by rw [hfr₂.len_eq, hfr₁.len_eq, (hBelow z.1 hlive.2.2.1).1]; exact hz)
  refine (hclear.in_frame rfl rfl
    (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq, hlen]; omega)).mono
    (le_sup_left.trans le_sup_left) ?_
  intro m₃ hfr₃ ⟨hp₃, hZ₃, _⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), W, Z, hP, hZ₃,
    hfr₃.keep (Store.readsOnly_readBlock _ _ _ _) hzd hD₂⟩

/-- **The rounded single shifted QR step is backward stable**
([BanksGarzaVargasSrivastava2022, Lemma 3.5], with the error base $\|\mathbf{H}\|_2 + \lvert
s\rvert$ for the paper's $\|\mathbf{H} - s\|_2$, which rounding does not meet, and the constant
$300(n+1)^2$ for the paper's $32n^{3/2}$): on a machine with the standard model at the unit
roundoff $\boldsymbol{u} \ge 0$ with $(n+1)\boldsymbol{u} \le 1/2500$, from an upper Hessenberg
$\mathbf{H}$ of order $n + 1$ and a shift $s$, the program `stepWithDiag` stores an
$\widehat{\mathbf{H}}'$ and the last diagonal entry of an $\widehat{\mathbf{R}}$ such that
$(\widehat{\mathbf{H}}', \widehat{\mathbf{R}})$ is a backward-stable QR step of $(\mathbf{H}, s)$
with error $300(n+1)^2\boldsymbol{u}(\|\mathbf{H}\|_2 + \lvert s\rvert)$. The input, the shift and
the outputs are given views; the output matrix is disjoint from the input matrix, the shift and
the diagonal pair. -/
theorem stepWithDiag_isStableQRStep {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s z dg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} (hH : IsUpperHessenberg H)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hl : m.Live [a, s, z, dg]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (hd : dg.2 + 2 ≤ m.store.len dg.1)
    (haz : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hsz : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hzd : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock dg.1 dg.2 2)) :
    Writes .total I τ stepWithDiag.body (Env.frame [n + 1] [a, s, z, dg])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2)
      (fun m' => m'.pos = m.pos ∧ ∃ H' R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsStableQRStep (300 * (n + 1) ^ 2 * u * (specNorm H + ‖shift‖)) H shift H' R ∧
          HoldsMatrix z H' m'.store ∧
          m'.store.readBlock dg.1 dg.2 2 =
            some [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im]) m := by
  have hzero : M.lit 0 = 0 := by simpa using hM.lit 0
  refine (stepWithDiag_writes_of_sweep
    (P := fun W Z => RoundedSweepInv u n H (machineShiftedPrefix M H shift (n + 1)) W Z)
    hS hzero hl hA hs hz hd haz hsz hzd fun m₁ w cf hW hZ hc hwz hwc hzc hl₁ =>
      sweep_writes_roundedSweepInv hS hM hu hCmp hnu
        (isUpperHessenberg_machineShiftedPrefix hH shift _) hW hZ hc hwz hwc hzc hl₁).mono
    le_rfl ?_
  intro m' _ ⟨hp, W, Z, hinv, hZ', hD⟩
  obtain ⟨R, hR, hRl⟩ := hinv.exists_isStableQRStep hu hnu
    (specNorm_machineShiftedPrefix_sub_le hM hu H shift)
  exact ⟨hp, upperHessenbergPart Z, R, hR, hZ', by rw [hRl]; exact hD⟩

/-- **The rounded single shifted QR step in place is backward stable**
([BanksGarzaVargasSrivastava2022, Lemma 3.5], with the error base $\|\mathbf{H}\|_2 + \lvert
s\rvert$ for the paper's $\|\mathbf{H} - s\|_2$ and the constant $300(n+1)^2$ for the paper's
$32n^{3/2}$): on a machine with the standard model at $\boldsymbol{u} \ge 0$ with
$(n+1)\boldsymbol{u} \le 1/2500$, `stepWithDiagInPlace` replaces an upper Hessenberg $\mathbf{H}$
by a backward-stable step with error $300(n+1)^2\boldsymbol{u}(\|\mathbf{H}\|_2 + \lvert s\rvert)$
and stores the last diagonal entry of its triangular factor. The scratch matrix is disjoint from
the matrix, the shift and the diagonal pair; the matrix is disjoint from the diagonal pair. -/
theorem stepWithDiagInPlace_isStableQRStep {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s t dg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} (hH : IsUpperHessenberg H)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hl : m.Live [a, s, t, dg]) (hA : HoldsMatrix a H m.store)
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
      (Store.inBlock dg.1 dg.2 2)) :
    Writes .total I τ stepWithDiagInPlace.body (Env.frame [n + 1] [a, s, t, a, dg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2)
      (fun m' => m'.pos = m.pos ∧ ∃ H' R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsStableQRStep (300 * (n + 1) ^ 2 * u * (specNorm H + ‖shift‖)) H shift H' R ∧
          HoldsMatrix a H' m'.store ∧
          m'.store.readBlock dg.1 dg.2 2 =
            some [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im]) m := by
  have hlen := Store.le_len_of_readBlock hA (by positivity)
  have hstep := stepWithDiag_isStableQRStep (τ := τ) hS hM hu hCmp hH hnu hl hA hs ht hd hat hst
    htd
  refine hstep.frame_seq_le rfl rfl hl (sup_le (le_sup_right.trans le_sup_left) le_sup_right) ?_
  intro m₁ hfr ⟨hp, H', R, hR, hT, hD⟩
  have hcopy := copyMatrix_writes (τ := τ) hS hT (by rw [hfr.len_eq]; exact hlen) hat.symm
  refine (hcopy.in_frame rfl rfl ((hl.congr hfr.length_eq).mono (by simp))).mono
    (le_sup_left.trans le_sup_left) ?_
  intro m₂ hfr₂ ⟨hp₂, hA₂⟩
  exact ⟨hp₂.trans hp, H', R, hR, hA₂, hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) had hD⟩

/-- The words of entry `j` of a list of complex numbers stored as interleaved pairs. -/
private theorem take_drop_flatMap_pair (ss : List ℂ) {j : ℕ} (hj : j < ss.length) :
    ((ss.flatMap fun z => [z.re, z.im]).drop (2 * j)).take 2 = [ss[j].re, ss[j].im] := by
  induction ss generalizing j with
  | nil => simp at hj
  | cons z zs ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [List.flatMap_cons, show 2 * (j + 1) = 2 + 2 * j by ring, ← List.drop_drop]
      simpa using ih (by simpa using hj)

/-- **The degree $k$ rounded step is a stable chain** (the setting of
[BanksGarzaVargasSrivastava2022, Lemma 3.6]): on a machine with the standard model at
$\boldsymbol{u} \ge 0$ with $(n+1)\boldsymbol{u} \le 1/2500$, from an upper Hessenberg
$\mathbf{H}$ of order $n + 1$ and the shifts $s_1, \dots, s_k$ stored as $2k$ words, the program
`multiStepStable` stores in place an $\widehat{\mathbf{H}}'$, and in `Ds` the last diagonal entries
of triangular factors $\widehat{\mathbf{R}}_1, \dots, \widehat{\mathbf{R}}_k$, such that the steps
form a backward-stable chain with relative error $x = 300(n+1)^2\boldsymbol{u}$ (step $\ell$ has
error $x(\|\mathbf{H}_\ell\|_2 + \lvert s_\ell\rvert)$ at its own input). The matrix, the shifts
and the diagonal outputs are pairwise disjoint views. -/
theorem multiStepStable_isStableQRChain {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s ds : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} (hH : IsUpperHessenberg H)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hl : m.Live [a, s, ds]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 (2 * ss.length) =
      some (ss.flatMap fun z => [z.re, z.im]))
    (hd : ds.2 + 2 * ss.length ≤ m.store.len ds.1)
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * ss.length)))
    (had : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * ss.length)))
    (hsd : Fp.Disj (Store.inBlock s.1 s.2 (2 * ss.length))
      (Store.inBlock ds.1 ds.2 (2 * ss.length))) :
    Writes .total I τ multiStepStable.body (Env.frame [n + 1, ss.length] [a, s, a, ds])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock ds.1 ds.2 (2 * ss.length))
      (fun m' => m'.pos = m.pos ∧ ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
        IsStableQRChain (300 * (n + 1) ^ 2 * u) H ss H' Rs ∧ IsUpperHessenberg H' ∧
          HoldsMatrix a H' m'.store ∧
          m'.store.readBlock ds.1 ds.2 (2 * ss.length) =
            some (Rs.flatMap fun R =>
              [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im])) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length ∧ ds.1 < m.store.length := by
    simpa [Mem.Live] using hl
  -- the post of the loop is kept by the release of the scratch matrix
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0)] _) _ _ _ m
  refine writes_allocs_preserving_post rfl
    (fun hBelow ⟨hp, H', Rs, hc, hH', hA', hD'⟩ => ⟨hp, H', Rs, hc, hH',
      hA'.of_below hBelow hlive.1, hBelow.readBlock_of hlive.2.2 hD'⟩) ?_
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : store.len t.1 = 2 * ((n + 1) * (n + 1)) := by
    simpa [t] using hlens 0 (by simp)
  have hta : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * ss.length)) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * ss.length)) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  set F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock ds.1 ds.2 (2 * ss.length)
  have hFs : Fp.Disj F (Store.inBlock s.1 s.2 (2 * ss.length)) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨has, hts⟩, hsd.symm⟩
  have hl₀ : (⟨store, m.pos⟩ : Mem ℝ).Live [a, s, a, ds, t] := by
    simp [Mem.Live, t, hlen]; omega
  refine (writes_loop (m := ⟨store, m.pos⟩) (n := .var 1) (N := ss.length) rfl (fun _ => F)
    (fun _ _ => le_rfl)
    (fun j μ => μ.pos = m.pos ∧ ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
      IsStableQRChain (300 * (n + 1) ^ 2 * u) H (ss.take j) H' Rs ∧ IsUpperHessenberg H' ∧
        HoldsMatrix a H' μ.store ∧
        μ.store.readBlock ds.1 ds.2 (2 * j) = some (Rs.flatMap fun R =>
          [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im]))
    ⟨rfl, H, [], by simpa using IsStableQRChain.nil (x := 300 * (n + 1) ^ 2 * u) H, hH,
      hA.of_below hBelow hlive.1, by simp⟩ ?_).mono
    (sup_le (sup_le (le_sup_left.trans le_sup_left) (Fp.inBlock_le_sup_above le_rfl))
      (le_sup_right.trans le_sup_left)) ?_
  · intro j hj μ hfr ⟨hp, Hj, Rs, hc, hHj, hAj, hDj⟩
    have hsμ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) hFs
      ((hBelow.readBlock hlive.2.1 _ _).trans hs)
    have hsj : μ.store.readBlock s.1 (s.2 + 2 * j) 2 = some [ss[j].re, ss[j].im] := by
      rw [Store.readBlock_sub hsμ (by omega), take_drop_flatMap_pair ss hj]
    have hdlen : ds.2 + 2 * ss.length ≤ μ.store.len ds.1 := by
      rw [hfr.len_eq, (hBelow ds.1 hlive.2.2).1]; exact hd
    have hdg : Store.inBlock ds.1 (ds.2 + 2 * j) 2 ≤ Store.inBlock ds.1 ds.2 (2 * ss.length) :=
      fun b i hi => ⟨hi.1, by have := hi.2.1; omega, by have := hi.2.2; omega⟩
    have hpre : Store.inBlock ds.1 ds.2 (2 * j) ≤ Store.inBlock ds.1 ds.2 (2 * ss.length) :=
      fun b i hi => ⟨hi.1, hi.2.1, by have := hi.2.2; omega⟩
    have hlμ : μ.Live [a, (s.1, s.2 + 2 * j), t, a, (ds.1, ds.2 + 2 * j)] := by
      simp [Mem.Live, hfr.length_eq, t, hlen]; omega
    have hstep := stepWithDiagInPlace_isStableQRStep (τ := τ) (m := μ) (t := t)
      (s := (s.1, s.2 + 2 * j)) (dg := (ds.1, ds.2 + 2 * j)) hS hM hu hCmp hHj hnu
      (hlμ.mono (by simp)) hAj hsj
      (by rw [hfr.len_eq]; dsimp [t]; simpa only [Nat.zero_add] using ht.ge)
      (by dsimp only; omega)
      hta.symm (Fp.disj_inBlock_of_ne (by dsimp [t]; omega))
      (htd.mono le_rfl hdg) (had.mono le_rfl hdg)
    refine (hstep.in_frame rfl rfl hlμ).mono
      (sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left))
        (hdg.trans le_sup_right)) ?_
    intro μ' hfr' ⟨hp', H', R, hR, hA', hD'⟩
    have hDj' := hfr'.keep (Store.readsOnly_readBlock _ _ _ _)
      (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨had.mono le_rfl hpre,
        htd.mono le_rfl hpre⟩, (Fp.disj_inBlock_of_le le_rfl).symm⟩) hDj
    refine ⟨hp'.trans hp, H', Rs ++ [R], ?_, hR.1, hA', ?_⟩
    · rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      exact hc.snoc hR
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring, List.flatMap_append]
      exact Store.readBlock_add hDj' hD'
  · intro μ _ ⟨hp, H', Rs, hc, hH', hA', hD'⟩
    exact ⟨hp, H', Rs, by simpa using hc, hH', hA', hD'⟩

end NLAlib.ShiftedQR
