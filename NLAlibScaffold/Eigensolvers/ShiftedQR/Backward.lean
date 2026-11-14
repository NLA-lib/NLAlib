/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.DecoupleState
public import NLAlib.Eigensolvers.ShiftedQR.DeflationProgram
public import NLAlib.Eigensolvers.ShiftedQR.Step
public import NLAlib.Matrix.FinitePrecision.OpsUnitarySimilarity
public import NLAlibScaffold.Matrix.FinitePrecision.GivensRounded

/-!
# Backward-error contracts of shifted QR

The exact shifted QR program returns exact unitary similarities: `IterationContract` and
`DecouplingContract` end with $\mathbf{H}' = \mathbf{U}^{\mathsf H}\mathbf{H}\mathbf{U}$. In
floating point each layer returns a **perturbed** unitary similarity
(`NLAlib.IsPerturbedUnitarySimilar`) whose backward error is relative to a norm bound of its
input. This file states the weakened contracts, the bridges from the exact contracts (backward
error $0$, [BanksGarzaVargasSrivastava2022, Definition 3.4] at $\boldsymbol{u} = 0$), the rounded
single shifted QR step of the existing program as a perturbed similarity
([BanksGarzaVargasSrivastava2022, Lemma 3.5], with the error $O(n\boldsymbol{u})$ of a sweep
analysed round by round), and the deflation worklist driven by a backward decoupling
implementation (the backward half of [BanksGarzaVargasSrivastava2022, Theorem 6.3]).

The worklist and its program are the exact development's, unchanged: only the contract of the
decoupling implementation it is given is weaker. The final perturbation is the sum of the
discarded couplings and of the backward errors of the decoupling calls.

## Main definitions

* `NLAlib.ShiftedQR.BackwardIterationContract`, `NLAlib.ShiftedQR.BackwardDecouplingContract`.

## Main results

* `NLAlib.ShiftedQR.IterationContract.backward`, `NLAlib.ShiftedQR.DecouplingContract.backward`:
  exact contracts are backward contracts with error $0$.
* `NLAlib.ShiftedQR.isRoundedRowRotation_machineRowRotation`,
  `NLAlib.ShiftedQR.isRoundedColRotation_machineColRotation`: the rotations the program computes
  from rounded coefficients are rounded Givens rotations.
* `NLAlib.ShiftedQR.isPerturbedUnitarySimilar_machineColRotation`: one rounded round is a
  perturbed unitary similarity with error $49\boldsymbol{u}\|\mathbf{Z}\|_2$.
* `NLAlib.ShiftedQR.shiftedStep_isPerturbedUnitarySimilar`: the rounded single step.
* `NLAlib.ShiftedQR.solve_backward`: the worklist with a backward decoupling implementation.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type}

/-- The backward contract of one shift-strategy iteration with the relative backward error `ν`:
from a Hessenberg matrix of norm at most `N`, the stored result is upper Hessenberg and a
perturbed unitary similarity of the input with backward error $\nu N$. Optimality of the Ritz
values and the acceptance test are not part of the backward contract (they are the convergence
half). -/
def BackwardIterationContract (ν : ℝ) (Iter : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n m M : ℕ} {τ B θ α γ N : ℝ} {w p c : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    IsUpperHessenberg H → specNorm H ≤ N → 2 ^ m ≤ n → 0 ≤ τ → 0 ≤ B →
    M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊ → 0 < M →
    HoldsMatrix w H μ.store → μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ] →
    μ.store.readBlock c.1 c.2 2 = some [τ ^ 2, (1 - γ) ^ (2 * (2 ^ m))] →
    μ.Live [w, p, c, w] → w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock p.1 p.2 5 ⊔ Store.inBlock c.1 c.2 2) →
    Writes .total I tape Iter.body (Env.frame [n + 1, m, 2 ^ m, M] [w, p, c, w])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsPerturbedUnitarySimilar H H' (ν * N) ∧ IsUpperHessenberg H' ∧
          HoldsMatrix w H' μ'.store) μ

/-- The backward contract of a decoupling implementation with the backward error `ε N` for
inputs of norm at most `N`: as `NLAlib.ShiftedQR.DecouplingContract`, with the exact unitary
similarity replaced by a perturbed one. -/
def BackwardDecouplingContract (θ : ℝ) (ε : ℝ → ℝ) (D : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n m F M : ℕ} {τ B α γ δ N : ℝ} {w p r : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    IsUpperHessenberg H → specNorm H ≤ N → RapidDecouplingHyps H τ B θ α γ δ m F → 2 ^ m ≤ n →
    0 ≤ τ → M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊ → 0 < M →
    HoldsMatrix w H μ.store → μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ] →
    μ.Live [w, p, w, r] → w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 →
    r.2 + 5 ≤ μ.store.len r.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock r.1 r.2 5) →
    Fp.Disj (Store.inBlock p.1 p.2 5)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5) →
    Writes .total I tape D.body (Env.frame [n + 1, m, 2 ^ m, F, M] [w, p, w, r])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5)
      (fun μ' => μ'.pos = μ.pos ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsPerturbedUnitarySimilar H H' (ε N) ∧
          IsUpperHessenberg H' ∧ IsDecoupledAbs τ H' ∧
          HoldsMatrix w H' μ'.store ∧ ScanHolds H' (τ ^ 2) n r μ'.store) μ

/-- An exact iteration contract is a backward iteration contract with backward error $0$
(`NLAlib.ShiftedQR.shqrAcceptStep` is a unitary similarity of its input). -/
theorem IterationContract.backward {θ : ℝ} {Iter : Impl O Q} {I : Interp O Q ℝ}
    (h : IterationContract θ Iter I) : BackwardIterationContract 0 Iter I := by
  sorry

/-- An exact decoupling contract is a backward decoupling contract with backward error $0$. -/
theorem DecouplingContract.backward {θ : ℝ} {D : Impl O Q} {I : Interp O Q ℝ}
    (h : DecouplingContract θ D I) : BackwardDecouplingContract θ (fun _ => 0) D I := by
  intro n m F M τ B α γ δ N w p r tape μ H hH _ hyp hk hτ hM hM0 hW hP hl hw hr hd₁ hd₂
  refine (h H hH hyp hk hτ hM hM0 hW hP hl hw hr hd₁ hd₂).mono le_rfl ?_
  rintro μ' _ ⟨hpos, U, H', hU, rfl, hHess, hdec, hW', hR'⟩
  exact ⟨hpos, _, hU.isPerturbedUnitarySimilar H, hHess, hdec, hW', hR'⟩

section MachineRound

variable {M : Machine ℝ} {u : ℝ} {n : ℕ} {i j : Fin n}

/-- The coefficients the program computes are the rounded Givens coefficients. -/
theorem coefficientWords_eq_roundedGivensCoeffs (M : Machine ℝ) (p q : ℂ) :
    coefficientWords M p q = roundedGivensCoeffs M p q := rfl

/-- **The machine row rotation is a rounded rotation**: on a machine with the standard model at
$0 \le \boldsymbol{u} \le 1/100$, rotating the rows $i \ne j$ of $\mathbf{Z}$ by the coefficients
computed from $(p, q)$ is within $12\boldsymbol{u}$, per column pair, of the exact Givens rotation
of $(p, q)$. [Higham2002, Lemma 19.8]. -/
theorem isRoundedRowRotation_machineRowRotation (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu' : u ≤ 1 / 100) (hij : i ≠ j) (p q : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    IsRoundedRowRotation (12 * u) i j (givensCoeffs p q).1 (givensCoeffs p q).2 Z
      (machineRowRotation M i j (coefficientWords M p q).1 (coefficientWords M p q).2 Z) := by
  obtain ⟨h1, h2⟩ := hM.norm_roundedGivensCoeffs_sub_le hu hu' p q
  rw [← coefficientWords_eq_roundedGivensCoeffs] at h1 h2
  refine ⟨fun r k hri hrj => machineRowRotation_apply_of_ne hri hrj k, fun k => ?_⟩
  have hneg (r : ℝ) : M.neg r = -r := hM.neg r
  set c := (coefficientWords M p q).1
  set s := (coefficientWords M p q).2
  have e1 : (⟨M.neg s.re, s.im⟩ : ℂ) = -star s := by apply Complex.ext <;> simp [hneg]
  have e2 : (⟨c.re, M.neg c.im⟩ : ℂ) = star c := by apply Complex.ext <;> simp [hneg]
  rw [machineRowRotation_apply_left, machineRowRotation_apply_right hij,
    givens_mul_apply_left hij, givens_mul_apply_right hij, e1, e2]
  exact hM.norm_linearWords_rotation_sub_le hu hu' (norm_givensCoeffs_fst_sq_add p q) h1 h2 _ _

/-- **The machine column rotation is a rounded rotation**: on a machine with the standard model
at $0 \le \boldsymbol{u} \le 1/100$, rotating the columns $i \ne j$ of $\mathbf{Z}$ by the
adjoint of the rotation of the coefficients computed from $(p, q)$ is within $12\boldsymbol{u}$,
per row pair, of the adjoint of the exact Givens rotation of $(p, q)$. [Higham2002, Lemma 19.8]. -/
theorem isRoundedColRotation_machineColRotation (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu' : u ≤ 1 / 100) (hij : i ≠ j) (p q : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    IsRoundedColRotation (12 * u) i j (givensCoeffs p q).1 (givensCoeffs p q).2 Z
      (machineColRotation M i j (coefficientWords M p q).1 (coefficientWords M p q).2 Z) := by
  obtain ⟨h1, h2⟩ := hM.norm_roundedGivensCoeffs_sub_le hu hu' p q
  rw [← coefficientWords_eq_roundedGivensCoeffs] at h1 h2
  refine ⟨fun r k hki hkj => machineColRotation_apply_of_ne hki hkj r, fun r => ?_⟩
  have hneg (r : ℝ) : M.neg r = -r := hM.neg r
  set c := (coefficientWords M p q).1
  set s := (coefficientWords M p q).2
  set c₀ := (givensCoeffs p q).1
  set s₀ := (givensCoeffs p q).2
  have e1 : (⟨c.re, M.neg c.im⟩ : ℂ) = star c := by apply Complex.ext <;> simp [hneg]
  have e2 : (⟨s.re, M.neg s.im⟩ : ℂ) = star s := by apply Complex.ext <;> simp [hneg]
  have e3 : (⟨M.neg s.re, M.neg s.im⟩ : ℂ) = -s := by apply Complex.ext <;> simp [hneg]
  have g1 : (Z * (givens i j c₀ s₀)ᴴ) r i = star c₀ * Z r i + star s₀ * Z r j := by
    rw [conjTranspose_givens, mul_givens_apply_left hij]
    simp only [star_neg]
    ring
  have g2 : (Z * (givens i j c₀ s₀)ᴴ) r j = -s₀ * Z r i + c₀ * Z r j := by
    rw [conjTranspose_givens, mul_givens_apply_right hij, star_star]
    ring
  rw [machineColRotation_apply_left, machineColRotation_apply_right hij, g1, g2, e1, e2, e3]
  have h := hM.norm_linearWords_rotation_sub_le hu hu'
    (a := star c) (b := star s) (α := star c₀) (β := star s₀)
    (by rw [norm_star, norm_star]; exact norm_givensCoeffs_fst_sq_add p q)
    (by rw [← star_sub, norm_star, norm_star]; exact h1)
    (by rw [← star_sub, norm_star, norm_star]; exact h2) (Z r i) (Z r j)
  simp only [star_star] at h
  exact h

/-- **One rounded round of the shifted QR sweep is a perturbed unitary similarity**: on a machine
with the standard model at $0 \le \boldsymbol{u} \le 1/576$, rotating the rows $i \ne j$ of
$\mathbf{Z}$ and then its columns by the coefficients computed from $(p, q)$ gives
$\mathbf{G}(\mathbf{Z} + \mathbf{E})\mathbf{G}^{\mathsf{H}}$ for the exact Givens rotation
$\mathbf{G}$ of $(p, q)$, with $\|\mathbf{E}\|_2 \le 49\boldsymbol{u}\|\mathbf{Z}\|_2$: each
rotation contributes $24\boldsymbol{u}$ (`NLAlib.IsRoundedRowRotation.specNorm_sub_le`), the
second one relative to the rotated matrix. [Higham2002, Lemma 19.8]. -/
theorem isPerturbedUnitarySimilar_machineColRotation (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu' : u ≤ 1 / 576) (hij : i ≠ j) (p q : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    IsPerturbedUnitarySimilar Z
      (machineColRotation M i j (coefficientWords M p q).1 (coefficientWords M p q).2
        (machineRowRotation M i j (coefficientWords M p q).1 (coefficientWords M p q).2 Z))
      (49 * u * specNorm Z) := by
  have hu100 : u ≤ 1 / 100 := by linarith
  set G := givens i j (givensCoeffs p q).1 (givensCoeffs p q).2
  have hG : HasOrthonormalCols G :=
    hasOrthonormalCols_givens hij (norm_givensCoeffs_fst_sq_add p q)
  set Z₁ := machineRowRotation M i j (coefficientWords M p q).1 (coefficientWords M p q).2 Z
  set Z₂ := machineColRotation M i j (coefficientWords M p q).1 (coefficientWords M p q).2 Z₁
  have h1 := (isRoundedRowRotation_machineRowRotation hM hu hu100 hij p q Z).specNorm_sub_le
    (by positivity)
  have h2 := (isRoundedColRotation_machineColRotation hM hu hu100 hij p q Z₁).specNorm_sub_le
    (by positivity)
  have hZ₁ : specNorm Z₁ ≤ (1 + 24 * u) * specNorm Z := by
    have e : Z₁ = G * Z + (Z₁ - G * Z) := by abel
    have := specNorm_add_le (G * Z) (Z₁ - G * Z)
    rw [← e, hG.specNorm_mul_left] at this
    linarith
  refine IsPerturbedUnitarySimilar.of_specNorm_sub_le hG.conjTranspose ?_
  rw [Matrix.conjTranspose_conjTranspose]
  have e : Z₂ - G * Z * Gᴴ = (Z₂ - Z₁ * Gᴴ) + (Z₁ - G * Z) * Gᴴ := by
    rw [Matrix.sub_mul]
    abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [hG.specNorm_mul_conjTranspose_right]
  have hZ : 0 ≤ specNorm Z := specNorm_nonneg Z
  nlinarith [mul_le_mul_of_nonneg_left hZ₁ (by positivity : (0 : ℝ) ≤ 2 * (12 * u)),
    mul_nonneg (mul_nonneg hu hZ) (by linarith : (0 : ℝ) ≤ 1 - 576 * u)]

end MachineRound

/-- The geometric growth of $N$ rounds of relative backward error $49\boldsymbol{u}$ is at most
$50 N \boldsymbol{u}$ when $(N + 1)\boldsymbol{u} \le 1/2500$. -/
private theorem one_add_pow_sub_one_le {u : ℝ} {N : ℕ} (hu : 0 ≤ u)
    (hNu : (N + 1 : ℝ) * u ≤ 1 / 2500) : (1 + 49 * u) ^ N - 1 ≤ 50 * N * u := by
  have hN : (N : ℝ) * u ≤ 1 / 2500 := by nlinarith
  have hx : 49 * u ≤ 1 := by nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hu]
  have hB : 1 + N * (-(49 * u)) ≤ (1 + -(49 * u)) ^ N := one_add_mul_le_pow (by linarith) N
  have hAB : (1 + 49 * u) ^ N * (1 + -(49 * u)) ^ N ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hA : 0 ≤ (1 + 49 * u) ^ N := by positivity
  have h1 : (1 + 49 * u) ^ N * (1 - 49 * (N * u)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hB hA
    nlinarith
  have hpos : 0 < 1 - 49 * (N * u) := by linarith
  have h2 : 1 ≤ (1 + 50 * (N * u)) * (1 - 49 * (N * u)) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hu]
  have h3 : (1 + 49 * u) ^ N ≤ 1 + 50 * (N * u) :=
    le_of_mul_le_mul_right (h1.trans h2) hpos
  linarith

variable [Has ScalarOp O] [Has CmpTst Q]

/-- The state between two rounds of the rounded sweep: the position, the live views, the
coefficient arena, some working matrix, and the output matrix `Z`. -/
private def SweepState {n : ℕ} (p : ℕ) (w z cf : ℕ × ℕ) (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (m : Mem ℝ) : Prop :=
  m.pos = p ∧ m.Live [w, z, cf, w, z] ∧ cf.2 + 4 ≤ m.store.len cf.1 ∧
    (∃ W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w W m.store) ∧
    HoldsMatrix z Z m.store

/-- One round of the sweep on a machine with the standard model is a backward step for the
perturbed unitary similarity of the output, with the relative error $49\boldsymbol{u}$. -/
private theorem round_backwardStep {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 576)
    (hCmp : IsCmp id I) {τ : Tape ℝ} {n k : ℕ} (hk : k < n) {p : ℕ} {w z cf : ℕ × ℕ}
    (hwz : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hwc : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4))
    (hzc : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4)) (B : ℝ) :
    BackwardStep .total I τ
      (.frame [.var 0, .var 6]
        [⟨0, .var 1⟩, ⟨1, .var 2⟩, ⟨2, .var 3⟩, ⟨3, .var 4⟩, ⟨4, .var 5⟩] round.body)
      ((Env.frame [n + 1] [w, z, cf, w, z]).pushIdx k)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4)
      (fun ε A B => IsPerturbedUnitarySimilar A B ε)
      (fun (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) m => SweepState p w z cf Z m ∧ specNorm Z ≤ B)
      (SweepState (n := n) p w z cf)
      (49 * u * B) := by
  rintro Z m ⟨⟨hp, hl, hc, ⟨W, hW⟩, hZ⟩, hZB⟩
  have hij : (⟨k, by omega⟩ : Fin (n + 1)) ≠ ⟨k + 1, by omega⟩ :=
    Fin.ne_of_val_ne (Nat.succ_ne_self k).symm
  have hround := round_writes_word (τ := τ) (m := m) (k := k) hS hCmp (by omega)
    (cv := (coefficientWords M (W ⟨k, by omega⟩ ⟨k, by omega⟩)
      (W ⟨k + 1, by omega⟩ ⟨k, by omega⟩)).1)
    (sv := (coefficientWords M (W ⟨k, by omega⟩ ⟨k, by omega⟩)
      (W ⟨k + 1, by omega⟩ ⟨k, by omega⟩)).2) rfl hW hZ hc hwz hwc hzc
  refine (hround.in_frame rfl rfl hl).mono le_rfl fun m' hfr ⟨hp', hW', hZ'⟩ =>
    ⟨_, ?_, hp'.trans hp, hl.congr hfr.length_eq, by rw [hfr.len_eq]; exact hc, ⟨_, hW'⟩, hZ'⟩
  exact (isPerturbedUnitarySimilar_machineColRotation hM hu hu' hij _ _ Z).mono
    (mul_le_mul_of_nonneg_left hZB (by positivity))

/-- **The rounded sweep is a perturbed unitary similarity of the output**: on a machine with the
standard model at $0 \le \boldsymbol{u} \le 1/576$, the $n$ rounds of the sweep of an
$(n+1)\times(n+1)$ output $\mathbf{H}$ end with a perturbed unitary similarity of $\mathbf{H}$
with backward error $((1 + 49\boldsymbol{u})^n - 1)\|\mathbf{H}\|_2$, whatever the working
matrix. The rounds compose by `NLAlib.Ops.BackwardStep.loop_rel`. -/
private theorem sweep_writes_isPerturbedUnitarySimilar {M : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 576)
    (hCmp : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {w z cf : ℕ × ℕ}
    {W H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hW : HoldsMatrix w W m.store) (hH : HoldsMatrix z H m.store)
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
      (fun m' => m'.pos = m.pos ∧ ∃ H', IsPerturbedUnitarySimilar H H'
        ((1 + 49 * u) ^ n * specNorm H - specNorm H) ∧ HoldsMatrix z H' m'.store) m := by
  have hloop := BackwardStep.loop_rel (md := .total) (I := I) (τ := τ)
    (body := .frame [.var 0, .var 6]
      [⟨0, .var 1⟩, ⟨1, .var 2⟩, ⟨2, .var 3⟩, ⟨3, .var 4⟩, ⟨4, .var 5⟩] round.body)
    isBackwardErrorRel_isPerturbedUnitarySimilar (n := .var 0 - .const 1) (N := n) rfl
    (fun _ => SweepState (n := n) m.pos w z cf) specNorm (fun h => h.specNorm_le) (49 * u)
    (specNorm H)
    fun k hk B => round_backwardStep hS hM hu hu' hCmp hk hwz hwc hzc B
  exact (hloop H m ⟨⟨rfl, hl, hc, ⟨W, hW⟩, hH⟩, le_rfl⟩).mono le_rfl
    fun _ _ ⟨H', hR, ⟨hp, _, _, _, hZ⟩, _⟩ => ⟨hp, H', hR, hZ⟩

/-- **The rounded single shifted QR step is backward stable** ([BanksGarzaVargasSrivastava2022,
Lemma 3.5], for the conjugating implementation): the existing scalar program `shiftedStep`, run on
a machine with the standard model at the unit roundoff $\boldsymbol{u}$ with
$(n + 1)\boldsymbol{u} \le 1/2500$, returns a perturbed unitary similarity of its input with
backward error $50(n + 1)\boldsymbol{u}\|\mathbf{H}\|_2$, for every shift. Each round rotates two
rows and two columns with rounded coefficients
(`NLAlib.IsRoundedRowRotation.specNorm_sub_le`, $49\boldsymbol{u}\|\mathbf{Z}\|_2$ per round); the
rounds compose by `NLAlib.Ops.BackwardStep.loop_rel`. The bound is $O(n)$, not the paper's
$32n^{3/2}$; it is relative to $\|\mathbf{H}\|_2$ because this implementation conjugates
$\mathbf{H}$ itself. The output is upper Hessenberg up to the rounding of entries that cancel in
exact arithmetic; the finite-precision program zeroes them (design note). -/
theorem shiftedStep_isPerturbedUnitarySimilar {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s z : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hl : m.Live [a, s, z]) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (haz : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hsz : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I τ shiftedStep.body (Env.frame [n + 1] [a, s, z])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (fun m' => m'.pos = m.pos ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsPerturbedUnitarySimilar H H' (50 * (n + 1) * u * specNorm H) ∧
          HoldsMatrix z H' m'.store) m := by
  have hu' : u ≤ 1 / 576 := by nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hu]
  have hgrow : (1 + 49 * u) ^ n * specNorm H - specNorm H ≤ 50 * (n + 1) * u * specNorm H := by
    have h := mul_le_mul_of_nonneg_right (one_add_pow_sub_one_le hu hnu) (specNorm_nonneg H)
    nlinarith [mul_nonneg hu (specNorm_nonneg H)]
  refine shiftedStep_writes_of_sweep hS hl hH hs hz haz hsz
    fun m₁ w cf hW hZ hc hwz hwc hzc hl₁ => ?_
  exact (sweep_writes_isPerturbedUnitarySimilar hS hM hu hu' hCmp hW hZ hc hwz hwc hzc
    hl₁).mono le_rfl fun _ _ ⟨hp, H', hR, hZ'⟩ => ⟨hp, H', hR.mono hgrow, hZ'⟩

variable [Has IndexOp O] [Has EigenvalueKernelOp O] [Has IdxTst Q]

/-- **Backward error of the deflation worklist with a backward decoupling implementation** (the
backward half of [BanksGarzaVargasSrivastava2022, Theorem 6.3]): the exact development's program
`solve D`, with `D` meeting the backward decoupling contract with a monotone error `ε`, returns
all roots of $\mathbf{H} + \mathbf{E}$ with
$\|\mathbf{E}\|_2 \le n(\delta\|\mathbf{H}\|_{\mathsf F} + \varepsilon(2\|\mathbf{H}\|_2))$,
provided that this total stays within the exact development's perturbation budget (the
conditioning and norm hypotheses of `NLAlib.ShiftedQRHyps`, with the backward errors added). The
scalar arithmetic of the worklist itself (the threshold, the scans) is exact here; its rounding is
the subject of the finite-precision program. -/
theorem solve_backward {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I)
    (hQ : IsToNat id I) (hC : IsCmp id I)
    {θ : ℝ} {K : KernelRoutines θ} (hK : IsEigenvalueKernels K I)
    (D : Impl O Q) {ε : ℝ → ℝ} (hεm : Monotone ε) (hε0 : ∀ N, 0 ≤ ε N)
    (hD : BackwardDecouplingContract θ ε D I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m F M : ℕ} {a raw out : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {B α γ δ g : ℝ}
    (hl : μ.Live [a, raw, out])
    (hr : μ.Room [a, raw, out] [2 * ((n + 1) * (n + 1)), 5, 2 * (n + 1)])
    (ha : Fp.Apart [a, raw, out] [2 * ((n + 1) * (n + 1)), 5, 2 * (n + 1)])
    (hHess : IsUpperHessenberg H) (hA : HoldsMatrix a H μ.store)
    (hGlobal : ShiftedQRHyps H B θ α γ δ g m F)
    (hεg : (n : ℝ) * (δ * frobNorm H + ε (2 * specNorm H)) ≤ g / (8 * (n + 1) * B))
    (hεn : (n : ℝ) * (δ * frobNorm H + ε (2 * specNorm H)) ≤ specNorm H)
    (hM : M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hRaw : μ.store.readBlock raw.1 raw.2 5 = some [B, θ, α, γ, δ]) :
    Writes .total I tape (solve D).body
      (Env.frame [n + 1, m, 2 ^ m, F, M] [a, raw, out])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)))
      (fun μ' => μ'.pos = μ.pos ∧
        ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
          HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
          specNorm E ≤ (n : ℝ) * (δ * frobNorm H + ε (2 * specNorm H)) ∧
          (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)) μ := by
  sorry

end NLAlib.ShiftedQR
