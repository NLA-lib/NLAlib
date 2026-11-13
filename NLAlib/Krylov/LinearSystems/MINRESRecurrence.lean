/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.MINRESLanczos

/-!
# The Paige–Saunders MINRES recurrence

Preconditioned MINRES as a total recursion on a state indexed by the step, with short
recurrences only: one step of the preconditioned Lanczos recurrence (one application of
$\mathbf{A}$ and one of $\mathbf{M}$), the new column of the tridiagonal matrix
$\underline{\mathbf{T}}_k$ rotated by the two previous Givens rotations and a new rotation
clearing its subdiagonal (`NLAlib.givensCoeffs`), the rotated right-hand side, and the
three-term update of the direction $\mathbf{d}_k$ and of the iterate
$\mathbf{x}_{k+1} = \mathbf{x}_k + \tau_k\mathbf{d}_k$. With $\mathbf{M} = \mathbf{I}$ it is
MINRES. The rotations are those of Givens QR of $\underline{\mathbf{T}}_q$
(`NLAlib.givensHessenbergState`), applied one column at a time; for a tridiagonal matrix the
factor $\mathbf{R}$ has three diagonals (`NLAlib.givensHessenbergR_apply_eq_zero_of_add_two_lt`),
which is why three-term updates suffice. Breakdown is a value: after the Lanczos recurrence stops
at the grade every new quantity is zero and the iterate stays put.

The realisation theorem says that for invertible Hermitian $\mathbf{A}$ and positive definite
$\mathbf{M}$ the computed iterate is `NLAlib.pminresIterate`, for every $k$, with no breakdown
hypothesis. Invertibility is needed: for singular $\mathbf{A}$ a pivot $\gamma_k$ of the rotated
tridiagonal matrix can vanish before the grade and the recurrence then fails (the QLP variant of
Choi, Paige and Saunders treats that case, not stated here). The proof shows that the state
after $j$ steps is the state after $j$ steps of Givens QR of the computed
$\underline{\mathbf{T}}_k$ (two old rotations and one new per column, since the column has three
nonzeros), that the directions satisfy $\mathbf{D}_k\mathbf{R}_k = \mathbf{Z}_k$ while the pivots
are nonzero, and then uses the Givens realisation of GMRES
(`NLAlib.gmresIterate_eq_backSubst_givensHessenberg`) on the split system
$\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}$, whose Arnoldi Hessenberg matrix is
$\underline{\mathbf{T}}_k$, for any factor $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$. The
pivots are nonzero up to the grade $\nu$
(`NLAlib.forall_givensHessenbergR_mgsArnoldiHessenberg_ne_zero_iff`); from the grade on the
Lanczos vectors and coefficients vanish, so the directions are zero and the state is frozen, as
is preconditioned MINRES (`NLAlib.pminresIterate_eq_of_krylovGrade_le`).

## Main definitions

* `NLAlib.MINRESState`, `NLAlib.minresStep`, `NLAlib.minresState`.

## Main results

* `Matrix.IsHermitian.minresState_x_eq`: the computed iterates are the PMINRES iterates.
* `Matrix.IsHermitian.minresState_x_eq_gmresIterate`: without a preconditioner, MINRES.
* `Matrix.IsHermitian.norm_minresState_phi_sq`: the residual estimate.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The state of the Paige–Saunders recurrence before step $k$. -/
structure MINRESState (𝕜 n : Type*) where
  /-- The preconditioned Lanczos state before step $k$. -/
  lanczos : PreconditionedLanczosState 𝕜 n
  /-- The cosine of the rotation of step $k - 1$. -/
  c₁ : 𝕜
  /-- The sine of the rotation of step $k - 1$. -/
  s₁ : 𝕜
  /-- The cosine of the rotation of step $k - 2$. -/
  c₂ : 𝕜
  /-- The sine of the rotation of step $k - 2$. -/
  s₂ : 𝕜
  /-- The last entry $\bar{\varphi}_k$ of the rotated right-hand side, the residual estimate. -/
  phi : 𝕜
  /-- The direction $\mathbf{d}_{k-1}$. -/
  d₁ : n → 𝕜
  /-- The direction $\mathbf{d}_{k-2}$. -/
  d₂ : n → 𝕜
  /-- The iterate $\mathbf{x}_k$. -/
  x : n → 𝕜

/-- **One Paige–Saunders step.** With $\alpha_k$, $\beta_k$ from the current Lanczos state and
$\beta_{k+1}$ from the next: rotate the new column $(\beta_k, \alpha_k, \beta_{k+1})$ by the two
previous rotations, $\varepsilon_k = s_{k-2}\beta_k$, $\delta'_k = \bar{c}_{k-2}\beta_k$,
$\delta_k = c_{k-1}\delta'_k + s_{k-1}\alpha_k$, $\bar\gamma_k = -\bar{s}_{k-1}\delta'_k +
\bar{c}_{k-1}\alpha_k$; take $(c_k, s_k)$ = `givensCoeffs` $(\bar\gamma_k, \beta_{k+1})$,
$\gamma_k = c_k\bar\gamma_k + s_k\beta_{k+1}$; then $\tau_k = c_k\bar\varphi_k$,
$\bar\varphi_{k+1} = -\bar{s}_k\bar\varphi_k$,
$\mathbf{d}_k = \gamma_k^{-1}(\mathbf{z}_k - \varepsilon_k\mathbf{d}_{k-2} -
\delta_k\mathbf{d}_{k-1})$
and $\mathbf{x}_{k+1} = \mathbf{x}_k + \tau_k\mathbf{d}_k$. The signs follow `NLAlib.givens`
($\begin{bmatrix} c & s \\ -\bar{s} & \bar{c} \end{bmatrix}$), not the paper's reflections.
[PaigeSaunders1975, §6]; [Greenbaum1997, §2.5, Algorithm 4]. The preconditioned form is
[Greenbaum1997, Chapter 8, Algorithm 4P]. Paige and Saunders, over $\mathbb{R}$ and without a
preconditioner, form the iterate as $\mathbf{x}_k = \mathbf{V}_k\mathbf{L}_k^{-\mathsf{T}}
\mathbf{t}_k$ ((6.8)–(6.9)): the columns of $\mathbf{V}_k\mathbf{L}_k^{-\mathsf{T}}$ are the
directions $\mathbf{d}_k$ here and the entries of $\mathbf{t}_k$ the $\tau_k$. -/
noncomputable def minresStep (A M : Matrix n n 𝕜) (s : MINRESState 𝕜 n) : MINRESState 𝕜 n :=
  let α : 𝕜 := (preconditionedLanczosAlpha A s.lanczos : 𝕜)
  let L' := preconditionedLanczosStep A M s.lanczos
  let β : 𝕜 := (s.lanczos.beta : 𝕜)
  let β' : 𝕜 := (L'.beta : 𝕜)
  let ε := s.s₂ * β
  let δ₀ := star s.c₂ * β
  let δ := s.c₁ * δ₀ + s.s₁ * α
  let γ₀ := -star s.s₁ * δ₀ + star s.c₁ * α
  let c := (givensCoeffs γ₀ β').1
  let sn := (givensCoeffs γ₀ β').2
  let γ := c * γ₀ + sn * β'
  let d := γ⁻¹ • (s.lanczos.z - ε • s.d₂ - δ • s.d₁)
  ⟨L', c, sn, s.c₁, s.s₁, -star sn * s.phi, d, s.d₁, s.x + (c * s.phi) • d⟩

/-- The **Paige–Saunders recurrence** (preconditioned MINRES) from $\mathbf{x}_0$, with
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$: identity rotations, zero directions and
$\bar\varphi_0 = \|\mathbf{r}_0\|_{\mathbf{M}}$. -/
noncomputable def minresState (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) : ℕ → MINRESState 𝕜 n
  | 0 => ⟨preconditionedLanczosState A M (b - A *ᵥ x₀) 0, 1, 0, 1, 0,
      ((Real.sqrt (RCLike.re (quadForm M (b - A *ᵥ x₀))) : ℝ) : 𝕜), 0, 0, x₀⟩
  | k + 1 => minresStep A M (minresState A M b x₀ k)

/-! ### The coefficients of a step -/

section Coefficients

omit [DecidableEq n]

variable (A : Matrix n n 𝕜)

/-- The diagonal coefficient $\alpha_k$ of the current Lanczos state, as a scalar. -/
noncomputable def minresAlpha (s : MINRESState 𝕜 n) : 𝕜 :=
  (preconditionedLanczosAlpha A s.lanczos : 𝕜)

/-- The coefficient $\beta_k$ of the current Lanczos state, as a scalar. -/
noncomputable def minresBeta (s : MINRESState 𝕜 n) : 𝕜 := (s.lanczos.beta : 𝕜)

/-- $\varepsilon_k = s_{k-2}\beta_k$. -/
noncomputable def minresEps (s : MINRESState 𝕜 n) : 𝕜 := s.s₂ * minresBeta s

/-- $\delta'_k = \bar{c}_{k-2}\beta_k$. -/
noncomputable def minresDelta0 (s : MINRESState 𝕜 n) : 𝕜 := star s.c₂ * minresBeta s

/-- $\delta_k = c_{k-1}\delta'_k + s_{k-1}\alpha_k$. -/
noncomputable def minresDelta (s : MINRESState 𝕜 n) : 𝕜 :=
  s.c₁ * minresDelta0 s + s.s₁ * minresAlpha A s

/-- $\bar\gamma_k = -\bar{s}_{k-1}\delta'_k + \bar{c}_{k-1}\alpha_k$. -/
noncomputable def minresGammaBar (s : MINRESState 𝕜 n) : 𝕜 :=
  -star s.s₁ * minresDelta0 s + star s.c₁ * minresAlpha A s

/-- $\gamma_k = c_k\bar\gamma_k + s_k\beta_{k+1}$, from the state $s$ before step $k$ and the
state $s'$ after it. -/
noncomputable def minresGamma (s s' : MINRESState 𝕜 n) : 𝕜 :=
  s'.c₁ * minresGammaBar A s + s'.s₁ * minresBeta s'

variable (M : Matrix n n 𝕜) (s : MINRESState 𝕜 n)

/-- The Lanczos component of a MINRES step is exactly one preconditioned Lanczos step. -/
theorem minresStep_lanczos :
    (minresStep A M s).lanczos = preconditionedLanczosStep A M s.lanczos := rfl

/-- The new cosine is the Givens coefficient of the rotated diagonal and next subdiagonal. -/
theorem minresStep_c₁ :
    (minresStep A M s).c₁ = (givensCoeffs (minresGammaBar A s) (minresBeta (minresStep A M s))).1 :=
  rfl

/-- The new sine is the Givens coefficient of the rotated diagonal and next subdiagonal. -/
theorem minresStep_s₁ :
    (minresStep A M s).s₁ = (givensCoeffs (minresGammaBar A s) (minresBeta (minresStep A M s))).2 :=
  rfl

/-- A MINRES step retains the previous cosine for the next rotation. -/
theorem minresStep_c₂ : (minresStep A M s).c₂ = s.c₁ := rfl

/-- A MINRES step retains the previous sine for the next rotation. -/
theorem minresStep_s₂ : (minresStep A M s).s₂ = s.s₁ := rfl

/-- The MINRES residual estimate follows the new Givens sine. -/
theorem minresStep_phi : (minresStep A M s).phi = -star (minresStep A M s).s₁ * s.phi :=
  rfl

/-- The new MINRES direction is the three-term direction recurrence, with total inverse. -/
theorem minresStep_d₁ : (minresStep A M s).d₁ = (minresGamma A s (minresStep A M s))⁻¹ •
    (s.lanczos.z - minresEps s • s.d₂ - minresDelta A s • s.d₁) := rfl

/-- A MINRES step shifts the previous direction into the second direction slot. -/
theorem minresStep_d₂ : (minresStep A M s).d₂ = s.d₁ := rfl

/-- The MINRES iterate adds the new direction scaled by the rotated right-hand side. -/
theorem minresStep_x :
    (minresStep A M s).x = s.x + ((minresStep A M s).c₁ * s.phi) • (minresStep A M s).d₁ := rfl

end Coefficients

/-! ### The rotated tridiagonal matrix -/

section Rotated

omit [DecidableEq n]

variable (A : Matrix n n 𝕜) (S : ℕ → MINRESState 𝕜 n)

/-- The entries of the tridiagonal matrix, in natural-number indices. -/
private noncomputable def minresTri (a l : ℕ) : 𝕜 :=
  if a = l then minresAlpha A (S l) else if a = l + 1 then minresBeta (S a)
  else if l = a + 1 then minresBeta (S l) else 0

/-- The entries of the three-diagonal factor: column $l$ is $(\varepsilon_l, \delta_l,
\gamma_l)$ in rows $l - 2, l - 1, l$. -/
private noncomputable def minresR (a l : ℕ) : 𝕜 :=
  if a = l then minresGamma A (S l) (S (l + 1)) else if a + 1 = l then minresDelta A (S l)
  else if a + 2 = l then minresEps (S l) else 0

/-- The tridiagonal matrix after $j$ Givens steps: columns $l < j$ are triangularised, column $j$
has been rotated by the two previous rotations, column $j + 1$ by the last one, and the others are
untouched. -/
private noncomputable def minresRot (j a l : ℕ) : 𝕜 :=
  if l < j then minresR A S a l
  else if l = j then
    (if a = l then minresGammaBar A (S l) else if a + 1 = l then minresDelta A (S l)
    else if a + 2 = l then minresEps (S l) else if a = l + 1 then minresBeta (S (l + 1)) else 0)
  else if l = j + 1 then
    (if a = l then minresAlpha A (S l) else if a + 1 = l then minresDelta0 (S l)
    else if a + 2 = l then minresEps (S l) else if a = l + 1 then minresBeta (S (l + 1)) else 0)
  else minresTri A S a l

/-- The rotated right-hand side after $j$ Givens steps: $\tau_a = c_a\bar\varphi_a$ for $a < j$,
then $\bar\varphi_j$. -/
private noncomputable def minresRhs (j a : ℕ) : 𝕜 :=
  if a < j then (S (a + 1)).c₁ * (S a).phi else if a = j then (S j).phi else 0

variable {A} {M : Matrix n n 𝕜} {S}

private theorem minresRot_zero (h0 : (S 0).c₁ = 1 ∧ (S 0).s₁ = 0 ∧ (S 0).lanczos.beta = 0)
    (hS : ∀ l, S (l + 1) = minresStep A M (S l)) (a l : ℕ) :
    minresRot A S 0 a l = minresTri A S a l := by
  have h1 : minresDelta0 (S 1) = minresBeta (S 1) := by
    rw [minresDelta0, hS 0, minresStep_c₂, h0.1, star_one, one_mul]
  have h2 : minresGammaBar A (S 0) = minresAlpha A (S 0) := by
    rw [minresGammaBar, h0.1, h0.2.1, star_zero, star_one, neg_zero, zero_mul, zero_add, one_mul]
  rcases l with _ | _ | l
  · rcases a with _ | _ | a <;> simp [minresRot, minresTri, h2]
  · rcases a with _ | _ | _ | a <;> simp [minresRot, minresTri, h1]
  · simp [minresRot]

private theorem minresRot_succ_left (hS : ∀ l, S (l + 1) = minresStep A M (S l)) (j l : ℕ) :
    (S (j + 1)).c₁ * minresRot A S j j l + (S (j + 1)).s₁ * minresRot A S j (j + 1) l =
      minresRot A S (j + 1) j l := by
  rcases lt_trichotomy l j with h | rfl | h
  · simp (disch := omega) only [minresRot, minresR, if_pos, if_neg, mul_zero, add_zero]
  · simp (disch := omega) only [minresRot, minresR, if_pos, if_neg, ite_true]
    rfl
  · obtain ⟨t, rfl⟩ : ∃ t, l = j + 1 + t := ⟨l - (j + 1), by omega⟩
    rcases t with _ | _ | t
    · simp (disch := omega) only [minresRot, if_pos, if_neg, ite_true]
      rfl
    · have hs : (S (j + 1 + 1)).s₂ = (S (j + 1)).s₁ := by rw [hS (j + 1), minresStep_s₂]
      simp (disch := omega) only [minresRot, minresTri, if_pos, if_neg, ite_true, mul_zero,
        zero_add, minresEps]
      rw [show j + 1 + (0 + 1) = j + 1 + 1 by omega, hs]
    · simp (disch := omega) only [minresRot, minresTri, if_pos, if_neg, mul_zero, add_zero]

private theorem minresRot_succ_right (hS : ∀ l, S (l + 1) = minresStep A M (S l)) (j l : ℕ) :
    -star (S (j + 1)).s₁ * minresRot A S j j l + star (S (j + 1)).c₁ * minresRot A S j (j + 1) l =
      minresRot A S (j + 1) (j + 1) l := by
  rcases lt_trichotomy l j with h | rfl | h
  · simp (disch := omega) only [minresRot, minresR, if_pos, if_neg, mul_zero, add_zero]
  · simp (disch := omega) only [minresRot, minresR, if_pos, if_neg, ite_true]
    rw [hS l, minresStep_c₁, minresStep_s₁]
    exact neg_star_givensCoeffs_snd_mul_add _ _
  · obtain ⟨t, rfl⟩ : ∃ t, l = j + 1 + t := ⟨l - (j + 1), by omega⟩
    rcases t with _ | _ | t
    · simp (disch := omega) only [minresRot, if_pos, if_neg, ite_true]
      rfl
    · have hc : (S (j + 1 + 1)).c₂ = (S (j + 1)).c₁ := by rw [hS (j + 1), minresStep_c₂]
      simp (disch := omega) only [minresRot, minresTri, if_pos, if_neg, ite_true, mul_zero,
        zero_add, minresDelta0]
      rw [show j + 1 + (0 + 1) = j + 1 + 1 by omega, hc]
    · simp (disch := omega) only [minresRot, minresTri, if_pos, if_neg, mul_zero, add_zero]

private theorem minresRot_succ_of_ne {j a : ℕ} (ha : a ≠ j) (ha' : a ≠ j + 1) (l : ℕ) :
    minresRot A S j a l = minresRot A S (j + 1) a l := by
  rcases lt_trichotomy l j with h | rfl | h
  · simp (disch := omega) only [minresRot, if_pos]
  · simp (disch := omega) only [minresRot, minresR, if_pos, if_neg, ite_true]
  · obtain ⟨t, rfl⟩ : ∃ t, l = j + 1 + t := ⟨l - (j + 1), by omega⟩
    rcases t with _ | _ | t
    · simp (disch := omega) only [minresRot, if_pos, if_neg, ite_true]
    · simp only [minresRot, minresTri]
      split_ifs <;> first | omega | rfl | (subst_vars; rfl)
    · simp (disch := omega) only [minresRot, if_pos, if_neg]

omit [Fintype n] in
private theorem minresRhs_succ_of_ne {j a : ℕ} (ha : a ≠ j) (ha' : a ≠ j + 1) :
    minresRhs S j a = minresRhs S (j + 1) a := by
  simp only [minresRhs]
  split_ifs <;> first | omega | rfl

/-- **The rotations are those of Givens QR**: on the computed tridiagonal matrix, the state after
$j \le k$ Givens steps is `minresRot` and the rotated $\bar\varphi_0\mathbf{e}_0$ is `minresRhs`. -/
private theorem givensHessenbergState_eq_minresRot
    (h0 : (S 0).c₁ = 1 ∧ (S 0).s₁ = 0 ∧ (S 0).lanczos.beta = 0)
    (hS : ∀ l, S (l + 1) = minresStep A M (S l)) {k : ℕ} {H : Matrix (Fin (k + 1)) (Fin k) 𝕜}
    (hH : ∀ (a : Fin (k + 1)) (l : Fin k), H a l = minresTri A S a l) {j : ℕ} (hj : j ≤ k) :
    (∀ (a : Fin (k + 1)) (l : Fin k), (givensHessenbergState H j).2 a l = minresRot A S j a l) ∧
      ∀ a : Fin (k + 1),
        (S 0).phi * ((givensHessenbergState H j).1ᴴ *ᵥ Pi.single 0 1) a = minresRhs S j a := by
  induction j with
  | zero =>
    refine ⟨fun a l => (hH a l).trans (minresRot_zero h0 hS a l).symm, fun a => ?_⟩
    simp only [givensHessenbergState, Matrix.conjTranspose_one, Matrix.one_mulVec, minresRhs,
      Pi.single_apply, Fin.ext_iff, Fin.val_zero, Nat.not_lt_zero, if_false, mul_ite, mul_one,
      mul_zero]
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hjk : j < k := by omega
    have hne : (⟨j, by omega⟩ : Fin (k + 1)) ≠ ⟨j + 1, by omega⟩ :=
      Fin.ne_of_val_ne (Nat.succ_ne_self j).symm
    have e1 : minresRot A S j j j = minresGammaBar A (S j) := by simp [minresRot]
    have e2 : minresRot A S j (j + 1) j = minresBeta (S (j + 1)) := by
      simp (disch := omega) only [minresRot, if_pos, if_neg, ite_true]
    have hG : givensHessenbergStep (givensHessenbergState H j).2 j =
        givens ⟨j, by omega⟩ ⟨j + 1, by omega⟩ (S (j + 1)).c₁ (S (j + 1)).s₁ := by
      rw [givensHessenbergStep_of_lt _ (by omega) (by omega) hjk, ih1, ih1]
      dsimp only
      rw [e1, e2, hS j]
      rfl
    refine ⟨fun a l => ?_, fun a => ?_⟩
    · rw [givensHessenbergState_succ_snd, hG]
      rcases (show (a : ℕ) = j ∨ (a : ℕ) = j + 1 ∨ ((a : ℕ) ≠ j ∧ (a : ℕ) ≠ j + 1) by omega) with
        ha | ha | ha
      · rw [show a = ⟨j, by omega⟩ from Fin.ext ha, givens_mul_apply_left hne, ih1, ih1]
        exact minresRot_succ_left hS j l
      · rw [show a = ⟨j + 1, by omega⟩ from Fin.ext ha, givens_mul_apply_right hne, ih1, ih1]
        exact minresRot_succ_right hS j l
      · rw [givens_mul_apply_of_ne (Fin.ne_of_val_ne ha.1) (Fin.ne_of_val_ne ha.2), ih1]
        exact minresRot_succ_of_ne ha.1 ha.2 l
    · rw [conjTranspose_givensHessenbergState_succ_fst_mulVec, hG]
      rcases (show (a : ℕ) = j ∨ (a : ℕ) = j + 1 ∨ ((a : ℕ) ≠ j ∧ (a : ℕ) ≠ j + 1) by omega) with
        ha | ha | ha
      · rw [show a = ⟨j, by omega⟩ from Fin.ext ha, givens_mulVec_apply_left hne, mul_add,
          mul_left_comm, mul_left_comm (S 0).phi, ih2, ih2]
        simp (disch := omega) only [minresRhs, if_pos, if_neg, ite_true, mul_zero, add_zero]
      · rw [show a = ⟨j + 1, by omega⟩ from Fin.ext ha, givens_mulVec_apply_right hne, mul_add,
          mul_left_comm, mul_left_comm (S 0).phi, ih2, ih2]
        simp (disch := omega) only [minresRhs, if_neg, ite_true, mul_zero, add_zero]
        rw [hS j, minresStep_phi]
      · rw [givens_mulVec_apply_of_ne (Fin.ne_of_val_ne ha.1) (Fin.ne_of_val_ne ha.2), ih2]
        exact minresRhs_succ_of_ne ha.1 ha.2

/-- **The directions solve $\mathbf{D}_k\mathbf{R}_k = \mathbf{Z}_k$** when the pivots
$\gamma_l$, $l < k$, are nonzero: $\mathbf{z}_l = \gamma_l\mathbf{d}_l + \delta_l\mathbf{d}_{l-1} +
\varepsilon_l\mathbf{d}_{l-2}$ is the direction update solved for $\mathbf{z}_l$. -/
private theorem minres_z_eq_mul (hS : ∀ l, S (l + 1) = minresStep A M (S l))
    (hd : (S 0).d₁ = 0 ∧ (S 0).d₂ = 0) {k : ℕ}
    (hγ : ∀ l < k, minresGamma A (S l) (S (l + 1)) ≠ 0) :
    (Matrix.of fun i (l : Fin k) => (S l).lanczos.z i) =
      (Matrix.of fun i (a : Fin k) => (S (a + 1)).d₁ i) *
        Matrix.of fun (a l : Fin k) => minresR A S a l := by
  ext i l
  have hz : ∀ l : ℕ, l < k → (S l).lanczos.z = minresGamma A (S l) (S (l + 1)) • (S (l + 1)).d₁ +
      minresEps (S l) • (S l).d₂ + minresDelta A (S l) • (S l).d₁ := by
    intro l hl
    rw [hS l, minresStep_d₁, ← hS l, smul_smul, mul_inv_cancel₀ (hγ l hl), one_smul]
    abel
  rw [Matrix.of_apply, Matrix.mul_apply, hz l l.2]
  simp only [Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun a => (S (a + 1)).d₁ i * minresR A S a l) k]
  obtain ⟨l, hl⟩ := l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hR : ∀ a, minresR A S a l = (if a = l then minresGamma A (S l) (S (l + 1)) else 0) +
      (if a + 1 = l then minresDelta A (S l) else 0) +
        (if a + 2 = l then minresEps (S l) else 0) := by
    intro a
    simp only [minresR]
    split_ifs <;> first | omega | simp
  simp only [hR, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]
  rcases l with _ | _ | l
  · simp [Finset.sum_ite_eq', Finset.mem_range.mpr hl, hd.1, hd.2, mul_comm]
  · have h1 : (S 1).d₂ = 0 := by rw [hS 0, minresStep_d₂, hd.1]
    simp [Finset.sum_ite_eq', Finset.mem_range.mpr hl, h1, mul_comm, show 0 < k by omega]
  · have h2 : (S (l + 2)).d₂ = (S (l + 1)).d₁ := by rw [hS (l + 1), minresStep_d₂]
    simp [Finset.sum_ite_eq', Finset.mem_range.mpr hl, h2, show l + 1 < k by omega,
      show l < k by omega]
    ring

end Rotated

/-! ### The realisation -/

section Realisation

variable {A M : Matrix n n 𝕜}

section Basic

omit [DecidableEq n]

/-- The Lanczos part of the state is the preconditioned Lanczos recurrence from $\mathbf{r}_0$. -/
private theorem minresState_lanczos (b x₀ : n → 𝕜) (k : ℕ) :
    (minresState A M b x₀ k).lanczos = preconditionedLanczosState A M (b - A *ᵥ x₀) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [minresState, minresStep_lanczos, ih]; rfl

/-- The iterate is $\mathbf{x}_0 + \sum_{a < k}\tau_a\mathbf{d}_a$ with $\tau_a =
c_a\bar\varphi_a$. -/
private theorem minresState_x_eq_add_sum (b x₀ : n → 𝕜) (k : ℕ) :
    (minresState A M b x₀ k).x = x₀ + ∑ a ∈ Finset.range k,
      ((minresState A M b x₀ (a + 1)).c₁ * (minresState A M b x₀ a).phi) •
        (minresState A M b x₀ (a + 1)).d₁ := by
  induction k with
  | zero => simp [minresState]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    rfl

/-- The computed tridiagonal matrix in natural-number indices. -/
private theorem preconditionedLanczosTridiagonal_submatrix_apply (b x₀ : n → 𝕜) (k : ℕ)
    (a : Fin (k + 1)) (l : Fin k) :
    (preconditionedLanczosTridiagonal A M (b - A *ᵥ x₀) (k + 1)).submatrix id Fin.castSucc a l =
      minresTri A (minresState A M b x₀) a l := by
  simp only [preconditionedLanczosTridiagonal, Matrix.submatrix_apply, id_eq, Matrix.of_apply,
    Fin.ext_iff, Fin.val_castSucc, minresTri, minresAlpha, minresBeta, minresState_lanczos]
  split_ifs with h
  · rw [h]
  all_goals rfl

/-- The computed basis as a matrix of the Lanczos part of the states. -/
private theorem preconditionedLanczosMatrix_eq_of (b x₀ : n → 𝕜) (k : ℕ) :
    preconditionedLanczosMatrix A M (b - A *ᵥ x₀) k =
      Matrix.of fun i (l : Fin k) => (minresState A M b x₀ l).lanczos.z i := by
  ext i l
  simp only [preconditionedLanczosMatrix, Matrix.of_apply, minresState_lanczos]

end Basic

variable {C : Matrix n n 𝕜}

omit [DecidableEq n] in
/-- The computed tridiagonal matrix is the Arnoldi Hessenberg matrix of the split system. -/
private theorem preconditionedLanczosTridiagonal_submatrix_eq (hA : A.IsHermitian)
    (hMC : M = C * Cᴴ) (r : n → 𝕜) (k : ℕ) :
    (preconditionedLanczosTridiagonal A M r (k + 1)).submatrix id Fin.castSucc =
      mgsArnoldiHessenberg (Cᴴ * A * C) (Cᴴ *ᵥ r) k := by
  classical
  rw [mgsArnoldiHessenberg_eq,
    ← submatrix_conjTranspose_arnoldiMatrix_mul_mul_arnoldiMatrix_castSucc,
    ← hA.preconditionedLanczosTridiagonal_eq hMC]

/-- **Preconditioned MINRES by Givens QR of the computed tridiagonal matrix**, for every $k$. -/
private theorem pminresIterate_eq_backSubst (hA : A.IsHermitian) (hAu : IsUnit A)
    (hC : IsUnit C) (hMC : M = C * Cᴴ) (b x₀ : n → 𝕜) (k : ℕ) :
    pminresIterate A M b x₀ k = x₀ +
      ((Real.sqrt (RCLike.re (quadForm M (b - A *ᵥ x₀))) : ℝ) : 𝕜) •
      (preconditionedLanczosMatrix A M (b - A *ᵥ x₀) k *ᵥ
        backSubst ((givensHessenbergR ((preconditionedLanczosTridiagonal A M (b - A *ᵥ x₀)
            (k + 1)).submatrix id Fin.castSucc)).submatrix Fin.castSucc id)
          (fun i => ((givensHessenbergQ ((preconditionedLanczosTridiagonal A M (b - A *ᵥ x₀)
            (k + 1)).submatrix id Fin.castSucc))ᴴ *ᵥ Pi.single 0 1) i.castSucc)) := by
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, C *ᵥ y₀ = x₀ :=
    ⟨C⁻¹ *ᵥ x₀, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv C
      ((Matrix.isUnit_iff_isUnit_det C).mp hC), Matrix.one_mulVec]⟩
  have hr : Cᴴ *ᵥ b - (Cᴴ * A * C) *ᵥ y₀ = Cᴴ *ᵥ (b - A *ᵥ x₀) := by
    rw [← hy₀]
    exact (Matrix.conjTranspose_mulVec_sub_mulVec_mulVec A C b y₀).symm
  have hÂ : IsUnit (Cᴴ * A * C) := ((isUnit_star.mpr hC : IsUnit Cᴴ).mul hAu).mul hC
  have hn : Real.sqrt (RCLike.re (quadForm M (b - A *ᵥ x₀))) =
      ‖WithLp.toLp 2 (Cᴴ *ᵥ (b - A *ᵥ x₀))‖ := by
    rw [hMC, quadForm_mul_conjTranspose_self, RCLike.ofReal_re, Real.sqrt_sq (norm_nonneg _)]
  rw [pminresIterate_eq_mulVec_gmresIterate hAu hC hMC hy₀,
    gmresIterate_eq_backSubst_givensHessenberg hÂ, hr,
    preconditionedLanczosTridiagonal_submatrix_eq hA hMC, hn,
    hA.preconditionedLanczosMatrix_eq hMC, ← mgsArnoldiMatrix_eq_arnoldiMatrix,
    Matrix.mulVec_add, hy₀, Matrix.mulVec_smul, Matrix.mulVec_mulVec]

/-- **The preconditioned MINRES residual from the rotated right-hand side**, for every $k$. -/
private theorem re_quadForm_sub_mulVec_pminresIterate (hA : A.IsHermitian) (hAu : IsUnit A)
    (hC : IsUnit C) (hMC : M = C * Cᴴ) (b x₀ : n → 𝕜) (k : ℕ) :
    RCLike.re (quadForm M (b - A *ᵥ pminresIterate A M b x₀ k)) =
      (Real.sqrt (RCLike.re (quadForm M (b - A *ᵥ x₀))) *
        ‖((givensHessenbergQ ((preconditionedLanczosTridiagonal A M (b - A *ᵥ x₀)
            (k + 1)).submatrix id Fin.castSucc))ᴴ *ᵥ Pi.single 0 1) (Fin.last k)‖) ^ 2 := by
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, C *ᵥ y₀ = x₀ :=
    ⟨C⁻¹ *ᵥ x₀, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv C
      ((Matrix.isUnit_iff_isUnit_det C).mp hC), Matrix.one_mulVec]⟩
  have hr : Cᴴ *ᵥ b - (Cᴴ * A * C) *ᵥ y₀ = Cᴴ *ᵥ (b - A *ᵥ x₀) := by
    rw [← hy₀]
    exact (Matrix.conjTranspose_mulVec_sub_mulVec_mulVec A C b y₀).symm
  have hÂ : IsUnit (Cᴴ * A * C) := ((isUnit_star.mpr hC : IsUnit Cᴴ).mul hAu).mul hC
  have hq : ∀ v, RCLike.re (quadForm M v) = ‖WithLp.toLp 2 (Cᴴ *ᵥ v)‖ ^ 2 := fun v => by
    rw [hMC, quadForm_mul_conjTranspose_self, RCLike.ofReal_re]
  rw [pminresIterate_eq_mulVec_gmresIterate hAu hC hMC hy₀, hq,
    Matrix.conjTranspose_mulVec_sub_mulVec_mulVec,
    norm_sub_mulVec_gmresIterate_eq_norm_givensHessenbergQ hÂ,
    hr, preconditionedLanczosTridiagonal_submatrix_eq hA hMC, hq, Real.sqrt_sq (norm_nonneg _)]

end Realisation

variable {A M : Matrix n n 𝕜}

/-- Below the grade of the split system the recurrence is preconditioned MINRES. -/
private theorem minresState_x_eq_of_le {C : Matrix n n 𝕜} (hA : A.IsHermitian) (hAu : IsUnit A)
    (hC : IsUnit C) (hMC : M = C * Cᴴ) (b x₀ : n → 𝕜) {k : ℕ}
    (hk : k ≤ krylovGrade (Cᴴ * A * C) (Cᴴ *ᵥ (b - A *ᵥ x₀))) :
    (minresState A M b x₀ k).x = pminresIterate A M b x₀ k := by
  set S := minresState A M b x₀ with hSdef
  set T := (preconditionedLanczosTridiagonal A M (b - A *ᵥ x₀) (k + 1)).submatrix id Fin.castSucc
  have hÂ : IsUnit (Cᴴ * A * C) := ((isUnit_star.mpr hC : IsUnit Cᴴ).mul hAu).mul hC
  have hS : ∀ l, S (l + 1) = minresStep A M (S l) := fun l => rfl
  obtain ⟨inv1, inv2⟩ := givensHessenbergState_eq_minresRot (S := S) ⟨rfl, rfl, rfl⟩ hS
    (preconditionedLanczosTridiagonal_submatrix_apply b x₀ k) (le_refl k)
  have hpiv := (forall_givensHessenbergR_mgsArnoldiHessenberg_ne_zero_iff hÂ _ k).mpr hk
  rw [← preconditionedLanczosTridiagonal_submatrix_eq hA hMC] at hpiv
  have hR : (givensHessenbergR T).submatrix Fin.castSucc id =
      Matrix.of fun a l : Fin k => minresR A S a l := by
    ext a l
    refine (inv1 a.castSucc l).trans ?_
    simp [minresRot, l.2]
  have hγ : ∀ l < k, minresGamma A (S l) (S (l + 1)) ≠ 0 := fun l hl => by
    have h := congrFun (congrFun hR ⟨l, hl⟩) ⟨l, hl⟩
    simp only [Matrix.submatrix_apply, id_eq, Matrix.of_apply, minresR, if_true] at h
    rw [← h]
    exact hpiv ⟨l, hl⟩
  have hU : (Matrix.of fun a l : Fin k => minresR A S a l).IsUpperTriangular := by
    intro a l hla
    have hla' : (l : ℕ) < a := hla
    simp (disch := omega) only [Matrix.of_apply, minresR, if_neg]
  have hdiag : ∀ i : Fin k, (Matrix.of fun a l : Fin k => minresR A S a l) i i ≠ 0 := fun i => by
    simp only [Matrix.of_apply, minresR, if_true]
    exact hγ i i.2
  have hg : ∀ a : Fin k, (S 0).phi *
      ((givensHessenbergQ T)ᴴ *ᵥ Pi.single 0 1) a.castSucc = (S (a + 1)).c₁ * (S a).phi :=
    fun a => (inv2 a.castSucc).trans (by simp [minresRhs, a.2])
  rw [pminresIterate_eq_backSubst hA hAu hC hMC, preconditionedLanczosMatrix_eq_of, ← hSdef, hR,
    minres_z_eq_mul hS ⟨rfl, rfl⟩ hγ, ← Matrix.mulVec_mulVec, mulVec_backSubst hU hdiag,
    minresState_x_eq_add_sum]
  congr 1
  rw [← Matrix.mulVec_smul, Matrix.mulVec_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun a => ((S (a + 1)).c₁ * (S a).phi) • (S (a + 1)).d₁) k]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [op_smul_eq_smul, Pi.smul_apply, smul_eq_mul]
  erw [hg a]
  rfl

/-- **The Paige–Saunders iterates are the preconditioned MINRES iterates**: for invertible
Hermitian $\mathbf{A}$, positive definite $\mathbf{M}$ and every $k$, with no breakdown
hypothesis, $\mathbf{x}_k = \mathsf{pminresIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b},
\mathbf{x}_0, k)$. [PaigeSaunders1975, §6]; there without a preconditioner ($\mathbf{M} =
\mathbf{I}$), over $\mathbb{R}$ and up to termination: the iterate (6.9) of the recurrence solves
the minimum residual problem (2.7) in the Lanczos basis.
Result: minres-recurrence -/
theorem _root_.Matrix.IsHermitian.minresState_x_eq (hA : A.IsHermitian) (hAu : IsUnit A)
    (hM : M.PosDef) (b x₀ : n → 𝕜) (k : ℕ) :
    (minresState A M b x₀ k).x = pminresIterate A M b x₀ k := by
  obtain ⟨C, hC, hMC⟩ := hM.exists_isUnit_eq_mul_conjTranspose
  set ν := krylovGrade (Cᴴ * A * C) (Cᴴ *ᵥ (b - A *ᵥ x₀)) with hν
  rcases le_or_gt k ν with hk | hk
  · exact minresState_x_eq_of_le hA hAu hC hMC b x₀ hk
  have hfreeze : ∀ l, ν ≤ l → (minresState A M b x₀ (l + 1)).x = (minresState A M b x₀ l).x := by
    intro l hl
    have hz := hA.preconditionedLanczosState_z_eq_zero_of_le hMC (b - A *ᵥ x₀) hl
    have hβ := hA.preconditionedLanczosState_beta_eq_zero_of_le hMC (b - A *ᵥ x₀) hl
    have hd : (minresState A M b x₀ (l + 1)).d₁ = 0 := by
      rw [show minresState A M b x₀ (l + 1) = minresStep A M (minresState A M b x₀ l) from rfl,
        minresStep_d₁, minresEps, minresDelta, minresDelta0, minresAlpha, minresBeta,
        minresState_lanczos, hz, hβ, preconditionedLanczosAlpha, hz]
      simp
    rw [show (minresState A M b x₀ (l + 1)).x = (minresState A M b x₀ l).x +
      ((minresState A M b x₀ (l + 1)).c₁ * (minresState A M b x₀ l).phi) •
        (minresState A M b x₀ (l + 1)).d₁ from rfl, hd, smul_zero, add_zero]
  have hxk : ∀ l, ν ≤ l → (minresState A M b x₀ l).x = (minresState A M b x₀ ν).x := by
    intro l hl
    induction l, hl using Nat.le_induction with
    | base => rfl
    | succ l hl ih => rw [hfreeze l hl, ih]
  have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hAu
  have hxs : A *ᵥ (A⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  have hg : krylovGrade (M * A) (M *ᵥ (b - A *ᵥ x₀)) =
      krylovGrade (Cᴴ * A * C) (Cᴴ *ᵥ (b - A *ᵥ x₀)) := by
    rw [hMC, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, krylovGrade_mul_mulVec hC]
  rw [hxk k hk.le, minresState_x_eq_of_le hA hAu hC hMC b x₀ le_rfl,
    pminresIterate_eq_of_krylovGrade_le hAu hM hxs x₀ (hg.trans_le hk.le),
    pminresIterate_eq_of_krylovGrade_le hAu hM hxs x₀ hg.le]

/-- **MINRES without a preconditioner**: for invertible Hermitian $\mathbf{A}$ and every $k$ the
recurrence with $\mathbf{M} = \mathbf{I}$ computes `gmresIterate`:
$\mathbf{x}_k = \mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, k)$.
[PaigeSaunders1975, §6]; there over $\mathbb{R}$ and up to termination, the iterate (6.9) of the
recurrence solving the minimum residual problem (2.7).
Result: minres-recurrence -/
theorem _root_.Matrix.IsHermitian.minresState_x_eq_gmresIterate (hA : A.IsHermitian)
    (hAu : IsUnit A) (b x₀ : n → 𝕜) (k : ℕ) :
    (minresState A 1 b x₀ k).x = gmresIterate A b x₀ k := by
  rw [hA.minresState_x_eq hAu Matrix.PosDef.one, pminresIterate_one]

/-- **The residual estimate**: for invertible Hermitian $\mathbf{A}$, positive definite
$\mathbf{M}$ and every $k$, the recurrence's $\bar\varphi_k$ and iterate $\mathbf{x}_k$ satisfy
$\lvert\bar\varphi_k\rvert^2 = \|\mathbf{b} - \mathbf{A}\mathbf{x}_k\|_{\mathbf{M}}^2$, available
without forming the residual. [PaigeSaunders1975, (7.4)]; there without a preconditioner, as
$\|\mathbf{r}_k\| = \beta_1\lvert s_1 \cdots s_k \rvert$, the product of the rotation sines
that $\lvert\bar\varphi_k\rvert$ is here (the paper indexes from $1$).
Result: minres-residual-estimate -/
theorem _root_.Matrix.IsHermitian.norm_minresState_phi_sq (hA : A.IsHermitian) (hAu : IsUnit A)
    (hM : M.PosDef) (b x₀ : n → 𝕜) (k : ℕ) :
    ‖(minresState A M b x₀ k).phi‖ ^ 2 =
      RCLike.re (quadForm M (b - A *ᵥ (minresState A M b x₀ k).x)) := by
  obtain ⟨C, hC, hMC⟩ := hM.exists_isUnit_eq_mul_conjTranspose
  obtain ⟨-, inv2⟩ := givensHessenbergState_eq_minresRot (S := minresState A M b x₀)
    ⟨rfl, rfl, rfl⟩ (fun l => rfl) (preconditionedLanczosTridiagonal_submatrix_apply b x₀ k)
    (le_refl k)
  have h := inv2 (Fin.last k)
  simp only [Fin.val_last, minresRhs, lt_irrefl, if_false, if_true] at h
  have h0 : ‖(minresState A M b x₀ 0).phi‖ = Real.sqrt (RCLike.re (quadForm M (b - A *ᵥ x₀))) := by
    rw [show (minresState A M b x₀ 0).phi =
        ((Real.sqrt (RCLike.re (quadForm M (b - A *ᵥ x₀))) : ℝ) : 𝕜) from rfl,
      RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [hA.minresState_x_eq hAu hM, re_quadForm_sub_mulVec_pminresIterate hA hAu hC hMC, ← h,
    norm_mul, h0]
  rfl

end NLAlib
