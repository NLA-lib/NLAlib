/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CG

/-!
# The Hestenes–Stiefel recurrence

The conjugate gradient algorithm of Hestenes and Stiefel as a total recursion on a state indexed
by the step: iterate $\mathbf{x}_k$, residual $\mathbf{r}_k$, search direction $\mathbf{p}_k$.
Breakdown is a value: with $0^{-1} = 0$ a zero residual makes both step sizes zero, and the state
stays at the solution.

The realisation theorem says that for positive definite $\mathbf{A}$ the computed iterates are
the conjugate gradient iterates `NLAlib.cgIterate` from the same start, for every $k$ and with no
breakdown
hypothesis. Its proof needs only that $\mathbf{x}_k - \mathbf{x}_0$ lies in the Krylov space and
that the residual is orthogonal to it, through the Galerkin characterisation
`Matrix.PosDef.eq_cgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero`.

## Main definitions

* `NLAlib.CGState`, `NLAlib.cgStep`, `NLAlib.cgState`.

## Main results

* `NLAlib.cgState_r_eq`, `NLAlib.cgState_x_sub_mem_krylovSpace`: for every $\mathbf{A}$.
* `NLAlib.cgStep_eq`: real dot-product scalarization of the specified step.
* `Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_cgState_r_eq_zero`: the residual is
  orthogonal to the Krylov space.
* `Matrix.PosDef.cgState_x_eq`: the Hestenes–Stiefel iterates are the CG iterates.
* `Matrix.PosDef.cgState_r_eq_zero_iff`: the residual vanishes exactly from the grade on.
* `NLAlib.cgState_p_eq_zero_of_r_eq_zero`, `NLAlib.cgState_succ_eq_of_r_eq_zero`:
  a zero residual has zero direction and the entire recurrence state stays fixed.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The state of the Hestenes–Stiefel recurrence after $k$ steps: iterate $\mathbf{x}_k$,
residual $\mathbf{r}_k$, search direction $\mathbf{p}_k$.
Algorithm: cg -/
structure CGState (𝕜 n : Type*) where
  /-- The iterate $\mathbf{x}_k$. -/
  x : n → 𝕜
  /-- The residual vector $\mathbf{r}_k$. The exact recurrence identifies it with
  $\mathbf{b} - \mathbf{A}\mathbf{x}_k$; a stored rounded state may have a residual gap. -/
  r : n → 𝕜
  /-- The search direction $\mathbf{p}_k$. -/
  p : n → 𝕜

/-- **One Hestenes–Stiefel step**:
$\alpha_k = \|\mathbf{r}_k\|^2 /
\operatorname{Re}(\mathbf{p}_k^{\mathsf{H}}\mathbf{A}\mathbf{p}_k)$,
$\mathbf{x}_{k+1} = \mathbf{x}_k + \alpha_k\mathbf{p}_k$,
$\mathbf{r}_{k+1} = \mathbf{r}_k - \alpha_k\mathbf{A}\mathbf{p}_k$,
$\beta_k = \|\mathbf{r}_{k+1}\|^2/\|\mathbf{r}_k\|^2$,
$\mathbf{p}_{k+1} = \mathbf{r}_{k+1} + \beta_k\mathbf{p}_k$. With $0^{-1} = 0$ a zero residual
gives $\alpha_k = \beta_k = 0$ and the state stays put.
[HestenesStiefel1952, (3:1)]; [TrefethenBau1997, Algorithm 38.1]. Hestenes and Stiefel write
$(\mathbf{p}_k, \mathbf{A}\mathbf{p}_k)$ for real symmetric $\mathbf{A}$, here its real part.
Algorithm: cg -/
noncomputable def cgStep (A : Matrix n n 𝕜) (s : CGState 𝕜 n) : CGState 𝕜 n :=
  let α : ℝ := ‖WithLp.toLp 2 s.r‖ ^ 2 / RCLike.re (quadForm A s.p)
  let r' := s.r - (α : 𝕜) • (A *ᵥ s.p)
  ⟨s.x + (α : 𝕜) • s.p, r',
    r' + ((‖WithLp.toLp 2 r'‖ ^ 2 / ‖WithLp.toLp 2 s.r‖ ^ 2 : ℝ) : 𝕜) • s.p⟩

/-- The **Hestenes–Stiefel recurrence** (the conjugate gradient algorithm) from the start
$\mathbf{x}_0$: the state after $k$ steps, from $(\mathbf{x}_0, \mathbf{r}_0, \mathbf{r}_0)$,
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$. [HestenesStiefel1952, (3:1)]; the start
$\mathbf{p}_0 = \mathbf{r}_0$ is (3:1a) there.
Algorithm: cg -/
noncomputable def cgState (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) : ℕ → CGState 𝕜 n
  | 0 => ⟨x₀, b - A *ᵥ x₀, b - A *ᵥ x₀⟩
  | k + 1 => cgStep A (cgState A b x₀ k)

omit [DecidableEq n] in
/-- The specified real CG step expressed using dot products and componentwise arithmetic.
Squared Euclidean residual norms equal self-dot products, and the real quadratic form is
$\mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p}$. No positivity or nonbreakdown assumption is
needed because division is total. This identifies the exact scalar-loop outputs with the
existing recurrence. -/
theorem cgStep_eq (A : Matrix n n ℝ) (s : CGState ℝ n) :
    cgStep A s =
      let α := (s.r ⬝ᵥ s.r) / (s.p ⬝ᵥ (A *ᵥ s.p))
      let r' := fun i => s.r i - α * (A *ᵥ s.p) i
      ⟨fun i => s.x i + α * s.p i, r',
        fun i => r' i + ((r' ⬝ᵥ r') / (s.r ⬝ᵥ s.r)) * s.p i⟩ := by
  simp only [cgStep, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, quadForm,
    star_trivial, RCLike.re_to_real]
  rfl

omit [DecidableEq n] in
/-- A zero residual in the total CG recurrence has zero direction, for every matrix and
starting vector. This includes the initial state and terminal states after any step. -/
theorem cgState_p_eq_zero_of_r_eq_zero (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) {j : ℕ}
    (hr : (cgState A b x₀ j).r = 0) : (cgState A b x₀ j).p = 0 := by
  cases j with
  | zero => exact hr
  | succ j =>
    have hp : (cgState A b x₀ (j + 1)).p = (cgState A b x₀ (j + 1)).r +
        ((‖WithLp.toLp 2 (cgState A b x₀ (j + 1)).r‖ ^ 2 /
          ‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2 : ℝ) : 𝕜) • (cgState A b x₀ j).p := rfl
    rw [hp, hr]
    simp

omit [DecidableEq n] in
/-- Once its residual is zero, the entire total CG recurrence state is fixed at the next
step. This justifies zero-residual stopping without changing a later exact iterate. -/
theorem cgState_succ_eq_of_r_eq_zero (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) {j : ℕ}
    (hr : (cgState A b x₀ j).r = 0) :
    cgState A b x₀ (j + 1) = cgState A b x₀ j := by
  have hp := cgState_p_eq_zero_of_r_eq_zero A b x₀ hr
  change cgStep A (cgState A b x₀ j) = cgState A b x₀ j
  generalize cgState A b x₀ j = s at hr hp ⊢
  rcases s with ⟨x, r, p⟩
  change r = 0 at hr
  change p = 0 at hp
  subst r
  subst p
  simp [cgStep]

variable {A : Matrix n n 𝕜} {b x₀ : n → 𝕜}

omit [DecidableEq n] in
/-- The exact CG state advances by one application of its total step function. -/
theorem cgState_succ (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    cgState A b x₀ (k + 1) = cgStep A (cgState A b x₀ k) :=
  rfl

omit [DecidableEq n] in
/-- The updated residual is the true residual, for every $\mathbf{A}$. -/
theorem cgState_r_eq (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (cgState A b x₀ k).r = b - A *ᵥ (cgState A b x₀ k).x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cgState_succ]
    simp only [cgStep, ih, Matrix.mulVec_add, Matrix.mulVec_smul]
    abel

omit [DecidableEq n] in
/-- The residual against the initial residual:
$\mathbf{r}_k = \mathbf{r}_0 - \mathbf{A}(\mathbf{x}_k - \mathbf{x}_0)$. -/
private lemma cgState_r_eq_sub (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (cgState A b x₀ k).r = (b - A *ᵥ x₀) - A *ᵥ ((cgState A b x₀ k).x - x₀) := by
  rw [cgState_r_eq, Matrix.mulVec_sub]
  abel

/-- The memberships behind the realisation, for every $\mathbf{A}$:
$\mathbf{x}_k - \mathbf{x}_0 \in \mathcal{K}_k$ and
$\mathbf{p}_k - \mathbf{r}_k \in \mathcal{K}_k$. -/
private lemma cgState_mem (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (cgState A b x₀ k).x - x₀ ∈ krylovSpace A (b - A *ᵥ x₀) k ∧
      (cgState A b x₀ k).p - (cgState A b x₀ k).r ∈ krylovSpace A (b - A *ᵥ x₀) k := by
  induction k with
  | zero => simp [cgState]
  | succ k ih =>
    obtain ⟨hx, hpr⟩ := ih
    have hr : (cgState A b x₀ k).r ∈ krylovSpace A (b - A *ᵥ x₀) (k + 1) := by
      rw [cgState_r_eq_sub]
      exact Submodule.sub_mem _ (self_mem_krylovSpace _ _ k.succ_pos)
        (mulVec_mem_krylovSpace_succ hx)
    have hp : (cgState A b x₀ k).p ∈ krylovSpace A (b - A *ᵥ x₀) (k + 1) := by
      have h := Submodule.add_mem _ hr (krylovSpace_mono _ _ k.le_succ hpr)
      rwa [add_sub_cancel] at h
    rw [cgState_succ]
    refine ⟨?_, ?_⟩
    · simp only [cgStep]
      rw [add_sub_right_comm]
      exact Submodule.add_mem _ (krylovSpace_mono _ _ k.le_succ hx) (Submodule.smul_mem _ _ hp)
    · simp only [cgStep]
      rw [add_sub_cancel_left]
      exact Submodule.smul_mem _ _ hp

private lemma cgState_r_mem (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (cgState A b x₀ k).r ∈ krylovSpace A (b - A *ᵥ x₀) (k + 1) := by
  rw [cgState_r_eq_sub]
  exact Submodule.sub_mem _ (self_mem_krylovSpace _ _ k.succ_pos)
    (mulVec_mem_krylovSpace_succ (cgState_mem A b x₀ k).1)

private lemma cgState_p_mem (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (cgState A b x₀ k).p ∈ krylovSpace A (b - A *ᵥ x₀) (k + 1) := by
  have h := Submodule.add_mem _ (cgState_r_mem A b x₀ k)
    (krylovSpace_mono _ _ k.le_succ (cgState_mem A b x₀ k).2)
  rwa [add_sub_cancel] at h

/-- The iterates stay in the shifted Krylov space, for every $\mathbf{A}$:
$\mathbf{x}_k - \mathbf{x}_0 \in \mathcal{K}_k(\mathbf{A}, \mathbf{r}_0)$. -/
theorem cgState_x_sub_mem_krylovSpace (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (cgState A b x₀ k).x - x₀ ∈ krylovSpace A (b - A *ᵥ x₀) k :=
  (cgState_mem A b x₀ k).1

/-! ### The orthogonality invariants -/

omit [DecidableEq n] in
/-- Orthogonality to a sum with a line reduces to the two parts. -/
private lemma star_dotProduct_eq_zero_of_mem_sup {M : Submodule 𝕜 (n → 𝕜)} {p w : n → 𝕜}
    (hM : ∀ y ∈ M, star y ⬝ᵥ w = 0) (hp : star p ⬝ᵥ w = 0) {y : n → 𝕜}
    (hy : y ∈ M ⊔ Submodule.span 𝕜 {p}) : star y ⬝ᵥ w = 0 := by
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  rw [star_add, add_dotProduct, star_smul, smul_dotProduct, hM u hu, hp, smul_zero, add_zero]

/-- $\mathbf{p}_k^{\mathsf{H}}\mathbf{r}_k = \|\mathbf{r}_k\|^2$ once
$\mathbf{r}_k \perp \mathcal{K}_k$. -/
private lemma star_p_dotProduct_r {k : ℕ}
    (hr : ∀ y ∈ krylovSpace A (b - A *ᵥ x₀) k, star y ⬝ᵥ (cgState A b x₀ k).r = 0) :
    star (cgState A b x₀ k).p ⬝ᵥ (cgState A b x₀ k).r =
      star (cgState A b x₀ k).r ⬝ᵥ (cgState A b x₀ k).r := by
  have h := hr _ (cgState_mem A b x₀ k).2
  rwa [star_sub, sub_dotProduct, sub_eq_zero] at h

private lemma r_eq_zero_of_p_eq_zero {k : ℕ}
    (hr : ∀ y ∈ krylovSpace A (b - A *ᵥ x₀) k, star y ⬝ᵥ (cgState A b x₀ k).r = 0)
    (hp0 : (cgState A b x₀ k).p = 0) : (cgState A b x₀ k).r = 0 := by
  have h := star_p_dotProduct_r hr
  rw [hp0, star_zero, zero_dotProduct] at h
  exact dotProduct_star_self_eq_zero.1 h.symm

/-- With the invariants at step $k$, $\mathcal{K}_{k+1} = \mathcal{K}_k + \operatorname{span}
\{\mathbf{p}_k\}$. -/
private lemma krylovSpace_succ_eq_sup (hA : A.PosDef) {k : ℕ}
    (hr : ∀ y ∈ krylovSpace A (b - A *ᵥ x₀) k, star y ⬝ᵥ (cgState A b x₀ k).r = 0)
    (hp : ∀ y ∈ krylovSpace A (b - A *ᵥ x₀) k, star y ⬝ᵥ (A *ᵥ (cgState A b x₀ k).p) = 0) :
    krylovSpace A (b - A *ᵥ x₀) (k + 1) =
      krylovSpace A (b - A *ᵥ x₀) k ⊔ Submodule.span 𝕜 {(cgState A b x₀ k).p} := by
  refine le_antisymm ?_ (sup_le (krylovSpace_mono _ _ k.le_succ)
    ((Submodule.span_singleton_le_iff_mem _ _).2 (cgState_p_mem A b x₀ k)))
  by_cases hν : krylovGrade A (b - A *ᵥ x₀) ≤ k
  · rw [krylovSpace_eq_of_krylovGrade_le (hν.trans k.le_succ),
      ← krylovSpace_eq_of_krylovGrade_le hν]
    exact le_sup_left
  push Not at hν
  rw [krylovSpace_succ]
  refine sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
  have hpk := cgState_p_mem A b x₀ k
  rw [krylovSpace_succ] at hpk
  obtain ⟨u, hu, z, hz, hpuz⟩ := Submodule.mem_sup.1 hpk
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  rcases eq_or_ne c 0 with rfl | hc
  · exfalso
    rw [zero_smul, add_zero] at hpuz
    have hq := hp _ (hpuz ▸ hu)
    have hp0 : (cgState A b x₀ k).p = 0 := by
      by_contra hne
      exact (hA.dotProduct_mulVec_pos hne).ne' hq
    have hr0 := r_eq_zero_of_p_eq_zero hr hp0
    rw [cgState_r_eq_sub, sub_eq_zero] at hr0
    exact hν.not_ge (krylovGrade_le_of_mem_of_mulVec_eq (cgState_mem A b x₀ k).1 hr0.symm)
  · have h : A ^ k *ᵥ (b - A *ᵥ x₀) = c⁻¹ • ((cgState A b x₀ k).p - u) := by
      rw [← hpuz, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) (Submodule.mem_sup_left hu))

/-- One step of the joint induction: $\mathbf{r}_k \perp \mathcal{K}_k$ and
$\mathbf{A}\mathbf{p}_k \perp \mathcal{K}_k$ pass to $k + 1$. -/
private lemma orth_succ (hA : A.PosDef) {k : ℕ}
    (hr : ∀ y ∈ krylovSpace A (b - A *ᵥ x₀) k, star y ⬝ᵥ (cgState A b x₀ k).r = 0)
    (hp : ∀ y ∈ krylovSpace A (b - A *ᵥ x₀) k, star y ⬝ᵥ (A *ᵥ (cgState A b x₀ k).p) = 0) :
    (∀ y ∈ krylovSpace A (b - A *ᵥ x₀) (k + 1), star y ⬝ᵥ (cgState A b x₀ (k + 1)).r = 0) ∧
      ∀ y ∈ krylovSpace A (b - A *ᵥ x₀) (k + 1),
        star y ⬝ᵥ (A *ᵥ (cgState A b x₀ (k + 1)).p) = 0 := by
  have hsup := krylovSpace_succ_eq_sup hA hr hp
  set s := cgState A b x₀ k with hs
  by_cases hr0 : s.r = 0
  · have h1 : (cgState A b x₀ (k + 1)).r = 0 := by
      rw [cgState_succ, ← hs]
      simp [cgStep, hr0]
    have h2 : (cgState A b x₀ (k + 1)).p = 0 := by
      rw [cgState_succ, ← hs]
      simp [cgStep, hr0]
    simp [h1, h2]
  have hp0 : s.p ≠ 0 := fun h => hr0 (r_eq_zero_of_p_eq_zero hr h)
  set ρ := ‖WithLp.toLp 2 s.r‖ ^ 2 with hρdef
  set Q := RCLike.re (quadForm A s.p) with hQdef
  have hQ : 0 < Q := hA.re_quadForm_pos hp0
  have hρ : 0 < ρ := by
    have : WithLp.toLp 2 s.r ≠ 0 := by simpa using hr0
    positivity
  set α := ρ / Q with hαdef
  have hr' : (cgState A b x₀ (k + 1)).r = s.r - (α : 𝕜) • (A *ᵥ s.p) := rfl
  have hp' : (cgState A b x₀ (k + 1)).p = (cgState A b x₀ (k + 1)).r +
      ((‖WithLp.toLp 2 (cgState A b x₀ (k + 1)).r‖ ^ 2 / ρ : ℝ) : 𝕜) • s.p := rfl
  have hquad : star s.p ⬝ᵥ (A *ᵥ s.p) = (Q : 𝕜) := (hA.isHermitian.coe_re_quadForm _).symm
  have hρ𝕜 : star s.p ⬝ᵥ s.r = (ρ : 𝕜) := by
    rw [star_p_dotProduct_r hr, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq]
  have horth : ∀ y ∈ krylovSpace A (b - A *ᵥ x₀) (k + 1),
      star y ⬝ᵥ (cgState A b x₀ (k + 1)).r = 0 := by
    intro y hy
    rw [hsup] at hy
    refine star_dotProduct_eq_zero_of_mem_sup (fun u hu => ?_) ?_ hy
    · rw [hr', dotProduct_sub, dotProduct_smul, hr u hu, hp u hu, smul_zero, sub_zero]
    · rw [hr', dotProduct_sub, dotProduct_smul, hquad, hρ𝕜, smul_eq_mul, ← RCLike.ofReal_mul,
        div_mul_cancel₀ _ hQ.ne', sub_self]
  refine ⟨horth, fun y hy => ?_⟩
  rw [hsup] at hy
  refine star_dotProduct_eq_zero_of_mem_sup (fun u hu => ?_) ?_ hy
  · rw [hp', Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, hp u hu,
      smul_zero, add_zero, hA.isHermitian.star_dotProduct_mulVec_comm, ← Matrix.star_dotProduct]
    exact horth _ (mulVec_mem_krylovSpace_succ hu)
  · set ρ' := ‖WithLp.toLp 2 (cgState A b x₀ (k + 1)).r‖ ^ 2 with hρ'def
    have hrr : star s.r ⬝ᵥ (cgState A b x₀ (k + 1)).r = 0 := horth _ (cgState_r_mem A b x₀ k)
    have hr'r' : star (cgState A b x₀ (k + 1)).r ⬝ᵥ (cgState A b x₀ (k + 1)).r = (ρ' : 𝕜) :=
      EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq _
    have hX : (α : 𝕜) * (star s.p ⬝ᵥ (A *ᵥ (cgState A b x₀ (k + 1)).r)) = -(ρ' : 𝕜) := by
      have h : (α : 𝕜) • star (A *ᵥ s.p) = star (s.r - (cgState A b x₀ (k + 1)).r) := by
        rw [hr', sub_sub_cancel, star_smul, RCLike.star_def, RCLike.conj_ofReal]
      rw [hA.isHermitian.star_dotProduct_mulVec_comm, ← Matrix.star_dotProduct, ← smul_eq_mul,
        ← smul_dotProduct, h, star_sub, sub_dotProduct, hrr, hr'r', zero_sub]
    have hα : (α : 𝕜) ≠ 0 := by exact_mod_cast (div_pos hρ hQ).ne'
    rw [hp', Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, hquad,
      smul_eq_mul]
    apply mul_left_cancel₀ hα
    rw [mul_add, hX, mul_zero, hαdef]
    push_cast
    field_simp
    ring

private lemma orth (hA : A.PosDef) (b x₀ : n → 𝕜) (k : ℕ) :
    (∀ y ∈ krylovSpace A (b - A *ᵥ x₀) k, star y ⬝ᵥ (cgState A b x₀ k).r = 0) ∧
      ∀ y ∈ krylovSpace A (b - A *ᵥ x₀) k, star y ⬝ᵥ (A *ᵥ (cgState A b x₀ k).p) = 0 := by
  induction k with
  | zero => simp [krylovSpace_zero]
  | succ k ih => exact orth_succ hA ih.1 ih.2

/-- **The residual is orthogonal to the Krylov space**, for positive definite $\mathbf{A}$:
$\mathbf{K}_k(\mathbf{A}, \mathbf{r}_0)^{\mathsf{H}}\mathbf{r}_k = \mathbf{0}$.
[HestenesStiefel1952, Theorem 5:1]; [TrefethenBau1997, Theorem 38.1]. Hestenes and Stiefel
state $(\mathbf{p}_i, \mathbf{r}_j) = 0$ for $i < j$ ((5:3c)), with the directions spanning the
Krylov space (`Matrix.PosDef.span_cgState_p`). -/
theorem _root_.Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_cgState_r_eq_zero (hA : A.PosDef)
    (b x₀ : n → 𝕜) (k : ℕ) : (krylovMatrix A (b - A *ᵥ x₀) k)ᴴ *ᵥ (cgState A b x₀ k).r = 0 :=
  forall_mem_range_star_dotProduct_eq_zero_iff.1 (orth hA b x₀ k).1

omit [DecidableEq n] in
private lemma range_fin_succ {α : Type*} (f : ℕ → α) (k : ℕ) :
    Set.range (fun j : Fin (k + 1) => f j) = insert (f k) (Set.range fun j : Fin k => f j) := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inr ⟨j, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last k, rfl⟩
    · exact ⟨i.castSucc, rfl⟩

/-- The search directions span the Krylov spaces, for positive definite $\mathbf{A}$.
[HestenesStiefel1952, Theorem 5:4]; [TrefethenBau1997, Theorem 38.1]. Hestenes and Stiefel give
the three-term relations (5:7) for the directions, from which $\mathbf{p}_j$ lies in
$\mathcal{K}_{j+1}(\mathbf{A}, \mathbf{r}_0)$. -/
theorem _root_.Matrix.PosDef.span_cgState_p (hA : A.PosDef) (k : ℕ) :
    Submodule.span 𝕜 (Set.range fun j : Fin k => (cgState A b x₀ j).p) =
      krylovSpace A (b - A *ᵥ x₀) k := by
  induction k with
  | zero => rw [Set.range_eq_empty, Submodule.span_empty, krylovSpace_zero]
  | succ k ih =>
    rw [range_fin_succ (fun j => (cgState A b x₀ j).p), Submodule.span_insert, ih,
      krylovSpace_succ_eq_sup hA (orth hA b x₀ k).1 (orth hA b x₀ k).2, sup_comm]

omit [DecidableEq n] in
/-- **The residuals are orthogonal**, for positive definite $\mathbf{A}$:
$\mathbf{r}_j^{\mathsf{H}}\mathbf{r}_k = 0$ for $j < k$.
[HestenesStiefel1952, Theorem 5:1]; [TrefethenBau1997, Theorem 38.1]. It is (5:3a) there, for
real symmetric $\mathbf{A}$.
Result: cg-orthogonality -/
theorem _root_.Matrix.PosDef.star_cgState_r_dotProduct_eq_zero (hA : A.PosDef) {j k : ℕ}
    (hjk : j < k) : star (cgState A b x₀ j).r ⬝ᵥ (cgState A b x₀ k).r = 0 := by
  classical
  exact (orth hA b x₀ k).1 _ (krylovSpace_mono _ _ hjk (cgState_r_mem A b x₀ j))

omit [DecidableEq n] in
/-- **The search directions are $\mathbf{A}$-conjugate**, for positive definite $\mathbf{A}$:
$\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_k = 0$ for $j < k$.
[HestenesStiefel1952, Theorem 5:1]; [TrefethenBau1997, Theorem 38.1]. It is (5:3b) there, for
real symmetric $\mathbf{A}$.
Result: cg-orthogonality -/
theorem _root_.Matrix.PosDef.star_cgState_p_dotProduct_mulVec_eq_zero (hA : A.PosDef) {j k : ℕ}
    (hjk : j < k) : star (cgState A b x₀ j).p ⬝ᵥ (A *ᵥ (cgState A b x₀ k).p) = 0 := by
  classical
  exact (orth hA b x₀ k).2 _ (krylovSpace_mono _ _ hjk (cgState_p_mem A b x₀ j))

/-- **The Hestenes–Stiefel iterates are the CG iterates**: for positive definite $\mathbf{A}$ and
every $k$, with no breakdown hypothesis,
$\mathbf{x}_k = \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, k)$.
[HestenesStiefel1952, Theorem 6:1]; [TrefethenBau1997, Theorem 38.1]. Hestenes and Stiefel show
that $\mathbf{x}_k$ minimises the $\mathbf{A}$-norm error on the plane through
$\mathbf{x}_0, \dots, \mathbf{x}_k$, which is $\mathbf{x}_0 + \mathcal{K}_k(\mathbf{A},
\mathbf{r}_0)$ (`Matrix.PosDef.span_cgState_p`), for real symmetric $\mathbf{A}$ and up to
termination; here every $k$.
Result: cg-recurrence -/
theorem _root_.Matrix.PosDef.cgState_x_eq (hA : A.PosDef) (b x₀ : n → 𝕜) (k : ℕ) :
    (cgState A b x₀ k).x = cgIterate A b x₀ k := by
  have h : (krylovMatrix A (b - A *ᵥ x₀) k)ᴴ *ᵥ (b - A *ᵥ (cgState A b x₀ k).x) = 0 := by
    rw [← cgState_r_eq]
    exact hA.conjTranspose_krylovMatrix_mulVec_cgState_r_eq_zero b x₀ k
  exact hA.eq_cgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero
    (cgState_x_sub_mem_krylovSpace A b x₀ k) h

/-- **CG stops exactly at the grade**: for positive definite $\mathbf{A}$ the computed residual
vanishes iff $k$ is at least the grade of $\mathbf{r}_0$. [Saad2003, §6.7]. -/
theorem _root_.Matrix.PosDef.cgState_r_eq_zero_iff (hA : A.PosDef) (b x₀ : n → 𝕜) (k : ℕ) :
    (cgState A b x₀ k).r = 0 ↔ krylovGrade A (b - A *ᵥ x₀) ≤ k := by
  constructor
  · intro h
    rw [cgState_r_eq_sub, sub_eq_zero] at h
    exact krylovGrade_le_of_mem_of_mulVec_eq (cgState_x_sub_mem_krylovSpace A b x₀ k) h.symm
  · intro hν
    have hxs : A *ᵥ (A⁻¹ *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
        hA.isUnit), Matrix.one_mulVec]
    rw [cgState_r_eq, hA.cgState_x_eq, hA.cgIterate_eq_of_krylovGrade_le hxs x₀ hν, hxs,
      sub_self]

end NLAlib
