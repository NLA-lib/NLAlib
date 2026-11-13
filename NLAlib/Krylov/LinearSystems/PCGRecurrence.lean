/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGRecurrence
public import NLAlib.Krylov.LinearSystems.PCG

/-!
# The preconditioned Hestenes–Stiefel recurrence

Preconditioned conjugate gradients as a total recursion on a state indexed by the step: iterate
$\mathbf{x}_k$, residual $\mathbf{r}_k$, preconditioned residual $\mathbf{z}_k =
\mathbf{M}\mathbf{r}_k$ and search direction $\mathbf{p}_k$. Each step applies $\mathbf{A}$ once
and $\mathbf{M}$ once; no square root of $\mathbf{M}$ is formed. Breakdown is a value: a zero
residual makes both step sizes zero and the state stays at the solution.

The realisation theorem says that for positive definite $\mathbf{A}$ and $\mathbf{M}$ the
computed iterates are `NLAlib.pcgIterate`, for every $k$ and with no breakdown hypothesis. The
proof compares the recurrence, step by step, with the Hestenes–Stiefel recurrence on the split
system for any factor $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$
(`NLAlib.pcgState_x_eq_mulVec_cgState_x`), and then uses the CG realisation
`Matrix.PosDef.cgState_x_eq` and `Matrix.PosDef.pcgIterate_eq_mulVec_cgIterate`; the factor is
in the proof only.

[Saad2003, Algorithm 9.1] writes the preconditioner as the matrix it approximates; their
$\mathbf{M}$ is our $\mathbf{M}^{-1}$.

## Main definitions

* `NLAlib.PCGState`, `NLAlib.pcgStep`, `NLAlib.pcgState`.

## Main results

* `NLAlib.pcgState_r_eq`, `NLAlib.pcgState_z_eq`, `NLAlib.pcgState_x_sub_mem_krylovSpace`.
* `NLAlib.pcgState_x_eq_mulVec_cgState_x`: the recurrence is HS on the split system.
* `Matrix.PosDef.pcgState_x_eq`: the computed iterates are the PCG iterates.
* `Matrix.PosDef.star_pcgState_z_dotProduct_eq_zero`,
  `Matrix.PosDef.star_pcgState_p_dotProduct_mulVec_eq_zero`: $\mathbf{M}$-orthogonal residuals,
  $\mathbf{A}$-conjugate directions.
* `Matrix.PosDef.pcgState_r_eq_zero_iff`: breakdown exactly at the grade.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The state of the preconditioned Hestenes–Stiefel recurrence after $k$ steps.
Algorithm: pcg -/
structure PCGState (𝕜 n : Type*) where
  /-- The iterate $\mathbf{x}_k$. -/
  x : n → 𝕜
  /-- The residual $\mathbf{r}_k = \mathbf{b} - \mathbf{A}\mathbf{x}_k$. -/
  r : n → 𝕜
  /-- The preconditioned residual $\mathbf{z}_k = \mathbf{M}\mathbf{r}_k$. -/
  z : n → 𝕜
  /-- The search direction $\mathbf{p}_k$. -/
  p : n → 𝕜

/-- **One preconditioned Hestenes–Stiefel step**, one application of $\mathbf{A}$ and one of
$\mathbf{M}$: $\rho_k = \operatorname{Re}\langle\mathbf{r}_k, \mathbf{z}_k\rangle$,
$\alpha_k = \rho_k/\operatorname{Re}(\mathbf{p}_k^{\mathsf{H}}\mathbf{A}\mathbf{p}_k)$,
$\mathbf{x}_{k+1} = \mathbf{x}_k + \alpha_k\mathbf{p}_k$,
$\mathbf{r}_{k+1} = \mathbf{r}_k - \alpha_k\mathbf{A}\mathbf{p}_k$,
$\mathbf{z}_{k+1} = \mathbf{M}\mathbf{r}_{k+1}$,
$\beta_k = \rho_{k+1}/\rho_k$, $\mathbf{p}_{k+1} = \mathbf{z}_{k+1} + \beta_k\mathbf{p}_k$.
[Saad2003, Algorithm 9.1]; [Greenbaum1997, Chapter 8, Algorithm 2P].
Algorithm: pcg -/
noncomputable def pcgStep (A M : Matrix n n 𝕜) (s : PCGState 𝕜 n) : PCGState 𝕜 n :=
  let ρ : ℝ := RCLike.re (star s.r ⬝ᵥ s.z)
  let α : ℝ := ρ / RCLike.re (quadForm A s.p)
  let r' := s.r - (α : 𝕜) • (A *ᵥ s.p)
  let z' := M *ᵥ r'
  ⟨s.x + (α : 𝕜) • s.p, r', z', z' + ((RCLike.re (star r' ⬝ᵥ z') / ρ : ℝ) : 𝕜) • s.p⟩

/-- The **preconditioned Hestenes–Stiefel recurrence** from $\mathbf{x}_0$: the state after $k$
steps, from $(\mathbf{x}_0, \mathbf{r}_0, \mathbf{M}\mathbf{r}_0, \mathbf{M}\mathbf{r}_0)$.
Algorithm: pcg -/
noncomputable def pcgState (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) : ℕ → PCGState 𝕜 n
  | 0 => ⟨x₀, b - A *ᵥ x₀, M *ᵥ (b - A *ᵥ x₀), M *ᵥ (b - A *ᵥ x₀)⟩
  | k + 1 => pcgStep A M (pcgState A M b x₀ k)

variable {A M : Matrix n n 𝕜}

omit [DecidableEq n] in
private lemma pcgState_succ (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    pcgState A M b x₀ (k + 1) = pcgStep A M (pcgState A M b x₀ k) :=
  rfl

omit [DecidableEq n] in
/-- The split matrix applied: $\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}\mathbf{v}$. -/
private lemma conjTranspose_mulVec_mulVec_mulVec (A C : Matrix n n 𝕜) (v : n → 𝕜) :
    Cᴴ *ᵥ (A *ᵥ (C *ᵥ v)) = (Cᴴ * A * C) *ᵥ v := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

omit [DecidableEq n] in
/-- The updated residual is the true residual, for every $\mathbf{A}$ and $\mathbf{M}$. -/
theorem pcgState_r_eq (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (pcgState A M b x₀ k).r = b - A *ᵥ (pcgState A M b x₀ k).x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pcgState_succ]
    simp only [pcgStep, ih, Matrix.mulVec_add, Matrix.mulVec_smul]
    abel

omit [DecidableEq n] in
/-- The stored preconditioned residual is $\mathbf{M}\mathbf{r}_k$. -/
theorem pcgState_z_eq (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (pcgState A M b x₀ k).z = M *ᵥ (pcgState A M b x₀ k).r := by
  cases k <;> rfl

omit [DecidableEq n] in
/-- The residual against the initial residual:
$\mathbf{r}_k = \mathbf{r}_0 - \mathbf{A}(\mathbf{x}_k - \mathbf{x}_0)$. -/
private lemma pcgState_r_eq_sub (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (pcgState A M b x₀ k).r = (b - A *ᵥ x₀) - A *ᵥ ((pcgState A M b x₀ k).x - x₀) := by
  rw [pcgState_r_eq, Matrix.mulVec_sub]
  abel

/-- The memberships, for every $\mathbf{A}$ and $\mathbf{M}$:
$\mathbf{x}_k - \mathbf{x}_0 \in \mathcal{K}_k$ and $\mathbf{p}_k - \mathbf{z}_k \in \mathcal{K}_k$,
for $\mathcal{K}_k = \mathcal{K}_k(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{r}_0)$. -/
private lemma pcgState_mem (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (pcgState A M b x₀ k).x - x₀ ∈ krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) k ∧
      (pcgState A M b x₀ k).p - (pcgState A M b x₀ k).z ∈
        krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) k := by
  induction k with
  | zero => simp [pcgState]
  | succ k ih =>
    obtain ⟨hx, hpz⟩ := ih
    have hz : (pcgState A M b x₀ k).z ∈ krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) (k + 1) := by
      rw [pcgState_z_eq, pcgState_r_eq_sub, Matrix.mulVec_sub M (b - A *ᵥ x₀), Matrix.mulVec_mulVec]
      exact Submodule.sub_mem _ (self_mem_krylovSpace _ _ k.succ_pos)
        (mulVec_mem_krylovSpace_succ hx)
    have hp : (pcgState A M b x₀ k).p ∈ krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) (k + 1) := by
      have h := Submodule.add_mem _ hz (krylovSpace_mono _ _ k.le_succ hpz)
      rwa [add_sub_cancel] at h
    rw [pcgState_succ]
    refine ⟨?_, ?_⟩
    · simp only [pcgStep]
      rw [add_sub_right_comm]
      exact Submodule.add_mem _ (krylovSpace_mono _ _ k.le_succ hx) (Submodule.smul_mem _ _ hp)
    · simp only [pcgStep]
      rw [add_sub_cancel_left]
      exact Submodule.smul_mem _ _ hp

omit [DecidableEq n] in
/-- One step of the correspondence with the Hestenes–Stiefel recurrence on the split system
$\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}$. -/
private lemma pcgStep_corr {C : Matrix n n 𝕜} (hM : M = C * Cᴴ) {s : PCGState 𝕜 n}
    {t : CGState 𝕜 n} (hx : s.x = C *ᵥ t.x) (hr : Cᴴ *ᵥ s.r = t.r) (hz : s.z = C *ᵥ t.r)
    (hp : s.p = C *ᵥ t.p) :
    (pcgStep A M s).x = C *ᵥ (cgStep (Cᴴ * A * C) t).x ∧
      Cᴴ *ᵥ (pcgStep A M s).r = (cgStep (Cᴴ * A * C) t).r ∧
      (pcgStep A M s).z = C *ᵥ (cgStep (Cᴴ * A * C) t).r ∧
      (pcgStep A M s).p = C *ᵥ (cgStep (Cᴴ * A * C) t).p := by
  have hnorm : ∀ u, RCLike.re (star u ⬝ᵥ (M *ᵥ u)) = ‖WithLp.toLp 2 (Cᴴ *ᵥ u)‖ ^ 2 := fun u => by
    rw [hM, ← quadForm_def, quadForm_mul_conjTranspose_self, RCLike.ofReal_re]
  have hρ : RCLike.re (star s.r ⬝ᵥ s.z) = ‖WithLp.toLp 2 t.r‖ ^ 2 := by
    rw [hz, ← hr, Matrix.mulVec_mulVec, ← hM]
    exact hnorm s.r
  have hQ : RCLike.re (quadForm A s.p) = RCLike.re (quadForm (Cᴴ * A * C) t.p) := by
    rw [hp, quadForm_conjTranspose_mul_mul]
  have hα : RCLike.re (star s.r ⬝ᵥ s.z) / RCLike.re (quadForm A s.p) =
      ‖WithLp.toLp 2 t.r‖ ^ 2 / RCLike.re (quadForm (Cᴴ * A * C) t.p) := by
    rw [hρ, hQ]
  set α := ‖WithLp.toLp 2 t.r‖ ^ 2 / RCLike.re (quadForm (Cᴴ * A * C) t.p) with hαdef
  have hr' : Cᴴ *ᵥ (s.r - (α : 𝕜) • (A *ᵥ s.p)) = t.r - (α : 𝕜) • ((Cᴴ * A * C) *ᵥ t.p) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hr, hp, conjTranspose_mulVec_mulVec_mulVec]
  have hz' : M *ᵥ (s.r - (α : 𝕜) • (A *ᵥ s.p)) =
      C *ᵥ (t.r - (α : 𝕜) • ((Cᴴ * A * C) *ᵥ t.p)) := by
    rw [hM, ← Matrix.mulVec_mulVec, hr']
  have hρ' : RCLike.re (star (s.r - (α : 𝕜) • (A *ᵥ s.p)) ⬝ᵥ
      (M *ᵥ (s.r - (α : 𝕜) • (A *ᵥ s.p)))) =
        ‖WithLp.toLp 2 (t.r - (α : 𝕜) • ((Cᴴ * A * C) *ᵥ t.p))‖ ^ 2 := by
    rw [hnorm, hr']
  simp only [pcgStep, cgStep]
  rw [hα, ← hαdef]
  refine ⟨?_, hr', hz', ?_⟩
  · rw [hx, hp, Matrix.mulVec_add, Matrix.mulVec_smul]
  · rw [hρ', hz', hρ, hp, Matrix.mulVec_add, Matrix.mulVec_smul]

omit [DecidableEq n] in
/-- **The state correspondence**: for $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$ and
$\mathbf{C}\mathbf{y}_0 = \mathbf{x}_0$, with hats on the Hestenes–Stiefel state for
$(\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}, \mathbf{C}^{\mathsf{H}}\mathbf{b}, \mathbf{y}_0)$,
$\mathbf{x}_k = \mathbf{C}\hat{\mathbf{x}}_k$,
$\mathbf{C}^{\mathsf{H}}\mathbf{r}_k = \hat{\mathbf{r}}_k$,
$\mathbf{z}_k = \mathbf{C}\hat{\mathbf{r}}_k$ and $\mathbf{p}_k = \mathbf{C}\hat{\mathbf{p}}_k$. -/
private lemma pcgState_corr {C : Matrix n n 𝕜} (hM : M = C * Cᴴ) {b x₀ y₀ : n → 𝕜}
    (hy₀ : C *ᵥ y₀ = x₀) (k : ℕ) :
    (pcgState A M b x₀ k).x = C *ᵥ (cgState (Cᴴ * A * C) (Cᴴ *ᵥ b) y₀ k).x ∧
      Cᴴ *ᵥ (pcgState A M b x₀ k).r = (cgState (Cᴴ * A * C) (Cᴴ *ᵥ b) y₀ k).r ∧
      (pcgState A M b x₀ k).z = C *ᵥ (cgState (Cᴴ * A * C) (Cᴴ *ᵥ b) y₀ k).r ∧
      (pcgState A M b x₀ k).p = C *ᵥ (cgState (Cᴴ * A * C) (Cᴴ *ᵥ b) y₀ k).p := by
  induction k with
  | zero =>
    have hr := Matrix.conjTranspose_mulVec_sub_mulVec_mulVec A C b y₀
    rw [hy₀] at hr
    have hz : M *ᵥ (b - A *ᵥ x₀) = C *ᵥ (Cᴴ *ᵥ b - (Cᴴ * A * C) *ᵥ y₀) := by
      rw [hM, ← Matrix.mulVec_mulVec, hr]
    exact ⟨hy₀.symm, hr, hz, hz⟩
  | succ k ih => exact pcgStep_corr hM ih.1 ih.2.1 ih.2.2.1 ih.2.2.2

/-- The iterates stay in the preconditioned Krylov space, for every $\mathbf{A}$, $\mathbf{M}$. -/
theorem pcgState_x_sub_mem_krylovSpace (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (pcgState A M b x₀ k).x - x₀ ∈ krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) k := by
  exact (pcgState_mem A M b x₀ k).1

omit [DecidableEq n] in
/-- The preconditioned recurrence is Hestenes–Stiefel on the split system: for any
$\mathbf{C}$ with $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$ and
$\mathbf{C}\mathbf{y}_0 = \mathbf{x}_0$, the computed iterate is $\mathbf{C}$ times the
Hestenes–Stiefel iterate for $(\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C},
\mathbf{C}^{\mathsf{H}}\mathbf{b}, \mathbf{y}_0)$, for every $\mathbf{A}$ and $k$. The states
correspond step by step, $\mathbf{C}^{\mathsf{H}}\mathbf{r}_k = \hat{\mathbf{r}}_k$,
$\mathbf{z}_k = \mathbf{C}\hat{\mathbf{r}}_k$, $\mathbf{p}_k = \mathbf{C}\hat{\mathbf{p}}_k$, and
the step sizes agree, since $\langle\mathbf{r}, \mathbf{M}\mathbf{r}\rangle =
\|\mathbf{C}^{\mathsf{H}}\mathbf{r}\|^2$ and $\mathbf{p}^{\mathsf{H}}\mathbf{A}\mathbf{p} =
\hat{\mathbf{p}}^{\mathsf{H}}\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}\hat{\mathbf{p}}$. -/
theorem pcgState_x_eq_mulVec_cgState_x {C : Matrix n n 𝕜} (hM : M = C * Cᴴ) {b x₀ y₀ : n → 𝕜}
    (hy₀ : C *ᵥ y₀ = x₀) (k : ℕ) :
    (pcgState A M b x₀ k).x = C *ᵥ (cgState (Cᴴ * A * C) (Cᴴ *ᵥ b) y₀ k).x := by
  exact (pcgState_corr hM hy₀ k).1

/-- **The preconditioned Hestenes–Stiefel iterates are the PCG iterates**: for positive definite
$\mathbf{A}$ and $\mathbf{M}$ and every $k$, with no breakdown hypothesis,
$\mathbf{x}_k = \mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, k)$.
[Saad2003, §9.2.1].
Result: pcg-recurrence -/
theorem _root_.Matrix.PosDef.pcgState_x_eq (hA : A.PosDef) (hM : M.PosDef) (b x₀ : n → 𝕜)
    (k : ℕ) : (pcgState A M b x₀ k).x = pcgIterate A M b x₀ k := by
  obtain ⟨S, hS, hMS⟩ := hM.exists_isUnit_eq_mul_conjTranspose
  obtain ⟨y₀, hy₀⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hS x₀
  have hA' : (Sᴴ * A * S).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hS).mpr hA
  rw [pcgState_x_eq_mulVec_cgState_x hMS hy₀ k, hA'.cgState_x_eq,
    ← hA.pcgIterate_eq_mulVec_cgIterate hS hMS hy₀ k]

omit [DecidableEq n] in
/-- **The residuals are $\mathbf{M}$-orthogonal**: for positive definite $\mathbf{A}$ and
$\mathbf{M}$, $\mathbf{z}_j^{\mathsf{H}}\mathbf{r}_k = 0$ for $j < k$. [Saad2003, §9.2].
Result: pcg-orthogonality -/
theorem _root_.Matrix.PosDef.star_pcgState_z_dotProduct_eq_zero (hA : A.PosDef) (hM : M.PosDef)
    {b x₀ : n → 𝕜} {j k : ℕ} (hjk : j < k) :
    star (pcgState A M b x₀ j).z ⬝ᵥ (pcgState A M b x₀ k).r = 0 := by
  classical
  obtain ⟨S, hS, hMS⟩ := hM.exists_isUnit_eq_mul_conjTranspose
  obtain ⟨y₀, hy₀⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hS x₀
  rw [(pcgState_corr hMS hy₀ j).2.2.1, star_mulVec_dotProduct,
    (pcgState_corr hMS hy₀ k).2.1]
  have hA' : (Sᴴ * A * S).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hS).mpr hA
  exact hA'.star_cgState_r_dotProduct_eq_zero hjk

omit [DecidableEq n] in
/-- **The search directions are $\mathbf{A}$-conjugate**, for positive definite $\mathbf{A}$ and
$\mathbf{M}$: $\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_k = 0$ for $j < k$.
[Saad2003, §9.2.1]; [HestenesStiefel1952, Theorem 5:1]. Saad shows that the PCG directions are
$\mathbf{L}^{-\mathsf{H}}$ times the CG directions of the split system
$\mathbf{L}^{-1}\mathbf{A}\mathbf{L}^{-\mathsf{H}}$,
$\mathbf{M}^{-1} = \mathbf{L}\mathbf{L}^{\mathsf{H}}$, with the same $\mathbf{A}$-inner products,
and those are conjugate by Hestenes and Stiefel; both work over $\mathbb{R}$.
Result: pcg-orthogonality -/
theorem _root_.Matrix.PosDef.star_pcgState_p_dotProduct_mulVec_eq_zero (hA : A.PosDef)
    (hM : M.PosDef) {b x₀ : n → 𝕜} {j k : ℕ} (hjk : j < k) :
    star (pcgState A M b x₀ j).p ⬝ᵥ (A *ᵥ (pcgState A M b x₀ k).p) = 0 := by
  classical
  obtain ⟨S, hS, hMS⟩ := hM.exists_isUnit_eq_mul_conjTranspose
  obtain ⟨y₀, hy₀⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hS x₀
  rw [(pcgState_corr hMS hy₀ j).2.2.2, (pcgState_corr hMS hy₀ k).2.2.2,
    star_mulVec_dotProduct, conjTranspose_mulVec_mulVec_mulVec]
  have hA' : (Sᴴ * A * S).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hS).mpr hA
  exact hA'.star_cgState_p_dotProduct_mulVec_eq_zero hjk

/-- PCG stops exactly at the grade: for positive definite $\mathbf{A}$ and $\mathbf{M}$ the
computed residual vanishes iff $k$ is at least the grade of $\mathbf{M}\mathbf{r}_0$ for
$\mathbf{M}\mathbf{A}$, which is the grade of the split system. -/
theorem _root_.Matrix.PosDef.pcgState_r_eq_zero_iff (hA : A.PosDef) (hM : M.PosDef)
    (b x₀ : n → 𝕜) (k : ℕ) :
    (pcgState A M b x₀ k).r = 0 ↔ krylovGrade (M * A) (M *ᵥ (b - A *ᵥ x₀)) ≤ k := by
  obtain ⟨S, hS, hMS⟩ := hM.exists_isUnit_eq_mul_conjTranspose
  obtain ⟨y₀, hy₀⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hS x₀
  have hA' : (Sᴴ * A * S).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hS).mpr hA
  have hinj : Function.Injective Sᴴ.mulVec := Matrix.mulVec_injective_of_isUnit (A := Sᴴ) hS.star
  have hr := Matrix.conjTranspose_mulVec_sub_mulVec_mulVec A S b y₀
  rw [hy₀] at hr
  have hg : krylovGrade (M * A) (M *ᵥ (b - A *ᵥ x₀)) =
      krylovGrade (Sᴴ * A * S) (Sᴴ *ᵥ b - (Sᴴ * A * S) *ᵥ y₀) := by
    rw [← hr, ← krylovGrade_mul_mulVec hS (Sᴴ * A), Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      ← hMS]
  rw [hg, ← hA'.cgState_r_eq_zero_iff,
    ← (pcgState_corr hMS hy₀ k).2.1]
  exact ⟨fun h => by rw [h, Matrix.mulVec_zero],
    fun h => hinj (by rw [h, Matrix.mulVec_zero])⟩

end NLAlib
