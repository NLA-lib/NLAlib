/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosRecurrence
public import NLAlib.Matrix.Spectral.Congruence

/-!
# The preconditioned Lanczos recurrence

The Lanczos recurrence for $\mathbf{M}\mathbf{A}$ in the $\mathbf{M}^{-1}$ inner product, with the
preconditioner $\mathbf{M}$ applied once per step and no square root: the state holds
$\mathbf{v}_{j-1}$, $\mathbf{v}_j$, $\mathbf{z}_j = \mathbf{M}\mathbf{v}_j$ and $\beta_j$, and a
step forms $\mathbf{w} = \mathbf{A}\mathbf{z}_j - \beta_j\mathbf{v}_{j-1} - \alpha_j\mathbf{v}_j$
with $\alpha_j = \operatorname{Re}\langle\mathbf{z}_j, \mathbf{A}\mathbf{z}_j -
\beta_j\mathbf{v}_{j-1}\rangle$, then $\mathbf{u} = \mathbf{M}\mathbf{w}$,
$\beta_{j+1} = \sqrt{\operatorname{Re}\langle\mathbf{w}, \mathbf{u}\rangle}$ and
$(\mathbf{v}_{j+1}, \mathbf{z}_{j+1}) = (\mathbf{w}, \mathbf{u})/\beta_{j+1}$. It is the Lanczos
process of preconditioned MINRES.

The realisation theorem compares it with the Lanczos recurrence of the split matrix: for
Hermitian $\mathbf{A}$ and any factor $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$, the
computed $\mathbf{z}_j$ are $\mathbf{C}$ times the canonical Lanczos vectors of
$\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}$ from $\mathbf{C}^{\mathsf{H}}\mathbf{b}$, and the
tridiagonal matrices agree, for every $q$ and with no breakdown hypothesis. The factor appears
only in the theorem, never in the recurrence.

[ElmanSilvesterWathen2014] write the preconditioner as the matrix it approximates; their
$\mathbf{M}$ is our $\mathbf{M}^{-1}$.

## Main definitions

* `NLAlib.PreconditionedLanczosState`, `NLAlib.preconditionedLanczosStep`,
  `NLAlib.preconditionedLanczosState`.
* `NLAlib.preconditionedLanczosMatrix`, `NLAlib.preconditionedLanczosTridiagonal`.

## Main results

* `NLAlib.preconditionedLanczosState_z_eq_mulVec`,
  `NLAlib.conjTranspose_mulVec_preconditionedLanczosState_cur`,
  `NLAlib.preconditionedLanczosState_beta_eq`, `NLAlib.preconditionedLanczosAlpha_eq`: the state
  correspondence with the split recurrence, for every $\mathbf{A}$ and factor.
* `Matrix.IsHermitian.preconditionedLanczosMatrix_eq`,
  `Matrix.IsHermitian.preconditionedLanczosTridiagonal_eq`: the realisation through a factor.
* `Matrix.IsHermitian.range_preconditionedLanczosMatrix`: the computed vectors span
  $\mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{b})$.
* `Matrix.IsHermitian.preconditionedLanczosState_z_eq_zero_of_le`,
  `Matrix.IsHermitian.preconditionedLanczosState_beta_eq_zero_of_le`: breakdown from the grade of
  the split system on.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The state of the preconditioned Lanczos recurrence before step $j$. -/
structure PreconditionedLanczosState (𝕜 n : Type*) where
  /-- The previous vector $\mathbf{v}_{j-1}$ ($\mathbf{0}$ for $j = 0$). -/
  prev : n → 𝕜
  /-- The current vector $\mathbf{v}_j$. -/
  cur : n → 𝕜
  /-- The preconditioned current vector $\mathbf{z}_j = \mathbf{M}\mathbf{v}_j$. -/
  z : n → 𝕜
  /-- The coefficient $\beta_j$ ($0$ for $j = 0$). -/
  beta : ℝ

/-- The diagonal coefficient
$\alpha_j = \operatorname{Re}\langle\mathbf{z}_j, \mathbf{A}\mathbf{z}_j -
\beta_j\mathbf{v}_{j-1}\rangle$. -/
noncomputable def preconditionedLanczosAlpha (A : Matrix n n 𝕜)
    (s : PreconditionedLanczosState 𝕜 n) : ℝ :=
  RCLike.re (star s.z ⬝ᵥ (A *ᵥ s.z - (s.beta : 𝕜) • s.prev))

/-- **One preconditioned Lanczos step**, one application of $\mathbf{M}$:
$\mathbf{w} = \mathbf{A}\mathbf{z}_j - \beta_j\mathbf{v}_{j-1} - \alpha_j\mathbf{v}_j$,
$\mathbf{u} = \mathbf{M}\mathbf{w}$, $\beta_{j+1} = \sqrt{\operatorname{Re}\langle\mathbf{w},
\mathbf{u}\rangle}$, $\mathbf{v}_{j+1} = \mathbf{w}/\beta_{j+1}$,
$\mathbf{z}_{j+1} = \mathbf{u}/\beta_{j+1}$. At breakdown everything after is zero.
[Greenbaum1997, Chapter 8, p. 121, Preconditioned Lanczos Algorithm]. -/
noncomputable def preconditionedLanczosStep (A M : Matrix n n 𝕜)
    (s : PreconditionedLanczosState 𝕜 n) : PreconditionedLanczosState 𝕜 n :=
  let w := A *ᵥ s.z - (s.beta : 𝕜) • s.prev - (preconditionedLanczosAlpha A s : 𝕜) • s.cur
  let u := M *ᵥ w
  let β := Real.sqrt (RCLike.re (star w ⬝ᵥ u))
  ⟨s.cur, ((β⁻¹ : ℝ) : 𝕜) • w, ((β⁻¹ : ℝ) : 𝕜) • u, β⟩

/-- The **preconditioned Lanczos recurrence** from $\mathbf{b}$: the state before step $j$, from
$\mathbf{v}_0 = \mathbf{b}/\beta_0$, $\mathbf{z}_0 = \mathbf{M}\mathbf{b}/\beta_0$,
$\beta_0 = \sqrt{\operatorname{Re}\langle\mathbf{b}, \mathbf{M}\mathbf{b}\rangle}$. -/
noncomputable def preconditionedLanczosState (A M : Matrix n n 𝕜) (b : n → 𝕜) :
    ℕ → PreconditionedLanczosState 𝕜 n
  | 0 =>
    let β := Real.sqrt (RCLike.re (star b ⬝ᵥ (M *ᵥ b)))
    ⟨0, ((β⁻¹ : ℝ) : 𝕜) • b, ((β⁻¹ : ℝ) : 𝕜) • (M *ᵥ b), 0⟩
  | j + 1 => preconditionedLanczosStep A M (preconditionedLanczosState A M b j)

/-- The preconditioned basis computed by $q$ steps: column $j$ is $\mathbf{z}_j$. -/
noncomputable def preconditionedLanczosMatrix (A M : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    Matrix n (Fin q) 𝕜 :=
  Matrix.of fun i j => (preconditionedLanczosState A M b j).z i

/-- The tridiagonal matrix computed by the preconditioned recurrence. -/
noncomputable def preconditionedLanczosTridiagonal (A M : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    Matrix (Fin q) (Fin q) 𝕜 :=
  Matrix.of fun i j =>
    if i = j then (preconditionedLanczosAlpha A (preconditionedLanczosState A M b i) : 𝕜)
    else if (i : ℕ) = j + 1 then ((preconditionedLanczosState A M b i).beta : 𝕜)
    else if (j : ℕ) = i + 1 then ((preconditionedLanczosState A M b j).beta : 𝕜)
    else 0

variable {A M : Matrix n n 𝕜}

/-! ### The correspondence with the split recurrence

For every $\mathbf{A}$ and every $\mathbf{C}$ with $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$,
the state of the preconditioned recurrence from $\mathbf{b}$ corresponds to the Lanczos state
of $\hat{\mathbf{A}} = \mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}$ from
$\mathbf{C}^{\mathsf{H}}\mathbf{b}$: $\mathbf{C}^{\mathsf{H}}\mathbf{v}_j = \hat{\mathbf{q}}_j$,
$\mathbf{z}_j = \mathbf{C}\hat{\mathbf{q}}_j$, equal $\alpha_j$ and $\beta_j$. Proved by one joint
induction (private); no invertibility and no Hermitian hypothesis. -/

omit [DecidableEq n] in
/-- The diagonal coefficients agree on corresponding states. -/
private theorem preconditionedLanczosAlpha_eq_of {C : Matrix n n 𝕜}
    {s : PreconditionedLanczosState 𝕜 n} {t : LanczosState 𝕜 n} (hz : s.z = C *ᵥ t.cur)
    (hp : Cᴴ *ᵥ s.prev = t.prev) (hb : s.beta = t.beta) :
    preconditionedLanczosAlpha A s = lanczosAlpha (Cᴴ * A * C) t := by
  rw [preconditionedLanczosAlpha, lanczosAlpha, hz, hb, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, hp, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

omit [DecidableEq n] in
/-- One step preserves the correspondence. -/
private theorem preconditionedLanczosStep_corr {C : Matrix n n 𝕜} (hM : M = C * Cᴴ)
    {s : PreconditionedLanczosState 𝕜 n} {t : LanczosState 𝕜 n} (hc : Cᴴ *ᵥ s.cur = t.cur)
    (hz : s.z = C *ᵥ t.cur) (hp : Cᴴ *ᵥ s.prev = t.prev) (hb : s.beta = t.beta) :
    Cᴴ *ᵥ (preconditionedLanczosStep A M s).cur = (lanczosStep (Cᴴ * A * C) t).cur ∧
      (preconditionedLanczosStep A M s).z = C *ᵥ (lanczosStep (Cᴴ * A * C) t).cur ∧
      Cᴴ *ᵥ (preconditionedLanczosStep A M s).prev = (lanczosStep (Cᴴ * A * C) t).prev ∧
      (preconditionedLanczosStep A M s).beta = (lanczosStep (Cᴴ * A * C) t).beta := by
  have hα := preconditionedLanczosAlpha_eq_of (A := A) hz hp hb
  have hw : Cᴴ *ᵥ (A *ᵥ s.z - (s.beta : 𝕜) • s.prev -
      (preconditionedLanczosAlpha A s : 𝕜) • s.cur) =
      (Cᴴ * A * C) *ᵥ t.cur - (t.beta : 𝕜) • t.prev -
        (lanczosAlpha (Cᴴ * A * C) t : 𝕜) • t.cur := by
    rw [hz, hb, hα, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hc, hp, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  subst hM
  dsimp only [preconditionedLanczosStep, lanczosStep]
  rw [← quadForm_def, quadForm_mul_conjTranspose_self, RCLike.ofReal_re,
    Real.sqrt_sq (norm_nonneg _), hw]
  refine ⟨?_, ?_, hc, rfl⟩
  · rw [Matrix.mulVec_smul, hw, RCLike.ofReal_inv]
  · rw [← Matrix.mulVec_mulVec _ C Cᴴ, hw, Matrix.mulVec_smul, RCLike.ofReal_inv]

omit [DecidableEq n] in
/-- The correspondence, by one joint induction. -/
private theorem preconditionedLanczosState_corr {C : Matrix n n 𝕜} (hM : M = C * Cᴴ)
    (b : n → 𝕜) (j : ℕ) :
    Cᴴ *ᵥ (preconditionedLanczosState A M b j).cur =
        (lanczosState (Cᴴ * A * C) (Cᴴ *ᵥ b) j).cur ∧
      (preconditionedLanczosState A M b j).z =
        C *ᵥ (lanczosState (Cᴴ * A * C) (Cᴴ *ᵥ b) j).cur ∧
      Cᴴ *ᵥ (preconditionedLanczosState A M b j).prev =
        (lanczosState (Cᴴ * A * C) (Cᴴ *ᵥ b) j).prev ∧
      (preconditionedLanczosState A M b j).beta =
        (lanczosState (Cᴴ * A * C) (Cᴴ *ᵥ b) j).beta := by
  induction j with
  | zero =>
    subst hM
    dsimp only [preconditionedLanczosState, lanczosState]
    rw [← quadForm_def, quadForm_mul_conjTranspose_self, RCLike.ofReal_re,
      Real.sqrt_sq (norm_nonneg _)]
    refine ⟨?_, ?_, Matrix.mulVec_zero _, rfl⟩
    · rw [Matrix.mulVec_smul, RCLike.ofReal_inv]
    · rw [← Matrix.mulVec_mulVec _ C Cᴴ, Matrix.mulVec_smul, RCLike.ofReal_inv]
  | succ j ih =>
    obtain ⟨hc, hz, hp, hb⟩ := ih
    exact preconditionedLanczosStep_corr hM hc hz hp hb

omit [DecidableEq n] in
/-- The preconditioned vectors are $\mathbf{C}$ times the split Lanczos vectors:
$\mathbf{z}_j = \mathbf{C}\hat{\mathbf{q}}_j$, for every $\mathbf{A}$ and every $\mathbf{C}$
with $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$. -/
theorem preconditionedLanczosState_z_eq_mulVec {C : Matrix n n 𝕜} (hM : M = C * Cᴴ)
    (b : n → 𝕜) (j : ℕ) :
    (preconditionedLanczosState A M b j).z =
      C *ᵥ (lanczosState (Cᴴ * A * C) (Cᴴ *ᵥ b) j).cur :=
  (preconditionedLanczosState_corr hM b j).2.1

omit [DecidableEq n] in
/-- The unpreconditioned vectors map to the split Lanczos vectors under $\mathbf{C}^{\mathsf{H}}$:
$\mathbf{C}^{\mathsf{H}}\mathbf{v}_j = \hat{\mathbf{q}}_j$. -/
theorem conjTranspose_mulVec_preconditionedLanczosState_cur {C : Matrix n n 𝕜} (hM : M = C * Cᴴ)
    (b : n → 𝕜) (j : ℕ) :
    Cᴴ *ᵥ (preconditionedLanczosState A M b j).cur =
      (lanczosState (Cᴴ * A * C) (Cᴴ *ᵥ b) j).cur :=
  (preconditionedLanczosState_corr hM b j).1

omit [DecidableEq n] in
/-- The previous vectors correspond likewise: $\mathbf{C}^{\mathsf{H}}\mathbf{v}_{j-1} =
\hat{\mathbf{q}}_{j-1}$. -/
theorem conjTranspose_mulVec_preconditionedLanczosState_prev {C : Matrix n n 𝕜}
    (hM : M = C * Cᴴ) (b : n → 𝕜) (j : ℕ) :
    Cᴴ *ᵥ (preconditionedLanczosState A M b j).prev =
      (lanczosState (Cᴴ * A * C) (Cᴴ *ᵥ b) j).prev :=
  (preconditionedLanczosState_corr hM b j).2.2.1

omit [DecidableEq n] in
/-- The off-diagonal coefficients agree: $\beta_j = \hat\beta_j$. -/
theorem preconditionedLanczosState_beta_eq {C : Matrix n n 𝕜} (hM : M = C * Cᴴ) (b : n → 𝕜)
    (j : ℕ) :
    (preconditionedLanczosState A M b j).beta = (lanczosState (Cᴴ * A * C) (Cᴴ *ᵥ b) j).beta :=
  (preconditionedLanczosState_corr hM b j).2.2.2

omit [DecidableEq n] in
/-- The diagonal coefficients agree: $\alpha_j = \hat\alpha_j$. -/
theorem preconditionedLanczosAlpha_eq {C : Matrix n n 𝕜} (hM : M = C * Cᴴ) (b : n → 𝕜)
    (j : ℕ) :
    preconditionedLanczosAlpha A (preconditionedLanczosState A M b j) =
      lanczosAlpha (Cᴴ * A * C) (lanczosState (Cᴴ * A * C) (Cᴴ *ᵥ b) j) :=
  preconditionedLanczosAlpha_eq_of (preconditionedLanczosState_z_eq_mulVec hM b j)
    (conjTranspose_mulVec_preconditionedLanczosState_prev hM b j)
    (preconditionedLanczosState_beta_eq hM b j)

/-- **The preconditioned recurrence is the split recurrence**: for Hermitian $\mathbf{A}$ and any
$\mathbf{C}$ with $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$, the computed
$\mathbf{z}_j$ are $\mathbf{C}\mathbf{q}_j$ for the canonical Lanczos basis of
$\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}$ from $\mathbf{C}^{\mathsf{H}}\mathbf{b}$, every $q$,
with no breakdown hypothesis and no invertibility of $\mathbf{C}$: the matrix of the
$\mathbf{z}_j$ computed by $q$ steps from $\mathbf{b}$ is
$\mathbf{C}\,\mathsf{arnoldiMatrix}(\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C},
\mathbf{C}^{\mathsf{H}}\mathbf{b}, q)$.
[Greenbaum1997, Chapter 8, p. 121, Preconditioned Lanczos Algorithm].
Result: preconditioned-lanczos-recurrence -/
theorem _root_.Matrix.IsHermitian.preconditionedLanczosMatrix_eq (hA : A.IsHermitian)
    {C : Matrix n n 𝕜} (hM : M = C * Cᴴ) (b : n → 𝕜) (q : ℕ) :
    preconditionedLanczosMatrix A M b q = C * arnoldiMatrix (Cᴴ * A * C) (Cᴴ *ᵥ b) q := by
  rw [← (Matrix.isHermitian_conjTranspose_mul_mul C hA).lanczosMatrix_eq_arnoldiMatrix]
  ext i j
  change (preconditionedLanczosState A M b j).z i = _
  rw [preconditionedLanczosState_z_eq_mulVec hM]
  rfl

/-- **The preconditioned recurrence computes the split tridiagonal matrix**: for Hermitian
$\mathbf{A}$, any $\mathbf{C}$ with $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$ (no
invertibility), every $q$ and no breakdown hypothesis, the tridiagonal matrix computed by $q$
steps of the preconditioned recurrence from $\mathbf{b}$ is
$\hat{\mathbf{Q}}^{\mathsf{H}}(\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C})\hat{\mathbf{Q}}$ for
the canonical basis $\hat{\mathbf{Q}} = \mathsf{arnoldiMatrix}(\mathbf{C}^{\mathsf{H}}\mathbf{A}
\mathbf{C}, \mathbf{C}^{\mathsf{H}}\mathbf{b}, q)$ of the split system. The tridiagonal form of
`Matrix.IsHermitian.preconditionedLanczosMatrix_eq`.
Result: preconditioned-lanczos-recurrence -/
theorem _root_.Matrix.IsHermitian.preconditionedLanczosTridiagonal_eq (hA : A.IsHermitian)
    {C : Matrix n n 𝕜} (hM : M = C * Cᴴ) (b : n → 𝕜) (q : ℕ) :
    preconditionedLanczosTridiagonal A M b q =
      (arnoldiMatrix (Cᴴ * A * C) (Cᴴ *ᵥ b) q)ᴴ * (Cᴴ * A * C) *
        arnoldiMatrix (Cᴴ * A * C) (Cᴴ *ᵥ b) q := by
  rw [← (Matrix.isHermitian_conjTranspose_mul_mul C hA).lanczosTridiagonal_eq]
  ext i j
  simp only [preconditionedLanczosTridiagonal, lanczosTridiagonal, Matrix.of_apply,
    preconditionedLanczosAlpha_eq hM, preconditionedLanczosState_beta_eq hM]

/-- The computed vectors span the preconditioned Krylov space
$\mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{b})$, for Hermitian $\mathbf{A}$ and
positive definite $\mathbf{M}$. -/
theorem _root_.Matrix.IsHermitian.range_preconditionedLanczosMatrix (hA : A.IsHermitian)
    (hM : M.PosDef) (b : n → 𝕜) (q : ℕ) :
    LinearMap.range (preconditionedLanczosMatrix A M b q).mulVecLin =
      krylovSpace (M * A) (M *ᵥ b) q := by
  obtain ⟨C, -, hMC⟩ := hM.exists_isUnit_eq_mul_conjTranspose
  rw [hA.preconditionedLanczosMatrix_eq hMC, Matrix.mulVecLin_mul, LinearMap.range_comp,
    range_arnoldiMatrix, hMC, show C * Cᴴ * A = C * (Cᴴ * A) from Matrix.mul_assoc _ _ _,
    ← Matrix.mulVec_mulVec b C Cᴴ, krylovSpace_mul_mulVec]

/-- Breakdown of the preconditioned recurrence, vectors: for Hermitian $\mathbf{A}$ and any
$\mathbf{C}$ with $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$, from the grade $\nu$ of
$\mathbf{C}^{\mathsf{H}}\mathbf{b}$ for the split matrix
$\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}$ on, $\mathbf{z}_l = \mathbf{0}$. -/
theorem _root_.Matrix.IsHermitian.preconditionedLanczosState_z_eq_zero_of_le (hA : A.IsHermitian)
    {C : Matrix n n 𝕜} (hM : M = C * Cᴴ) (b : n → 𝕜) {l : ℕ}
    (hl : krylovGrade (Cᴴ * A * C) (Cᴴ *ᵥ b) ≤ l) :
    (preconditionedLanczosState A M b l).z = 0 := by
  have h := congrArg (fun Q => Q.col (Fin.last l))
    ((Matrix.isHermitian_conjTranspose_mul_mul C hA).lanczosMatrix_eq_arnoldiMatrix (Cᴴ *ᵥ b)
      (l + 1))
  simp only [arnoldiMatrix_col_last_eq_zero_iff.mpr hl] at h
  rw [preconditionedLanczosState_z_eq_mulVec hM,
    show (lanczosState (Cᴴ * A * C) (Cᴴ *ᵥ b) l).cur = 0 from h, Matrix.mulVec_zero]

/-- Breakdown of the preconditioned recurrence, coefficients: for Hermitian $\mathbf{A}$ and
any $\mathbf{C}$ with $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$, from the grade $\nu$ of
$\mathbf{C}^{\mathsf{H}}\mathbf{b}$ for $\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C}$ on,
$\beta_l = 0$. -/
theorem _root_.Matrix.IsHermitian.preconditionedLanczosState_beta_eq_zero_of_le
    (hA : A.IsHermitian) {C : Matrix n n 𝕜} (hM : M = C * Cᴴ) (b : n → 𝕜) {l : ℕ}
    (hl : krylovGrade (Cᴴ * A * C) (Cᴴ *ᵥ b) ≤ l) :
    (preconditionedLanczosState A M b l).beta = 0 := by
  rcases l with _ | l
  · rfl
  · rw [preconditionedLanczosState_beta_eq hM,
      (Matrix.isHermitian_conjTranspose_mul_mul C hA).lanczosState_beta_eq_zero_iff]
    exact hl

end NLAlib
