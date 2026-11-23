/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Verified
public import NLAlib.Eigensolvers.Schur.Completion
public import NLAlib.Matrix.Perturbation.ApproximateEigendecomposition

/-!
# The generic eigensolver: a Schur solver and an eigenvector stage

`NLAlib.Schur.eigSolverWith Solve Ev` runs a Schur solver `Solve` and then an eigenvector stage
`Ev` (`NLAlib.Schur.EigenvectorStageContract`) on its own words, and sets the flag to $1$ if the
stage flagged. If the Schur solver stores, except with probability $\varphi$, a Schur output of a
regularized matrix $\mathbf{X}$ with $s^{-1}\mathbf{X}$ of the class $(B, \Gamma)$
(`NLAlib.Schur.RegularizedSchurOutput`), the eigensolver stores, except with probability
$\varphi$, an approximate eigendecomposition (`NLAlib.Schur.EigOutput`): column and matrix
residuals, $\kappa(\widehat{\mathbf{V}}) \le 2\sqrt{n + 1}\,B$, the backward form and the gaps of
the diagonal (`NLAlib.eigDecompOf_of_schur`). If the Schur solver is verified on every tape, the
flag $0$ certifies the residual part on every tape (`NLAlib.eigResidualOf_of_schur`).

## Main definitions

* `NLAlib.Schur.eigSolverWith`: the program `[N, nr, nq, k, F, T, ne] (A, P, Pe) → (A, U, V, Fl)`.
* `NLAlib.Schur.EigSolverInput`, `NLAlib.Schur.eigFp`, `NLAlib.Schur.EigResidual`,
  `NLAlib.Schur.EigOutput`: its input memory, footprint and outputs.

## Main results

* `NLAlib.Schur.eigSolverWith_pwrites`: the Monte Carlo composition.
* `NLAlib.Schur.eigSolverWith_writes_residual`: the verified composition on every tape.
* `NLAlib.Schur.eigSolverWith_terminates`: termination on every tape.
* `NLAlib.Schur.size_stmtCost_eigSolverWith_le`: the static count.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Schur

open Ops MeasureTheory

variable {O Q : Type}

/-! ### Memories and outputs -/

/-- The input of the eigensolver: the pipeline's input for the solver words `qs` at `P`
(`NLAlib.Schur.SchurPipelineInput`), the stage's words `qe` at `Pe`, and room for $\mathbf{V}$;
the six blocks live and pairwise apart. -/
def EigSolverInput {n : ℕ} (qs qe : List ℝ) (a p pe uo v f : ℕ × ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  SchurPipelineInput qs a p uo f A μ ∧ μ.Live [pe, v] ∧
    μ.Room [pe, v] [qe.length, 2 * ((n + 1) * (n + 1))] ∧
    Fp.Apart [a, p, uo, f, pe, v] [2 * ((n + 1) * (n + 1)), qs.length,
      2 * ((n + 1) * (n + 1)), 1, qe.length, 2 * ((n + 1) * (n + 1))] ∧
    μ.store.readBlock pe.1 pe.2 qe.length = some qe

/-- The blocks the eigensolver writes: those of the Schur solver and $\mathbf{V}$. -/
def eigFp (n : ℕ) (a uo v f : ℕ × ℕ) : Fp :=
  schurFp n a uo f ⊔ Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1)))

/-- **The residual part of an eigendecomposition output**: stored $\widehat{\mathbf{T}}$ at `a`
and $\widehat{\mathbf{V}}$ at `v` with `NLAlib.EigResidualOf` against $\mathbf{A}$. -/
def EigResidual {n : ℕ} (a v : ℕ × ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eC eM c : ℝ) (μ' : Mem ℝ) : Prop :=
  ∃ T V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a T μ'.store ∧
    HoldsMatrix v V μ'.store ∧ EigResidualOf A T V eC eM c

/-- **An eigendecomposition output**: the flag $0$ and stored $\widehat{\mathbf{T}}$ at `a` and
$\widehat{\mathbf{V}}$ at `v` with `NLAlib.EigDecompOf` against $\mathbf{A}$. -/
def EigOutput {n : ℕ} (a v f : ℕ × ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eC eM c eE K g : ℝ) (μ' : Mem ℝ) : Prop :=
  μ'.store.get f.1 f.2 = some 0 ∧ ∃ T V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    HoldsMatrix a T μ'.store ∧ HoldsMatrix v V μ'.store ∧ EigDecompOf A T V eC eM c eE K g

/-- The columns of a matrix are continuous in it. -/
private theorem continuous_toLp_col {n : ℕ} (j : Fin (n + 1)) :
    Continuous fun V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => WithLp.toLp 2 (V.col j) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply_apply i j)

/-- The pairs $(\mathbf{T}, \mathbf{V})$ with the residual part of an eigendecomposition of
$\mathbf{A}$ form a measurable set. -/
private theorem measurableSet_eigResidualOf {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eC eM c : ℝ) :
    MeasurableSet {p : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ × Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ |
      EigResidualOf A p.1 p.2 eC eM c} := by
  simp only [EigResidualOf, Set.ofPred_and, Set.ofPred_forall]
  refine (MeasurableSet.iInter fun j => ?_).inter ((MeasurableSet.iInter fun j => ?_).inter ?_)
  · exact measurableSet_le (((continuous_toLp_col j).comp continuous_snd).norm.sub
      continuous_const).abs.measurable measurable_const
  · refine measurableSet_le ?_ ?_
    · exact ((PiLp.continuous_toLp 2 _).comp ((continuous_const.sub
        (((continuous_apply_apply j j).comp continuous_fst).smul continuous_const)).matrix_mulVec
        (continuous_pi fun i => (continuous_apply_apply i j).comp continuous_snd))).norm.measurable
    · exact (continuous_const.mul ((continuous_toLp_col j).comp continuous_snd).norm).measurable
  · refine measurableSet_le ?_ ?_
    · exact (continuous_specNorm.comp ((continuous_const.matrix_mul continuous_snd).sub
        (continuous_snd.matrix_mul (Continuous.matrix_diagonal (continuous_pi fun i =>
          continuous_fst.matrix_elem i i))))).measurable
    · exact (continuous_const.mul (continuous_specNorm.comp continuous_snd)).measurable

/-- The pairs $(\mathbf{T}, \mathbf{V})$ with an eigendecomposition of $\mathbf{A}$ form a
measurable set. -/
private theorem measurableSet_eigDecompOf {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eC eM c eE K g : ℝ) :
    MeasurableSet {p : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ × Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ |
      EigDecompOf A p.1 p.2 eC eM c eE K g} := by
  simp only [EigDecompOf, Set.ofPred_and]
  refine (measurableSet_eigResidualOf A eC eM c).inter (MeasurableSet.inter ?_
    (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)))
  · have e : {p : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ × Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ |
        IsUnit p.2} = {p | p.2.det = 0}ᶜ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Matrix.isUnit_iff_isUnit_det,
        isUnit_iff_ne_zero]
    rw [e]
    exact (measurableSet_eq_fun (continuous_snd.matrix_det).measurable measurable_const).compl
  · refine measurableSet_le ?_ measurable_const
    simp only [pseudoConditionNumber]
    exact (continuous_specNorm.comp continuous_snd).measurable.mul
      (continuous_specNorm.measurable.comp (measurable_pinv.comp measurable_snd))
  · refine measurableSet_le ?_ measurable_const
    exact continuous_specNorm.measurable.comp (((measurable_snd.matrix_mul
      (Continuous.matrix_diagonal (continuous_pi fun i =>
        continuous_fst.matrix_elem i i)).measurable).matrix_mul
      measurable_snd.matrix_inv).matrix_sub measurable_const)
  · simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ne_eq, not_false_eq_true]
      have hd : ∀ l, Continuous fun p : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ ×
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => p.1 l l :=
        fun l => continuous_fst.matrix_elem l l
      have hm : Measurable fun p : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ ×
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => ‖p.1 i i - p.1 j j‖ :=
        ((hd i).sub (hd j)).norm.measurable
      exact MeasurableSet.iInter fun _ => measurableSet_le measurable_const hm

/-- A stored matrix: the words are initialised and the matrix is the one read. -/
private theorem holdsMatrix_iff {n : ℕ} (b : ℕ × ℕ) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (s : Store ℝ) :
    HoldsMatrix b X s ↔ (∀ j < 2 * ((n + 1) * (n + 1)), (s.get b.1 (b.2 + j)).isSome) ∧
      X = storedMatrix b (n + 1) (n + 1) s := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, h.eq_storedMatrix⟩
    rw [Store.get_of_readBlock h hj 0]; rfl
  · rintro ⟨h, rfl⟩
    exact holdsMatrix_storedMatrix h

/-- **The memories holding an eigendecomposition output form a measurable set.** -/
theorem measurableSet_eigOutput {n : ℕ} (a v f : ℕ × ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (eC eM c eE K g : ℝ) :
    MeasurableSet {μ' : Mem ℝ | EigOutput a v f A eC eM c eE K g μ'} := by
  set Tm := fun μ' : Mem ℝ => storedMatrix a (n + 1) (n + 1) μ'.store
  set Vm := fun μ' : Mem ℝ => storedMatrix v (n + 1) (n + 1) μ'.store
  have e : {μ' : Mem ℝ | EigOutput a v f A eC eM c eE K g μ'} =
      {μ' | μ'.store.get f.1 f.2 = some 0} ∩
        ({μ' | ∀ j < 2 * ((n + 1) * (n + 1)), (μ'.store.get a.1 (a.2 + j)).isSome} ∩
        ({μ' | ∀ j < 2 * ((n + 1) * (n + 1)), (μ'.store.get v.1 (v.2 + j)).isSome} ∩
          (fun μ' => (Tm μ', Vm μ')) ⁻¹' {p | EigDecompOf A p.1 p.2 eC eM c eE K g})) := by
    ext μ'
    simp only [EigOutput, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, holdsMatrix_iff]
    constructor
    · rintro ⟨hf, T, V, ⟨ha, rfl⟩, ⟨hv, rfl⟩, h⟩
      exact ⟨hf, ha, hv, h⟩
    · rintro ⟨hf, ha, hv, h⟩
      exact ⟨hf, _, _, ⟨ha, rfl⟩, ⟨hv, rfl⟩, h⟩
  rw [e]
  exact (Mem.measurableSet_get_eq f 0).inter ((ShiftedQR.measurableSet_forall_isSome a _).inter
    ((ShiftedQR.measurableSet_forall_isSome v _).inter
      (((ShiftedQR.measurable_storedMatrix a _ _).prodMk
        (ShiftedQR.measurable_storedMatrix v _ _)) (measurableSet_eigDecompOf A eC eM c eE K g))))

/-- **The memories holding the residual part of an eigendecomposition form a measurable set.** -/
theorem measurableSet_eigResidual {n : ℕ} (a v : ℕ × ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (eC eM c : ℝ) :
    MeasurableSet {μ' : Mem ℝ | EigResidual a v A eC eM c μ'} := by
  set Tm := fun μ' : Mem ℝ => storedMatrix a (n + 1) (n + 1) μ'.store
  set Vm := fun μ' : Mem ℝ => storedMatrix v (n + 1) (n + 1) μ'.store
  have e : {μ' : Mem ℝ | EigResidual a v A eC eM c μ'} =
      {μ' | ∀ j < 2 * ((n + 1) * (n + 1)), (μ'.store.get a.1 (a.2 + j)).isSome} ∩
        ({μ' | ∀ j < 2 * ((n + 1) * (n + 1)), (μ'.store.get v.1 (v.2 + j)).isSome} ∩
          (fun μ' => (Tm μ', Vm μ')) ⁻¹' {p | EigResidualOf A p.1 p.2 eC eM c}) := by
    ext μ'
    simp only [EigResidual, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      holdsMatrix_iff]
    constructor
    · rintro ⟨T, V, ⟨ha, rfl⟩, ⟨hv, rfl⟩, h⟩
      exact ⟨ha, hv, h⟩
    · rintro ⟨ha, hv, h⟩
      exact ⟨_, _, ⟨ha, rfl⟩, ⟨hv, rfl⟩, h⟩
  rw [e]
  exact (ShiftedQR.measurableSet_forall_isSome a _).inter
    ((ShiftedQR.measurableSet_forall_isSome v _).inter
      (((ShiftedQR.measurable_storedMatrix a _ _).prodMk
        (ShiftedQR.measurable_storedMatrix v _ _)) (measurableSet_eigResidualOf A eC eM c)))

/-! ### The program -/

section Program

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The eigensolver** with a Schur solver `Solve` (`[N, nr, nq, k, F, T] (A, P) → (A, U, Fl)`)
and an eigenvector stage `Ev` (`[N, ne] (T, U, Pe) → (V, G)`): run the solver, then the stage on
the stored pair and its own words `Pe`, and set the flag to $1$ if the stage's flag is positive.
The interface is `[N, nr, nq, k, F, T, ne] (A, P, Pe) → (A, U, V, Fl)`.
Algorithm: dense-eigendecomposition -/
def eigSolverWith (Solve Ev : Stmt O Q) : Stmt O Q :=
  ops% [N, nr, nq, k, F, T, ne] (A, P, Pe) → (A, U, V, Fl) {
    let G ← alloc 1;
    run Solve [N, nr, nq, k, F, T] (A, P, A, U, Fl);
    run Ev [N, ne] (A, U, Pe, V, G);
    if (Has.inj CmpTst.isPos) [] (G) {
      call (Has.inj IndexOp.lit) [1] () → (Fl)
    } else { skip }
  }

end Program

/-! ### The norm of the triangular factor -/

/-- A factor with $\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e < 1$ is bounded
below on products: $\sqrt{1 - e}\,\|\mathbf{M}\|_2 \le \|\mathbf{U}\mathbf{M}\|_2$. -/
private theorem sqrt_mul_specNorm_le_specNorm_mul {n : ℕ}
    {U M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : ℝ} (hU : specNorm (Uᴴ * U - 1) ≤ e)
    (he : e < 1) : √(1 - e) * specNorm M ≤ specNorm (U * M) := by
  have hs : 0 < √(1 - e) := Real.sqrt_pos.mpr (by linarith)
  rw [← le_div_iff₀' hs]
  refine (specNorm_le_iff (div_nonneg (specNorm_nonneg _) hs.le)).mpr fun x => ?_
  have h1 := sqrt_one_sub_mul_norm_le_norm_mulVec hU he.le (M *ᵥ x)
  have h2 := norm_toLp_mulVec_le (U * M) x
  rw [← Matrix.mulVec_mulVec] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hs]
  linarith

/-- $(1 - e)\|\mathbf{T}\|_2 \le \|\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_2$ for
$\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e < 1$. -/
private theorem one_sub_mul_specNorm_le {n : ℕ} {U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : ℝ} (hU : specNorm (Uᴴ * U - 1) ≤ e) (he : e < 1) :
    (1 - e) * specNorm T ≤ specNorm (U * T * Uᴴ) := by
  have h1 := sqrt_mul_specNorm_le_specNorm_mul (M := T * Uᴴ) hU he
  have h2 := sqrt_mul_specNorm_le_specNorm_mul (M := Tᴴ) hU he
  have e1 : specNorm (T * Uᴴ) = specNorm (U * Tᴴ) := by
    rw [← specNorm_conjTranspose (T * Uᴴ), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  rw [specNorm_conjTranspose] at h2
  rw [e1, ← mul_assoc] at h1
  have hs := Real.mul_self_sqrt (show 0 ≤ 1 - e by linarith)
  have hs0 := Real.sqrt_nonneg (1 - e)
  calc (1 - e) * specNorm T = √(1 - e) * (√(1 - e) * specNorm T) := by rw [← mul_assoc, hs]
    _ ≤ √(1 - e) * specNorm (U * Tᴴ) := mul_le_mul_of_nonneg_left h2 hs0
    _ ≤ _ := h1

/-- **The diagonal gaps exceed the floor gap**: from a Schur output of a regularized matrix with
$e_R + e_X \le 1/2$, $e_U \le 1/8$, gaps $\lvert t_{ii} - t_{jj}\rvert \ge
\tfrac78c_1\Gamma\|\mathbf{A}\|_2$, $\mathbf{A} \ne 0$ and $16g_0\sqrt{n + 1} < 7c_1\Gamma$, the
gaps exceed $g_0\|\mathbf{T}\|_{\mathsf F}$. -/
private theorem gap_lt_of_schur {n : ℕ} {A X U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {eR eX eU c₁ Γ g₀ : ℝ} (hU : specNorm (Uᴴ * U - 1) ≤ eU)
    (hAX : specNorm (A - X) ≤ eR * specNorm A)
    (hXT : specNorm (X - U * T * Uᴴ) ≤ eX * specNorm A) (he : eR + eX ≤ 1 / 2)
    (heU : eU ≤ 1 / 8) (hA : A ≠ 0) (hc₁ : 0 < c₁) (hΓ : 0 < Γ)
    (hfloor : 16 * g₀ * √((n : ℝ) + 1) < 7 * c₁ * Γ)
    (hgap : ∀ i j, i ≠ j → 7 / 8 * c₁ * Γ * specNorm A ≤ ‖T i i - T j j‖) :
    ∀ i j, i ≠ j → g₀ * frobNorm T < ‖T i i - T j j‖ := by
  intro i j hij
  have hA0 : 0 < specNorm A := by
    rcases (specNorm_nonneg A).lt_or_eq with h | h
    · exact h
    · exact absurd (specNorm_eq_zero_iff.mp h.symm) hA
  have hUTU : specNorm (U * T * Uᴴ) ≤ 3 / 2 * specNorm A := by
    have h1 := specNorm_sub_le (A - X) (U * T * Uᴴ - X)
    have h2 : specNorm (U * T * Uᴴ - X) = specNorm (X - U * T * Uᴴ) := by
      rw [← specNorm_neg, neg_sub]
    have h3 := specNorm_add_le A (U * T * Uᴴ - A)
    rw [add_sub_cancel] at h3
    have h4 : specNorm (U * T * Uᴴ - A) ≤ specNorm (A - X) + specNorm (X - U * T * Uᴴ) := by
      rw [show U * T * Uᴴ - A = -((A - X) + (X - U * T * Uᴴ)) by abel, specNorm_neg]
      exact specNorm_add_le _ _
    nlinarith
  have hT := one_sub_mul_specNorm_le (T := T) hU (by linarith)
  have hTn : specNorm T ≤ 12 / 7 * specNorm A := by nlinarith [specNorm_nonneg T]
  have hF : frobNorm T ≤ √((n : ℝ) + 1) * specNorm T := by
    simpa using frobNorm_le_sqrt_card_mul_specNorm T
  have hsq := Real.sqrt_nonneg ((n : ℝ) + 1)
  have hg := hgap i j hij
  rcases le_or_gt g₀ 0 with hg0 | hg0
  · have : g₀ * frobNorm T ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hg0 (frobNorm_nonneg T)
    have : 0 < 7 / 8 * c₁ * Γ * specNorm A := by positivity
    linarith
  · have h1 : g₀ * frobNorm T ≤ g₀ * √((n : ℝ) + 1) * (12 / 7 * specNorm A) := by
      calc g₀ * frobNorm T ≤ g₀ * (√((n : ℝ) + 1) * specNorm T) :=
            mul_le_mul_of_nonneg_left hF hg0.le
        _ ≤ g₀ * (√((n : ℝ) + 1) * (12 / 7 * specNorm A)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTn hsq) hg0.le
        _ = _ := by ring
    have h2 : g₀ * √((n : ℝ) + 1) * (12 / 7 * specNorm A) <
        7 / 8 * c₁ * Γ * specNorm A := by
      have h3 := mul_lt_mul_of_pos_right hfloor hA0
      have h4 : 0 < c₁ * Γ * specNorm A := by positivity
      nlinarith
    linarith

/-! ### The compositions -/

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The Monte Carlo composition of the eigensolver.** On a scalar machine with the standard
model, index literals, exact natural literals up to $n + 1$ and exact comparisons, a measurable
interpretation reading the tape only in its windows, let `Solve` store, except with probability
$\varphi$, a Schur output with its regularized matrix $\mathbf{X}$, $s^{-1}\mathbf{X}$ of the class
$(B, \Gamma)$ (`NLAlib.Schur.RegularizedSchurOutput` with the errors $e_R$, $e_X$, $e_U$), and let
`Ev` meet `NLAlib.Schur.EigenvectorStageContract` with $(c_{R,0}, c_R, c_V, c_N, g_0)$ at the
order $n + 1$ and the words `qe`. With $\eta$ = `eigEta n eX eU cR₀ cV` and $c$ =
`eigColTol n eU cV cN`, let $\Gamma > 0$, $B \ge 1$, $c_1 > 0$, $e_R + e_X \le 1/2$,
$e_U \le 1/8$, $c \le 1/8$, $16g_0\sqrt{n + 1} < 7c_1\Gamma$,
$e_X + 6e_U \le c_1\Gamma/(16(n + 1)B)$ and $8\sqrt{n + 1}\,B\eta \le c_1\Gamma$. Then from every
input of the eigensolver, except with probability $\varphi$, the run writes only $\mathbf{A}$,
$\widehat{\mathbf{U}}$, $\widehat{\mathbf{V}}$ and the flag, and stores a Schur output with the
errors $(e_R + e_X, e_U)$ and an eigendecomposition output (`NLAlib.Schur.EigOutput`): column
residuals $e_R + \eta$, matrix residual $e_R + \sqrt{n + 1}\,\eta$, column tolerance $c$,
backward form $e_R + 2(n + 1)B\eta$, $\kappa \le 2\sqrt{n + 1}\,B$ and gaps
$\tfrac78c_1\Gamma\|\mathbf{A}\|_2$. No printed source. -/
theorem eigSolverWith_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {Solve Ev : Stmt O Q} {nr nq k F T : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {a p pe uo v f : ℕ × ℕ} {qs qe : List ℝ} {B Γ c₁ c₂ eR eX eU φ cR₀ cR cV cN g₀ : ℝ}
    (hSolve : PWrites law I Solve (Env.frame [n + 1, nr, nq, k, F, T] [a, p, a, uo, f])
      (schurFp n a uo f) (SchurPipelineInput qs a p uo f A)
      (RegularizedSchurOutput (IsConditionedDiagonalizable B Γ) a uo f A c₁ c₂ eR eX eU) φ)
    (hEv : EigenvectorStageContract cR₀ cR cV cN g₀ (n + 1) qe Ev I)
    (hΓ : 0 < Γ) (hB : 1 ≤ B) (hc₁ : 0 < c₁) (he : eR + eX ≤ 1 / 2) (heU : eU ≤ 1 / 8)
    (hc : eigColTol n eU cV cN ≤ 1 / 8)
    (hfloor : 16 * g₀ * √((n : ℝ) + 1) < 7 * c₁ * Γ)
    (hsep : eX + 6 * eU ≤ c₁ * Γ / (16 * (n + 1) * B))
    (hκ : 8 * √((n : ℝ) + 1) * B * eigEta n eX eU cR₀ cV ≤ c₁ * Γ) :
    PWrites law I (eigSolverWith Solve Ev)
      (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (EigSolverInput qs qe a p pe uo v f A)
      (fun μ' => SchurOutput a uo f A (eR + eX) eU μ' ∧
        EigOutput a v f A (eR + eigEta n eX eU cR₀ cV)
          (eR + √((n : ℝ) + 1) * eigEta n eX eU cR₀ cV) (eigColTol n eU cV cN)
          (eR + 2 * ((n : ℝ) + 1) * B * eigEta n eX eU cR₀ cV)
          (2 * √((n : ℝ) + 1) * B) (7 / 8 * c₁ * Γ) μ') φ := by
  sorry

/-- **The verified composition of the eigensolver, on every tape.** On a scalar machine with the
standard model, index literals, exact natural literals up to $n + 1$ and exact comparisons, let
`Solve` store on every tape a pair at `a`, `uo` and, if its flag is $0$, a Schur output with the
errors $(e_A, e_U)$ (as `NLAlib.Schur.verifiedSchurWith` does), and let `Ev` meet
`NLAlib.Schur.EigenvectorStageContract` with $(c_{R,0}, c_R, c_V, c_N, g_0)$ at the order $n + 1$
and the words `qe`. With $\eta$ = `eigEta n eA eU cR₀ cV` and $c$ = `eigColTol n eU cV cN`, let
$e_A \le 1/2$, $e_U \le 1/8$ and $c \le 1/8$. Then from every input of the eigensolver, on every
tape, the run writes only $\mathbf{A}$, $\widehat{\mathbf{U}}$, $\widehat{\mathbf{V}}$ and the
flag, and if the flag is $0$ it stores a Schur output and the residual part of an
eigendecomposition (`NLAlib.Schur.EigResidual`): column residuals $\eta$, matrix residual
$\sqrt{n + 1}\,\eta$ and column tolerance $c$. No probability and no hypothesis on $\mathbf{A}$.
No printed source. -/
theorem eigSolverWith_writes_residual {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I) {Solve Ev : Stmt O Q}
    {nr nq k F T : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p pe uo v f : ℕ × ℕ}
    {qs qe : List ℝ} {τ : Tape ℝ} {μ : Mem ℝ} {eA eU cR₀ cR cV cN g₀ : ℝ}
    (hSolve : ∀ τ μ, SchurPipelineInput qs a p uo f A μ →
      Writes .total I τ Solve (Env.frame [n + 1, nr, nq, k, F, T] [a, p, a, uo, f])
        (schurFp n a uo f) (fun μ' => (∃ U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          HoldsSchurPair a uo U T μ'.store) ∧
          (μ'.store.get f.1 f.2 = some 0 → SchurOutput a uo f A eA eU μ')) μ)
    (hEv : EigenvectorStageContract cR₀ cR cV cN g₀ (n + 1) qe Ev I)
    (he : eA ≤ 1 / 2) (heU : eU ≤ 1 / 8) (hc : eigColTol n eU cV cN ≤ 1 / 8)
    (hin : EigSolverInput qs qe a p pe uo v f A μ) :
    Writes .total I τ (eigSolverWith Solve Ev)
      (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 →
        SchurOutput a uo f A eA eU μ' ∧
        EigResidual a v A (eigEta n eA eU cR₀ cV) (√((n : ℝ) + 1) * eigEta n eA eU cR₀ cV)
          (eigColTol n eU cV cN) μ') μ := by
  sorry

/-- **The eigensolver terminates on every tape**: on a scalar machine with index literals and exact
comparisons, if `Solve` terminates on every tape with the accumulator within $e_U$ of orthonormal
(`NLAlib.Schur.TerminatingSchurSolver`) and `Ev` completes
(`NLAlib.Schur.CompletingEigenvectorStage`), then from every input of the eigensolver the run
succeeds on every tape, writes only $\mathbf{A}$, $\widehat{\mathbf{U}}$, $\widehat{\mathbf{V}}$
and the flag, and stores a matrix at `a`, $\widehat{\mathbf{U}}$ within $e_U$ of orthonormal and a
matrix at `v`. -/
theorem eigSolverWith_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hC : IsCmp id I) {Solve Ev : Stmt O Q}
    {nr nq k F T : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p pe uo v f : ℕ × ℕ}
    {qs qe : List ℝ} {eU : ℝ} {μ : Mem ℝ}
    (hSolve : TerminatingSchurSolver eU n [n + 1, nr, nq, k, F, T] qs Solve I)
    (hEv : CompletingEigenvectorStage (n + 1) qe Ev I)
    (hin : EigSolverInput qs qe a p pe uo v f A μ) (τ : Tape ℝ) :
    Writes .total I τ (eigSolverWith Solve Ev)
      (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (fun μ' => SchurOrth (n := n) a uo eU μ' ∧
        ∃ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix v V μ'.store) μ := by
  sorry

/-- **The static count of the eigensolver** with its structural instructions, at zero offsets, is
at most the instrumented counts of the solver and the stage at the offsets the eigensolver passes
to them, plus $128$ for the glue (the flag word, the branch and the frames). -/
theorem size_stmtCost_eigSolverWith_le (Solve Ev : Stmt O Q) (N nr nq k F T ne : ℕ) :
    Count.size (stmtCost (eigSolverWith Solve Ev).instrument
        [N, nr, nq, k, F, T, ne, 0, 0, 0, 0, 0, 0, 0]) ≤
      Count.size (stmtCost Solve.instrument [N, nr, nq, k, F, T, 0, 0, 0, 0, 0]) +
        Count.size (stmtCost Ev.instrument [N, ne, 0, 0, 0, 0, 0]) + 128 := by
  sorry

end Theorems

end NLAlib.Schur
