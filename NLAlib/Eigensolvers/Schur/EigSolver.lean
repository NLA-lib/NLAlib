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

/-- The fifteen disjointness facts of the operands of the eigensolver. -/
theorem eigSolverInput_disj {n : ℕ} {a p uo f pe v : ℕ × ℕ} {qs qe : List ℝ}
    (hap : Fp.Apart [a, p, uo, f, pe, v] [2 * ((n + 1) * (n + 1)), qs.length,
      2 * ((n + 1) * (n + 1)), 1, qe.length, 2 * ((n + 1) * (n + 1))]) :
    Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock p.1 p.2 qs.length) ∧
    Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) ∧
    Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1) ∧
    Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock pe.1 pe.2 qe.length) ∧
    Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1)))) ∧
    Fp.Disj (Store.inBlock p.1 p.2 qs.length)
      (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) ∧
    Fp.Disj (Store.inBlock p.1 p.2 qs.length) (Store.inBlock f.1 f.2 1) ∧
    Fp.Disj (Store.inBlock p.1 p.2 qs.length) (Store.inBlock pe.1 pe.2 qe.length) ∧
    Fp.Disj (Store.inBlock p.1 p.2 qs.length) (Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1)))) ∧
    Fp.Disj (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1) ∧
    Fp.Disj (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock pe.1 pe.2 qe.length) ∧
    Fp.Disj (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1)))) ∧
    Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock pe.1 pe.2 qe.length) ∧
    Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1)))) ∧
    Fp.Disj (Store.inBlock pe.1 pe.2 qe.length)
      (Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1)))) := by
  simpa only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true, and_assoc] using hap

/-- The constants of an eigenvector stage are nonnegative: at the order $1$, with
$\mathbf{U} = \mathbf{I}$ and $\mathbf{T} = \mathbf{0}$, the stage stores $\mathbf{V} = \mathbf{U}$
and a matrix $\mathbf{Y}$ with $\|\mathbf{V} - \mathbf{U}\mathbf{Y}\|_2 \le
c_V\|\mathbf{U}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$ and column norms within $c_N$ of $1$. -/
private theorem nonneg_of_eigenvectorStageContract {I : Interp O Q ℝ} {cR₀ cR cV cN g₀ : ℝ}
    {nmax : ℕ} {ps : List ℝ} {Ev : Stmt O Q}
    (h : EigenvectorStageContract cR₀ cR cV cN g₀ nmax ps Ev I) (hn : 1 ≤ nmax) :
    0 ≤ cV ∧ 0 ≤ cN := by
  let U : Matrix (Fin 1) (Fin 1) ℂ := 1
  let T : Matrix (Fin 1) (Fin 1) ℂ := 0
  let μ : Mem ℝ := ⟨[(matrixWords T).map some, (matrixWords U).map some, ps.map some,
    [none, none], [none]], 0⟩
  have hread : ∀ (b : ℕ) (xs : List ℝ), μ.store[b]? = some (xs.map some) →
      μ.store.readBlock b 0 xs.length = some xs := fun b xs hb =>
    Store.readBlock_eq_some_iff.mpr ⟨rfl, fun j hj => by
      simp only [Store.get, hb, Nat.zero_add, Option.bind_some, List.getElem?_map]
      cases xs[j]? <;> rfl⟩
  have hT : HoldsMatrix (0, 0) T μ.store := by
    simpa [HoldsMatrix] using hread 0 (matrixWords T) rfl
  have hU : HoldsMatrix (1, 0) U μ.store := by
    simpa [HoldsMatrix] using hread 1 (matrixWords U) rfl
  have hps : μ.store.readBlock 2 0 ps.length = some ps := hread 2 ps rfl
  have hw := h (N := 1) (a := (0, 0)) (uo := (1, 0)) (pe := (2, 0)) (v := (3, 0)) (g := (4, 0))
    (tape := fun _ _ => 0) (μ := μ) U T hn ⟨hT, hU⟩ hps
    (by simp [Mem.Live, μ]) (by simp [Mem.Room, Store.len, μ])
    (by
      simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
        and_true]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
        exact Fp.disj_inBlock_of_ne (by omega))
  obtain ⟨m', -, -, V, -, -, h0, htri⟩ := hw
  obtain ⟨⟨Y, hY, hV⟩, -⟩ := htri (fun i j hij => rfl)
  have hVU : V = U := (h0 rfl).1
  have hcN : 0 ≤ cN := (abs_nonneg _).trans (hY 0).1
  refine ⟨?_, hcN⟩
  by_contra hneg
  have hcV : cV < 0 := not_le.mp hneg
  have hUF : 0 < frobNorm U :=
    lt_of_le_of_ne (frobNorm_nonneg U) fun e => one_ne_zero (frobNorm_eq_zero_iff.mp e.symm)
  rcases (frobNorm_nonneg Y).lt_or_eq with hY0 | hY0
  · have h1 : cV * frobNorm U * frobNorm Y < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hcV hUF) hY0
    linarith [specNorm_nonneg (V - U * Y)]
  · have hY00 : Y = 0 := frobNorm_eq_zero_iff.mp hY0.symm
    subst hY00
    rw [hVU, Matrix.mul_zero, sub_zero] at hV
    simp only [frobNorm_zero, mul_zero] at hV
    exact one_ne_zero (specNorm_eq_zero_iff.mp (le_antisymm hV (specNorm_nonneg _)))

/-! ### The tail of the run -/

section Tail

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- The part of the eigensolver after the Schur solver: the stage and the branch on its flag. -/
private def eigTail (Ev : Stmt O Q) : Stmt O Q :=
  (Stmt.frame [.var 0, .var 6] [⟨0, .var 7⟩, ⟨4, .var 11⟩, ⟨2, .var 9⟩, ⟨5, .var 12⟩,
    ⟨7, .const 0⟩] Ev).seq
    (Stmt.ite (Has.inj CmpTst.isPos) [] [⟨7, .const 0⟩]
      (Stmt.call (Has.inj IndexOp.lit) [.const 1] [] [⟨6, .var 13⟩]) .skip)

omit [Has ScalarOp O] in
/-- The eigensolver is the allocation of the stage's flag, the Schur solver and the tail. -/
private theorem eigSolverWith_eq (Solve Ev : Stmt O Q) :
    eigSolverWith Solve Ev = Stmt.allocs [.const 1]
      ((Stmt.frame [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5]
        [⟨0, .var 7⟩, ⟨1, .var 8⟩, ⟨0, .var 7⟩, ⟨4, .var 11⟩, ⟨6, .var 13⟩] Solve).seq
        (eigTail Ev)) := rfl

/-- The memory after the Schur solver, as the tail needs it. -/
private structure EigTailMem (n : ℕ) (qe : List ℝ) (a uo pe v f : ℕ × ℕ) (L : ℕ) (m : Mem ℝ) :
    Prop where
  words : m.store.readBlock pe.1 pe.2 qe.length = some qe
  live : m.Live [a, uo, pe, v, (L, 0)]
  room : m.Room [v, (L, 0)] [2 * ((n + 1) * (n + 1)), 1]
  apart : Fp.Apart [a, uo, pe, v, (L, 0)]
    [2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), qe.length, 2 * ((n + 1) * (n + 1)), 1]
  flag : f.2 < m.store.len f.1
  fa : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1)
  fu : Fp.Disj (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1)
  fv : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1))))
  fL : f.1 ≠ L

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] in
/-- The input of the eigensolver, after the allocation of the flag word and a run writing only
the blocks of the Schur solver, is a memory for the tail. -/
private theorem EigSolverInput.tailMem {n : ℕ} {qs qe : List ℝ} {a p pe uo v f : ℕ × ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {μ : Mem ℝ} {s₁ : Store ℝ} {m₁ : Mem ℝ}
    (hin : EigSolverInput qs qe a p pe uo v f A μ) (hLs : s₁.length = μ.store.length + 1)
    (hL1 : s₁.len μ.store.length = 1) (hBelow : Store.Below μ.store.length μ.store s₁)
    (hfr₁ : s₁.EqOff (schurFp n a uo f) m₁.store) :
    EigTailMem n qe a uo pe v f μ.store.length m₁ := by
  obtain ⟨⟨hl4, hroom4, -, -, -⟩, hlv, hroom, hap, hqe⟩ := hin
  set L := μ.store.length with hLdef
  have hlt : ∀ z ∈ [a, p, uo, f, pe, v], z.1 < L := fun z hz => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hl4 _ (by simp)
    · exact hl4 _ (by simp)
    · exact hl4 _ (by simp)
    · exact hl4 _ (by simp)
    · exact hlv _ (by simp)
    · exact hlv _ (by simp)
  obtain ⟨h12, h13, h14, h15, h16, h23, h24, h25, h26, h34, h35, h36, h45, h46, h56⟩ :=
    eigSolverInput_disj hap
  have hdS : ∀ {G : Fp}, Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) G →
      Fp.Disj (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) G →
      Fp.Disj (Store.inBlock f.1 f.2 1) G → Fp.Disj (schurFp n a uo f) G := fun h1 h2 h3 => by
    simp only [schurFp, Fp.disj_sup_left]; exact ⟨⟨h1, h2⟩, h3⟩
  have hlen₁ : m₁.store.length = L + 1 := hfr₁.length_eq.trans hLs
  have hlen : ∀ b < L, m₁.store.len b = μ.store.len b := fun b hb => by
    rw [hfr₁.len_eq]; exact (hBelow b hb).1
  have hLa : ∀ z ∈ [a, uo, pe, v], ∀ l,
      Fp.Disj (Store.inBlock z.1 z.2 l) (Store.inBlock L 0 1) :=
    fun z hz l => Fp.disj_inBlock_of_ne (by
      have := hlt z (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢; tauto)
      omega)
  refine ⟨hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hdS h15 h35 h45)
      (hBelow.keep (Store.readsOnly_readBlock _ _ _ _) (fun _ _ h => h.1 ▸ hlt pe (by simp)) hqe),
    fun z hz => ?_, ⟨?_, ?_, trivial⟩, ?_, ?_, h14, h34, h46, ?_⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rw [hlen₁]
    rcases hz with h | h | h | h | h <;> rw [h]
    · have := hlt a (by simp); omega
    · have := hlt uo (by simp); omega
    · have := hlt pe (by simp); omega
    · have := hlt v (by simp); omega
    · simp
  · rw [hlen _ (hlt v (by simp))]; exact hroom.2.1
  · rw [hfr₁.len_eq]; simp [hL1]
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨h13, h15, h16, hLa a (by simp) _⟩, ⟨h35, h36, hLa uo (by simp) _⟩,
      ⟨h56, hLa pe (by simp) _⟩, hLa v (by simp) _⟩
  · rw [hlen _ (hlt f (by simp))]
    have := hroom4.2.2.2.1
    omega
  · have := hlt f (by simp); omega

omit [Has ScalarOp O] in
/-- **The tail of the run**: from a memory for the tail, if the stage writes only $\mathbf{V}$ and
its flag and stores a word, the tail writes only the blocks of the eigensolver and scratch, and
ends in `Post` given `Post` after the stage with a flag that is not positive (`hN`), and after the
stage and the literal $1$ in the flag with a positive flag (`hP`). -/
private theorem eigTail_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} (hL : IsIndexLit Mch I)
    (hC : IsCmp id I) {Ev : Stmt O Q} {n L : ℕ} {qe : List ℝ} {a uo pe v f : ℕ × ℕ}
    {ρ : Env} {τ : Tape ℝ} {m₁ : Mem ℝ} {R Post : Mem ℝ → Prop}
    (hd : IExp.evalList ρ.idx [.var 0, .var 6] = some [n + 1, qe.length])
    (ha : Operand.evalList ρ [⟨0, .var 7⟩, ⟨4, .var 11⟩, ⟨2, .var 9⟩, ⟨5, .var 12⟩,
      ⟨7, .const 0⟩] = some [a, uo, pe, v, (L, 0)])
    (hg : Operand.evalList ρ [⟨7, .const 0⟩] = some [(L, 0)])
    (ho : (⟨6, .var 13⟩ : Operand).eval ρ = some f)
    (hm : EigTailMem n qe a uo pe v f L m₁)
    (hEv : Writes .total I τ Ev (Env.frame [n + 1, qe.length] [a, uo, pe, v, (L, 0)])
      (Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock L 0 1) R m₁)
    (hx : ∀ m₂, R m₂ → ∃ x, m₂.store.get L 0 = some x)
    (hN : ∀ m₂ x, m₁.store.EqOff
        (Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock L 0 1) m₂.store →
      R m₂ → m₂.store.get L 0 = some x → ¬ 0 < x → Post m₂)
    (hP : ∀ m₂ m₃ x, m₁.store.EqOff
        (Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock L 0 1) m₂.store →
      R m₂ → m₂.store.get L 0 = some x → 0 < x →
      m₂.store.EqOff (Store.inBlock f.1 f.2 1) m₃.store →
      m₃.store.get f.1 f.2 = some (Mch.lit ((1 : ℕ) : ℚ)) → Post m₃) :
    Writes .total I τ (eigTail Ev) ρ (eigFp n a uo v f ⊔ Fp.above L) Post m₁ := by
  have hFE : Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock L 0 1 ≤
      eigFp n a uo v f ⊔ Fp.above L :=
    sup_le (fun _ _ h => Or.inl (Or.inr h)) (fun _ _ h => Or.inr (h.1 ▸ le_rfl))
  refine hEv.frame_seq_le hd ha hm.live hFE fun m₂ hfr₂ hR => ?_
  obtain ⟨x, hx₂⟩ := hx m₂ hR
  refine writes_ite rfl hg (hC.test_isPos (x := (L, 0)) (d := []) hx₂) ?_
  by_cases hx0 : 0 < x
  · have hf₂ : f.2 < m₂.store.len f.1 := by rw [hfr₂.len_eq]; exact hm.flag
    simp only [id, hx0, decide_true, if_true]
    exact (writes_indexLit hL (n := 1) rfl ho hf₂).mono
      (fun _ _ h => Or.inl (Or.inl (Or.inr h)))
      fun m₃ hf₃ h => hP m₂ m₃ x hfr₂ hR hx₂ hx0 hf₃ h.2
  · simp only [id, hx0, decide_false, Bool.false_eq_true, if_false]
    exact (Writes.skip (P := Post) (hN m₂ x hfr₂ hR hx₂ hx0)).mono bot_le fun _ _ h => h

end Tail

/-! ### The compositions -/

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] in
/-- What the stage's footprint leaves alone: the blocks of $\mathbf{T}$ and $\widehat{\mathbf{U}}$
and the flag. -/
private theorem EigTailMem.stage_disj {n L : ℕ} {qe : List ℝ} {a uo pe v f : ℕ × ℕ} {m : Mem ℝ}
    (hm : EigTailMem n qe a uo pe v f L m) :
    Fp.Disj (Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock L 0 1)
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) ∧
      Fp.Disj (Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock L 0 1)
        (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) ∧
      ¬ (Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock L 0 1) f.1 f.2 := by
  have hap := hm.apart
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true] at hap
  obtain ⟨⟨-, -, hav, haL⟩, ⟨-, huv, huL⟩, -, -⟩ := hap
  refine ⟨Fp.disj_sup_left.mpr ⟨hav.symm, haL.symm⟩, Fp.disj_sup_left.mpr ⟨huv.symm, huL.symm⟩, ?_⟩
  rintro (h | h)
  · exact hm.fv _ _ ⟨rfl, le_rfl, Nat.lt_succ_self _⟩ h
  · exact hm.fL h.1

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] in
/-- A Schur output survives a run writing off its blocks. -/
private theorem SchurOutput.of_eqOff {n : ℕ} {a uo f : ℕ × ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {eA eU : ℝ} {m m' : Mem ℝ} {G : Fp}
    (h : SchurOutput a uo f A eA eU m) (hfr : m.store.EqOff G m'.store)
    (ha : Fp.Disj G (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hu : Fp.Disj G (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))))) (hf : ¬ G f.1 f.2) :
    SchurOutput a uo f A eA eU m' := by
  obtain ⟨h0, U, T, hT, hU, hTu, hr, ho⟩ := h
  exact ⟨by rw [hfr.get_eq hf]; exact h0, U, T, hT.of_eqOff hfr ha, hU.of_eqOff hfr hu, hTu, hr, ho⟩

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] in
/-- A Schur output is kept by the release of scratch above its blocks. -/
private theorem SchurOutput.of_below {n L : ℕ} {a uo f : ℕ × ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {eA eU : ℝ} {s s' : Store ℝ} {q : ℕ}
    (h : SchurOutput a uo f A eA eU ⟨s, q⟩) (hB : Store.Below L s s') (ha : a.1 < L)
    (hu : uo.1 < L) (hf : f.1 < L) : SchurOutput a uo f A eA eU ⟨s', q⟩ := by
  obtain ⟨h0, U, T, hT, hU, hTu, hr, ho⟩ := h
  exact ⟨by rw [show s'.get f.1 f.2 = s.get f.1 f.2 from (hB f.1 hf).2 f.2]; exact h0, U, T,
    hT.of_below hB ha, hU.of_below hB hu, hTu, hr, ho⟩

omit [Has ScalarOp O] in
/-- **The run on one tape, from its parts**: if the Schur solver writes its blocks and ends in `S`
from the input of the pipeline, and the tail ends in `Post` from a memory for the tail in `S`,
then the eigensolver writes only its blocks and ends in `Post`, for a `Post` kept by the release
of the flag word. -/
private theorem eigSolverWith_writes_of {I : Interp O Q ℝ} {Solve Ev : Stmt O Q} {n nr nq k F T : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p pe uo v f : ℕ × ℕ} {qs qe : List ℝ}
    {τ : Tape ℝ} {μ : Mem ℝ} {S Post : Mem ℝ → Prop}
    (hin : EigSolverInput qs qe a p pe uo v f A μ)
    (hSolve : ∀ m', SchurPipelineInput qs a p uo f A m' →
      Writes .total I τ Solve (Env.frame [n + 1, nr, nq, k, F, T] [a, p, a, uo, f])
        (schurFp n a uo f) S m')
    (hkeep : ∀ {s s' : Store ℝ} {q : ℕ}, Store.Below μ.store.length s s' → Post ⟨s, q⟩ →
      Post ⟨s', q⟩)
    (hTail : ∀ m₁, EigTailMem n qe a uo pe v f μ.store.length m₁ → S m₁ →
      Writes .total I τ (eigTail Ev)
        ⟨(Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]).idx,
          (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]).buf ++
            [μ.store.length]⟩
        (eigFp n a uo v f ⊔ Fp.above μ.store.length) Post m₁) :
    Writes .total I τ (eigSolverWith Solve Ev)
      (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      Post μ := by
  rw [eigSolverWith_eq]
  refine writes_allocs_preserving_post (ns := [1]) rfl hkeep fun s₁ hlen hlens hBelow => ?_
  have hLs : s₁.length = μ.store.length + 1 := by simpa using hlen
  have hL1 : s₁.len μ.store.length = 1 := by simpa using hlens 0 (by simp)
  have hpin := hin.1.of_below (μ' := ⟨s₁, μ.pos⟩) hBelow hin.1.1 (by simp only; omega)
  have hlive : (⟨s₁, μ.pos⟩ : Mem ℝ).Live [a, p, a, uo, f] := fun z hz => hpin.1 z (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢; tauto)
  exact (hSolve _ hpin).frame_seq_le rfl rfl hlive (fun _ _ h => Or.inl (Or.inl h))
    fun m₁ hfr₁ hS => hTail m₁ (hin.tailMem hLs hL1 hBelow hfr₁) hS

omit [Has ScalarOp O] in
/-- The tail of the Monte Carlo composition, from a stored Schur output of a regularized matrix:
the stage's flag is $0$ and the run stores the Schur output and the eigendecomposition. -/
private theorem eigTail_writes_eigOutput {Mch : Machine ℝ} {I : Interp O Q ℝ} {n L : ℕ}
    (hL : IsIndexLit Mch I) (hC : IsCmp id I) {Ev : Stmt O Q}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a pe uo v f : ℕ × ℕ} {qe : List ℝ} {ρ : Env}
    {τ : Tape ℝ} {m₁ : Mem ℝ} {B Γ c₁ c₂ eR eX eU cR₀ cR cV cN g₀ : ℝ}
    (hd : IExp.evalList ρ.idx [.var 0, .var 6] = some [n + 1, qe.length])
    (ha : Operand.evalList ρ [⟨0, .var 7⟩, ⟨4, .var 11⟩, ⟨2, .var 9⟩, ⟨5, .var 12⟩,
      ⟨7, .const 0⟩] = some [a, uo, pe, v, (L, 0)])
    (hg : Operand.evalList ρ [⟨7, .const 0⟩] = some [(L, 0)])
    (ho : (⟨6, .var 13⟩ : Operand).eval ρ = some f)
    (hm : EigTailMem n qe a uo pe v f L m₁)
    (hreg : RegularizedSchurOutput (IsConditionedDiagonalizable B Γ) a uo f A c₁ c₂ eR eX eU m₁)
    (hEv : EigenvectorStageContract cR₀ cR cV cN g₀ (n + 1) qe Ev I)
    (hΓ : 0 < Γ) (hB : 1 ≤ B) (hc₁ : 0 < c₁) (he : eR + eX ≤ 1 / 2) (heU : eU ≤ 1 / 8)
    (hc : eigColTol n eU cV cN ≤ 1 / 8)
    (hfloor : 16 * g₀ * √((n : ℝ) + 1) < 7 * c₁ * Γ)
    (hsep : eX + 6 * eU ≤ c₁ * Γ / (16 * (n + 1) * B))
    (hκ : 8 * √((n : ℝ) + 1) * B * eigEta n eX eU cR₀ cV ≤ c₁ * Γ) :
    Writes .total I τ (eigTail Ev) ρ (eigFp n a uo v f ⊔ Fp.above L)
      (fun μ' => SchurOutput a uo f A (eR + eX) eU μ' ∧
        EigOutput a v f A (eR + eigEta n eX eU cR₀ cV)
          (eR + √((n : ℝ) + 1) * eigEta n eX eU cR₀ cV) (eigColTol n eU cV cN)
          (eR + 2 * ((n : ℝ) + 1) * B * eigEta n eX eU cR₀ cV)
          (2 * √((n : ℝ) + 1) * B) (7 / 8 * c₁ * Γ) μ') m₁ := by
  obtain ⟨hcV, hcN⟩ := nonneg_of_eigenvectorStageContract hEv (by omega)
  have hso := hreg.schurOutput
  obtain ⟨hf, U, T', X, hT, hUs, hTu, hoU, hr, hx, hclass⟩ := hreg
  obtain ⟨hda, hdu, hdf⟩ := hm.stage_disj
  have heU0 : 0 ≤ eU := (specNorm_nonneg _).trans hoU
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hT0 : A = 0 → T' = 0 := by
    rintro rfl
    have hX : X = 0 := by
      have h := hr
      simp only [specNorm_zero, mul_zero, zero_sub, specNorm_neg] at h
      exact specNorm_eq_zero_iff.mp (le_antisymm h (specNorm_nonneg _))
    subst hX
    have h := hx
    simp only [specNorm_zero, mul_zero, zero_sub, specNorm_neg] at h
    have h1 := one_sub_mul_specNorm_le_specNorm_mul_mul_conjTranspose hoU (by linarith) T'
    exact specNorm_eq_zero_iff.mp
      (le_antisymm (by nlinarith [specNorm_nonneg T']) (specNorm_nonneg _))
  have hgaps : A ≠ 0 → ∀ i j, i ≠ j → 7 / 8 * c₁ * Γ * specNorm A ≤ ‖T' i i - T' j j‖ := by
    intro hA i j hij
    obtain ⟨s, hsl, -, hCs⟩ := hclass.resolve_left hA
    exact mul_specNorm_le_norm_sub_diag_of_schur hTu hoU hr hx hsl hc₁ hA hCs hΓ he heU hsep i j
      hij
  have hzero : ∀ m₂ : Mem ℝ, (∃ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      HoldsMatrix v V m₂.store ∧
      (m₂.store.get L 0 = some 0 ∨ m₂.store.get L 0 = some 1) ∧
      (T' = 0 → V = U ∧ m₂.store.get L 0 = some 0) ∧
      (T'.IsUpperTriangular → (∃ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          (∀ j, |‖WithLp.toLp 2 (Y.col j)‖ - 1| ≤ cN ∧
            ‖WithLp.toLp 2 ((T' - T' j j • 1) *ᵥ Y.col j)‖ ≤
              (if m₂.store.get L 0 = some 0 then cR₀ else cR) * frobNorm T' *
                ‖WithLp.toLp 2 (Y.col j)‖) ∧
          specNorm (V - U * Y) ≤ cV * frobNorm U * frobNorm Y) ∧
        ((∀ i j, i ≠ j → g₀ * frobNorm T' < ‖T' i i - T' j j‖) →
          m₂.store.get L 0 = some 0))) → m₂.store.get L 0 = some 0 := by
    rintro m₂ ⟨V, -, -, h0, htri⟩
    by_cases hA : A = 0
    · exact (h0 (hT0 hA)).2
    · exact (htri hTu).2 (gap_lt_of_schur hoU hr hx he heU hA hc₁ hΓ hfloor (hgaps hA))
  refine eigTail_writes hL hC hd ha hg ho hm
    (hEv U T' le_rfl ⟨hT, hUs⟩ hm.words hm.live hm.room hm.apart) ?_ ?_ ?_
  · rintro m₂ ⟨V, -, hg', -⟩
    rcases hg' with h | h <;> exact ⟨_, h⟩
  · intro m₂ x hfr hR hx₂ hx0
    have hg0 := hzero m₂ hR
    obtain ⟨V, hV, -, h0, htri⟩ := hR
    have hT₂ := hT.of_eqOff hfr hda
    have hf₂ : m₂.store.get f.1 f.2 = some 0 := by rw [hfr.get_eq hdf]; exact hf
    refine ⟨hso.of_eqOff hfr hda hdu hdf, hf₂, T', V, hT₂, hV, ?_⟩
    by_cases hA : A = 0
    · obtain rfl := hA
      obtain rfl := hT0 rfl
      obtain ⟨rfl, -⟩ := h0 rfl
      refine eigDecompOf_zero hoU ?_ hc hB
      unfold eigColTol
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1) hcV]
    · obtain ⟨⟨Y, hY, hVY⟩, -⟩ := htri hTu
      rw [if_pos hg0] at hY
      obtain ⟨s, hsl, -, hCs⟩ := hclass.resolve_left hA
      exact eigDecompOf_of_schur hTu hoU hr hx hsl hc₁ hA hCs hΓ hY hVY hcV he heU hc hsep hκ
  · rintro m₂ m₃ x - hR hx₂ hx0 - -
    have hg0 := hzero m₂ hR
    rw [hg0] at hx₂
    obtain rfl : (0 : ℝ) = x := Option.some.inj hx₂
    exact absurd hx0 (lt_irrefl _)

omit [Has ScalarOp O] in
/-- **The Monte Carlo composition of the eigensolver.** On a machine with index literals and
exact comparisons, a measurable interpretation reading the tape only in its windows, let `Solve`
store, except with probability
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
theorem eigSolverWith_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hL : IsIndexLit Mch I) (hC : IsCmp id I) (hI : I.IsMeasurable)
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
  have hkeep : ∀ m, EigSolverInput qs qe a p pe uo v f A m → ∀ {s s' : Store ℝ} {q : ℕ},
      Store.Below m.store.length s s' →
      (SchurOutput a uo f A (eR + eX) eU ⟨s, q⟩ ∧
        EigOutput a v f A (eR + eigEta n eX eU cR₀ cV)
          (eR + √((n : ℝ) + 1) * eigEta n eX eU cR₀ cV) (eigColTol n eU cV cN)
          (eR + 2 * ((n : ℝ) + 1) * B * eigEta n eX eU cR₀ cV)
          (2 * √((n : ℝ) + 1) * B) (7 / 8 * c₁ * Γ) ⟨s, q⟩) →
      SchurOutput a uo f A (eR + eX) eU ⟨s', q⟩ ∧
        EigOutput a v f A (eR + eigEta n eX eU cR₀ cV)
          (eR + √((n : ℝ) + 1) * eigEta n eX eU cR₀ cV) (eigColTol n eU cV cN)
          (eR + 2 * ((n : ℝ) + 1) * B * eigEta n eX eU cR₀ cV)
          (2 * √((n : ℝ) + 1) * B) (7 / 8 * c₁ * Γ) ⟨s', q⟩ := by
    rintro m ⟨⟨hl, -⟩, hlv, -⟩ s s' q hB ⟨hso, h0, T₀, V₀, hT₀, hV₀, hE⟩
    have ha : a.1 < m.store.length := hl a (by simp)
    have hu : uo.1 < m.store.length := hl uo (by simp)
    have hf : f.1 < m.store.length := hl f (by simp)
    have hv : v.1 < m.store.length := hlv v (by simp)
    exact ⟨hso.of_below hB ha hu hf,
      by rw [show s'.get f.1 f.2 = s.get f.1 f.2 from (hB f.1 hf).2 f.2]; exact h0, T₀, V₀,
      hT₀.of_below hB ha, hV₀.of_below hB hv, hE⟩
  rw [eigSolverWith_eq]
  refine PWrites.allocs (ns := [1]) rfl
    (Pre₁ := fun L m => ∃ μ : Mem ℝ, EigSolverInput qs qe a p pe uo v f A μ ∧
      μ.store.length = L ∧ m.store.length = L + 1 ∧ m.store.len L = 1 ∧
      Store.Below L μ.store m.store ∧ m.pos = μ.pos)
    (fun m s₁ hm h1 h2 h3 =>
      ⟨m, hm, rfl, by simpa using h1, by simpa using h2 0 (by simp), h3, rfl⟩)
    hkeep fun L => ?_
  refine PWrites.of_forall_eq hI hloc (fun m₀ hm₀ => ?_)
    ((Mem.measurableSet_eqOff _).inter
      ((measurable_snd (measurableSet_schurOutput a uo f A _ _)).inter
        (measurable_snd (measurableSet_eigOutput a v f A _ _ _ _ _ _))))
  obtain ⟨μ, hin, rfl, hLs, hL1, hBelow, hpos⟩ := hm₀
  obtain ⟨s₀, q₀⟩ := m₀
  obtain rfl : q₀ = μ.pos := hpos
  have hLs' : s₀.length = μ.store.length + 1 := hLs
  have hpin := hin.1.of_below (μ' := ⟨s₀, μ.pos⟩) hBelow hin.1.1 (by simp only; omega)
  have hlive : ∀ m, SchurPipelineInput qs a p uo f A m → m.Live [a, p, a, uo, f] :=
    fun m hm z hz => hm.1 z (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢; tauto)
  have h₁ : PWrites law I (Stmt.frame [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5]
      [⟨0, .var 7⟩, ⟨1, .var 8⟩, ⟨0, .var 7⟩, ⟨4, .var 11⟩, ⟨6, .var 13⟩] Solve)
      ⟨(Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]).idx,
        (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]).buf ++
          (List.range [1].length).map (μ.store.length + ·)⟩ (schurFp n a uo f)
      (· = ⟨s₀, μ.pos⟩)
      (fun m' => s₀.EqOff (schurFp n a uo f) m'.store ∧
        RegularizedSchurOutput (IsConditionedDiagonalizable B Γ) a uo f A c₁ c₂ eR eX eU m') φ :=
    (hSolve.in_frame rfl rfl hlive).mono_eqOff (fun m hm => hm ▸ hpin)
      fun m m' hm hfr hp => by subst hm; exact ⟨hfr, hp⟩
  have h₂ : PWrites law I (eigTail Ev)
      ⟨(Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]).idx,
        (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]).buf ++
          (List.range [1].length).map (μ.store.length + ·)⟩
      (eigFp n a uo v f ⊔ Fp.above μ.store.length)
      (fun m' => s₀.EqOff (schurFp n a uo f) m'.store ∧
        RegularizedSchurOutput (IsConditionedDiagonalizable B Γ) a uo f A c₁ c₂ eR eX eU m')
      (fun μ' => SchurOutput a uo f A (eR + eX) eU μ' ∧
        EigOutput a v f A (eR + eigEta n eX eU cR₀ cV)
          (eR + √((n : ℝ) + 1) * eigEta n eX eU cR₀ cV) (eigColTol n eU cV cN)
          (eR + 2 * ((n : ℝ) + 1) * B * eigEta n eX eU cR₀ cV)
          (2 * √((n : ℝ) + 1) * B) (7 / 8 * c₁ * Γ) μ') 0 :=
    PWrites.of_writes le_rfl fun m' τ ⟨hfr, hreg⟩ =>
      eigTail_writes_eigOutput hL hC rfl rfl rfl rfl
        (hin.tailMem hLs hL1 hBelow hfr) hreg hEv hΓ hB hc₁ he heU hc hfloor hsep hκ
  exact (PWrites.seq hI hloc le_rfl h₁ h₂).mono (fun _ h => h)
    (sup_le (fun _ _ h => Or.inl (Or.inl h)) le_rfl) (fun _ h => h) (by simp)

omit [Has ScalarOp O] in
/-- **The verified composition of the eigensolver, on every tape.** On a machine with index
literals, exact natural literals up to $n + 1$ and exact comparisons, let
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
theorem eigSolverWith_writes_residual {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I)
    {Solve Ev : Stmt O Q}
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
  obtain ⟨hcV, -⟩ := nonneg_of_eigenvectorStageContract hEv (by omega)
  have hlit : Mch.lit ((1 : ℕ) : ℚ) = 1 := by simpa using hNat 1 (by omega)
  obtain ⟨⟨hl, -⟩, hlv, -⟩ := id hin
  have hal : a.1 < μ.store.length := hl a (by simp)
  have hul : uo.1 < μ.store.length := hl uo (by simp)
  have hfl : f.1 < μ.store.length := hl f (by simp)
  have hvl : v.1 < μ.store.length := hlv v (by simp)
  refine eigSolverWith_writes_of hin (hSolve τ) (fun {s s' q} hB h h0 => ?_)
    fun m₁ hm ⟨⟨U, T', hpair⟩, hsch⟩ => ?_
  · have hg : s'.get f.1 f.2 = s.get f.1 f.2 := (hB f.1 hfl).2 f.2
    obtain ⟨hso, T₀, V₀, hT₀, hV₀, hE⟩ := h (by rw [← hg]; exact h0)
    exact ⟨hso.of_below hB hal hul hfl, T₀, V₀, hT₀.of_below hB hal, hV₀.of_below hB hvl, hE⟩
  obtain ⟨hda, hdu, hdf⟩ := hm.stage_disj
  refine eigTail_writes hL hC rfl rfl rfl rfl hm
    (hEv U T' le_rfl hpair hm.words hm.live hm.room hm.apart) ?_ ?_ ?_
  · rintro m₂ ⟨V, -, hg', -⟩
    rcases hg' with h | h <;> exact ⟨_, h⟩
  · rintro m₂ x hfr ⟨V, hV, hg', -, htri⟩ hx₂ hx0 h0
    have hf₁ : m₁.store.get f.1 f.2 = some 0 := by rw [← hfr.get_eq hdf]; exact h0
    have hso := hsch hf₁
    obtain ⟨-, U₀, T₀, hT₀, hU₀, hTu, hr, ho⟩ := id hso
    obtain rfl : T₀ = T' := hT₀.eq_storedMatrix.trans hpair.1.eq_storedMatrix.symm
    obtain rfl : U₀ = U := hU₀.eq_storedMatrix.trans hpair.2.eq_storedMatrix.symm
    have hg0 : m₂.store.get μ.store.length 0 = some 0 := by
      rcases hg' with h | h
      · exact h
      · rw [h] at hx₂
        obtain rfl : (1 : ℝ) = x := Option.some.inj hx₂
        exact absurd one_pos hx0
    obtain ⟨⟨Y, hY, hVY⟩, -⟩ := htri hTu
    rw [if_pos hg0] at hY
    exact ⟨hso.of_eqOff hfr hda hdu hdf, T₀, V, hT₀.of_eqOff hfr hda, hV,
      eigResidualOf_of_schur ho hr hY hVY hcV he heU hc⟩
  · rintro m₂ m₃ x - - - - - h₃ h0
    rw [h0, hlit] at h₃
    exact absurd (Option.some.inj h₃) zero_ne_one

omit [Has ScalarOp O] in
/-- **The eigensolver terminates on every tape**: on a machine with index literals and exact
comparisons, if `Solve` terminates on every tape with the accumulator within $e_U$ of orthonormal
(`NLAlib.Schur.TerminatingSchurSolver`) and `Ev` completes
(`NLAlib.Schur.CompletingEigenvectorStage`), then from every input of the eigensolver the run
succeeds on every tape, writes only $\mathbf{A}$, $\widehat{\mathbf{U}}$, $\widehat{\mathbf{V}}$
and the flag, and stores a matrix at `a`, $\widehat{\mathbf{U}}$ within $e_U$ of orthonormal and a
matrix at `v`. -/
theorem eigSolverWith_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hL : IsIndexLit Mch I) (hC : IsCmp id I) {Solve Ev : Stmt O Q}
    {nr nq k F T : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p pe uo v f : ℕ × ℕ}
    {qs qe : List ℝ} {eU : ℝ} {μ : Mem ℝ}
    (hSolve : TerminatingSchurSolver eU n [n + 1, nr, nq, k, F, T] qs Solve I)
    (hEv : CompletingEigenvectorStage (n + 1) qe Ev I)
    (hin : EigSolverInput qs qe a p pe uo v f A μ) (τ : Tape ℝ) :
    Writes .total I τ (eigSolverWith Solve Ev)
      (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (fun μ' => SchurOrth (n := n) a uo eU μ' ∧
        ∃ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix v V μ'.store) μ := by
  obtain ⟨⟨hl, -⟩, hlv, -⟩ := id hin
  have hal : a.1 < μ.store.length := hl a (by simp)
  have hul : uo.1 < μ.store.length := hl uo (by simp)
  have hvl : v.1 < μ.store.length := hlv v (by simp)
  refine eigSolverWith_writes_of hin (fun m' hm' => hSolve A hm')
    (fun {s s' q} hB ⟨⟨⟨T₀, hT₀⟩, U₀, hU₀, ho⟩, V₀, hV₀⟩ =>
      ⟨⟨⟨T₀, hT₀.of_below hB hal⟩, U₀, hU₀.of_below hB hul, ho⟩, V₀, hV₀.of_below hB hvl⟩)
    fun m₁ hm hS => ?_
  obtain ⟨⟨T₀, hT₀⟩, U₀, hU₀, ho⟩ := id hS
  obtain ⟨hda, hdu, -⟩ := hm.stage_disj
  refine eigTail_writes hL hC rfl rfl rfl rfl hm
    (hEv U₀ T₀ le_rfl ⟨hT₀, hU₀⟩ hm.words hm.live hm.room hm.apart) (fun _ h => h.2) ?_ ?_
  · rintro m₂ x hfr ⟨⟨V, hV⟩, -⟩ - -
    exact ⟨⟨⟨T₀, hT₀.of_eqOff hfr hda⟩, U₀, hU₀.of_eqOff hfr hdu, ho⟩, V, hV⟩
  · rintro m₂ m₃ x hfr ⟨⟨V, hV⟩, -⟩ - - hf₃ -
    exact ⟨⟨⟨T₀, (hT₀.of_eqOff hfr hda).of_eqOff hf₃ hm.fa.symm⟩, U₀,
      (hU₀.of_eqOff hfr hdu).of_eqOff hf₃ hm.fu.symm, ho⟩, V, hV.of_eqOff hf₃ hm.fv⟩

omit [Has ScalarOp O] in
/-- **The static count of the eigensolver** with its structural instructions, at zero offsets, is
at most the instrumented counts of the solver and the stage at the offsets the eigensolver passes
to them, plus $128$ for the glue (the flag word, the branch and the frames). -/
theorem size_stmtCost_eigSolverWith_le (Solve Ev : Stmt O Q) (N nr nq k F T ne : ℕ) :
    Count.size (stmtCost (eigSolverWith Solve Ev).instrument
        [N, nr, nq, k, F, T, ne, 0, 0, 0, 0, 0, 0, 0]) ≤
      Count.size (stmtCost Solve.instrument [N, nr, nq, k, F, T, 0, 0, 0, 0, 0]) +
        Count.size (stmtCost Ev.instrument [N, ne, 0, 0, 0, 0, 0]) + 128 := by
  have hsup : ∀ x y : Count (O ⊕ Bookkeeping) Q,
      Count.size (x ⊔ y) = Count.size x + Count.size y - Count.size (x ⊓ y) := fun x y => by
    rw [← size_sup_add_size_inf]; omega
  simp only [eigSolverWith, Stmt.alloc, Stmt.instrument, stmtCost, tally, indexBookkeeping,
    operandBookkeeping, IExp.bookkeeping, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, useCost, testCost, IExp.evalList, IExp.eval, List.map_cons,
    List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
    Option.getD_some, map_add, map_zero, hsup, Count.one, Count.test, size_single]
  omega

end Theorems

end NLAlib.Schur
