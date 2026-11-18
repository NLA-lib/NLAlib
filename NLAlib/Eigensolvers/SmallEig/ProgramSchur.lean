/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.Program
public import NLAlib.Matrix.Perturbation.EigenvalueMatching
public import NLAlib.Ops.Confined
public import NLAlib.Ops.MonomialWork
public import NLAlib.Ops.Static
public import NLAlib.Eigensolvers.SmallEig.Precision
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveSchur
public import NLAlib.Eigensolvers.ShiftedQR.RoundedWorklistSchur

/-!
# The small-eigenvalue program in Schur form on the good tapes

The proof pieces of the `SmallEig` theorems (`NLAlib.Eigensolvers.SmallEig.Theorems`): the
program `NLAlib.SmallEig.smallEigProg` reduces its input to Hessenberg form, randomizes it,
decouples the last eigenvalue with the decoupler and recurses on the leading block. On the good
tapes it stores an upper triangular $\widehat{\mathbf{T}}$ and an accumulator
$\widehat{\mathbf{U}}$ tracked from $(\mathbf{I}, \mathbf{M})$ with explicit errors, so its
diagonal lists the eigenvalues of a nearby matrix.

## Main definitions

* `NLAlib.SmallEig.SmallEigCoreClass`: the class of the blocks handed to the decoupler.
* `NLAlib.SmallEig.SmallEigScratch`: the scratch memory of a run.

## Main results

* `NLAlib.SmallEig.smallEigProg_core_pwrites`, `NLAlib.SmallEig.smallEigProg_tail_pwrites`: the
  core and the tail of the program on the good tapes.
* `NLAlib.SmallEig.smallEigProg_pwrites_schur`: the program stores a tracked Schur pair.
* `NLAlib.SmallEig.smallEigProg_pwrites`: the forward contract on blocks.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-! ### The pieces of the proofs -/

/-- A matrix of order at most $1$ is listed by its diagonal. -/
theorem isEigenvalueListing_diag_of_le_one {d : ℕ} (hd : d ≤ 1) (B : Matrix (Fin d) (Fin d) ℂ) :
    IsEigenvalueListing B fun i => B i i := by
  have hT : B.IsUpperTriangular := fun i j hji => absurd hji (by omega)
  simpa using hT.isEigenvalueListing_diag

/-- A tracked Schur pair lists a nearby spectrum: if the stored pair
$(\widehat{\mathbf{U}}_b, \widehat{\mathbf{T}}_b)$ at `(o, w)` has $\widehat{\mathbf{T}}_b$ upper
triangular and is tracked from $(\mathbf{I}, \mathbf{M})$ with the backward error $\delta$, then
the diagonal of $\widehat{\mathbf{T}}_b$ lists the spectrum of $\mathbf{M} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le \delta$ (`NLAlib.SmallEig.SmallEigSpectrum`). -/
theorem smallEigSpectrum_of_tracked {n : ℕ} {w o : ℕ × ℕ}
    {M Ub Tb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {εU δ : ℝ} {μ' : Mem ℝ}
    (hP : Schur.HoldsSchurPair w o Ub Tb μ'.store) (hT : Tb.IsUpperTriangular)
    (ht : IsTrackedUnitarySimilar εU δ 1 M Ub Tb) : SmallEigSpectrum w o M δ μ' := by
  obtain ⟨V, ⟨hV, E, hE, rfl⟩, -⟩ := ht
  exact ⟨_, Ub, E, hP.1, hP.2, hT, hE,
    hV.isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul hT⟩

/-- The precision threshold is at most $1/100$: for tail records with $b_1, b_2 > 0$,
$n_{\max} \ge 1$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$,
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ gives $\boldsymbol{u} \le 1/100$. -/
theorem le_one_div_hundred_of_le_uSmallEig {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b)
    (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : 1 ≤ nmax) {S δ φ u : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) : u ≤ 1 / 100 := by
  obtain ⟨-, h1, -⟩ := uSmallEig_spec hb₁ hb₂ hn hδ hδS hφ hφ1
  have h2 : uSmallEigBasic nmax ≤ 1 / (100000 * ((nmax : ℝ) + 1) ^ 2) := min_le_right _ _
  have h3 : 1 / (100000 * ((nmax : ℝ) + 1) ^ 2) ≤ 1 / 100 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith [(nmax.cast_nonneg : (0 : ℝ) ≤ nmax)])
  linarith

/-! ### The Schur form -/

/-- The rotation count of the accumulator of `NLAlib.SmallEig.smallEigProg` on blocks of order at
most $k_{\max}$ with the cap $T$: the $k_{\max}^2$ replayed rotations of the reduction and the
replays of the core's $2(k_{\max} + 1)$ rounds at the bottom width $1$, each of a log of
$(T + k_{\max})k_{\max}$ entries and the products of the order-one leaves ($6$). -/
def smallEigLeafRotations (kmax T : ℕ) : ℕ :=
  kmax * kmax + 2 * (kmax + 1) * ((T + kmax) * kmax + 6)

/-- **The class of the matrix the core receives** in `NLAlib.SmallEig.smallEigProg`: upper
Hessenberg, diagonalizable with condition at most $B_c$ and eigenvalues separated by $g_c$
(`NLAlib.SmallEig.smallEigCondition`, `NLAlib.SmallEig.smallEigSeparation`), and of norm at most
$\Sigma + 3\delta/4$. -/
def SmallEigCoreClass {n : ℕ} (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  IsUpperHessenberg H ∧
    (∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ), IsUnit V ∧
      H * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ smallEigCondition nmax S δ φ c₂ ∧
      ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ ≤ ‖d i - d j‖) ∧
    specNorm H ≤ S + 3 * δ / 4

/-- **The reduction keeps the class, by the unitary of its log** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], the step from the perturbation to the core): on a machine with the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ and $M.\mathrm{lit}(0) = 0$, if
$\|\mathbf{M}\|_2 \le \Sigma$ and $\mathbf{M} + \mathbf{E}$, $\|\mathbf{E}\|_2 \le \delta/2$, has a
diagonalization with condition at most $2/t_2$ and eigenvalues separated by $t_1/2$ (the class of
`NLAlib.SmallEig.ginibrePerturb_pwrites`), then the rounded bottom-up Hessenberg form of
$\mathbf{M} + \mathbf{E}$ is in the class of the core (`NLAlib.SmallEig.SmallEigCoreClass`) and is
a perturbed unitary similarity of $\mathbf{M}$ by the unitary of the recorded rotations with
backward error $5\delta/8$. -/
theorem smallEigCoreClass_hessenbergReduceLastWord {Mch : Machine ℝ} {u : ℝ}
    (hM : StdModel u id Mch) (hzero : Mch.lit 0 = 0) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b)
    (hb₂ : 0 < c₂.b) {nmax n : ℕ} (hn : n + 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂)
    {M E V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hMS : specNorm M ≤ S)
    (hE : specNorm E ≤ δ / 2) (hV : IsUnit V) (hAV : (M + E) * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ 2 / smallEigCond nmax S δ φ c₂)
    (hgap : ∀ i j, i ≠ j → smallEigGap nmax S δ φ c₁ / 2 ≤ ‖d i - d j‖) :
    SmallEigCoreClass nmax S δ φ c₁ c₂ (hessenbergReduceLastWord Mch (M + E)) ∧
      IsPerturbedUnitarySimilarBy
        (givensLog (n + 1) (hessenbergReduceLastSlots Mch (M + E)).flatten) M
        (hessenbergReduceLastWord Mch (M + E)) (5 * δ / 8) := by
  have hS : 0 < S := hδ.trans_le hδS
  have hn1 : 1 ≤ nmax := by omega
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  obtain ⟨-, hu1, hu2, -⟩ := uSmallEig_spec hb₁ hb₂ hn1 hδ hδS hφ hφ1
  have ht₁ := (smallEigGap_pos_le hb₁ hn1 hS.le hδ hφ hφ1).1
  have ht₂ := (smallEigCond_pos_le hb₂ hn1 hS.le hδ hφ hφ1).1
  set t₁ := smallEigGap nmax S δ φ c₁
  set t₂ := smallEigCond nmax S δ φ c₂
  have hnn : ((n : ℝ) + 1) ≤ nmax := by exact_mod_cast hn
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((nmax : ℝ) + 1) ^ 2 := by gcongr; linarith
  have hb : u * (100000 * ((nmax : ℝ) + 1) ^ 2) ≤ 1 := by
    have := (hu.trans hu1).trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at this
  have hnu : 100 * ((n : ℝ) + 1) ^ 2 * u ≤ 1 := by nlinarith
  have hr : u * (1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S)) ≤
      min (δ / 8) (t₁ / (64 * ((nmax : ℝ) + 1) * (2 / t₂))) := by
    have := hu.trans hu2
    unfold uSmallEigReduce at this
    rwa [le_div_iff₀ (by positivity)] at this
  obtain ⟨hHess, -, hBy⟩ := hessenbergReduceLast_isPerturbedUnitarySimilarBy hM hzero hnu (M + E)
  set Q := givensLog (n + 1) (hessenbergReduceLastSlots Mch (M + E)).flatten
  set H := hessenbergReduceLastWord Mch (M + E)
  have hQ : HasOrthonormalCols Q := hBy.1
  have hF : specNorm (H - Qᴴ * (M + E) * Q) ≤ 50 * ((n : ℝ) + 1) ^ 2 * u * specNorm (M + E) := by
    obtain ⟨-, E', hE', he⟩ := hBy
    rw [he, Matrix.mul_add, Matrix.add_mul, add_sub_cancel_left, hQ.specNorm_conjTranspose_mul_mul]
    exact hE'
  have hA : specNorm (M + E) ≤ 2 * S := by
    have := specNorm_add_le M E; linarith
  have hε : 50 * ((n : ℝ) + 1) ^ 2 * u * specNorm (M + E) ≤
      u * (1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S)) := by
    have h0 : 0 ≤ specNorm (M + E) := specNorm_nonneg _
    calc 50 * ((n : ℝ) + 1) ^ 2 * u * specNorm (M + E)
        ≤ 50 * ((nmax : ℝ) + 1) ^ 2 * u * (2 * S) := by gcongr
      _ ≤ _ := by
        have := mul_nonneg (mul_nonneg hu0 (sq_nonneg ((nmax : ℝ) + 1))) hS.le
        nlinarith
  have hεδ := hε.trans (hr.trans (min_le_left _ _))
  have hFg : specNorm (H - Qᴴ * (M + E) * Q) ≤ t₁ / (64 * ((n : ℝ) + 1) * (1 / t₂)) := by
    refine hF.trans (hε.trans (hr.trans ((min_le_right _ _).trans ?_)))
    refine div_le_div_of_nonneg_left ht₁.le (by positivity) ?_
    rw [show 64 * ((nmax : ℝ) + 1) * (2 / t₂) = 128 * ((nmax : ℝ) + 1) * (1 / t₂) by ring]
    have : 0 < 1 / t₂ := by positivity
    nlinarith
  obtain ⟨V', d', hV', hHV', hκ', hgap'⟩ := class_of_rhess (B := 1 / t₂) hV hAV
    (by rw [show 2 * (1 / t₂) = 2 / t₂ by ring]; exact hκ) ht₁ hgap hQ hFg
  have hBy' : IsPerturbedUnitarySimilarBy Q M H (5 * δ / 8) := by
    have h0 : IsPerturbedUnitarySimilarBy 1 M (M + E) (specNorm E) :=
      ⟨hasOrthonormalCols_one, E, le_rfl, by simp⟩
    have := h0.trans hBy
    rw [Matrix.one_mul] at this
    exact this.mono (by linarith)
  refine ⟨⟨hHess, ⟨V', d', hV', hHV', ?_, hgap'⟩, ?_⟩, hBy'⟩
  · unfold smallEigCondition; rw [show 4 / t₂ = 4 * (1 / t₂) by ring]; exact hκ'
  · have := hBy'.isPerturbedUnitarySimilar.specNorm_le; linarith

/-- The relative accumulator errors of the replay of the reduction,
$(1 + 24\boldsymbol{u})^{(n+1)^2} - 1$, and of the core,
$(1 + 24\boldsymbol{u})^{2(n+1)((T + n + 1)(n + 1) + 6)} - 1$, compose within
$(1 + 24\boldsymbol{u})^R - 1$, $R$ = `NLAlib.SmallEig.smallEigLeafRotations` $k_{\max}$ $T$, for
$n + 1 \le k_{\max}$ and $\boldsymbol{u} \ge 0$. -/
theorem smallEigLeaf_accumulator_le {u : ℝ} (hu0 : 0 ≤ u) {n kmax T : ℕ} (hdk : n + 1 ≤ kmax) :
    (1 + ((1 + 24 * u) ^ ((n + 1) * (n + 1)) - 1)) *
      (1 + ((1 + 24 * u) ^ (2 * (n + 1) * ((T + (n + 1)) * (n + 1) + 2 * 1 * (1 + 2))) *
        (1 + 0) ^ (n + 1) - 1)) - 1 ≤ (1 + 24 * u) ^ smallEigLeafRotations kmax T - 1 := by
  have h1u : (1 : ℝ) ≤ 1 + 24 * u := by linarith
  rw [add_sub_cancel, add_sub_cancel, add_zero, one_pow, mul_one, ← pow_add]
  have h2' : (T + (n + 1)) * (n + 1) ≤ (T + kmax) * kmax := Nat.mul_le_mul (by omega) hdk
  have h3' : 2 * (n + 1) * ((T + (n + 1)) * (n + 1) + 2 * 1 * (1 + 2)) ≤
      2 * (kmax + 1) * ((T + kmax) * kmax + 6) := Nat.mul_le_mul (by omega) (by omega)
  have := pow_le_pow_right₀ h1u (Nat.add_le_add (Nat.mul_le_mul hdk hdk) h3')
  unfold smallEigLeafRotations
  linarith

/-- The outcomes of the core call of `NLAlib.SmallEig.smallEigProg`, as pairs of a memory before
and after: the frame `F`, initialised words of the block at `w` and of the accumulator at `ub`,
the block read after upper triangular, and the pair read after tracked from
$(\mathbf{I}, \mathbf{M})$ with the errors $(\varepsilon_U, \delta)$. They form a measurable set
(`NLAlib.isClosed_setOf_isTrackedUnitarySimilar`). -/
theorem measurableSet_smallEigOutcome {n : ℕ} (εU δ : ℝ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (w ub : ℕ × ℕ) (F : Fp) :
    MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (x.2.store.get w.1 (w.2 + j)).isSome) ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (x.2.store.get ub.1 (ub.2 + j)).isSome) ∧
      (storedMatrix w (n + 1) (n + 1) x.2.store).IsUpperTriangular ∧
      IsTrackedUnitarySimilar εU δ 1 M (storedMatrix ub (n + 1) (n + 1) x.2.store)
        (storedMatrix w (n + 1) (n + 1) x.2.store)} := by
  have hm : ∀ b, Measurable fun x : Mem ℝ × Mem ℝ => storedMatrix b (n + 1) (n + 1) x.2.store :=
    fun b => (measurable_storedMatrix b (n + 1) (n + 1)).comp measurable_snd
  have hut : MeasurableSet {x : Mem ℝ × Mem ℝ |
      (storedMatrix w (n + 1) (n + 1) x.2.store).IsUpperTriangular} := by
    have e : {x : Mem ℝ × Mem ℝ | (storedMatrix w (n + 1) (n + 1) x.2.store).IsUpperTriangular} =
        ⋂ i, ⋂ j, {x | j < i → storedMatrix w (n + 1) (n + 1) x.2.store i j = 0} := by
      ext x
      simp [Matrix.IsUpperTriangular, Matrix.BlockTriangular]
    rw [e]
    exact .iInter fun i => .iInter fun j => (MeasurableSet.const (j < i)).imp
      (measurableSet_eq_fun ((Matrix.measurable_apply i j).comp (hm w)) measurable_const)
  have htr : MeasurableSet {x : Mem ℝ × Mem ℝ | IsTrackedUnitarySimilar εU δ 1 M
      (storedMatrix ub (n + 1) (n + 1) x.2.store) (storedMatrix w (n + 1) (n + 1) x.2.store)} := by
    have hf : Measurable fun x : Mem ℝ × Mem ℝ =>
        (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), M),
          (storedMatrix ub (n + 1) (n + 1) x.2.store, storedMatrix w (n + 1) (n + 1) x.2.store)) :=
      measurable_const.prodMk ((hm ub).prodMk (hm w))
    exact hf (isClosed_setOf_isTrackedUnitarySimilar εU δ).measurableSet
  exact (Mem.measurableSet_eqOff F).inter ((measurable_snd (measurableSet_forall_isSome w _)).inter
    ((measurable_snd (measurableSet_forall_isSome ub _)).inter (hut.inter htr)))

/-- **The scratch memory of `NLAlib.SmallEig.smallEigProg`** on a block of order $n + 1 \ge 2$,
after its three scratch buffers are allocated on top of $L$ buffers: the failure word at
`(L, 0)`, the threshold word at `(L + 1, 0)` and the log of $(n + 1)(1 + 5(n + 1))$ words at
`(L + 2, 0)`; the block at `w`, the words `qs` at `q` and the identity accumulator at `ub`, all
below $L$, the accumulator apart from the block and the words apart from both. -/
def SmallEigScratch (n L : ℕ) (qs : List ℝ) (w q ub : ℕ × ℕ) (μ : Mem ℝ) : Prop :=
  μ.store.length = L + 3 ∧ μ.store.len L = 1 ∧ μ.store.len (L + 1) = 1 ∧
    μ.store.len (L + 2) = (n + 1) * (1 + 5 * (n + 1)) ∧ w.1 < L ∧ q.1 < L ∧ ub.1 < L ∧
    HoldsMatrix ub (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) μ.store ∧
    μ.store.readBlock q.1 q.2 qs.length = some qs ∧
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1)))) ∧
    Fp.Disj (Store.inBlock q.1 q.2 qs.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))))

/-- The scratch memory survives a run that writes neither the accumulator nor the words. -/
theorem SmallEigScratch.of_eqOff {n L : ℕ} {qs : List ℝ} {w q ub : ℕ × ℕ} {μ μ' : Mem ℝ}
    {F : Fp} (h : SmallEigScratch n L qs w q ub μ) (hfr : μ.store.EqOff F μ'.store)
    (hu : Fp.Disj F (Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1)))))
    (hq : Fp.Disj F (Store.inBlock q.1 q.2 qs.length)) : SmallEigScratch n L qs w q ub μ' := by
  obtain ⟨hlen, h0, h1, h2, hw, hqL, huL, hU, hp, hwu, hpwu⟩ := h
  exact ⟨by rw [hfr.length_eq]; exact hlen, by rw [hfr.len_eq]; exact h0,
    by rw [hfr.len_eq]; exact h1, by rw [hfr.len_eq]; exact h2, hw, hqL, huL,
    hU.of_eqOff hfr hu, hfr.keep (Store.readsOnly_readBlock _ _ _ _) hq hp, hwu, hpwu⟩

/-- **The outcome of the core call**: if $(\mathbf{X}, \mathbf{H})$ is tracked from
$(\mathbf{I}, \mathbf{M})$ with errors $((1 + 24\boldsymbol{u})^{(n+1)^2} - 1, 5\delta/8)$ and the
stored pair $(\widehat{\mathbf{U}}_b, \widehat{\mathbf{T}}_b)$ is tracked from
$(\mathbf{X}, \mathbf{H})$ with the accumulator error of the core and a backward error $K$ with
$5\delta/8 + K \le \delta$, $\widehat{\mathbf{T}}_b$ upper triangular, then the words of both are
stored and the pair read from the store is upper triangular and tracked from
$(\mathbf{I}, \mathbf{M})$ with errors $((1 + 24\boldsymbol{u})^R - 1, \delta)$
(`NLAlib.SmallEig.smallEigLeaf_accumulator_le`). -/
theorem smallEigCore_outcome {u δ K : ℝ} (hu0 : 0 ≤ u) {n nmax T : ℕ} (hn : n + 1 ≤ nmax)
    (hK : 5 * δ / 8 + K ≤ δ) {M X H U' Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {s : Store ℝ} {w ub : ℕ × ℕ}
    (hx : IsTrackedUnitarySimilar ((1 + 24 * u) ^ ((n + 1) * (n + 1)) - 1) (5 * δ / 8) 1 M X H)
    (htr : IsTrackedUnitarySimilar
      ((1 + 24 * u) ^ (2 * (n + 1) * ((T + (n + 1)) * (n + 1) + 2 * 1 * (1 + 2))) *
        (1 + 0) ^ (n + 1) - 1) K X H U' Tm)
    (hTm : HoldsMatrix w Tm s) (hU' : HoldsMatrix ub U' s) (hup : Tm.IsUpperTriangular) :
    (∀ j < 2 * ((n + 1) * (n + 1)), (s.get w.1 (w.2 + j)).isSome) ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (s.get ub.1 (ub.2 + j)).isSome) ∧
      (storedMatrix w (n + 1) (n + 1) s).IsUpperTriangular ∧
      IsTrackedUnitarySimilar ((1 + 24 * u) ^ smallEigLeafRotations nmax T - 1) δ 1 M
        (storedMatrix ub (n + 1) (n + 1) s) (storedMatrix w (n + 1) (n + 1) s) := by
  have h₂ : 0 ≤ (1 + 24 * u) ^ (2 * (n + 1) * ((T + (n + 1)) * (n + 1) + 2 * 1 * (1 + 2))) *
      (1 + 0) ^ (n + 1) - 1 := by
    have := one_le_pow₀ (M₀ := ℝ) (n := 2 * (n + 1) * ((T + (n + 1)) * (n + 1) + 2 * 1 * (1 + 2)))
      (by linarith : (1 : ℝ) ≤ 1 + 24 * u)
    rw [add_zero, one_pow, mul_one]; linarith
  have htr' := (hx.trans h₂ htr).mono (εT' := δ) (smallEigLeaf_accumulator_le hu0 hn) hK
  have hw : ∀ j < 2 * ((n + 1) * (n + 1)), (s.get w.1 (w.2 + j)).isSome := fun j hj => by
    rw [Store.get_of_readBlock hTm hj 0]; rfl
  have hub : ∀ j < 2 * ((n + 1) * (n + 1)), (s.get ub.1 (ub.2 + j)).isSome :=
    fun j hj => by rw [Store.get_of_readBlock hU' hj 0]; rfl
  have e1 := hTm.eq_storedMatrix
  have e2 := hU'.eq_storedMatrix
  subst e1 e2
  exact ⟨hw, hub, hup, htr'⟩

/-- The $2(n + 1)$ rounds of the worklist fail with probability at most $\varphi/4$: for
$n + 1 \le n_{\max}$ and $\varphi \ge 0$, $2(n + 1)\varphi_D \le \varphi/4$,
$\varphi_D$ = `NLAlib.SmallEig.smallEigDecouplerFailure`. -/
theorem two_mul_smallEigDecouplerFailure_le {n nmax : ℕ} (hn : n + 1 ≤ nmax) {φ : ℝ}
    (hφ : 0 ≤ φ) : 2 * ((n : ℝ) + 1) * (smallEigDecouplerFailure nmax φ + 0) ≤ φ / 4 := by
  have hnn : ((n : ℝ) + 1) ≤ nmax := by exact_mod_cast hn
  have hN : (0 : ℝ) < nmax := by linarith
  have e : 2 * (nmax : ℝ) * (φ / (16 * nmax)) = φ / 8 := by field_simp; ring
  have h := mul_le_mul_of_nonneg_right (by linarith : 2 * ((n : ℝ) + 1) ≤ 2 * nmax)
    (by positivity : 0 ≤ φ / (16 * nmax))
  unfold smallEigDecouplerFailure
  rw [add_zero]
  linarith

/-- **The backward error of the core is within its budget** (the precision of the Schur form):
for tail records with $b_1, b_2 > 0$, $n + 1 \le n_{\max}$, $0 < \delta \le \Sigma$,
$0 < \varphi \le 1$ and $0 \le \boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$, the backward
error of `NLAlib.ShiftedQR.solveRoundedWith_pwrites` at the cut level $2.25\,\omega$, the decoupler
error at $2\Sigma$, the replays of the log of $(T + n + 1)$ slots of $n + 1$ entries and the
products of the order-one leaves is at most $\min(\delta/4, g_c/(16n_{\max}B_c))$
(`NLAlib.SmallEig.smallEigReplay_le_omega`, `NLAlib.SmallEig.smallEigDecoupleError_le_omega`). -/
theorem smallEigCore_backwardError_le {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax n : ℕ} (hn : n + 1 ≤ nmax) {S δ φ u : ℝ} (hu0 : 0 ≤ u) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) :
    2 * ((n : ℝ) + 1) * (2.25 * smallEigOmega nmax S δ φ c₁ c₂ +
      smallEigDecoupleError nmax S δ φ c₂ u (2 * S) + 0 +
      78 * u * (((smallEigCap nmax S δ φ c₁ c₂ + (n + 1) : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) * (2 * S) +
      8 * ((n : ℝ) + 1) * (((1 : ℕ) : ℝ) + 2) * u * (2 * S)) ≤
      min (δ / 4) (smallEigSeparation nmax S δ φ c₁ /
        (16 * nmax * smallEigCondition nmax S δ φ c₂)) := by
  have hS0 : 0 < S := hδ.trans_le hδS
  have hn1 : 1 ≤ nmax := by omega
  have hnn : ((n : ℝ) + 1) ≤ nmax := by exact_mod_cast hn
  obtain ⟨-, hε⟩ := smallEigDecoupleError_le_omega hb₁ hb₂ hn1 hu0 hδ hδS hφ hφ1 hu
  have hRp := smallEigReplay_le_omega hb₁ hb₂ hn1 hu0 hδ hδS hφ hφ1 hu
  have hΩ := two_mul_mul_smallEigOmega (c₁ := c₁) (c₂ := c₂) hn1 S δ φ
  have hω := smallEigOmega_pos hb₁ hb₂ hn1 hS0.le hδ hφ hφ1
  push_cast
  set T : ℝ := (smallEigCap nmax S δ φ c₁ c₂ : ℝ)
  set ω := smallEigOmega nmax S δ φ c₁ c₂
  set X := min (δ / 4) (smallEigSeparation nmax S δ φ c₁ /
    (16 * nmax * smallEigCondition nmax S δ φ c₂))
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hr1 : (T + ((n : ℝ) + 1)) * ((n : ℝ) + 1) ≤ (T + nmax) * nmax := by gcongr
  have hus : 0 ≤ u * (2 * S) := by positivity
  have hr2 : 78 * u * ((T + ((n : ℝ) + 1)) * ((n : ℝ) + 1)) * (2 * S) +
      8 * ((n : ℝ) + 1) * (1 + 2) * u * (2 * S) ≤ ω := by
    refine le_trans ?_ hRp
    nlinarith [mul_le_mul_of_nonneg_right hr1 hus, mul_le_mul_of_nonneg_right hnn hus]
  have hb : 2.25 * ω + smallEigDecoupleError nmax S δ φ c₂ u (2 * S) + 0 +
      78 * u * ((T + ((n : ℝ) + 1)) * ((n : ℝ) + 1)) * (2 * S) +
      8 * ((n : ℝ) + 1) * (1 + 2) * u * (2 * S) ≤ 3.26 * ω := by linarith
  calc _ ≤ 2 * (nmax : ℝ) * (3.26 * ω) := by
        have := mul_le_mul hb (by linarith : 2 * ((n : ℝ) + 1) ≤ 2 * nmax)
          (by linarith [hω.le]) (by positivity)
        linarith
    _ ≤ X := by nlinarith

/-- **The core call of `NLAlib.SmallEig.smallEigProg`** ([BanksGarzaVargasSrivastava2025,
Theorem 6.1], in Schur form): on the machine and streams of
`NLAlib.SmallEig.smallEigProg_pwrites_schur`, from a memory set up for the core
(`NLAlib.SmallEig.SmallEigCoreReady`) with a block $\mathbf{H}$ in the class of the core and an
accumulator $\mathbf{X}$, the pair $(\mathbf{X}, \mathbf{H})$ tracked from $(\mathbf{I},
\mathbf{M})$ with errors $((1 + 24\boldsymbol{u})^{(n+1)^2} - 1, 5\delta/8)$, the rounded worklist
(`NLAlib.ShiftedQR.solveRoundedWith_pwrites` with the decoupler and the order-one leaf) writes only
the block, the accumulator and the failure word and, except with probability at most
$\varphi/4$, stores an upper triangular $\widehat{\mathbf{T}}_b$ and $\widehat{\mathbf{U}}_b$
tracked from $(\mathbf{I}, \mathbf{M})$ with errors $((1 + 24\boldsymbol{u})^R - 1, \delta)$. The
replay errors are absorbed by `NLAlib.SmallEig.smallEigReplay_le_omega`. -/
theorem smallEigProg_core_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I) {n : ℕ}
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : n + 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {w p ub : ℕ × ℕ} {L : ℕ} {ρ : Env}
    {ds : List IExp} {args : List Operand}
    (hd : IExp.evalList ρ.idx ds = some [n + 1, 1, (smallEigParams nmax S δ φ c₁ c₂).length,
      smallEigCap nmax S δ φ c₁ c₂, smallEigCap nmax S δ φ c₁ c₂,
      smallEigCap nmax S δ φ c₁ c₂ + (n + 1), n + 1])
    (ha : Operand.evalList ρ args = some [w, (L + 1, 0), p, ub, w, ub, (L, 0)]) :
    PWrites law I (.frame ds args (smallEigCore (O := O) (Q := Q) sG).body) ρ
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock L 0 1)
      (fun μ => ∃ H X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        SmallEigCoreClass nmax S δ φ c₁ c₂ H ∧
        IsTrackedUnitarySimilar ((1 + 24 * u) ^ ((n + 1) * (n + 1)) - 1) (5 * δ / 8) 1 M X H ∧
        SmallEigCoreReady (smallEigParams nmax S δ φ c₁ c₂) w p ub L H X μ)
      (fun μ' => ∃ Ub Tb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        Schur.HoldsSchurPair w ub Ub Tb μ'.store ∧ Tb.IsUpperTriangular ∧
        IsTrackedUnitarySimilar
          ((1 + 24 * u) ^ smallEigLeafRotations nmax (smallEigCap nmax S δ φ c₁ c₂) - 1) δ 1 M
          Ub Tb) (φ / 4) := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hzero : Mch.lit 0 = 0 := by simpa using hNat 0 (by omega)
  have h1 : Mch.lit 1 = 1 := by simpa using hNat 1 (by omega)
  have hS0 : 0 < S := hδ.trans_le hδS
  have hn1 : 1 ≤ nmax := by omega
  have hnn : ((n : ℝ) + 1) ≤ nmax := by exact_mod_cast hn
  have hu1 := le_one_div_hundred_of_le_uSmallEig hb₁ hb₂ hn1 hδ hδS hφ hφ1 hu
  obtain ⟨hε0, hε⟩ := smallEigDecoupleError_le_omega hb₁ hb₂ hn1 hu0 hδ hδS hφ hφ1 hu
  have hBc := smallEigCondition_ge hb₂ hn1 hS0.le hδ hφ hφ1
  have hsep := smallEigSeparation_pos hb₁ hn1 hS0.le hδ hφ hφ1
  have hω := smallEigOmega_pos hb₁ hb₂ hn1 hS0.le hδ hφ hφ1
  set qs := smallEigParams nmax S δ φ c₁ c₂ with hqs
  set T := smallEigCap nmax S δ φ c₁ c₂ with hT
  set ω := smallEigOmega nmax S δ φ c₁ c₂ with hωdef
  set ε := smallEigDecoupleError nmax S δ φ c₂ u (2 * S)
  set X := min (δ / 4) (smallEigSeparation nmax S δ φ c₁ /
    (16 * nmax * smallEigCondition nmax S δ φ c₂))
  have hX1 : X ≤ δ / 4 := min_le_left _ _
  have hX2 : X ≤
      smallEigSeparation nmax S δ φ c₁ / (16 * (n + 1) * smallEigCondition nmax S δ φ c₂) :=
    (min_le_right _ _).trans (div_le_div_of_nonneg_left hsep.le (by positivity) (by gcongr))
  -- the decoupler and the leaf
  have hDn : RandomDecouplingRoutineContract law (2 * smallEigCondition nmax S δ φ c₂)
      (smallEigSeparation nmax S δ φ c₁ / 2) (smallEigDecouplerFailure nmax φ) 1 T T n (2 * S) qs
      (T + (n + 1)) (n + 1) (1.5 * ω) (smallEigDecoupleError nmax S δ φ c₂ u)
      (smallEigDecoupler (O := O) (Q := Q) sG) I :=
    smallEigDecoupler_randomDecouplingRoutineContract_of_le (O := O) (Q := Q) hS hM
    hzero hL (kb := n) (by omega) hNat hC hQ hI hloc hSmp hDisk hU hG hb₁ hb₂ hn1 hδ hδS hφ hφ1 hu
    T (ns := T + (n + 1)) (ws := n + 1) (by omega) (by omega)
  have hLeaf : Schur.RandomSchurLeafContract law 0 0 0 (min 1 (n + 1)) (2 * S) qs T
      (identityLeaf (O := O) (Q := Q)) I := by
    rw [show min 1 (n + 1) = 1 by omega]
    exact identityLeaf_randomSchurLeafContract hS hzero h1 law _ _ _
  have h6 : qs.getD 6 0 = 2 * (1.5 * ω) ^ 2 := by simp [qs, smallEigParams, ω]
  have hsqu : (1 + u) ^ 2 ≤ 2 := by
    have := mul_le_mul hu1 hu1 hu0 (by norm_num : (0 : ℝ) ≤ 1 / 100); nlinarith
  have hsqd : 0.98 ≤ (1 - u) ^ 2 := by nlinarith
  have hφD : 0 ≤ smallEigDecouplerFailure nmax φ := by
    unfold smallEigDecouplerFailure; positivity
  set F := Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock L 0 1
  set εU := (1 + 24 * u) ^ smallEigLeafRotations nmax T - 1
  let ι := {x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ × Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ //
    SmallEigCoreClass nmax S δ φ c₁ c₂ x.1 ∧
      IsTrackedUnitarySimilar ((1 + 24 * u) ^ ((n + 1) * (n + 1)) - 1) (5 * δ / 8) 1 M x.2 x.1}
  have hfind : (1 + u) ^ 2 * (1.5 * ω) ^ 2 ≤ qs.getD 6 0 := by
    rw [h6]; exact mul_le_mul_of_nonneg_right hsqu (sq_nonneg _)
  have hcut : qs.getD 6 0 ≤ (1 - u) ^ 2 * (2.25 * ω) ^ 2 := by
    have e1 : 2 * (1.5 * ω) ^ 2 = 4.5 * ω ^ 2 := by ring
    have e2 : 0.98 * (2.25 * ω) ^ 2 = 4.96125 * ω ^ 2 := by ring
    have := mul_le_mul_of_nonneg_right hsqd (sq_nonneg (2.25 * ω))
    have := sq_nonneg ω
    rw [h6]; linarith
  have hK' := smallEigCore_backwardError_le hb₁ hb₂ hn hu0 hδ hδS hφ hφ1 hu
  have hfam := fun x : ι => (solveRoundedWith_pwrites (c := 2.25 * ω) (thr := qs.getD 6 0)
      (a := w) (t := (L + 1, 0)) (p := p) (uo := ub) (f := (L, 0)) (U := x.1.2) hS hM hu0
      (by linarith) hL hNat hQ hC hI hloc _ hDn _ hLeaf hφD le_rfl le_rfl x.2.1.1
      x.2.1.2.1.choose_spec.choose_spec.1 x.2.1.2.1.choose_spec.choose_spec.2.1
      x.2.1.2.1.choose_spec.choose_spec.2.2.1 hsep x.2.1.2.1.choose_spec.choose_spec.2.2.2
      hfind hcut (by positivity) le_rfl hε0 (by positivity) (by linarith [x.2.1.2.2])
      ((le_of_eq (by ring)).trans (hK'.trans hX2))).in_frame
      hd ha
      fun μ h y hy => h.1 y (by simp at hy ⊢; tauto)
  refine PStep.mono (PWrites.pstep_of_forall hI hloc (F := F)
    (P := fun (x : ι) μ => SmallEigCoreReady qs w p ub L x.1.1 x.1.2 μ) hfam
    (measurableSet_smallEigOutcome εU δ M w ub F) ?_)
    (fun μ ⟨H, X', hc, ht, hr⟩ => ⟨⟨(H, X'), hc, ht⟩, hr⟩) ?_ ?_
  · rintro x μ μ' - hfr ⟨-, U', Tm, hTm, hU', hup, htr⟩
    exact ⟨hfr, smallEigCore_outcome hu0 hn (by linarith [hK', hX1]) x.2.2 htr hTm hU' hup⟩
  · rintro μ μ' - ⟨hfr, hw, hub, hup, htr⟩
    exact ⟨hfr, _, _, ⟨holdsMatrix_storedMatrix hw, holdsMatrix_storedMatrix hub⟩, hup, htr⟩
  · exact two_mul_smallEigDecouplerFailure_le hn hφ.le

omit [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- **The identity accumulator of `NLAlib.SmallEig.smallEigProg`**: from the memory of the input
(`NLAlib.SmallEig.SmallEigInput`), on a scalar machine with the literals $0$ and $1$ exact,
`NLAlib.SmallEig.identityLeaf` writes only the output block, stores the identity there and keeps
the input. -/
theorem SmallEigInput.identity_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (h0 : Mch.lit 0 = 0) (h1 : Mch.lit 1 = 1) {nmax n T : ℕ}
    {S δ φ : ℝ} {c₁ c₂ : PolyLogTail} {w q o : ℕ × ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {μ : Mem ℝ} {τ : Tape ℝ} (hin : SmallEigInput nmax S δ φ c₁ c₂ w q o M μ) :
    Writes .total I τ (identityLeaf (O := O) (Q := Q)).body
      (Env.frame [n + 1, (smallEigParams nmax S δ φ c₁ c₂).length, T] [w, q, w, o])
      (Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1))))
      (fun μ' => SmallEigInput nmax S δ φ c₁ c₂ w q o M μ' ∧
        HoldsMatrix o (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) μ'.store) μ := by
  obtain ⟨hW, hq, hl, hroom, hwo, hqwo⟩ := hin
  refine (identityLeaf_writes hS h0 (fun _ => h1) hroom).mono le_rfl ?_
  rintro μ' hfr ⟨-, hU⟩
  exact ⟨⟨hW.of_eqOff hfr hwo.symm,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hqwo.mono le_rfl le_sup_right).symm hq,
    fun x hx => hfr.length_eq ▸ hl x hx, by rw [hfr.len_eq]; exact hroom, hwo, hqwo⟩, hU⟩

/-- The scratch memory after the three allocations of `NLAlib.SmallEig.smallEigProg` on top of
a memory holding the input and the identity accumulator. -/
theorem SmallEigScratch.of_alloc {nmax n : ℕ} {S δ φ : ℝ} {c₁ c₂ : PolyLogTail}
    {w q o : ℕ × ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {μ : Mem ℝ} {s₁ : Store ℝ}
    (hin : SmallEigInput nmax S δ φ c₁ c₂ w q o M μ)
    (hU : HoldsMatrix o (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) μ.store)
    (hlen₁ : s₁.length = μ.store.length + 3)
    (hlens : ∀ i (hi : i < [1, 1, (n + 1) * (1 + 5 * (n + 1))].length),
      s₁.len (μ.store.length + i) = [1, 1, (n + 1) * (1 + 5 * (n + 1))][i])
    (hBelow : Store.Below μ.store.length μ.store s₁) :
    SmallEigScratch n μ.store.length (smallEigParams nmax S δ φ c₁ c₂) w q o ⟨s₁, μ.pos⟩ ∧
      HoldsMatrix w M s₁ := by
  obtain ⟨hW, hq, hl, -, hwo, hqwo⟩ := hin
  have hwL : w.1 < μ.store.length := hl w (by simp)
  have hqL : q.1 < μ.store.length := hl q (by simp)
  have hoL : o.1 < μ.store.length := hl o (by simp)
  exact ⟨⟨hlen₁, by simpa using hlens 0 (by simp), by simpa using hlens 1 (by simp),
    by simpa using hlens 2 (by simp), hwL, hqL, hoL, hU.of_below hBelow hoL,
    hBelow.readBlock_of hqL hq, hwo, hqwo⟩, hW.of_below hBelow hwL⟩

/-- **The tail of `NLAlib.SmallEig.smallEigProg`**: after the perturbation, the reduction, the
replay (`NLAlib.SmallEig.smallEigProg_reduce_writes`, on every tape) and the core
(`NLAlib.SmallEig.smallEigProg_core_pwrites`, $\varphi/4$) store, from a perturbed block in the
class of `NLAlib.SmallEig.ginibrePerturb_pwrites`, an upper triangular
$\widehat{\mathbf{T}}_b$ and $\widehat{\mathbf{U}}_b$ tracked from $(\mathbf{I}, \mathbf{M})$:
the reduction keeps the class (`NLAlib.SmallEig.smallEigCoreClass_hessenbergReduceLastWord`) and
the replay is within $(1 + 24\boldsymbol{u})^{(n+1)^2} - 1$ of its unitary. The frames are given
by their evaluations. -/
theorem smallEigProg_tail_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I) {n : ℕ} (hn0' : 1 ≤ n)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : n + 1 ≤ nmax) {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S δ φ : ℝ}
    (hMS : specNorm M ≤ S) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {w q o : ℕ × ℕ} {L : ℕ} {ρ : Env}
    {ds₁ ds₂ ds₃ ds₄ : List IExp} {as₁ as₂ as₃ as₄ : List Operand}
    (hd₁ : IExp.evalList ρ.idx ds₁ = some [n + 1, n + 1])
    (ha₁ : Operand.evalList ρ as₁ = some [(L + 2, 0)])
    (hd₂ : IExp.evalList ρ.idx ds₂ = some [n + 1, n + 1, 0])
    (ha₂ : Operand.evalList ρ as₂ = some [w, w, (L + 2, 0)])
    (hd₃ : IExp.evalList ρ.idx ds₃ = some [n + 1, 0, 0, n + 1, n + 1, n + 1])
    (ha₃ : Operand.evalList ρ as₃ = some [(L + 2, 0), o, o])
    (hd₄ : IExp.evalList ρ.idx ds₄ = some [n + 1, 1, (smallEigParams nmax S δ φ c₁ c₂).length,
      smallEigCap nmax S δ φ c₁ c₂, smallEigCap nmax S δ φ c₁ c₂,
      smallEigCap nmax S δ φ c₁ c₂ + (n + 1), n + 1])
    (ha₄ : Operand.evalList ρ as₄ = some [w, (L + 1, 0), q, o, w, o, (L, 0)]) :
    PWrites law I
      (.seq (.frame ds₁ as₁ (slottedLogOpen (O := O) (Q := Q)).body)
        (.seq (.frame ds₂ as₂ (hessenbergReduceLast (O := O) (Q := Q)).body)
          (.seq (.frame ds₃ as₃ (givensReplayColumns (O := O) (Q := Q)).body)
            (.frame ds₄ as₄ (smallEigCore (O := O) (Q := Q) sG).body)))) ρ
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1))) ⊔ Fp.above L)
      (fun μ => SmallEigScratch n L (smallEigParams nmax S δ φ c₁ c₂) w q o μ ∧
        μ.store.get (L + 1) 0 = some ((smallEigParams nmax S δ φ c₁ c₂).getD 6 0) ∧
        ∃ (E V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
          HoldsMatrix w (M + E) μ.store ∧ specNorm E ≤ δ / 2 ∧ IsUnit V ∧
          (M + E) * V = V * Matrix.diagonal d ∧
          pseudoConditionNumber V ≤ 2 / smallEigCond nmax S δ φ c₂ ∧
          ∀ i j, i ≠ j → smallEigGap nmax S δ φ c₁ / 2 ≤ ‖d i - d j‖)
      (fun μ' => ∃ Ub Tb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        Schur.HoldsSchurPair w o Ub Tb μ'.store ∧ Tb.IsUpperTriangular ∧
        IsTrackedUnitarySimilar
          ((1 + 24 * u) ^ smallEigLeafRotations nmax (smallEigCap nmax S δ φ c₁ c₂) - 1) δ 1 M
          Ub Tb) (φ / 4) := by
  have h0 : Mch.lit 0 = 0 := by simpa using hNat 0 (by omega)
  have hn1 : 1 ≤ nmax := by omega
  set qs := smallEigParams nmax S δ φ c₁ c₂
  set Bw := Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))
  set Bo := Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1)))
  rw [← PWrites.seq_assoc_iff, ← PWrites.seq_assoc_iff]
  refine (PWrites.seq (F₁ := Bw ⊔ Bo ⊔ Fp.above L) (φ₁ := 0)
    (Mid := fun μ => ∃ H X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      SmallEigCoreClass nmax S δ φ c₁ c₂ H ∧
      IsTrackedUnitarySimilar ((1 + 24 * u) ^ ((n + 1) * (n + 1)) - 1) (5 * δ / 8) 1 M X H ∧
      SmallEigCoreReady qs w q o L H X μ) hI hloc (by positivity) ?_
    (smallEigProg_core_pwrites hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hb₁ hb₂ hn hδ hδS
      hφ hφ1 hu hd₄ ha₄)).mono (fun _ h => h) (by simp only [Bw, Bo]; fp_sub) (fun _ h => h)
      (by simp)
  refine PWrites.of_writes le_rfl fun μ τ ⟨hsc, hThv, E, V, d, hW, hE, hV, hAV, hκ, hgap⟩ => ?_
  obtain ⟨hlen₂, hFl, hTh, hLg, hwL, hqL, hoL, hU₁, hq, hwu, hpwu⟩ := hsc
  obtain ⟨hcl, hby⟩ := smallEigCoreClass_hessenbergReduceLastWord hM h0 hb₁ hb₂ hn hδ hδS hφ hφ1
    hu hMS hE hV hAV hκ hgap
  refine (Writes.seq_assoc_iff.mpr (smallEigProg_reduce_writes hS hM
    (le_one_div_hundred_of_le_uSmallEig hb₁ hb₂ hn1 hδ hδS hφ hφ1 hu) hL hn0' hNat hC hQ
    (length_smallEigParams _ _ _ _ _ _).ge hd₁ ha₁ hd₂ ha₂ hd₃ ha₃ hwL hqL hoL hlen₂ hFl hTh hLg
    hW hU₁ hq hThv hwu
    hpwu)).mono le_rfl fun μ' _ ⟨X, hready, hX⟩ => ⟨_, X, hcl, ⟨_, hby, ?_⟩, hready⟩
  rw [Matrix.one_mul, specNorm_one, mul_one]
  exact hX

/-- **The small-eigenvalue program in Schur form** ([BanksGarzaVargasSrivastava2025, Theorem 1.1],
with the Schur form): let the machine have the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ (`NLAlib.SmallEig.uSmallEig` at
$n_{\max}$), index literals, exact natural literals up to
$n + 1$, exact `toNat` and comparisons, a measurable interpretation reading the tape only in its
windows, draws that store the tape entry, a stream $s_U$ uniform on $[0, 1]$ with an exact polar
disk sampler on it, and a stream $s_G$ with the standard real Gaussian law; let the eigenvalue gap
and the eigenvector condition of a complex Ginibre perturbation have the tails $c_1$, $c_2$ with
$b_1, b_2 > 0$; let $n + 1 \le n_{\max}$, $\mathbf{M}$ of order $n + 1$ with
$\|\mathbf{M}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$. Then from a
memory holding $\mathbf{M}$ and the words (`NLAlib.SmallEig.SmallEigInput`), except with
probability at most $\varphi$, the run writes only the block and the accumulator and stores an
upper triangular $\widehat{\mathbf{T}}_b$ and $\widehat{\mathbf{U}}_b$ with
$\|\widehat{\mathbf{U}}_b - \mathbf{V}\|_2 \le (1 + 24\boldsymbol{u})^{R} - 1$ and
$\widehat{\mathbf{T}}_b = \mathbf{V}^{\mathsf H}(\mathbf{M} + \mathbf{E})\mathbf{V}$ for an exact
unitary $\mathbf{V}$ and some $\|\mathbf{E}\|_2 \le \delta$, $R$ =
`NLAlib.SmallEig.smallEigLeafRotations` at $n_{\max}$ and the cap. -/
theorem smallEigProg_pwrites_schur {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S δ φ : ℝ} (hMS : specNorm M ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) (w q o : ℕ × ℕ) :
    PWrites law I (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S δ φ c₁ c₂) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1)))) (SmallEigInput nmax S δ φ c₁ c₂ w q o M)
      (fun μ' => ∃ Ub Tb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        Schur.HoldsSchurPair w o Ub Tb μ'.store ∧ Tb.IsUpperTriangular ∧
        IsTrackedUnitarySimilar
          ((1 + 24 * u) ^ smallEigLeafRotations nmax (smallEigCap nmax S δ φ c₁ c₂) - 1) δ 1 M
          Ub Tb) φ := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have h0 : Mch.lit 0 = 0 := by simpa using hNat 0 (by omega)
  have h1 : Mch.lit 1 = 1 := by simpa using hNat 1 (by omega)
  obtain ⟨-, -, hred, -⟩ := uSmallEig_spec (nmax := nmax) hb₁ hb₂ (by omega) hδ hδS hφ hφ1
  set qs := smallEigParams nmax S δ φ c₁ c₂ with hqs
  set T := smallEigCap nmax S δ φ c₁ c₂ with hT
  have hR0 : 0 ≤ (1 + 24 * u) ^ smallEigLeafRotations nmax T - 1 := by
    have := one_le_pow₀ (M₀ := ℝ) (n := smallEigLeafRotations nmax T)
      (by linarith : (1 : ℝ) ≤ 1 + 24 * u)
    linarith
  set Bw := Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))
  set Bo := Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1)))
  unfold smallEigProg
  refine (PWrites.seq (F₁ := Bo) (Mid := fun μ => SmallEigInput nmax S δ φ c₁ c₂ w q o M μ ∧
    HoldsMatrix o (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) μ.store) (φ₁ := 0) hI hloc hφ.le
    ?_ ?_).mono (fun _ h => h) (sup_le le_sup_right le_rfl) (fun _ h => h) (by simp)
  · -- the identity accumulator
    exact PWrites.of_writes le_rfl fun μ τ hin => (hin.identity_writes hS h0 h1).in_frame rfl
      rfl fun x hx => hin.2.2.1 x (by simp at hx ⊢; tauto)
  refine PWrites.ifPos (n := n + 1 - 1) rfl hφ.le (fun hn0 => ?_) (fun hn0 μ ⟨⟨hW, _⟩, hU⟩ => ?_)
  swap
  · -- the order one
    obtain rfl : n = 0 := by omega
    exact ⟨1, M, ⟨hW, hU⟩, fun i j hji => absurd hji (by omega),
      (IsTrackedUnitarySimilar.refl 1 M).mono hR0 hδ.le⟩
  have hn0' : 1 ≤ n := by omega
  change PWrites law I (Stmt.allocs [.const 1, .const 1,
    .var 0 * (.const 1 + .const 5 * .var 0)] _) _ _ _ _ _
  refine PWrites.allocs (ns := [1, 1, (n + 1) * (1 + 5 * (n + 1))]) rfl
    (Pre₁ := fun L μ => SmallEigScratch n L qs w q o μ ∧ HoldsMatrix w M μ.store) ?_ ?_
    fun L => ?_
  · rintro μ s₁ ⟨hin, hU⟩ hlen₁ hlens hBelow
    exact SmallEigScratch.of_alloc hin hU (by simpa using hlen₁) hlens hBelow
  · rintro μ ⟨⟨-, -, hl, -⟩, -⟩ s s' p hBelow ⟨Ub, Tb, ⟨hTb, hUb⟩, hT, htr⟩
    exact ⟨Ub, Tb, ⟨hTb.of_below hBelow (hl w (by simp)), hUb.of_below hBelow (hl o (by simp))⟩,
      hT, htr⟩
  have hnew : ∀ {b o k b' o' k' : ℕ}, b < L → L ≤ b' →
      Fp.Disj (Store.inBlock b o k) (Store.inBlock b' o' k') :=
    fun hb hb' => Fp.disj_inBlock_of_ne (by omega)
  refine (PWrites.seq (F₁ := Store.inBlock (L + 1) 0 1) (F₂ := Bw ⊔ (Bw ⊔ Bo ⊔ Fp.above L))
    (φ₁ := 0)
    (Mid := fun μ => SmallEigScratch n L qs w q o μ ∧ HoldsMatrix w M μ.store ∧
      μ.store.get (L + 1) 0 = some (qs.getD 6 0)) hI hloc (by positivity) ?_
    (PWrites.seq (F₁ := Bw) (F₂ := Bw ⊔ Bo ⊔ Fp.above L) (φ₁ := 3 * φ / 4) (φ₂ := φ / 4)
      (Mid := fun μ => SmallEigScratch n L qs w q o μ ∧
        μ.store.get (L + 1) 0 = some (qs.getD 6 0) ∧
        ∃ (E V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
          HoldsMatrix w (M + E) μ.store ∧ specNorm E ≤ δ / 2 ∧ IsUnit V ∧
          (M + E) * V = V * Matrix.diagonal d ∧
          pseudoConditionNumber V ≤ 2 / smallEigCond nmax S δ φ c₂ ∧
          ∀ i j, i ≠ j → smallEigGap nmax S δ φ c₁ / 2 ≤ ‖d i - d j‖) hI hloc (by positivity)
      ?_ ?_)).mono (fun _ h => h) ?_ (fun _ h => h) (by linarith)
  · -- the threshold word
    refine PWrites.of_writes le_rfl fun μ τ ⟨hsc, hW⟩ => ?_
    obtain ⟨hlen₁, -, hTh, -, hwL, hqL, hoL, -, hq, -, -⟩ := id hsc
    refine (writes_call_un (hS .copy) (x := (q.1, q.2 + 6)) (z := (L + 1, 0)) rfl rfl trivial
      (Store.get_of_readBlock hq (j := 6) (by simp [qs, smallEigParams]) 0) rfl
      (by simp [hTh])).mono le_rfl ?_
    rintro μ₁ hfr ⟨-, hTh₁⟩
    exact ⟨hsc.of_eqOff hfr (hnew hoL (by omega)).symm (hnew hqL (by omega)).symm,
      hW.of_eqOff hfr (hnew hwL (by omega)).symm, hTh₁⟩
  · -- the perturbation
    refine ((ginibrePerturb_pwrites (O := O) (Q := Q) hS hM hL hSmp hG hA hB hb₁ hb₂ hδ hδS hφ hφ1
      (hu.trans hred) hn hMS (a := w) (q := q)).mono_eqOff
      (Pre' := fun μ => SmallEigScratch n L qs w q o μ ∧ HoldsMatrix w M μ.store ∧
        μ.store.get (L + 1) 0 = some (qs.getD 6 0)) ?_ ?_).in_frame rfl rfl ?_
    · rintro μ ⟨hsc, hW, -⟩
      obtain ⟨hlen₁, -, -, -, hwL, hqL, -, -, hq, -, hpwu⟩ := hsc
      exact ⟨hW, hq, by simp [Mem.Live, hlen₁]; omega,
        (hpwu.mono le_rfl le_sup_left).symm⟩
    · rintro μ μ' ⟨hsc, -, hTh⟩ hfr hpost
      obtain ⟨-, -, -, -, hwL, -, -, -, -, hwu, hpwu⟩ := id hsc
      exact ⟨hsc.of_eqOff hfr hwu (hpwu.mono le_rfl le_sup_left).symm,
        hfr.keep (Store.readsOnly_get _ _ _) (hnew hwL (by omega)) hTh, hpost⟩
    · rintro μ ⟨⟨hlen₁, -, -, -, hwL, hqL, -⟩, -⟩
      simp [Mem.Live, hlen₁]; omega
  · exact smallEigProg_tail_pwrites hS hM hL hn0' hNat hQ hC hI hloc hSmp hDisk hU hG hb₁ hb₂ hn
      hMS hδ hδS hφ hφ1 hu rfl rfl rfl rfl rfl rfl rfl rfl
  · simp only [Bw, Bo]
    fp_sub

/-- **The small-eigenvalue program as a probabilistic block** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1]): let the machine have the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ (`NLAlib.SmallEig.uSmallEig` at
$n_{\max}$), index literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons, a
measurable interpretation reading the tape only in its windows, draws that store the tape entry,
a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on it, and a stream $s_G$ with
the standard real Gaussian law; let the eigenvalue gap and the eigenvector condition of a complex
Ginibre perturbation have the tails $c_1$, $c_2$ with $b_1, b_2 > 0$; let $n + 1 \le n_{\max}$,
$\mathbf{M}$ of order $n + 1$ with $\|\mathbf{M}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$ and
$0 < \varphi \le 1$. Then from a memory holding $\mathbf{M}$ and the words
(`NLAlib.SmallEig.SmallEigInput`), except with probability at most $\varphi$, the run of
`NLAlib.SmallEig.smallEigProg` writes only its output and lists the spectrum of
$\mathbf{M} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta$
(`NLAlib.SmallEig.SmallEigSpectrum`). The order $1$ is copied; otherwise the perturbation
(`NLAlib.SmallEig.ginibrePerturb_pwrites`, $3\varphi/4$), the reduction
(`NLAlib.SmallEig.smallEigProg_reduce_pwrites`) and the core
(`NLAlib.SmallEig.smallEigProg_core_pwrites`, $\varphi/4$) compose by `NLAlib.Ops.PWrites.seq`;
the backward errors $\delta/2 + \delta/8 + \delta/4$ add. -/
theorem smallEigProg_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S δ φ : ℝ} (hMS : specNorm M ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) (w q o : ℕ × ℕ) :
    PWrites law I (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S δ φ c₁ c₂) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1)))) (SmallEigInput nmax S δ φ c₁ c₂ w q o M)
      (SmallEigSpectrum w o M δ) φ :=
  (smallEigProg_pwrites_schur hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁ hb₂ hn hMS hδ
    hδS hφ hφ1 hu w q
    o).mono (fun _ h => h) le_rfl (fun _ ⟨_, _, hP, hT, ht⟩ => smallEigSpectrum_of_tracked hP hT ht)
    le_rfl

end NLAlib.SmallEig
