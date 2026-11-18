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

/-!
# The small-eigenvalue solver: headline theorems

[BanksGarzaVargasSrivastava2025, Theorem 1.1] as a theorem about the fixed program
`NLAlib.SmallEig.smallEigProg`: on any complex matrix $\mathbf{M}$ of order at most $n_{\max}$ and
norm at most $\Sigma$, with probability at least $1 - \varphi$ the program stores all eigenvalues
of $\mathbf{M} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta$, at the unit roundoff
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$, conditional on the two random-matrix
theorems (`NLAlib.PolyLogTail.BoundsGinibreGap`, `NLAlib.PolyLogTail.BoundsGinibreCondition`),
which are hypotheses here and proved at the records
`NLAlib.ginibreGapTail` <!-- value ginibreGapTail --> $(10000e, 5, 1/2, 2)$,
`NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail --> $(128e, 3, 2, 2)$ (the
`_unconditional` corollaries). The error is absolute: $\Sigma$ is an input, the paper's relative
form is the corollary `NLAlib.SmallEig.smallEig_relative`. [BanksGarzaVargasSrivastava2025,
Corollary 1.3] is the forward contract on blocks of order at most $k_{\max}$ and norm at most
$\Sigma$ (`NLAlib.SmallEig.smallEigProg_pwrites`), which the shifted QR algorithm
consumes.

What is not claimed: a rounded Gaussian or disk sampler (the draws are exact tape values; their
rounding after the draw is modelled), range safety, the paper's question of $O(n^3)$ work.

## Main results

* `NLAlib.SmallEig.smallEigProg_pwrites`: Theorem 1.1 as a probabilistic block specification.
* `NLAlib.SmallEig.smallEig_measureReal_not_spectrum_le`: Theorem 1.1.
* `NLAlib.SmallEig.smallEig_relative`: the relative form.
* `NLAlib.SmallEig.smallEigProg_pwrites`: Corollary 1.3 as a routine contract.
* `NLAlib.SmallEig.smallEig_measureReal_not_forward_le`: Corollary 1.3 for one input.
* `NLAlib.SmallEig.smallEig_work_le`: the operation count.
* `NLAlib.SmallEig.smallEigProg_pwrites_schur`: Theorem 1.1 in Schur form, the computed
  $(\widehat{\mathbf{U}}_b, \widehat{\mathbf{T}}_b)$ tracked from $(\mathbf{I}, \mathbf{M})$.
* `NLAlib.SmallEig.smallEigProg_randomSchurLeafContract`: the program is a small-block Schur
  solver (`NLAlib.Schur.RandomSchurLeafContract`) at the forward words.
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

/-- A tracked Schur pair lists a nearby spectrum (PP3 at the leaf): if the stored pair
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
  simp only [Set.ofPred_and]
  refine (Mem.measurableSet_eqOff F).inter ((measurable_snd (measurableSet_forall_isSome w _)).inter
    ((measurable_snd (measurableSet_forall_isSome ub _)).inter ((?_ : MeasurableSet _).inter
      ((isClosed_setOf_isTrackedUnitarySimilar εU δ).measurableSet.preimage
        (measurable_const.prodMk ((hm ub).prodMk (hm w)))))))
  simp only [Matrix.IsUpperTriangular, Matrix.BlockTriangular, Set.ofPred_forall]
  refine .iInter fun i => .iInter fun j => ?_
  by_cases hij : j < i
  · simpa [hij] using measurableSet_eq_fun ((Matrix.measurable_apply i j).comp (hm w))
      measurable_const
  · simp [hij]

omit [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q] in
/-- Reassociate three blocks of a probabilistic block specification. -/
theorem PWrites.seq_assoc_iff' {law : ℕ → Measure ℝ} {I : Interp O Q ℝ} {ρ : Env}
    {a b c : Stmt O Q} {F : Fp} {Pre Post : Mem ℝ → Prop} {φ : ℝ} :
    PWrites law I (.seq (.seq a b) c) ρ F Pre Post φ ↔
      PWrites law I (.seq a (.seq b c)) ρ F Pre Post φ := by
  constructor <;> rintro ⟨G, hGm, hGd, hG⟩ <;>
    exact ⟨G, hGm, hGd, fun m hm => ⟨fun τ hτ => by
      first
      | exact Writes.seq_assoc_iff.mp ((hG m hm).1 τ hτ)
      | exact Writes.seq_assoc_iff.mpr ((hG m hm).1 τ hτ), (hG m hm).2⟩⟩

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
  have hRp := smallEigReplay_le_omega hb₁ hb₂ hn1 hu0 hδ hδS hφ hφ1 hu
  have hΩ := two_mul_mul_smallEigOmega (c₁ := c₁) (c₂ := c₂) hn1 S δ φ
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
  -- the worklist's backward error is within `X`
  have hK : 2 * ((n : ℝ) + 1) * (2.25 * ω + ε + 0 + 78 * u * (((T : ℝ) + ((n : ℝ) + 1)) *
      ((n : ℝ) + 1)) * (2 * S) + 8 * ((n : ℝ) + 1) * (1 + 2) * u * (2 * S)) ≤ X := by
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    have hr1 : ((T : ℝ) + ((n : ℝ) + 1)) * ((n : ℝ) + 1) ≤ ((T : ℝ) + nmax) * nmax := by gcongr
    have hus : 0 ≤ u * (2 * S) := by positivity
    have hr2 : 78 * u * (((T : ℝ) + ((n : ℝ) + 1)) * ((n : ℝ) + 1)) * (2 * S) +
        8 * ((n : ℝ) + 1) * (1 + 2) * u * (2 * S) ≤ ω := by
      refine le_trans ?_ hRp
      nlinarith [mul_le_mul_of_nonneg_right hr1 hus, mul_le_mul_of_nonneg_right hnn hus]
    have hb : 2.25 * ω + ε + 0 + 78 * u * (((T : ℝ) + ((n : ℝ) + 1)) * ((n : ℝ) + 1)) * (2 * S) +
        8 * ((n : ℝ) + 1) * (1 + 2) * u * (2 * S) ≤ 3.26 * ω := by linarith
    calc _ ≤ 2 * (nmax : ℝ) * (3.26 * ω) := by
          have := mul_le_mul hb (by linarith : 2 * ((n : ℝ) + 1) ≤ 2 * nmax)
            (by linarith [hω.le]) (by positivity)
          linarith
      _ ≤ X := by nlinarith
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
  refine PStep.mono (PWrites.pstep_of_forall hI hloc (F := F)
    (P := fun (x : ι) μ => SmallEigCoreReady qs w p ub L x.1.1 x.1.2 μ) (fun x => ?_)
    (measurableSet_smallEigOutcome εU δ M w ub F) ?_)
    (fun μ ⟨H, X', hc, ht, hr⟩ => ⟨⟨(H, X'), hc, ht⟩, hr⟩) ?_ ?_
  · obtain ⟨hHess, ⟨V, d, hV, hHV, hκ, hgap⟩, hHS⟩ := x.2.1
    exact (solveRoundedWith_pwrites (c := 2.25 * ω) (thr := qs.getD 6 0) (a := w)
      (t := (L + 1, 0)) (p := p) (uo := ub) (f := (L, 0)) (U := x.1.2) hS hM hu0 (by linarith)
      hL hNat hQ hC hI hloc _ hDn _ hLeaf hφD le_rfl le_rfl hHess hV hHV hκ hsep hgap
      (by rw [h6]; nlinarith [sq_nonneg (1.5 * ω)]) (by rw [h6]; nlinarith [sq_nonneg ω])
      (by positivity) le_rfl hε0 (by push_cast; linarith) (by push_cast; linarith)).in_frame hd
      ha fun μ h => h.1
  · rintro x μ μ' - hfr ⟨-, U', Tm, hTm, hU', hup, htr⟩
    have h₁ : 0 ≤ (1 + 24 * u) ^ ((n + 1) * (n + 1)) - 1 := by
      have := one_le_pow₀ (M₀ := ℝ) (n := (n + 1) * (n + 1)) (by linarith : (1 : ℝ) ≤ 1 + 24 * u)
      linarith
    have h₂ : 0 ≤ (1 + 24 * u) ^ (2 * (n + 1) * ((T + (n + 1)) * (n + 1) + 2 * 1 * (1 + 2))) *
        (1 + 0) ^ (n + 1) - 1 := by
      have := one_le_pow₀ (M₀ := ℝ) (n := 2 * (n + 1) * ((T + (n + 1)) * (n + 1) + 2 * 1 * (1 + 2)))
        (by linarith : (1 : ℝ) ≤ 1 + 24 * u)
      simp only [add_zero, one_pow, mul_one]; linarith
    have htr' := (x.2.2.trans h₁ h₂ htr).mono (smallEigLeaf_accumulator_le hu0 hn)
      (by push_cast; linarith)
    rw [hTm.eq_storedMatrix, hU'.eq_storedMatrix] at htr'
    rw [hTm.eq_storedMatrix] at hup
    exact ⟨hfr, fun j hj => by rw [Store.get_of_readBlock hTm hj 0]; rfl,
      fun j hj => by rw [Store.get_of_readBlock hU' hj 0]; rfl, hup, htr'⟩
  · rintro μ μ' - ⟨hfr, hw, hub, hup, htr⟩
    exact ⟨hfr, _, _, ⟨holdsMatrix_storedMatrix hw, holdsMatrix_storedMatrix hub⟩, hup, htr⟩
  · unfold smallEigDecouplerFailure
    rw [add_zero, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- **The small-eigenvalue program in Schur form** ([BanksGarzaVargasSrivastava2025, Theorem 1.1],
with the Schur form): let the machine have the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ (`NLAlib.SmallEig.uSmallEig` at
$n_{\max}$) and $\boldsymbol{u} \le 1/100$, index literals, exact natural literals up to
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
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu1 : u ≤ 1 / 100)
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
  have hn1 : 1 ≤ nmax := by omega
  obtain ⟨-, -, hred, -⟩ := uSmallEig_spec hb₁ hb₂ hn1 hδ hδS hφ hφ1
  set qs := smallEigParams nmax S δ φ c₁ c₂ with hqs
  set T := smallEigCap nmax S δ φ c₁ c₂ with hT
  have hlen : qs.length = 12 := length_smallEigParams _ _ _ _ _ _
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
    refine PWrites.of_writes le_rfl fun μ τ hin => ?_
    obtain ⟨hW, hq, hl, hroom, hwo, hqwo⟩ := hin
    refine ((identityLeaf_writes (O := O) (Q := Q) (ps := qs) (T := T) (τ := τ) hS h0
      (fun _ => h1) (fun x hx => hl x (by simp at hx ⊢; tauto)) hroom hwo).in_frame rfl rfl
      (fun x hx => hl x (by simp at hx ⊢; tauto))).mono le_rfl fun μ' hfr ⟨-, hU⟩ => ?_
    refine ⟨⟨hW.of_eqOff hfr hwo.symm,
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hqwo.mono le_rfl le_sup_right).symm hq,
      fun x hx => hfr.length_eq ▸ hl x hx, by rw [hfr.len_eq]; exact hroom, hwo, hqwo⟩, hU⟩
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
  · rintro μ s₁ ⟨⟨hW, hq, hl, -, hwo, hqwo⟩, hU⟩ hlen₁ hlens hBelow
    simp only [List.length_cons, List.length_nil] at hlen₁
    have hwL : w.1 < μ.store.length := hl w (by simp)
    have hqL : q.1 < μ.store.length := hl q (by simp)
    have hoL : o.1 < μ.store.length := hl o (by simp)
    exact ⟨⟨hlen₁, by simpa using hlens 0 (by simp), by simpa using hlens 1 (by simp),
      by simpa using hlens 2 (by simp), hwL, hqL, hoL, hU.of_below hBelow hoL,
      hBelow.readBlock_of hqL hq, hwo, hqwo⟩, hW.of_below hBelow hwL⟩
  · rintro μ ⟨⟨-, -, hl, -⟩, -⟩ s s' p hBelow ⟨Ub, Tb, ⟨hTb, hUb⟩, hT, htr⟩
    exact ⟨Ub, Tb, ⟨hTb.of_below hBelow (hl w (by simp)), hUb.of_below hBelow (hl o (by simp))⟩,
      hT, htr⟩
  have hnew : ∀ {b o k b' o' k' : ℕ}, b < L → L ≤ b' →
      Fp.Disj (Store.inBlock b o k) (Store.inBlock b' o' k') :=
    fun hb hb' => Fp.disj_inBlock_of_ne (by omega)
  refine (PWrites.seq (F₁ := Store.inBlock (L + 1) 0 1) (φ₁ := 0)
    (Mid := fun μ => SmallEigScratch n L qs w q o μ ∧ HoldsMatrix w M μ.store ∧
      μ.store.get (L + 1) 0 = some (qs.getD 6 0)) hI hloc (by positivity) ?_
    (PWrites.seq (F₁ := Bw) (φ₁ := 3 * φ / 4) (φ₂ := φ / 4)
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
    obtain ⟨hlen₁, -, hTh, -, hwL, hqL, hoL, -, hq, -, -⟩ := hsc
    refine (writes_call_un (hS .copy) (x := (q.1, q.2 + 6)) (z := (L + 1, 0)) rfl rfl trivial
      (Store.get_of_readBlock hq (j := 6) (by omega) 0) rfl (by simp [hTh])).mono le_rfl ?_
    rintro μ₁ hfr ⟨-, hTh₁⟩
    exact ⟨hsc.of_eqOff hfr (hnew hoL (by omega)).symm (hnew hqL (by omega)).symm, hW.of_eqOff hfr (hnew hwL (by omega)).symm, hTh₁⟩
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
      obtain ⟨-, -, -, -, hwL, -, -, -, -, hwu, hpwu⟩ := hsc
      exact ⟨hsc.of_eqOff hfr hwu (hpwu.mono le_rfl le_sup_left).symm,
        hfr.keep (Store.readsOnly_get _ _ _) (hnew hwL (by omega)) hTh, hpost⟩
    · rintro μ ⟨⟨hlen₁, -, -, -, hwL, hqL, -⟩, -⟩
      simp [Mem.Live, hlen₁]; omega
  · -- the reduction, the replay and the core
    rw [← PWrites.seq_assoc_iff', ← PWrites.seq_assoc_iff']
    refine (PWrites.seq (F₁ := Bw ⊔ Bo ⊔ Fp.above L) (φ₁ := 0)
      (Mid := fun μ => ∃ H X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        SmallEigCoreClass nmax S δ φ c₁ c₂ H ∧
        IsTrackedUnitarySimilar ((1 + 24 * u) ^ ((n + 1) * (n + 1)) - 1) (5 * δ / 8) 1 M X H ∧
        SmallEigCoreReady qs w q o L H X μ) hI hloc (by positivity) ?_
      (smallEigProg_core_pwrites hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hb₁ hb₂ hn hδ hδS
        hφ hφ1 hu rfl rfl)).mono (fun _ h => h) le_rfl (fun _ h => h) (by simp)
    refine PWrites.of_writes le_rfl fun μ τ ⟨hsc, hThv, E, V, d, hW, hE, hV, hAV, hκ, hgap⟩ => ?_
    obtain ⟨hlen₂, hFl, hTh, hLg, hwL, hqL, hoL, hU₁, hq, hwu, hpwu⟩ := hsc
    obtain ⟨hcl, hby⟩ := smallEigCoreClass_hessenbergReduceLastWord hM h0 hb₁ hb₂ hn hδ hδS hφ hφ1
      hu hMS hE hV hAV hκ hgap
    refine (Writes.seq_assoc_iff.mpr (smallEigProg_reduce_writes hS hM
      (le_one_div_hundred_of_le_uSmallEig hb₁ hb₂ hn1 hδ hδS hφ hφ1 hu) hL hn0' hNat hC hQ
      (by omega) rfl rfl rfl rfl rfl rfl hwL hqL hoL hlen₂ hFl hTh hLg hW hU₁ hq hThv hwu
      hpwu)).mono le_rfl fun μ' _ ⟨X, hready, hX⟩ => ⟨_, X, hcl, ⟨_, hby, ?_⟩, hready⟩
    rw [Matrix.one_mul, specNorm_one, mul_one]
    exact hX
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
  (smallEigProg_pwrites_schur hS hM (le_one_div_hundred_of_le_uSmallEig hb₁ hb₂ (by omega) hδ hδS
    hφ hφ1 hu) hL hNat hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁ hb₂ hn hMS hδ hδS hφ hφ1 hu w q
    o).mono (fun _ h => h) le_rfl (fun _ ⟨_, _, hP, hT, ht⟩ => smallEigSpectrum_of_tracked hP hT ht)
    le_rfl

/-- **The backward listing at $\delta_b$ is a forward one at $\beta$**
([BanksGarzaVargasSrivastava2025, Corollary 1.3], the matching): for $\mathbf{M}$ of order
$n + 1 \le k_{\max}$ with $\|\mathbf{M}\|_2 \le \Sigma$ and $0 < \beta \le \Sigma$, an output
listing the spectrum of $\mathbf{M} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta_b$
(`NLAlib.SmallEig.forwardBackwardError`) is within $\beta$ of a listing of the spectrum of
$\mathbf{M}$, by the Ostrowski–Elsner matching
(`NLAlib.exists_isEigenvalueListing_norm_sub_le_rpow`) and
`NLAlib.SmallEig.forwardBackwardError_spec`. -/
theorem smallEigSpectrum_forward {kmax n : ℕ} (hn : n + 1 ≤ kmax) {S β : ℝ} (hβ : 0 < β)
    (hβS : β ≤ S) {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hMS : specNorm M ≤ S)
    {o : ℕ × ℕ} {μ' : Mem ℝ} {w : ℕ × ℕ}
    (h : SmallEigSpectrum w o M (forwardBackwardError kmax S β) μ') :
    ∃ (Tb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ev : Fin (n + 1) → ℂ),
      HoldsMatrix w Tb μ'.store ∧ IsEigenvalueListing M ev ∧ ∀ i, ‖Tb i i - ev i‖ ≤ β := by
  obtain ⟨Tb, -, E, hW, -, -, hE, hL⟩ := h
  obtain ⟨-, hbS, h2⟩ := forwardBackwardError_spec (kmax := kmax) hβ hβS
  obtain ⟨ev, hev, hb⟩ := exists_isEigenvalueListing_norm_sub_le_rpow (A' := M) hL
  refine ⟨Tb, ev, hW, hev, fun i => ?_⟩
  rw [norm_sub_rev]
  refine (hb i).trans (le_trans ?_ (h2 n hn))
  have hα : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hE' : specNorm (M - (M + E)) = specNorm E := by rw [sub_add_cancel_left, specNorm_neg]
  have hsum : specNorm (M + E) + specNorm M ≤ 3 * S := by
    linarith [specNorm_add_le M E]
  have h0 : 0 ≤ specNorm (M + E) + specNorm M := by positivity
  rw [hE']
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 hsum hα) (by positivity))
    (Real.rpow_le_rpow (specNorm_nonneg _) hE (by positivity)) (by positivity)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))

/-- **The small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025, Theorem 1.1], corrected:
$\Sigma$ an input, the base case of order $1$, every loop capped, the error absolute). Let the
machine have the standard model at $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$, index
literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons, a measurable
interpretation reading the tape only in its windows, draws that store the tape entry, a stream
$s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on it, and a stream $s_G$ with the
standard real Gaussian law; let the eigenvalue gap and the eigenvector condition of a complex
Ginibre perturbation have the tails $c_1$, $c_2$ with $b_1, b_2 > 0$. Let $n + 1 \le n_{\max}$,
$\mathbf{M}$ of order $n + 1$ with $\|\mathbf{M}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$ and
$0 < \varphi \le 1$. Then from a memory holding $\mathbf{M}$ and the words of
`NLAlib.SmallEig.smallEigParams`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{smallEigProg}(\mathbf{M}) \text{ fails, or writes outside its output,
  or lists no } \operatorname{spec}(\mathbf{M} + \mathbf{E}),\ \|\mathbf{E}\|_2 \le \delta\bigr]
  \le \varphi\,.$$
Here $\boldsymbol{u}_{\mathrm{SmallEig}}$ is `NLAlib.SmallEig.uSmallEig` at $n_{\max}$.
[BanksGarzaVargasSrivastava2025, Theorem 1.1]; there $\Sigma$ is not an input (its errata P9,
N4) and the error is relative.

Note: The run terminates on every tape (`NLAlib.SmallEig.smallEigProg_terminates`). The failure
is split in four: the gap, the condition, the norm of the perturbation, and the worklist.
Result: small-eig-backward-error -/
theorem smallEig_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
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
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S δ φ c₁ c₂ w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S δ φ c₁ c₂) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1)))) (SmallEigSpectrum w o M δ) μ} ≤ φ :=
  (smallEigProg_pwrites hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁ hb₂ hn hMS hδ hδS hφ
    hφ1 hu w q o).measureReal_not_writes_le hin hξ

/-- **The small-eigenvalue solver, relative form** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], as printed: the error relative to $\|\mathbf{M}\|_2$). With the hypotheses on the
machine, the streams and the tails of `NLAlib.SmallEig.smallEig_measureReal_not_spectrum_le`
written out below: let $n + 1 \le n_{\max}$, $\mathbf{M}$ of order $n + 1$, $c \ge 1$ and
$\Sigma > 0$ with $\|\mathbf{M}\|_2 \le \Sigma \le c\|\mathbf{M}\|_2$, $0 < \varepsilon \le 1$,
$0 < \varphi \le 1$, and $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ at the absolute
error $\varepsilon\Sigma/c$. Then from a memory holding $\mathbf{M}$ and the words at
$\delta = \varepsilon\Sigma/c$,
$$\mathbb{P}\bigl[\mathsf{smallEigProg}(\mathbf{M}) \text{ fails, or writes outside its output,
  or lists no } \operatorname{spec}(\mathbf{M} + \mathbf{E}),\
  \|\mathbf{E}\|_2 \le \varepsilon\|\mathbf{M}\|_2\bigr] \le \varphi\,.$$
[BanksGarzaVargasSrivastava2025, Theorem 1.1]; the bound $\Sigma$ of the norm is an input there
too (its errata P9, N4).
Result: small-eig-backward-error -/
theorem smallEig_relative {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S c ε φ : ℝ} (hS0 : 0 < S) (hMS : specNorm M ≤ S)
    (hc : 1 ≤ c) (hSM : S ≤ c * specNorm M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S (ε * S / c) φ c₁ c₂)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S (ε * S / c) φ c₁ c₂ w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S (ε * S / c) φ c₁ c₂) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1))))
            (SmallEigSpectrum w o M (ε * specNorm M)) μ} ≤ φ := by
  have hc0 : 0 < c := by linarith
  have hδ : 0 < ε * S / c := by positivity
  have hδS : ε * S / c ≤ S := by
    rw [div_le_iff₀ hc0]; nlinarith
  have hδM : ε * S / c ≤ ε * specNorm M := by
    rw [div_le_iff₀ hc0]; nlinarith [mul_le_mul_of_nonneg_left hSM hε.le]
  exact ((smallEigProg_pwrites hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁ hb₂ hn hMS
    hδ hδS hφ hφ1 hu w q o).mono (fun _ h => h) le_rfl
    (fun _ ⟨Tb, Ub, E, hT, hO, hTu, hE, hLst⟩ => ⟨Tb, Ub, E, hT, hO, hTu, hE.trans hδM, hLst⟩)
    le_rfl).measureReal_not_writes_le hin hξ

/-- **The forward error on one input** ([BanksGarzaVargasSrivastava2025, Corollary 1.3]): with the
hypotheses on the machine, the streams and the tails written out in
`NLAlib.SmallEig.smallEigProg_pwrites` (standard model at
$\boldsymbol{u} \le \boldsymbol{u}^{\mathrm{fwd}}_{\mathrm{SmallEig}}$, exact literals up to
$k_{\max}$, a measurable tape-local interpretation, the uniform and Gaussian streams, the tails
with $b_1, b_2 > 0$): for $\mathbf{M}$ of order $n + 1 \le k_{\max}$ with
$\|\mathbf{M}\|_2 \le \Sigma$, $0 < \beta \le \Sigma$ and $0 < \varphi \le 1$, from a memory
holding $\mathbf{M}$ and the words `NLAlib.SmallEig.smallEigForwardParams`,
$$\mathbb{P}\bigl[\mathsf{smallEigProg}(\mathbf{M}) \text{ fails, or writes outside its output,
  or lists no } \boldsymbol{\mu} \text{ with } \lvert\mu_i - \lambda_i\rvert \le \beta\bigr]
  \le \varphi$$
for a listing $\boldsymbol{\lambda}$ of the eigenvalues of $\mathbf{M}$.
Result: small-eig-forward-error -/
theorem smallEig_measureReal_not_forward_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    {kmax : ℕ} (hNat : IsExactNatLit id Mch kmax) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {S β φ : ℝ} (hβ : 0 < β) (hβS : β ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEigForward kmax S β φ c₁ c₂) {n : ℕ} (hn : n + 1 ≤ kmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hMS : specNorm M ≤ S) {w q o : ℕ × ℕ}
    {μ : Mem ℝ} (hin : SmallEigInput kmax S (forwardBackwardError kmax S β) φ c₁ c₂ w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n kmax S (forwardBackwardError kmax S β) φ c₁ c₂) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1))))
      (fun μ' => ∃ (Tb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ev : Fin (n + 1) → ℂ),
        HoldsMatrix w Tb μ'.store ∧ IsEigenvalueListing M ev ∧ ∀ i, ‖Tb i i - ev i‖ ≤ β) μ} ≤ φ := by
  obtain ⟨hb0, hbS, -⟩ := forwardBackwardError_spec (kmax := kmax) hβ hβS
  exact ((smallEigProg_pwrites hS hM hL (hNat.mono hn) hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁
    hb₂ hn hMS hb0 hbS hφ hφ1 hu w q o).mono (fun _ h => h) le_rfl
    (fun _ h => smallEigSpectrum_forward hn hβ hβS hMS h) le_rfl).measureReal_not_writes_le hin hξ

/-- **The operation count of the small-eigenvalue program** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], running time, on every tape): there is an absolute constant $c$ such that the static
count (`NLAlib.Ops.stmtCost`) of `NLAlib.SmallEig.smallEigProg` at the order $n + 1$, $n_q$ words
and the cap $T$ has at most $c(n + 1)^4(T + 1)^2$ operations and tests. The count holds on every
tape: the loops are capped by $T$ ($m, t, m_2 \le T$, $q \le m$). The paper's count has the factor
$n$ in its last term (its erratum N5). The monomial bound of the tree
(`NLAlib.Ops.size_stmtCost_le_stmtWorkMono`) gives $c = 4629$; the certificate's
`NLAlib.SmallEig.smallEigWork` is larger because its instrumentation also counts the structural
instructions. -/
theorem smallEig_work_le (sG : ℕ) : ∃ c : ℕ, ∀ n nq T : ℕ,
    Count.size (stmtCost (smallEigProg (O := O) (Q := Q) sG).body [n + 1, nq, T]) ≤
      c * (n + 1) ^ 4 * (T + 1) ^ 2 := by
  refine ⟨4629, fun n nq T => ?_⟩
  have hw : stmtWorkMono (smallEigProg (O := O) (Q := Q) sG).body
      [⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩] = ⟨4629, [4, 0, 2]⟩ := by
    kernel_rfl
  have hσ : SlotsLe [n + 1, nq + 1, T + 1] [n + 1, nq, T]
      [⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩] := by
    simp [SlotsLe, WorkMono.eval]
  refine (size_stmtCost_le_stmtWorkMono (by simp) _ hσ).trans ?_
  rw [hw]
  simp [WorkMono.eval, mul_assoc]

/-- **The cap of the small-eigenvalue program is polylogarithmic**: for tail records with
$b_1, b_2 > 0$ there are constants $c$ and $p$ with
$T \le c(\log_2(4(n_{\max} + 1)\Sigma/(\delta\varphi)) + 1)^p$, $T$ = `NLAlib.SmallEig.smallEigCap`,
for every $n_{\max} \ge 1$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$ (the degree, round and
step caps are logarithms of the condition, weight and accuracy thresholds, themselves polynomial in
$n_{\max}\Sigma/(\delta\varphi)$). -/
theorem smallEigCap_le_log (c₁ c₂ : PolyLogTail) (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    ∃ (c : ℝ) (p : ℕ), ∀ {nmax : ℕ} {S δ φ : ℝ}, 1 ≤ nmax → 0 < δ → δ ≤ S → 0 < φ → φ ≤ 1 →
      (smallEigCap nmax S δ φ c₁ c₂ : ℝ) ≤
        c * (Real.logb 2 (4 * (nmax + 1) * S / (δ * φ)) + 1) ^ p := by
  obtain ⟨c, hc, h⟩ := smallEigCap_le_logb c₁ c₂ hb₁ hb₂
  refine ⟨c, 1, fun {nmax S δ φ} hn hδ hδS hφ hφ1 => (h hn hδ hδS hφ hφ1).trans ?_⟩
  have hn' : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
  have hS : 0 < S := hδ.trans_le hδS
  rw [pow_one]
  gcongr
  · exact Real.logb_le_logb_of_le (by norm_num) (by positivity) (by gcongr; linarith)

/-- **The small-eigenvalue program is a small-block Schur solver**
([BanksGarzaVargasSrivastava2025, Theorem 1.1 and Corollary 1.3], with the Schur form): on the
machine and streams of `NLAlib.SmallEig.smallEigProg_pwrites_schur`, with exact natural literals
up to $d_{\max} \le k_{\max}$, $0 < \beta \le \Sigma$, $0 < \varphi \le 1$ and
$\boldsymbol{u} \le \boldsymbol{u}^{\mathrm{fwd}}_{\mathrm{SmallEig}}$
(`NLAlib.SmallEig.uSmallEigForward`) and $\boldsymbol{u} \le 1/100$, the program with the forward
words `NLAlib.SmallEig.smallEigForwardParams` and cap meets
`NLAlib.Schur.RandomSchurLeafContract` on the orders at most $d_{\max}$ and norms at most
$\Sigma$: the backward error is the backward accuracy
$\delta_b$ = `NLAlib.SmallEig.forwardBackwardError` of $\beta$, the failure $\varphi$ and the
accumulator error $(1 + 24\boldsymbol{u})^R - 1$, $R$ = `NLAlib.SmallEig.smallEigLeafRotations`
at $k_{\max}$ and the cap. Orders $d \le 1$ are kept with the identity accumulator. -/
theorem smallEigProg_randomSchurLeafContract {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu1 : u ≤ 1 / 100) (hL : IsIndexLit Mch I)
    {dmax kmax : ℕ} (hdk : dmax ≤ kmax) (hNat : IsExactNatLit id Mch dmax) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {S β φ : ℝ} (hβ : 0 < β) (hβS : β ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEigForward kmax S β φ c₁ c₂) :
    Schur.RandomSchurLeafContract law
      ((1 + 24 * u) ^ smallEigLeafRotations kmax (smallEigForwardCap kmax S β φ c₁ c₂) - 1)
      (forwardBackwardError kmax S β) φ dmax S (smallEigForwardParams kmax S β φ c₁ c₂)
      (smallEigForwardCap kmax S β φ c₁ c₂) (smallEigProg (O := O) (Q := Q) sG) I := by
  intro d w p ub B hd hBS
  obtain ⟨hb0, hbS, -⟩ := forwardBackwardError_spec (kmax := kmax) hβ hβS
  have hR0 : 0 ≤ (1 + 24 * u) ^ smallEigLeafRotations kmax
      (smallEigForwardCap kmax S β φ c₁ c₂) - 1 := by
    have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
    have := one_le_pow₀ (M₀ := ℝ) (n := smallEigLeafRotations kmax
      (smallEigForwardCap kmax S β φ c₁ c₂)) (by linarith : (1 : ℝ) ≤ 1 + 24 * u)
    linarith
  rcases d with _ | n
  · have h0 : Mch.lit 0 = 0 := by simpa using hM.lit 0
    refine PWrites.of_writes hφ.le fun μ τ ⟨hW, _, hl, hroom, hap⟩ => ?_
    have hwu : Fp.Disj (Store.inBlock w.1 w.2 (2 * (0 * 0)))
        (Store.inBlock ub.1 ub.2 (2 * (0 * 0))) := by
      simpa using hap.disj_getD_of_lt (i := 0) (j := 2) (by omega) (by simp)
    unfold smallEigProg
    have hl4 : μ.Live [w, p, w, ub] := fun x hx => hl x (by simp at hx ⊢; tauto)
    refine (identityLeaf_writes (O := O) (Q := Q) (τ := τ) hS h0 (fun h => absurd h (lt_irrefl 0))
      hl hroom hwu).frame_seq_le rfl rfl hl4 le_sup_right ?_
    rintro μ' hfr ⟨-, hU⟩
    refine writes_ifPos (n := 0) rfl ?_
    rw [if_neg (lt_irrefl 0)]
    refine ⟨1, B, ⟨hW.of_eqOff hfr hwu.symm, hU⟩, fun i => i.elim0,
      (IsTrackedUnitarySimilar.refl 1 B).mono hR0 hb0.le⟩
  · have hdk' : n + 1 ≤ kmax := hd.trans hdk
    refine (smallEigProg_pwrites_schur hS hM hu1 hL (hNat.mono hd) hQ hC hI hloc hSmp hDisk hU hG
      hA hB hb₁ hb₂ hdk' hBS hb0 hbS hφ hφ1 hu w p ub).mono ?_ le_rfl (fun _ h => h) le_rfl
    rintro μ ⟨hW, hq, hl, hroom, hap⟩
    simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true] at hap
    exact ⟨hW, hq, hl, hroom, hap.1.2, Fp.disj_sup_right.mpr ⟨hap.1.1.symm, hap.2⟩⟩

/-! ### With the proved random-matrix tails -/

/-- **The small-eigenvalue solver, unconditional**.
The unconditional form of `NLAlib.SmallEig.smallEig_measureReal_not_spectrum_le`
([BanksGarzaVargasSrivastava2025, Theorem 1.1]): the eigenvalue-gap and eigenvector-condition tails
of a complex Ginibre perturbation are proved, at the records
`NLAlib.ginibreGapTail` <!-- value ginibreGapTail --> $(10000e, 5, 1/2, 2)$ and
`NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail --> $(128e, 3, 2, 2)$.
Result: small-eig-backward-error -/
theorem smallEig_measureReal_not_spectrum_le_unconditional {Mch : Machine ℝ} {I : Interp O Q ℝ} {u
  : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S δ φ : ℝ} (hMS : specNorm M ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ ginibreGapTail ginibreConditionTail)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S δ φ ginibreGapTail
      ginibreConditionTail w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S δ φ ginibreGapTail
        ginibreConditionTail) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1)))) (SmallEigSpectrum w o M δ) μ} ≤ φ := by
  apply smallEig_measureReal_not_spectrum_le
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

/-- **The small-eigenvalue solver, relative form, unconditional**.
The unconditional form of `NLAlib.SmallEig.smallEig_relative` ([BanksGarzaVargasSrivastava2025,
Theorem 1.1]): the eigenvalue-gap and eigenvector-condition tails of a complex Ginibre perturbation
are proved, at the records `NLAlib.ginibreGapTail` <!-- value ginibreGapTail -->
$(10000e, 5, 1/2, 2)$ and `NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail -->
$(128e, 3, 2, 2)$.
Result: small-eig-backward-error -/
theorem smallEig_relative_unconditional {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S c ε φ : ℝ} (hS0 : 0 < S) (hMS : specNorm M ≤ S)
    (hc : 1 ≤ c) (hSM : S ≤ c * specNorm M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S (ε * S / c) φ ginibreGapTail
      ginibreConditionTail)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S (ε * S / c) φ
      ginibreGapTail ginibreConditionTail w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S (ε * S / c) φ ginibreGapTail
        ginibreConditionTail) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1))))
            (SmallEigSpectrum w o M (ε * specNorm M)) μ} ≤ φ := by
  apply smallEig_relative
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

/-- **The forward error on one input, unconditional**.
The unconditional form of `NLAlib.SmallEig.smallEig_measureReal_not_forward_le`
([BanksGarzaVargasSrivastava2025, Corollary 1.3]): the eigenvalue-gap and eigenvector-condition
tails of a complex Ginibre perturbation are proved, at the records
`NLAlib.ginibreGapTail` <!-- value ginibreGapTail --> $(10000e, 5, 1/2, 2)$ and
`NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail --> $(128e, 3, 2, 2)$.
Result: small-eig-forward-error -/
theorem smallEig_measureReal_not_forward_le_unconditional {Mch : Machine ℝ} {I : Interp O Q ℝ} {u :
  ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    {kmax : ℕ} (hNat : IsExactNatLit id Mch kmax) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {S β φ : ℝ} (hβ : 0 < β) (hβS : β ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEigForward kmax S β φ ginibreGapTail
      ginibreConditionTail) {n : ℕ} (hn : n + 1 ≤ kmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hMS : specNorm M ≤ S) {w q o : ℕ × ℕ}
    {μ : Mem ℝ} (hin : SmallEigInput kmax S (forwardBackwardError kmax S β) φ
      ginibreGapTail ginibreConditionTail w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n kmax S (forwardBackwardError kmax S β) φ
        ginibreGapTail ginibreConditionTail) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1))))
      (fun μ' => ∃ (Tb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ev : Fin (n + 1) → ℂ),
        HoldsMatrix w Tb μ'.store ∧ IsEigenvalueListing M ev ∧ ∀ i, ‖Tb i i - ev i‖ ≤ β) μ} ≤ φ := by
  apply smallEig_measureReal_not_forward_le
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

end NLAlib.SmallEig
