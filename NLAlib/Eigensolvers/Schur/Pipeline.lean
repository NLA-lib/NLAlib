/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Residual
public import NLAlib.Ops.Blas.Matrix
public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.OperationCount
public import NLAlib.Ops.Confined
public import NLAlib.Ops.Static
public import NLAlib.Ops.MonomialWork
public import NLAlib.Matrix.Spectral.Schur
public import NLAlib.Matrix.FinitePrecision.Deflation
public import NLAlib.Eigensolvers.ShiftedQR.RoundedHeadline
public import NLAlib.Probability.Measurability.Matrix

/-!
# The generic dense Schur pipeline

`NLAlib.Schur.schurPipelineWith Nm Reg Red Core` composes any four stages that meet their
contracts (`NLAlib.Eigensolvers.Schur.Contracts`): estimate $s \approx \|\mathbf{A}\|_{\mathsf F}$;
if $s$ is zero ($\mathbf{A} = 0$) store $\widehat{\mathbf{U}} = \mathbf{I}$ and the flag $0$;
otherwise scale $\mathbf{A}$ by $\mathrm{fl}(1/s)$, regularize, set $\widehat{\mathbf{U}} =
\mathbf{I}$, reduce to Hessenberg form, run the Schur core and scale back by $s$. The generic
composition theorem adds the stages' errors and failure probabilities; the computed form of the
output comes from the tracked relation (`NLAlib.IsTrackedUnitarySimilar`).

## Main definitions

* `NLAlib.Schur.schurPipelineWith`: the pipeline program.
* `NLAlib.Schur.SchurPipelineInput`, `NLAlib.Schur.SchurOutput`, `NLAlib.Schur.SchurOrth`,
  `NLAlib.Schur.schurFp`: its input memory, output, all-tape output and footprint.

## Main results

* `NLAlib.Schur.schurPipelineWith_measureReal_not_schur_le`: the generic composition theorem.
* `NLAlib.Schur.SchurOutput.exists_isEigenvalueListing`,
  `NLAlib.Schur.SchurOutput.exists_hasOrthonormalCols`: the eigenvalues and an exact unitary.
* `NLAlib.Schur.size_stmtCost_schurPipelineWith_le`: the static count is the sum of the stages'.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops MeasureTheory
open scoped Matrix

variable {O Q : Type}

section Program

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The dense Schur pipeline** with a norm estimate `Nm` (`[N] (A) → (S)`), a regularizer `Reg`
(`[N, nr] (A, P) → (A)`), a Hessenberg reducer `Red` (`[N] (A, U) → (A, U)`) and a Schur core
`Core` (`[N, nq, k, F, T] (A, P, U) → (A, U, Fl)`). The interface is
`[N, nr, nq, k, F, T] (A, P) → (A, U, Fl)`: `P[0]` holds the regularizer's `nr` words, `P[nr]`
the core's `nq` words. A zero norm estimate (only $\mathbf{A} = 0$, under the standard model)
stores the identity and the flag $0$ without a division. -/
def schurPipelineWith (Nm Reg Red Core : Impl O Q) : Impl O Q :=
  opsImpl% [N, nr, nq, k, F, T] (A, P) → (A, U, Fl) {
    let S ← alloc 1;
    let R ← alloc 1;
    run Nm.body [N] (A, S);
    if (Has.inj CmpTst.isPos) [] (S) {
      call (Has.inj (ScalarOp.lit 1)) [] () → (R);
      call (Has.inj ScalarOp.div) [] (R, S) → (R);
      for t < 2 * (N * N) { call (Has.inj ScalarOp.mul) [] (A[t], R) → (A[t]) };
      run Reg.body [N, nr] (A, P, A);
      run (PairMatrix.identity (Op := O) (Tst := Q)).body [N] (U);
      run Red.body [N] (A, U, A, U);
      run Core.body [N, nq, k, F, T] (A, P[nr], U, A, U, Fl);
      for t < 2 * (N * N) { call (Has.inj ScalarOp.mul) [] (A[t], S) → (A[t]) }
    } else {
      run (PairMatrix.identity (Op := O) (Tst := Q)).body [N] (U);
      call (Has.inj IndexOp.lit) [0] () → (Fl)
    }
  }

end Program

/-- The input memory of the pipeline: live, room for and pairwise apart blocks `A`, `P`, `U`,
`Fl`; the matrix and the parameter words stored. -/
def SchurPipelineInput {n : ℕ} (ps : List ℝ) (a p uo f : ℕ × ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  μ.Live [a, p, uo, f] ∧
    μ.Room [a, p, uo, f] [2 * ((n + 1) * (n + 1)), ps.length, 2 * ((n + 1) * (n + 1)), 1] ∧
    Fp.Apart [a, p, uo, f] [2 * ((n + 1) * (n + 1)), ps.length, 2 * ((n + 1) * (n + 1)), 1] ∧
    HoldsMatrix a A μ.store ∧ μ.store.readBlock p.1 p.2 ps.length = some ps

/-- **A Schur output** of $\mathbf{A}$: the flag $0$ and stored $\widehat{\mathbf{T}}$ (upper
triangular), $\widehat{\mathbf{U}}$ with $\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}
\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le e_A\|\mathbf{A}\|_2$ (relative) and
$\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le e_U$ (absolute). -/
def SchurOutput {n : ℕ} (a uo f : ℕ × ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eA eU : ℝ) (μ' : Mem ℝ) : Prop :=
  μ'.store.get f.1 f.2 = some 0 ∧ ∃ U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    HoldsMatrix a T μ'.store ∧ HoldsMatrix uo U μ'.store ∧ T.IsUpperTriangular ∧
    specNorm (A - U * T * Uᴴ) ≤ eA * specNorm A ∧ specNorm (Uᴴ * U - 1) ≤ eU

/-- Larger errors are weaker. -/
theorem SchurOutput.mono {n : ℕ} {a uo f : ℕ × ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {eA eU eA' eU' : ℝ} {μ' : Mem ℝ} (h : SchurOutput a uo f A eA eU μ') (hA : eA ≤ eA')
    (hU : eU ≤ eU') : SchurOutput a uo f A eA' eU' μ' := by
  obtain ⟨hf, U, T, hT, hUs, hTu, hr, ho⟩ := h
  exact ⟨hf, U, T, hT, hUs, hTu, hr.trans (mul_le_mul_of_nonneg_right hA (specNorm_nonneg A)),
    ho.trans hU⟩

/-- The matrix stored by a Schur output is upper triangular. -/
theorem SchurOutput.isUpperTriangular_of_holdsMatrix {n : ℕ} {a uo f : ℕ × ℕ}
    {A T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {eA eU : ℝ} {μ' : Mem ℝ}
    (h : SchurOutput a uo f A eA eU μ') (hT : HoldsMatrix a T μ'.store) : T.IsUpperTriangular := by
  obtain ⟨-, U, T', hT', -, hTu, -⟩ := h
  rwa [hT.eq_storedMatrix, ← hT'.eq_storedMatrix]

/-- The all-tape output: the stored accumulator is within $e_U$ of orthonormal. -/
def SchurOrth {n : ℕ} (uo : ℕ × ℕ) (eU : ℝ) (μ' : Mem ℝ) : Prop :=
  ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix uo U μ'.store ∧
    specNorm (Uᴴ * U - 1) ≤ eU

/-- The blocks the pipeline writes. -/
def schurFp (n : ℕ) (a uo f : ℕ × ℕ) : Fp :=
  Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1

/-! ### Stored identities, scaled words and measurable outputs -/

/-- **The memories holding a Schur output form a measurable set.** -/
theorem measurableSet_schurOutput {n : ℕ} (a uo f : ℕ × ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (eA eU : ℝ) :
    MeasurableSet {μ' : Mem ℝ | SchurOutput a uo f A eA eU μ'} := by
  set T := fun μ' : Mem ℝ => storedMatrix a (n + 1) (n + 1) μ'.store
  set U := fun μ' : Mem ℝ => storedMatrix uo (n + 1) (n + 1) μ'.store
  have e : {μ' : Mem ℝ | SchurOutput a uo f A eA eU μ'} =
      {μ' | μ'.store.get f.1 f.2 = some 0} ∩
        ({μ' | ∀ j < 2 * ((n + 1) * (n + 1)), (μ'.store.get a.1 (a.2 + j)).isSome} ∩
        ({μ' | ∀ j < 2 * ((n + 1) * (n + 1)), (μ'.store.get uo.1 (uo.2 + j)).isSome} ∩
        ({μ' | ∀ i j : Fin (n + 1), j < i → T μ' i j = 0} ∩
        ({μ' | specNorm (A - U μ' * T μ' * (U μ')ᴴ) ≤ eA * specNorm A} ∩
          {μ' | specNorm ((U μ')ᴴ * U μ' - 1) ≤ eU})))) := by
    ext μ'
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, SchurOutput]
    constructor
    · rintro ⟨hf, U', T', hT, hU, hTu, hr, ho⟩
      obtain rfl := hT.eq_storedMatrix
      obtain rfl := hU.eq_storedMatrix
      refine ⟨hf, fun j hj => ?_, fun j hj => ?_, fun i j hij => hTu hij, hr, ho⟩
      · rw [Store.get_of_readBlock hT hj 0]; rfl
      · rw [Store.get_of_readBlock hU hj 0]; rfl
    · rintro ⟨hf, ha, hu, hTu, hr, ho⟩
      exact ⟨hf, U μ', T μ', holdsMatrix_storedMatrix ha, holdsMatrix_storedMatrix hu,
        fun i j hij => hTu i j hij, hr, ho⟩
  rw [e]
  have hT : Measurable T := ShiftedQR.measurable_storedMatrix a (n + 1) (n + 1)
  have hU : Measurable U := ShiftedQR.measurable_storedMatrix uo (n + 1) (n + 1)
  have hc₁ : Continuous fun p : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ ×
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => specNorm (A - p.1 * p.2 * p.1ᴴ) :=
    continuous_specNorm.comp (continuous_const.sub ((continuous_fst.matrix_mul
      continuous_snd).matrix_mul continuous_fst.matrix_conjTranspose))
  have hc₂ : Continuous fun V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => specNorm (Vᴴ * V - 1) :=
    continuous_specNorm.comp ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).sub
      continuous_const)
  refine (Mem.measurableSet_get_eq f 0).inter ((ShiftedQR.measurableSet_forall_isSome a _).inter
    ((ShiftedQR.measurableSet_forall_isSome uo _).inter ((?_ : MeasurableSet _).inter ?_)))
  · simp only [Set.ofPred_forall]
    refine .iInter fun i => .iInter fun j => ?_
    by_cases hij : j < i
    · simpa [hij] using measurableSet_eq_fun ((Matrix.measurable_apply i j).comp hT)
        measurable_const
    · simp [hij]
  · exact (measurableSet_le (hc₁.measurable.comp (hU.prodMk hT)) measurable_const).inter
      (measurableSet_le (hc₂.measurable.comp hU) measurable_const)

/-- **The outcomes of a run ending in a Schur output form a measurable set**: the frame `F`
and a Schur output after. -/
theorem measurableSet_eqOff_schurOutput {n : ℕ} (F : Fp) (a uo f : ℕ × ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (eA eU : ℝ) :
    MeasurableSet {y : Mem ℝ × Mem ℝ | y.1.store.EqOff F y.2.store ∧
      SchurOutput a uo f A eA eU y.2} :=
  (Mem.measurableSet_eqOff F).inter (measurable_snd (measurableSet_schurOutput a uo f A eA eU))

/-! ### The memory of a pipeline run -/

/-- The four apart blocks of a pipeline input, pairwise. -/
theorem apart_four {a p uo f : ℕ × ℕ} {la lp lu lf : ℕ}
    (h : Fp.Apart [a, p, uo, f] [la, lp, lu, lf]) :
    Fp.Disj (Store.inBlock a.1 a.2 la) (Store.inBlock p.1 p.2 lp) ∧
      Fp.Disj (Store.inBlock a.1 a.2 la) (Store.inBlock uo.1 uo.2 lu) ∧
      Fp.Disj (Store.inBlock a.1 a.2 la) (Store.inBlock f.1 f.2 lf) ∧
      Fp.Disj (Store.inBlock p.1 p.2 lp) (Store.inBlock uo.1 uo.2 lu) ∧
      Fp.Disj (Store.inBlock p.1 p.2 lp) (Store.inBlock f.1 f.2 lf) ∧
      Fp.Disj (Store.inBlock uo.1 uo.2 lu) (Store.inBlock f.1 f.2 lf) := by
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true] at h
  exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1.1, h.2.1.2, h.2.2⟩

/-- **The memory of a pipeline run** after its two scratch cells $S = (L, 0)$ and
$R = (L + 1, 0)$: the input blocks below $L$, with room, apart, and the words `qs` stored. -/
def SchurPipelineMem (n : ℕ) (qs : List ℝ) (a p uo f : ℕ × ℕ) (L : ℕ) (m : Mem ℝ) : Prop :=
  m.store.length = L + 2 ∧ a.1 < L ∧ p.1 < L ∧ uo.1 < L ∧ f.1 < L ∧
    m.Room [a, p, uo, f] [2 * ((n + 1) * (n + 1)), qs.length, 2 * ((n + 1) * (n + 1)), 1] ∧
    m.store.len L = 1 ∧ m.store.len (L + 1) = 1 ∧
    Fp.Apart [a, p, uo, f] [2 * ((n + 1) * (n + 1)), qs.length, 2 * ((n + 1) * (n + 1)), 1] ∧
    m.store.readBlock p.1 p.2 qs.length = some qs

namespace SchurPipelineMem

variable {n : ℕ} {qs : List ℝ} {a p uo f : ℕ × ℕ} {L : ℕ} {m m' : Mem ℝ}

/-- The memory survives a run that writes away from the words. -/
theorem of_eqOff (h : SchurPipelineMem n qs a p uo f L m) {F : Fp}
    (hfr : m.store.EqOff F m'.store) (hF : Fp.Disj F (Store.inBlock p.1 p.2 qs.length)) :
    SchurPipelineMem n qs a p uo f L m' := by
  obtain ⟨hlen, ha, hp, hu, hf, hr, hL, hL', hap, hq⟩ := h
  refine ⟨hfr.length_eq ▸ hlen, ha, hp, hu, hf, ?_, by rw [hfr.len_eq, hL],
    by rw [hfr.len_eq, hL'], hap, hfr.keep (Store.readsOnly_readBlock _ _ _ _) hF hq⟩
  simpa only [Mem.Room, hfr.len_eq] using hr

/-- Every block of the run is live. -/
theorem live (h : SchurPipelineMem n qs a p uo f L m) :
    m.Live [a, p, uo, f, (L, 0), (L + 1, 0), a, uo] := by
  obtain ⟨hlen, ha, hp, hu, hf, -⟩ := h
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [hlen] <;> omega

/-- A sublist of the live blocks is live. -/
theorem live_of_subset (h : SchurPipelineMem n qs a p uo f L m) {zs : List (ℕ × ℕ)}
    (hz : zs ⊆ [a, p, uo, f, (L, 0), (L + 1, 0), a, uo]) : m.Live zs :=
  fun x hx => h.live x (hz hx)

/-- The footprint of the run misses the words. -/
theorem disj_words (h : SchurPipelineMem n qs a p uo f L m) :
    Fp.Disj (schurFp n a uo f ⊔ Store.inBlock L 0 1 ⊔ Store.inBlock (L + 1) 0 1)
      (Store.inBlock p.1 p.2 qs.length) := by
  obtain ⟨-, -, hp, -, -, -, -, -, hap, -⟩ := h
  obtain ⟨h1, -, -, h4, h5, -⟩ := apart_four hap
  simp only [schurFp, Fp.disj_sup_left]
  exact ⟨⟨⟨⟨h1, h4.symm⟩, h5.symm⟩, Fp.disj_inBlock_of_ne (by omega)⟩,
    Fp.disj_inBlock_of_ne (by omega)⟩

/-- The room of the matrix block. -/
theorem room_a (h : SchurPipelineMem n qs a p uo f L m) :
    a.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len a.1 := h.2.2.2.2.2.1.1

/-- The room of the accumulator block. -/
theorem room_uo (h : SchurPipelineMem n qs a p uo f L m) :
    uo.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len uo.1 := h.2.2.2.2.2.1.2.2.1

/-- The room of the flag. -/
theorem room_f (h : SchurPipelineMem n qs a p uo f L m) : f.2 + 1 ≤ m.store.len f.1 :=
  h.2.2.2.2.2.1.2.2.2.1

end SchurPipelineMem

/-- The cells of the buffers from `L` on are not written by the pipeline's footprint. -/
theorem not_schurFp_of_le {n : ℕ} {a uo f : ℕ × ℕ} {L b i : ℕ} (ha : a.1 < L) (hu : uo.1 < L)
    (hf : f.1 < L) (hb : L ≤ b) : ¬ schurFp n a uo f b i := by
  rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩) <;> omega

/-- The environment of the pipeline body after its two scratch allocations. -/
def schurPipelineEnv (n nr nq k F T : ℕ) (a p uo f : ℕ × ℕ) (L : ℕ) : Env :=
  ⟨[n + 1, nr, nq, k, F, T, a.2, p.2, a.2, uo.2, f.2], [a.1, p.1, a.1, uo.1, f.1, L, L + 1]⟩

section Steps


variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- The identity program stores the identity when the literals $0$ and $1$ are exact. -/
theorem writes_identity_holdsMatrix_one {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (h1 : Mch.lit 1 = 1) {τ : Tape ℝ}
    {m : Mem ℝ} {N : ℕ} {b : ℕ × ℕ} (hroom : b.2 + 2 * (N * N) ≤ m.store.len b.1) :
    Writes .total I τ (PairMatrix.identity (Op := O) (Tst := Q)).body (Env.frame [N] [b])
      (Store.inBlock b.1 b.2 (2 * (N * N)))
      (fun m' => HoldsMatrix b (1 : Matrix (Fin N) (Fin N) ℂ) m'.store) m := by
  have h0 : Mch.lit 0 = 0 := hM.dec_lit_zero
  refine (PairMatrix.writes_identity hS hroom).mono le_rfl fun m' _ hv => ?_
  refine holdsMatrix_one_of_holdsVec fun i hi => ?_
  rw [hv.1 i hi, h0, h1]

/-- **The zero branch of the pipeline**: from the memory of a run holding $\mathbf{A} = 0$, the
identity and the flag $0$ make a Schur output. -/
theorem schurPipeline_zero_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I) (h1 : Mch.lit 1 = 1)
    {n nr nq k F T L : ℕ} {qs : List ℝ} {a p uo f : ℕ × ℕ} {τ : Tape ℝ} {m : Mem ℝ}
    (hm : SchurPipelineMem n qs a p uo f L m)
    (hA : HoldsMatrix a (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) m.store) {eA eU : ℝ}
    (heU : 0 ≤ eU) :
    Writes .total I τ (.seq (.frame [.var 0] [⟨3, .var 9⟩]
        (PairMatrix.identity (Op := O) (Tst := Q)).body)
        (.call (Has.inj IndexOp.lit) [.const 0] [] [⟨4, .var 10⟩]))
      (schurPipelineEnv n nr nq k F T a p uo f L) (schurFp n a uo f)
      (SchurOutput a uo f (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) eA eU) m := by
  obtain ⟨-, -, -, -, -, -, -, -, hap, -⟩ := id hm
  obtain ⟨-, h2, -, -, -, h6⟩ := apart_four hap
  refine (writes_identity_holdsMatrix_one (N := n + 1) hS hM h1 hm.room_uo).frame_seq_le rfl rfl
    (hm.live_of_subset (by simp)) (by simp only [schurFp]; fp_sub) fun m' hfr hU => ?_
  have hf : f.2 < m'.store.len f.1 := by have := hm.room_f; rw [hfr.len_eq]; omega
  refine (writes_indexLit hL (n := 0) rfl rfl hf).mono (by simp only [schurFp]; fp_sub)
    fun m'' hfr' hg => ?_
  have hz : Mch.lit ((0 : ℕ) : ℚ) = 0 := by simpa using hM.dec_lit_zero
  refine ⟨by rw [hg.2, hz], 1, 0, ?_, hU.of_eqOff hfr' h6.symm, ?_, ?_, ?_⟩
  · obtain ⟨-, -, h3, -, -, -⟩ := apart_four hap
    exact (hA.of_eqOff hfr h2.symm).of_eqOff hfr' h3.symm
  · intro i j _; rfl
  · simp
  · simpa using heU

/-- **The scaling of the pipeline**: from a run memory holding $\mathbf{A}$ and the norm estimate
$x > 0$ in $S$, the literal $1$, the division $r = \mathrm{fl}(1/x)$ and the scaling of the words
by $r$ store an $\mathbf{A}_1$ with $\|x\mathbf{A}_1 - \mathbf{A}\|_2 \le
3\boldsymbol{u}\|\mathbf{A}\|_{\mathsf F}$. -/
theorem schurPipeline_scale_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (h1 : Mch.lit 1 = 1) (hu1 : u ≤ 1)
    {n nr nq k F T L : ℕ} {qs : List ℝ} {a p uo f : ℕ × ℕ} {τ : Tape ℝ} {m : Mem ℝ}
    (hm : SchurPipelineMem n qs a p uo f L m) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : HoldsMatrix a A m.store) {x : ℝ} (hx : m.store.get L 0 = some x) (hx0 : 0 < x) :
    Writes .total I τ
      ((Stmt.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨6, .const 0⟩]).seq
        ((Stmt.call (Has.inj ScalarOp.div) [] [⟨6, .const 0⟩, ⟨5, .const 0⟩] [⟨6, .const 0⟩]).seq
          (.loop (.const 2 * (.var 0 * .var 0)) (.call (Has.inj ScalarOp.mul) []
            [⟨0, .var 6 + .var 11⟩, ⟨6, .const 0⟩] [⟨0, .var 6 + .var 11⟩]))))
      (schurPipelineEnv n nr nq k F T a p uo f L)
      (Store.inBlock (L + 1) 0 1 ⊔ Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (fun m' => SchurPipelineMem n qs a p uo f L m' ∧ m'.store.get L 0 = some x ∧
        ∃ A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A₁ m'.store ∧
          specNorm ((x : ℂ) • A₁ - A) ≤ 3 * u * frobNorm A) m := by
  obtain ⟨hlen, ha, -, -, -, -, hL, hL', -⟩ := id hm
  have hu : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hRroom : (0 : ℕ) < m.store.len (L + 1) := by omega
  refine (writes_call_const (hS (.lit 1)) (z := (L + 1, 0)) rfl trivial hRroom).seq_le
    le_sup_left fun m₁ hfr₁ hR₁ => ?_
  have hx₁ : m₁.store.get L 0 = some x := by
    rw [hfr₁.2 L 0 (by simp [Store.inBlock]), hx]
  have hlive₁ : m₁.Live [(L + 1, 0), (L, 0), (L + 1, 0)] := by
    have := hm.live.congr hfr₁.length_eq
    exact fun z hz => this z (by simp at hz ⊢; tauto)
  refine (writes_call_bin (hS .div) (x := (L + 1, 0)) (y := (L, 0)) (z := (L + 1, 0)) rfl rfl
    trivial hR₁.2 hx₁ rfl fun _ => ⟨hlive₁, by rw [hfr₁.len_eq]; omega⟩).seq_le le_sup_left
    fun m₂ hfr₂ hR₂ => ?_
  have hfr₁₂ := hfr₁.trans hfr₂
  have hA₂ : HoldsMatrix a A m₂.store := hA.of_eqOff hfr₁₂ (Fp.disj_inBlock_of_ne (by omega))
  have hx₂ : m₂.store.get L 0 = some x := by
    rw [hfr₂.2 L 0 (by simp [Store.inBlock]), hx₁]
  set r := Mch.div (Mch.lit 1) x
  refine (writes_loop_mul_cell hS (N := 2 * ((n + 1) * (n + 1))) (b := a.1) (o := a.2)
    (y := (L + 1, 0)) (r := r) rfl (fun t _ => rfl) (fun t _ => rfl) ?_
    (fun t ht => ⟨_, Store.get_of_readBlock hA₂ ht 0⟩) hR₂.2 ?_).mono le_sup_right ?_
  · have := hm.live.congr hfr₁₂.length_eq
    exact fun z hz => this z (by simp at hz ⊢; tauto)
  · rintro ⟨h, -⟩; omega
  rintro m₃ hfr₃ ⟨-, hmul⟩
  have hfr : m.store.EqOff (Store.inBlock (L + 1) 0 1 ⊔
      Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) m₃.store :=
    (hfr₁₂.mono fun _ _ h => Or.inl h).trans (hfr₃.mono fun _ _ h => Or.inr h)
  obtain ⟨A₁, hA₁, hA₁n, -⟩ := hM.exists_holdsMatrix_mul hA₂ hmul
  refine ⟨hm.of_eqOff hfr (hm.disj_words.mono (by simp only [schurFp]; fp_sub) le_rfl),
    by rw [hfr₃.2 L 0 (by simp [Store.inBlock]; omega), hx₂], A₁, hA₁, ?_⟩
  -- the numbers
  have hr : |r - 1 / x| ≤ u * |1 / x| := by
    have := hM.div (Mch.lit 1) x hx0.ne'
    simpa [r, h1] using this
  have hxr : |x * r - 1| ≤ u := by
    have e : x * r - 1 = x * (r - 1 / x) := by field_simp
    rw [e, abs_mul, abs_of_pos hx0]
    calc x * |r - 1 / x| ≤ x * (u * |1 / x|) := mul_le_mul_of_nonneg_left hr hx0.le
      _ = u := by rw [abs_of_pos (by positivity)]; field_simp
  have hxr' : x * |r| ≤ 1 + u := by
    have : |x * r| ≤ 1 + u := by
      have := abs_sub_abs_le_abs_sub (x * r) 1; rw [abs_one] at this; linarith
    rwa [abs_mul, abs_of_pos hx0] at this
  have e : (x : ℂ) • A₁ - A = (x : ℂ) • (A₁ - (r : ℂ) • A) + (((x * r - 1 : ℝ)) : ℂ) • A := by
    rw [smul_sub, smul_smul]
    push_cast
    rw [sub_smul, one_smul]; abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [specNorm_smul, specNorm_smul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hx0.le,
    Real.norm_eq_abs]
  have hF := frobNorm_nonneg A
  have h₁ : x * specNorm (A₁ - (r : ℂ) • A) ≤ x * (u * |r| * frobNorm A) :=
    mul_le_mul_of_nonneg_left ((specNorm_le_frobNorm _).trans hA₁n) hx0.le
  have h₂ : |x * r - 1| * specNorm A ≤ u * frobNorm A :=
    mul_le_mul hxr (specNorm_le_frobNorm A) (specNorm_nonneg _) hu
  have h₃ : x * (u * |r| * frobNorm A) ≤ (1 + u) * u * frobNorm A := by
    have := mul_le_mul_of_nonneg_right hxr' (mul_nonneg hu hF)
    linarith [show x * (u * |r| * frobNorm A) = x * |r| * (u * frobNorm A) by ring]
  have h₄ : (1 + u) * u * frobNorm A ≤ 2 * u * frobNorm A := by
    have := mul_le_mul_of_nonneg_right hu1 (mul_nonneg hu hF); nlinarith
  linarith

/-- The blocks of the core: the parameter words of the core are the tail of the words. -/
theorem apart_tail {a p uo f : ℕ × ℕ} {la lu lf : ℕ} {qR qC : List ℝ}
    (h : Fp.Apart [a, p, uo, f] [la, (qR ++ qC).length, lu, lf]) :
    Fp.Apart [a, (p.1, p.2 + qR.length), uo, f] [la, qC.length, lu, lf] := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := apart_four h
  have hs : Store.inBlock p.1 (p.2 + qR.length) qC.length ≤
      Store.inBlock p.1 p.2 (qR ++ qC).length :=
    Fp.inBlock_le_inBlock (by omega) (by simp; omega)
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true]
  exact ⟨⟨h1.mono le_rfl hs, h2, h3⟩, ⟨h4.mono hs le_rfl, h5.mono hs le_rfl⟩, h6⟩

variable [Has IdxTst Q] in
/-- **The core and the scaling back**: from a run memory holding the pair $(\mathbf{U}_1,
\mathbf{H})$ ($\mathbf{H}$ upper Hessenberg of the core's class, $\|\mathbf{H}\|_2 \le 4/c_1$) and
the norm estimate $x$, the core and the scaling of the words by $x$ end, except with probability
$\varphi_C$, in a memory with the flag $0$, the accumulator $\mathbf{U}_2$ and the scaled
$\mathbf{T}'$ of an upper triangular $\mathbf{T}$ tracked from $(\mathbf{U}_1, \mathbf{H})$. The
conclusion is passed as `hpost`. -/
theorem schurPipeline_core_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {Core : Impl O Q} {n k F T L : ℕ} {c₁ εCU εCT φC : ℝ} {qR qC : List ℝ}
    {C' : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop}
    (hCore : RandomSchurCoreContract law εCU εCT φC C' k F T (n + 1) (4 / c₁) qC Core I)
    {a p uo f : ℕ × ℕ} {m : Mem ℝ} (hm : SchurPipelineMem n (qR ++ qC) a p uo f L m)
    {x : ℝ} (hx : m.store.get L 0 = some x) {U₁ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpair : HoldsSchurPair a uo U₁ H m.store) (hH : IsUpperHessenberg H)
    (hHn : specNorm H ≤ 4 / c₁) (hC' : C' H) {Goal : Mem ℝ → Prop}
    (hpost : ∀ U₂ Tm T' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Tm.IsUpperTriangular →
      IsTrackedUnitarySimilar εCU εCT U₁ H U₂ Tm →
      frobNorm (T' - (x : ℂ) • Tm) ≤ u * |x| * frobNorm Tm →
      (∀ i j, Tm i j = 0 → T' i j = 0) → ∀ m' : Mem ℝ, m'.store.get f.1 f.2 = some 0 →
      HoldsMatrix a T' m'.store → HoldsMatrix uo U₂ m'.store → Goal m') :
    PWrites law I ((Stmt.frame [.var 0, .var 2, .var 3, .var 4, .var 5]
        [⟨0, .var 6⟩, ⟨1, .var 7 + .var 1⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩, ⟨4, .var 10⟩]
        Core.body).seq (.loop (.const 2 * (.var 0 * .var 0)) (.call (Has.inj ScalarOp.mul) []
          [⟨0, .var 6 + .var 11⟩, ⟨5, .const 0⟩] [⟨0, .var 6 + .var 11⟩])))
      (schurPipelineEnv n qR.length qC.length k F T a p uo f L) (schurFp n a uo f) (· = m)
      Goal φC := by
  obtain ⟨hlen, ha, hp, hu, hf, hroom, hL, -, hap, hq⟩ := id hm
  obtain ⟨-, h2, h3, -, -, h6⟩ := apart_four hap
  have hcore := ((hCore H U₁ le_rfl hH hHn hC' (a := a) (p := (p.1, p.2 + qR.length))
    (uo := uo) (f := f)).in_frame (ρ := schurPipelineEnv n qR.length qC.length k F T a p uo f L)
    (ds := [.var 0, .var 2, .var 3, .var 4, .var 5])
    (args := [⟨0, .var 6⟩, ⟨1, .var 7 + .var 1⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩,
      ⟨4, .var 10⟩]) rfl rfl
    fun m' hm' z hz => hm'.2.2.1 z (by
      simp only [List.mem_cons, List.mem_nil_iff] at hz ⊢; tauto)).mono_eqOff
    (Pre' := (· = m)) (Post' := fun m' => SchurPipelineMem n (qR ++ qC) a p uo f L m' ∧
      m'.store.get L 0 = some x ∧ m'.store.get f.1 f.2 = some 0 ∧
      ∃ U₂ Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsSchurPair a uo U₂ Tm m'.store ∧
        Tm.IsUpperTriangular ∧ IsTrackedUnitarySimilar εCU εCT U₁ H U₂ Tm)
    (fun m' hm' => ?_) (fun m₀ m' hm₀ hfr ⟨hf0, U₂, Tm, hp₂, hTu, htr⟩ => ?_)
  rotate_left
  · subst hm'
    refine ⟨hpair, Store.readBlock_append_right hq, fun z hz => ?_, ?_, apart_tail hap⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> simp only [hlen] <;> omega
    · have := hm.room_f; omega
  · subst hm₀
    refine ⟨hm.of_eqOff hfr (hm.disj_words.mono (fun _ _ h => Or.inl (Or.inl h)) le_rfl),
      ?_, hf0, U₂, Tm, hp₂, hTu, htr⟩
    rw [hfr.2 L 0 (not_schurFp_of_le ha hu hf le_rfl), hx]
  refine (PWrites.seq hI hloc le_rfl hcore (PWrites.of_writes le_rfl fun m' τ hm' => ?_)).mono
    (fun _ h => h) (sup_le le_rfl (fun _ _ h => Or.inl (Or.inl h))) (fun _ h => h) (by simp)
  obtain ⟨hm', hx', hf0, U₂, Tm, ⟨hT₂, hU₂⟩, hTu, htr⟩ := hm'
  refine (writes_loop_mul_cell hS (N := 2 * ((n + 1) * (n + 1))) (b := a.1) (o := a.2)
    (y := (L, 0)) (r := x) rfl (fun t _ => rfl) (fun t _ => rfl)
    (hm'.live_of_subset (by simp)) (fun t ht => ⟨_, Store.get_of_readBlock hT₂ ht 0⟩) hx'
    (by rintro ⟨h, -⟩; omega)).mono le_rfl ?_
  rintro m'' hfr ⟨-, hmul⟩
  obtain ⟨T', hT', hTn, hz⟩ := hM.exists_holdsMatrix_mul hT₂ hmul
  exact hpost U₂ Tm T' hTu htr hTn hz m''
    (by rw [hfr.2 f.1 f.2 (fun h => h3 _ _ h ⟨rfl, le_rfl, by omega⟩), hf0]) hT'
    (hU₂.of_eqOff hfr h2)

variable [Has IdxTst Q] in
/-- **The regularizer, the identity, the reducer, the core and the scaling back**: from a run
memory holding a scaled $\mathbf{A}_1$ with $\|\mathbf{A}_1\|_2 \le 2/c_1$ and the norm estimate
$x$, except with probability $\varphi_R + \varphi_C$ the run ends with the flag $0$, the
accumulator $\mathbf{U}_2$ and the scaled $\mathbf{T}'$ of an upper triangular $\mathbf{T}$
tracked from $(\mathbf{I}, \mathbf{A}_2)$, $\|\mathbf{A}_2 - \mathbf{A}_1\|_2 \le \delta_R$. The
conclusion is passed as `hpost`, its outcomes measurable. -/
theorem schurPipeline_reg_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (h1 : Mch.lit 1 = 1) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {Reg Red Core : Impl O Q} {n k F T L : ℕ} {c₁ δR φR εHU εHT εCU εCT φC : ℝ}
    {qR qC : List ℝ} {C C' : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop}
    (hReg : RandomRegularizerContract law δR φR C (n + 1) (2 / c₁) qR Reg I)
    (hRed : HessenbergReducerContract εHU εHT (n + 1) Red I)
    (hCore : RandomSchurCoreContract law εCU εCT φC C' k F T (n + 1) (4 / c₁) qC Core I)
    (hCC' : ∀ (A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), C A →
      IsPerturbedUnitarySimilarBy V A H (εHT * (2 / c₁ + δR)) → C' H)
    (hc₁ : 0 < c₁) (hδR : δR ≤ 1 / c₁) (hεHT0 : 0 ≤ εHT) (hεHT : εHT ≤ 1 / 8)
    (hεHU : 0 ≤ εHU) (hεCU : 0 ≤ εCU) (hφC : 0 ≤ φC)
    {a p uo f : ℕ × ℕ} {m : Mem ℝ} (hm : SchurPipelineMem n (qR ++ qC) a p uo f L m)
    {x : ℝ} (hx : m.store.get L 0 = some x) {A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA₁ : HoldsMatrix a A₁ m.store) (hA₁n : specNorm A₁ ≤ 2 / c₁) {Goal : Mem ℝ → Prop}
    (hGoal : MeasurableSet {y : Mem ℝ × Mem ℝ |
      y.1.store.EqOff (schurFp n a uo f) y.2.store ∧ Goal y.2})
    (hpost : ∀ A₂ U₂ Tm T' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, 0 ≤ εCT →
      specNorm (A₂ - A₁) ≤ δR →
      Tm.IsUpperTriangular → IsTrackedUnitarySimilar ((1 + εHU) * (1 + εCU) - 1)
        (εHT * specNorm A₂ + εCT) 1 A₂ U₂ Tm →
      frobNorm (T' - (x : ℂ) • Tm) ≤ u * |x| * frobNorm Tm →
      (∀ i j, Tm i j = 0 → T' i j = 0) → ∀ m' : Mem ℝ, m'.store.get f.1 f.2 = some 0 →
      HoldsMatrix a T' m'.store → HoldsMatrix uo U₂ m'.store → Goal m') :
    PWrites law I ((Stmt.frame [.var 0, .var 1] [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩]
        Reg.body).seq ((Stmt.frame [.var 0] [⟨3, .var 9⟩]
          (PairMatrix.identity (Op := O) (Tst := Q)).body).seq
        ((Stmt.frame [.var 0] [⟨0, .var 6⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩] Red.body).seq
          ((Stmt.frame [.var 0, .var 2, .var 3, .var 4, .var 5]
            [⟨0, .var 6⟩, ⟨1, .var 7 + .var 1⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩,
              ⟨4, .var 10⟩] Core.body).seq (.loop (.const 2 * (.var 0 * .var 0))
            (.call (Has.inj ScalarOp.mul) [] [⟨0, .var 6 + .var 11⟩, ⟨5, .const 0⟩]
              [⟨0, .var 6 + .var 11⟩]))))))
      (schurPipelineEnv n qR.length qC.length k F T a p uo f L) (schurFp n a uo f) (· = m)
      Goal (φR + φC) := by
  obtain ⟨hlen, ha, hp, hu, hf, -, -, -, hap, hq⟩ := id hm
  obtain ⟨h1', h2, -, -, -, -⟩ := apart_four hap
  have hFa : Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ≤ schurFp n a uo f :=
    fun _ _ h => Or.inl (Or.inl h)
  have hFu : Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ≤ schurFp n a uo f :=
    fun _ _ h => Or.inl (Or.inr h)
  -- the regularizer
  have hreg := ((hReg A₁ le_rfl hA₁n (a := a) (q := p)).in_frame
    (ρ := schurPipelineEnv n qR.length qC.length k F T a p uo f L) (ds := [.var 0, .var 1])
    (args := [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩]) rfl rfl
    fun m' hm' z hz => hm'.2.2.1 z (by
      simp only [List.mem_cons, List.mem_nil_iff] at hz ⊢; tauto)).mono_eqOff
    (Pre' := (· = m)) (Post' := fun m' => SchurPipelineMem n (qR ++ qC) a p uo f L m' ∧
      m'.store.get L 0 = some x ∧ ∃ A₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix a A₂ m'.store ∧ specNorm (A₂ - A₁) ≤ δR ∧ C A₂)
    (fun m' hm' => ?_) (fun m₀ m' hm₀ hfr ⟨E, hE, hEn, hCE⟩ => ?_)
  rotate_left
  · subst hm'
    refine ⟨hA₁, Store.readBlock_append_left hq, hm.live_of_subset (by simp), h1'.mono le_rfl
      (Fp.inBlock_le_inBlock le_rfl (by simp))⟩
  · subst hm₀
    refine ⟨hm.of_eqOff hfr (hm.disj_words.mono (fun _ _ h => Or.inl (Or.inl (hFa _ _ h)))
      le_rfl), by rw [hfr.2 L 0 (fun h => by obtain ⟨h, -⟩ := h; omega), hx], A₁ + E, hE,
      by simpa using hEn, hCE⟩
  set Mid₁ : Mem ℝ → Prop := fun m' => SchurPipelineMem n (qR ++ qC) a p uo f L m' ∧
    m'.store.get L 0 = some x ∧ ∃ A₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      HoldsMatrix a A₂ m'.store ∧ specNorm (A₂ - A₁) ≤ δR ∧ C A₂ ∧
        HoldsMatrix uo (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) m'.store with hMid₁
  set Mid₃ : Mem ℝ → Prop := fun m' => SchurPipelineMem n (qR ++ qC) a p uo f L m' ∧
    m'.store.get L 0 = some x ∧ ∃ A₂ U₁ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      specNorm (A₂ - A₁) ≤ δR ∧ C A₂ ∧ HoldsSchurPair a uo U₁ H m'.store ∧
        IsUpperHessenberg H ∧ IsTrackedUnitarySimilar εHU (εHT * specNorm A₂) 1 A₂ U₁ H
    with hMid₃
  have hid : ∀ m' τ, (fun m' => SchurPipelineMem n (qR ++ qC) a p uo f L m' ∧
      m'.store.get L 0 = some x ∧ ∃ A₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix a A₂ m'.store ∧ specNorm (A₂ - A₁) ≤ δR ∧ C A₂) m' →
      Writes .total I τ (Stmt.frame [.var 0] [⟨3, .var 9⟩]
        (PairMatrix.identity (Op := O) (Tst := Q)).body)
        (schurPipelineEnv n qR.length qC.length k F T a p uo f L)
        (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) Mid₁ m' := by
    rintro m' τ ⟨hm', hx', A₂, hA₂, hA₂n, hC⟩
    exact (writes_identity_holdsMatrix_one (N := n + 1) hS hM h1 hm'.room_uo).in_frame rfl rfl
      (hm'.live_of_subset (by simp)) |>.mono le_rfl fun m'' hfr hU => ⟨hm'.of_eqOff hfr
        (hm'.disj_words.mono (fun _ _ h => Or.inl (Or.inl (hFu _ _ h))) le_rfl),
        by rw [hfr.2 L 0 (fun h => by obtain ⟨h, -⟩ := h; omega), hx'], A₂,
        hA₂.of_eqOff hfr h2.symm, hA₂n, hC, hU⟩
  have hred : ∀ m' τ, Mid₁ m' →
      Writes .total I τ (Stmt.frame [.var 0] [⟨0, .var 6⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩]
        Red.body) (schurPipelineEnv n qR.length qC.length k F T a p uo f L)
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) Mid₃ m' := by
    rintro m' τ ⟨hm', hx', A₂, hA₂, hA₂n, hC, hU⟩
    refine ((hRed A₂ 1 le_rfl ⟨hA₂, hU⟩ (hm'.live_of_subset (by simp)) h2).in_frame rfl rfl
      (hm'.live_of_subset (by simp))).mono le_rfl fun m'' hfr ⟨U₁, H, hp₁, hH, htr⟩ => ?_
    exact ⟨hm'.of_eqOff hfr (hm'.disj_words.mono (sup_le (fun _ _ h => Or.inl (Or.inl (hFa _ _ h)))
      (fun _ _ h => Or.inl (Or.inl (hFu _ _ h)))) le_rfl),
      by rw [hfr.2 L 0 (fun h => by rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> omega), hx'],
      A₂, U₁, H, hA₂n, hC, hp₁, hH, htr⟩
  have hcore : ∀ m', Mid₃ m' → PWrites law I ((Stmt.frame [.var 0, .var 2, .var 3, .var 4, .var 5]
        [⟨0, .var 6⟩, ⟨1, .var 7 + .var 1⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩,
          ⟨4, .var 10⟩] Core.body).seq (.loop (.const 2 * (.var 0 * .var 0))
          (.call (Has.inj ScalarOp.mul) [] [⟨0, .var 6 + .var 11⟩, ⟨5, .const 0⟩]
            [⟨0, .var 6 + .var 11⟩])))
      (schurPipelineEnv n qR.length qC.length k F T a p uo f L) (schurFp n a uo f) (· = m')
      Goal φC := by
    rintro m' ⟨hm', hx', A₂, U₁, H, hA₂n, hC, hp₁, hH, htr⟩
    obtain ⟨V, hV, -⟩ := id htr
    obtain ⟨hA₂b, hHn⟩ := specNorm_le_of_reduced hc₁ hδR hεHT hA₁n hA₂n hV
    have hC'H : C' H := hCC' A₂ H V hC (hV.mono (mul_le_mul_of_nonneg_left hA₂b hεHT0))
    exact schurPipeline_core_pwrites hS hM hI hloc hCore hm' hx' hp₁ hH hHn hC'H
      fun U₂ Tm T' hTu htr' hTn hz m'' hf hT hU => hpost A₂ U₂ Tm T'
        (by obtain ⟨_, ⟨_, E, hE, _⟩, _⟩ := htr'; exact (specNorm_nonneg E).trans hE) hA₂n hTu
        (IsTrackedUnitarySimilar.trans hεHU hεCU htr htr') hTn hz m'' hf hT hU
  refine (PWrites.seq hI hloc (by linarith : (0 : ℝ) ≤ 0 + (0 + φC)) hreg
    (PWrites.seq hI hloc (by linarith : (0 : ℝ) ≤ 0 + φC)
    (PWrites.of_writes le_rfl fun m' τ hm' => hid m' τ hm')
    (PWrites.seq hI hloc hφC (PWrites.of_writes le_rfl fun m' τ hm' => hred m' τ hm')
      (PWrites.of_forall_eq hI hloc hcore hGoal)))).mono
    (fun _ h => h) (sup_le hFa (sup_le hFu (sup_le (sup_le hFa hFu) le_rfl))) (fun _ h => h)
    (by simp)

/-- **The numbers of a pipeline run end in a Schur output**: the scaled, regularized and
tracked matrices of a run with the budget's side conditions give the residual and the
orthogonality of `NLAlib.Schur.schurPipelineWith_measureReal_not_schur_le`. -/
theorem schurOutput_of_run {n : ℕ} {a uo f : ℕ × ℕ}
    {A A₁ A₂ U₂ Tm T' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {m' : Mem ℝ}
    {u x c₁ c₂ δR εHU εHT εCU εCT : ℝ} (hu0 : 0 ≤ u) (hu : 8 * ((n : ℝ) + 1) * u ≤ 1 / 4)
    (hc₁ : 0 < c₁) (hx0 : 0 < x) (hxl : c₁ * frobNorm A ≤ x) (hxu : x ≤ c₂ * frobNorm A)
    (hδR : δR ≤ 1 / c₁) (hεHT0 : 0 ≤ εHT) (hεHT : εHT ≤ 1 / 8) (hεHU : 0 ≤ εHU)
    (hεCU : 0 ≤ εCU) (hεU : (1 + εHU) * (1 + εCU) - 1 ≤ 1 / 16) (hεCT : 0 ≤ εCT)
    (hA₁ : specNorm ((x : ℂ) • A₁ - A) ≤ 3 * u * frobNorm A) (hA₂ : specNorm (A₂ - A₁) ≤ δR)
    (hTu : Tm.IsUpperTriangular)
    (htr : IsTrackedUnitarySimilar ((1 + εHU) * (1 + εCU) - 1) (εHT * specNorm A₂ + εCT) 1 A₂
      U₂ Tm)
    (hT' : frobNorm (T' - (x : ℂ) • Tm) ≤ u * |x| * frobNorm Tm)
    (hz : ∀ i j, Tm i j = 0 → T' i j = 0) (hf : m'.store.get f.1 f.2 = some 0)
    (hTs : HoldsMatrix a T' m'.store) (hUs : HoldsMatrix uo U₂ m'.store) :
    SchurOutput a uo f A
      (2 * c₂ * √((n : ℝ) + 1) * (δR + 3 * εHT / c₁ + εCT +
        8 * ((1 + εHU) * (1 + εCU) - 1) / c₁) + 8 * (n + 1) * u)
      (2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2) m' := by
  set ε := (1 + εHU) * (1 + εCU) - 1 with hεdef
  have hε0 : 0 ≤ ε := by nlinarith
  have hδR0 : 0 ≤ δR := (specNorm_nonneg _).trans hA₂
  have hres := specNorm_sub_mul_mul_conjTranspose_le_of_scaled hx0 hu0 hA₁ hA₂ htr hε0
    (by linarith) (by rwa [abs_of_pos hx0] at hT')
  have hn1 : (1 : ℝ) ≤ √((n : ℝ) + 1) := by
    rw [Real.one_le_sqrt]; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hsq : √((n : ℝ) + 1) * √((n : ℝ) + 1) = (n : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hFa : frobNorm A ≤ √((n : ℝ) + 1) * specNorm A := by
    have := frobNorm_le_sqrt_card_mul_specNorm A
    simpa [Fintype.card_fin] using this
  have hAF := specNorm_le_frobNorm A
  have ht₁ : x * specNorm A₁ ≤ specNorm A + 3 * u * frobNorm A := by
    have h := specNorm_add_le A ((x : ℂ) • A₁ - A)
    rw [add_sub_cancel, specNorm_smul, Complex.norm_real, Real.norm_of_nonneg hx0.le] at h
    linarith
  have hb := schurPipeline_budget (t₁ := specNorm A₁) (t₂ := specNorm A₂) (specNorm_nonneg A)
    (frobNorm_nonneg A) hFa hn1
    (by rw [hsq]; linarith) hu0 hc₁ hx0 hxl hxu ht₁ (by linarith)
    (by have := specNorm_add_le A₁ (A₂ - A₁); rw [add_sub_cancel] at this; linarith)
    (specNorm_nonneg _) hδR0 hδR hεHT0 hεHT hεCT hε0 hεU
  rw [hsq] at hb
  have hN : √(((n + 1 : ℕ) : ℝ)) = √((n : ℝ) + 1) := by push_cast; rfl
  rw [hN] at hres
  refine ⟨hf, U₂, T', hTs, hUs, fun i j hij => hz i j (hTu hij), hres.trans hb,
    (htr.specNorm_sub_mul_mul_conjTranspose_le hε0 (by linarith)).2⟩

variable [Has IdxTst Q] in
/-- **The positive branch of the pipeline**: from a run memory holding $\mathbf{A}$ and a norm
estimate $c_1\|\mathbf{A}\|_{\mathsf F} \le x \le c_2\|\mathbf{A}\|_{\mathsf F}$, $x > 0$, the run
of
the scaling, the four stages and the scaling back ends in a Schur output except with probability
$\varphi_R + \varphi_C$. -/
theorem schurPipeline_pos_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (h1 : Mch.lit 1 = 1) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {Reg Red Core : Impl O Q} {n k F T L : ℕ} {c₁ c₂ δR φR εHU εHT εCU εCT φC : ℝ}
    {qR qC : List ℝ} {C C' : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop}
    (hReg : RandomRegularizerContract law δR φR C (n + 1) (2 / c₁) qR Reg I)
    (hRed : HessenbergReducerContract εHU εHT (n + 1) Red I)
    (hCore : RandomSchurCoreContract law εCU εCT φC C' k F T (n + 1) (4 / c₁) qC Core I)
    (hCC' : ∀ (A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), C A →
      IsPerturbedUnitarySimilarBy V A H (εHT * (2 / c₁ + δR)) → C' H)
    (hc₁ : 0 < c₁) (hu0 : 0 ≤ u) (hu : 8 * ((n : ℝ) + 1) * u ≤ 1 / 4) (hδR : δR ≤ 1 / c₁)
    (hεHT0 : 0 ≤ εHT) (hεHT : εHT ≤ 1 / 8) (hεHU : 0 ≤ εHU) (hεCU : 0 ≤ εCU)
    (hεU : (1 + εHU) * (1 + εCU) - 1 ≤ 1 / 16) (hφR : 0 ≤ φR) (hφC : 0 ≤ φC)
    {a p uo f : ℕ × ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {m : Mem ℝ}
    (hm : SchurPipelineMem n (qR ++ qC) a p uo f L m) (hA : HoldsMatrix a A m.store) {x : ℝ}
    (hx : m.store.get L 0 = some x) (hx0 : 0 < x) (hxl : c₁ * frobNorm A ≤ x)
    (hxu : x ≤ c₂ * frobNorm A) :
    PWrites law I ((Stmt.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨6, .const 0⟩]).seq
        ((Stmt.call (Has.inj ScalarOp.div) [] [⟨6, .const 0⟩, ⟨5, .const 0⟩] [⟨6, .const 0⟩]).seq
          ((Stmt.loop (.const 2 * (.var 0 * .var 0)) (.call (Has.inj ScalarOp.mul) []
            [⟨0, .var 6 + .var 11⟩, ⟨6, .const 0⟩] [⟨0, .var 6 + .var 11⟩])).seq
          ((Stmt.frame [.var 0, .var 1] [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩] Reg.body).seq
            ((Stmt.frame [.var 0] [⟨3, .var 9⟩]
              (PairMatrix.identity (Op := O) (Tst := Q)).body).seq
            ((Stmt.frame [.var 0] [⟨0, .var 6⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩]
              Red.body).seq
            ((Stmt.frame [.var 0, .var 2, .var 3, .var 4, .var 5]
              [⟨0, .var 6⟩, ⟨1, .var 7 + .var 1⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩,
                ⟨4, .var 10⟩] Core.body).seq (.loop (.const 2 * (.var 0 * .var 0))
              (.call (Has.inj ScalarOp.mul) [] [⟨0, .var 6 + .var 11⟩, ⟨5, .const 0⟩]
                [⟨0, .var 6 + .var 11⟩])))))))))
      (schurPipelineEnv n qR.length qC.length k F T a p uo f L)
      (schurFp n a uo f ⊔ Store.inBlock (L + 1) 0 1) (· = m)
      (SchurOutput a uo f A
        (2 * c₂ * √((n : ℝ) + 1) * (δR + 3 * εHT / c₁ + εCT +
          8 * ((1 + εHU) * (1 + εCU) - 1) / c₁) + 8 * (n + 1) * u)
        (2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2)) (φR + φC) := by
  have hu1 : u ≤ 1 := by
    have : (8 : ℝ) * 1 * u ≤ 8 * ((n : ℝ) + 1) * u :=
      mul_le_mul_of_nonneg_right (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith) hu0
    linarith
  refine PWrites.congr_eval (eval_seq_seq_seq_assoc _ _ _ _ _) ?_
  refine (PWrites.seq hI hloc (φ₂ := φR + φC) (by linarith) (PWrites.of_writes le_rfl
    fun m' τ hm' => by subst hm'; exact schurPipeline_scale_writes hS hM h1 hu1 hm hA hx hx0)
    (PWrites.of_forall_eq hI hloc (fun m' hm' => ?_)
      (measurableSet_eqOff_schurOutput _ a uo f A _ _))).mono (fun _ h => h)
    (sup_le (sup_le le_sup_right (fun _ _ h => Or.inl (Or.inl (Or.inl h)))) le_sup_left)
    (fun _ h => h) (by simp)
  obtain ⟨hm', hx', A₁, hA₁, hA₁n⟩ := hm'
  have hF0 := frobNorm_nonneg A
  have hA₁b : specNorm A₁ ≤ 2 / c₁ := by
    have h := specNorm_add_le A ((x : ℂ) • A₁ - A)
    rw [add_sub_cancel, specNorm_smul, Complex.norm_real, Real.norm_of_nonneg hx0.le] at h
    have hAF := specNorm_le_frobNorm A
    have h3 : 3 * u * frobNorm A ≤ frobNorm A := by nlinarith
    have hFx : frobNorm A ≤ x / c₁ := by rw [le_div_iff₀ hc₁]; linarith
    have : x * specNorm A₁ ≤ x * (2 / c₁) := by
      have : 2 * frobNorm A ≤ x * (2 / c₁) := by
        rw [show x * (2 / c₁) = 2 * (x / c₁) by ring]; linarith
      linarith
    exact le_of_mul_le_mul_left this hx0
  exact schurPipeline_reg_pwrites hS hM h1 hI hloc hReg hRed hCore hCC' hc₁ hδR hεHT0 hεHT hεHU
    hεCU hφC hm' hx' hA₁ hA₁b (measurableSet_eqOff_schurOutput _ a uo f A _ _)
    fun A₂ U₂ Tm T' hεCT hA₂ hTu htr hT' hz m'' hf hT hU => schurOutput_of_run hu0 hu hc₁ hx0
      hxl hxu hδR hεHT0 hεHT hεHU hεCU hεU hεCT hA₁n hA₂ hTu htr hT' hz hf hT hU

variable [Has IdxTst Q] in
/-- **The positive branch on every tape**: with a regularizer that terminates storing some matrix,
a reducer and a terminating core, the positive branch of the pipeline terminates and stores an
accumulator with $\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le 2\varepsilon +
\varepsilon^2$. -/
theorem schurPipeline_pos_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (h1 : Mch.lit 1 = 1) (hu1 : u ≤ 1)
    {Reg Red Core : Impl O Q} {n k F T L : ℕ} {εHU εHT εCU : ℝ} {qR qC : List ℝ}
    (hReg : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {a q : ℕ × ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      HoldsMatrix a A μ.store → μ.store.readBlock q.1 q.2 qR.length = some qR → μ.Live [a, q] →
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock q.1 q.2 qR.length) →
      Writes .total I τ Reg.body (Env.frame [n + 1, qR.length] [a, q, a])
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (fun μ' => ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A' μ'.store) μ)
    (hRed : HessenbergReducerContract εHU εHT (n + 1) Red I)
    (hCore : TerminatingSchurCore εCU k F T (n + 1) qC Core I) (hεHU : 0 ≤ εHU)
    (hεCU : 0 ≤ εCU) {a p uo f : ℕ × ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {m : Mem ℝ} (hm : SchurPipelineMem n (qR ++ qC) a p uo f L m)
    (hA : HoldsMatrix a A m.store) {x : ℝ} (hx : m.store.get L 0 = some x) (hx0 : 0 < x)
    (τ : Tape ℝ) :
    Writes .total I τ ((Stmt.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨6, .const 0⟩]).seq
        ((Stmt.call (Has.inj ScalarOp.div) [] [⟨6, .const 0⟩, ⟨5, .const 0⟩] [⟨6, .const 0⟩]).seq
          ((Stmt.loop (.const 2 * (.var 0 * .var 0)) (.call (Has.inj ScalarOp.mul) []
            [⟨0, .var 6 + .var 11⟩, ⟨6, .const 0⟩] [⟨0, .var 6 + .var 11⟩])).seq
          ((Stmt.frame [.var 0, .var 1] [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩] Reg.body).seq
            ((Stmt.frame [.var 0] [⟨3, .var 9⟩]
              (PairMatrix.identity (Op := O) (Tst := Q)).body).seq
            ((Stmt.frame [.var 0] [⟨0, .var 6⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩]
              Red.body).seq
            ((Stmt.frame [.var 0, .var 2, .var 3, .var 4, .var 5]
              [⟨0, .var 6⟩, ⟨1, .var 7 + .var 1⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩,
                ⟨4, .var 10⟩] Core.body).seq (.loop (.const 2 * (.var 0 * .var 0))
              (.call (Has.inj ScalarOp.mul) [] [⟨0, .var 6 + .var 11⟩, ⟨5, .const 0⟩]
                [⟨0, .var 6 + .var 11⟩])))))))))
      (schurPipelineEnv n qR.length qC.length k F T a p uo f L)
      (schurFp n a uo f ⊔ Store.inBlock (L + 1) 0 1)
      (SchurOrth (n := n) uo (2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2))
      m := by
  obtain ⟨hlen, ha, hp, hu, hf, -, -, -, hap, hq⟩ := id hm
  obtain ⟨h1', h2, h3, -, -, h6⟩ := apart_four hap
  set G := schurFp n a uo f ⊔ Store.inBlock (L + 1) 0 1
  have hFa : Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ≤ G :=
    fun _ _ h => Or.inl (Or.inl (Or.inl h))
  have hFu : Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ≤ G :=
    fun _ _ h => Or.inl (Or.inl (Or.inr h))
  have hdG : Fp.Disj G (Store.inBlock p.1 p.2 (qR ++ qC).length) :=
    hm.disj_words.mono (sup_le (fun _ _ h => Or.inl (Or.inl h)) (fun _ _ h => Or.inr h)) le_rfl
  have hdw : ∀ {m' : Mem ℝ} {F' : Fp}, F' ≤ G → m.store.EqOff F' m'.store →
      SchurPipelineMem n (qR ++ qC) a p uo f L m' := fun hF hfr =>
    hm.of_eqOff hfr ((hdG.mono hF le_rfl))
  refine Writes.congr_eval (eval_seq_seq_seq_assoc _ _ _ _ _ _ _) ?_
  refine (schurPipeline_scale_writes hS hM h1 hu1 hm hA hx hx0).seq_le
    (sup_le (fun _ _ h => Or.inr h) hFa) fun m₁ hfr₁ h₁ => ?_
  obtain ⟨hm₁, hx₁, A₁, hA₁, -⟩ := h₁
  refine (hReg A₁ hA₁ (Store.readBlock_append_left hm₁.2.2.2.2.2.2.2.2.2)
    (hm₁.live_of_subset (by simp)) (h1'.mono le_rfl (Fp.inBlock_le_inBlock le_rfl
      (by simp)))).frame_seq_le rfl rfl (hm₁.live_of_subset (by simp)) hFa
    fun m₂ hfr₂ h₂ => ?_
  obtain ⟨A₂, hA₂⟩ := h₂
  have hm₂ := hm₁.of_eqOff hfr₂ (hdG.mono hFa le_rfl)
  refine (writes_identity_holdsMatrix_one (N := n + 1) hS hM h1 hm₂.room_uo).frame_seq_le
    rfl rfl (hm₂.live_of_subset (by simp)) hFu fun m₃ hfr₃ hU => ?_
  have hm₃ := hm₂.of_eqOff hfr₃ (hdG.mono hFu le_rfl)
  refine (hRed A₂ 1 le_rfl ⟨hA₂.of_eqOff hfr₃ h2.symm, hU⟩ (hm₃.live_of_subset (by simp))
    h2).frame_seq_le rfl rfl (hm₃.live_of_subset (by simp)) (sup_le hFa hFu)
    fun m₄ hfr₄ h₄ => ?_
  obtain ⟨U₁, H, hp₄, -, V₁, ⟨hV₁, -⟩, hU₁⟩ := h₄
  have hm₄ := hm₃.of_eqOff hfr₄ (hdG.mono (sup_le hFa hFu) le_rfl)
  obtain ⟨hlen₄, -, -, -, -, -, -, -, -, hq₄⟩ := id hm₄
  refine (hCore H U₁ le_rfl hp₄ (Store.readBlock_append_right hq₄) (fun z hz => ?_)
    (by have := hm₄.room_f; omega) (apart_tail hap)).frame_seq_le rfl rfl
    (fun z hz => ?_) (fun _ _ h => Or.inl h) fun m₅ hfr₅ h₅ => ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp only [hlen₄] <;> omega
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [hlen₄] <;> omega
  obtain ⟨U₂, Tm, V, ⟨hT₅, hU₅⟩, hV, hU₂⟩ := h₅
  have hm₅ := hm₄.of_eqOff hfr₅ (hdG.mono (fun _ _ h => Or.inl h) le_rfl)
  have hx₅ : m₅.store.get L 0 = some x := by
    rw [hfr₅.2 L 0 (not_schurFp_of_le ha hu hf le_rfl), hfr₄.2 L 0 (fun h => by
      rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> omega), hfr₃.2 L 0 (fun h => by obtain ⟨h, -⟩ := h; omega),
      hfr₂.2 L 0 (fun h => by obtain ⟨h, -⟩ := h; omega), hx₁]
  refine (writes_loop_mul_cell hS (N := 2 * ((n + 1) * (n + 1))) (b := a.1) (o := a.2)
    (y := (L, 0)) (r := x) rfl (fun t _ => rfl) (fun t _ => rfl)
    (hm₅.live_of_subset (by simp)) (fun t ht => ⟨_, Store.get_of_readBlock hT₅ ht 0⟩) hx₅
    (by rintro ⟨h, -⟩; omega)).mono hFa ?_
  rintro m₆ hfr₆ -
  have h1n : specNorm (U₁ - V₁) ≤ εHU := by
    have := hU₁; rw [Matrix.one_mul] at this
    exact this.trans (mul_le_of_le_one_right hεHU specNorm_one_le)
  exact ⟨U₂, hU₅.of_eqOff hfr₆ h2,
    specNorm_conjTranspose_mul_self_sub_one_le_of_tracked hεCU hV₁ hV h1n hU₂⟩

/-- The memory of a run after the two scratch cells of the pipeline, from its input. -/
theorem SchurPipelineInput.mem_of_alloc {n : ℕ} {qs : List ℝ} {a p uo f : ℕ × ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {μ : Mem ℝ}
    (hin : SchurPipelineInput qs a p uo f A μ) {s₁ : Store ℝ} {q : ℕ}
    (hlen : s₁.length = μ.store.length + [1, 1].length)
    (hlens : ∀ i (hi : i < [1, 1].length), s₁.len (μ.store.length + i) = [1, 1][i])
    (hBelow : Store.Below μ.store.length μ.store s₁) :
    SchurPipelineMem n qs a p uo f μ.store.length ⟨s₁, q⟩ ∧ HoldsMatrix a A s₁ := by
  obtain ⟨hl, hroom, hap, hA, hP⟩ := hin
  have hlt : ∀ z ∈ [a, p, uo, f], z.1 < μ.store.length := hl
  have ha := hlt a (by simp)
  have hp := hlt p (by simp)
  refine ⟨⟨by simpa using hlen, ha, hp, hlt uo (by simp), hlt f (by simp), ?_,
    by simpa using hlens 0 (by simp), by simpa using hlens 1 (by simp), hap, ?_⟩,
    hA.of_below hBelow ha⟩
  · rw [Mem.room_eq_of_below (μ := μ) (μ' := ⟨s₁, q⟩) hBelow (by simpa using hlt)]
    exact hroom
  · exact hBelow.keep (Store.readsOnly_readBlock _ _ _ _) (fun _ _ h => h.1 ▸ hp) hP

variable [Has IdxTst Q] in
/-- **The pipeline terminates on every tape** with a regularizer that terminates storing some
matrix, a reducer and a terminating core, and stores an accumulator with
$\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le 2\varepsilon +
\varepsilon^2$, $\varepsilon = (1 + \varepsilon_{H,U})(1 + \varepsilon_{C,U}) - 1$. -/
theorem schurPipelineWith_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I) (hu1 : u ≤ 1)
    {Nm Reg Red Core : Impl O Q} {k F T : ℕ} {c₁ c₂ εHU εHT εCU : ℝ} {qR qC : List ℝ}
    (hNm : FrobNormEstimateContract c₁ c₂ (n + 1) Nm I)
    (hReg : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {a q : ℕ × ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      HoldsMatrix a A μ.store → μ.store.readBlock q.1 q.2 qR.length = some qR → μ.Live [a, q] →
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock q.1 q.2 qR.length) →
      Writes .total I τ Reg.body (Env.frame [n + 1, qR.length] [a, q, a])
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (fun μ' => ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A' μ'.store) μ)
    (hRed : HessenbergReducerContract εHU εHT (n + 1) Red I)
    (hCore : TerminatingSchurCore εCU k F T (n + 1) qC Core I) (hc₁ : 0 < c₁)
    (hεHU : 0 ≤ εHU) (hεCU : 0 ≤ εCU) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {a p uo f : ℕ × ℕ} {μ : Mem ℝ} (hin : SchurPipelineInput (qR ++ qC) a p uo f A μ)
    (τ : Tape ℝ) :
    Writes .total I τ (schurPipelineWith Nm Reg Red Core).body
      (Env.frame [n + 1, qR.length, qC.length, k, F, T] [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOrth (n := n) uo
        (2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2)) μ := by
  have h1 : Mch.lit 1 = 1 := by simpa using hNat 1 (by omega)
  have heU : 0 ≤ 2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2 := by
    have : 0 ≤ (1 + εHU) * (1 + εCU) - 1 := by nlinarith
    positivity
  have hlt : ∀ z ∈ [a, p, uo, f], z.1 < μ.store.length := hin.1
  change Writes .total I τ (Stmt.allocs [.const 1, .const 1] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [1, 1]) rfl
    (fun hBelow ⟨U, hU, ho⟩ => ⟨U, hU.of_below hBelow (hlt uo (by simp)), ho⟩) ?_
  intro s₁ hlen hlens hBelow
  obtain ⟨hm, hA⟩ := hin.mem_of_alloc (q := μ.pos) hlen hlens hBelow
  set L := μ.store.length
  show Writes .total I τ _ (schurPipelineEnv n qR.length qC.length k F T a p uo f L) _ _ _
  obtain ⟨-, ha, hp, hu, hf, -, hLl, -⟩ := id hm
  have hlive : (⟨s₁, μ.pos⟩ : Mem ℝ).Live [a, (L, 0)] := hm.live_of_subset (by simp)
  have hFL : Store.inBlock L 0 1 ≤ schurFp n a uo f ⊔ Fp.above L :=
    fun _ _ h => Or.inr (h.1 ▸ le_rfl)
  refine (hNm A le_rfl hA hlive (show 0 + 1 ≤ s₁.len L by simp at hLl ⊢; omega)
    (show a.1 ≠ L by omega)).frame_seq_le rfl rfl hlive hFL fun m hfr ⟨x, hx, hxl, hxu⟩ => ?_
  have hm' := hm.of_eqOff hfr (Fp.disj_inBlock_of_ne (by omega))
  have hA' := hA.of_eqOff hfr (Fp.disj_inBlock_of_ne (by omega))
  refine writes_ite rfl rfl (hC.test_isPos (x := (L, 0)) (d := []) hx) ?_
  by_cases hx0 : 0 < x
  · simp only [id, hx0, decide_true, if_true]
    exact (schurPipeline_pos_terminates hS hM h1 hu1 hReg hRed hCore hεHU hεCU hm' hA' hx hx0
      τ).mono (sup_le le_sup_left (fun b _ h => Or.inr (show L ≤ b by rw [h.1]; omega)))
      fun _ _ h => h
  · simp only [id, hx0, decide_false, Bool.false_eq_true, if_false]
    have hF : frobNorm A = 0 :=
      le_antisymm (by nlinarith [frobNorm_nonneg A]) (frobNorm_nonneg A)
    obtain rfl := frobNorm_eq_zero_iff.mp hF
    refine (schurPipeline_zero_writes (nr := qR.length) (nq := qC.length) (k := k) (F := F)
      (T := T) (eA := 0) hS hM hL h1 hm' hA' heU).mono le_sup_left ?_
    rintro m' - ⟨-, U, -, -, hU, -, -, ho⟩
    exact ⟨U, hU, ho⟩

end Steps

/-- **The generic composition theorem**: for any norm estimate, regularizer (into `C`), reducer
and Schur core (from `C'`) meeting their contracts, with the class transfer `hCC'` through the
reducer's witnessed similarity, the pipeline stores a Schur output except with probability
$\varphi_R + \varphi_C$. The accumulator errors compose relatively,
$\varepsilon = (1 + \varepsilon_{H,U})(1 + \varepsilon_{C,U}) - 1$, and
$e_U = 2\varepsilon + \varepsilon^2$; the residual adds the regularizer's, the reducer's and the
core's errors, scaled by $s \le c_2\|\mathbf{A}\|_{\mathsf F} \le c_2\sqrt{n+1}\|\mathbf{A}\|_2$. -/
theorem schurPipelineWith_measureReal_not_schur_le [Has ScalarOp O] [Has IndexOp O]
    [Has CmpTst Q] [Has IdxTst Q] {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {Nm Reg Red Core : Impl O Q} {k F T : ℕ}
    {c₁ c₂ δR φR εHU εHT εCU εCT φC : ℝ} {qR qC : List ℝ}
    {C C' : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop}
    (hNm : FrobNormEstimateContract c₁ c₂ (n + 1) Nm I)
    (hReg : RandomRegularizerContract law δR φR C (n + 1) (2 / c₁) qR Reg I)
    (hRed : HessenbergReducerContract εHU εHT (n + 1) Red I)
    (hCore : RandomSchurCoreContract law εCU εCT φC C' k F T (n + 1) (4 / c₁) qC Core I)
    (hCC' : ∀ (A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), C A →
      IsPerturbedUnitarySimilarBy V A H (εHT * (2 / c₁ + δR)) → C' H)
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂) (hu0 : 0 ≤ u) (hu : 8 * ((n : ℝ) + 1) * u ≤ 1 / 4)
    (hδR : δR ≤ 1 / c₁) (hεHT0 : 0 ≤ εHT) (hεHT : εHT ≤ 1 / 8) (hεHU : 0 ≤ εHU)
    (hεCU : 0 ≤ εCU) (hεU : (1 + εHU) * (1 + εCU) - 1 ≤ 1 / 16) (hφR : 0 ≤ φR) (hφC : 0 ≤ φC)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (qR ++ qC) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (schurPipelineWith Nm Reg Red Core).body
      (Env.frame [n + 1, qR.length, qC.length, k, F, T] [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOutput a uo f A
        (2 * c₂ * √((n : ℝ) + 1) * (δR + 3 * εHT / c₁ + εCT +
          8 * ((1 + εHU) * (1 + εCU) - 1) / c₁) + 8 * (n + 1) * u)
        (2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2)) μ} ≤
      φR + φC := by
  obtain ⟨hl, hroom, hap, hA, hP⟩ := hin
  have h1 : Mch.lit 1 = 1 := by simpa using hNat 1 (by omega)
  set eA := 2 * c₂ * √((n : ℝ) + 1) * (δR + 3 * εHT / c₁ + εCT +
    8 * ((1 + εHU) * (1 + εCU) - 1) / c₁) + 8 * (n + 1) * u
  set eU := 2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2
  have heU : 0 ≤ eU := by
    have : 0 ≤ (1 + εHU) * (1 + εCU) - 1 := by nlinarith
    positivity
  have hlt : ∀ z ∈ [a, p, uo, f], z.1 < μ.store.length := hl
  refine PWrites.measureReal_not_writes_le (Pre := (· = μ)) ?_ rfl hξ
  change PWrites law I (Stmt.allocs [.const 1, .const 1] _) _ _ _ _ _
  refine PWrites.allocs (ns := [1, 1]) rfl
    (Pre₁ := fun L m => SchurPipelineMem n (qR ++ qC) a p uo f L m ∧ HoldsMatrix a A m.store)
    (fun m s₁ hm hlen hlens hBelow => ?_) (fun m hm s s' q hBelow hout => ?_) fun L => ?_
  · subst hm
    exact SchurPipelineInput.mem_of_alloc ⟨hl, hroom, hap, hA, hP⟩ hlen hlens hBelow
  · subst hm
    have ha := hlt a (by simp)
    have hu := hlt uo (by simp)
    have hf := hlt f (by simp)
    obtain ⟨hf0, U, T', hT, hU, hTu, hr, ho⟩ := hout
    exact ⟨by rw [← hf0]; exact (hBelow f.1 hf).2 f.2, U, T', hT.of_below hBelow ha,
      hU.of_below hBelow hu, hTu, hr, ho⟩
  show PWrites law I _ (schurPipelineEnv n qR.length qC.length k F T a p uo f L) _ _ _ _
  have hFL : Store.inBlock L 0 1 ≤ schurFp n a uo f ⊔ Fp.above L :=
    fun _ _ h => Or.inr (h.1 ▸ le_rfl)
  have hFL' : Store.inBlock (L + 1) 0 1 ≤ schurFp n a uo f ⊔ Fp.above L :=
    fun b _ h => Or.inr (show L ≤ b by rw [h.1]; omega)
  set MidN : Mem ℝ → Prop := fun m => SchurPipelineMem n (qR ++ qC) a p uo f L m ∧
    HoldsMatrix a A m.store ∧ ∃ x : ℝ, m.store.get L 0 = some x ∧ c₁ * frobNorm A ≤ x ∧
      x ≤ c₂ * frobNorm A with hMidN
  have hnm : ∀ m τ, SchurPipelineMem n (qR ++ qC) a p uo f L m ∧ HoldsMatrix a A m.store →
      Writes .total I τ (Stmt.frame [.var 0] [⟨0, .var 6⟩, ⟨5, .const 0⟩] Nm.body)
        (schurPipelineEnv n qR.length qC.length k F T a p uo f L) (Store.inBlock L 0 1) MidN m := by
    rintro m τ ⟨hm, hA'⟩
    obtain ⟨-, ha, hp, -, -, -, hLl, -⟩ := id hm
    have hlive : m.Live [a, (L, 0)] := hm.live_of_subset (by simp)
    refine ((hNm A le_rfl hA' hlive (show 0 + 1 ≤ m.store.len L by omega)
      (show a.1 ≠ L by omega)).in_frame rfl rfl hlive).mono
      le_rfl fun m' hfr ⟨x, hx, hxl, hxu⟩ => ⟨hm.of_eqOff hfr
        (Fp.disj_inBlock_of_ne (by omega)), hA'.of_eqOff hfr (Fp.disj_inBlock_of_ne (by omega)),
        x, hx, hxl, hxu⟩
  have htest : ∀ m, MidN m → ∃ b, I.testAt (Has.inj CmpTst.isPos) [] [⟨5, .const 0⟩]
      (schurPipelineEnv n qR.length qC.length k F T a p uo f L) m = some b := by
    rintro m ⟨-, -, x, hx, -⟩
    rw [Interp.testAt_eq rfl rfl]
    exact ⟨_, hC.test_isPos (x := (L, 0)) hx⟩
  have hthen := PWrites.of_forall_eq hI hloc (Pre := fun m => MidN m ∧
      I.testAt (Has.inj CmpTst.isPos) [] [⟨5, .const 0⟩]
        (schurPipelineEnv n qR.length qC.length k F T a p uo f L) m = some true)
    (fun m ⟨⟨hm, hA', x, hx, hxl, hxu⟩, ht⟩ => by
      rw [Interp.testAt_eq rfl rfl, hC.test_isPos (x := (L, 0)) hx] at ht
      have hx0 : 0 < x := by simpa using ht
      exact (schurPipeline_pos_pwrites hS hM h1 hI hloc hReg hRed hCore hCC' hc₁ hu0 hu hδR
        hεHT0 hεHT hεHU hεCU hεU hφR hφC hm hA' hx hx0 hxl hxu).mono (fun _ h => h)
        (sup_le le_sup_left hFL') (fun _ h => h) le_rfl)
    (measurableSet_eqOff_schurOutput (schurFp n a uo f ⊔ Fp.above L) a uo f A eA eU)
  have helse := PWrites.of_writes (law := law) (φ := 0) le_rfl
    (Pre := fun m => MidN m ∧ I.testAt (Has.inj CmpTst.isPos) [] [⟨5, .const 0⟩]
        (schurPipelineEnv n qR.length qC.length k F T a p uo f L) m = some false)
    (F := schurFp n a uo f ⊔ Fp.above L) (Post := SchurOutput a uo f A eA eU)
    fun m τ ⟨⟨hm, hA', x, hx, hxl, hxu⟩, ht⟩ => by
      rw [Interp.testAt_eq rfl rfl, hC.test_isPos (x := (L, 0)) hx] at ht
      have hx0 : x ≤ 0 := by simpa using ht
      have hF : frobNorm A = 0 :=
        le_antisymm (by nlinarith [frobNorm_nonneg A]) (frobNorm_nonneg A)
      obtain rfl := frobNorm_eq_zero_iff.mp hF
      exact (schurPipeline_zero_writes (nr := qR.length) (nq := qC.length) (k := k) (F := F)
        (T := T) hS hM hL h1 hm hA' heU).mono le_sup_left fun _ _ h => h
  refine (PWrites.seq hI hloc (φ₂ := max (φR + φC) 0) (le_max_right _ _)
    (PWrites.of_writes le_rfl fun m τ hm => hnm m τ hm)
    (PWrites.ite hI htest hthen helse)).mono (fun _ h => h) (sup_le hFL le_rfl) (fun _ h => h)
    (by rw [max_eq_left (by linarith)]; linarith)

/-- **The eigenvalue corollary of a Schur output**: with $e_U \le 1/8$, the diagonal of
$\widehat{\mathbf{T}}$ lists the eigenvalues of $\mathbf{A} + \mathbf{E}$ with
$\|\mathbf{E}\|_2 \le (e_A + 4e_U(1 + e_A))\|\mathbf{A}\|_2$
(`NLAlib.HasOrthonormalCols.isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul`). -/
theorem SchurOutput.exists_isEigenvalueListing {n : ℕ} {a uo f : ℕ × ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {eA eU : ℝ} {μ' : Mem ℝ}
    (h : SchurOutput a uo f A eA eU μ') (heU : eU ≤ 1 / 8) :
    ∃ (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      HoldsMatrix a T μ'.store ∧ specNorm E ≤ (eA + 4 * eU * (1 + eA)) * specNorm A ∧
      IsEigenvalueListing (A + E) fun i => T i i := by
  obtain ⟨-, U, T, hT, -, hTu, hA, hU⟩ := h
  obtain ⟨V, E, hV, -, hE, hAE⟩ := exists_hasOrthonormalCols_add_eq_mul_mul_conjTranspose hA hU heU
  have hT' : Vᴴ * (A + E) * V = T := by
    rw [hAE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.one_mul,
      Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.mul_one]
  refine ⟨T, E, hT, hE, ?_⟩
  have := hV.isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul (A := A + E)
    (by rw [hT']; exact hTu)
  simpa only [hT'] using this

/-- **The exact-unitary corollary of a Schur output**: with $e_U \le 1/8$, an exact unitary
$\mathbf{V}$ within $e_U$ of $\widehat{\mathbf{U}}$ with $\mathbf{A} + \mathbf{E} =
\mathbf{V}\widehat{\mathbf{T}}\mathbf{V}^{\mathsf H}$,
$\|\mathbf{E}\|_2 \le (e_A + 4e_U(1 + e_A))\|\mathbf{A}\|_2$. -/
theorem SchurOutput.exists_hasOrthonormalCols {n : ℕ} {a uo f : ℕ × ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {eA eU : ℝ} {μ' : Mem ℝ}
    (h : SchurOutput a uo f A eA eU μ') (heU : eU ≤ 1 / 8) :
    ∃ U T V E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a T μ'.store ∧
      HoldsMatrix uo U μ'.store ∧ HasOrthonormalCols V ∧ specNorm (U - V) ≤ eU ∧
      specNorm E ≤ (eA + 4 * eU * (1 + eA)) * specNorm A ∧ A + E = V * T * Vᴴ := by
  obtain ⟨-, U, T, hT, hUs, -, hA, hU⟩ := h
  obtain ⟨V, E, hV, hUV, hE, hAE⟩ :=
    exists_hasOrthonormalCols_add_eq_mul_mul_conjTranspose hA hU heU
  exact ⟨U, T, V, E, hT, hUs, hV, hUV, hE, hAE⟩

/-- **The static count of the pipeline** is the sum of the stages' counts plus
$64(N + 1)^2$ for the glue (scaling, identity, branch). -/
theorem size_stmtCost_schurPipelineWith_le [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]
    (Nm Reg Red Core : Impl O Q) (N nr nq k F T : ℕ) :
    Count.size (stmtCost (schurPipelineWith Nm Reg Red Core).body [N, nr, nq, k, F, T]) ≤
      Count.size (stmtCost Nm.body [N]) + Count.size (stmtCost Reg.body [N, nr]) +
        Count.size (stmtCost Red.body [N]) + Count.size (stmtCost Core.body [N, nq, k, F, T]) +
        64 * (N + 1) ^ 2 := by
  have hsup : ∀ x y : Count O Q, Count.size (x ⊔ y) ≤ Count.size x + Count.size y := fun x y =>
    (size_mono (sup_le (le_add_of_nonneg_right (zero_le (a := y)))
      (le_add_of_nonneg_left (zero_le (a := x))))).trans_eq (map_add _ x y)
  simp only [schurPipelineWith, Stmt.alloc, stmtCost, useCost, testCost, IExp.evalList,
    IExp.eval, List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
    List.getElem?_nil, Option.map_some, Option.getD_some, Finset.sum_const, Finset.card_range,
    Operand.off, zero_add]
  refine le_trans ?_ (Nat.le_add_left _ _)
  rw [map_add]
  refine (Nat.add_le_add_left (hsup _ _) _).trans ?_
  simp only [map_add, map_nsmul, Count.one, Count.test, size_single, smul_eq_mul]
  nlinarith

end NLAlib.Schur
