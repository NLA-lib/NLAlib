/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Pipeline

/-!
# The composition theorem of the dense Schur pipeline

For any norm estimate, regularizer, Hessenberg reducer and Schur core meeting their contracts
(`NLAlib.Eigensolvers.Schur.Contracts`), the pipeline `NLAlib.Schur.schurPipelineWith` stores a
Schur output of its input except with the sum of the failure probabilities of the regularizer and
the core: the accumulator errors compose relatively and the residual adds the stages' errors, scaled
back by the norm estimate. Its static count is at most the sum of the stages' counts and the glue.

## Main results

* `NLAlib.Schur.schurPipelineWith_measureReal_not_schur_le`: the generic composition theorem.
* `NLAlib.Schur.schurPipelineWith_pwrites_regularizedSchur`,
  `NLAlib.Schur.schurPipelineWith_measureReal_not_regularizedSchur_le`: the same with the
  regularized matrix exposed.
* `NLAlib.Schur.SchurOutput.exists_isEigenvalueListing`,
  `NLAlib.Schur.SchurOutput.exists_hasOrthonormalCols`: the eigenvalues and an exact unitary.
* `NLAlib.Schur.size_stmtCost_schurPipelineWith_le`: the instrumented static count is at most the
  sum of the stages' and the glue.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops MeasureTheory
open scoped Matrix
variable {O Q : Type}

/-- **The generic composition theorem**: for any norm estimate, regularizer (into `C`), reducer
and Schur core (from `C'`) meeting their contracts, with the class transfer `hCC'` through the
reducer's witnessed similarity, the pipeline stores a Schur output except with probability
$\varphi_R + \varphi_C$. The accumulator errors compose relatively,
$\varepsilon = (1 + \varepsilon_{H,U})(1 + \varepsilon_{C,U}) - 1$, and
$e_U = 2\varepsilon + \varepsilon^2$; the residual adds the regularizer's, the reducer's and the
core's errors, scaled by $s \le c_2\|\mathbf{A}\|_{\mathsf F} \le c_2\sqrt{n+1}\|\mathbf{A}\|_2$. -/
theorem schurPipelineWith_measureReal_not_schur_le [Has ScalarOp O] [Has IndexOp O]
    [Has CmpTst Q] {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {Nm Reg Red Core : Stmt O Q} {k F T : ℕ}
    {c₁ c₂ δR φR εHU εHT εCU εCT φC : ℝ} {qR qC : List ℝ}
    {C C' : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop}
    (hNm : FrobNormEstimateContract c₁ c₂ (n + 1) Nm I)
    (hReg : RandomRegularizerContract law δR φR C (n + 1) (2 / c₁) qR Reg I)
    (hRed : HessenbergReducerContract εHU εHT (n + 1) Red I)
    (hCore : RandomSchurCoreContract law εCU εCT φC C' k F T (n + 1) (4 / c₁) qC Core I)
    (hCC' : ∀ (A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), C A →
      IsPerturbedUnitarySimilarBy V A H (εHT * (2 / c₁ + δR)) → C' H)
    (hc₁ : 0 < c₁) (hu0 : 0 ≤ u) (hu : 8 * ((n : ℝ) + 1) * u ≤ 1 / 4)
    (hδR : δR ≤ 1 / c₁) (hεHT0 : 0 ≤ εHT) (hεHT : εHT ≤ 1 / 8) (hεHU : 0 ≤ εHU)
    (hεCU : 0 ≤ εCU) (hεU : (1 + εHU) * (1 + εCU) - 1 ≤ 1 / 16) (hφR : 0 ≤ φR) (hφC : 0 ≤ φC)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (qR ++ qC) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (schurPipelineWith Nm Reg Red Core)
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
  change PWrites law I _ (schurPipelineEnv n qR.length qC.length k F T a p uo f L) _ _ _ _
  have hFL : Store.inBlock L 0 1 ≤ schurFp n a uo f ⊔ Fp.above L :=
    fun _ _ h => Or.inr (h.1 ▸ le_rfl)
  have hFL' : Store.inBlock (L + 1) 0 1 ≤ schurFp n a uo f ⊔ Fp.above L :=
    fun b _ h => Or.inr (show L ≤ b by rw [h.1]; omega)
  set MidN : Mem ℝ → Prop := fun m => SchurPipelineMem n (qR ++ qC) a p uo f L m ∧
    HoldsMatrix a A m.store ∧ ∃ x : ℝ, m.store.get L 0 = some x ∧ c₁ * frobNorm A ≤ x ∧
      x ≤ c₂ * frobNorm A with hMidN
  have hnm : ∀ m τ, SchurPipelineMem n (qR ++ qC) a p uo f L m ∧ HoldsMatrix a A m.store →
      Writes .total I τ (Stmt.frame [.var 0] [⟨0, .var 6⟩, ⟨5, .const 0⟩] Nm)
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

/-- **The scaled matrix is bounded**: if $c_1\|\mathbf{A}\|_{\mathsf F} \le x$, $x > 0$,
$c_1 > 0$, $\boldsymbol{u} \le 1/3$ and $\|x\mathbf{A}_1 - \mathbf{A}\|_2 \le
3\boldsymbol{u}\|\mathbf{A}\|_{\mathsf F}$, then $\|\mathbf{A}_1\|_2 \le 2/c_1$. -/
theorem specNorm_le_two_div_of_scaled {N : ℕ} {A A₁ : Matrix (Fin N) (Fin N) ℂ} {x u c₁ : ℝ}
    (hc₁ : 0 < c₁) (hx0 : 0 < x) (hxl : c₁ * frobNorm A ≤ x) (hu : u ≤ 1 / 3)
    (hA₁ : specNorm ((x : ℂ) • A₁ - A) ≤ 3 * u * frobNorm A) : specNorm A₁ ≤ 2 / c₁ := by
  have hF0 := frobNorm_nonneg A
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

/-- **The numbers of a pipeline run end in a Schur output with its regularized matrix**: the
scaled $\mathbf{A}_1$, the regularized $\mathbf{A}_2$ of the class `C` and the end of the tail
(`NLAlib.Schur.SchurTailOutput`) give `NLAlib.Schur.RegularizedSchurOutput` with
$\mathbf{X} = x\mathbf{A}_2$ and $s = x$, the errors read off
`NLAlib.Schur.schurPipeline_budget_split`. -/
theorem regularizedSchurOutput_of_tail {n : ℕ}
    {C : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop} {a uo f : ℕ × ℕ}
    {A A₁ A₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {m' : Mem ℝ}
    {u x c₁ c₂ δR εHT εCT ε : ℝ} (hu0 : 0 ≤ u) (hu : 8 * ((n : ℝ) + 1) * u ≤ 1 / 4)
    (hc₁ : 0 < c₁) (hx0 : 0 < x) (hxl : c₁ * frobNorm A ≤ x) (hxu : x ≤ c₂ * frobNorm A)
    (hδR : δR ≤ 1 / c₁) (hεHT0 : 0 ≤ εHT) (hεHT : εHT ≤ 1 / 8) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 16)
    (hA₁ : specNorm ((x : ℂ) • A₁ - A) ≤ 3 * u * frobNorm A) (hA₂ : specNorm (A₂ - A₁) ≤ δR)
    (hC : C A₂)
    (hT : SchurTailOutput a uo f ε εHT εCT u x A₂ m') :
    RegularizedSchurOutput C a uo f A c₁ c₂
      (c₂ * √((n : ℝ) + 1) * δR + 3 * √((n : ℝ) + 1) * u)
      (schurPipelineEX n c₁ c₂ u εHT εCT ε) (2 * ε + ε ^ 2) m' := by
  obtain ⟨hf, U, T₁, T', hTs, hUs, hTu, hεCT, htr, hT'⟩ := hT
  have hδR0 : 0 ≤ δR := (specNorm_nonneg _).trans hA₂
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
  obtain ⟨hb₁, hb₂⟩ := schurPipeline_budget_split (t₁ := specNorm A₁) (t₂ := specNorm A₂)
    (specNorm_nonneg A) (frobNorm_nonneg A) hFa hn1 (by rw [hsq]; linarith) hu0 hc₁ hx0 hxl hxu
    ht₁ (by linarith)
    (by have := specNorm_add_le A₁ (A₂ - A₁); rw [add_sub_cancel] at this; linarith)
    (specNorm_nonneg _) hδR0 hδR hεHT0 hεHT hεCT hε0 hε
  rw [hsq] at hb₂
  have hX := specNorm_smul_sub_mul_mul_conjTranspose_le_of_tracked hx0 hu0 htr hε0 hT'
  have hN : √(((n + 1 : ℕ)) : ℝ) = √((n : ℝ) + 1) := by push_cast; rfl
  rw [hN] at hX
  refine ⟨hf, U, T', (x : ℂ) • A₂, hTs, hUs, hTu,
    (htr.specNorm_sub_mul_mul_conjTranspose_le hε0).2, ?_, ?_, Or.inr ⟨x, hxl, hxu, ?_⟩⟩
  · have e : A - (x : ℂ) • A₂ = -((x : ℂ) • A₁ - A) - (x : ℂ) • (A₂ - A₁) := by
      rw [smul_sub]; abel
    rw [e]
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_neg, specNorm_smul, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    have := mul_le_mul_of_nonneg_left hA₂ hx0.le
    have e2 : (c₂ * √((n : ℝ) + 1) * δR + 3 * √((n : ℝ) + 1) * u) * specNorm A =
        (c₂ * √((n : ℝ) + 1) * δR + 3 * √((n : ℝ) + 1) * u) * specNorm A := rfl
    linarith
  · refine hX.trans ?_
    unfold schurPipelineEX
    linarith
  · have e : x⁻¹ • (x : ℂ) • A₂ = A₂ := by
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hx0.ne',
        Complex.ofReal_one, one_mul]
    rw [e]
    exact hC

/-- The memories of the pipeline after the scaling: the norm estimate $x$ and a stored
$\mathbf{A}_1$ with
$\|x\mathbf{A}_1 - \mathbf{A}\|_2 \le 3\boldsymbol{u}\|\mathbf{A}\|_{\mathsf F}$. -/
private abbrev SchurScaledMem (n : ℕ) (qs : List ℝ) (a p uo f : ℕ × ℕ) (L : ℕ) (c₁ c₂ u : ℝ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (m' : Mem ℝ) : Prop :=
  SchurPipelineMem n qs a p uo f L m' ∧
    ∃ x : ℝ, m'.store.get L 0 = some x ∧ 0 < x ∧ c₁ * frobNorm A ≤ x ∧ x ≤ c₂ * frobNorm A ∧
      ∃ A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A₁ m'.store ∧
        specNorm ((x : ℂ) • A₁ - A) ≤ 3 * u * frobNorm A

/-- The memories of the pipeline after the regularizer: a stored $\mathbf{A}_2$ of the class `C`
within $\delta_R$ of the scaled $\mathbf{A}_1$. -/
private abbrev SchurRegularizedMem (C : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop)
    (n : ℕ) (qs : List ℝ) (a p uo f : ℕ × ℕ) (L : ℕ) (c₁ c₂ u δR : ℝ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (m' : Mem ℝ) : Prop :=
  SchurPipelineMem n qs a p uo f L m' ∧
    ∃ x : ℝ, m'.store.get L 0 = some x ∧ 0 < x ∧ c₁ * frobNorm A ≤ x ∧ x ≤ c₂ * frobNorm A ∧
      ∃ A₁ A₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        specNorm ((x : ℂ) • A₁ - A) ≤ 3 * u * frobNorm A ∧ HoldsMatrix a A₂ m'.store ∧
          specNorm (A₂ - A₁) ≤ δR ∧ C A₂

/-- The regularizer on the scaled memories, glued over them through the class `C`: except with
probability $\varphi_R$ it stores a matrix of `C` within $\delta_R$ of the scaled matrix. -/
private theorem schurPipeline_regularizer_pwrites {I : Interp O Q ℝ} (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {Reg : Stmt O Q} {n k F T L : ℕ} {c₁ c₂ δR φR u : ℝ} {qR qC : List ℝ}
    {C : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop}
    (hReg : RandomRegularizerContract law δR φR C (n + 1) (2 / c₁) qR Reg I)
    (hCm : MeasurableSet {X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ | C X})
    (hc₁ : 0 < c₁) (hu3 : u ≤ 1 / 3) {a p uo f : ℕ × ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} :
    PWrites law I (Stmt.frame [.var 0, .var 1] [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩] Reg)
      (schurPipelineEnv n qR.length qC.length k F T a p uo f L)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (SchurScaledMem n (qR ++ qC) a p uo f L c₁ c₂ u A)
      (SchurRegularizedMem C n (qR ++ qC) a p uo f L c₁ c₂ u δR A) φR := by
  have hFa : Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ≤ schurFp n a uo f :=
    fun _ _ h => Or.inl (Or.inl h)
  set g : Mem ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    fun m => storedMatrix a (n + 1) (n + 1) m.store with hg
  have hgm : Measurable g := ShiftedQR.measurable_storedMatrix a (n + 1) (n + 1)
  set Mid₁ := SchurScaledMem n (qR ++ qC) a p uo f L c₁ c₂ u A with hMid₁
  set Mid₂ := SchurRegularizedMem C n (qR ++ qC) a p uo f L c₁ c₂ u δR A with hMid₂
  -- the regularizer, glued over the scaled memories through the class
  have hfam : ∀ y : {m // Mid₁ m}, PWrites law I
      (Stmt.frame [.var 0, .var 1] [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩] Reg)
      (schurPipelineEnv n qR.length qC.length k F T a p uo f L)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (fun m => m = y.1)
      (fun m' => (∀ j < 2 * ((n + 1) * (n + 1)), (m'.store.get a.1 (a.2 + j)).isSome) ∧
        C (g m') ∧ specNorm (g m' - g y.1) ≤ δR) φR := by
    rintro ⟨m, hm, x, hx, hx0, hxl, hxu, A₁, hA₁, hn⟩
    obtain ⟨-, -, -, -, -, -, -, -, hap, hq⟩ := id hm
    obtain ⟨h1', -, -, -, -, -⟩ := apart_four hap
    have hA₁b := specNorm_le_two_div_of_scaled hc₁ hx0 hxl hu3 hn
    refine ((hReg A₁ le_rfl hA₁b (a := a) (q := p)).in_frame
      (ρ := schurPipelineEnv n qR.length qC.length k F T a p uo f L) (ds := [.var 0, .var 1])
      (args := [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩]) rfl rfl
      fun m' hm' z hz => hm'.2.2.1 z (by
        simp only [List.mem_cons, List.mem_nil_iff] at hz ⊢; tauto)).mono_eqOff
      (Pre' := fun m' => m' = m) (fun m' hm' => ?_) (fun m₀ m' hm₀ hfr ⟨E, hE, hEn, hCE⟩ => ?_)
    · subst hm'
      exact ⟨hA₁, Store.readBlock_append_left hq, hm.live_of_subset (by simp),
        h1'.mono le_rfl (Fp.inBlock_le_inBlock le_rfl (by simp))⟩
    · subst hm₀
      have e₁ : g m' = A₁ + E := hE.eq_storedMatrix.symm
      have e₂ : g m₀ = A₁ := hA₁.eq_storedMatrix.symm
      refine ⟨fun j hj => ?_, by rw [e₁]; exact hCE, by rw [e₁, e₂]; simpa using hEn⟩
      rw [Store.get_of_readBlock hE hj 0]; rfl
  have hTR : MeasurableSet {y : Mem ℝ × Mem ℝ |
      y.1.store.EqOff (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) y.2.store ∧
      ((∀ j < 2 * ((n + 1) * (n + 1)), (y.2.store.get a.1 (a.2 + j)).isSome) ∧
        C (g y.2) ∧ specNorm (g y.2 - g y.1) ≤ δR)} :=
    (Mem.measurableSet_eqOff _).inter ((measurable_snd
      (ShiftedQR.measurableSet_forall_isSome a _)).inter (((hgm.comp measurable_snd) hCm).inter
      (measurableSet_le
        ((continuous_specNorm.comp (continuous_fst.sub continuous_snd)).measurable.comp
        ((hgm.comp measurable_snd).prodMk (hgm.comp measurable_fst))) measurable_const)))
  refine PStep.mono (PWrites.pstep_of_forall hI hloc (ι := {m // Mid₁ m})
    (P := fun y m => m = y.1) hfam hTR
    fun y m m' hm hfr hq => ⟨hfr, hm ▸ hq⟩) (fun m hm => ⟨⟨m, hm⟩, rfl⟩)
    (fun m m' hm ⟨hfr, hsome, hCg, hδ⟩ => ⟨hfr, ?_⟩) le_rfl
  obtain ⟨hm', x, hx, hx0, hxl, hxu, A₁, hA₁, hn⟩ := hm
  have haL : a.1 < L := hm'.2.1
  have e₂ : g m = A₁ := hA₁.eq_storedMatrix.symm
  rw [e₂] at hδ
  exact ⟨hm'.of_eqOff hfr (hm'.disj_words.mono (fun _ _ h => Or.inl (Or.inl (hFa _ _ h)))
    le_rfl), x, by rw [hfr.2 L 0 (fun h => by obtain ⟨h, -⟩ := h; omega), hx], hx0, hxl, hxu,
    A₁, g m', hn, holdsMatrix_storedMatrix hsome, hδ, hCg⟩

/-- **The positive branch of the pipeline with the regularized matrix exposed**: from the run
memories holding $\mathbf{A}$ and a norm estimate $c_1\|\mathbf{A}\|_{\mathsf F} \le x \le
c_2\|\mathbf{A}\|_{\mathsf F}$, $x > 0$, for a measurable class `C`, the run of the scaling, the
four stages and the scaling back ends in a Schur output with its regularized matrix except with
probability $\varphi_R + \varphi_C$. The runs are glued after the regularizer (by the class) and
after the scaling back (by `NLAlib.Schur.schurPipeline_tail_pwrites`). -/
theorem schurPipeline_pos_pwrites_regularizedSchur [Has ScalarOp O] {Mch : Machine ℝ}
    {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (h1 : Mch.lit 1 = 1) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {Reg Red Core : Stmt O Q} {n k F T L : ℕ} {c₁ c₂ δR φR εHU εHT εCU εCT φC : ℝ}
    {qR qC : List ℝ} {C C' : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop}
    (hReg : RandomRegularizerContract law δR φR C (n + 1) (2 / c₁) qR Reg I)
    (hRed : HessenbergReducerContract εHU εHT (n + 1) Red I)
    (hCore : RandomSchurCoreContract law εCU εCT φC C' k F T (n + 1) (4 / c₁) qC Core I)
    (hCC' : ∀ (A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), C A →
      IsPerturbedUnitarySimilarBy V A H (εHT * (2 / c₁ + δR)) → C' H)
    (hCm : MeasurableSet {X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ | C X})
    (hc₁ : 0 < c₁) (hu0 : 0 ≤ u) (hu : 8 * ((n : ℝ) + 1) * u ≤ 1 / 4) (hδR : δR ≤ 1 / c₁)
    (hεHT0 : 0 ≤ εHT) (hεHT : εHT ≤ 1 / 8) (hεHU : 0 ≤ εHU) (hεCU : 0 ≤ εCU)
    (hεU : (1 + εHU) * (1 + εCU) - 1 ≤ 1 / 16) (hφR : 0 ≤ φR) (hφC : 0 ≤ φC)
    {a p uo f : ℕ × ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} :
    PWrites law I ((Stmt.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨6, .const 0⟩]).seq
        ((Stmt.call (Has.inj ScalarOp.div) [] [⟨6, .const 0⟩, ⟨5, .const 0⟩] [⟨6, .const 0⟩]).seq
          ((Stmt.loop (.const 2 * (.var 0 * .var 0)) (.call (Has.inj ScalarOp.mul) []
            [⟨0, .var 6 + .var 11⟩, ⟨6, .const 0⟩] [⟨0, .var 6 + .var 11⟩])).seq
          ((Stmt.frame [.var 0, .var 1] [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩] Reg).seq
            ((Stmt.frame [.var 0] [⟨3, .var 9⟩]
              (PairMatrix.identity (Op := O) (Tst := Q))).seq
            ((Stmt.frame [.var 0] [⟨0, .var 6⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩]
              Red).seq
            ((Stmt.frame [.var 0, .var 2, .var 3, .var 4, .var 5]
              [⟨0, .var 6⟩, ⟨1, .var 7 + .var 1⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩,
                ⟨4, .var 10⟩] Core).seq (.loop (.const 2 * (.var 0 * .var 0))
              (.call (Has.inj ScalarOp.mul) [] [⟨0, .var 6 + .var 11⟩, ⟨5, .const 0⟩]
                [⟨0, .var 6 + .var 11⟩])))))))))
      (schurPipelineEnv n qR.length qC.length k F T a p uo f L)
      (schurFp n a uo f ⊔ Store.inBlock (L + 1) 0 1)
      (fun m => SchurPipelineMem n (qR ++ qC) a p uo f L m ∧ HoldsMatrix a A m.store ∧
        ∃ x : ℝ, m.store.get L 0 = some x ∧ 0 < x ∧ c₁ * frobNorm A ≤ x ∧
          x ≤ c₂ * frobNorm A)
      (RegularizedSchurOutput C a uo f A c₁ c₂
        (c₂ * √((n : ℝ) + 1) * δR + 3 * √((n : ℝ) + 1) * u)
        (schurPipelineEX n c₁ c₂ u εHT εCT ((1 + εHU) * (1 + εCU) - 1))
        (2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2)) (φR + φC) := by
  have hu1 : u ≤ 1 := by
    have : (8 : ℝ) * 1 * u ≤ 8 * ((n : ℝ) + 1) * u :=
      mul_le_mul_of_nonneg_right (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith) hu0
    linarith
  have hu3 : u ≤ 1 / 3 := by
    have : (8 : ℝ) * 1 * u ≤ 8 * ((n : ℝ) + 1) * u :=
      mul_le_mul_of_nonneg_right (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith) hu0
    linarith
  have hε0 : 0 ≤ (1 + εHU) * (1 + εCU) - 1 := by nlinarith
  have hFa : Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ≤ schurFp n a uo f :=
    fun _ _ h => Or.inl (Or.inl h)
  set Mid₁ := SchurScaledMem n (qR ++ qC) a p uo f L c₁ c₂ u A with hMid₁
  set Mid₂ := SchurRegularizedMem C n (qR ++ qC) a p uo f L c₁ c₂ u δR A with hMid₂
  -- the scaling
  have hscale : ∀ (m : Mem ℝ) (τ : Tape ℝ), (SchurPipelineMem n (qR ++ qC) a p uo f L m ∧
      HoldsMatrix a A m.store ∧ ∃ x : ℝ, m.store.get L 0 = some x ∧ 0 < x ∧
        c₁ * frobNorm A ≤ x ∧ x ≤ c₂ * frobNorm A) →
      Writes .total I τ ((Stmt.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨6, .const 0⟩]).seq
        ((Stmt.call (Has.inj ScalarOp.div) [] [⟨6, .const 0⟩, ⟨5, .const 0⟩]
          [⟨6, .const 0⟩]).seq (.loop (.const 2 * (.var 0 * .var 0))
            (.call (Has.inj ScalarOp.mul) [] [⟨0, .var 6 + .var 11⟩, ⟨6, .const 0⟩]
              [⟨0, .var 6 + .var 11⟩]))))
        (schurPipelineEnv n qR.length qC.length k F T a p uo f L)
        (Store.inBlock (L + 1) 0 1 ⊔ Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) Mid₁ m := by
    rintro m τ ⟨hm, hA, x, hx, hx0, hxl, hxu⟩
    exact (schurPipeline_scale_writes hS hM h1 hu1 hm hA hx hx0).mono le_rfl
      fun m' _ ⟨hm', hx', A₁, hA₁, hn⟩ => ⟨hm', x, hx', hx0, hxl, hxu, A₁, hA₁, hn⟩
  have hreg := schurPipeline_regularizer_pwrites (k := k) (F := F) (T := T) (L := L) (a := a)
    (p := p) (uo := uo) (f := f) (A := A) (qC := qC) (u := u) (c₂ := c₂) hI hloc hReg hCm hc₁ hu3
  -- the tail
  have htail := schurPipeline_tail_pwrites (Mid₂ := Mid₂)
    (Post := RegularizedSchurOutput C a uo f A c₁ c₂
      (c₂ * √((n : ℝ) + 1) * δR + 3 * √((n : ℝ) + 1) * u)
      (schurPipelineEX n c₁ c₂ u εHT εCT ((1 + εHU) * (1 + εCU) - 1))
      (2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2))
    hS hM h1 hI hloc hRed hCore hCC' hc₁ hδR hεHT0 hεHT hεCU hφC
    (fun m hm => by
      obtain ⟨hm, x, hx, hx0, hxl, hxu, A₁, A₂, hn, hA₂, hA₂n, hC⟩ := hm
      exact ⟨hm, x, A₁, A₂, hx, hx0, hA₂,
        specNorm_le_two_div_of_scaled hc₁ hx0 hxl hu3 hn, hA₂n, hC⟩)
    (fun m₂ m'' x' A₂' hm₂ hx' hA₂' _ hT => by
      obtain ⟨_, x, hx, hx0, hxl, hxu, A₁, A₂, hn, hA₂, hA₂n, hC⟩ := hm₂
      obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
      obtain rfl : A₂' = A₂ := hA₂'.eq_storedMatrix.trans hA₂.eq_storedMatrix.symm
      exact regularizedSchurOutput_of_tail hu0 hu hc₁ hx0 hxl hxu hδR hεHT0 hεHT hε0 hεU hn
        hA₂n hC hT)
  refine PWrites.congr_eval (eval_seq_seq_seq_assoc _ _ _ _ _) ?_
  refine (PWrites.seq hI hloc (φ₂ := φR + φC) (by linarith) (PWrites.of_writes le_rfl hscale)
    (PWrites.seq hI hloc hφC hreg htail)).mono (fun _ h => h)
    (sup_le (sup_le le_sup_right (fun _ _ h => Or.inl (Or.inl (Or.inl h))))
      (sup_le (fun _ _ h => Or.inl (Or.inl (Or.inl h))) le_sup_left))
    (fun _ h => h) (by simp)

/-- **The generic composition theorem with the regularized matrix exposed**, in the form of a
probabilistic step (`NLAlib.Ops.PWrites`): on a scalar machine with the standard model at
$\boldsymbol{u}$, $8(n + 1)\boldsymbol{u} \le 1/4$, index literals, exact natural literals up to
$n + 1$ and exact comparisons, a measurable interpretation reading the tape only in its windows,
let the norm estimate have the constants $(c_1, c_2)$, $c_1 > 0$, the regularizer map into the class
`C` with the error $\delta_R \le 1/c_1$ and the failure $\varphi_R \ge 0$, the reducer have the
errors $(\varepsilon_{H,U}, \varepsilon_{H,T})$, $0 \le \varepsilon_{H,T} \le 1/8$, the core from
the class `C'` the errors $(\varepsilon_{C,U}, \varepsilon_{C,T})$ and the failure
$\varphi_C \ge 0$, with $(1 + \varepsilon_{H,U})(1 + \varepsilon_{C,U}) - 1 \le 1/16$, and the
reducer carry `C` into `C'`. Then from every input of the pipeline the run stores, except with
probability
$\varphi_R + \varphi_C$, a Schur output with its regularized matrix $\mathbf{X}$
(`NLAlib.Schur.RegularizedSchurOutput`): $\|\mathbf{A} - \mathbf{X}\|_2 \le (c_2\sqrt{n + 1}\,
\delta_R + 3\sqrt{n + 1}\,\boldsymbol{u})\|\mathbf{A}\|_2$, the error against $\mathbf{X}$
`NLAlib.Schur.schurPipelineEX` at $\varepsilon = (1 + \varepsilon_{H,U})(1 + \varepsilon_{C,U}) -
1$, $e_U = 2\varepsilon + \varepsilon^2$, and $s^{-1}\mathbf{X}$ in `C` for the norm estimate $s$
unless $\mathbf{A} = 0$. No printed source. -/
theorem schurPipelineWith_pwrites_regularizedSchur [Has ScalarOp O] [Has IndexOp O]
    [Has CmpTst Q] {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {Nm Reg Red Core : Stmt O Q} {k F T : ℕ}
    {c₁ c₂ δR φR εHU εHT εCU εCT φC : ℝ} {qR qC : List ℝ}
    {C C' : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop}
    (hNm : FrobNormEstimateContract c₁ c₂ (n + 1) Nm I)
    (hReg : RandomRegularizerContract law δR φR C (n + 1) (2 / c₁) qR Reg I)
    (hRed : HessenbergReducerContract εHU εHT (n + 1) Red I)
    (hCore : RandomSchurCoreContract law εCU εCT φC C' k F T (n + 1) (4 / c₁) qC Core I)
    (hCC' : ∀ (A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), C A →
      IsPerturbedUnitarySimilarBy V A H (εHT * (2 / c₁ + δR)) → C' H)
    (hCm : MeasurableSet {X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ | C X})
    (hc₁ : 0 < c₁) (hu0 : 0 ≤ u) (hu : 8 * ((n : ℝ) + 1) * u ≤ 1 / 4)
    (hδR : δR ≤ 1 / c₁) (hεHT0 : 0 ≤ εHT) (hεHT : εHT ≤ 1 / 8) (hεHU : 0 ≤ εHU)
    (hεCU : 0 ≤ εCU) (hεU : (1 + εHU) * (1 + εCU) - 1 ≤ 1 / 16) (hφR : 0 ≤ φR) (hφC : 0 ≤ φC)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p uo f : ℕ × ℕ} :
    PWrites law I (schurPipelineWith Nm Reg Red Core)
      (Env.frame [n + 1, qR.length, qC.length, k, F, T] [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurPipelineInput (qR ++ qC) a p uo f A)
      (RegularizedSchurOutput C a uo f A c₁ c₂
        (c₂ * √((n : ℝ) + 1) * δR + 3 * √((n : ℝ) + 1) * u)
        (schurPipelineEX n c₁ c₂ u εHT εCT ((1 + εHU) * (1 + εCU) - 1))
        (2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2)) (φR + φC) := by
  have h1 : Mch.lit 1 = 1 := by simpa using hNat 1 (by omega)
  have hε0 : 0 ≤ (1 + εHU) * (1 + εCU) - 1 := by nlinarith
  have heU : 0 ≤ 2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2 := by
    positivity
  set Out := RegularizedSchurOutput C a uo f A c₁ c₂
    (c₂ * √((n : ℝ) + 1) * δR + 3 * √((n : ℝ) + 1) * u)
    (schurPipelineEX n c₁ c₂ u εHT εCT ((1 + εHU) * (1 + εCU) - 1))
    (2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2) with hOut
  change PWrites law I (Stmt.allocs [.const 1, .const 1] _) _ _ _ _ _
  refine PWrites.allocs (ns := [1, 1]) rfl
    (Pre₁ := fun L m => SchurPipelineMem n (qR ++ qC) a p uo f L m ∧ HoldsMatrix a A m.store)
    (fun m s₁ hm hlen hlens hBelow => SchurPipelineInput.mem_of_alloc hm hlen hlens hBelow)
    (fun m hm s s' q hBelow hout => ?_) fun L => ?_
  · have hlt : ∀ z ∈ [a, p, uo, f], z.1 < m.store.length := hm.1
    have ha := hlt a (by simp)
    have hu := hlt uo (by simp)
    have hf := hlt f (by simp)
    obtain ⟨hf0, U, T', X, hT, hU, hTu, ho, hr, hx, hc⟩ := hout
    exact ⟨by rw [← hf0]; exact (hBelow f.1 hf).2 f.2, U, T', X, hT.of_below hBelow ha,
      hU.of_below hBelow hu, hTu, ho, hr, hx, hc⟩
  change PWrites law I _ (schurPipelineEnv n qR.length qC.length k F T a p uo f L) _ _ _ _
  have hFL : Store.inBlock L 0 1 ≤ schurFp n a uo f ⊔ Fp.above L :=
    fun _ _ h => Or.inr (h.1 ▸ le_rfl)
  have hFL' : Store.inBlock (L + 1) 0 1 ≤ schurFp n a uo f ⊔ Fp.above L :=
    fun b _ h => Or.inr (show L ≤ b by rw [h.1]; omega)
  set MidN : Mem ℝ → Prop := fun m => SchurPipelineMem n (qR ++ qC) a p uo f L m ∧
    HoldsMatrix a A m.store ∧ ∃ x : ℝ, m.store.get L 0 = some x ∧ c₁ * frobNorm A ≤ x ∧
      x ≤ c₂ * frobNorm A with hMidN
  have hnm : ∀ m τ, SchurPipelineMem n (qR ++ qC) a p uo f L m ∧ HoldsMatrix a A m.store →
      Writes .total I τ (Stmt.frame [.var 0] [⟨0, .var 6⟩, ⟨5, .const 0⟩] Nm)
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
  have hthen := (schurPipeline_pos_pwrites_regularizedSchur (k := k) (F := F) (T := T) (L := L)
    (a := a) (p := p) (uo := uo) (f := f) (A := A) hS hM h1 hI hloc hReg hRed hCore hCC' hCm hc₁
    hu0 hu hδR hεHT0 hεHT hεHU hεCU hεU hφR hφC).mono
    (Pre' := fun m => MidN m ∧ I.testAt (Has.inj CmpTst.isPos) [] [⟨5, .const 0⟩]
        (schurPipelineEnv n qR.length qC.length k F T a p uo f L) m = some true)
    (fun m ⟨⟨hm, hA', x, hx, hxl, hxu⟩, ht⟩ => by
      rw [Interp.testAt_eq rfl rfl, hC.test_isPos (x := (L, 0)) hx] at ht
      have hx0 : 0 < x := by simpa using ht
      exact ⟨hm, hA', x, hx, hx0, hxl, hxu⟩)
    (sup_le le_sup_left hFL') (fun _ h => h) le_rfl
  have helse := PWrites.of_writes (law := law) (φ := 0) le_rfl
    (Pre := fun m => MidN m ∧ I.testAt (Has.inj CmpTst.isPos) [] [⟨5, .const 0⟩]
        (schurPipelineEnv n qR.length qC.length k F T a p uo f L) m = some false)
    (F := schurFp n a uo f ⊔ Fp.above L) (Post := Out)
    fun m τ ⟨⟨hm, hA', x, hx, hxl, hxu⟩, ht⟩ => by
      rw [Interp.testAt_eq rfl rfl, hC.test_isPos (x := (L, 0)) hx] at ht
      have hx0 : x ≤ 0 := by simpa using ht
      have hF : frobNorm A = 0 :=
        le_antisymm (by nlinarith [frobNorm_nonneg A]) (frobNorm_nonneg A)
      obtain rfl := frobNorm_eq_zero_iff.mp hF
      refine (schurPipeline_zero_writes (nr := qR.length) (nq := qC.length) (k := k) (F := F)
        (T := T) (eA := 0) hS hM hL h1 hm hA' heU).mono le_sup_left ?_
      rintro m' - ⟨hf0, U, T', hT, hU, hTu, hr, ho⟩
      refine ⟨hf0, U, T', 0, hT, hU, hTu, ho, by simp, ?_, Or.inl rfl⟩
      simpa using hr
  refine (PWrites.seq hI hloc (φ₂ := max (φR + φC) 0) (le_max_right _ _)
    (PWrites.of_writes le_rfl fun m τ hm => hnm m τ hm)
    (PWrites.ite hI htest hthen helse)).mono (fun _ h => h) (sup_le hFL le_rfl) (fun _ h => h)
    (by rw [max_eq_left (by linarith)]; linarith)

/-- **The generic composition theorem with the regularized matrix exposed**: on a scalar machine
with the standard model at $\boldsymbol{u}$, $8(n + 1)\boldsymbol{u} \le 1/4$, index literals,
exact natural literals up to $n + 1$ and exact comparisons, a measurable interpretation reading the
tape only in its windows, let the norm estimate have the constants $(c_1, c_2)$, $c_1 > 0$, the
regularizer map into `C` with the error $\delta_R \le 1/c_1$ and the failure $\varphi_R \ge 0$,
the reducer have the errors $(\varepsilon_{H,U}, \varepsilon_{H,T})$,
$0 \le \varepsilon_{H,T} \le 1/8$, the core from `C'` the errors
$(\varepsilon_{C,U}, \varepsilon_{C,T})$ and the failure $\varphi_C \ge 0$, with
$(1 + \varepsilon_{H,U})(1 + \varepsilon_{C,U}) - 1 \le 1/16$, and the reducer carry `C` into
`C'`. Then from a memory holding the input of the pipeline, under a random tape with the
stream laws,
$$\mathbb{P}\bigl[\mathsf{schurPipelineWith}(\mathbf{A}) \text{ fails, writes outside }
  \mathbf{A}, \widehat{\mathbf{U}} \text{ and the flag, or stores no Schur output with a
  regularized } \mathbf{X}\bigr] \le \varphi_R + \varphi_C\,,$$
the errors those of `NLAlib.Schur.schurPipelineWith_pwrites_regularizedSchur`. No printed
source. -/
theorem schurPipelineWith_measureReal_not_regularizedSchur_le [Has ScalarOp O] [Has IndexOp O]
    [Has CmpTst Q] {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {Nm Reg Red Core : Stmt O Q} {k F T : ℕ}
    {c₁ c₂ δR φR εHU εHT εCU εCT φC : ℝ} {qR qC : List ℝ}
    {C C' : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop}
    (hNm : FrobNormEstimateContract c₁ c₂ (n + 1) Nm I)
    (hReg : RandomRegularizerContract law δR φR C (n + 1) (2 / c₁) qR Reg I)
    (hRed : HessenbergReducerContract εHU εHT (n + 1) Red I)
    (hCore : RandomSchurCoreContract law εCU εCT φC C' k F T (n + 1) (4 / c₁) qC Core I)
    (hCC' : ∀ (A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), C A →
      IsPerturbedUnitarySimilarBy V A H (εHT * (2 / c₁ + δR)) → C' H)
    (hCm : MeasurableSet {X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ | C X})
    (hc₁ : 0 < c₁) (hu0 : 0 ≤ u) (hu : 8 * ((n : ℝ) + 1) * u ≤ 1 / 4)
    (hδR : δR ≤ 1 / c₁) (hεHT0 : 0 ≤ εHT) (hεHT : εHT ≤ 1 / 8) (hεHU : 0 ≤ εHU)
    (hεCU : 0 ≤ εCU) (hεU : (1 + εHU) * (1 + εCU) - 1 ≤ 1 / 16) (hφR : 0 ≤ φR) (hφC : 0 ≤ φC)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (qR ++ qC) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (schurPipelineWith Nm Reg Red Core)
      (Env.frame [n + 1, qR.length, qC.length, k, F, T] [a, p, a, uo, f]) (schurFp n a uo f)
      (RegularizedSchurOutput C a uo f A c₁ c₂
        (c₂ * √((n : ℝ) + 1) * δR + 3 * √((n : ℝ) + 1) * u)
        (schurPipelineEX n c₁ c₂ u εHT εCT ((1 + εHU) * (1 + εCU) - 1))
        (2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2)) μ} ≤ φR + φC :=
  (schurPipelineWith_pwrites_regularizedSchur hS hM hL hNat hC hI hloc hNm hReg hRed hCore hCC'
    hCm hc₁ hu0 hu hδR hεHT0 hεHT hεHU hεCU hεU hφR hφC).measureReal_not_writes_le hin hξ

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

/-- **The static count of the pipeline** with its structural instructions, at zero offsets of
the matrix, the parameter words, the accumulator and the flag, is at most the sum of the stages'
instrumented counts, each at the offsets the pipeline passes to it (zero, and $n_r$ for the core's
parameter words), plus $120(N + 1)^2$ for the glue (the scaling loops, the identity, the branch
and the frames). -/
theorem size_stmtCost_schurPipelineWith_le [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]
    (Nm Reg Red Core : Stmt O Q) (N nr nq k F T : ℕ) :
    Count.size (stmtCost (schurPipelineWith Nm Reg Red Core).instrument
        [N, nr, nq, k, F, T, 0, 0, 0, 0, 0]) ≤
      Count.size (stmtCost Nm.instrument [N, 0, 0]) +
        Count.size (stmtCost Reg.instrument [N, nr, 0, 0, 0]) +
        Count.size (stmtCost Red.instrument [N, 0, 0, 0, 0]) +
        Count.size (stmtCost Core.instrument [N, nq, k, F, T, 0, nr, 0, 0, 0, 0]) +
        120 * (N + 1) ^ 2 := by
  have hsup : ∀ x y : Count (O ⊕ Bookkeeping) Q,
      Count.size (x ⊔ y) = Count.size x + Count.size y - Count.size (x ⊓ y) := fun x y => by
    rw [← size_sup_add_size_inf]; omega
  simp only [schurPipelineWith, Stmt.alloc, Stmt.instrument, PairMatrix.identityRoutine,
    PairMatrix.identity, tally,
    indexBookkeeping, operandBookkeeping, IExp.bookkeeping, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, stmtCost, useCost, testCost,
    IExp.evalList, IExp.eval, List.map_cons, List.map_nil, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.map_some, Option.getD_some, Finset.sum_const,
    Finset.card_range, zero_add, add_zero, map_add, map_nsmul, hsup, Count.one, Count.test,
    size_single, smul_eq_mul]
  have hsq : (N + 1) ^ 2 = N * N + 2 * N + 1 := by ring
  rw [hsq]
  generalize N * N = M
  simp only [Nat.reduceAdd]
  omega

end NLAlib.Schur
