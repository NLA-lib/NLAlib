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
  simp only [schurPipelineWith, Stmt.alloc, Stmt.instrument, PairMatrix.identity, tally,
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
