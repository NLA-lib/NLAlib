/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Certification
public import NLAlib.Eigensolvers.Schur.DenseEig

/-!
# The dense eigensolver as a canonical certificate

## Main definitions

* `NLAlib.Schur.eigSolverRoutine`, `NLAlib.Schur.eigSolverSpec`: the routine and its every-tape
  specification.
* `NLAlib.Schur.eigSolverInputs`, `NLAlib.Schur.eigSolverProgram`, `NLAlib.Schur.eigSolverProblem`,
  `NLAlib.Schur.eigSolverWork`, `NLAlib.Schur.eigSolverSpecification`,
  `NLAlib.Schur.eigSolverAlgorithm`: the eigensolver's generic certificate.
* `NLAlib.Schur.denseEigProblem`, `NLAlib.Schur.denseEigWork`, `NLAlib.Schur.denseEigAlgorithm`:
  the dense eigensolver's.

## Main results

* `NLAlib.Schur.denseEigRoutine_meets`: the judgment of the routine, on every tape.
* `NLAlib.Schur.denseEig_algorithm_measureReal_not_accepts_le`: the dense eigendecomposition
  theorem on one counted run.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops SmallEig ShiftedQR MeasureTheory ProbabilityTheory
open scoped Matrix

/-! ### Completion with the stored pair

The dense Schur solver at two tolerances runs to completion on any scalar machine and stores a
pair, so that the eigenvector stage runs after it (`NLAlib.Schur.denseEigRoutine_meets`). -/

section CompletesPair

open Ops SmallEig ShiftedQR MeasureTheory ProbabilityTheory
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O]

/-- The positive branch of the pipeline runs to completion on any scalar machine with completing
stages, and stores a pair. -/
theorem schurPipeline_pos_completes_pair {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (h0 : Mch.lit 0 = 0) (h1 : Mch.lit 1 = 1)
    {Reg Red Core : Stmt O Q} {n k F T L : ℕ} {qR qC : List ℝ}
    (hReg : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {a q : ℕ × ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      HoldsMatrix a A μ.store → μ.store.readBlock q.1 q.2 qR.length = some qR → μ.Live [a, q] →
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock q.1 q.2 qR.length) →
      Writes .total I τ Reg (Env.frame [n + 1, qR.length] [a, q, a])
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (fun μ' => ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A' μ'.store) μ)
    (hRed : CompletingReducer (n + 1) Red I) (hCore : CompletingSchurCore k F T (n + 1) qC Core I)
    {a p uo f : ℕ × ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {m : Mem ℝ} (hm : SchurPipelineMem n (qR ++ qC) a p uo f L m)
    (hA : HoldsMatrix a A m.store) {x : ℝ} (hx : m.store.get L 0 = some x) (τ : Tape ℝ) :
    Writes .total I τ ((Stmt.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨6, .const 0⟩]).seq
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
      (fun m' => ∃ U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsSchurPair a uo U T m'.store)
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
  refine Writes.congr_eval (eval_seq_seq_seq_assoc _ _ _ _ _ _ _) ?_
  refine (schurPipeline_scale_completes hS hm hA hx).seq_le
    (sup_le (fun _ _ h => Or.inr h) hFa) fun m₁ hfr₁ h₁ => ?_
  obtain ⟨hm₁, hx₁, A₁, hA₁⟩ := h₁
  refine (hReg A₁ hA₁ (Store.readBlock_append_left hm₁.2.2.2.2.2.2.2.2.2)
    (hm₁.live_of_subset (by simp)) (h1'.mono le_rfl (Fp.inBlock_le_inBlock le_rfl
      (by simp)))).frame_seq_le rfl rfl (hm₁.live_of_subset (by simp)) hFa
    fun m₂ hfr₂ h₂ => ?_
  obtain ⟨A₂, hA₂⟩ := h₂
  have hm₂ := hm₁.of_eqOff hfr₂ (hdG.mono hFa le_rfl)
  refine (identity_writes_holdsMatrix_one_of_lit (N := n + 1) hS h0 h1 hm₂.room_uo).frame_seq_le
    rfl rfl (hm₂.live_of_subset (by simp)) hFu fun m₃ hfr₃ hU => ?_
  have hm₃ := hm₂.of_eqOff hfr₃ (hdG.mono hFu le_rfl)
  refine (hRed A₂ 1 le_rfl ⟨hA₂.of_eqOff hfr₃ h2.symm, hU⟩ (hm₃.live_of_subset (by simp))
    h2).frame_seq_le rfl rfl (hm₃.live_of_subset (by simp)) (sup_le hFa hFu)
    fun m₄ hfr₄ h₄ => ?_
  obtain ⟨U₁, H, hp₄⟩ := h₄
  have hm₄ := hm₃.of_eqOff hfr₄ (hdG.mono (sup_le hFa hFu) le_rfl)
  obtain ⟨hlen₄, -, -, -, -, -, -, -, -, hq₄⟩ := id hm₄
  refine (hCore H U₁ le_rfl hp₄ (Store.readBlock_append_right hq₄) (fun z hz => ?_)
    (by have := hm₄.room_f; omega) (apart_tail hap)).frame_seq_le rfl rfl
    (fun z hz => ?_) (fun _ _ h => Or.inl h) fun m₅ hfr₅ h₅ => ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp only [hlen₄] <;> omega
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [hlen₄] <;> omega
  obtain ⟨U₂, Tm, hT₅, hU₅⟩ := h₅
  have hm₅ := hm₄.of_eqOff hfr₅ (hdG.mono (fun _ _ h => Or.inl h) le_rfl)
  have hx₅ : m₅.store.get L 0 = some x := by
    rw [hfr₅.2 L 0 (not_schurFp_of_le ha hu hf le_rfl), hfr₄.2 L 0 (fun h => by
      rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> omega), hfr₃.2 L 0 (fun h => by obtain ⟨h, -⟩ := h; omega),
      hfr₂.2 L 0 (fun h => by obtain ⟨h, -⟩ := h; omega), hx₁]
  refine (writes_loop_mul_cell hS (N := 2 * ((n + 1) * (n + 1))) (b := a.1) (o := a.2)
    (y := (L, 0)) (r := x) rfl (fun t _ => rfl) (fun t _ => rfl)
    (hm₅.live_of_subset (by simp)) (fun t ht => ⟨_, Store.get_of_readBlock hT₅ ht 0⟩) hx₅
    (by rintro ⟨h, -⟩; omega)).mono hFa fun m₆ hfr₆ ⟨_, hmul⟩ => ?_
  obtain ⟨T', hT'⟩ := exists_holdsMatrix_of_mul hT₅ hmul
  exact ⟨U₂, T', hT', hU₅.of_eqOff hfr₆ h2⟩


/-- The zero branch of the pipeline runs to completion on any scalar machine with exact literals
$0$, $1$, and keeps the stored matrix with the identity: it stores a pair. -/
theorem schurPipeline_zero_completes_pair [Has IndexOp O] {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (h0 : Mch.lit 0 = 0) (h1 : Mch.lit 1 = 1)
    {n nr nq k F T L : ℕ} {qs : List ℝ}
    {a p uo f : ℕ × ℕ} {τ : Tape ℝ} {m : Mem ℝ} (hm : SchurPipelineMem n qs a p uo f L m)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : HoldsMatrix a A m.store) :
    Writes .total I τ (.seq (.frame [.var 0] [⟨3, .var 9⟩]
        (PairMatrix.identity (Op := O) (Tst := Q)))
        (.call (Has.inj IndexOp.lit) [.const 0] [] [⟨4, .var 10⟩]))
      (schurPipelineEnv n nr nq k F T a p uo f L) (schurFp n a uo f)
      (fun m' => ∃ U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsSchurPair a uo U T m'.store)
      m := by
  obtain ⟨-, -, -, -, -, -, -, -, hap, -⟩ := id hm
  obtain ⟨-, h2, h3, -, -, h6⟩ := apart_four hap
  refine (identity_writes_holdsMatrix_one_of_lit (N := n + 1) hS h0 h1 hm.room_uo).frame_seq_le
    rfl rfl (hm.live_of_subset (by simp)) (by simp only [schurFp]; fp_sub) fun m' hfr hU => ?_
  have hf : f.2 < m'.store.len f.1 := by have := hm.room_f; rw [hfr.len_eq]; omega
  refine (writes_indexLit hL (n := 0) rfl rfl hf).mono (by simp only [schurFp]; fp_sub)
    fun m'' hfr' _ => ⟨1, A, (hA.of_eqOff hfr h2.symm).of_eqOff hfr' h3.symm,
      hU.of_eqOff hfr' h6.symm⟩

/-- The pipeline runs to completion on any scalar machine with completing stages and stores a
pair (`NLAlib.Schur.schurPipelineWith_completes` with the pair). -/
theorem schurPipelineWith_completes_pair [Has IndexOp O] [Has CmpTst Q] {Mch : Machine ℝ}
    {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hC : IsCmp id I) {Nm Reg Red Core : Stmt O Q} {k F T : ℕ} {qR qC : List ℝ}
    (hNm : CompletingNormEstimate (n + 1) Nm I)
    (hReg : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {a q : ℕ × ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      HoldsMatrix a A μ.store → μ.store.readBlock q.1 q.2 qR.length = some qR → μ.Live [a, q] →
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock q.1 q.2 qR.length) →
      Writes .total I τ Reg (Env.frame [n + 1, qR.length] [a, q, a])
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (fun μ' => ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A' μ'.store) μ)
    (hRed : CompletingReducer (n + 1) Red I) (hCore : CompletingSchurCore k F T (n + 1) qC Core I)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (qR ++ qC) a p uo f A μ) (τ : Tape ℝ) :
    Writes .total I τ (schurPipelineWith Nm Reg Red Core)
      (Env.frame [n + 1, qR.length, qC.length, k, F, T] [a, p, a, uo, f]) (schurFp n a uo f)
      (fun m' => ∃ U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsSchurPair a uo U T m'.store)
      μ := by
  have h1 : Mch.lit 1 = 1 := by simpa using hNat 1 (by omega)
  have h0 : Mch.lit 0 = 0 := by simpa using hNat 0 (by omega)
  have hlt : ∀ z ∈ [a, p, uo, f], z.1 < μ.store.length := hin.1
  change Writes .total I τ (Stmt.allocs [.const 1, .const 1] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [1, 1]) rfl
    (fun hBelow ⟨U, T, hT, hU⟩ => ⟨U, T, hT.of_below hBelow (hlt a (by simp)),
      hU.of_below hBelow (hlt uo (by simp))⟩) ?_
  intro s₁ hlen hlens hBelow
  obtain ⟨hm, hA⟩ := hin.mem_of_alloc (q := μ.pos) hlen hlens hBelow
  set L := μ.store.length
  change Writes .total I τ _ (schurPipelineEnv n qR.length qC.length k F T a p uo f L) _ _ _
  obtain ⟨-, ha, hp, hu, hf, -, hLl, -⟩ := id hm
  have hlive : (⟨s₁, μ.pos⟩ : Mem ℝ).Live [a, (L, 0)] := hm.live_of_subset (by simp)
  have hFL : Store.inBlock L 0 1 ≤ schurFp n a uo f ⊔ Fp.above L :=
    fun _ _ h => Or.inr (h.1 ▸ le_rfl)
  refine (hNm A le_rfl hA hlive (show 0 + 1 ≤ s₁.len L by simp at hLl ⊢; omega)
    (show a.1 ≠ L by omega)).frame_seq_le rfl rfl hlive hFL fun m hfr ⟨x, hx⟩ => ?_
  have hm' := hm.of_eqOff hfr (Fp.disj_inBlock_of_ne (by omega))
  have hA' := hA.of_eqOff hfr (Fp.disj_inBlock_of_ne (by omega))
  refine writes_ite rfl rfl (hC.test_isPos (x := (L, 0)) (d := []) hx) ?_
  by_cases hx0 : 0 < x
  · simp only [id, hx0, decide_true, if_true]
    exact (schurPipeline_pos_completes_pair hS h0 h1 hReg hRed hCore hm' hA' hx τ).mono
      (sup_le le_sup_left (fun b _ h => Or.inr (show L ≤ b by rw [h.1]; omega))) fun _ _ h => h
  · simp only [id, hx0, decide_false, Bool.false_eq_true, if_false]
    exact (schurPipeline_zero_completes_pair hS hL h0 h1 hm' hA').mono le_sup_left
      fun _ _ h => h

/-- The dense Schur solver at two tolerances runs to completion on every tape and on any scalar
machine, and stores a pair (`NLAlib.Schur.denseSchur_completes` with the pair). -/
theorem denseSchurAt_completes_pair [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
    [Has CmpTst Q] [Has IdxTst Q] {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δR δC φ : ℝ}
    {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (denseSchurParamsAt n δR δC φ) a p uo f A μ) (τ : Tape ℝ) :
    Writes .total I τ (denseSchur (O := O) (Q := Q) sG)
      (Env.frame (denseSchurDimsAt n δR δC φ) [a, p, a, uo, f]) (schurFp n a uo f)
      (fun m' => ∃ U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsSchurPair a uo U T m'.store)
      μ := by
  have hReg : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {a q : ℕ × ℕ}
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), HoldsMatrix a A μ.store →
      μ.store.readBlock q.1 q.2 (denseSchurRegParams n δR φ).length =
        some (denseSchurRegParams n δR φ) → μ.Live [a, q] →
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock q.1 q.2 (denseSchurRegParams n δR φ).length) →
      Writes .total I τ (ginibrePerturb (O := O) (Q := Q) sG)
        (Env.frame [n + 1, (denseSchurRegParams n δR φ).length] [a, q, a])
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (fun μ' => ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A' μ'.store) μ :=
    fun A hA hq hl _ => (SmallEig.ginibrePerturb_writes_word hS hL hSmp hl hA
      (Store.get_of_readBlock hq (j := 0) (by simp [denseSchurRegParams,
        SmallEig.length_smallEigParams]) 0)).mono le_rfl fun _ _ h => ⟨_, h.2⟩
  have hCore : CompletingSchurCore (denseSchurDegree n δR φ) (denseSchurCapAt n δR δC φ)
      (denseSchurLeafCapAt n δR δC φ) (n + 1)
      (denseSchurThresholdAt n δR δC φ ::
        (denseSchurShQRParamsAt n δR δC φ ++ denseSchurLeafParamsAt n δR δC φ))
      (roundedShQRSchur (O := O) (Q := Q) sG) I := by
    rw [← shqrSchurParamsAt_eq]
    have h12 := length_smallEigParams (denseSchurDegree n δR φ) (4 * 8)
      (forwardBackwardError (denseSchurDegree n δR φ) (4 * 8)
        (shqrSmallEigAccuracy n (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8
          (denseSchurDelta n δC)))
      (shqrSmallEigFailure n (2 * denseSchurB n δR φ) (denseSchurΓ n δR φ / 2) 8
        (denseSchurDelta n δC) (φ / 2)) ginibreGapTail ginibreConditionTail
    intro n' a p uo f tape μ H U hn hHU hp hl hf ha
    exact roundedShQRSchurWith_completing (B := 2 * denseSchurB n δR φ)
      (Γ := denseSchurΓ n δR φ / 2) (S := 8) (δ := denseSchurDelta n δC) (φ := φ / 2)
      hS hL hNat hQ hC hDisk rfl
      (smallEigProg_completes (kmax := min (denseSchurDegree n δR φ) (n + 1)) hS hL
        (hNat.mono (min_le_right _ _)) hC hQ hSmp hDisk (smallEigCaps_smallEigParams _ _ _ _ _ _)
        h12.ge) h12 H U hn hHU hp hl hf ha
  exact schurPipelineWith_completes_pair hS hL hNat hC (frobNormStage_completing hS (n + 1)) hReg
    (hessenbergReduceQ_completing hS hC hQ hL hNat (by omega)) hCore hin τ

/-- **The eigensolver runs to completion** on any scalar machine with index literals and exact
comparisons, given a Schur solver that completes storing a pair and an eigenvector stage that
completes: it writes only $\mathbf{A}$, $\widehat{\mathbf{U}}$, $\widehat{\mathbf{V}}$ and the
flag. No rounding model is needed. -/
theorem eigSolverWith_completes_of_pair [Has IndexOp O] [Has CmpTst Q] {Mch : Machine ℝ}
    {I : Interp O Q ℝ} {n : ℕ} (hL : IsIndexLit Mch I) (hC : IsCmp id I)
    {Solve Ev : Stmt O Q} {nr nq k F T : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {a p pe uo v f : ℕ × ℕ} {qs qe : List ℝ} {μ : Mem ℝ}
    (hSolve : ∀ {τ : Tape ℝ} {μ : Mem ℝ}, SchurPipelineInput qs a p uo f A μ →
      Writes .total I τ Solve (Env.frame [n + 1, nr, nq, k, F, T] [a, p, a, uo, f])
        (schurFp n a uo f)
        (fun m' => ∃ U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          HoldsSchurPair a uo U T m'.store) μ)
    (hEv : CompletingEigenvectorStage (n + 1) qe Ev I)
    (hin : EigSolverInput qs qe a p pe uo v f A μ) (τ : Tape ℝ) :
    Writes .total I τ (eigSolverWith Solve Ev)
      (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (fun _ => True) μ := by
  obtain ⟨hpin, hlv, hroom, hap, hqe⟩ := hin
  obtain ⟨hl4, hroom4, hap4, hA, hP⟩ := hpin
  have hlt : ∀ z ∈ [a, p, uo, f, pe, v], z.1 < μ.store.length := fun z hz => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hl4 _ (by simp)
    · exact hl4 _ (by simp)
    · exact hl4 _ (by simp)
    · exact hl4 _ (by simp)
    · exact hlv _ (by simp)
    · exact hlv _ (by simp)
  change Writes .total I τ (Stmt.allocs [.const 1] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [1]) rfl (fun _ _ => trivial) ?_
  intro s₁ hlen hlens hBelow
  set L := μ.store.length with hLdef
  have hLs : s₁.length = L + 1 := by simpa using hlen
  have hL1 : s₁.len L = 1 := by simpa using hlens 0 (by simp)
  have hroomeq : ∀ {zs : List (ℕ × ℕ)} {ls : List ℕ}, (∀ z ∈ zs, z.1 < L) →
      (⟨s₁, μ.pos⟩ : Mem ℝ).Room zs ls = μ.Room zs ls :=
    fun hz => Mem.room_eq_of_below (μ' := ⟨s₁, μ.pos⟩) hBelow hz
  have hpin' : SchurPipelineInput qs a p uo f A ⟨s₁, μ.pos⟩ := by
    refine ⟨fun z hz => ?_, ?_, hap4, hA.of_below hBelow (hlt a (by simp)),
      hBelow.keep (Store.readsOnly_readBlock _ _ _ _) (fun _ _ h => h.1 ▸ hlt p (by simp)) hP⟩
    · have := hl4 z hz; simp only at this ⊢; omega
    · rw [hroomeq (by intro z hz; exact hl4 z hz)]; exact hroom4
  obtain ⟨h12, h13, h14, h15, h16, h23, h24, h25, h26, h34, h35, h36, h45, h46, h56⟩ :
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock p.1 p.2 qs.length) ∧
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) ∧
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1) ∧
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock pe.1 pe.2 qe.length) ∧
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
  have hlive7 : (⟨s₁, μ.pos⟩ : Mem ℝ).Live [a, p, a, uo, f] := fun z hz => hpin'.1 z (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢; tauto)
  have hFS : schurFp n a uo f ≤ eigFp n a uo v f ⊔ Fp.above L := fun _ _ h => Or.inl (Or.inl h)
  refine (hSolve hpin').frame_seq_le rfl rfl hlive7 hFS fun m₁ hfr₁ ⟨U, T', hpair⟩ => ?_
  have hdS : ∀ {G : Fp}, Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) G →
      Fp.Disj (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) G →
      Fp.Disj (Store.inBlock f.1 f.2 1) G → Fp.Disj (schurFp n a uo f) G := fun h1 h2 h3 => by
    simp only [schurFp, Fp.disj_sup_left]; exact ⟨⟨h1, h2⟩, h3⟩
  have hqe₁ : m₁.store.readBlock pe.1 pe.2 qe.length = some qe :=
    hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hdS h15 h35 h45)
      (hBelow.keep (Store.readsOnly_readBlock _ _ _ _) (fun _ _ h => h.1 ▸ hlt pe (by simp)) hqe)
  have hlen₁ : m₁.store.length = L + 1 := hfr₁.length_eq.trans hLs
  have hlive₁ : m₁.Live [a, uo, pe, v, (L, 0)] := fun z hz => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    simp only [hlen₁]
    rcases hz with h | h | h | h | h <;> rw [h]
    · have := hlt a (by simp); omega
    · have := hlt uo (by simp); omega
    · have := hlt pe (by simp); omega
    · have := hlt v (by simp); omega
    · simp
  have hroom₁ : m₁.Room [v, (L, 0)] [2 * ((n + 1) * (n + 1)), 1] := by
    have hv : (⟨s₁, μ.pos⟩ : Mem ℝ).Room [v] [2 * ((n + 1) * (n + 1))] := by
      rw [hroomeq (fun z hz => by simp at hz; rw [hz]; exact hlt v (by simp))]
      exact ⟨hroom.2.1, trivial⟩
    refine ⟨?_, ?_, trivial⟩
    · rw [hfr₁.len_eq]; exact hv.1
    · rw [hfr₁.len_eq]; simp [hL1]
  have hap₁ : Fp.Apart [a, uo, pe, v, (L, 0)]
      [2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), qe.length, 2 * ((n + 1) * (n + 1)), 1] := by
    have hLa : ∀ z ∈ [a, uo, pe, v], ∀ l, Fp.Disj (Store.inBlock z.1 z.2 l) (Store.inBlock L 0 1) :=
      fun z hz l => Fp.disj_inBlock_of_ne (by have := hlt z (by simp at hz ⊢; tauto); omega)
    simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨h13, h15, h16, hLa a (by simp) _⟩, ⟨h35, h36, hLa uo (by simp) _⟩,
      ⟨h56, hLa pe (by simp) _⟩, hLa v (by simp) _⟩
  have hFE : Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock L 0 1 ≤
      eigFp n a uo v f ⊔ Fp.above L :=
    sup_le (fun _ _ h => Or.inl (Or.inr h)) (fun _ _ h => Or.inr (h.1 ▸ le_rfl))
  refine (hEv U T' le_rfl hpair hqe₁ hlive₁ hroom₁ hap₁).frame_seq_le rfl rfl hlive₁ hFE
    fun m₂ hfr₂ ⟨_, x, hx⟩ => ?_
  have hf₂ : f.2 < m₂.store.len f.1 := by
    have hf0 : f.2 + 1 ≤ s₁.len f.1 := hpin'.2.1.2.2.2.1
    rw [hfr₂.len_eq, hfr₁.len_eq]
    change f.2 < s₁.len f.1
    omega
  refine writes_ite rfl rfl (hC.test_isPos (x := (L, 0)) (d := []) hx) ?_
  split
  · exact (writes_indexLit hL (n := 1) rfl rfl hf₂).mono
      (fun _ _ h => Or.inl (Or.inl (Or.inr (by simpa using h)))) fun _ _ _ => trivial
  · exact (Writes.skip (P := fun _ => True) trivial).mono bot_le fun _ _ _ => trivial

end CompletesPair

/-! ### The eigensolver -/

/-- **The routine of the eigensolver** of a Schur solver `Solve` and an eigenvector stage `Ev`:
`[n, nr, nq, k, F, T, ne] (A : update 2 (n + 1)², P : read nr + nq, Pe : isolated ne) →
(U : write 2 (n + 1)², V : write 2 (n + 1)², Fl : write 1)`, the tree
`NLAlib.Schur.eigSolverWith` at the order `n + 1`. The number of draws depends on the data, so
the routine declares none. The written operands are unreported: the every-tape statement is the
footprint, and the eigendecomposition is a statement in probability
(`NLAlib.Schur.denseEig_algorithm_measureReal_not_accepts_le`). The tree has one variable for the
matrix, named in both positions of the call. -/
def eigSolverRoutine (Solve Ev : Stmt SmallEigOp Tst) : Routine SmallEigOp Tst :=
  routine% [n, nr, nq, k, F, T, ne]
      (unreported A : 2 * ((n + 1) * (n + 1)), P : nr + nq, isolated Pe : ne) →
      (A, unreported U : 2 * ((n + 1) * (n + 1)), unreported V : 2 * ((n + 1) * (n + 1)),
        unreported Fl : 1)
    draws unspecified one variable {
    run (eigSolverWith Solve Ev) [n + 1, nr, nq, k, F, T, ne] (A, P, Pe, A, U, V, Fl)
  }

/-- The input of the eigensolver at the dimensions `dims`: the words of a matrix of order `n + 1`,
the solver's words `ws` and the stage's words `es`. Nothing is claimed of the written blocks. -/
def eigSolverSpec (ws es : List ℝ) (dims : List ℕ) : Routine.Spec ℝ :=
  .terminates fun d _ X => d = dims ∧
    ∃ A : Matrix (Fin (d.headD 0 + 1)) (Fin (d.headD 0 + 1)) ℂ, X = [matrixWords A, ws, es]

/-- **The eigensolver program** of a Schur solver `Solve` and an eigenvector stage `Ev` at the
order `d 0 + 1`, the solver's dimensions `d 1`, …, `d 5` and `d 6` stage words, on the six
supplied buffers (matrix, solver words, stage words, accumulator, eigenvectors, flag): the routine
`NLAlib.Schur.eigSolverRoutine` on those buffers. -/
def eigSolverProgram (Solve Ev : Stmt SmallEigOp Tst) : Program SmallEigOp Tst 7 6 :=
  (eigSolverRoutine Solve Ev).close 7 6

/-- The program is the frame of the eigensolver at the order `d 0 + 1` on the supplied buffers. -/
theorem eigSolverProgram_eq (Solve Ev : Stmt SmallEigOp Tst) :
    eigSolverProgram Solve Ev =
      ⟨.frame [.var 0 + .const 1, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6]
        [⟨0, .var 7⟩, ⟨1, .var 8⟩, ⟨2, .var 9⟩, ⟨0, .var 7⟩, ⟨3, .var 10⟩, ⟨4, .var 11⟩,
          ⟨5, .var 12⟩]
        (eigSolverWith Solve Ev)⟩ := rfl

/-- **The inputs of the eigensolver** at the sizes `d`: the matrix of order `d 0 + 1` and the
reals $\delta, \varphi$. -/
structure EigData (d : Fin 7 → ℕ) where
  /-- The matrix. -/
  matrix : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ
  /-- The backward error. -/
  δ : ℝ
  /-- The failure probability. -/
  φ : ℝ

/-- **The admitted sizes of the eigensolver** on the machine `Mch`: the natural literals up to the
order $n + 1$ are exact and the sizes are those of some $0 < \delta \le 1$, $0 < \varphi \le 1$. -/
def EigSizes (Mch : Machine ℝ) (sizes : ℕ → ℝ → ℝ → Fin 7 → ℕ) (d : Fin 7 → ℕ) : Prop :=
  IsExactNatLit id Mch (d 0 + 1) ∧
    ∃ δ φ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < φ ∧ φ ≤ 1 ∧ sizes (d 0) δ φ = d

/-- **The admitted inputs of the eigensolver** on the machine `Mch`, for the word functions
`words` (solver) and `ewords` (stage) and the size function `sizes` of $(n, \delta, \varphi)$, at
the sizes `NLAlib.Schur.EigSizes`: every matrix of order `d 0 + 1` and all reals
$\delta, \varphi$ whose sizes are `d`. The first operand holds the words of the matrix. The reals
are in no buffer: the second and third operands hold the words computed from them, at the
`d 1 + d 2` and `d 6` cells of their ports. The accumulator, the eigenvectors and the flag are
blank. -/
noncomputable def eigSolverInputs (Mch : Machine ℝ) (words ewords : ℕ → ℝ → ℝ → List ℝ)
    (sizes : ℕ → ℝ → ℝ → Fin 7 → ℕ) (admitted : ∃ d, EigSizes Mch sizes d) :
    (eigSolverRoutine .skip .skip).Domain ℝ 7 6 where
  valid := EigSizes Mch sizes
  In := EigData
  accepts d x := sizes (d 0) x.δ x.φ = d
  slot d := ![.stored (Codec.complexMatrix (d 0 + 1)) EigData.matrix,
    .derivedOfLength (d 1 + d 2) (fun x => words (d 0) x.δ x.φ),
    .derivedOfLength (d 6) (fun x => ewords (d 0) x.δ x.φ),
    .blank (2 * ((d 0 + 1) * (d 0 + 1))), .blank (2 * ((d 0 + 1) * (d 0 + 1))), .blank 1]
  fits := by
    intro d i p hp
    fin_cases i <;> (
      have hport := Option.some.inj hp
      subst hport
      constructor <;>
        simp [Slot.len, Slot.held, Slot.derivedOfLength, Access.readable, Codec.complexMatrix,
          List.ofFn_succ])
  Unstored _ := ℝ × ℝ
  unstored _ x := (x.δ, x.φ)
  faithful d x y hu h := by
    have h0 := h 0
    simp only [Slot.input, Matrix.cons_val_zero, Option.some.injEq] at h0
    have hm := (Codec.complexMatrix (d 0 + 1)).encode_injective h0
    obtain ⟨_, _, _⟩ := x
    obtain ⟨_, _, _⟩ := y
    simp only [Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    obtain rfl : _ = _ := hm
    rfl
  admitted := admitted
  inhabited d hd := by
    obtain ⟨-, δ, φ, -, -, -, -, hs⟩ := hd
    exact ⟨⟨0, δ, φ⟩, hs⟩

/-- **The problem of the eigensolver** on the machine `Mch`: the problem of the admitted inputs
`NLAlib.Schur.eigSolverInputs`. -/
noncomputable abbrev eigSolverProblem (Mch : Machine ℝ) (words ewords : ℕ → ℝ → ℝ → List ℝ)
    (sizes : ℕ → ℝ → ℝ → Fin 7 → ℕ) (admitted : ∃ d, EigSizes Mch sizes d) : Problem ℝ 7 6 :=
  (eigSolverInputs Mch words ewords sizes admitted).problem

/-- **The work (and span) of the eigensolver** from the solver's and the stage's work bounds:
their sum and the glue $128$. -/
def eigSolverWork (WSolve WEv : (Fin 7 → ℕ) → ℕ) (d : Fin 7 → ℕ) : ℕ :=
  WSolve d + WEv d + 128

/-- The payload words of the six supplied buffers. -/
def eigSolverInputWords (d : Fin 7 → ℕ) : ℕ :=
  2 * ((d 0 + 1) * (d 0 + 1)) + (d 1 + d 2) + d 6 + 2 * ((d 0 + 1) * (d 0 + 1)) +
    2 * ((d 0 + 1) * (d 0 + 1)) + 1

/-- **The specification of the eigensolver**: the budget, scratch and resident memory of the
static count, the work and the span `NLAlib.Schur.eigSolverWork`, and on every tape the frame:
the run writes only the matrix, the accumulator, the eigenvectors and the flag. -/
noncomputable def eigSolverSpecification (Mch : Machine ℝ) (words ewords : ℕ → ℝ → ℝ → List ℝ)
    (sizes : ℕ → ℝ → ℝ → Fin 7 → ℕ) (admitted : ∃ d, EigSizes Mch sizes d)
    (Solve Ev : Stmt SmallEigOp Tst) (WSolve WEv : (Fin 7 → ℕ) → ℕ) :
    Specification SmallEigOp Tst (eigSolverProblem Mch words ewords sizes admitted) where
  budget := staticCost (eigSolverProgram Solve Ev)
  scratch := staticPeak smallEigResources (eigSolverProgram Solve Ev)
  work := eigSolverWork WSolve WEv
  span := eigSolverWork WSolve WEv
  memory d := eigSolverInputWords d + staticPeak smallEigResources (eigSolverProgram Solve Ev) d
  good d x _ _ m := (eigSolverProblem Mch words ewords sizes admitted).initial d x |>.store.EqOff
    (eigFp (d 0) (0, 0) (3, 0) (4, 0) (5, 0)) m.store

section EigGeneric

variable {Mch : Machine ℝ} {words ewords : ℕ → ℝ → ℝ → List ℝ}
  {sizes : ℕ → ℝ → ℝ → Fin 7 → ℕ} {admitted : ∃ d, EigSizes Mch sizes d}

/-- The static count of the eigensolver program is at most the work
`NLAlib.Schur.eigSolverWork` of bounds on the solver's and the stage's instrumented static counts
at the offsets the eigensolver passes to them
(`NLAlib.Schur.size_stmtCost_eigSolverWith_le`). -/
theorem size_staticCost_eigSolverProgram_le {Solve Ev : Stmt SmallEigOp Tst}
    {WSolve WEv : (Fin 7 → ℕ) → ℕ}
    (hSolve : ∀ d, Count.size (stmtCost Solve.instrument
      [d 0 + 1, d 1, d 2, d 3, d 4, d 5, 0, 0, 0, 0, 0]) ≤ WSolve d)
    (hEv : ∀ d, Count.size (stmtCost Ev.instrument [d 0 + 1, d 6, 0, 0, 0, 0, 0]) ≤ WEv d)
    (d : Fin 7 → ℕ) :
    Count.size (staticCost (eigSolverProgram Solve Ev) d) ≤ eigSolverWork WSolve WEv d := by
  have he : (Program.environment (b := 6) d).idx =
      [d 0, d 1, d 2, d 3, d 4, d 5, d 6, 0, 0, 0, 0, 0, 0] := rfl
  have h1 := hSolve d
  have h2 := hEv d
  have hsup : ∀ x y : Count (SmallEigOp ⊕ Bookkeeping) Tst,
      Count.size (x ⊔ y) = Count.size x + Count.size y - Count.size (x ⊓ y) := fun x y => by
    rw [← size_sup_add_size_inf]; omega
  simp only [staticCost, eigSolverProgram_eq, eigSolverWith, Stmt.alloc, he, Stmt.instrument,
    stmtCost, tally, indexBookkeeping, operandBookkeeping, IExp.bookkeeping, List.flatMap_cons,
    List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, useCost, testCost,
    IExp.evalList, IExp.eval, List.map_cons, List.map_nil, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.map_some, Option.getD_some, map_add, map_zero, hsup,
    Count.one, Count.test, size_single]
  unfold eigSolverWork
  omega

/-- The sizes of an input of the problem are those of its reals. -/
theorem eigSolverProblem_sizes_eq (d : Fin 7 → ℕ)
    (x : (eigSolverProblem Mch words ewords sizes admitted).Input d) :
    sizes (d 0) x.val.1.δ x.val.1.φ = d :=
  (eigSolverInputs Mch words ewords sizes admitted).accepts_data x

/-- The six supplied buffers of an input, when the words have the sizes' counts: the matrix
words, the solver's and the stage's words, and uninitialized room for the accumulator, the
eigenvectors and the flag. -/
theorem eigSolverProblem_buffers
    (hwords : ∀ n δ φ, (words n δ φ).length = sizes n δ φ 1 + sizes n δ φ 2)
    (hewords : ∀ n δ φ, (ewords n δ φ).length = sizes n δ φ 6) (d : Fin 7 → ℕ)
    (x : (eigSolverProblem Mch words ewords sizes admitted).Input d) :
    x.val.2 = ![(matrixWords x.val.1.matrix).map some,
      (words (d 0) x.val.1.δ x.val.1.φ).map some, (ewords (d 0) x.val.1.δ x.val.1.φ).map some,
      List.replicate (2 * ((d 0 + 1) * (d 0 + 1))) none,
      List.replicate (2 * ((d 0 + 1) * (d 0 + 1))) none, [none]] := by
  rw [(eigSolverInputs Mch words ewords sizes admitted).buffers_eq x]
  funext i
  fin_cases i
  · rfl
  · refine Slot.buffer_derivedOfLength ?_
    rw [hwords, eigSolverProblem_sizes_eq d x]
  · refine Slot.buffer_derivedOfLength ?_
    rw [hewords, eigSolverProblem_sizes_eq d x]
  · rfl
  · rfl
  · rfl

/-- The initial payload of an input is `NLAlib.Schur.eigSolverInputWords`. -/
theorem eigSolverProblem_initialBytes (d : Fin 7 → ℕ)
    (x : (eigSolverProblem Mch words ewords sizes admitted).Input d) :
    (eigSolverProblem Mch words ewords sizes admitted).initialBytes d x =
      eigSolverInputWords d := by
  refine ((eigSolverInputs Mch words ewords sizes admitted).initialBytes_eq x).trans ?_
  simp [eigSolverInputs, Slot.len, Slot.derivedOfLength, Codec.complexMatrix, List.ofFn_succ,
    eigSolverInputWords, Nat.add_assoc]

/-- The initial memory holds the input of the eigensolver (`NLAlib.Schur.EigSolverInput`) at the
six supplied buffers, when the words have the sizes' counts. -/
theorem eigSolverProblem_initial_input
    (hwords : ∀ n δ φ, (words n δ φ).length = sizes n δ φ 1 + sizes n δ φ 2)
    (hewords : ∀ n δ φ, (ewords n δ φ).length = sizes n δ φ 6) (d : Fin 7 → ℕ)
    (x : (eigSolverProblem Mch words ewords sizes admitted).Input d) :
    EigSolverInput (words (d 0) x.val.1.δ x.val.1.φ) (ewords (d 0) x.val.1.δ x.val.1.φ) (0, 0)
      (1, 0) (2, 0) (3, 0) (4, 0) (5, 0) x.val.1.matrix
      ((eigSolverProblem Mch words ewords sizes admitted).initial d x) := by
  have hb := eigSolverProblem_buffers hwords hewords d x
  have hs : ((eigSolverProblem Mch words ewords sizes admitted).initial d x).store =
      List.ofFn x.val.2 := rfl
  have hA := Problem.initial_readBlock (P := eigSolverProblem Mch words ewords sizes admitted) d x
    (0 : Fin 6) (xs := matrixWords x.val.1.matrix) (by rw [hb]; rfl)
  have hP := Problem.initial_readBlock (P := eigSolverProblem Mch words ewords sizes admitted) d x
    (1 : Fin 6) (xs := words (d 0) x.val.1.δ x.val.1.φ) (by rw [hb]; rfl)
  have hE := Problem.initial_readBlock (P := eigSolverProblem Mch words ewords sizes admitted) d x
    (2 : Fin 6) (xs := ewords (d 0) x.val.1.δ x.val.1.φ) (by rw [hb]; rfl)
  refine ⟨⟨?_, ?_, ?_, by simpa [HoldsMatrix] using hA, by simpa using hP⟩, ?_, ?_, ?_,
    by simpa using hE⟩
  · simp [Mem.Live, Problem.initial]
  · simp [hs, hb, Mem.Room, Store.len, List.ofFn_succ]
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨Fp.disj_inBlock_of_ne (by omega), Fp.disj_inBlock_of_ne (by omega),
      Fp.disj_inBlock_of_ne (by omega)⟩, ⟨Fp.disj_inBlock_of_ne (by omega),
      Fp.disj_inBlock_of_ne (by omega)⟩, Fp.disj_inBlock_of_ne (by omega)⟩
  · simp [Mem.Live, Problem.initial]
  · simp [hs, hb, Mem.Room, Store.len, List.ofFn_succ]
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
      exact Fp.disj_inBlock_of_ne (by omega)

/-- **The eigensolver as a canonical certificate, from component data**: the fixed program
`NLAlib.Schur.eigSolverProgram` of a Schur solver and an eigenvector stage, over the model
`NLAlib.SmallEig.smallEigModel` with the unit costs, given that it passes the storage discipline
(`ht`), its routine meets the every-tape specification `NLAlib.Schur.eigSolverSpec` under every
interpretation of the model (`hmeets`: it terminates and writes only the matrix, the accumulator,
the eigenvectors and the flag), and the components' instrumented static counts are at most
$W_\bullet$, succeeds within the static budget, scratch and memory, with work and span at most
`NLAlib.Schur.eigSolverWork` of the $W_\bullet$.
Algorithm: dense-eigendecomposition (run model) -/
noncomputable def eigSolverAlgorithm (sU : ℕ) (Solve Ev : Stmt SmallEigOp Tst)
    (WSolve WEv : (Fin 7 → ℕ) → ℕ)
    (hSolve : ∀ d, Count.size (stmtCost Solve.instrument
      [d 0 + 1, d 1, d 2, d 3, d 4, d 5, 0, 0, 0, 0, 0]) ≤ WSolve d)
    (hEv : ∀ d, Count.size (stmtCost Ev.instrument [d 0 + 1, d 6, 0, 0, 0, 0, 0]) ≤ WEv d)
    (hwords : ∀ n δ φ, (words n δ φ).length = sizes n δ φ 1 + sizes n δ φ 2)
    (hewords : ∀ n δ φ, (ewords n δ φ).length = sizes n δ φ 6)
    (ht : (eigSolverProgram Solve Ev).wellTyped smallEigResources
      (eigSolverProblem Mch words ewords sizes admitted).formats = true)
    (hmeets : ∀ d, EigSizes Mch sizes d →
      ∀ (x : (eigSolverProblem Mch words ewords sizes admitted).Input d)
        (I : Interp SmallEigOp Tst ℝ),
      (smallEigModel (eigSolverProblem Mch words ewords sizes admitted) Mch sU).contracts d x I →
      (eigSolverRoutine Solve Ev).Meets I
        (eigSolverSpec (words (d 0) x.val.1.δ x.val.1.φ) (ewords (d 0) x.val.1.δ x.val.1.φ)
          (List.ofFn d))) :
    Algorithm (smallEigModel (eigSolverProblem Mch words ewords sizes admitted) Mch sU)
      (eigSolverSpecification Mch words ewords sizes admitted Solve Ev WSolve WEv) :=
  ((eigSolverInputs Mch words ewords sizes admitted).cast (eigSolverRoutine Solve Ev)
      rfl rfl).algorithm
    (fun d x => eigSolverSpec (words (d 0) x.δ x.φ) (ewords (d 0) x.δ x.φ) (List.ofFn d)) hmeets
    (fun d _ x hx _ => by
      have hx' : sizes (d 0) x.δ x.φ = d := hx
      have hw : (Slot.derivedOfLength (d 1 + d 2) fun x : EigData d =>
          words (d 0) x.δ x.φ).words x = words (d 0) x.δ x.φ :=
        Slot.words_derivedOfLength (by rw [hwords, hx'])
      have he : (Slot.derivedOfLength (d 6) fun x : EigData d =>
          ewords (d 0) x.δ x.φ).words x = ewords (d 0) x.δ x.φ :=
        Slot.words_derivedOfLength (by rw [hewords, hx'])
      refine ⟨rfl, x.matrix, ?_⟩
      change [matrixWords x.matrix, (Slot.derivedOfLength (d 1 + d 2) fun x : EigData d =>
        words (d 0) x.δ x.φ).words x, (Slot.derivedOfLength (d 6) fun x : EigData d =>
        ewords (d 0) x.δ x.φ).words x] = _
      rw [hw, he]
      rfl)
    (fun d _ x τ m' hfr _ ys _ _ c _ => by
      change Store.EqOff (Fp.blocks [(0, 0), (3, 0), (4, 0), (5, 0)]
        [2 * ((d 0 + 1) * (d 0 + 1)), 2 * ((d 0 + 1) * (d 0 + 1)),
          2 * ((d 0 + 1) * (d 0 + 1)), 1]) _ _ at hfr
      refine hfr.mono ?_
      unfold eigFp schurFp
      fp_sub)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun d _ => (smallEigResources_work _).trans_le
      (size_staticCost_eigSolverProgram_le hSolve hEv d))
    (fun d _ => (smallEigResources_span _).trans_le
      (size_staticCost_eigSolverProgram_le hSolve hEv d))
    (fun d _ x =>
      Nat.add_le_add_right (eigSolverProblem_initialBytes (admitted := admitted) d x).le _)
    (ht := ht)

end EigGeneric

/-- The sizes of a run of the dense eigensolver at $(n, \delta, \varphi)$: those of the dense
Schur solver at $(\delta, \delta_C)$ and the one stage word. -/
noncomputable def denseEigSizes (n : ℕ) (δ φ : ℝ) : Fin 7 → ℕ :=
  ![n, (denseSchurRegParams n δ φ).length,
    (denseSchurThresholdAt n δ (denseEigCoreDelta n δ φ) φ ::
      (denseSchurShQRParamsAt n δ (denseEigCoreDelta n δ φ) φ ++
        denseSchurLeafParamsAt n δ (denseEigCoreDelta n δ φ) φ)).length,
    denseSchurDegree n δ φ, denseSchurCapAt n δ (denseEigCoreDelta n δ φ) φ,
    denseSchurLeafCapAt n δ (denseEigCoreDelta n δ φ) φ, 1]

/-- The stage word of the dense eigensolver: the floor parameter. -/
noncomputable def denseEigStageParams (n : ℕ) (δ φ : ℝ) : List ℝ := [denseEigFloor n δ φ]

/-- **The problem of the dense eigensolver** on the machine `Mch`. -/
noncomputable abbrev denseEigProblem (Mch : Machine ℝ)
    (admitted : ∃ d, EigSizes Mch denseEigSizes d) : Problem ℝ 7 6 :=
  eigSolverProblem Mch denseEigSchurParams denseEigStageParams denseEigSizes admitted

/-- **The work (and span) of the dense eigensolver** at the sizes
$(n, n_r, n_q, k, F, T, n_e)$ = `d`: `NLAlib.Schur.eigSolverWork` of the dense Schur solver's
$384547(n + 1)^3(k + 1)^4(n_r + n_q + 1)(F + 1)(T + 1)^2$ (`NLAlib.Schur.denseSchur_work_le`) and
the stage's $10^4(n + 1)^3$ (`NLAlib.Schur.size_stmtCost_triEigvecStage_le`). Every primitive,
test and structural instruction is counted at unit cost; the parameter words are supplied in the
input. -/
def denseEigWork (d : Fin 7 → ℕ) : ℕ :=
  eigSolverWork (fun d => 384547 * (d 0 + 1) ^ 3 * (d 3 + 1) ^ 4 * (d 1 + d 2 + 1) *
    (d 4 + 1) * (d 5 + 1) ^ 2) (fun d => 10000 * (d 0 + 1) ^ 3) d

/-- **The specification of the dense eigensolver** on the machine `Mch`. -/
noncomputable def denseEigSpecification (Mch : Machine ℝ)
    (admitted : ∃ d, EigSizes Mch denseEigSizes d) (sG : ℕ) :
    Specification SmallEigOp Tst (denseEigProblem Mch admitted) :=
  eigSolverSpecification Mch denseEigSchurParams denseEigStageParams denseEigSizes admitted
    (denseSchur sG) triEigvecStage
    (fun d => 384547 * (d 0 + 1) ^ 3 * (d 3 + 1) ^ 4 * (d 1 + d 2 + 1) * (d 4 + 1) *
      (d 5 + 1) ^ 2) (fun d => 10000 * (d 0 + 1) ^ 3)

-- The kernel evaluates the discipline over the whole tree; its recursion is deep.
set_option maxRecDepth 100000 in
/-- The dense eigensolver program passes the storage discipline of the costs. -/
theorem denseEigProgram_wellTyped (sG : ℕ) {Mch : Machine ℝ}
    {admitted : ∃ d, EigSizes Mch denseEigSizes d} :
    (eigSolverProgram (denseSchur sG) triEigvecStage).wellTyped smallEigResources
      (denseEigProblem Mch admitted).formats = true := by
  kernel_rfl

/-- The solver words have the sizes' count. -/
theorem length_denseEigSchurParams (n : ℕ) (δ φ : ℝ) :
    (denseEigSchurParams n δ φ).length = denseEigSizes n δ φ 1 + denseEigSizes n δ φ 2 := by
  simp [denseEigSchurParams, denseSchurParamsAt, denseSchurParamsAtWith, denseEigSizes]

/-- The stage words have the sizes' count. -/
theorem length_denseEigStageParams (n : ℕ) (δ φ : ℝ) :
    (denseEigStageParams n δ φ).length = denseEigSizes n δ φ 6 := by
  simp [denseEigStageParams, denseEigSizes]

-- Six operands and the long parameter words make the side conditions heavy.
set_option maxHeartbeats 1000000 in
/-- **The routine of the dense eigensolver meets its every-tape specification**: on the words of
a matrix of order $n + 1$, the words `NLAlib.Schur.denseEigSchurParams` and the floor, at the
sizes `NLAlib.Schur.denseEigSizes`, it terminates on every tape and writes only the matrix, the
accumulator, the eigenvectors and the flag (`NLAlib.Schur.eigSolverWith_completes_of_pair` with
`NLAlib.Schur.triEigvecStage_completes`; no rounding model). -/
theorem denseEigRoutine_meets {Mch : Machine ℝ} {I : Interp SmallEigOp Tst ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {δ φ : ℝ} :
    (eigSolverRoutine (denseSchur sG) triEigvecStage).Meets I
      (eigSolverSpec (denseEigSchurParams n δ φ) (denseEigStageParams n δ φ)
        (List.ofFn (denseEigSizes n δ φ))) := by
  routine_intro [n', nr, nq, k, F, T, ne] (a, p, pe, uo, v, f) reads (ws, ps, es)
  have hapart : ∀ l₁ l₂ : ℕ, Fp.Apart [a, p, uo, f, pe, v] [2 * ((n' + 1) * (n' + 1)), l₁,
      2 * ((n' + 1) * (n' + 1)), 1, l₂, 2 * ((n' + 1) * (n' + 1))] := fun l₁ l₂ => by
    disjoint
  obtain ⟨hd, A, heq⟩ := hpre
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : n' = n ∧ nr = (denseSchurRegParams n δ φ).length ∧
      nq = (denseSchurThresholdAt n δ (denseEigCoreDelta n δ φ) φ ::
        (denseSchurShQRParamsAt n δ (denseEigCoreDelta n δ φ) φ ++
          denseSchurLeafParamsAt n δ (denseEigCoreDelta n δ φ) φ)).length ∧
      k = denseSchurDegree n δ φ ∧ F = denseSchurCapAt n δ (denseEigCoreDelta n δ φ) φ ∧
      T = denseSchurLeafCapAt n δ (denseEigCoreDelta n δ φ) φ ∧ ne = 1 := by
    simpa [denseEigSizes, List.ofFn_succ] using hd
  obtain ⟨rfl, rfl, rfl⟩ : ws = matrixWords A ∧ ps = denseEigSchurParams n' δ φ ∧
      es = denseEigStageParams n' δ φ := by simpa using heq
  have hlen : (denseEigSchurParams n' δ φ).length = (denseSchurRegParams n' δ φ).length +
      (denseSchurThresholdAt n' δ (denseEigCoreDelta n' δ φ) φ ::
        (denseSchurShQRParamsAt n' δ (denseEigCoreDelta n' δ φ) φ ++
          denseSchurLeafParamsAt n' δ (denseEigCoreDelta n' δ φ) φ)).length := by
    simp [denseEigSchurParams, denseSchurParamsAt, denseSchurParamsAtWith]
  rw [← hlen] at hps
  have hes' : m.store.readBlock pe.1 pe.2 (denseEigStageParams n' δ φ).length =
      some (denseEigStageParams n' δ φ) := hes
  have hin : EigSolverInput (denseEigSchurParams n' δ φ) (denseEigStageParams n' δ φ)
      a p pe uo v f A m := by
    refine ⟨⟨by room, ?_, by disjoint, hws, hps⟩, by room, ?_, ?_, hes'⟩
    · simp only [Mem.room_cons, Mem.room_nil, and_true]
      exact ⟨hroom.1, Store.le_len_of_readBlock hps (by rw [hlen, List.length_cons]; omega),
        hroom.2.1, hroom.2.2.2⟩
    · simp only [Mem.room_cons, Mem.room_nil, and_true]
      exact ⟨Store.le_len_of_readBlock hes' (by simp [denseEigStageParams]), hroom.2.2.1⟩
    · exact hapart _ _
  have hT := eigSolverWith_completes_of_pair (nr := (denseSchurRegParams n' δ φ).length)
    (nq := (denseSchurThresholdAt n' δ (denseEigCoreDelta n' δ φ) φ ::
      (denseSchurShQRParamsAt n' δ (denseEigCoreDelta n' δ φ) φ ++
        denseSchurLeafParamsAt n' δ (denseEigCoreDelta n' δ φ) φ)).length)
    (k := denseSchurDegree n' δ φ) (F := denseSchurCapAt n' δ (denseEigCoreDelta n' δ φ) φ)
    (T := denseSchurLeafCapAt n' δ (denseEigCoreDelta n' δ φ) φ) hL hC
    (fun hin' => denseSchurAt_completes_pair (O := SmallEigOp) (Q := Tst) (sG := sG)
      (δR := δ) (δC := denseEigCoreDelta n' δ φ) (φ := φ) hS hL hNat hQ hC hSmp hDisk hin' _)
    (triEigvecStage_completes hS hL hC (n' + 1) _) hin τ
  refine (hT.in_frame (ρ := Env.frame [n', (denseSchurRegParams n' δ φ).length,
    (denseSchurThresholdAt n' δ (denseEigCoreDelta n' δ φ) φ ::
      (denseSchurShQRParamsAt n' δ (denseEigCoreDelta n' δ φ) φ ++
        denseSchurLeafParamsAt n' δ (denseEigCoreDelta n' δ φ) φ)).length,
    denseSchurDegree n' δ φ, denseSchurCapAt n' δ (denseEigCoreDelta n' δ φ) φ,
    denseSchurLeafCapAt n' δ (denseEigCoreDelta n' δ φ) φ, 1] [a, p, pe, uo, v, f])
    rfl rfl (by room)).mono ?_ ?_
  · unfold eigFp schurFp
    fp_sub
  · rintro m' - -
    exact ⟨trivial, [], rfl, trivial⟩

/-- **The dense eigensolver as a canonical certificate**: `NLAlib.Schur.eigSolverAlgorithm` with
the dense Schur solver and the eigenvector stage and their static counts, over the model
`NLAlib.SmallEig.smallEigModel` (no oracle) with the unit costs: it succeeds on every admitted
input, interpretation of the model and tape, within the static budget, scratch and memory, with
work and span at most `NLAlib.Schur.denseEigWork`, writing only the matrix, the accumulator, the
eigenvectors and the flag. The eigendecomposition holds with probability at least $1 - \varphi$
(`NLAlib.Schur.denseEig_algorithm_measureReal_not_accepts_le`).
Algorithm: dense-eigendecomposition (run model) -/
noncomputable def denseEigAlgorithm (Mch : Machine ℝ)
    (admitted : ∃ d, EigSizes Mch denseEigSizes d) (sU sG : ℕ) :
    Algorithm (smallEigModel (denseEigProblem Mch admitted) Mch sU)
      (denseEigSpecification Mch admitted sG) :=
  eigSolverAlgorithm sU _ _ _ _
    (fun d => denseSchur_work_le sG (d 0) (d 1) (d 2) (d 3) (d 4) (d 5))
    (fun d => size_stmtCost_triEigvecStage_le (d 0) (d 6))
    length_denseEigSchurParams length_denseEigStageParams (denseEigProgram_wellTyped sG)
    (fun d hd x _ hI => by
      obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
      have h := denseEigRoutine_meets (sG := sG) (n := d 0) (δ := x.val.1.δ) (φ := x.val.1.φ)
        hS hL hd.1 hQ hC hSmp hDisk
      rw [eigSolverProblem_sizes_eq d x] at h
      exact h)

/-- **The dense eigensolver, on one run.** Let the machine `Mch` have the standard model at
$\boldsymbol{u}$; let the tape $\xi$ have the stream laws `law`, with `law` $s_U$ uniform on
$[0, 1]$ and `law` $s_G$ the standard real Gaussian law. Let $(n, n_r, n_q, k, F, T, n_e)$ = `d`
be admitted and let the input `x` hold a complex $\mathbf{A}$ of order $n + 1$,
$0 < \delta \le 1$, $0 < \varphi \le 1$ and $\boldsymbol{u} \le \boldsymbol{u}_E$. Let `I` meet the
model, be measurable and read the tape only in its windows. Then
$$\mathbb{P}\bigl[\mathsf{denseEigAlgorithm}(\mathbf{A}) \text{ fails, exceeds its budget,
  scratch, memory, work or span, writes outside } \mathbf{A}, \widehat{\mathbf{U}},
  \widehat{\mathbf{V}} \text{ and the flag, or stores no Schur output and eigendecomposition
  output of } \mathsf{denseEig}\bigr] \le \varphi\,,$$
on one counted run, with the work and the span `NLAlib.Schur.denseEigWork`, the outputs those of
`NLAlib.Schur.denseEig_measureReal_not_eig_le`. Here $\boldsymbol{u}_E$ is
`NLAlib.Schur.uDenseEig`. No printed source: [BanksGarzaVargasSrivastava2022, Theorem 1.4]
computes eigenvalues only.

Note: General form, any program meeting the model: `NLAlib.Ops.Algorithm`; the statement on the
program is `NLAlib.Schur.denseEig_measureReal_not_eig_le`.
Result: dense-eigendecomposition-certificate -/
theorem denseEig_algorithm_measureReal_not_accepts_le {Mch : Machine ℝ}
    {admitted : ∃ d, EigSizes Mch denseEigSizes d} {u : ℝ} (hM : StdModel u id Mch)
    {law : ℕ → Measure ℝ} {sU sG : ℕ} (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {d : Fin 7 → ℕ} (hd : EigSizes Mch denseEigSizes d)
    (x : (denseEigProblem Mch admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (denseEigProblem Mch admitted) Mch sU).contracts d x I)
    (hIm : I.IsMeasurable) {win : SmallEigOp → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hδ : 0 < x.val.1.δ) (hδ1 : x.val.1.δ ≤ 1) (hφ : 0 < x.val.1.φ) (hφ1 : x.val.1.φ ≤ 1)
    (hu : u ≤ uDenseEig (d 0) x.val.1.δ x.val.1.φ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ (denseEigSpecification Mch admitted sG).Accepts
        (denseEigAlgorithm Mch admitted sU sG).program I smallEigResources (ξ ω) d x
      fun _ m => ((denseEigProblem Mch admitted).initial d x).store.EqOff
          (eigFp (d 0) (0, 0) (3, 0) (4, 0) (5, 0)) m.store ∧
        SchurOutput (0, 0) (3, 0) (5, 0) x.val.1.matrix x.val.1.δ
          (58 * denseEigRotations (d 0) x.val.1.δ x.val.1.φ * u) m ∧
        EigOutput (0, 0) (4, 0) (5, 0) x.val.1.matrix x.val.1.δ x.val.1.δ (1 / 8) x.val.1.δ
          (2 * √((d 0 : ℝ) + 1) * denseSchurB (d 0) x.val.1.δ x.val.1.φ)
          (denseSchurΓ (d 0) x.val.1.δ x.val.1.φ / 4) m} ≤ x.val.1.φ := by
  have := hξ.isProbabilityMeasure
  obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
  have hin := eigSolverProblem_initial_input (admitted := admitted)
    length_denseEigSchurParams length_denseEigStageParams d x
  have hT := denseEig_measureReal_not_eig_le (O := SmallEigOp) (Q := Tst) (sG := sG) hS hM
    hL hd.1 hQ hC hIm hloc hSmp hDisk hU hG hδ hδ1 hφ hφ1 hu hin hξ
  refine (denseEigAlgorithm Mch admitted sU sG).measureReal_not_accepts_le_of_wp hd x
    I hI P ξ _ ?_
  refine (measureReal_mono ?_).trans hT
  intro ω hω hW
  have hl7 : ((denseEigProblem Mch admitted).initial d x).Live
      [(0, 0), (1, 0), (2, 0), (0, 0), (3, 0), (4, 0), (5, 0)] := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Problem.initial]
  have hsz := eigSolverProblem_sizes_eq (admitted := admitted) d x
  refine hω (wp_frame ?_ ?_ hl7 hW)
  · have h := fun i => (congrFun hsz i).symm
    simp [Program.environment, IExp.evalList, IExp.eval, denseEigDims, denseSchurDimsAt,
      denseSchurDimsAtWith, List.ofFn_succ, h 1, h 2, h 3, h 4, h 5, h 6, denseEigSizes]
  · simp [Program.environment, Operand.evalList, Operand.eval, IExp.eval, List.ofFn_succ]

end NLAlib.Schur
