/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQRoundingBody
public import NLAlib.Matrix.Computation.PLUQRoundingOutput
public import NLAlib.Matrix.Computation.PLUQRoutine

/-!
# Rounded complete-pivoted LU and its routine certificate

The unchanged stored complete-pivoted driver succeeds under the standard scalar model with
exact bounded index controls. Its actual factors are triangular with exact unit lower
diagonal and multipliers bounded by one plus unit roundoff. For unit roundoff below one,
the decoded factors have the componentwise backward-error allowance associated with the
actual recorded row permutation. Singular inputs and empty matrices are admitted.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_pluqFactor`: full actual rounded execution and error bound.
* `NLAlib.Computation.isPLUQRoutine_pluqFactor_of_isRelErrSem`: the actual rounded routine instance.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Full actual complete-pivoted LU succeeds on every decoded square input under standard
relative-error semantics with every scalar result in range and exact index literals/conversion
through the dimension. Its only net writes are the two factors and actual absolute pivot log;
the separate input is retained. The factors have exact triangular shapes and unit lower
diagonal, and lower entries have magnitude at most $1+u_p$. If $u_p<1$, the factors satisfy the
componentwise backward-error budget $\gamma_{N+4}$ for the input permuted by that actual log.
No nonsingularity, nonzero-pivot or successful-run premise is required. Empty matrices perform
no source or output reads and require no valid buffer handles. Arithmetic charges and scalar
word carriers are arbitrary. [Higham2002, §9.3; CarsonMaShao2026, Lemma 2]. -/
theorem IsRelErrSem.exec_pluqFactor {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (st : St P K C) (A L U Hr Hc : ℕ) (ao lo uo hro hco : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : HoldsDecoded st.store dec tag A ao.eval M)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hU : Writable st.store tag U uo.eval (n.eval * n.eval))
    (hR : Writable st.store tag Hr hro.eval n.eval)
    (hC : Writable st.store tag Hc hco.eval n.eval)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc)
    (hAL : 0 < n.eval → A ≠ L) (hAU : 0 < n.eval → A ≠ U) (hAR : 0 < n.eval → A ≠ Hr)
    (hAC : 0 < n.eval → A ≠ Hc) :
    ∃ (out : St P K C) (WL WU WR WC : Array K) (rows cols : Fin n.eval → Fin n.eval),
      exec I (pluqFactor tag n A L U Hr Hc ao lo uo hro hco).run st = some out ∧
      WL.size = n.eval * n.eval ∧ WU.size = n.eval * n.eval ∧ WR.size = n.eval ∧ WC.size = n.eval ∧
      st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
        (Hr, hro.eval, n.eval), (Hc, hco.eval, n.eval)] [WL, WU, WR, WC] = some out.store ∧
      ReadsDecoded out.store dec tag Hr hro.eval (fun j => ((rows j).val : ℝ)) ∧
      ReadsDecoded out.store dec tag Hc hco.eval (fun j => ((cols j).val : ℝ)) ∧
      (∀ j, j ≤ rows j) ∧ (∀ j, j ≤ cols j) ∧
      (unflatten n.eval n.eval (WL.map (dec tag))).IsLowerTriangular ∧
      (∀ j, unflatten n.eval n.eval (WL.map (dec tag)) j j = 1) ∧
      (unflatten n.eval n.eval (WU.map (dec tag))).IsUpperTriangular ∧
      (∀ i j, |unflatten n.eval n.eval (WL.map (dec tag)) i j| ≤ 1 + u tag) ∧
      (u tag < 1 → IsLUErr (roundingFactor (n.eval + 4) (u tag))
        (M.submatrix (luPivotPermutation rows n.eval) (luPivotPermutation cols n.eval))
        (unflatten n.eval n.eval (WL.map (dec tag)))
        (unflatten n.eval n.eval (WU.map (dec tag)))) ∧
      HoldsDecoded out.store dec tag L lo.eval (unflatten n.eval n.eval (WL.map (dec tag))) ∧
      HoldsDecoded out.store dec tag U uo.eval (unflatten n.eval n.eval (WU.map (dec tag))) ∧
      HoldsDecoded out.store dec tag A ao.eval M := by
  let Q : Store P K → Prop := fun store => ∃ (WL WU WR WC : Array K)
      (rows cols : Fin n.eval → Fin n.eval),
    WL.size = n.eval * n.eval ∧ WU.size = n.eval * n.eval ∧ WR.size = n.eval ∧ WC.size = n.eval ∧
    st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
      (Hr, hro.eval, n.eval), (Hc, hco.eval, n.eval)] [WL, WU, WR, WC] = some store ∧
    ReadsDecoded store dec tag Hr hro.eval (fun j => ((rows j).val : ℝ)) ∧
    ReadsDecoded store dec tag Hc hco.eval (fun j => ((cols j).val : ℝ)) ∧
    (∀ j, j ≤ rows j) ∧ (∀ j, j ≤ cols j) ∧
    (unflatten n.eval n.eval (WL.map (dec tag))).IsLowerTriangular ∧
    (∀ j, unflatten n.eval n.eval (WL.map (dec tag)) j j = 1) ∧
    (unflatten n.eval n.eval (WU.map (dec tag))).IsUpperTriangular ∧
    (∀ i j, |unflatten n.eval n.eval (WL.map (dec tag)) i j| ≤ 1 + u tag) ∧
    (u tag < 1 → IsLUErr (roundingFactor (n.eval + 4) (u tag))
      (M.submatrix (luPivotPermutation rows n.eval) (luPivotPermutation cols n.eval))
      (unflatten n.eval n.eval (WL.map (dec tag)))
      (unflatten n.eval n.eval (WU.map (dec tag)))) ∧
    HoldsDecoded store dec tag L lo.eval (unflatten n.eval n.eval (WL.map (dec tag))) ∧
    HoldsDecoded store dec tag U uo.eval (unflatten n.eval n.eval (WU.map (dec tag)))
  obtain ⟨out, hr, WL, WU, WR, WC, rows, cols, hLs, hUs, hRs, hCs, hw, hrow, hcol, hp, hq, hlower,
    hdiag,
      hupper, hbound, herr, hF, hG⟩ := exists_exec_alloc I tag (n * n)
    (fun S => ((do
      copyv tag A ao S 0 (n * n)
      forRange (n * n) fun i => Builder.ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => Builder.ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        completePivotChoice tag n (.var k) S 0
          ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
        bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
          swapRows tag n n S 0 (.var k) (.var row)
          swapRows tag n n L lo (.var k) (.var row)
        bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
          swapColumns tag n n S 0 (.var k) (.var col)
          swapColumns tag n n U uo (.var k) (.var col)
        luColumnTotal tag n (.var k) S L U 0 lo uo
        schurStepTotal tag n S 0 (.var k)) : Builder P ι ℕ ℕ Unit).run) st Q (by
      intro σ hσ
      obtain ⟨final, hrun, hs⟩ := PLUQRounding.exec_body I h n hi tag st.store σ A L U Hr Hc
        ao lo uo hro hco M hM hL hU hR hC hLU hLR hLC hUR hUC hRC
        (by simpa only [IExp.eval_mul] using hσ)
      obtain ⟨WL, WU, WR, WC, rows, cols, hresult⟩ := PLUQRounding.State.writeBlocks_pop
        (hσ ▸ hs) hL hU hR hC hLU hLR hLC hUR hUC hRC (h.nonneg (p := tag) trivial)
      exact ⟨final, hrun, WL, WU, WR, WC, rows, cols, hresult⟩)
  refine ⟨out, WL, WU, WR, WC, rows, cols, ?_, hLs, hUs, hRs, hCs, hw, hrow, hcol, hp, hq, hlower,
    hdiag,
    hupper, hbound, herr, hF, hG, ?_⟩
  · change exec I (.seq (.alloc tag (n * n) _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · intro i j
    have hN : 0 < n.eval := Nat.zero_lt_of_lt i.isLt
    obtain ⟨w, hwM, hd⟩ := hM i j
    refine ⟨w, ?_, hd⟩
    rw [Store.read_of_writeBlocks_eq_some_of_forall hw (fun block hblock => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
      rcases hblock with rfl | rfl | rfl | rfl
      · exact Or.inl (hAL hN)
      · exact Or.inl (hAU hN)
      · exact Or.inl (hAR hN)
      · exact Or.inl (hAC hN))]
    exact hwM

/-- The actual complete-pivoted driver supplies a typed two-log LU certificate at the
saved-pivot budget $\gamma_{N+4}$. Scalar results are assumed in range, index controls exact,
and roundoff below one. All singular and empty inputs are admitted. No finite-format range
safety is inferred from the abstract scalar-model hypothesis. [Higham2002, §9.3]. -/
theorem isPLUQRoutine_pluqFactor_of_isRelErrSem {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (tag : P) {N : ℕ} (hi : IsIndexExactSem dec N I.sem) (hu : u tag < 1)
    (A : Matrix (Fin N) (Fin N) ℝ) (Ab Lb Ub Rb Cb : ℕ) (ao lo uo ro co : IExp ℕ)
    (hAL : Ab ≠ Lb) (hAU : Ab ≠ Ub) (hAR : Ab ≠ Rb) (hAC : Ab ≠ Cb)
    (hLU : Lb ≠ Ub) (hLR : Lb ≠ Rb) (hLC : Lb ≠ Cb)
    (hUR : Ub ≠ Rb) (hUC : Ub ≠ Cb) (hRC : Rb ≠ Cb) :
    IsPLUQRoutine I dec tag A (roundingFactor (N + 4) (u tag))
      (fun s => HoldsDecoded s dec tag Ab ao.eval A) Lb Ub Rb Cb lo uo ro co
      (pluqFactor tag (.const N) Ab Lb Ub Rb Cb ao lo uo ro co) where
  composable := executionComposable_pluqFactor I tag (.const N) Ab Lb Ub Rb Cb ao lo uo ro co
  run st hA hw _ _ _ _ _ _ := by
    obtain ⟨out, WL, WU, WR, WC, p, q, hr, hLs, hUs, hRs, hCs, hs, hrow, hcol,
      hp, hq, -, -, -, -, herr, -⟩ :=
      h.exec_pluqFactor I (.const N) hi tag st Ab Lb Ub Rb Cb ao lo uo ro co A hA
        (hw _ List.mem_cons_self) (hw (Ub, uo.eval, N * N) (by simp))
        (hw (Rb, ro.eval, N) (by simp)) (hw (Cb, co.eval, N) (by simp))
        hLU hLR hLC hUR hUC hRC (fun _ => hAL) (fun _ => hAU) (fun _ => hAR) (fun _ => hAC)
    exact ⟨out, WL, WU, WR, WC, p, q, hLs, hUs, hRs, hCs, hr, hs, hrow, hcol,
      hp, hq, herr hu⟩

end NLAlib.Computation
