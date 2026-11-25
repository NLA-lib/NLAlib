/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLURoundingBody
public import NLAlib.Matrix.Computation.PLURoundingOutput
public import NLAlib.Matrix.Computation.PLURoutine

/-!
# Rounded partial-pivoted LU and its routine certificate

The unchanged stored partial-pivoted driver succeeds under the standard scalar model with
exact bounded index controls. Its actual factors are triangular with exact unit lower
diagonal and multipliers bounded by one plus unit roundoff. For unit roundoff below one,
the decoded factors have the componentwise backward-error allowance associated with the
actual recorded row permutation. Singular inputs and empty matrices are admitted.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_pluFactor`: full actual rounded execution and error bound.
* `NLAlib.Computation.isPLURoutine_pluFactor_of_isRelErrSem`: the actual rounded routine instance.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Full actual partial-pivoted LU succeeds on every decoded square input under standard
relative-error semantics with every scalar result in range and exact index literals/conversion
through the dimension. Its only net writes are the two factors and actual absolute pivot log;
the separate input is retained. The factors have exact triangular shapes and unit lower
diagonal, and lower entries have magnitude at most $1+u_p$. If $u_p<1$, the factors satisfy the
componentwise backward-error budget $\gamma_{N+4}$ for the input permuted by that actual log.
No nonsingularity, nonzero-pivot or successful-run premise is required. Empty matrices perform
no source or output reads and require no valid buffer handles. Arithmetic charges and scalar
word carriers are arbitrary. [Higham2002, §9.3; CarsonMaShao2026, Lemma 2]. -/
theorem IsRelErrSem.exec_pluFactor {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (st : St P K C) (A L U H : ℕ) (ao lo uo ho : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : HoldsDecoded st.store dec tag A ao.eval M)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hU : Writable st.store tag U uo.eval (n.eval * n.eval))
    (hH : Writable st.store tag H ho.eval n.eval) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (hAL : 0 < n.eval → A ≠ L) (hAU : 0 < n.eval → A ≠ U) (hAH : 0 < n.eval → A ≠ H) :
    ∃ (out : St P K C) (WL WU WH : Array K) (history : Fin n.eval → Fin n.eval),
      exec I (pluFactor tag n A L U H ao lo uo ho).run st = some out ∧
      WL.size = n.eval * n.eval ∧ WU.size = n.eval * n.eval ∧ WH.size = n.eval ∧
      st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
        (H, ho.eval, n.eval)] [WL, WU, WH] = some out.store ∧
      ReadsDecoded out.store dec tag H ho.eval (fun j => ((history j).val : ℝ)) ∧
      (∀ j, j ≤ history j) ∧
      (unflatten n.eval n.eval (WL.map (dec tag))).IsLowerTriangular ∧
      (∀ j, unflatten n.eval n.eval (WL.map (dec tag)) j j = 1) ∧
      (unflatten n.eval n.eval (WU.map (dec tag))).IsUpperTriangular ∧
      (∀ i j, |unflatten n.eval n.eval (WL.map (dec tag)) i j| ≤ 1 + u tag) ∧
      (u tag < 1 → IsLUErr (roundingFactor (n.eval + 4) (u tag))
        (M.submatrix (luPivotPermutation history n.eval) id)
        (unflatten n.eval n.eval (WL.map (dec tag)))
        (unflatten n.eval n.eval (WU.map (dec tag)))) ∧
      HoldsDecoded out.store dec tag L lo.eval (unflatten n.eval n.eval (WL.map (dec tag))) ∧
      HoldsDecoded out.store dec tag U uo.eval (unflatten n.eval n.eval (WU.map (dec tag))) ∧
      HoldsDecoded out.store dec tag A ao.eval M := by
  let Q : Store P K → Prop := fun store => ∃ (WL WU WH : Array K)
      (history : Fin n.eval → Fin n.eval),
    WL.size = n.eval * n.eval ∧ WU.size = n.eval * n.eval ∧ WH.size = n.eval ∧
    st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
      (H, ho.eval, n.eval)] [WL, WU, WH] = some store ∧
    ReadsDecoded store dec tag H ho.eval (fun j => ((history j).val : ℝ)) ∧
    (∀ j, j ≤ history j) ∧
    (unflatten n.eval n.eval (WL.map (dec tag))).IsLowerTriangular ∧
    (∀ j, unflatten n.eval n.eval (WL.map (dec tag)) j j = 1) ∧
    (unflatten n.eval n.eval (WU.map (dec tag))).IsUpperTriangular ∧
    (∀ i j, |unflatten n.eval n.eval (WL.map (dec tag)) i j| ≤ 1 + u tag) ∧
    (u tag < 1 → IsLUErr (roundingFactor (n.eval + 4) (u tag))
      (M.submatrix (luPivotPermutation history n.eval) id)
      (unflatten n.eval n.eval (WL.map (dec tag)))
      (unflatten n.eval n.eval (WU.map (dec tag)))) ∧
    HoldsDecoded store dec tag L lo.eval (unflatten n.eval n.eval (WL.map (dec tag))) ∧
    HoldsDecoded store dec tag U uo.eval (unflatten n.eval n.eval (WU.map (dec tag)))
  obtain ⟨out, hr, WL, WU, WH, history, hLs, hUs, hHs, hw, hlog, hp, hlower, hdiag,
      hupper, hbound, herr, hF, hG⟩ := exists_exec_alloc I tag (n * n)
    (fun S => ((do
      copyv tag A ao S 0 (n * n)
      forRange (n * n) fun i => Builder.ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => Builder.ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        partialPivot tag n (.var k) S 0 ⟨H, ho + IExp.var k⟩
        bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
          swapRows tag n n L lo (.var k) (.var selected)
        luColumnTotal tag n (.var k) S L U 0 lo uo
        schurStepTotal tag n S 0 (.var k)) : Builder P ι ℕ ℕ Unit).run) st Q (by
      intro σ hσ
      obtain ⟨final, hrun, hs⟩ := PLURounding.exec_body I h n hi tag st.store σ A L U H
        ao lo uo ho M hM hL hU hH hLU hLH hUH
        (by simpa only [IExp.eval_mul] using hσ)
      obtain ⟨WL, WU, WH, history, hresult⟩ := PLURounding.State.writeBlocks_pop
        (hσ ▸ hs) hL hU hH hLU hLH hUH (h.nonneg (p := tag) trivial)
      exact ⟨final, hrun, WL, WU, WH, history, hresult⟩)
  refine ⟨out, WL, WU, WH, history, ?_, hLs, hUs, hHs, hw, hlog, hp, hlower, hdiag,
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
      rcases hblock with rfl | rfl | rfl
      · exact Or.inl (hAL hN)
      · exact Or.inl (hAU hN)
      · exact Or.inl (hAH hN))]
    exact hwM

/-- The actual stored partial-pivoted driver supplies a rounded row-pivoted LU routine
certificate at the standard saved-pivot budget $\gamma_{N+4}$. The scalar model has every
result in range, bounded index literals and conversion are exact, and $u_p<1$. Input, factors
and log occupy separate buffers; arbitrary offsets and singular/empty inputs are admitted.
[Higham2002, §9.3; CarsonMaShao2026, Lemma 2]. -/
theorem isPLURoutine_pluFactor_of_isRelErrSem {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (tag : P) {N : ℕ} (hi : IsIndexExactSem dec N I.sem) (hu : u tag < 1)
    (A : Matrix (Fin N) (Fin N) ℝ) (Ab Lb Ub Pb : ℕ) (ao lo uo po : IExp ℕ)
    (hAL : Ab ≠ Lb) (hAU : Ab ≠ Ub) (hAP : Ab ≠ Pb)
    (hLU : Lb ≠ Ub) (hLP : Lb ≠ Pb) (hUP : Ub ≠ Pb) :
    IsPLURoutine I dec tag A (roundingFactor (N + 4) (u tag))
      (fun s => HoldsDecoded s dec tag Ab ao.eval A) Lb Ub Pb lo uo po
      (pluFactor tag (.const N) Ab Lb Ub Pb ao lo uo po) where
  composable := executionComposable_pluFactor I tag (.const N) Ab Lb Ub Pb ao lo uo po
  run st hA hw _ _ _ := by
    obtain ⟨out, WL, WU, WH, history, hr, hLs, hUs, hHs, hs, hlog, hp, -, -, -, -, herr, -⟩ :=
      h.exec_pluFactor I (.const N) hi tag st Ab Lb Ub Pb ao lo uo po A hA
        (hw _ List.mem_cons_self) (hw (Ub, uo.eval, N * N) (by simp))
        (hw (Pb, po.eval, N) (by simp)) hLU hLP hUP
        (fun _ => hAL) (fun _ => hAU) (fun _ => hAP)
    exact ⟨out, WL, WU, WH, history, hLs, hUs, hHs, hr, hs, hlog, hp, herr hu⟩

end NLAlib.Computation
