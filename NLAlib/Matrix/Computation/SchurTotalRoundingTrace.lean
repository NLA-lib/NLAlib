/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.GuardedElimination
public import NLAlib.Matrix.Computation.SchurRounding
public import NLAlib.Computation.MatrixStorage

/-!
# Actual guarded Schur execution and its rounding witnesses

A decoded zero pivot takes the actual skip branch and returns the original decoded matrix.
The nonzero branch retains the local literal, division, multiplication and addition witnesses
of the saved-pivot update. No successful-run premise or fictitious zero-branch intermediate
is used. This supports the rounded LU prefix recurrence.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_schurStepTotal_trace`: total execution, one output
  block write and the actual branch's numerical guarantee.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

namespace SchurTotalRoundingTrace

private abbrev TraceResult {N : ℕ} (u : ℝ) (r : Fin N)
    (M M' : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (M r r = 0 ∧ M' = M) ∨ (M r r ≠ 0 ∧
    ∃ (ell c : ℝ) (t : Fin N → ℝ) (q : Matrix (Fin N) (Fin N) ℝ),
      RelErr u (-1) ell ∧ RelErr u (ell / M r r) c ∧
      (∀ j, RelErr u (c * M r j) (t j)) ∧
      ∀ i j, RelErr u (M i r * t j) (q i j) ∧ RelErr u (M i j + q i j) (M' i j))

private theorem holdsDecoded_of_writeBlock {N : ℕ} {dec : P → K → ℝ} {p : P}
    {R off : ℕ} {initial final : Store P K} {W : Array K}
    (hw : initial.writeBlock p R off W = some final) (hWs : W.size = N * N) :
    HoldsDecoded final dec p R off (unflatten N N (W.map (dec p))) := by
  intro i j
  have ht : i.val + N * j.val < W.size :=
    hWs ▸ Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt
  refine ⟨W[i.val + N * j.val], ?_, ?_⟩
  · simpa only [Nat.add_assoc, Array.getElem?_eq_getElem ht] using
      Store.read_of_writeBlock_eq_some_of_lt hw ht
  · simp only [unflatten, Matrix.of_apply, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_eq_getElem ht, Option.map_some, Option.getD_some]

private theorem exec_schurStepTotal_body {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (initial : Store P K) (st : St P K C) (n : IExp ℕ) (R : ℕ) (off k : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : HoldsDecoded initial dec p R off.eval M)
    (hst : st.store = initial.push (p, Array.replicate 1 none)) :
    ∃ (out : St P K C) (W : Array K), exec I (do
      ins (.lit p ⟨initial.size, 0⟩ 0)
      ifThenElse p .eq ⟨R, off + k + n * k⟩ ⟨initial.size, 0⟩
        (pure ()) (schurStep p n R off k)).run st = some out ∧
      W.size = n.eval * n.eval ∧ initial.writeBlock p R off.eval W = some out.store.pop ∧
      TraceResult (u p) ⟨k.eval, hk⟩ M
        (unflatten n.eval n.eval (W.map (dec p))) := by
  classical
  let r : Fin n.eval := ⟨k.eval, hk⟩
  choose Mw hMw hdMw using hM
  change Matrix (Fin n.eval) (Fin n.eval) K at Mw
  have hraw : Holds initial p R off.eval Mw := hMw
  have hRb := Store.lt_size_of_read_eq_some (hMw r r)
  obtain ⟨z, hz⟩ := h.lit_ok p 0 trivial
  have hdz : dec p z = 0 := by
    obtain ⟨δ, -, hd⟩ := h.lit_err p 0 z hz
    simpa only [Rat.cast_zero, zero_mul] using hd
  obtain ⟨s₀, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape z
    (hst ▸ Store.getElem?_shape_push_size initial p 1) (by omega : 0 < 1)
  let ready : St P K C := { st with store := s₀, cnt := st.cnt + I.charge (.lit p) }
  let tested : St P K C := { ready with cnt := ready.cnt + I.charge (.cmp p) }
  have hM₀ : HoldsDecoded s₀ dec p R off.eval M := by
    intro i j
    refine ⟨Mw i j, ?_, hdMw i j⟩
    rw [Store.read_of_write_eq_some_of_ne hw (Or.inl (Nat.ne_of_lt hRb)), hst,
      Store.read_push_of_lt hRb]
    exact hMw i j
  obtain ⟨pw, hpw, hdp⟩ := hM₀ r r
  change s₀.read p R (off.eval + k.eval + n.eval * k.eval) = some pw at hpw
  have hcmp : cmpStep I p .eq ⟨R, off + k + n * k⟩ ⟨initial.size, 0⟩ ready =
      some (decide (M r r = 0), tested) := by
    simp only [cmpStep, ready, IExp.eval_add, IExp.eval_mul, IExp.eval_zero,
      hpw, Store.read_of_write_eq_some hw, Option.bind_some, h.cmp_eq, hdp, hdz]
    rfl
  have hpop : s₀.pop = initial := by
    rw [Store.pop_of_write_top hw (by simp only [hst, Array.size_push]; omega), hst]
    exact Array.pop_push
  have hsize : s₀.size = initial.size + 1 :=
    (Store.size_of_write_eq_some hw).trans (by simp only [hst, Array.size_push])
  have run_eq : ∀ out,
      exec I (.ite p .eq ⟨R, off + k + n * k⟩ ⟨initial.size, 0⟩
        .skip (schurStep p n R off k).run) ready = some out →
      exec I (do
        ins (.lit p ⟨initial.size, 0⟩ 0)
        ifThenElse p .eq ⟨R, off + k + n * k⟩ ⟨initial.size, 0⟩
          (pure ()) (schurStep p n R off k)).run st = some out := by
    intro out hr
    change exec I (.seq (.instr (.lit p ⟨initial.size, 0⟩ 0))
      (.seq (.ite p .eq ⟨R, off + k + n * k⟩ ⟨initial.size, 0⟩
        .skip (schurStep p n R off k).run) .skip)) st = some out
    rw [exec_seq_instr_lit I hz hw, exec_seq_skip]
    exact hr
  by_cases hp : M r r = 0
  · obtain ⟨W, hWs, -, hentry, hself⟩ := hraw.exists_array
    refine ⟨tested, W, run_eq _ ?_, hWs,
      by simpa only [tested, ready, hpop] using hself, Or.inl ⟨hp, ?_⟩⟩
    · rw [exec_ite, hcmp]
      simp only [hp, decide_true, Option.bind_some, ↓reduceIte, exec_skip]
    · ext i j
      simp only [unflatten, Matrix.of_apply, Array.getD_eq_getD_getElem?, Array.getElem?_map,
        hentry i j, Option.map_some, Option.getD_some, hdMw]
  · obtain ⟨out, W, ell, c, t, q, hr, hWs, hm, htrace⟩ :=
      h.exec_schurStep I p tested n R off k M hk hM₀ hp
    refine ⟨out, W, run_eq _ ?_, hWs, ?_, Or.inr ⟨hp, ell, c, t, q, htrace⟩⟩
    · rw [exec_ite, hcmp]
      simpa only [hp, decide_false, Option.bind_some, Bool.false_eq_true, ↓reduceIte] using hr
    · have hh := Store.writeBlock_pop_of_lt hm (fun _ => by
        change R + 1 < s₀.size
        omega)
      simpa only [tested, ready, hpop] using hh

end SchurTotalRoundingTrace

/-- The actual guarded Schur step succeeds under the standard scalar model for every
stored decoded matrix. Its zero branch leaves the decoded matrix unchanged. Its nonzero
branch returns the actual saved-pivot literal/division and rank-one update error witnesses.
Exactly one complete matrix block is written and all scratch is released. No upper bound
on roundoff or nonsingularity premise is required. [Higham2002, §2.2; GolubVanLoan2013, §3.2]. -/
theorem IsRelErrSem.exec_schurStepTotal_trace {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (R : ℕ) (off k : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : HoldsDecoded st.store dec p R off.eval M) :
    ∃ (out : St P K C) (W : Array K), exec I (schurStepTotal p n R off k).run st = some out ∧
      W.size = n.eval * n.eval ∧ st.store.writeBlock p R off.eval W = some out.store ∧
      HoldsDecoded out.store dec p R off.eval (unflatten n.eval n.eval (W.map (dec p))) ∧
      ((M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ = 0 ∧ unflatten n.eval n.eval (W.map (dec p)) = M) ∨
        (M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ ≠ 0 ∧
          ∃ (ell c : ℝ) (t : Fin n.eval → ℝ) (q : Matrix (Fin n.eval) (Fin n.eval) ℝ),
            RelErr (u p) (-1) ell ∧ RelErr (u p) (ell / M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩) c ∧
            (∀ j, RelErr (u p) (c * M ⟨k.eval, hk⟩ j) (t j)) ∧
            ∀ i j, RelErr (u p) (M i ⟨k.eval, hk⟩ * t j) (q i j) ∧
              RelErr (u p) (M i j + q i j) (unflatten n.eval n.eval (W.map (dec p)) i j))) := by
  obtain ⟨out, hr, W, hWs, hw, htrace⟩ := exists_exec_alloc I p 1 (fun zbuf => ((do
    ins (.lit p ⟨zbuf, 0⟩ 0)
    ifThenElse p .eq ⟨R, off + k + n * k⟩ ⟨zbuf, 0⟩
      (pure ()) (schurStep p n R off k)) : Builder P ι ℕ ℕ Unit).run) st
    (fun s => ∃ W : Array K, W.size = n.eval * n.eval ∧
      st.store.writeBlock p R off.eval W = some s ∧
      SchurTotalRoundingTrace.TraceResult (u p) ⟨k.eval, hk⟩ M
        (unflatten n.eval n.eval (W.map (dec p))))
    (fun σ hσ => by
      obtain ⟨out, W, hr, hs⟩ := SchurTotalRoundingTrace.exec_schurStepTotal_body
        I h p st.store σ n R off k M hk hM hσ
      exact ⟨out, hr, W, hs⟩)
  refine ⟨out, W, ?_, hWs, hw,
    SchurTotalRoundingTrace.holdsDecoded_of_writeBlock hw hWs, htrace⟩
  change exec I (.seq (.alloc p 1 _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

end NLAlib.Computation
