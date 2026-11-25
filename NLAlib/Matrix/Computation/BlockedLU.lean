/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.BlockedLUExecution
public import NLAlib.Matrix.Computation.LURoutine

/-!
# Stored blocked LU with BLAS3 trailing updates

The input is copied before either factor is cleared. Each clipped panel uses two packed GER
rectangles per pivot, followed by one GEMM-backed trailing update. The symbolic positive block
size and ceiling block count control the actual loops, including a final partial panel.

## Main definitions

* `NLAlib.Computation.blockedLuFactor`: the actual blocked unpivoted LU driver.

## Main results

* `NLAlib.Computation.exec_blockedLuFactor`: exact successful factorization and complete frame.
* `NLAlib.Computation.exec_blockedLuFactor_of_zero`: handle-free empty execution and store return.
* `NLAlib.Computation.isLURoutine_blockedLuFactor`: typed zero-error factorization certificate.
-/

@[expose] public section

namespace NLAlib.Computation

open scoped Matrix
open Builder

/-- Factor a square matrix without pivoting using clipped panels and true GEMM-backed trailing
updates. The caller supplies a positive block size and its symbolic ceiling block count.
Copying the source to the scoped residual before clearing either factor permits input/output
overlap. Nonzero canonical pivots are the exact execution premise. [GolubVanLoan2013, §3.2]. -/
def blockedLuFactor {P ι VB VI : Type} (p : P) (n b q : IExp VI) (A L U : VB)
    (ao lo uo : IExp VI) : Builder P ι VB VI Unit := scope do
  let S ← alloc p (n * n)
  copyv p A ao S 0 (n * n)
  forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
  forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)
  forRange q fun block => do
    let start := b * IExp.var block
    let width := b - (b - (n - start))
    luPanel p n start width S L U lo uo
    trailingSchurUpdate p n start width L U S lo uo 0

variable {P ι : Type} [DecidableEq P]

/-- Every residual, panel and packed trailing workspace is released before the continuation. -/
theorem executionComposable_blockedLuFactor {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (p : P) (n b q : IExp ℕ) (A L U : ℕ) (ao lo uo : IExp ℕ) :
    ExecutionComposable I (blockedLuFactor p n b q A L U ao lo uo) :=
  executionComposable_single I (fun _ => rfl)

/-- At dimension zero the actual full driver restores the original store without scalar-model,
capacity or buffer-separation premises. This includes coincident invalid output handles and
permits an outer routine's empty output handle to equal its fresh scoped workspace. -/
theorem exec_blockedLuFactor_of_zero {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (p : P) (st : St P K C) (n b q : IExp ℕ)
    (A L U : ℕ) (ao lo uo : IExp ℕ) (hn : n.eval = 0) (hb : 0 < b.eval)
    (hq : q.eval = (n.eval + b.eval - 1) / b.eval) :
    ∃ out, exec I (blockedLuFactor p n b q A L U ao lo uo).run st = some out ∧
      out.store = st.store := by
  obtain ⟨out, hex, hout⟩ := exists_exec_alloc I p (n * n)
    (fun S => ((do
      copyv p A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)
      forRange q fun block => do
        let start := b * IExp.var block
        let width := b - (b - (n - start))
        luPanel p n start width S L U lo uo
        trailingSchurUpdate p n start width L U S lo uo 0) : Builder P ι ℕ ℕ Unit).run)
    st (fun store => store = st.store) (by
      intro σ hσ
      exact ⟨σ, BlockedLU.exec_body_of_zero I p σ n b q A st.store.size L U ao lo uo hn hb hq,
        by rw [hσ, Array.pop_push]⟩)
  refine ⟨out, ?_, hout⟩
  change exec I (.seq (.alloc p (n * n) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hex

/-- Nonzero canonical pivots suffice for actual blocked LU success, canonical exact factors
and exactly their two original-store writes. The input may overlap either output; if it is
separate from both, it is retained. Empty inputs require no valid handles. The block size is
positive and the supplied count is its exact ceiling quotient. No rounded-error claim is
made for this exact-semantics routine. [GolubVanLoan2013, §3.2]. -/
theorem exec_blockedLuFactor (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n b q : IExp ℕ) (A L U : ℕ) (ao lo uo : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hb : 0 < b.eval)
    (hq : q.eval = (n.eval + b.eval - 1) / b.eval)
    (hp : ∀ r : Fin n.eval, gaussState M r.val r r ≠ 0) (hM : Holds st.store p A ao.eval M)
    (hL : Writable st.store p L lo.eval (n.eval * n.eval))
    (hU : Writable st.store p U uo.eval (n.eval * n.eval)) (hLU : L ≠ U) :
    ∃ out, exec I (blockedLuFactor p n b q A L U ao lo uo).run st = some out ∧
      st.store.writeBlocks p [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
        [flatten (luLower M), flatten (luUpper M)] = some out.store ∧
      IsLU M (luLower M) (luUpper M) ∧ Holds out.store p L lo.eval (luLower M) ∧
      Holds out.store p U uo.eval (luUpper M) ∧
      ((0 < n.eval → A ≠ L) → (0 < n.eval → A ≠ U) → Holds out.store p A ao.eval M) := by
  let Q := fun store => st.store.writeBlocks p
      [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
      [flatten (luLower M), flatten (luUpper M)] = some store ∧
    Holds store p L lo.eval (luLower M) ∧ Holds store p U uo.eval (luUpper M)
  obtain ⟨out, hex, hw, hLf, hUf⟩ := exists_exec_alloc I p (n * n)
    (fun S => ((do
      copyv p A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)
      forRange q fun block => do
        let start := b * IExp.var block
        let width := b - (b - (n - start))
        luPanel p n start width S L U lo uo
        trailingSchurUpdate p n start width L U S lo uo 0) : Builder P ι ℕ ℕ Unit).run)
    st Q (by
      intro σ hσ
      obtain ⟨final, hrun, hs⟩ := BlockedLU.exec_body I hI hc p st.store σ n b q A L U
        ao lo uo M hb hq hp hM hL hU hLU (by simpa only [IExp.eval_mul] using hσ)
      obtain ⟨hw, hLf, hUf⟩ := BlockedLU.State.writeBlocks_pop (hσ ▸ hs) hL hU hLU
      exact ⟨final, hrun, hw, hLf, hUf⟩)
  refine ⟨out, ?_, hw, ?_, hLf, hUf, ?_⟩
  · change exec I (.seq (.alloc p (n * n) _) .skip) st = some out
    rw [exec_seq_skip]
    exact hex
  · exact isLU_luLower_luUpper (fun r _ => by rw [luUpper_apply_self]; exact hp r)
  · intro hAL hAU i j
    have hN := Nat.zero_lt_of_lt i.isLt
    rw [Store.read_of_writeBlocks_eq_some_of_forall hw (fun block hblock => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
      rcases hblock with rfl | rfl
      · exact Or.inl (hAL hN)
      · exact Or.inl (hAU hN))]
    exact hM i j

/-- The actual blocked driver supplies an ordinary zero-error LU routine certificate under
exact semantics, nonzero canonical pivots and standard charges. Input/output overlap is
permitted because the input is copied before clearing either factor. [GolubVanLoan2013, §3.2]. -/
theorem isLURoutine_blockedLuFactor (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hp : ∀ r : Fin N, gaussState A r.val r r ≠ 0)
    (b q : IExp ℕ) (hb : 0 < b.eval) (hq : q.eval = (N + b.eval - 1) / b.eval)
    (Ab Lb Ub : ℕ) (ao lo uo : IExp ℕ) (hLU : Lb ≠ Ub) :
    IsLURoutine I (fun _ x => x) p A 0 (fun s => Holds s p Ab ao.eval A) Lb Ub lo uo
      (blockedLuFactor p (.const N) b q Ab Lb Ub ao lo uo) where
  composable := executionComposable_blockedLuFactor I p (.const N) b q Ab Lb Ub ao lo uo
  run st hA hL hU _ := by
    obtain ⟨out, hex, hw, hfactor, _, _, _⟩ := exec_blockedLuFactor I hI hc p st (.const N)
      b q Ab Lb Ub ao lo uo A hb hq hp hA hL hU hLU
    obtain ⟨hLs, hUs, mid, hwL, hwU⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
    refine ⟨out, flatten (luLower A), flatten (luUpper A), mid,
      size_flatten _, size_flatten _, hex, hwL, hwU, ?_⟩
    rw [Array.map_id', Array.map_id', unflatten_flatten, unflatten_flatten]
    exact hfactor.isLUErr

end NLAlib.Computation
