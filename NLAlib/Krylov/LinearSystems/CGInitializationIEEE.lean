/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.IEEE
public import NLAlib.Krylov.LinearSystems.CGOracleProgramRoundedInitialization
-- Reveal the logical scientific-literal conversion for the checked constants zero and one.
import all Init.Data.OfScientific

/-!
# Literal and copy initialization of CG with finite binary64 words

The existing stored and oracle CG setup APIs require only the actual flag words and their
literal, negation and decoding facts. Checked binary64 supplies exact zero and one literals
and exact negation, so the pre-dot setup executes for arbitrary finite input words in every
dimension. The stored routine additionally loads the supplied ROM words.

These are executions of the actual existing setup blocks, retaining their buffer reads.
No global relative arithmetic model, dot-kernel success or initialized numerical trajectory
is assumed. The unit-charge hypothesis concerns operation accounting independently of values.

## Main results

* `NLAlib.CGImplementation.exists_cg_flag_words_of_sem_eq_finiteFloatSem`:
  the actual finite binary64 flag words are produced with zero literal error.
* `NLAlib.CGImplementation.exec_rounded_setup_of_sem_eq_finiteFloatSem`:
  stored CG setup for arbitrary input and ROM words.
* `NLAlib.CGOracleImplementation.exec_rounded_setup_of_sem_eq_finiteFloatSem`:
  matrix-free CG setup for arbitrary input words.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation Computation.Builder

/-- Checked binary64 supplies exact zero and one literals and an exact negative flag.
The returned words carry their actual literal and negation execution equations. Literal
error is zero, without an assumption about any arithmetic operation or input range. -/
theorem exists_cg_flag_words_of_sem_eq_finiteFloatSem {ι C : Type}
    (I : Interp Unit ι FiniteFloat C) (hsem : I.sem = finiteFloatSem) :
    ∃ zero one negative : FiniteFloat,
      I.sem.lit () 0 = some zero ∧ floatDecode zero.val = 0 ∧
      I.sem.lit () 1 = some one ∧ 0 < floatDecode one.val ∧
      |floatDecode one.val - 1| ≤ 0 ∧
      I.sem.un () .neg one = some negative ∧
      floatDecode negative.val = -floatDecode one.val := by
  apply exists_cg_flag_words (u := fun _ => 0)
    (dec := fun _ (x : FiniteFloat) => floatDecode x.val) I ()
  · refine ⟨finiteFloatZero, ?_, floatDecode_finiteFloatZero⟩
    rw [hsem]
    rfl
  · refine ⟨finiteFloatOne, ?_, ?_⟩
    · rw [hsem]
      rfl
    · exact ⟨0, by norm_num, by rw [floatDecode_finiteFloatOne]; norm_num⟩
  · intro x
    rw [hsem]
    exact isArithErrSem_finiteFloatSem.neg () x
  · norm_num

/-- The actual stored CG pre-dot setup executes with finite binary64 words in every dimension.
The input words and supplied ROM words are arbitrary. ROM availability and workspace capacity
are retained; the flag literals are exact, and no global arithmetic accuracy
or future-success hypothesis is used. -/
theorem exec_rounded_setup_of_sem_eq_finiteFloatSem {ι : Type}
    (I : Interp Unit ι FiniteFloat (OpCount Unit ι)) (hsem : I.sem = finiteFloatSem)
    (hc : IsUnitCharge I)
    (st : St Unit FiniteFloat (OpCount Unit ι)) (N : ℕ) (b : Fin N → FiniteFloat)
    (vals : ℕ → FiniteFloat)
    (hshape : st.store.shape = workspaceShape () N)
    (hb : ∀ i : Fin N, st.store.read () 0 i = some (b i))
    (hrom : ∀ i < N * N, I.rom i = some (vals i)) :
    ∃ (out : St Unit FiniteFloat (OpCount Unit ι)) (zero one negative : FiniteFloat),
      exec I (do
        forRange (IExp.const N * IExp.const N) fun i => stmt (.rom () ⟨5, .var i⟩ (.var i))
        ins (.lit () ⟨7, 6⟩ 0)
        ins (.lit () ⟨7, 7⟩ 1)
        ins (.un () .neg ⟨7, 8⟩ ⟨7, 7⟩)
        ins (.copy () ⟨4, 0⟩ ⟨7, 6⟩)
        forRange (.const N) fun i => ins (.lit () ⟨1, .var i⟩ 0)
        copyv () 0 0 2 0 (.const N)
        copyv () 0 0 3 0 (.const N)).run st = some out ∧
      out.store.shape = workspaceShape () N ∧
      Holds out.store () 5 0 (fun i j : Fin N => vals (i + N * j)) ∧
      (∀ i : Fin N, out.store.read () 0 i = some (b i)) ∧
      (∀ i : Fin N, out.store.read () 1 i = some zero) ∧
      (∀ i : Fin N, out.store.read () 2 i = some (b i)) ∧
      (∀ i : Fin N, out.store.read () 3 i = some (b i)) ∧
      out.store.read () 7 6 = some zero ∧ out.store.read () 7 7 = some one ∧
      out.store.read () 7 8 = some negative ∧ out.store.read () 4 0 = some zero ∧
      floatDecode zero.val = 0 ∧ 0 < floatDecode one.val ∧ |floatDecode one.val - 1| ≤ 0 ∧
      floatDecode negative.val = -floatDecode one.val := by
  obtain ⟨zero, one, negative, hz, hd0, ho, hpos, herr, hn, hdn⟩ :=
    CGImplementation.exists_cg_flag_words_of_sem_eq_finiteFloatSem I hsem
  exact exec_rounded_setup (u := fun _ => 0)
    (dec := fun _ (x : FiniteFloat) => floatDecode x.val) I () zero one negative
    hz hd0 ho hpos herr hn hdn hc st N b vals hshape hb hrom

end NLAlib.CGImplementation

namespace NLAlib.CGOracleImplementation

open Computation Computation.Builder CGImplementation

/-- The actual oracle CG pre-dot setup executes with finite binary64 words in every dimension.
The input words are arbitrary. Workspace capacity is retained; the flag literals are exact,
and no global arithmetic accuracy or future-success hypothesis is used. -/
theorem exec_rounded_setup_of_sem_eq_finiteFloatSem {ι : Type}
    (I : Interp Unit ι FiniteFloat (OpCount Unit ι)) (hsem : I.sem = finiteFloatSem)
    (hc : IsUnitCharge I)
    (st : St Unit FiniteFloat (OpCount Unit ι)) (N : ℕ) (b : Fin N → FiniteFloat)
    (hshape : st.store.shape = workspaceShape () N false)
    (hb : ∀ i : Fin N, st.store.read () 0 i = some (b i))
    :
    ∃ (out : St Unit FiniteFloat (OpCount Unit ι)) (zero one negative : FiniteFloat),
      exec I (do
        ins (.lit () ⟨7, 6⟩ 0)
        ins (.lit () ⟨7, 7⟩ 1)
        ins (.un () .neg ⟨7, 8⟩ ⟨7, 7⟩)
        ins (.copy () ⟨4, 0⟩ ⟨7, 6⟩)
        forRange (.const N) fun i => ins (.lit () ⟨1, .var i⟩ 0)
        copyv () 0 0 2 0 (.const N)
        copyv () 0 0 3 0 (.const N)).run st = some out ∧
      out.store.shape = workspaceShape () N false ∧
      (∀ i : Fin N, out.store.read () 0 i = some (b i)) ∧
      (∀ i : Fin N, out.store.read () 1 i = some zero) ∧
      (∀ i : Fin N, out.store.read () 2 i = some (b i)) ∧
      (∀ i : Fin N, out.store.read () 3 i = some (b i)) ∧
      out.store.read () 7 6 = some zero ∧ out.store.read () 7 7 = some one ∧
      out.store.read () 7 8 = some negative ∧ out.store.read () 4 0 = some zero ∧
      floatDecode zero.val = 0 ∧ 0 < floatDecode one.val ∧ |floatDecode one.val - 1| ≤ 0 ∧
      floatDecode negative.val = -floatDecode one.val := by
  obtain ⟨zero, one, negative, hz, hd0, ho, hpos, herr, hn, hdn⟩ :=
    CGImplementation.exists_cg_flag_words_of_sem_eq_finiteFloatSem I hsem
  exact exec_rounded_setup (u := fun _ => 0)
    (dec := fun _ (x : FiniteFloat) => floatDecode x.val) I () zero one negative
    hz hd0 ho hpos herr hn hdn hc st N b hshape hb

end NLAlib.CGOracleImplementation
