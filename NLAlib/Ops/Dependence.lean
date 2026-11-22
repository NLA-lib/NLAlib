/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.CallSupport
public import NLAlib.Ops.Cert
public import NLAlib.Ops.Confined
public import NLAlib.Ops.RoutineProblem

/-!
# What a run depends on

A certificate is about the run of a fixed tree from the supplied buffers. These theorems say what
that run can depend on, for every tree, so that a reader does not have to ask of each program
whether data reached it by a route that is not declared.

A run is given by the tree, the sizes, the supplied buffers, the tape and the interpretation of
the operations, and by nothing else: these are the arguments of
`NLAlib.Ops.Reference.Execution`. The data of a problem that is in no buffer is not among them.
It can therefore reach a run only through the interpretation, that is, through which
interpretations the contracts of the model allow at that input. The theorems below make each
step of this a statement.

* **The tree.** The interpretation reaches a run only at a call, a test or an index use of the
  tree: two interpretations that agree on the operations a tree calls, and on the tests, derive
  the same outcomes (`NLAlib.Ops.Reference.derives_congr_of_allOps`).
* **The input.** A run starts from the supplied buffers: two inputs with the same buffers have
  the same runs and the same resident payload
  (`NLAlib.Ops.Specification.accepts_congr_of_buffers`).
* **A uniform model.** The contracts do not depend on the input, so one run from given buffers
  meets the output condition of every input that has those buffers
  (`NLAlib.Ops.Algorithm.good_of_buffers_eq`). The output cannot depend on data that is in no
  buffer.
* **Declared oracles.** With the oracles of a model declared (`NLAlib.Ops.Inputs.Oracles`), two
  inputs with the same buffers can be told apart only by an oracle: a run under an interpretation
  whose declared oracles are also allowed at the other input meets the output condition of both
  (`NLAlib.Ops.Inputs.Oracles.good_of_satisfies`), and so does every run of a tree that calls no
  declared oracle (`NLAlib.Ops.Inputs.Oracles.good_of_allOps`).

## What these theorems do not say

* They do not bound what a contract may compute from its operands, or what it costs: that is the
  content of the model, which a reader checks (`NLAlib.Ops.AccessModel.Confined` says that every
  contract reads and writes only its operand blocks, `NLAlib.Ops.AccessModel.Charged` that every
  call has positive work).
* They say nothing of a model that is neither uniform nor has its oracles declared. There the
  conclusion fails: `NLAlib.Ops.Examples.Oracles.oracleAlgorithm` is a certificate whose two
  inputs have the same buffers and no common output
  (`NLAlib.Ops.Examples.Oracles.not_good_oracleInput_zero_one`).
* The parameters of a certificate (a matrix that a contract of the model mentions, a unit
  roundoff) are not inputs of the problem; they are in the statement of the certificate.
* The resource bounds of a specification are functions of the sizes alone, by the type of
  `NLAlib.Ops.Specification`: a bound cannot depend on the data. The count of one run can, through
  the tests of the tree.

## Main results

* `NLAlib.Ops.Reference.derives_congr_of_allOps`, `NLAlib.Ops.Reference.execution_congr_of_allOps`:
  a run depends on the interpretation only through the operations its tree calls and the tests.
* `NLAlib.Ops.Specification.accepts_congr_of_buffers`: a run depends on the input only through
  the supplied buffers.
* `NLAlib.Ops.Algorithm.good_of_contracts`, `NLAlib.Ops.Algorithm.good_of_buffers_eq`: one run
  meets the output condition of every input with the same buffers at which its interpretation is
  allowed; in a uniform model, of every input with the same buffers.
* `NLAlib.Ops.Inputs.Oracles.good_of_satisfies`, `NLAlib.Ops.Inputs.Oracles.good_of_allOps`: data
  in no buffer reaches a run only through a declared oracle.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-! ### The tree: the interpretation is reached only at calls and tests -/

namespace Reference

variable {I J : Interp Op Tst K} {R : ResourceModel Op Tst} {τ : Tape K}

private theorem repeats_of_derives {body : Stmt Op Tst}
    (ih : ∀ ρ a c, Derives I R τ body ρ a c → Derives J R τ body ρ a c) {ρ : Env} :
    ∀ {k : ℕ} {a c : State Op Tst K}, Repeats I R τ body ρ k a c →
      Repeats J R τ body ρ k a c := by
  intro k
  induction k with
  | zero =>
    intro a c h
    cases h
    exact .zero _ _ _
  | succ n ihn =>
    intro a c h
    cases h with
    | succ hp hb => exact .succ (ihn hp) (ih _ _ _ hb)

private theorem while_of_derives (htest : I.test = J.test) {q : Tst} {ds : List IExp}
    {ins : List Operand} {body : Stmt Op Tst}
    (ih : ∀ ρ a c, Derives I R τ body ρ a c → Derives J R τ body ρ a c) {ρ : Env} :
    ∀ {n i j : ℕ} {a c : State Op Tst K}, While I R τ q ds ins body ρ n i a j c →
      While J R τ q ds ins body ρ n i a j c := by
  intro n
  induction n with
  | zero =>
    intro i j a c h
    cases h
    exact .cap _ _ _ _ _ _ _
  | succ n ihn =>
    intro i j a c h
    cases h with
    | stop hd hx hq => exact .stop hd hx (by rw [← htest]; exact hq)
    | step hd hx hq hb hw =>
      exact .step hd hx (by rw [← htest]; exact hq) (ih _ _ _ hb) (ihn hw)

private theorem derives_of_allOps (p : Op → Bool)
    (hcall : ∀ o, p o = true → I.call o = J.call o) (htest : I.test = J.test)
    (hindex : I.index = J.index) :
    ∀ s : Stmt Op Tst, s.allOps p = true → ∀ ρ a c,
      Derives I R τ s ρ a c → Derives J R τ s ρ a c := by
  intro s
  induction s with
  | skip =>
    intro _ ρ a c h
    cases h
    exact .skip ρ a
  | abort =>
    intro _ ρ a c h
    cases h
  | seq s t ihs iht =>
    intro hs ρ a c h
    simp only [Stmt.allOps, Bool.and_eq_true] at hs
    cases h with
    | seq h₁ h₂ => exact .seq (ihs hs.1 _ _ _ h₁) (iht hs.2 _ _ _ h₂)
  | call o ds ins outs =>
    intro hs ρ a c h
    cases h with
    | call hd hx hy hl hr hshape =>
      exact .call hd hx hy hl (by rw [← hcall o hs]; exact hr) hshape
  | ite q ds ins s t ihs iht =>
    intro hs ρ a c h
    simp only [Stmt.allOps, Bool.and_eq_true] at hs
    cases h with
    | ite hd hx hq hb =>
      rename_i d xs v
      refine .ite hd hx (by rw [← htest]; exact hq) ?_
      cases v <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
      · exact iht hs.2 _ _ _ hb
      · exact ihs hs.1 _ _ _ hb
  | whileFuel fuel q ds ins body next ihb ihn =>
    intro hs ρ a c h
    simp only [Stmt.allOps, Bool.and_eq_true] at hs
    cases h with
    | whileFuel hn hw hk =>
      exact .whileFuel hn (while_of_derives htest (ihb hs.1) hw) (ihn hs.2 _ _ _ hk)
  | bindIdx q ins bound body ih =>
    intro hs ρ a c h
    cases h with
    | bindIdx hx hn hq hv hb =>
      exact .bindIdx hx hn (by rw [← hindex]; exact hq) hv (ih hs _ _ _ hb)
  | allocAs fmt len body ih =>
    intro hs ρ a c h
    cases h with
    | allocAs hn hb => exact .allocAs hn (ih hs _ _ _ hb)
  | loop n body ih =>
    intro hs ρ a c h
    cases h with
    | loop hn hb => exact .loop hn (repeats_of_derives (ih hs) hb)
  | frame ds args body ih =>
    intro hs ρ a c h
    cases h with
    | frame hd hx hl hb => exact .frame hd hx hl (ih hs _ _ _ hb)
  | note n s ih =>
    intro hs ρ a c h
    cases h with
    | note h' => exact .note (ih hs _ _ _ h')

/-- The interpretation reaches a run only at the calls and the tests of the tree. If every
operation the tree `s` calls passes the check `p`, and two interpretations have the same calls of
the operations that pass `p` and the same tests and index uses, then the execution rules derive
the same outcomes under both: the same memory, tape position, count, scratch and peak. Nothing
else of an interpretation can affect a run. -/
theorem derives_congr_of_allOps (p : Op → Bool)
    (hcall : ∀ o, p o = true → I.call o = J.call o) (htest : I.test = J.test)
    (hindex : I.index = J.index) (R : ResourceModel Op Tst) (τ : Tape K) {s : Stmt Op Tst}
    (hs : s.allOps p = true) (ρ : Env) (a c : State Op Tst K) :
    Derives I R τ s ρ a c ↔ Derives J R τ s ρ a c :=
  ⟨derives_of_allOps p hcall htest hindex s hs ρ a c,
    derives_of_allOps p (fun o ho => (hcall o ho).symm) htest.symm hindex.symm s hs ρ a c⟩

/-- The same for the run of a program: two interpretations that agree on the operations its tree
calls, and on the tests and index uses, have the same executions. -/
theorem execution_congr_of_allOps (p : Op → Bool)
    (hcall : ∀ o, p o = true → I.call o = J.call o) (htest : I.test = J.test)
    (hindex : I.index = J.index) (R : ResourceModel Op Tst) {r b : ℕ}
    (prog : Program Op Tst r b) (hs : prog.body.allOps p = true)
    (formats : Fin b → StorageFormat) (τ : Tape K) (d : Fin r → ℕ) (m : Mem K)
    (out : State Op Tst K) :
    Execution prog I R formats τ d m out ↔ Execution prog J R formats τ d m out := by
  unfold Execution
  simp only [derives_congr_of_allOps p hcall htest hindex R τ hs]

end Reference

/-! ### Contracts: an operation is constrained through its own call -/

/-- A contract of the operation `o` constrains the call of `o` and nothing else of the
interpretation. -/
theorem Interp.Satisfies.congr {I J : Interp Op Tst K} {md : Mode} {o : Op} {C : Contract K}
    (h : I.Satisfies md o C) (hcall : I.call o = J.call o) : J.Satisfies md o C := by
  intro d ins outs τ m hp
  have h' := h d ins outs τ m hp
  rwa [hcall] at h'

/-- A contract of the query `q` constrains the test and the index use of `q` and nothing else
of the interpretation. -/
theorem Interp.SatisfiesQuery.congr {I J : Interp Op Tst K} {q : Tst} {C : QueryContract K}
    (h : I.SatisfiesQuery q C) (htest : I.test q = J.test q) (hindex : I.index q = J.index q) :
    J.SatisfiesQuery q C :=
  ⟨fun d a m => by rw [← htest]; exact h.1 d a m, fun a m => by rw [← hindex]; exact h.2 a m⟩

/-! ### The input: a run starts from the supplied buffers -/

section Problem

variable {r b : ℕ} {P : Problem K r b}

/-- The initial memory is that of the supplied buffers: the data of the input is not in it. -/
theorem Problem.initial_eq_of_buffers (P : Problem K r b) {d : Fin r → ℕ} {x y : P.Input d}
    (h : x.val.2 = y.val.2) : P.initial d x = P.initial d y := by
  unfold Problem.initial
  rw [h]

/-- The resident payload is that of the supplied buffers. -/
theorem Problem.initialBytes_eq_of_buffers (P : Problem K r b) {d : Fin r → ℕ}
    {x y : P.Input d} (h : x.val.2 = y.val.2) : P.initialBytes d x = P.initialBytes d y := by
  unfold Problem.initialBytes
  rw [h]

/-- A run depends on the input only through the supplied buffers. At two inputs with the
same buffers, under the same interpretation and tape, the same runs are accepted: the outcome,
its count and its memory are the same, and so is every resource claim. -/
theorem Specification.accepts_congr_of_buffers (S : Specification Op Tst P)
    (p : Program Op Tst r b) (I : Interp Op Tst K) (resources : ResourceModel Op Tst)
    (τ : Tape K) {d : Fin r → ℕ} {x y : P.Input d} (h : x.val.2 = y.val.2)
    (Q : Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop) :
    S.Accepts p I resources τ d x Q ↔ S.Accepts p I resources τ d y Q := by
  unfold Specification.Accepts
  rw [P.initial_eq_of_buffers h, P.initialBytes_eq_of_buffers h]

variable {M : AccessModel Op Tst P} {S : Specification Op Tst P}

/-- In a uniform model the interpretations the contracts allow are the same at every size and
input. -/
theorem AccessModel.Uniform.contracts_iff (M : AccessModel Op Tst P) [hM : M.Uniform]
    (d d' : Fin r → ℕ) (x : P.Input d) (y : P.Input d') (I : Interp Op Tst K) :
    M.contracts d x I ↔ M.contracts d' y I := by
  unfold AccessModel.contracts
  simp only [hM.operation d x d' y, hM.query d x d' y]

/-- One run, two inputs. If two inputs have the same supplied buffers and the contracts of
the model allow the interpretation `I` at both, then the one run of a certified program from
those buffers under `I` meets the output condition of both inputs. Whatever distinguishes the
two inputs must therefore be visible in which interpretations the model allows. -/
theorem Algorithm.good_of_contracts (A : Algorithm M S) {d : Fin r → ℕ} (hd : P.valid d)
    {x y : P.Input d} (h : x.val.2 = y.val.2) {I : Interp Op Tst K}
    (hx : M.contracts d x I) (hy : M.contracts d y I) (τ : Tape K) :
    ∃ st, Reference.Execution A.program I M.resources P.formats τ d (P.initial d x) st ∧
      S.good d x τ st.cost st.mem ∧ S.good d y τ st.cost st.mem := by
  obtain ⟨st, hst, -, -, -, -, -, hgx⟩ := A.correct d hd x I hx τ
  obtain ⟨st', hst', -, -, -, -, -, hgy⟩ := A.correct d hd y I hy τ
  rw [← P.initial_eq_of_buffers h] at hst'
  obtain rfl := Reference.Execution.unique I M.resources τ hst hst'
  exact ⟨st, hst, hgx, hgy⟩

/-- In a uniform model the output cannot depend on data that is in no buffer. If two inputs
have the same supplied buffers, the one run of a certified program from those buffers, under any
interpretation the model allows, meets the output condition of both. So a specification whose
output condition separates two inputs with the same buffers has no certificate in a uniform
model. -/
theorem Algorithm.good_of_buffers_eq [M.Uniform] (A : Algorithm M S) {d : Fin r → ℕ}
    (hd : P.valid d) {x y : P.Input d} (h : x.val.2 = y.val.2) {I : Interp Op Tst K}
    (hI : M.contracts d x I) (τ : Tape K) :
    ∃ st, Reference.Execution A.program I M.resources P.formats τ d (P.initial d x) st ∧
      S.good d x τ st.cost st.mem ∧ S.good d y τ st.cost st.mem :=
  A.good_of_contracts hd h hI ((AccessModel.Uniform.contracts_iff M d d x y I).mp hI) τ

end Problem

/-! ### Declared oracles: data in no buffer is reached only through them -/

namespace Inputs.Oracles

variable {r b : ℕ} {D : Inputs K r b} {M : AccessModel Op Tst D.problem}
  {S : Specification Op Tst D.problem}

/-- An interpretation the model allows at the input `X` is allowed at the input `Y` as soon as
its declared oracles satisfy their contracts at `Y`: every other operation and every query has
the same contract at both. -/
theorem contracts_of_satisfies (O : D.Oracles M) {d : Fin r → ℕ} (X Y : D.problem.Input d)
    {I : Interp Op Tst K} (hI : M.contracts d X I)
    (hO : ∀ o ∈ O.ops, I.Satisfies .total o (M.operation d Y o)) : M.contracts d Y I := by
  classical
  refine And.intro (fun o => ?_) (fun q => ?_)
  · by_cases ho : o ∈ O.ops
    · exact hO o ho
    · rw [← O.operation o ho d X d Y]
      exact hI.1 o
  · rw [← O.query d X d Y q]
    exact hI.2 q

/-- Two inputs with the same buffers are told apart only by an oracle. If the declared
oracles of the interpretation `I` satisfy their contracts at the input `Y` as well as at `X`, and
`X` and `Y` have the same supplied buffers, then the one run of a certified program under `I`
meets the output condition of both. So for the output to depend on data that is in no buffer,
some declared oracle must answer in a way that the other input does not allow. -/
theorem good_of_satisfies (O : D.Oracles M) (A : Algorithm M S) {d : Fin r → ℕ}
    (hd : D.valid d) {X Y : D.problem.Input d} (h : X.val.2 = Y.val.2) {I : Interp Op Tst K}
    (hI : M.contracts d X I) (hO : ∀ o ∈ O.ops, I.Satisfies .total o (M.operation d Y o))
    (τ : Tape K) :
    ∃ st, Reference.Execution A.program I M.resources D.problem.formats τ d
        (D.problem.initial d X) st ∧
      S.good d X τ st.cost st.mem ∧ S.good d Y τ st.cost st.mem :=
  A.good_of_contracts hd h hI (O.contracts_of_satisfies X Y hI hO) τ

/-- A tree that calls no declared oracle cannot use data that is in no buffer. If every
operation the tree of a certified program calls passes a check `p` that no declared oracle
passes, and two inputs have the same supplied buffers, then the one run from those buffers,
under any interpretation the model allows, meets the output condition of both inputs. -/
theorem good_of_allOps (O : D.Oracles M) (A : Algorithm M S) (p : Op → Bool)
    (hp : ∀ o, p o = true → o ∉ O.ops) (hA : A.program.body.allOps p = true) {d : Fin r → ℕ}
    (hd : D.valid d) {X Y : D.problem.Input d} (h : X.val.2 = Y.val.2) {I : Interp Op Tst K}
    (hI : M.contracts d X I) (τ : Tape K) :
    ∃ st, Reference.Execution A.program I M.resources D.problem.formats τ d
        (D.problem.initial d X) st ∧
      S.good d X τ st.cost st.mem ∧ S.good d Y τ st.cost st.mem := by
  classical
  obtain ⟨I', hI'⟩ := M.realize d hd Y
  -- the interpretation `I`, with the declared oracles of an interpretation allowed at `Y`
  let J : Interp Op Tst K :=
    ⟨fun o => if o ∈ O.ops then I'.call o else I.call o, I.test, I.index⟩
  have hin : ∀ o, o ∈ O.ops → I'.call o = J.call o := fun o ho => by
    change I'.call o = if o ∈ O.ops then I'.call o else I.call o
    rw [if_pos ho]
  have hout : ∀ o, o ∉ O.ops → I.call o = J.call o := fun o ho => by
    change I.call o = if o ∈ O.ops then I'.call o else I.call o
    rw [if_neg ho]
  have hJ : M.contracts d Y J := by
    refine And.intro (fun o => ?_) (fun q => ?_)
    · by_cases ho : o ∈ O.ops
      · exact (hI'.1 o).congr (hin o ho)
      · rw [← O.operation o ho d X d Y]
        exact (hI.1 o).congr (hout o ho)
    · rw [← O.query d X d Y q]
      exact (hI.2 q).congr rfl rfl
  obtain ⟨st, hst, -, -, -, -, -, hgx⟩ := A.correct d hd X I hI τ
  obtain ⟨st', hst', -, -, -, -, -, hgy⟩ := A.correct d hd Y J hJ τ
  rw [← D.problem.initial_eq_of_buffers h,
    ← Reference.execution_congr_of_allOps p (fun o ho => hout o (hp o ho)) rfl rfl
      M.resources A.program hA] at hst'
  obtain rfl := Reference.Execution.unique I M.resources τ hst hst'
  exact ⟨st, hst, hgx, hgy⟩

end Inputs.Oracles

end NLAlib.Ops
