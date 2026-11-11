/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Rules

/-!
# Total certification and conditional proof rules

The canonical certificates are `NLAlib.Ops.Algorithm` and `NLAlib.Ops.Impl.Meets`: one fixed
program, jointly realized contracts and successful execution with mandatory full accounting.
`Impl.Triple` and the conditional judgments below are the proof calculus used to build them. A raw
`ConditionalRuns`, `ConditionalRunsL` or `Impl.Triple` theorem is not that certificate.

**One statement for every program**, an algorithm of the library or an implementation of an
operation: `NLAlib.Ops.Impl.Triple R I md C`, *the implementation `R` meets the contract `C` over
the interpretation `I`*. It is the statement that an operation meets a contract
(`NLAlib.Ops.Interp.Meets`) with the call replaced by the run of the tree, so the two are
exchanged by linking:

* **grounding** (`NLAlib.Ops.Interp.link_meets`): if the implementation of `o` in a table meets
  `C` over `I`, then the operation `o` of the induced interpretation meets `C`. An algorithm
  that is certified this way is an operation for the algorithms above it.
* **the bridge** (`NLAlib.Ops.Impl.Triple.runs`, `NLAlib.Ops.Impl.Triple.runs_rel`): a certificate
  in total mode gives the top-level statement `NLAlib.Ops.ConditionalRuns`, with the static counts
    and
  workspace of the tree. The hypotheses on handles and operands are those of the contract, once.

Certificates are proved in operand form through `NLAlib.Ops.Impl.meets_rel` (from the blocks that
are read) or, for an exact certificate, `NLAlib.Ops.Impl.meets_fn_of_run` (the run of the tree is
the block function).

A conditional certificate in **liberal mode** says nothing of success: an implementation
that fails meets every contract (`NLAlib.Ops.Impl.meets_liberal_abort`,
`NLAlib.Ops.Interp.link_meets_liberal_of_abort`). A liberal statement is never a result by
itself. `Algorithm` requires total correctness in its own type, rather than looking up a
separately named success theorem.

## Main results

* `NLAlib.Ops.Impl.Triple`: the certificate.
* `NLAlib.Ops.Interp.link_meets`, `NLAlib.Ops.Interp.link_meets_kept`,
  `NLAlib.Ops.Interp.link_isFn`: grounding.
* `NLAlib.Ops.Impl.Triple.runs`, `NLAlib.Ops.Impl.Triple.runs_rel`, `NLAlib.Ops.Impl.Triple.runsL`:
  the bridge to the top-level statements.
* `NLAlib.Ops.Interp.IsFn.meets_rel`: a functional operation meets a relational contract that
  its values satisfy.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Op₁ Op₂ Tst K : Type}

/-- **The implementation `R` meets the contract `C`** over the interpretation `I`, in the mode
`md`: under the precondition of `C`, on operands that are buffers of the store (the evaluator
rejects the others; in total mode the precondition must give that they are), the numbers of
dimensions and operands fit and the run of the tree satisfies the postcondition of `C`. This is
the certificate of a program, independent of any table. -/
def Impl.Triple (R : Impl Op Tst) (I : Interp Op Tst K) (md : Mode) (C : Contract K) : Prop :=
  ∀ d ins outs τ m, (C.on md d ins outs τ m).pre m →
    md.Needs (m.Live (ins ++ outs)) ∧ (m.Live (ins ++ outs) →
      R.Fits d.length ins.length outs.length ∧
        Wp md I τ R.body (Env.frame d (ins ++ outs)) ((C.on md d ins outs τ m).post m) m)

/-- **Grounding**: the induced interpretation meets the contract of an implemented operation
when its implementation meets it. -/
theorem Interp.link_meets {I : Interp Op₂ Tst K} {T : Table Op₁ Op₂ Tst} {o : Op₁}
    {R : Impl Op₂ Tst} (hT : T o = .inl R) {md : Mode} {C : Contract K} (h : R.Triple I md C) :
    (I.link T).Meets md o C := by
  intro d ins outs τ m hpre
  obtain ⟨hl, hw⟩ := h d ins outs τ m hpre
  rw [Interp.link_callS_inl I hT]
  by_cases hlive : m.Live (ins ++ outs)
  · rw [if_pos hlive, if_pos (hw hlive).1]
    exact (hw hlive).2
  · rw [if_neg hlive]
    cases md
    · exact absurd (hl rfl) hlive
    · exact fun _ h => by cases h

/-- A kept operation meets the contracts it meets below. -/
theorem Interp.link_meets_kept {I : Interp Op₂ Tst K} {T : Table Op₁ Op₂ Tst} {o : Op₁} {o' : Op₂}
    (hT : T o = .inr o') {md : Mode} {C : Contract K} (h : I.Meets md o' C) :
    (I.link T).Meets md o C := by
  intro d ins outs τ m hpre
  rw [Interp.link_callS_inr I hT]
  exact h d ins outs τ m hpre

/-- **In liberal mode an implementation that fails meets every contract.** -/
theorem Impl.meets_liberal_abort (nd nin nout : ℕ) (I : Interp Op Tst K) (C : Contract K)
    (hfit : ∀ d ins outs τ m, (C.on .liberal d ins outs τ m).pre m →
      d.length = nd ∧ ins.length = nin ∧ outs.length = nout) :
    (⟨nd, nin, nout, .abort⟩ : Impl Op Tst).Triple I .liberal C :=
  fun d ins outs τ m hpre => ⟨by simp, fun _ => ⟨hfit d ins outs τ m hpre, wp_abort_liberal⟩⟩

/-- **Liberal statements can be vacuous**: an operation whose implementation in the table fails
meets every contract in liberal mode, under the induced interpretation. So a liberal corollary of
linking is never a result without a statement of success. -/
theorem Interp.link_meets_liberal_of_abort {I : Interp Op₂ Tst K} {T : Table Op₁ Op₂ Tst}
    {o : Op₁} {R : Impl Op₂ Tst} (hT : T o = .inl R) (hR : R.body = .abort) (C : Contract K) :
    (I.link T).Meets .liberal o C := by
  intro d ins outs τ m _ m' hm'
  rw [Interp.link_callS_inl I hT, hR] at hm'
  split_ifs at hm'
  cases hm'

/-- **A certificate in operand form**, total correctness: on admitted, live operands, with the
input blocks `xs` read and in the domain and room for the outputs, the implementation fits and
its run writes output blocks related to `xs` and to the window, advances the position by the
window, and changes nothing else. Whatever it draws into its scratch is gone at the end. -/
theorem Impl.meets_rel {R : Impl Op Tst} {I : Interp Op Tst K} {B : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    (h : ∀ (d : List ℕ) (ins outs : List (ℕ × ℕ)) (τ : Tape K) (m : Mem K) (xs : List (List K)),
      d.length = B.nd → adm d ins outs → m.Live (ins ++ outs) →
      m.readBlocks ins (B.inLens d) = some xs →
      B.dom d xs (τ.window B.stream m.pos (B.win d)) → m.Room outs (B.outLens d) →
      R.Fits d.length ins.length outs.length ∧ Wp .total I τ R.body (Env.frame d (ins ++ outs))
        (B.Post d xs outs (τ.window B.stream m.pos (B.win d)) m) m) :
    R.Triple I .total (B.spec adm) := by
  rintro d ins outs τ m ⟨hnd, hadm, hn⟩
  obtain ⟨hl, ⟨xs, hxs, hdom⟩, hz⟩ := hn rfl
  obtain ⟨hfit, hw⟩ := h d ins outs τ m xs hnd hadm hl hxs hdom hz
  exact ⟨fun _ => hl, fun _ => ⟨hfit, hw.mono fun m' hp => ⟨xs, hxs, hz, hp⟩⟩⟩

/-- **An exact certificate**: on admitted operands, where the block function succeeds, the run of
the implementation is the block function. -/
theorem Impl.meets_fn_of_run {R : Impl Op Tst} {I : Interp Op Tst K} {f : BlockFn K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    (h : ∀ d ins outs τ m m', adm d ins outs → f.apply d ins outs τ m = some m' →
      R.Fits d.length ins.length outs.length ∧
        eval I τ R.body (Env.frame d (ins ++ outs)) m = some m') :
    R.Triple I .total (f.rel.spec adm) := by
  rintro d ins outs τ m ⟨hnd, hadm, hn⟩
  obtain ⟨hl, ⟨xs, hxs, ys, hys, hlen⟩, hz⟩ := hn rfl
  obtain ⟨hfit, hr⟩ := h d ins outs τ m _ hadm (BlockFn.apply_of_read hnd hl hxs hys hlen hz)
  exact ⟨fun _ => hl, fun _ => ⟨hfit, _, hr, xs, hxs, hz, ys, hlen, hys, rfl⟩⟩

/-- **Grounding a functional contract** (the exact certificate). -/
theorem Interp.link_isFn {I : Interp Op₂ Tst K} {T : Table Op₁ Op₂ Tst} {o : Op₁}
    {R : Impl Op₂ Tst} (hT : T o = .inl R) {f : BlockFn K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    (h : ∀ d ins outs τ m m', adm d ins outs → f.apply d ins outs τ m = some m' →
      R.Fits d.length ins.length outs.length ∧
        eval I τ R.body (Env.frame d (ins ++ outs)) m = some m') :
    (I.link T).IsFn .total o f adm :=
  Interp.link_meets hT (Impl.meets_fn_of_run h)

/-! ### The bridge to the top-level statements -/

/-- **The bridge**: a certificate in total mode gives the top-level statement. Under the
precondition of the contract, the tree, run in the environment of its dimensions and operands,
terminates within its static counts and workspace, and the postcondition of the contract holds
of the final memory. -/
theorem Impl.Triple.runs {R : Impl Op Tst} {I : Interp Op Tst K} {C : Contract K}
    (h : R.Triple I .total C) (W : Op → List ℕ → ℕ) {d : List ℕ} {ins outs : List (ℕ × ℕ)}
    {τ : Tape K} {m : Mem K} (hpre : (C.on .total d ins outs τ m).pre m) :
    ConditionalRuns I W τ R.body (Env.frame d (ins ++ outs)) m
      (stmtCost R.body (d ++ (ins ++ outs).map Prod.snd))
      (stmtPeak W R.body (d ++ (ins ++ outs).map Prod.snd))
      ((C.on .total d ins outs τ m).post m) := by
  obtain ⟨hl, hw⟩ := h d ins outs τ m hpre
  obtain ⟨m', hrun, hQ⟩ := (hw (hl rfl)).2
  exact ConditionalRuns.of_run hrun hQ W

/-- **The bridge, in operand form**: on admitted, live operands, with the input blocks `xs` read
and room for the outputs, the tree terminates within its static counts and workspace and has
written output blocks related to `xs` and to the window. -/
theorem Impl.Triple.runs_rel {R : Impl Op Tst} {I : Interp Op Tst K} {B : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (h : R.Triple I .total (B.spec adm))
    (W : Op → List ℕ → ℕ) {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape K} {m : Mem K}
    {xs : List (List K)} (hnd : d.length = B.nd) (hadm : adm d ins outs)
    (hl : m.Live (ins ++ outs)) (hr : m.readBlocks ins (B.inLens d) = some xs)
    (hdom : B.dom d xs (τ.window B.stream m.pos (B.win d))) (hz : m.Room outs (B.outLens d)) :
    ConditionalRuns I W τ R.body (Env.frame d (ins ++ outs)) m
      (stmtCost R.body (d ++ (ins ++ outs).map Prod.snd))
      (stmtPeak W R.body (d ++ (ins ++ outs).map Prod.snd))
      (B.Post d xs outs (τ.window B.stream m.pos (B.win d)) m) := by
  refine (h.runs W (d := d) (ins := ins) (outs := outs) (τ := τ) (m := m)
    ⟨hnd, hadm, fun _ => ⟨hl, ⟨xs, hr, hdom⟩, hz⟩⟩).mono le_rfl le_rfl ?_
  rintro m' ⟨xs', hr', -, hp⟩
  have e : xs' = xs := Option.some.inj (hr'.symm.trans hr)
  exact e ▸ hp

/-- **The bridge, partial correctness**: a liberal certificate gives a refinement statement,
which says nothing of success. -/
theorem Impl.Triple.runsL {R : Impl Op Tst} {I : Interp Op Tst K} {C : Contract K}
    (h : R.Triple I .liberal C) {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape K} {m : Mem K}
    (hpre : (C.on .liberal d ins outs τ m).pre m) (hl : m.Live (ins ++ outs)) :
    ConditionalRunsL I τ R.body (Env.frame d (ins ++ outs)) m ((C.on .liberal d ins outs τ m).post
      m) :=
  ((h d ins outs τ m hpre).2 hl).2

/-! ### Witnesses -/

/-- **A functional operation meets a relational contract that its values satisfy.** For
witnesses and model primitives: the block function has the shape of the relation, and on blocks
that were read its value has the declared lengths and is related to them. -/
theorem Interp.IsFn.meets_rel {I : Interp Op Tst K} {o : Op} {f : BlockFn K}
    {adm' : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (h : I.IsFn .total o f adm')
    {R : BlockRel K} {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    (hadm : ∀ d ins outs, adm d ins outs → adm' d ins outs) (hnd : f.nd = R.nd)
    (hst : f.stream = R.stream) (hwin : ∀ d, f.win d = R.win d)
    (hin : ∀ d, f.inLens d = R.inLens d) (hout : ∀ d, f.outLens d = R.outLens d)
    (hf : ∀ d w xs (m : Mem K) ins outs, d.length = R.nd → w.length = R.win d → adm d ins outs →
      m.readBlocks ins (R.inLens d) = some xs → R.dom d xs w →
      ∃ ys, f.fn d w xs = some ys ∧ ys.map List.length = R.outLens d ∧ R.rel d xs w ys) :
    I.Meets .total o (R.spec adm) := by
  rintro d ins outs τ m ⟨hnd', hadm', hn⟩
  obtain ⟨hl, ⟨xs, hxs, hdom⟩, hz⟩ := hn rfl
  obtain ⟨ys, hys, hlen, hrel⟩ := hf d _ xs m ins outs hnd'
    (Tape.length_window ..) hadm' hxs hdom
  have ha := BlockFn.apply_of_read (f := f) (τ := τ) (hnd'.trans hnd.symm) hl
    (by rw [hin]; exact hxs) (by rw [hst, hwin]; exact hys) (by rw [hout]; exact hlen)
    (by rw [hout]; exact hz)
  rw [hwin] at ha
  exact ⟨_, h.callS_eq (hadm _ _ _ hadm') ha, xs, hxs, hz, ys, hlen, hrel, rfl⟩

/-- Canonical implementation certification. Both operand lists and the implementation are
fixed before runtime sizes and inputs; the claim requires successful fully counted execution
under a jointly realized model. Conditional implementation proofs use `Impl.Triple`. -/
def Impl.Meets (R : Impl Op Tst) {b : ℕ} {P : Problem K R.nd b}
    (ins outs : List Operand) (M : AccessModel Op Tst P) (S : Specification Op Tst P) : Prop :=
  Runs (R.program b ins outs) M S

/-- One fixed symbolic program, with successful counted execution under every interpretation
satisfying a realized model, at every admitted size and input and every tape. A partial
correctness theorem alone cannot construct this structure. -/
structure Algorithm {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}
    (M : AccessModel Op Tst P) (S : Specification Op Tst P) where
  /-- The program, fixed before all runtime sizes and inputs. -/
  program : Program Op Tst r b
  /-- Total correctness, including all structural accounting on this very execution. -/
  correct : program.Certifies M S

namespace Algorithm

variable {Op Lo Tst K : Type} {r b : ℕ} {P : Problem K r b}
  {M : AccessModel Op Tst P} {S : Specification Op Tst P}

/-- Every certified program passes the core's storage discipline. -/
theorem wellTyped (A : Algorithm M S) : A.program.wellTyped M.resources P.formats = true := by
  obtain ⟨d, hd⟩ := P.admitted
  obtain ⟨x⟩ := P.inputs_exist d hd
  obtain ⟨I, hI⟩ := M.realize d hd x
  obtain ⟨st, hr, -⟩ := A.correct d hd x I hI (fun _ _ => M.word)
  unfold exec at hr
  split_ifs at hr with h
  exact h.1

/-- Successful execution and the specified output of the same format-checked program. -/
theorem run (A : Algorithm M S) {d : Fin r → ℕ} (hd : P.valid d) (x : P.Input d)
    (I : Interp Op Tst K) (hI : M.contracts d x I) (τ : Tape K) :
    ∃ c m', A.program.run I M.resources P.formats τ d (P.initial d x) = some m' ∧
      c ≤ S.budget d ∧ S.good d x τ c m' := by
  obtain ⟨st, hr, -, hc, -, -, -, hg⟩ := A.correct d hd x I hI τ
  have hm := congrArg (Option.map St.mem) hr
  rw [exec_mem, Option.map_some] at hm
  exact ⟨st.cost, st.mem, hm, hc, hg⟩

/-- Every admitted checked execution succeeds. -/
theorem run_ne_none (A : Algorithm M S) {d : Fin r → ℕ} (hd : P.valid d) (x : P.Input d)
    (I : Interp Op Tst K) (hI : M.contracts d x I) (τ : Tape K) :
    A.program.run I M.resources P.formats τ d (P.initial d x) ≠ none := by
  obtain ⟨c, m', hr, -, -⟩ := A.run hd x I hI τ
  rw [hr]
  exact Option.some_ne_none m'

/-- Construct a canonical certificate from total word-level logic and format/resource proofs.
The complete instruction budget is independently specified; work/span are evaluated with the
same fixed model, and resident bytes include the supplied buffers. -/
def ofWp (p : Program Op Tst r b)
    (ht : p.wellTyped M.resources P.formats = true)
    (hwp : ∀ d, P.valid d → ∀ (x : P.Input d) (I : Interp Op Tst K),
      M.contracts d x I → ∀ τ, Wp .total I τ p.body (Program.environment (b := b) d)
        (fun m' => ∀ c, c ≤ S.budget d → S.good d x τ c m') (P.initial d x))
    (hcost : ∀ d, P.valid d → staticCost p d ≤ S.budget d)
    (hspace : ∀ d, P.valid d → staticPeak M.resources p d ≤ S.scratch d)
    (hwork : ∀ d, P.valid d → M.resources.work (S.budget d) ≤ S.work d)
    (hspan : ∀ d, P.valid d → M.resources.span (S.budget d) ≤ S.span d)
    (hmemory : ∀ d, P.valid d → ∀ x : P.Input d,
      P.initialBytes d x + S.scratch d ≤ S.memory d) : Algorithm M S where
  program := p
  correct d hd x I hI τ := by
    obtain ⟨m', hr, hg⟩ := hwp d hd x I hI τ
    have hm : eval I.instrument τ p.body.instrument (Program.environment (b := b) d)
        (P.initial d x) = some m' := by rw [run_instrument]; exact hr
    obtain ⟨raw, he, -, -, hgood⟩ := ConditionalRuns.of_run
      (Q := fun m' => ∀ c, c ≤ S.budget d → S.good d x τ c m')
      hm hg (instrumentWorkspace M.resources.workspace)
    have hx := exec_of_evalCounted ht (by simp [Problem.initial]) he
    obtain ⟨hc, hp⟩ := exec_static hx
    have hcount := hc.trans (hcost d hd)
    have hpeak := hp.trans (hspace d hd)
    exact ⟨raw.reserveQueries M.resources, hx, hpeak, hcount,
      (M.resources.work_mono hcount).trans (hwork d hd),
      (M.resources.span_mono hcount).trans (hspan d hd),
      (Nat.add_le_add_left hpeak _).trans (hmemory d hd x), hgood _ hcount⟩

/-- A realized model excludes the always-failing program. -/
theorem body_ne_abort (A : Algorithm M S) : A.program.body ≠ .abort := by
  intro he
  obtain ⟨d, hd⟩ := P.admitted
  obtain ⟨x⟩ := P.inputs_exist d hd
  obtain ⟨I, hI⟩ := M.realize d hd x
  obtain ⟨c, m', hr, -, -⟩ := A.run hd x I hI (fun _ _ => M.word)
  simp [Program.run, Ops.run, he, eval] at hr

/-- Impossible output specifications cannot acquire certificates through vacuous models. -/
theorem not_nonempty (hgood : ∀ d, P.valid d → ∀ (x : P.Input d) (τ : Tape K) c m',
    ¬ S.good d x τ c m') (τ : Tape K) : ¬ Nonempty (Algorithm M S) := by
  rintro ⟨A⟩
  obtain ⟨d, hd⟩ := P.admitted
  obtain ⟨x⟩ := P.inputs_exist d hd
  obtain ⟨I, hI⟩ := M.realize d hd x
  obtain ⟨c, m', -, -, hg⟩ := A.run hd x I hI τ
  exact hgood d hd x τ c m' hg

/-- Link fixed trees and recheck storage compatibility, full lower work/span and resident bytes.
Different primitive parallel configurations require separately specified resource models. -/
def link (A : Algorithm M S) (T : Table Op Lo Tst) (L : AccessModel Lo Tst P)
    (R : Specification Lo Tst P)
    (ht : (A.program.link T).wellTyped L.resources P.formats = true)
    (hcontracts : ∀ d, P.valid d → ∀ (x : P.Input d) (I : Interp Lo Tst K),
      L.contracts d x I → M.contracts d x (I.link T))
    (hgood : ∀ d, P.valid d → ∀ (x : P.Input d) τ c m',
      c ≤ S.budget d → S.good d x τ c m' →
        ∀ c', c' ≤ R.budget d → R.good d x τ c' m')
    (hcost : ∀ d, P.valid d → staticCost (A.program.link T) d ≤ R.budget d)
    (hspace : ∀ d, P.valid d → staticPeak L.resources (A.program.link T) d ≤ R.scratch d)
    (hwork : ∀ d, P.valid d → L.resources.work (R.budget d) ≤ R.work d)
    (hspan : ∀ d, P.valid d → L.resources.span (R.budget d) ≤ R.span d)
    (hmemory : ∀ d, P.valid d → ∀ x : P.Input d,
      P.initialBytes d x + R.scratch d ≤ R.memory d) : Algorithm L R :=
  ofWp (A.program.link T) ht (fun d hd x I hI τ => by
    obtain ⟨c, m', hr, hc, hg⟩ := A.run hd x (I.link T) (hcontracts d hd x I hI) τ
    have hraw : eval (I.link T) τ A.program.body (Program.environment (b := b) d)
        (P.initial d x) = some m' := by
      simpa [Program.run, Ops.run, A.wellTyped, Problem.initial] using hr
    rw [← run_link] at hraw
    exact ⟨m', hraw, hgood d hd x τ c m' hc hg⟩)
    hcost hspace hwork hspan hmemory

end Algorithm

end NLAlib.Ops
