# Writing, proving and certifying a routine

Part of the [contributor guide](../../CONTRIBUTING.md). This guide is the path from nothing to a
certified routine: which statement lives at which layer, one example carried from the tree to
the line of the certificate report, and the mistakes that cost time. The rules are in
[programs](programs.md); the reference for every construction named here is the
[Ops README](../../NLAlib/Ops/README.md). Every code block below is library code, copied from
the file named under it.

## 1. The layers and their statements

A certified algorithm is built in five layers. Each has one kind of statement, and a proof at
one layer uses only the statement of the layer below, never its proof.

| Layer | Object | Statement | Who reads it |
|---|---|---|---|
| operation | a primitive of a model (`ScalarOp.add`, a matrix-vector product) | `I.Satisfies mode o contract`: the interpretation `I` satisfies the contract of `o` | reviewer (it is an assumption of the model) |
| fragment | a piece of one routine's tree, a plain `Stmt` written with `ops%` | one lemma `X_writes` in operand form (`Writes`): what the run writes and where | nobody outside the proof of its routine |
| routine | a tree with an interface, written with `routine%` | one judgment `XRoutine_meets : XRoutine.Meets I XSpec` | authors of callers |
| certificate | the routine on a problem, under a model | `Algorithm M S`, built by `Routine.Domain.certify` or `Routine.Domain.algorithm` | the certificate check |
| readable statement | the certificate, in terms of the evaluator | `X_checked` | reviewer |

A randomized guarantee adds one object beside the certificate: a `RandomizedClaim` of it
([programs](programs.md), "Resources and probability").

What a reviewer reads is short: the specification of the routine (`Routine.Spec`), the problem
(`Routine.Domain`), the model (operations, contracts, costs) and the `_checked` theorem. The
tree, the judgment and the count are checked by Lean.

What "run" and "counted" mean is stated twice: by the evaluator, which the certificate is
defined with, and by the reference rules of `NLAlib/Ops/Reference/Semantics.lean`, a readable
restatement with the charge of each construct written in its rule. The two are proved to give
the same outcome. The [reviewer's declaration map](../design/Ops-ReferenceReview.md) lists every
definition such a reading depends on.

**Routine or fragment.** A tree is a routine when it has operands of its own and something
calls it through its interface: a `run` in another tree, a linking table, or a certificate. A
tree that is a piece of one routine's tree, working on buffers that routine allocates or at
offsets computed inside its operands, is a fragment; its docstring names its routine. If you
are about to state the same run twice (a judgment and an operand-form lemma), stop: a routine
has one statement ([programs](programs.md), "Proving programs as mathematics", item 6, lists
the three exceptions).

## 2. The example

The example is `sum2`: sum two vectors of length `n` by two calls of a summation routine and
one addition. Files: `NLAlib/Ops/Examples/Routine.lean` (routine, specification, judgment) and
`NLAlib/Ops/Examples/RoutineCertification.lean` (problem, certificate, readable statement).
Read both whole before writing your own; they are about 300 lines together. A second example,
`NLAlib/Ops/Examples/VectorSum.lean` (`vadd`: $z_i = x_i + y_i$), is one file of 170 lines with
the whole chain for a loop over the cells of a block; start from it when your routine is a loop
over operations.

A file of routines begins as those files do, after the copyright header:

```lean
module

public import NLAlib.Ops.Routine
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.Profiles.RoundedScalarBlas
```

(`Examples/VectorSum.lean`.) The first three imports are the routine, the proof tactics and the
notation; the fourth is for the problem and the certificate; the last is the model the
certificate is stated under. The module docstring follows, then `@[expose] public section` and
the namespace.

### 2.1 The routine

```lean
def sum2 : Routine Op Tst := noted% routine% [n] (x : n, y : n) → (z : 1, unreported w : 1) {
  run (sum (Op := Op) (Tst := Tst)) [n] (x, z);
  run (sum (Op := Op) (Tst := Tst)) [n] (y, w);
  call (Has.inj ScalarOp.add) [] (z, w) → (z)
}
```

(`Examples/Routine.lean`. The `noted%` is particular to this example; leave it out.)

- `[n]` are the dimensions. `(x : n, y : n) → (z : 1, unreported w : 1)` is the interface: an
  operand named only on the left is read, only on the right written, on both sides updated in
  place. Each operand is declared once, with its length in the dimensions.
- `unreported` marks a written operand whose final contents the judgment does not state
  (scratch supplied by the caller).
- `run R [dims] (operands)` runs another routine by its interface. `call o [dims] (ins) → (outs)`
  calls an operation of the model. `for i < k { … }`, `let t ← alloc n`, and `if` are in
  `NLAlib/Ops/Logic/Builder.lean`.
- An operand of a `call` or a `run` is a name (`x`: the operand from its first cell) or a name
  with an offset in the dimensions and loop variables: `x[i]`, `x[(1 + i)]`, `x[inc * i]`. A loop
  over the cells of two blocks reads:

  ```lean
  def vadd : Routine Op Tst := routine% [n] (x : n, y : n) → (z : n) {
    for i < n {
      call (Has.inj ScalarOp.add) [] (x[i], y[i]) → (z[i])
    }
  }
  ```

  (`Examples/VectorSum.lean`.)
- `variable {Op Tst : Type} [Has ScalarOp Op]`: a routine is written for any collection of
  operations that contains the ones it calls, so that it can be certified under several models.

### 2.2 The specification

```lean
def sum2Spec (dec : K → ℝ) (u : ℝ) : Routine.Spec K :=
  spec% [n] (xs, ys) → ([v]) ensures
    |dec v - (∑ k ∈ Finset.range n, dec (vec xs k) + ∑ k ∈ Finset.range n, dec (vec ys k))| ≤
      ((1 + u) * (1 + u) ^ (n - 1) - 1) *
        (∑ k ∈ Finset.range n, |dec (vec xs k)| + ∑ k ∈ Finset.range n, |dec (vec ys k)|)
```

(`Examples/Routine.lean`.) A specification relates the blocks read to the blocks written and
mentions no memory, operand or tree. `(xs, ys)` name the blocks read, in the order of the
interface; `([v])` names the reported blocks written, here one block that is the one-cell list
`[v]`. An unreported operand has no block. `requires P` before `ensures` states a
precondition. A routine that implements an operation of a model states its specification as
`Routine.Spec.ofRel` of that operation's block relation instead.

### 2.3 The judgment

```lean
theorem sum2_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) :
    (sum2 (Op := Op) (Tst := Tst)).Meets I (sum2Spec dec u) := by
  routine_intro [n] (x, y, z, w) reads (xs, ys)
  have hsum := sum_meets (Op := Op) (Tst := Tst) hI hM hu
  call hsum [n] (x, z) as ν hfr hpos (zs) hpost
  obtain ⟨v₁, hv₁, rfl⟩ := Store.readBlock_one_eq_some.mp hzs
  call hsum [n] (y, w) as ν₂ hfr₂ hpos₂ (ws) hpost₂
  obtain ⟨v₂, hv₂, rfl⟩ := Store.readBlock_one_eq_some.mp hws
  step (hI .add) as ν₃ hfr₃ ⟨hpos₃, v, hv, rfl⟩
  routine_exit
  exact sum2_error hM hu hpost hpost₂
```

(`Examples/Routine.lean`.) The hypotheses are what the proof needs of the interpretation
(`IsScalar M I`: the scalar operations compute the functions of the machine `M`) and of the
arithmetic (`StdModel u dec M`). The proof has one line per statement of the tree:

1. **routine_intro** `[n] (x, y, z, w) reads (xs, ys)` names the dimensions, the operands (each a
   pair `(buffer, offset)`) and the blocks read. It puts in the context the tape `τ` and the
   memory `m`, `hxs : m.store.readBlock x.1 x.2 n = some xs` (one per block read), liveness
   `hlive`/`hl`, room for the written blocks `hrooms`/`hroom`, the precondition `hpre`, and one
   separation fact per pair of operands that must be apart (`hxz : x.1 ≠ z.1`). The goal is the
   `Writes` statement of the tree.
2. `call h [dims] (operands) as ν hfr hpos (zs) hpost` takes one `run` of the tree, with `h` the
   judgment of the routine run. It proves the side conditions from the context and introduces
   the memory after the call `ν`, its frame `hfr`, the tape position `hpos`, the block written
   `zs` with `hzs`, and the postcondition `hpost` of the callee at those blocks.
3. `step h as ν hfr ⟨pattern⟩` takes one `call` of an operation, with `h` the contract of the
   operation (`hI .add`). The pattern destructures its postcondition.
4. **routine_exit** closes the run at the final memory and leaves the postcondition of the
   specification as the goal. What is left is mathematics, proved as a separate lemma about
   values (`sum2_error`), which mentions no memory.

Between steps, a fact about an earlier memory is carried across the frames in the context. To
have a block read at the current memory, state it and prove it by `keep`:
`have hxs₁ : m₁.store.readBlock x.1 x.2 n = some xs := by keep`. `kept` proves one such goal
where a tactic leaves it. A bare `keep` restates every kept hypothesis, but under names that
cannot be written, so it serves only tactics that search the context.

**A loop** takes **loop_inv** `F P with i hi m₁ hfr hP`: `F i` is the footprint written by the
first `i` rounds and `P i m'` the invariant on the memory after them. It leaves the goals
`round`, and `initial` and `exit` when they are not immediate.

- The footprint may be the whole block the loop writes at every `i`, `Fp.blocks [z] [n]`; a
  growing footprint (`Store.inBlock z.1 z.2 i`) is needed only when a round must know that the
  cells after `i` are still untouched.
- The invariant states the tape position (`m'.pos = m.pos` for a loop that draws nothing), then
  the blocks the loop has written and the mathematical state.
- In `round`, `i` is the round, `hi : i < n`, `m₁` the memory before it, `hfr` the frame from
  the memory before the loop to `m₁` (what `keep` uses), and `hP` the invariant at `i`. The
  goal is the body, to be ended by the invariant at `i + 1`.
- In `exit`, for a loop that ends its routine, the goal is the final obligation of the routine
  at every memory satisfying the invariant at `n`: the tape position, and blocks read from the
  written operands that satisfy the postcondition. The term is
  `⟨hpos, [zs], Mem.readBlocks_of_cons hz rfl, post⟩`: `Mem.readBlocks_of_cons h rest` puts one
  block read (`h : m.store.readBlock z.1 z.2 n = some zs`) in front of the reads of the other
  written operands, and `rfl` is the empty rest.

A loop over the cells of a block:

```lean
theorem vadd_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (vadd (Op := Op) (Tst := Tst)).Meets I (vaddSpec M) := by
  routine_intro [n] (x, y, z) reads (xs, ys)
  loop_inv (fun _ => Fp.blocks [z] [n])
    (fun i m' => m'.pos = m.pos ∧
      m'.store.readBlock z.1 z.2 i = some (vaddF M (vec xs) (vec ys) i))
    with i hi m₁ hfr hP
  case round =>
    obtain ⟨hpos₁, hz₁⟩ := hP
    have hxs₁ : m₁.store.readBlock x.1 x.2 n = some xs := by keep
    have hys₁ : m₁.store.readBlock y.1 y.2 n = some ys := by keep
    have hxi : m₁.store.get x.1 (x.2 + i) = some (vec xs i) :=
      Store.get_of_readBlock hxs₁ hi default
    have hyi : m₁.store.get y.1 (y.2 + i) = some (vec ys i) :=
      Store.get_of_readBlock hys₁ hi default
    step (hI .add) as m₂ hfr₂ ⟨hpos₂, v, hv, rfl⟩
    refine ⟨hpos₂.trans hpos₁, ?_⟩
    rw [vaddF_succ]
    exact Store.readBlock_succ_of (by keep) hv
  case exit =>
    rintro m₁ - ⟨hpos₁, hz₁⟩
    exact ⟨hpos₁, [vaddF M (vec xs) (vec ys) n], Mem.readBlocks_of_cons hz₁ rfl, rfl⟩
```

(`Examples/VectorSum.lean`.) The specification is `zs = vaddF M (vec xs) (vec ys) n`, with
`vaddF` a function on values and `vaddF_succ` its one-round lemma. The lemmas a loop over cells
uses:

- `vec xs k` is entry `k` of the list `xs` (the default word when out of range; it needs
  `[Inhabited K]`).
- `Store.get_of_readBlock h hi default`: cell `i` of a block read is `vec xs i`. State the cells
  the round reads at the current memory before the `step`, as `hxi` and `hyi` above: the `step`
  then reads them as cells and its postcondition is about `vec xs i`.
- `Store.readBlock_succ_of h hv`: a block of length `i` read and the next cell make the block of
  length `i + 1`.
- `Store.length_of_readBlock`: the length of a block read.

A loop over a routine:

```lean
  loop_inv (fun _ => Fp.blocks [X] [n])
    (fun i m' => m'.pos = m.pos ∧ ∃ x, m'.store.readBlock X.1 X.2 n = some x ∧
      ‖WithLp.toLp 2 (decv id n x - (G ^ i) *ᵥ decv id n xs)‖ ≤
        ((‖G‖ + myEta (A n) δ e a) ^ i - ‖G‖ ^ i) * ‖WithLp.toLp 2 (decv id n xs)‖ ∧
      ‖WithLp.toLp 2 (decv id n x)‖ ≤
        (‖G‖ + myEta (A n) δ e a) ^ i * ‖WithLp.toLp 2 (decv id n xs)‖)
    with i hi m₁ hfr hP
  case round =>
    obtain ⟨hpos₁, x, hx, hbound, hnorm⟩ := hP
    have hh₁ : m₁.store.readBlock h.1 h.2 1 = some [a] := by keep
    call hstep [n] (h, X) as m₂ hfr₂ hpos₂ (zs) hpost
    have hz : ‖WithLp.toLp 2 (decv id n zs - G *ᵥ decv id n x)‖ ≤
        myEta (A n) δ e a * ‖WithLp.toLp 2 (decv id n x)‖ := hpost
    exact ⟨hpos₂.trans hpos₁, zs, hzs, iterate_bound G hη hbound hnorm hz⟩
  case initial =>
    exact ⟨rfl, xs, hxs, by simp, by simp⟩
  case exit =>
    rintro m₁ - ⟨hpos₁, x, hx, hbound, -⟩
    exact ⟨hpos₁, [x], Mem.readBlocks_of_cons hx rfl, hbound⟩
```

(`Examples/Integrator.lean`, `myIntegrate_meets`.) The mathematics of one round is again a
lemma about values (`iterate_bound`). A loop that is the last statement of a routine ends in
`case exit`, which proves the final obligation directly, as in both examples; otherwise the
proof continues after the loop and ends with **routine_exit**. Another loop over a routine is
`NLAlib/Krylov/CG/HSCG/Rounds.lean`. The loops of `NLAlib/Ops/Blas/Sum.lean`,
`NLAlib/Ops/Blas/Level1.lean` and `NLAlib/Ops/Examples/Strided.lean` are proved with the rules
below these tactics (the weakest-precondition rules of a loop and of a call); they are not the
model for a new routine.

### 2.4 The problem

```lean
def sum2Domain : (sum2 (Op := ScalarOp) (Tst := CmpTst)).Domain ℝ 1 4 where
  valid _ := True
  In d := (Fin (d 0) → ℝ) × (Fin (d 0) → ℝ)
  accepts _ _ := True
  slot d := ![.stored (Codec.vector (d 0)) Prod.fst, .stored (Codec.vector (d 0)) Prod.snd,
    .blank 1, .blank 1]
  fits := by domain_fits
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq] at h0 h1
    exact Prod.ext ((Codec.vector (d 0)).encode_injective h0)
      ((Codec.vector (d 0)).encode_injective h1)
  admitted := ⟨fun _ => 0, trivial⟩
  inhabited _ _ := ⟨(fun _ => 0, fun _ => 0), trivial⟩

abbrev sum2Problem : Problem ℝ 1 4 := sum2Domain.problem
```

(`Examples/RoutineCertification.lean`.) `Domain ℝ 1 4`: words are reals, one dimension, four
buffers. The author states mathematics only: `valid` (admitted sizes), `In` (the type of the
inputs), `accepts` (admitted inputs) and one `slot` per operand, in the order of the
interface: `stored codec component` for an operand that is read, `blank len` for one that is
only written, `derived len f` for words computed from the inputs. `fits` is `by` **domain_fits**.
`faithful` says the stored buffers determine the inputs: one `encode_injective` per stored
slot; with three or more slots the `simp only` set takes `Matrix.cons_val` as well
(`Examples/RoutineProblem.lean`, `thresholdDomain`). `admitted` and `inhabited` give one
admitted size and one admitted input at each size, so that the certificate is not vacuous. Here the certificate is stated at the concrete operations
`ScalarOp`, `CmpTst`; the routine stays generic.

A restriction on the inputs goes in `accepts`, where the `_checked` theorem shows it as a
hypothesis. An input that no buffer holds (the matrix of a matrix-free solver) is declared
`Unstored`, and the certificate then states `Routine.Domain.Oracles`
(`NLAlib/Krylov/CG/HSCG/Certification.lean`; [programs](programs.md), item 7).

### 2.5 The certificate

```lean
noncomputable abbrev sum2Model (M : Machine ℝ) : AccessModel ScalarOp CmpTst sum2Problem :=
  RoundedScalarBlas.model sum2Problem M

def sum2Input (d : Fin 1 → ℕ) (x : sum2Problem.Input d) : List (List ℝ) :=
  sum2Domain.blocks d x.val.1

def sum2Program : Program ScalarOp CmpTst 1 4 := (sum2 (Tst := CmpTst)).close 1 4

def sum2Work (d : Fin 1 → ℕ) : ℕ := 24 * d 0 + 63

theorem countPoly_sum2Program : sum2Program.countPoly = [(24, [0]), (63, [])] := by
  rfl

noncomputable def sum2Algorithm (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u) :
    Algorithm (sum2Model M)
      ((sum2 (Tst := CmpTst)).specification (P := sum2Problem) (fun _ _ => sum2Spec id u)
        (sum2Model M).resources sum2Input sum2Domain.bytes sum2Work) :=
  sum2Domain.certify (fun _ _ => sum2Spec id u) sum2Work
    (fun _ _ _ _ hI => sum2_meets (RoundedScalarBlas.model_laws hI).1 hM hu)
    (fun _ _ _ _ _ => trivial)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun d _ => (eval_countPoly_sum2Program d).le)
```

(`Examples/RoutineCertification.lean`, docstrings omitted.) The model is a standard collection
of `NLAlib/Ops/Profiles`; choose one that is confined and, without an oracle, uniform. The
program is the routine closed on the buffers of the problem. The work is a closed form: the
kernel computes the instruction polynomial of the tree (`Program.countPoly`, here by `rfl`;
**kernel_rfl** for a large tree), `[(24, [0]), (63, [])]` reads `24 * d 0 + 63`, and
`eval_countPoly_sum2Program` evaluates it: `rw [countPoly_sum2Program]` and then **poly_eval**
`[sum2Work]`, which takes the definition of the closed form to unfold. To find
the polynomial of a new program, write `#reduce fooProgram.countPoly` under its definition,
copy the list it prints and delete the command (`#eval` does not run in a `module` file). The
blocks read (`sum2Input`) are `Domain.blocks` of the typed input. The arguments of `certify` are, in order: the
specification of the routine at each size and input, the work, the judgment under every
interpretation of the model, the precondition at every admitted input, three bounds that are
`le_rfl` when the specification takes the computed budget, scratch and span, and the bound of
the polynomial by the stated work. In the third, `RoundedScalarBlas.model_laws hI` turns the
contracts of the model into the hypotheses of the judgment; its first component is
`IsScalar M I`. `RoundedScalarBlas.model` takes any `Machine ℝ`; a hypothesis on the arithmetic
(`StdModel u id M`) is a hypothesis of the certificate, as in `sum2Algorithm`.

`Routine.Domain.certify` is for a certificate that states exactly the specification of its
routine. A solver whose certificate states a different `Specification` (a residual bound read
on values, a count in calls of an oracle) uses `Routine.Domain.algorithm`, and
`(…).withCountPoly` for its closed-form work; `NLAlib/Krylov/CG/HSCG/Certification.lean` is
the model for that.

### 2.6 The readable statement

```lean
theorem sum2_checked (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
    (d : Fin 1 → ℕ) (x y : Fin (d 0) → ℝ) (I : Interp ScalarOp CmpTst ℝ)
    (hI : (sum2Model M).contracts d (sum2Domain.input d (x, y) trivial) I) (τ : Tape ℝ) :
    ∃ st, exec sum2Program I (sum2Model M).resources sum2Domain.formats τ d
        (sum2Domain.memory d (x, y)) = some st ∧
      (sum2Model M).resources.work st.cost ≤ 24 * d 0 + 63 ∧
      sum2Domain.bytes d + st.peak ≤
        sum2Domain.bytes d + staticPeak (sum2Model M).resources sum2Program d ∧
      ∃ v, st.mem.Holds Codec.scalar 2 v ∧
        |v - (∑ i, x i + ∑ i, y i)| ≤
          ((1 + u) * (1 + u) ^ (d 0 - 1) - 1) * (∑ i, |x i| + ∑ i, |y i|) := by
  obtain ⟨st, hr, hw, hm, ys, hys, hpost⟩ :=
    sum2Domain.checked_post (Sp := fun _ _ => sum2Spec id u) (work := sum2Work)
      (sum2Algorithm M u hM hu) d trivial (x, y) trivial I hI τ
  refine ⟨st, hr, hw, hm, ?_⟩
  read_outputs hys as (zs)
  …
```

(`Examples/RoutineCertification.lean`; the rest of the proof rewrites sums over positions as
sums over `Fin`.) The statement mentions the evaluator `exec`, the inputs as mathematical
values and the output as a value held by a buffer (`Mem.Holds codec i v`), and nothing of
routines, judgments or the program logic. `checked_post` gives it from a certificate built by
`certify`; **read_outputs** names the reported blocks.

A block-valued output is stated with the codec of its type: for a vector,
`st.mem.Holds (Codec.vector (d 0)) 2 fun i => M.add (x i) (y i)`. `Mem.Holds c i a` says that
buffer `i` reads as the encoding of `a`, here `List.ofFn` of the function. After
**read_outputs** `hys as (zs)`, rewrite the block `zs` given by the postcondition as that
encoding, with a lemma about values, and close with the read:

```lean
  read_outputs hys as (zs)
  obtain rfl : zs = vaddF M (vec (List.ofFn x)) (vec (List.ofFn y)) (d 0) := hpost
  rw [vaddF_ofFn] at hzs
  exact hzs
```

(`Examples/VectorSum.lean`, `vadd_checked`.) When the statement is about the decoded value and
not a formula for it, `Mem.holds_decode c hzs` gives `st.mem.Holds c i (c.decode zs)` from the
read.

The shortest form, for any certificate, is
the proposition `Routine.Domain.Checked`, proved by `Routine.Domain.checked_all`
(`NLAlib/Krylov/CG/HSPCG/Certification.lean`, `algorithm_checked`, two lines). The docstring says in words
what the statement says, and what a reader must check beyond it (declared oracles; the
probability theorem, when the deterministic claim is termination).

### 2.7 The certificate check

`scripts/OpsPrograms.lean` finds every `Algorithm` of the library and computes one line for it:

```
NLAlib.Ops.Examples.Routines.sum2Algorithm hyps=2 uniform=yes confined=yes charged=yes budget=manifest work=closed scratch=manifest problem=derived derived=0 unstored=no oracles=none claim=none
```

(`scripts/ops_certificates.txt`.) The script imports the library, so it sees a certificate only
once its file is imported by `NLAlib.lean` (section 3, step 5) and the library is built; until
then neither the check nor the report below knows the name. A new certificate passes without a
recorded line when its
model is confined, its work is `closed` and its problem is `derived`; otherwise the check
fails and says which field. Do not add or change a line of that file to pass
(`AGENTS.md`, rule 1): fix the certificate, or report why it cannot conform. Read what your
certificate states, as a reviewer will, with

```
OPS_CERTIFICATES_REPORT=sum2Algorithm lake env lean scripts/OpsPrograms.lean
```

The fields are explained in the [Ops README](../../NLAlib/Ops/README.md), "What the model must
also satisfy".

## 3. Order of work

1. State the mathematics first: the pure function and the error lemma about values
   (`sum2_error`), with no memory in them.
2. Write the routine and its specification; check the file compiles before proving anything.
3. Prove the judgment. Write **routine_intro** `…` and then one tactic per statement of the tree,
   looking at the goal after each.
4. Problem, model, program, count, certificate, `_checked`, in a `Certification.lean`.
5. A new file: add it to `NLAlib.lean` with `lake exe mk_all --module --lib NLAlib`. A new
   module in a subdirectory of `NLAlib/Ops` other than `Logic/` and `Tools/` is also imported
   by `NLAlib/Ops/Tools/LintAll.lean` (a unit test of the checks fails otherwise).
6. Names ([programs](programs.md), "Names of routines, files and certificates"). A routine
   written in one `routine%` block is `foo`, with `fooSpec` and the judgment named `foo` with
   the suffix `meets`; when its tree is a separate definition `foo`, the routine is
   `fooRoutine`. A solver's certificate is in its own namespace `X.Certification`, with the
   plain names `inputs`, `problem`, `model`, `program`, `algorithm`, `algorithm_checked`. A
   namespace that holds several routines and their certificates, as the example files do,
   prefixes each with its routine: `sum2Domain`, `sum2Problem`, `sum2Model`, `sum2Program`,
   `sum2Algorithm`, `sum2_checked`.
7. Checks while working: `lake lean <file>` checks one file and writes nothing, so use it for a
   file nothing imports yet; `LEAN_NUM_THREADS=4 lake build <Module.Name>` builds the module
   and what it imports, and is needed before another file can import it. Then
   `python3 scripts/check_rules.py --files <files>`. At the end,
   `bash scripts/stage_check.sh` ([CONTRIBUTING](../../CONTRIBUTING.md), "Pull requests and
   checks").

## 4. Pitfalls

- **Names the tactics introduce.** **routine_intro** introduces `τ`, `m`, `hlive`, `hl`, `hpre`,
  `hrooms`, `hroom`, `hr` and facts named from the operands (`hxs`, `hxz`). A dimension or
  operand with one of those names shadows it: for a routine with a dimension called `m`, write
  **routine_intro** `[m, n] (…) reads (…) memory μ`. In a `Routine.Domain` and in a
  `Specification`, `d : Fin r → ℕ` is the vector of sizes and `d 0` the first; do not also call
  a dimension `d` there.
- **Two spellings of a dimension.** `routine%` and `spec%` read dimension `i` of the list of
  dimensions as `d.getD i 0`. The block relations of the operation catalog read the first as
  `d.headD 0`. On a literal list `[n, k]` both compute; on a variable `d` they are not
  interchangeable by `rfl`. When you write by hand something that must agree with what the
  notation generates (the `draws` of a routine, a `Routine.Spec` without `spec%`), use
  `d.getD i 0`, and let **routine_intro** name the dimensions before reasoning about lengths.
- **The problem is an `abbrev`.** `abbrev problem := inputs.problem` (or `sum2Domain.problem`).
  With `def`, the model, the specification and `checked_all` no longer see that the problem is
  the one of the domain, and the errors are unification failures far from the cause.
- **A postcondition does not unfold under `simp`.** After **routine_exit**, or in `hpost` after a
  `call`, the postcondition of a `spec%` is closed by `exact` with a term of the written
  statement, or restated with `have h : <the statement> := hpost` or `change`: it holds by
  definitional unfolding. `simp` reports no progress, and `rw` finds no pattern. For a
  specification used often, state the unfolding once as a lemma proved by `Iff.rfl`
  (`myIntegrateSpec_post` in `Examples/Integrator.lean`).
- **One-cell blocks.** A block of length one is a list; get its cell with
  `obtain ⟨v, hv, rfl⟩ := Store.readBlock_one_eq_some.mp hzs` before the `step` that reads it.
- **A cell of a block.** A `step` whose call reads `x[i]` looks for the cell at the current
  memory first, and otherwise takes it out of a block read as the sub-block
  `List.take 1 (List.drop i xs)`. The postcondition is then about that list and does not
  reduce: the pattern fails with

  ```
  Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)
    (match [List.take 1 (List.drop i xs), List.take 1 (List.drop i ys)] with
      | [[a], [b]] => some [[M.add a b]]
      | x => none) = some [[v]]
  ```

  and a goal `hdom` about the same lists may be left. State each cell before the `step`:
  `have hxi : m₁.store.get x.1 (x.2 + i) = some (vec xs i) := Store.get_of_readBlock hxs₁ hi default`
  (section 2.3, the loop over cells).
- **Implicit operations.** A routine generic in `Op` needs `(Op := Op) (Tst := Tst)` where it is
  mentioned without an expected type (in a `run`, in the statement of its judgment).
- **A side goal a tactic leaves.** When the context lacks a fact, `call` leaves a goal named
  `hlive`, `hsep`, `hr`, `hpre`, `hroom` or `hle`, and `step` one named `hadm`, `hlive`, `hr`,
  `hdom`, `hz`, `hap` or `hle`. The usual causes: a block read (`hr`) that was not carried
  across the previous frame (`keep`); a precondition (`hpre`) that is not in the context
  (`call h … (pre := t) as …`); a length that `omega` needs stated. Prove the missing fact
  before the tactic; do not unfold the tree.
- **Do not prove against the tree of a callee.** If a `call` needs more than the callee's
  specification gives, strengthen that specification (and its one judgment); do not unfold the
  callee.
- **Do not weaken the problem to finish.** A hypothesis you need belongs in `accepts` (inputs)
  or in the model (operations), where the reader sees it; an extra hypothesis on the
  certificate is counted (`hyps=`) and printed by the report.
- **One build at a time.** `lake` and the stage check assume nothing else is building in the
  checkout; two builds on a machine with little memory are killed and leave stale outputs.
  Compile one module with `LEAN_NUM_THREADS=4 lake build <Module.Name>`, one file with
  `lake lean <file>`.
- **The stage script and CI.** `scripts/stage_check.sh` runs what CI runs on Linux, the unit
  tests of the check scripts included. CI alone also runs those tests on Windows and
  `mk_all --check` for `NLAlibTools`. A pass of the stage script on a stale build proves
  nothing: it rebuilds, so let it finish.
- **`lake env lean` is not `lake lean`.** The first ignores the options of `lakefile.toml`
  (`autoImplicit` is then on and a typo becomes a variable). The certificate report is the one
  documented use of `lake env lean`.
