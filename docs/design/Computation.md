# Design note: computation, stage 1 (exact arithmetic, counts, memory, oracles, draws)

> Archived execution-system design. The former evaluator, programs, target registry and
> emission tooling are retired. The current interfaces are documented in
> [the Ops migration](Ops-Migration.md) and [the program guide](../contributing/programs.md).
> Mathematical analysis is retained; program and registry names below describe the historical system.

Status recorded on 2026-11-04: this note includes historical proposals and
skeletons. Complete registered exact program proofs now cover Gram–Schmidt, Hutch++, CG
and Lanczos. The current Krylov implementations and their unchanged approved targets are
in `Krylov/LinearSystems/CGProgram.lean` and `Krylov/Processes/LanczosProgram.lean`.
The tree emitter exists and remains unverified; the target approval file exists.
See [Implementation coverage](Implementation-Coverage.md) and
[the integration record](Krylov-Implementation-Integration.md) for current evidence and
remaining rounded execution and machine-format obligations.


**Approved by the maintainer, 2026-10-23:** D1 option C (deep embedding); all other decisions as recommended; D16 to D19 (added after the first approval) as recommended; the same day, the change of section "Guarantees" (results are instances of access models, the scripts demoted); the same day, the two changes of section "First-order programs and target statements" (targets are library definitions; witnesses are first-order programs), whose design is that section.

**History.** Drafts 1 to 6, 2026-10-22 and 23, each after a bounded review. The fourth draft's
decisions (D1 to D15) were approved on 2026-10-23. D16 to D19, added for the maintainer's
requirement to reduce higher-level error models to bit operations ("we want to be able to reduce
certain higher level models of error to bit operations easily"), were approved the same day.
Targets: Hutch++ in stage 1, Lanczos in stage 1b.

**Summary.** Algorithms are small programs that work on memory buffers as BLAS code does. They
allocate scoped buffers, overwrite them in place, call BLAS kernels, draw random numbers, and
multiply blocks of vectors by the matrix through an oracle. Running a program gives its result,
its counts and its memory. One proved theorem replaces any scalar instruction or oracle call by a
certified implementation; comparisons, read-only reads and draws are kept. The result is the
same, and the costs are substituted kind by kind. This gives dense and sparse matvecs from the
oracle, and integer and bit operations from floating (here fixed-point) arithmetic. An error
analysis against a rounding contract, which now requires the operations to succeed in range and
not only to be accurate, thus reduces to a word-level program and a bit-operation count by
substitution. Hutch++ keeps its results: exact value, 2 loads, `2k + ℓ` matvecs, operation and
memory counts, and the Gaussian tail with no new probability. Programs print as NumPy and run in
Lean with `Float`.

**What was elaborated and run.** Every Lean definition and statement below was elaborated
during the design, against the library at `88016e3`, in scratch files whose content is now in
`NLAlib/Computation/` and the topic files of §11. The core (syntax, semantics, the
substitution theorem) elaborated with no `sorry`, using only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

Proved:
* The substitution theorem `RunsWithin.subst` with `exec_subst_sim`. Its read-only hypothesis is
  now general: the concrete read-only data extends the abstract data, with an identity cost on
  `rom` reads. So substitutions chain, and sparse Hutch++ can be taken on to the bit level.
* The oracle corollary `RunsWithin.substOracle`.
* `isRelErrSem_exactSem`: exact real arithmetic meets the **full** contract (error and success
  clauses, every operation family).
* `not_isRelErrSem_failSem`: the always-failing semantics does not meet it.
* The transfer lemma, the Gaussian tail with draws, and sparse Hutch++. These three rest on the
  stubbed realisations, certificates and tape laws.

Statements elaborated with `sorry`, for the skeleton (eleven), plus a deliberately cheating
realisation kept as the E3 test fixture:
* the kernel specifications `exec_dot` and `exec_axpy`;
* the frame lemma `Holds.write`;
* the Hutch++ realisation;
* the two tape laws;
* the COO certificate;
* the two Lanczos realisations;
* the fixed-point certificate and the fixed-point error contract.

Runs, unchanged:
* The fixed-point example gives the same word at both levels.
* `Float` and NumPy reproduce the table.
* The E1 and E3 checks give the same verdicts.

---

## 1. Decisions (approved 2026-10-23)

### D1. Encoding: structured programs over buffers, two-sorted PHOAS (option C)

Why C was chosen. Tracking memory (point 1) ruled out values held as host data (A). The free
monad over buffer operations (B) met every point except size-generic emission (point 6) and
syntactic control cost for the bit-cost stage. C buys both, for about 900 to 1,500 more lines.
The maintainer asked for code generation, so C was chosen. A first-order deep embedding (D)
gave nothing over C.

### D3. The run: deterministic, state-passing, partial oracles, random tape

`exec I s st` is a deterministic function into `Option`. The interpretation `I` holds:
* the value semantics;
* the charge per kind;
* the tape;
* the oracles, partial (`none` marks an invalid query);
* the read-only data and its size.

Randomness comes from the tape (D12), so the run is a function of `ω`. Still out of reach:
stateful adversarial oracles. Alternatives: a monadic or measure-valued run. Recommendation: this
run.


### D4. Oracles: block calls counted as loads and matvecs; implementations in their own files

* `apply o p dst dOff src sOff cols` computes `A_o · X` for an `N × cols` block. It charges one
  `load o` and `cols` counts of `matvec o`.
* Oracle names carry their own matrices: `exactInterp (A : ι → Matrix (Fin N) (Fin N) 𝕜) ξ`. So
  `Aᴴ` is a second name whose matrix the theorem sets to `(A o)ᴴ`.
* The algorithm theorem states loads, matvecs and its own operations only (point 2).
* An implementation is certified once, by `ImplementsOracle`, and composition is the proved
  theorem:

The current certificates and substitution theorems are displayed under D18 (oracle calls and
scalar instructions are substituted by one theorem; the oracle theorem is its corollary).

The review's four objections are each a hypothesis or a change of form:
* (a) Both interpretations use the standard charge (`hc`, `hc'`).
* (b) The concrete read-only data extends the abstract data (`hrom`; for the oracle corollary,
  the abstract interpretation has none), so a program that reads `rom` cannot succeed abstractly
  and then fail concretely.
* (c) The conclusion keeps the store, tape positions and current memory of an abstract final state
  satisfying `Q`, not `Q` itself, because the concrete peak and counts differ. In practice `Q`
  reads output cells, so it transfers.
* (d) The certificate quantifies over index expressions, as `substOracle` passes them.

The proof is a simulation, `Sim`: equal store, tape and current memory; concrete count at most
the substituted abstract count; concrete peak at most abstract peak plus scratch; and the
abstract invariant that current memory is at most peak. Alternatives: implementation data as an
input buffer (every address shifts, and the proof needs a store renaming); one effect per access
mode. Decision: as above, in the general form of D18.


### D7. Layer and placement

`NLAlib/Computation/` at layer 0 holds the syntax, semantics, interface, composition, exact
semantics and layout, BLAS, and the dense and COO implementations; it imports Mathlib and
ForMathlib only. Programs live with their specifications (`GramSchmidtProgram.lean`,
`HutchPlusPlusProgram.lean`, `Krylov/Processes/LanczosProgram.lean`). The tape laws go in
`RandomMatrix/Tape.lean`. The emitter and the `Float` interpreter go in a tools library
`NLAlibTools` (flag).


### D8. Precision tags, checked at run time

Tags label buffers and operations; a mismatch fails. Each interpretation has one carrier: `𝕜` at
the exact level, unbounded `ℤ` words at the format and word levels (D16), where every format and
integer width is a tag decoded from words. **What is lost**: every realisation must discharge tag-mismatch and
out-of-bounds failures explicitly, at every write. The kernel specifications carry them as the
hypothesis that the final write succeeds (`h₁ : st.store.write … = some s₁`). Alternative: a store
typed by tags (dependent arrays), which removes the tag check but not the bounds check, and is
heavier in every lemma. Recommendation: runtime tags.


### D9. Index layout: flat column-major `ℕ` inside programs, `Fin N` in theorems

Realisations are stated at `Fin N`; a general `Fintype n` reaches them through reindexing lemmas
for the specifications. `hutchpp_reindex` and `lanczosState_reindex` are new work, about 150
lines, now in the size table. Alternative: a `FinEnum` layout map in every realisation, which
needs the same lemmas. Recommendation: `Fin N` plus reindexing.


### D11. Memory model: scoped allocation, two-sorted variables (memory in bits: D17)

* **Two sorts (new; the fix for the forged handle).** `Stmt P ι VB VI`: `alloc` binds a handle of
  sort `VB`, `loop` binds an index of sort `VI`, `IExp VI` is index arithmetic, and
  `Cell VB VI` pairs a handle with an index. A loop variable cannot be used as a handle, and a
  handle cannot enter index arithmetic: both are type errors (checked). The emitter prints
  `b3[i2]`, never `i2[0]`.
* **What the scoping claim covers, exactly.** For a program that is generic in `VB` and `VI` and
  passes E1, every handle it uses is either a parameter (an input buffer, live for the whole run)
  or bound by an enclosing `alloc`, whose buffer is live throughout the body. Hence no use after
  free, no double free (there is no `free`), and no leak (the buffer is popped when the body ends).
  It does not cover:
  * interpreter-level terms at `VB := ℕ` (handles can be any number there; E1 rejects such
    definitions as programs);
  * the caller passing wrong input addresses (a failure or aliasing at run time);
  * implementation files, where `cooImpl` takes a host pattern.
* Alternative: explicit `free` with non-nested lifetimes, which no target needs.
* Units: cells per tag. Fresh cells are uninitialised, and reading one fails.


### D12. Random draws from an i.i.d. tape

`draw p d dst` writes the next tape value of distribution `d` and charges `draw p d`; the tape has
law `iidSequence` per distribution. The tape laws (`hasLaw_tapeMatrix_of_hasLaw_iidSequence`,
`indepFun_tapeMatrix_of_hasLaw_iidSequence`) need an injective-reindexing lemma for
`iidSequence`, which `Probability/Law.lean` lacks; it is included in the 200-line estimate.


### D13. BLAS kernels: derived programs inside `named` nodes

Each kernel has one specification of five parts: value, frame, tape, memory and counts. Offsets
and lengths are index expressions with `eval` hypotheses. Kernels that are not elementwise carry
disjointness hypotheses; in-place kernels allow exact aliasing and forbid partial overlap
(`exec_axpy`).


### D14. Accounting for read-only data

`Interp.romSize : P → ℕ` is the constant memory of an implementation's data. `RunsWithin` bounds
`peak + romSize`, and the composition theorem adds `I'.romSize` (proved). The sparse corollary
therefore certifies `2N(k + ℓ) + 5 + nnz`; without `romSize` it would certify
`2N(k + ℓ) + 5` while holding `nnz` values.
* Inputs and outputs are in the initial store and count from the start.
* The abstract oracle's `A` lives outside the store and is uncounted, as an oracle should be.
* An implementation's `A` is read-only data, counted through `romSize`.
* Index storage of a sparse pattern stays uncounted host data until integer buffers exist.

Alternative: read-only data uncounted, stated plainly. Recommendation: counted, as implemented.


### D15. Lanczos scope: designed now, proved in stage 1b

The program, its counts, memory and realisation statements against `lanczosState` exist now, and
Lanczos shaped the signature (`mod`, `re`, `whileFuel`). The proofs (a loop invariant over three
rotating slots, about 700 lines) are stage 1b, after Hutch++ has exercised the core and BLAS
lemmas. Alternative: both in stage 1, which delays the first complete result by the Lanczos proof.
Recommendation: 1b.


### Settled: D2, D5, D6, D10

* D2: failing operations. Also failing: uninitialised reads, out of bounds, tag mismatch, an
  invalid oracle query, running out of fuel.
* D5: `RunsWithin` is an upper bound (now on counts and on `peak + romSize`).
* D6: in-place rank-revealing modified Gram–Schmidt, realised with no rank hypothesis.
* D10: universe 0.
* Operation kinds, names (`<spec>Prog`, `runsWithin_<spec>Prog`, `<spec>Count`), and `ℓ ≥ 1`
  for `hutchppProg`.


### Decisions added for bit-level reduction (approved 2026-10-23)

Four decisions, all from the requirement to reduce higher-level error models to bit operations.

### D16. The carrier of word-level interpretations

The carrier `K` is a parameter of `Interp`, the store and the run. The exact interpretation keeps
`K := 𝕜`. `RunsWithin.subst` links only interpretations with the **same** `K` (its simulation
uses the identity store relation). So "one carrier" always means one carrier per interpretation:
the exact level (`𝕜`) and the word level are related through the contract and its decoding
(§7), never by substitution.

The options weighed (D8 follows the decision):
* **(i) Unbounded `ℤ` words, decoded per tag (chosen).** A floating cell holds its bit
  pattern as an integer, and integer and bit cells are integers too. The semantics enforces each
  tag's range and width, failing on overflow or wrapping, as chosen per tag. `convert` is
  reinterpretation or conversion. Substitution keeps the identity store relation, so floating
  operations reduce to integer programs by the proved theorem.
  * Stage 1 cost: none; elaborated.
  * Stage 2 cost: per-format encode and decode, and the proof that each format semantics meets the
    contract.
* **(ii) A sum or dependent carrier** (`Σ p, α p`, or an inductive of values). Values are typed
  by format, and `convert` is explicit encode and decode. Reduction to bits is then a data
  refinement: a store relation between carriers, and a second simulation proof (estimate 500
  lines), which §7.3 needs anyway for one-bit-per-cell layouts.
  * Stage 1 cost: none.
  * Stage 2 cost: that simulation, plus heavier lemmas everywhere a cell is read.
* **(iii) `BitVec` per width** (Lean's `BitVec w`, with `bv_decide` available). Widths are exact
  in types and overflow is impossible by construction. But the carrier is dependent as in (ii),
  with the same data-refinement cost, plus `BitVec` arithmetic in every word-level proof. Proofs
  under (i) can still pass through `BitVec` inside decode lemmas.

### D17. Memory in bits

What was added:
* `Interp.width : P → ℕ`, bits per cell;
* the state fields `curW` and `peakW`, current and peak bits over all tags, updated at allocation
  and freeing;
* a sixth part in every kernel specification: bit memory unchanged, bit peak raised by at most
  the scratch.

What it means:
* `RunsWithin` itself bounds cells only: its bound `m` has no bit component, and `romSize` has no
  bit form.
* The substitution theorem bounds the concrete `peakW` **relative to the abstract final state's
  `peakW`** plus the bit scratch. It is not an absolute bound.
* `exactInterp` has width 0, so bit memory is 0 at the exact level and meaningful only for
  word-level interpretations.

Alternatives:
* no joint tracking: the sum of per-tag peaks times widths is a sound but loose upper bound;
* a bit component in `RunsWithin` itself, which changes every statement;
* a separate predicate `RunsWithinBits` with `romBits = Σ romSize · width`, added when the first
  word-level theorem needs it.

Decision: keep the fields now (adding them later would change every kernel specification),
keep `RunsWithin` in cells, and add `RunsWithinBits` with the first word-level result.

### D18. General substitution, the new operations, and the changed certificates

What was added:
* `Stmt.subst implI implO`, `substCountG`, `ImplementsInstr`, and `RunsWithin.subst` (proved),
  with the oracle theorem as its corollary.
* `BinOp.shl`, `shr`, `band`, `bor`, `bxor`, `UnOp.bnot`, and the instruction
  `convert p q dst src`.
* The read-only hypothesis generalised to "the concrete data extends the abstract data", with
  `hcostRom`.
* D4's certificate and theorem changed as follows (current signatures):
```lean
def ImplementsOracle (I : Interp P ι K (OpCount P ι)) (I' : Interp P ι' K (OpCount P ι'))
    (impl : ι → P → ℕ → IExp ℕ → ℕ → IExp ℕ → IExp ℕ → Stmt P ι' ℕ ℕ)
    (cost : OpKind P ι → OpCount P ι') (scratch : P → ℕ) (scratchW : ℕ) : Prop :=
  ∀ o p dst dOff src sOff cols st X Y s₁,
    st.store.readBlock p src sOff.eval (I.height o * cols.eval) = some X →
    I.oracle o cols.eval X = some Y → st.store.writeBlock p dst dOff.eval Y = some s₁ →
    ∃ st', exec I' (impl o p dst dOff src sOff cols) st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt ≤ st.cnt + (cost (.load o) + cols.eval • cost (.matvec o)) ∧
      (∀ q, st'.peak q ≤ max (st.peak q) (st.cur q + scratch q)) ∧
      st'.peakW ≤ max st.peakW (st.curW + scratchW)

def ImplementsInstr (I : Interp P ι K C) (I' : Interp P ι' K (OpCount P ι'))
    (implI : Instr P ℕ ℕ → Stmt P ι' ℕ ℕ) (cost : OpKind P ι → OpCount P ι')
    (scratch : P → ℕ) (scratchW : ℕ) : Prop :=
  ∀ i st r, i.run I.sem I.tape st.store st.pos = some r →
    ∃ st', exec I' (implI i) st = some st' ∧ st'.store = r.1 ∧ st'.pos = r.2 ∧
      st'.cur = st.cur ∧ st'.curW = st.curW ∧ st'.cnt ≤ st.cnt + cost i.kind ∧
      (∀ q, st'.peak q ≤ max (st.peak q) (st.cur q + scratch q)) ∧
      st'.peakW ≤ max st.peakW (st.curW + scratchW)

theorem RunsWithin.subst (hcmp : I'.sem.cmp = I.sem.cmp)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (hc' : ∀ k, I'.charge k = Finsupp.single k 1)
    (hwidth : I'.width = I.width) (hrom : ∀ i v, I.rom i = some v → I'.rom i = some v)
    (hcostCmp : ∀ p, cost (.cmp p) = Finsupp.single (.cmp p) 1)
    (hcostRom : ∀ p, cost (.rom p) = Finsupp.single (.rom p) 1)
    (himplI : ImplementsInstr I I' implI cost scratch scratchW)
    (himplO : ImplementsOracle I I' implO cost scratch scratchW)
    {s} {st₀} (h0 : st₀.cnt = 0) (hcp : ∀ q, st₀.cur q ≤ st₀.peak q)
    (hcpW : st₀.curW ≤ st₀.peakW) {c} {m} {Q} (h : RunsWithin I s st₀ c m Q) :
    ∃ st₁', exec I' (s.subst implI implO) (st₀.withCnt 0) = some st₁' ∧
      st₁'.cnt ≤ substCountG cost c ∧
      (∀ q, st₁'.peak q + I'.romSize q ≤ m q + scratch q + I'.romSize q) ∧
      (∃ st, Q st ∧ st₁'.store = st.store ∧ st₁'.pos = st.pos ∧ st₁'.cur = st.cur ∧
        st₁'.peakW ≤ st.peakW + scratchW)

theorem RunsWithin.substOracle (hsem : I'.sem = I.sem) (htape : I'.tape = I.tape)
    (hc) (hc') (hwidth : I'.width = I.width) (hrom : ∀ i, I.rom i = none)
    (himpl : ImplementsOracle I I' implO (substKind cost) scratch scratchW)
    {s} {st₀} (h0 : st₀.cnt = 0) (hcp : ∀ q, st₀.cur q ≤ st₀.peak q)
    (hcpW : st₀.curW ≤ st₀.peakW) {c} {m} {Q} (h : RunsWithin I s st₀ c m Q) :
    RunsWithin I' (s.substOracle implO) (st₀.withCnt 0) (substCount cost c)
      (fun q => m q + scratch q + I'.romSize q)
      (fun st' => ∃ st, Q st ∧ st'.store = st.store ∧ st'.pos = st.pos ∧ st'.cur = st.cur)
```

Alternatives:
* oracle-only substitution (the fourth draft's D4), with scalar refinement as a separate
  theorem in stage 2;
* bit operations as a separate instruction family typed by width (natural with D16 (iii)).

Decision: as implemented. It is one theorem for every substitution, and it is proved.

### D19. The shape of error contracts

An error-only `IsRelErrSem` (the fifth draft's) had only an error clause, for binary arithmetic. The semantics
that always fails met it, so a contract-level theorem asserting success (as `RunsWithin` does)
was unprovable. The proposal's own warning applies: "if it succeeds it is accurate" is not
enough.

The contract is now a structure with an error clause and a **success clause** per operation
family, under a range predicate `safe : P → ℝ → Prop`:
* arithmetic: `bin_err`, and `bin_ok` (succeeds when the exact result is in range, the divisor
  nonzero);
* literals: `lit_err`, `lit_ok`;
* `neg`, `conj`, `re`: exact and total on real decodings;
* `sqrt`: `sqrt_err`, `sqrt_ok` (on nonnegative decodings);
* comparisons: exact on decoded values (Gram–Schmidt branches on them);
* `convert`: relative error at the target tag, succeeding when in range there.

Both are proved: `isRelErrSem_exactSem` (exact real arithmetic meets the full contract with
`u = 0` and every value in range, for `𝕜 = ℝ`), and `not_isRelErrSem_failSem`.

Variants to define in stage 2 with the same shape: relative error with underflow, absolute error,
and stochastic mean-zero error. Alternatives:
* error-only contracts: unsound for theorems that assert success;
* no contracts, only specified formats: each format would be analysed separately;
* relational (nondeterministic) semantics: these need a run over sets of states.

Decision: the clause structure, one per error model.

---
## 2. The model in one page

(D18 adds `convert` and the integer and bit operations to the instruction set, and D17 the width
and bit-memory fields.)

```lean
inductive Instr (P VB VI : Type) where          -- each writes one destination cell
  | lit (p : P) (dst : Cell VB VI) (q : ℚ) | litIdx (p : P) (dst : Cell VB VI) (e : IExp VI)
  | bin (p : P) (b : BinOp) (dst x y : Cell VB VI) | un (p : P) (u : UnOp) (dst x : Cell VB VI)
  | copy (p : P) (dst src : Cell VB VI) | draw (p : P) (d : Dist) (dst : Cell VB VI)
inductive Stmt (P ι VB VI : Type) where
  | skip | seq (s t : Stmt P ι VB VI) | instr (i : Instr P VB VI)
  | apply (o : ι) (p : P) (dst : VB) (dOff : IExp VI) (src : VB) (sOff cols : IExp VI)
  | rom (p : P) (dst : Cell VB VI) (i : IExp VI)
  | alloc (p : P) (len : IExp VI) (body : VB → Stmt P ι VB VI)
  | loop (n : IExp VI) (body : VI → Stmt P ι VB VI)
  | whileFuel (fuel : IExp VI) (p : P) (c : CmpOp) (x y : Cell VB VI) (body : Stmt P ι VB VI)
  | ite (p : P) (c : CmpOp) (x y : Cell VB VI) (t e : Stmt P ι VB VI)
  | named (name : String) (args : List (Arg VB VI)) (body : Stmt P ι VB VI)
```

* The scalar instructions form one constructor with an interpretation-independent kind
  (`Instr.kind`). That made the composition proof uniform over them.
* The store is a stack of tagged buffers of optional cells.
* `exec` runs at `VB := ℕ`, `VI := ℕ`.
* `RunsWithin I s st₀ c m Q` means: success, counts at most `c` more than at the start,
  `peak + romSize ≤ m` per tag, and `Q` of the final state.
* Counts are `OpKind P ι →₀ ℕ`, with kinds `bin`, `un` (`neg`, `conj`, `re`, `sqrt`), `lit`,
  `cmp`, `copy`, `draw`, `rom`, `load`, `matvec`.

## 3. Objects (§5.3 rows)

| Concept | Spelling | Bridge |
|---|---|---|
| program | `Computation.Stmt P ι VB VI` (handles `VB`, indices `VI`), `Instr P VB VI` | none; Mathlib has no syntax for imperative programs (searched) |
| `do` notation | `Computation.Builder P ι VB VI β := (β → Stmt P ι VB VI) → Stmt P ι VB VI` | Mathlib's `ContT (Stmt P ι VB VI) Id β` is the same type; the skeleton defines `Builder` as that abbreviation, so no deviation arises |
| index expression, cell | `IExp VI`, `Cell VB VI` | none |
| store, state, interpretation, run | `Store P K`, `St P K C` (with `curW`, `peakW`), `Interp P ι K C` (with `rom`, `romSize`, `width`), `exec` | none |
| value semantics | `ScalarSem P K`; exact `exactSem` | none |
| interface | `RunsWithin I s st₀ c m Q` | none |
| counts | `OpCount P ι`, weights `Finsupp.weight`, `substCountG`, `substCount` | Mathlib `Finsupp` |
| layout | `flatten`, `unflatten`, `tapeMatrix x off N k : Matrix (Fin N) (Fin k) 𝕜`, `Holds` | `Matrix.of` |
| oracle semantics | `matOracle A`, `exactInterp (A : ι → Matrix …) ξ` | `Matrix` multiplication |
| substitution | `Stmt.subst`, `Stmt.substOracle`, `ImplementsInstr`, `ImplementsOracle`, `Sim`, `St.withCnt` | none |
| implementations | `denseImpl`, `cooImpl`, `cooMatrix`, `cooInterp`, `cooCost` | none |
| contracts | `IsRelErrSem u dec safe sem` | none |
| tape law | `HasLaw ξ (iidSequence ν) μ` | the library's `iidSequence` |
| BLAS | `dot`, `axpy`, `scal`, `rscl`, `copyv`, `nrm2`, `gemv`, `gemm` (and `ger`) | none |

## 4. BLAS and the kernel specification family

The kernels are `dot`, `axpy`, `scal`, `rscl`, `copyv`, `nrm2`, `gemv` and `gemm`, with `ger` to
add. Specifications now take index-expression arguments with `eval` hypotheses. Elaborated:

```lean
theorem exec_dot (I) (hI : I.sem = exactSem) (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) (xs ys : ℕ → 𝕜)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hy : ∀ i < n.eval, st.store.read p y (yo.eval + i) = some (ys i))
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i) (s₁)
    (h₁ : st.store.write p dst.buf dst.idx.eval (∑ i ∈ Finset.range n.eval, star (xs i) * ys i)
      = some s₁) :
    ∃ st', exec I (dot p dst x xo y yo n).run st = some st' ∧ st'.store = s₁ ∧ st'.pos = st.pos ∧
      st'.cur = st.cur ∧ st'.cnt = st.cnt + (n.eval • (single (.un p .conj) 1 +
        single (.bin p .mul) 1 + single (.bin p .add) 1) + single (.lit p) 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1))

theorem exec_axpy … (hay : a.buf = y → ∀ i < n.eval, a.idx.eval ≠ yo.eval + i)
    (hxy : x = y → ∀ i < n.eval, ∀ j < n.eval, xo.eval + i = yo.eval + j → i = j) (s₁)
    (h₁ : st.store.writeBlock p y yo.eval ((List.range n.eval).toArray.map
      fun i => av * xs i + ys i) = some s₁) : ∃ st', … ∧ st'.store = s₁ ∧ …

theorem Holds.write (h : Holds s p b off M) (hw : s.write p' b' i' v = some s')
    (hout : b' = b → i' < off ∨ off + N * k ≤ i') : Holds s' p b off M
```

Algorithm proofs address matrices through flat indices `off + i + N * j`. The side conditions are
nonlinear, so `omega` will not close them. A column-arithmetic lemma set handles them (`i + N * j`
injective for `i < N`, columns disjoint, a block lies below `off + N * k`); it is now in the
`Exact.lean` estimate.

## 5. Programs and statements (elaborated)

**Hutch++** (two loads: the second product is batched, `A [Q | G']`; without batching, 3 loads and
the same `2k + ℓ` matvecs; batching costs the `N(k + ℓ)` destination that sets the peak):

```lean
/-- **Hutch++ as a program.** It draws an `N × k` sketch and `N × ℓ` probes from the tape `d`,
forms `Y = A S` (load 1), orthonormalises `Y` in place by rank-revealing modified Gram–Schmidt,
projects the probes in place, forms `A [Q G']` (load 2), and writes
`tr(Qᴴ A Q) + tr(G'ᴴ A G') / ℓ` into `out`. -/
def hutchppProg (p : P) (o : ι) (d : Dist) (N k ℓ : IExp VI) (out : Cell VB VI) :
    Builder P ι VB VI Unit := do
  let B ← alloc p (N * (k + ℓ))
  scope do
    let S ← alloc p (N * k)
    forRange (N * k) fun i => ins (.draw p d ⟨S, .var i⟩)
    stmt (.apply o p B 0 S 0 k)
  forRange (N * ℓ) fun i => ins (.draw p d ⟨B, N * k + .var i⟩)
  let t ← alloc p 2
  forRange k fun j => do
    orthAgainst p N B (.var j) B (N * .var j) ⟨t, 0⟩
    dot p ⟨t, 1⟩ B (N * .var j) B (N * .var j) N
    ins (.lit p ⟨t, 0⟩ 0)
    ifThenElse p .eq ⟨t, 1⟩ ⟨t, 0⟩ (pure ()) do
      ins (.un p .sqrt ⟨t, 1⟩ ⟨t, 1⟩)
      rscl p ⟨t, 1⟩ B (N * .var j) N
  forRange ℓ fun j => orthAgainst p N B k B (N * (k + .var j)) ⟨t, 0⟩
  let C ← alloc p (N * (k + ℓ))
  stmt (.apply o p C 0 B 0 (k + ℓ))
  ins (.lit p out 0)
  forRange k fun j => do
    dot p ⟨t, 0⟩ B (N * .var j) C (N * .var j) N
    ins (.bin p .add out out ⟨t, 0⟩)
  ins (.lit p ⟨t, 1⟩ 0)
  forRange ℓ fun j => do
    dot p ⟨t, 0⟩ B (N * (k + .var j)) C (N * (k + .var j)) N
    ins (.bin p .add ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩)
  ins (.litIdx p ⟨t, 0⟩ ℓ)
  ins (.bin p .div ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩)
  ins (.bin p .add out out ⟨t, 1⟩)
```

**Lanczos** (stage 1b for the proofs; three vectors rotate through slots `j mod 3`; breakdown by
an exact zero test, matching the library's junk value `0⁻¹ = 0` in `lanczosStep`):

```lean
/-- One Lanczos step from slot `cur` (previous vector in slot `prev`, `s[1] = β_j`) into slot
`nxt`; writes `α_j`, `β_{j+1}`. `s[3]` holds a literal zero. -/
def lanczosStepProg (p : P) (o : ι) (N : IExp VI) (W : VB) (cur prev nxt : IExp VI) (s : VB)
    (alphaCell betaCell : Cell VB VI) : Builder P ι VB VI Unit := do
  stmt (.apply o p W nxt W cur 1)
  ins (.un p .neg ⟨s, 0⟩ ⟨s, 1⟩)
  axpy p ⟨s, 0⟩ W prev W nxt N
  dot p ⟨s, 0⟩ W cur W nxt N
  ins (.un p .re ⟨s, 0⟩ ⟨s, 0⟩)
  ins (.copy p alphaCell ⟨s, 0⟩)
  ins (.un p .neg ⟨s, 0⟩ ⟨s, 0⟩)
  axpy p ⟨s, 0⟩ W cur W nxt N
  dot p ⟨s, 2⟩ W nxt W nxt N
  ins (.un p .sqrt ⟨s, 1⟩ ⟨s, 2⟩)
  ins (.copy p betaCell ⟨s, 1⟩)
  ifThenElse p .eq ⟨s, 2⟩ ⟨s, 3⟩ (pure ()) (rscl p ⟨s, 1⟩ W nxt N)

/-- Start: slot 0 holds `b / ‖b‖` (or `b = 0`), slot 2 holds zero, `β_0 = 0`. -/
def lanczosInit (p : P) (N : IExp VI) (b : VB) (W s : VB) : Builder P ι VB VI Unit := do
  ins (.lit p ⟨s, 3⟩ 0)
  forRange N fun i => ins (.lit p ⟨W, 2 * N + .var i⟩ 0)
  copyv p b 0 W 0 N
  dot p ⟨s, 2⟩ b 0 b 0 N
  ifThenElse p .eq ⟨s, 2⟩ ⟨s, 3⟩ (pure ()) do
    ins (.un p .sqrt ⟨s, 2⟩ ⟨s, 2⟩)
    rscl p ⟨s, 2⟩ W 0 N
  ins (.lit p ⟨s, 1⟩ 0)

/-- **Lanczos as a program**, `q` steps, three vectors rotating through slots `j mod 3`:
memory `3N + 4` besides the inputs `b` and the outputs `alpha`, `beta` (length `q`). -/
def lanczosProg (p : P) (o : ι) (N q : IExp VI) (b alpha beta : VB) : Builder P ι VB VI Unit := do
  let W ← alloc p (3 * N)
  let s ← alloc p 4
  lanczosInit p N b W s
  forRange q fun j =>
    lanczosStepProg p o N W (N * (.var j % 3)) (N * ((.var j + 2) % 3))
      (N * ((.var j + 1) % 3)) s ⟨alpha, .var j⟩ ⟨beta, .var j⟩

/-- The variant that also writes the basis into `Q` (`N × q`): memory `Nq` more, `Nq` copies. -/
def lanczosBasisProg (p : P) (o : ι) (N q : IExp VI) (b alpha beta Q : VB) :
    Builder P ι VB VI Unit := do
  let W ← alloc p (3 * N)
  let s ← alloc p 4
  lanczosInit p N b W s
  forRange q fun j => do
    copyv p W (N * (.var j % 3)) Q (N * .var j) N
    lanczosStepProg p o N W (N * (.var j % 3)) (N * ((.var j + 2) % 3))
      (N * ((.var j + 1) % 3)) s ⟨alpha, .var j⟩ ⟨beta, .var j⟩
```

**Realisations** (statements; the proofs are the skeleton's work). Superseded on 2026-10-23: results are now instances of the access models of section "Guarantees", and the statements below are private proof steps of the instances.

```lean
theorem runsWithin_hutchppProg (p : P) (o : ι) (d : Dist) {N k ℓ : ℕ} (hℓ : 0 < ℓ)
    (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ) :
    RunsWithin (exactInterp (fun _ => A) ξ)
      ((hutchppProg p o d (.const N) (.const k) (.const ℓ) ⟨0, .const 0⟩).run)
      (inputState p [Array.replicate 1 none]) (hutchppCount p o d N k ℓ)
      (fun q => if q = p then 2 * N * (k + ℓ) + 4 else 0)
      (fun st => st.store.read p 0 0 =
        some (hutchpp A (tapeMatrix (ξ d) 0 N k) (tapeMatrix (ξ d) (N * k) N ℓ))) := sorry
```

```lean
theorem runsWithin_lanczosProg (p : P) (o : ι) {N q : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (b : Fin N → 𝕜) :
    RunsWithin (exactInterp (fun _ => A) fun _ _ => 0)
      ((lanczosProg p o (.const N) (.const q) 0 1 2).run)
      (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
        Array.replicate q none]) (lanczosCount p o N q)
      (fun r => if r = p then 4 * N + 2 * q + 5 else 0)
      (fun st => (∀ j < q, st.store.read p 1 j =
          some (lanczosAlpha A (lanczosState A b j) : 𝕜)) ∧
        ∀ j < q, st.store.read p 2 j = some ((lanczosState A b (j + 1)).beta : 𝕜)) := sorry

theorem runsWithin_lanczosBasisProg (p : P) (o : ι) {N q : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (b : Fin N → 𝕜) :
    RunsWithin (exactInterp (fun _ => A) fun _ _ => 0)
      ((lanczosBasisProg p o (.const N) (.const q) 0 1 2 3).run)
      (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
        Array.replicate q none, Array.replicate (N * q) none])
      (lanczosCount p o N q + Finsupp.single (.copy p) (N * q))
      (fun r => if r = p then 4 * N + 2 * q + N * q + 5 else 0)
      (fun st => Holds st.store p 3 0 (lanczosMatrix A b q)) := sorry
```

The Lanczos realisations need neither a Hermitian nor a breakdown hypothesis: they are stated
against the library's total recursion `lanczosState`, and
`Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix` then gives the Krylov meaning. The sparse
Hutch++ corollary `runsWithin_substOracle_hutchppProg_cooImpl` (proved from the composition
theorem) states its representation: the COO pattern is unrolled into the implementation, the
values are read-only data, each matvec costs `nnz` mul, `nnz` add, `nnz` reads and `N` lits, and
memory is `2N(k + ℓ) + 5 + nnz`. The Gaussian tail for the program that draws its own test
matrices is `measureReal_not_runsWithin_hutchppProg_le_of_hasLaw_iidSequence`, proved from the
realisation, the tape laws and the existing
`measureReal_abs_trace_sub_hutchpp_ge_le_of_hasLaw_gaussianMatrix`.

## 6. Counts (verified by execution during the design)

Hutch++, `J = k(k − 1)/2`, full column rank of `AS` (each zero Gram–Schmidt column saves one
square root and `N` divisions):

| kind | count |
|---|---|
| loads, matvecs, draws | `2`, `2k + ℓ`, `N(k + ℓ)` |
| mul | `2NJ + 2Nk + 2Nkℓ + Nℓ` |
| add | `2NJ + 2Nk + 2Nkℓ + Nℓ + k + ℓ + 1` |
| div, sqrt | `Nk + 1`, `k` |
| conj, neg | `NJ + 2Nk + Nkℓ + Nℓ`, `J + kℓ` |
| lit, cmp | `J + 3k + kℓ + ℓ + 3`, `k` |
| flops | `2Nk² + 3Nk + 4Nkℓ + 2Nℓ + 2k + ℓ + 2` |
| peak memory | `2N(k + ℓ) + 4` cells |

Lanczos, `q` steps, no breakdown: loads and matvecs `q`; mul and add `4Nq + N` each; div `Nq + N`;
sqrt `q + 1`; conj `2Nq + N`; neg `2q`; re `q`; copy `2q + N`; lit `2q + N + 3`; cmp `q + 1`;
flops `9Nq + q + 3N + 1`; peak `4N + 2q + 5` (basis variant `+ Nq`, copies `+ Nq`).

Executed with the `Float` interpreter on a 5 × 5 symmetric `A`:

| run | result | flops | loads, matvecs | peak |
|---|---|---|---|---|
| Lanczos, `N = 5`, 4 steps, `b = 1` | α = (5, 1.4, 3.905556, 2.895728), β = (1.414214, 1.2, 0.980914, 1.086654) | 200 | 4, 4 | 33 |
| the same, keeping the basis | same | 200 | 4, 4 | 53 |
| Hutch++, `k = 2`, `ℓ = 1`, sign tape | 19.326978 | 127 | 2, 5 | 34 |
| Hutch++, `k = 5`, `ℓ = 1` | 15.000000 (`tr A`) | 448 | 2, 11 | 64 |

## 7. Reducing higher-level error models to bit operations, and later stages

### 7.1 The chain

1. **Contract.** A program over a tag `p` is analysed once against a contract (D19), quantified
   over every semantics meeting it: `∀ sem, IsRelErrSem u dec safe sem → RunsWithin {I with sem}
   prog … (error bound on decoded outputs)`. The analysis proves that every operation's inputs
   are in range, which yields success through the success clauses, and bounds the error through
   the error clauses. Exact arithmetic is one admissible semantics (`u = 0`, proved), so shared
   lemmas cover it.
2. **A specified format** on words (D16 (i)), for example `f64` with round to nearest, proved to
   meet the contract. Its partiality is the range condition.
3. **A word-level implementation** of each scalar instruction at `p`, certified once by
   `ImplementsInstr` against that format semantics: the same store whenever the format succeeds,
   the cost of its kind, bounded scratch.
4. **Refinement by substitution.** `RunsWithin.subst` gives the word-level program the store of
   the format-level run, hence its output and its error guarantee. Its counts are
   `substCountG cost c`, and a width weight turns them into bit operations.

**Why the transfer is sound.**
* `ImplementsInstr` demands the same store whenever the specification succeeds.
* Specification-level success at every executed operation is exactly what the contract theorem
  proves, through the success clauses.
* So every operation the substituted program executes is one where the implementation is
  certified to agree.
* An implementation that succeeds where the specification fails lies outside the theorem, and
  nothing is claimed for it.

### 7.2 What stage 1 supports

* Substitution of any scalar instruction or oracle call (D18, proved). It chains: the concrete
  read-only data extends the abstract data, so sparse Hutch++, already one substitution away from
  the oracle, can be substituted again down to words.
* Integer and bit operations, and `convert` (D18).
* Memory in bits (D17).
* The contract with success clauses (D19).
* Kept, not substituted: comparisons (the semantics must agree on them), read-only reads
  (identity cost), draws (equal tapes).

### 7.3 What stage 2 adds

* The format semantics on words (`f64`, `f32`, a parameterised `(p, emin, emax)`), the proof that
  it meets `IsRelErrSem` on range-safe inputs, and contract-level analyses of the BLAS kernels
  (floating `dot` and `axpy` bounds, proved once).
* Bit-level implementations of each floating operation, with `ImplementsInstr` certificates.
* **Comparison substitution.** Comparisons in `ite` and `whileFuel` are kept by the stage-1
  theorem (`hcmp`). A bit-level comparison computes a bit into a scratch cell and branches on it;
  stage 2 extends `Stmt.subst` with a comparison implementation and the simulation with the
  scratch cell.
* **Draw substitution** (Gaussian draws from uniform bits): the tape changes, so the simulation
  needs a coupling between tapes, not equal positions. This is a stochastic refinement, beyond
  this theorem.
* **Representation change** (one word into `w` separate bit cells, gate-level circuits): a data
  refinement with an encoding relation between stores, not the identity relation used here.
  Bit-operation counts do not need it: word operations weighted by width are the usual bit
  complexity.

### 7.4 The fixed-point example (run)

* Tags `fx` (Q16, value `w / 2^16`) and `int` over `ℤ`.
* `fxSem` (fixed-point `add`, `sub`, `neg`, and `mul` with the product shifted down), and
  `wordSem` (integer operations only).
* `fxImpl` (`add`, `sub`, `mul` and `neg` through reinterpretation and integer operations, with
  `shr 16` for `mul`; `conj` as a copy) and `fxCost`.
* Proved, 2026-10-27: `implementsInstr_fxImpl` and `fxSem_mul_abs_sub_le`, with their original
  signatures. The audit found that the old implementation kept fixed-point subtraction and
  negation even though `wordSem` rejects them. Both now have integer implementations, within
  the existing four-integer-cell/256-bit scratch bound, and their operation costs are counted.
  The error proof uses the nonnegative remainder of division by $2^{16}$, including negative
  products. A regression run checks subtraction, negation, negative-product rounding and an
  in-place destination; the original dot-product run and its counts are unchanged.

The run of `dot` at `fx` gives the same word (−0.6875 = −45056/2^16) at both levels: 9 fixed-point
operations versus 9 integer operations and 18 reinterpretations, peak 64 versus 320 bits.

**Caveat**: the `int` tag here is unbounded `ℤ`, with no overflow failure. So the bit cost 12,672
(64 per add and shift, 64² per multiply) is a weighted count, not a certified 64-bit count. A
certified one needs an `int64` semantics that fails or wraps outside its range (D16 (i)), and the
certificate's range side conditions.

### 7.5 Other later stages

Mixed precision (tags, `convert`), stochastic rounding (semantics reading the tape), and bit cost
of control (loop iterations and `IExp` are syntax) attach as described in D3 and D8.

## 8. Executable code (point 6)

A program is data with Lean binders, so an emitter is one more structural function: instantiate
`VB := String`, `VI := String`, let `alloc` and `loop` invent names, print `IExp` as Python
arithmetic. Emission is size-generic because loops, conditions and sizes are nodes of the
signature. The design's emitter (about 60 lines) prints NumPy in two modes: `named` kernels as
calls into a short NumPy prelude (`dot` as `np.vdot`, `axpy` as `y[...] += a * x[...]`, the
oracle as `A @ X.reshape(..., order='F')`), or inlined scalar loops. Fresh buffers are
`np.full(len, np.nan)`, so a read before write shows as NaN. The emitted Lanczos and Hutch++
(`def lanczos(A, N, q, b, alpha, beta)`, `def hutchpp(A, N, k, l, out)` with a `draw_rademacher`
hook) agreed with the Lean `Float` interpreter to six digits, and the reviewer ran them
size-generically at `N = 7`, `q = 5`, `k = 4`, `ℓ = 3`. The emitted code is an unverified
translation, for differential testing; Lean also runs programs directly with `Float`.

## 9. Lanczos

See D15 (stage 1b).

## 10. Rule checks (sketched as `MetaM` code during the design and run)

| id | rule | run during the design |
|---|---|---|
| E1 | A program (type ending in `Builder` or `Stmt`) is generic in its two variable sorts. No instance or hypothesis mentions them. Every argument is a type parameter, a tag or oracle name, a `Dist`, a handle, an index expression, a cell or a program; host data (`ℕ` sizes, `List`, functions) is rejected outside implementation files. | accepts `dot`, `axpy`, `orthAgainst`, `hutchppProg`, `lanczosStepProg`, `lanczosProg`, `lanczosBasisProg`; rejects `cooImpl` at `pattern` (an implementation, allowlisted by file), `forgeNat` (not generic), `forgeFun` at `f : VI → VB`, `hostSize` at `n : ℕ` |
| E2 | Programs, kernels and implementations are computable. | not re-run |
| E3 | In `RunsWithin I s st₀ c m Q`, no data variable of `I` (dimensions in `ℕ` excepted) occurs in `s` or in `st₀`. Replaced on 2026-10-23 by a lint: a public result about a program's runs is an instance of an access model (section "Guarantees"). | accepts `runsWithin_hutchppProg`, `runsWithin_lanczosProg`; rejects `runsWithin_cheat` (which puts `flatten A` in the initial store) at `A` |
| E4 | Every `<spec>Prog` has `runsWithin_<spec>Prog`; from 2026-10-23, a result in an access model. | not re-run |
| E5 | `NLAlib/Computation` imports only Mathlib and ForMathlib. | not re-run |
| E6 | Only `NLAlib/Computation` defines a `ScalarSem` or an `Interp`. | not re-run |
| E7 | Merged into E1 (host sizes). | |
| E8 | `Stmt.named` is constructed only in the BLAS and implementation files. | not re-run |

Not checked, and harmless for the information restriction: host-computed `ℚ` literals and
`.const n` sizes are uncounted host work.


## 11. Files and size

Amended 2026-10-23 at the skeleton (the files as they now are; the Hutch++ totals are in
`HutchPlusPlusProgram.lean`, since Computation is layer 0 and cannot import Estimation; see
"Changes during the skeleton"). Amended 2026-10-23 at the close of the proofs: the store moved
out of `Exec.lean` into its own file `Computation/Store.lean` (with the frame invariant), and the
level-2 and level-3 specifications of `BLAS.lean` into `Computation/BLAS/MatrixKernels.lean`, to
keep each file under about 1000 lines; the proved lengths are in "Changes during the proofs".

| file | contents | skeleton lines | estimate |
|---|---|---|---|
| `Computation/Syntax.lean` | `IExp`, `Cell`, `Instr` (integer and bit operations, `convert`), `Stmt`, `Builder` as `ContT` | 240 | 270 |
| `Computation/Store.lean` (split from `Exec.lean` at the close) | `Store` (read, write, blocks, shape), store lemmas, the frame invariant `Store.BlockFrame` | | |
| `Computation/Exec.lean` | `OpKind`, `ScalarSem`, `St`, `Interp`, `exec`, run lemmas (proved) | 460 | 650 |
| `Computation/RunsWithin.lean` | interface, transfer lemma | 70 | 150 |
| `Computation/Subst.lean` | substitution theorem, oracle corollary (proved) | 590 | 590 |
| `Computation/Exact.lean` | `exactSem`, `exactInterp`, layout, `Holds`, frame | 160 | 450 |
| `Computation/Contract.lean` | `IsRelErrSem`, exact instance, failing semantics (proved) | 160 | 200 |
| `Computation/Model.lean` (added for the guarantees) | `ProgFamily`, `storedInterp`, `MatrixFree`, `StoredEntries` | | |
| `Computation/BLAS.lean` | nine kernels, the level-1 specifications | 320 | 1,050 |
| `Computation/BLAS/MatrixKernels.lean` (split from `BLAS.lean` at the close) | the specifications of `gemv`, `ger`, `gemm` | | |
| `Computation/Dense.lean`, `Computation/Sparse.lean` | `denseImpl`, `cooImpl`, interpretations, costs, certificates | 170 | 400 |
| `ForMathlib/Data/Nat/Init.lean` | injectivity of flat indices (proved) | 45 | 45 |
| `Probability/Law.lean` (one lemma) | `HasLaw.comp_of_injective` (proved) | 10 | 10 |
| `RandomMatrix/Tape.lean` | the two tape laws | 60 | 200 |
| `Estimation/Trace/HutchPlusPlus.lean` (one lemma) | `hutchpp_reindex` (proved) | 25 | 80 |
| `Matrix/Factorizations/GramSchmidtProgram.lean` | `orthAgainst`, `gramSchmidtProg`, `gramSchmidtCount`, three specifications | 150 | 450 |
| `Estimation/Trace/HutchPlusPlusProgram.lean` | `hutchppProg`, `hutchppCount`, realisation, Gaussian tail, dense and sparse totals | 235 | 600 |
| **stage 1** | | **about 2,600** | **about 5,100** |
| stage 1b: Lanczos (`Krylov/Processes/LanczosProgram.lean`, `lanczosState_reindex`) | | not started | 770 |
| `NLAlibTools/` (`Float.lean`, `NumPy.lean`, `FixedPoint.lean`) | the `Float` runner, the emitter, the fixed-point example | 415 | 400 |
| checks: `scripts/Programs.lean` (E1 to E4), `scripts/check_rules.py` (E5, E6, E8), tests | | 330 | 300 |
| stage 2 (word formats and their contract proofs, `int64`-style semantics, comparison substitution, floating kernel bounds, word-level implementations; with D16 (ii) or (iii) also a data-refinement simulation, about 500) | | | estimate 3,000 to 3,500, its own note |

## 12. Material

* Quarry (`atlas/declarations.json`), searched for flop, matvec, cost, oracle, program, float and
  round: nothing relevant.
* CSLib (read 2026-10-22): `Cslib.FreeM` and its query interpreters (the free-monad option B),
  `Cslib/Algorithms/Lean/TimeM.lean` (annotation-based costs). Not a dependency.
* Mathlib, searched: no free monad and no imperative-program syntax; `WriterT`, `ContT`,
  `Finsupp.weight`, `Finsupp.liftAddHom`, the `Finsupp` order, `FinEnum`, `Mathlib.Data.Int.Bitwise`.
* Library: `hutchpp`, `hutchpp_eq_of_mul_conjTranspose_self_eq_rangeProjector`, the tails of
  `Estimation/Trace/HutchPlusPlusTail.lean`; `gramSchmidtQ`, `gramSchmidtQ_mul_conjTranspose`,
  `gramSchmidtR_apply_self_smul_col`, `mgsSweep_eq_sub_sum`; `Krylov/Processes/LanczosRecurrence.lean`;
  `Probability/Law.lean` (`iidSequence`); `RandomMatrix/Gaussian/Basic.lean`,
  `RandomMatrix/Rademacher/Basic.lean`.
* Citations: [MeyerMuscoMuscoWoodruff2021, Algorithm 1; Theorem 5], [GolubVanLoan2013, §5.2.8],
  [Paige1972, §2] and [Saad2011, §6.6] as `lanczosStep` cites them; [Higham2002] for the standard
  model (locator to check); Flocq, Cucker (arXiv:1403.6241) and Connolly, Higham and Mary to add
  with stage 2.
* Mathlib deviations: none. `Builder` is Mathlib's `ContT`, and no other object duplicates a
  Mathlib notion; `docs/design/Mathlib-deviations.md` is unchanged.


## Guarantees: what is proved and what is trusted (2026-10-23)

*Superseded after the migration of section "First-order programs and target statements" (F11),
whose F10 re-classifies every item below; until then this section describes the code.*

**A change approved by the maintainer on 2026-10-23**, in his words: "this stuff needs to be
watertight, because we will be allowing stuff to prove autonomously. The same general question for
stuff beyond oracles. Are we relying on checks or are we provably guaranteed about the costs. Make
this change."

**What was wrong.** Until this change, the information restriction (a realisation's program does
not see the matrix) was a script, the old E3 of `scripts/Programs.lean`, which inspected the
variables of each theorem concluding `RunsWithin`. It was a syntactic proxy with gaps: a tail
`μ.real {ω | ¬ RunsWithin (exactInterp (fun _ => A) (ξ ω)) prog …} ≤ δ` does not conclude
`RunsWithin` and was not examined; a tape law hypothesis could depend on $\mathbf{A}$
(`HasLaw ξ (iidSequence (leverageDist A)) μ`) and was not examined; a variable whose type is a type
parameter counted as non-data, and E1 admitted arguments of such types and instances not
mentioning the variable sorts, so a program taking `(M : Type) [Entries M] (x : M)` could turn
$\mathbf{A}$ into literals. Each gap is a fixture now (below).

**What replaces it.** Results are instances of access models (`NLAlib/Computation/Model.lean`,
`NLAlib/RandomMatrix/Tape.lean`), in the style of CSLib's query bounds
(`Cslib.Query.UpperBound prog size bound := ∀ oracle n x, size x ≤ n → … ≤ bound n`, where the
binder order makes the program independent of the oracle):

* `ProgFamily P ι r b := (VB VI : Type) → IExp VI → (Fin r → IExp VI) → (Fin b → VB) → Stmt P ι VB VI`:
  a program built from the oracle dimension, $r$ further sizes and the handles of $b$ declared
  buffers. It receives no data. `ProgFamily.inst prog N n` is the statement that runs.
* `MatrixFree p prog valid X inputs cost mem post`:
  `∀ N n, valid N n → ∀ (x : X N n) (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ),
  RunsWithin (exactInterp (fun _ => A) ξ) (prog.inst N n) (inputState p (List.ofFn (inputs N n x)))
  (cost N n) (mem N n) (post N n x A ξ)`.
* `MatrixFreeProb p prog valid X inputs cost mem good bound`: for the same data and every tape
  `ξ : Ω → Dist → ℕ → ℝ` with `HasLaw ξ tapeLaw μ`, the probability that the run fails to satisfy
  `RunsWithin … (good N n x A)` is at most `bound N n x A`. The law `tapeLaw` is fixed by the
  definition: the tapes of the distributions independent, the tape of `d` i.i.d. with law
  `Dist.law d` (`gaussianReal 0 1`, `rademacherMeasure`).
* `StoredEntries p prog valid X inputs len cost mem post`: the same with the data the entries
  `vals : ℕ → 𝕜` held as read-only data (`storedInterp (len N n) vals ξ p`: counted reads, `len`
  cells of counted constant memory, no oracle).

Instances (all proved): `matrixFree_gramSchmidtProg`, `matrixFree_hutchppProg`,
`matrixFreeProb_hutchppProg`, `storedEntries_substOracle_hutchppProg_denseImpl`,
`storedEntries_substOracle_hutchppProg_cooImpl`, and the model-level composition theorems
`MatrixFree.storedEntries_substOracle_denseImpl` and `MatrixFree.storedEntries_substOracle_cooImpl`.
The earlier realisations are private proof steps.

**The trusted base, once.** Every (P) below is proved by Lean relative to this base, and every (T)
names the part of it, or the script, that it rests on.

1. Lean's kernel, and the axioms `propext`, `Classical.choice`, `Quot.sound` (`scripts/Audit.lean`
   checks that nothing else, `sorryAx` included, is used; with `--wfail` a `sorry` fails the
   build).
2. The meaning of the definitions a result's statement unfolds to, read as written: the syntax
   (`Syntax.lean`), the store (`Store.read`, `Store.write`), the run `exec` with `Instr.run`,
   `Instr.kind` and `cmpStep`, the interpretations `exactSem`, `exactInterp`, `storedInterp`,
   `inputState`, `RunsWithin`, the three models, `Dist.law` and `tapeLaw`, and the Mathlib notions
   they use (`Matrix`, `Finsupp`, `Measure.infinitePi`, `HasLaw`, `gaussianReal`). These are about
   900 lines; a statement about a program means what they say.
3. The statement of each instance, read as written: its size condition `valid`, its declared
   inputs (`X`, `inputs`), its counts, memory and postcondition (or event and bound), and its
   other hypotheses. The model guarantees that the program meets exactly that statement for every
   datum, not that the statement is the interesting one (a false size condition or an empty type
   of declared inputs makes it vacuous, a weak postcondition gives an honest but weak result, and
   a postcondition may relate the declared inputs to the matrix; each is visible in it).

Certificates (`ImplementsInstr`, `ImplementsOracle`), kernel specifications and the proofs are not
in the base: a result's statement does not mention them, and the kernel checks the proofs.

**Key**: (P) proved by Lean, by definition, by the semantics or by a named theorem; (T) trusted,
naming what; (D) a documented modelling choice. For a (T): whether it can become (P) now, later or
never.

### Counts

| # | property | class | basis |
|---|---|---|---|
| G1 | Arithmetic (`bin`: add, sub, mul, div, and the word operations) is charged once per executed operation, at its kind `.bin p b` | P | `exec_instr` (an instruction adds `I.charge i.kind`), `Instr.kind`, the charge `Finsupp.single k 1` of `exactInterp` and `storedInterp`; trusting base item 2 (the 7-line `Instr.kind`) |
| G2 | Unary operations (`neg`, `conj`, `re`, `sqrt`, `bnot`), at `.un p u` | P | as G1 |
| G3 | Comparisons, at `.cmp p`, once per `ite` and once per test of `whileFuel` (the final failing test included) | P | `cmpStep`, `exec`; `snd_of_cmpStep_eq_some` |
| G4 | Literals, at `.lit p`; an index literal `litIdx` is charged as a literal | P, D | `Instr.kind`; charging `litIdx` as a literal is the modelling choice |
| G5 | Conversions, at `.convert p q`; copies at `.copy p` | P | as G1 |
| G6 | Read-only reads, at `.rom p`, one per read | P | `exec` |
| G7 | Oracle calls: one `.load p o` and `cols` counts of `.matvec p o` per call, whatever the dimension | P, D | `exec`, `exec_apply_exactInterp`; the oracle's own cost is abstract (D4) |
| G8 | Draws, at `.draw p d`, one per drawn value | P | `exec_seq_instr_draw`, `exec_forRange_draw` |
| G9 | Every write and every draw is charged: with every charge nonzero, a run whose counts do not grow leaves the store and the tape positions unchanged | P (new) | `store_eq_of_exec_eq_some_of_cnt_le`, `pos_eq_of_exec_eq_some_of_cnt_le` |
| G10 | Counts only grow, and the counts of a sequence are those of its parts in turn | P (new) | `cnt_le_of_exec_eq_some`, `exec_seq`; `RunsWithin` bounds the growth from the initial counts, which are $0$ (`inputState`) |
| G11 | Not counted: index arithmetic (`IExp`), loop iterations, `skip`, `seq`, `named`, the allocation itself (its memory is counted, G13). A loop with an empty body runs uncounted | D | §7.5 (control cost is a later stage, with a control kind) |
| G12 | A result is an upper bound per kind (`OpCount` ordered pointwise); weighted totals are `Finsupp.weight` | D | D5 |

### Memory

| # | property | class | basis |
|---|---|---|---|
| G13 | Current memory is the live allocations: an allocation raises the current memory of its tag by its length and frees it at the end of its body, and a run ends with the current memory (cells and bits) and the shape of the store (tag and length of every buffer) of its start, so it frees exactly what it allocates | P (new) | `exec_alloc`; `cur_eq_of_exec_eq_some`, `curW_eq_of_exec_eq_some`, `shape_eq_of_exec_eq_some` |
| G14 | The peak is raised at each allocation to cover the current memory plus the new buffer, and only grows | P (new) | `exec_alloc`; `peak_le_of_exec_eq_some`, `peakW_le_of_exec_eq_some` |
| G15 | The declared buffers count from the start, and the initial state is built by the model, not chosen by the theorem: current and peak memory are their total length, counts $0$, tape positions $0$ | P | `inputState`; the models build `inputState p (List.ofFn (inputs N n x))` |
| G16 | The memory bound is per tag on peak plus read-only data (`peak p + romSize p ≤ m p`); `storedInterp` counts its `len` entries | P | `RunsWithin`, `storedInterp` |
| G17 | Units: cells per tag; bits are tracked (`curW`, `peakW`) but `RunsWithin` bounds cells only, and the exact and stored interpretations have width $0$ | D | D17 |
| G18 | Not counted: the oracle's matrix (an oracle), and the index storage of a COO pattern (public, unrolled into the program) | D | D14 |
| G19 | Scoping: an `alloc` is live for its body, so an open `alloc` in a callee stays live, and counted, for the rest of the caller's block (E9 keeps it intended, not correct) | P, D | `exec_alloc`; D11 |
| G20 | No use after free and no unaccounted buffer: every access goes through `Store.read`/`Store.write`, which fail past the stack; a handle forged at `VB := ℕ` reaches only live, counted buffers | P | `Store.read`, `Store.write`, `Store.read_eq_none_of_size_le` |

### Success and failure

| # | property | class | basis |
|---|---|---|---|
| G21 | Division by zero, the square root of a number not nonnegative, the word operations and `bnot` fail at the exact level | P | `exactSem` |
| G22 | An invalid oracle query (wrong block length) fails; under `storedInterp` every oracle call fails | P | `matOracle`, `storedInterp` |
| G23 | An aliased oracle call (overlapping source and destination blocks) fails | P | `exec` |
| G24 | Reading an uninitialised cell fails (fresh buffers are `none`), and so do out-of-bounds access and a tag mismatch | P | `Store.read`, `Store.write`, `exec_alloc` |
| G25 | Running out of fuel in `whileFuel` fails | P | `exec` |
| G26 | A result proves success: `RunsWithin` asserts the run is `some`, so every instance proves that none of G21 to G25 happens | P | `RunsWithin` |

### Information restriction and host computation

| # | property | class | basis |
|---|---|---|---|
| G27 | The program does not depend on the matrix, the tape or the declared inputs: the models bind the program before them, and the family receives only sizes and handles | P (new) | `MatrixFree`, `MatrixFreeProb`, `StoredEntries` (binder order), checked by the kernel; the old gaps are false as instances (`not_matrixFree_leakProg`, `not_matrixFree_copyProg`, `not_matrixFree_drawProg`) |
| G28 | The counts and the memory are functions of the sizes only | P (new) | the models apply `cost` and `mem` to `N n` |
| G29 | During the run the matrix reaches the program only through oracle calls: a run that makes no oracle call is the same for every matrix | P (new) | `exactInterp` (only its oracle field depends on $\mathbf{A}$); `exec_eq_of_exec_eq_some_of_cnt_load_le`, `exec_exactInterp_eq_of_exec_eq_some_of_cnt_load_le` |
| G30 | The stored entries reach the program only through counted read-only reads | P | `storedInterp`, `exec` (only `.rom` reads `I.rom`); a theorem as for G29 is cheap, later |
| G31 | Type parameters (tags `P`, oracle names `ι`, the field, the input types `X`) cannot carry the data: they are fixed before it. The gap-3 program (`leakProg`, a value of a type parameter read by a class) is accepted by E1 and harmless | P | binder order; `not_matrixFree_leakProg` |
| G32 | Every oracle name means the one matrix $\mathbf{A}$; an adjoint oracle needs a model with a second matrix derived from $\mathbf{A}$ | D | later |
| G33 | No host computation on data: no Lean term in the program can mention the data, which are bound after it; the run `exec` is the only computation on data, and it is counted (G1 to G10) | P | G27, G9 |
| G34 | Host computation on sizes and literals is uncounted. It can: compute any rational literal and any index expression from the sizes, unroll loops, choose a different program for each size (the model is non-uniform, like a circuit family), and inspect the size expressions. It cannot: depend on the data (G27); write an irrational or data-dependent literal (literals are `ℚ` constants of the syntax); address memory by a data value (no construct turns a cell into an index: `IExp` has variables, constants and arithmetic only); or avoid the charge of any executed instruction (G9). The cost of building the program is not bounded | D | `Instr.lit`, `IExp`; E1 keeps programs uniform (hygiene) |
| G35 | Uniformity in the variable sorts (a program cannot forge a handle or compute one from an index) holds by parametricity, a meta-argument that Lean's logic does not prove (with `Classical.choice` a term can case on a type). The guarantees do not use it (G20) | T: parametricity, with E1 and E2 as its checks | never in Lean; not needed |

### Randomness

| # | property | class | basis |
|---|---|---|---|
| G36 | The program reads the tape only by draws, each at the current position of its distribution, which then advances | P | `Instr.run`, `exec_seq_instr_draw`; G9 |
| G37 | Deterministic results hold for every tape | P | `MatrixFree`, `StoredEntries` |
| G38 | Probabilistic results have the law `tapeLaw`, fixed by the definition, never a hypothesis supplied per theorem; it cannot depend on the matrix | P (new) | `MatrixFreeProb` (`matrixFreeProb_iff`); `not_matrixFreeProb_drawProg` |
| G39 | `Dist.law` is the intended law of each distribution: `gaussianReal 0 1` and `rademacherMeasure` | T: these two definitions | never (they are the meaning) |
| G40 | A tail bound for the specification transfers to the program, with no new probability; the Hutch++ tail is proved from the tape laws | P | `measureReal_not_runsWithin_le`, `hasLaw_tapeMatrix_of_hasLaw_iidSequence`, `indepFun_tapeMatrix_of_hasLaw_iidSequence`, `hasLaw_apply_of_hasLaw_tapeLaw`, `matrixFreeProb_hutchppProg` |
| G41 | A tail is on `μ.real` of a set that need not be measurable, that is on its outer measure, which bounds every measurable subset | P | Mathlib's `Measure.real` |
| G42 | Draws of other laws from bits (draw substitution) are not available; the tape is real-valued and cast into the field | D | §7.3 |

### Termination, composition, realisations

| # | property | class | basis |
|---|---|---|---|
| G43 | Every run terminates: `exec` is a total function by structural recursion, `whileFuel` is bounded by its fuel | P | `exec` (accepted by the kernel) |
| G44 | Substitution of instructions and oracle calls by certified implementations | P | `RunsWithin.subst`, `RunsWithin.substOracle` |
| G45 | Composition at the level of the models: a matrix-free result gives the dense and the sparse stored-entries results | P (new) | `MatrixFree.storedEntries_substOracle_denseImpl`, `MatrixFree.storedEntries_substOracle_cooImpl`, from `implementsOracle_denseImpl`, `implementsOracle_cooImpl` |
| G46 | Comparisons and draws are kept by substitution, read-only reads cost themselves | D | D18, §7.3 |
| G47 | The realisations meet their specifications: Gram–Schmidt computes `gramSchmidtQ`, Hutch++ computes `hutchpp`, with their counts, memory and tail | P | the instances listed above |
| G48 | The specifications mean the algorithms of the citations: `gramSchmidtQ`, `hutchpp` and their library theorems | T: those definitions, as every library statement | never; read with their theorems |
| G49 | The counts of Gram–Schmidt and Hutch++ are upper bounds, exact for full column rank | D | D5, D6 |

### Tools and scripts

| # | property | class | basis |
|---|---|---|---|
| G50 | NumPy emission (`NLAlibTools/NumPy.lean`) is an unverified translation, outside the guarantee | T: the emitter and NumPy | never (Python is not modelled); differential tests only |
| G51 | `Float` runs (`NLAlibTools/Float.lean`) are outside the guarantee | T: the interpreter and `Float` | later, relative to a format semantics (stage 2) |
| G52 | Every public result about a program's runs is an instance of a model, so a reader need not check binder order or laws: the lint E3 | T: script code (`isAboutRuns`, `isInstanceType` in `scripts/Programs.lean`) | never (a statement about the set of theorems); its failure is visible, a non-instance statement |
| G53 | No `sorry` and no extra axiom | T: `scripts/Audit.lean` and `--wfail` | never (meta); standard |
| G54 | Every `<spec>Prog` has a result in a model (E4) | T: script | never; completeness, not soundness |
| G55 | Hygiene with no guarantee resting on it: E1 (size-generic programs, so the emitted code is the program the result is about), E2 (programs run in the tools), E5 (layering), E6 (one home for interpretations; no longer load-bearing, since the models fix theirs), E8 (`named` matters only to the emitter), E9 (scope discipline: G19) | D | rules.toml |

**Count.** 55 properties: 37 (P) (of which G4, G7 and G19 are partly (D)), 8 (T) (G35, G39, G48,
G50 to G54), 10 (D) (G11, G12, G17, G18, G32, G34, G42, G46, G49, G55). The (T) items and their
future:

* G35, parametricity: never provable in Lean, and no longer needed.
* G39, `Dist.law`, and G48, the specifications: the meaning of definitions; never.
* G50, NumPy: never. G51, `Float`: later, against a stage-2 format semantics.
* G52, the lint, G53, the audit, G54, E4: meta-level scripts; never, and each fails visibly.

And base item 2, the semantics, is (T) by nature. This change made the following (P) where they
had rested on reading `exec` alone: G9, G10, G13, G14 (the invariants of the run,
`Exec.lean`), G29 (the oracle is the only access), and G27, G28, G38 (by definition). Cheap, later:
the analogue of G29 for the tape and the read-only data; a second, small-step semantics with an
equivalence theorem, as an independent cross-check of `exec`.

**What each script still contributes.** The guarantees G1 to G47 rest on no script. E3 is the
one check left that a reader relies on, for coverage: that every public result about runs is an
instance (G52). E4 (G54) is completeness. E1, E2, E5, E6, E8 and E9 are hygiene (G55). E1 was kept
as an error and not demoted to a warning: it keeps programs size-generic, which the emitter needs,
and it no longer guards information (`leakProg` passes it, harmlessly).


## Changes during the skeleton (2026-10-23)

The skeleton is on `computation/stage1` (worktree `nlalib-block`, from `d5c207b`). Every
declaration of §§2–5 for stage 1 is stated with its final docstring and elaborates; the core
(syntax, run, substitution, contracts) is proved, and the `sorry` statements sit in their final
files in `NLAlib/` (as in the other rounds' skeletons, not in `NLAlibScaffold`). Changes against
the note:

* **Three changes to approved vocabulary** (the maintainer has been told of each; the reasons
  are in the bullets below):
  * **D2.** `exec` also fails on an aliased oracle call, one whose source and destination blocks
    overlap. D2's list of failing operations gains this item.
  * **D4.** The kinds of an oracle call carry the tag of the call: `OpKind.load p o` and
    `OpKind.matvec p o`, where D4 said `load o` and `matvec o`.
  * **D11.** An `alloc` in a `Builder` is freed at the end of the enclosing block, not at the end
    of the program that allocates. A program called inside another program's `do` block must
    wrap its allocations in `scope` (a kernel is closed by its `named` node); otherwise its
    buffers stay live for the rest of the caller's block. This is checked: rule E9
    (`scripts/Programs.lean`, added at the skeleton review) runs each program that another
    program calls against a fresh continuation and rejects it when the continuation is reached
    under an `alloc`. `gramSchmidtProg` passes; `hutchppProg`, which no program calls, would be
    rejected if one did.
* **Two forced changes to the certificates.** As approved, `implementsOracle_cooImpl` is false in
  two cases, and each needed a change of the model:
  * *Aliased calls.* `ImplementsOracle` quantified over calls whose source and destination blocks
    overlap; the abstract oracle reads the whole block before writing, while an implementation with
    bounded scratch (`cooImpl`, `denseImpl`) overwrites its source. Now `exec` fails on an aliased
    oracle call (D2's list of failures gains it), and `ImplementsOracle` assumes the blocks are
    disjoint (`dst ≠ src` or the two intervals of `height · cols` cells are disjoint).
    `exec_subst_sim` passes the fact on from the abstract run; the substitution theorems keep
    their statements. Every program of the note calls with disjoint blocks.
  * *Tags of oracle calls.* The cost of a matrix-vector product was a count at the data tag `p₀`,
    but the implementation computes at the tag of the call, so the certificate failed for a call
    at another tag. The kinds `load` and `matvec` now carry the tag of the call
    (`.load p o`, `.matvec p o`, as `draw p d` does); `cooCost N nnz` and `denseCost N` charge
    each product at its own tag, and `cooCost` loses its `p₀`. `hutchppCount` counts
    `.load p o` and `.matvec p o`.
* **`Builder` is Mathlib's `ContT (Stmt P ι VB VI) Id`** (an `abbrev`), with the combinators
  built by `ContT.mk` and `ContT.run`; the `do` blocks of every program elaborate unchanged. One
  consequence, found by the `Float` run: an `alloc` scopes over the rest of the enclosing block,
  so a program that allocates and is called inside another program's `do` block must close its
  scope. `gramSchmidtProg` is wrapped in `scope` (the run's peak went from 36 back to the table's
  34); kernels are closed by their `named` node.
* **Gram–Schmidt extracted.** `gramSchmidtProg p N k Y` (in place, two scratch cells of its own)
  is the loop of the note's `hutchppProg`; `hutchppProg` calls it and allocates its own two cells
  after it. `orthAgainst` lost its `named` node (E8 allows `named` only in the BLAS and
  implementation files), so the emitter inlines it as a loop of `dot` and `axpy` calls and the
  prelude has no `orth`. The counts and peaks are unchanged: the `Float` run gives 127 flops, 2
  loads, 5 matvecs, peak 34 at $k = 2$, and 448, 2, 11, 64 at $k = 5$, as in §6. Added for the
  Hutch++ proof: `gramSchmidtCount` (the full-rank counts, an upper bound), `exec_orthAgainst`
  (the sweep computes `mgsSweep`; a frame-style specification, since the coefficient cell is
  overwritten), `exec_gramSchmidtProg` (from any state, the store with `flatten (gramSchmidtQ M)`
  written), and `runsWithin_gramSchmidtProg` under `exactInterp (fun _ => 0) (fun _ _ => 0)` with
  memory $Nk + 3$.
* **Kernel specifications.** All nine have the six parts of D17: `exec_dot` and `exec_axpy` gain
  `st'.curW = st.curW` and the bit peak. `ger` is added. `exec_rscl` assumes $a \ne 0$ (exact
  division by zero fails). The level-2 and level-3 kernels take their operands as matrices with
  `Holds` and write `Array.ofFn (M *ᵥ x)` or `flatten`, with disjointness as intervals. `exec_gemm`
  bounds the peaks (no allocation when $l = 0$); the others state them exactly. `exec_nrm2`
  writes `((√(re ∑ conj xᵢ xᵢ) : ℝ) : 𝕜)`.
* **Dense implementation**: `denseImpl` (generic in its sizes, no host data), `denseInterp`
  ($\mathbf{A}$ as read-only data, $N^2$ cells), `denseCost`, `implementsOracle_denseImpl`, and
  the dense total `runsWithin_substOracle_hutchppProg_denseImpl` next to the sparse one, both in
  `HutchPlusPlusProgram.lean`.
* **Store, run and layout lemmas** added: `Store.shape`, `Store.read_of_write_eq_some`,
  `Store.read_of_write_eq_some_of_ne`, `Store.size_of_write_eq_some`, `Store.shape_of_write_eq_some`,
  `Store.exists_write_eq_some_of_read_eq_some`, `Store.read_push_of_lt`,
  `Store.read_of_writeBlock_eq_some_of_lt`, `Store.read_of_writeBlock_eq_some_of_ne`; `exec_seq`, `exec_loop`,
  `exec_named`, `exec_alloc`, `exec_ite`, `exec_instr`; `size_flatten`, `getElem?_flatten`,
  `unflatten_flatten`, all proved, as is `Holds.write`.
* **Column arithmetic.** Batteries' `Nat.add_mul_lt_mul_of_lt_of_lt` is the block bound;
  injectivity of $i + Nj$ for $i < N$ is the new `Nat.add_mul_eq_add_mul_iff_of_lt`
  (`ForMathlib/Data/Nat/Init.lean`, proved); disjoint columns follow from it.
* **The reindexing lemma for `iidSequence`** is `ProbabilityTheory.HasLaw.comp_of_injective` in
  `Probability/Law.lean` (proved, from `hasLaw_infinitePi_iff` and `iIndepFun.precomp`).
  `hutchpp_reindex` is proved (from `mul_pinv` and `pinv_submatrix_equiv`).
* **Names.** `BinOp.real` is `BinOp.realOp`: a definition named `real` makes `real` a library
  token for the naming check (N4) and breaks 21 existing names such as `specNorm_real_smul`. The
  store lemmas follow the grammar (`Store.read_of_write_eq_some`, not `read_write_self`).
  `IExp.eval` keeps its name; the one existing name it trips, `map_eval_uniformOn_injective`
  (Mathlib's `eval` for `fun f => f j`), is allowlisted for N4 with that reason.
* **Namespaces.** The Computation layer is `NLAlib.Computation`; programs and their theorems in
  topic files are in `NLAlib` (`NLAlib.hutchppProg`, `NLAlib.runsWithin_gramSchmidtProg`).
* **Result ids** (new): `computation-substitution`, `computation-oracle-substitution`,
  `computation-tail-transfer`, `computation-exact-meets-contract`,
  `computation-failing-semantics`, `coo-oracle-certificate`, `dense-oracle-certificate`,
  `tape-gaussian-matrix`, `tape-independent-draws`, `gram-schmidt-program`, `hutchpp-program`,
  `hutchpp-program-tail`, `hutchpp-program-dense`, `hutchpp-program-sparse`.
* **Checks.** E1 to E4 and E9 are `scripts/Programs.lean` (MetaM, `check = "lean"` in
  `docs/rules/rules.toml`), run on the built library with fixtures that must be rejected; E5, E6
  and E8 are in `scripts/check_rules.py` with fixtures in `scripts/test_check_rules.py`. E7 has no
  entry (merged into E1). The new area is "programs", letter E; CONTRIBUTING gains §5.5, the
  `Computation/` row of §2 and the §5.3 rows of §3. E3 ignores variables whose type is a type
  parameter (tags, oracle names) or `Dist`, as E1 allows them; its allowlist has one entry, the
  COO pattern in the sparse total (unrolled into the implementation by D14). E1's implementation
  files are `Computation/Dense.lean` and `Computation/Sparse.lean`. At the skeleton review: E3
  also rejects a data variable of the oracle or read-only fields in the tape field (fixture
  `runsWithin_cheatTape`, $\mathbf{A}$ read from the tape); E2 also rejects opaque (`partial`,
  `opaque`), `unsafe` and `implemented_by` constants of program type, which now count as programs
  for E1, E2 and E4 (fixture `partialProg`); E9 is new (fixtures `leakyCallee`, `closedCallee`);
  E6 says "in the library (NLAlib)", since the tools define `floatSem`, `fxSem` and
  `floatInterp`; `scripts/stage_check.sh` runs `scripts/Programs.lean`.
* **Tools.** `NLAlibTools` is a separate `lean_lib` of plain (non-`module`) files: the module
  system withholds the compiled code `#eval` needs from a module that does not `meta import` it.
  `Float.lean` runs Hutch++ and checks the §6 rows with `#guard`; `NumPy.lean` prints Hutch++,
  and the emitted code reproduces 19.326978 and 15.000000 under NumPy; `FixedPoint.lean` runs the
  §7.4 example (`#guard`: the same word, 9 against 0 + 9 + 18 operations, 64 against 320 bits)
  and states `implementsInstr_fxImpl` and `fxSem_mul_abs_sub_le` with `sorry`.
* **Lanczos** is stage 1b: no Lanczos file yet, and the tools run Hutch++ only.
* **Mathlib deviations**: none.

## Changes during the proofs

* 2026-10-23 (added during the proofs, in the commits proving BLAS, GramSchmidtProgram and
  HutchPlusPlusProgram): public helpers in `Computation/Exec.lean`, used by `BLAS.lean` and
  `GramSchmidtProgram.lean`: the `IExp.eval_*` simp lemmas; the store lemmas
  `Store.lt_size_of_read_eq_some`, `Store.lt_size_of_write_eq_some`,
  `Store.exists_write_eq_some_of_write_eq_some`, `Store.write_of_write_eq_some`,
  `Store.write_push_of_lt`, `Store.write_push_size`, `Store.read_push_size`,
  `Store.read_push_of_ne`, `Store.read_pop_of_lt`, `Store.read_eq_none_of_size_le`,
  `Store.size_of_foldlM_write_eq_some`, `Store.read_of_foldlM_write_eq_some_of_forall_ne`,
  `Store.writeBlock_map_range`, `Store.exists_write_eq_some_of_shape_eq`,
  `Store.shape_of_writeBlock_eq_some`, `Store.exists_writeBlock_eq_some`,
  `Store.exists_writeBlock_eq_some_of_write` (also used by `HutchPlusPlusProgram.lean`),
  `Store.read_of_write_eq_some_of_ne_tag`, `Store.size_eq_of_shape_eq`, `Store.ext_of_shape_eq`;
  the run lemmas `exec_skip`, `exec_seq_skip`, `exec_run_bind`,
  `exists_exec_loop_eq_some_of_forall` and `exec_seq_instr_lit`, `_litIdx`, `_bin`, `_un`,
  `_copy`, `_draw`. The private copies of `read_pop_of_lt` and `read_eq_none_of_size_le` in
  `Dense.lean`, `Sparse.lean` and `BLAS.lean` duplicate the public ones (S5); they are deleted at
  the close (below).
* 2026-10-23 (closing step): the shared helpers are one public copy each (rule S5), and the
  generic run lemmas of the Hutch++ proof are public in their homes. Every addition is in
  `NLAlib/Computation` or a stage file; each home is the file of its subject.
  * **New file `Computation/Store.lean`.** `Store` and every store lemma above moved there from
    `Exec.lean`, names unchanged (`Exec.lean` would otherwise have passed 1000 lines); `Exec.lean`
    imports it. New public store lemmas, replacing the private copies of `Dense.lean`,
    `Sparse.lean`, `BLAS.lean` and `GramSchmidtProgram.lean`: `Store.getElem?_shape`,
    `Store.size_shape`, `Store.shape_pop`, `Store.getElem?_shape_push_of_lt`,
    `Store.getElem?_shape_push_size`, `Store.exists_write_eq_some_of_getElem?_shape`,
    `Store.exists_getElem?_shape_of_read_eq_some`, `Store.read_eq_none_of_getElem?_shape_of_ne`,
    `Store.size_of_readBlock_eq_some`, `Store.read_of_readBlock_eq_some_of_lt`,
    `Store.lt_size_of_readBlock_eq_some`, `Store.exists_getElem?_shape_of_writeBlock_eq_some`,
    `Store.lt_size_of_writeBlock_eq_some`, `Store.exists_writeBlock_eq_some_of_getElem?_shape`,
    and `Store.readBlock_eq_some_map_range` (from `HutchPlusPlusProgram.lean`).
  * **The frame invariant** of `Dense.lean`, `Sparse.lean` and `BLAS.lean` (three private copies
    of `DInv`) is the public `Store.BlockFrame s₀ p T dst dOff L s g` in `Store.lean`: a run that
    writes one block through a scratch buffer keeps it along its loops. Its API:
    `Store.BlockFrame.write_of_lt`, `.write_scratch` (any scratch cell, the `BLAS.lean` form),
    `.exists_write_eq_some`, `.read_of_ne`, `.writeBlock`, `.push` and `.pop_eq` (popping the
    scratch buffer gives the block write).
  * **Run lemmas.** `Exec.lean`: `exec_seq_of_exec_eq_some` (the private `exec_seq_of_eq_some` of
    `Dense.lean` and `Sparse.lean`) and `exec_forRange_draw` (the private `exec_draws` of
    `HutchPlusPlusProgram.lean`; it now asks that each cell can be written with some value, not
    with $0$, so it holds over any carrier). `Exact.lean`: `exec_apply_exactInterp` (an oracle call
    under exact arithmetic, from the same file). `BLAS.lean`: `exec_forRange_dot_add` (its
    `exec_trace_loop`, a loop of `dot` calls accumulated into one cell) and `run_gemv`, `run_ger`,
    `run_gemm` (the private `gemv_run`, `ger_run`, `gemm_run`, public because the split below
    needs them). `GramSchmidtProgram.lean`: `exec_forRange_orthAgainst` (its `exec_proj_loop`, a
    loop of `orthAgainst` sweeps against the same columns).
  * **Deleted private copies**, used through the public lemmas: the store lemmas and `DInv` of
    `Dense.lean`, `Sparse.lean` and `BLAS.lean` (`shape_getElem?`, `read_of_write_of_ne_tag`,
    `exists_write_of_shape`, `shape_of_read_eq_some`, `read_eq_none_of_shape`,
    `Store.ext_of_shape`, `shape_of_foldlM_write`, `shape_of_writeBlock`, `read_of_readBlock`,
    `read_eq_none_of_size_le`, `read_pop_of_lt`, `shape_pop`, `size_shape`, `shape_push_size`,
    `shape_push_of_lt`, `lt_size_of_read`, `exists_writeBlock_of_shape`, `callFacts`,
    `mapM_eq_some`, `pop_eq_of_DInv` and the `DInv` lemmas); `exec_seq_skip` of `Dense.lean` and
    `Sparse.lean` (the public `exec_seq_skip`); `foldlM_range_inv` of the same two files (its uses
    are `exists_exec_loop_eq_some_of_forall`); `read_eq_none_of_ne_tag` and
    `exists_shape_getElem?_of_read_eq_some` of `GramSchmidtProgram.lean`. Private helpers left,
    each in one file: `blockFacts` (`BLAS/MatrixKernels.lean`), two `List.mapM` facts
    (`Store.lean`) and `update_max_le_of_le` (`BLAS.lean`), general facts used once.
  * **Split.** The level-2 and level-3 specifications `exec_gemv`, `exec_ger`, `exec_gemm`, with
    their private steps, moved to the new `Computation/BLAS/MatrixKernels.lean` (names
    unchanged), which imports `BLAS.lean`; the kernels themselves and their unfoldings stay in
    `BLAS.lean`, so the new file constructs no `named` node (E8).
  * **Checks.** `IExp.eval_ofNat` loses its unused `[n.AtLeastTwo]` (the environment linter;
    every numeral of `IExp` is a constant), and `IExp.eval_zero`, `IExp.eval_one` are no longer
    `simp` (they are cases of it). `Store.getElem?_shape` needed an N2 allowlist entry until the checker learned to read `x[i]?` as `getElem?`; the entry is gone. `Store.BlockFrame` has no §5.3 row (one V7 warning): it is API of the store, not vocabulary of
    statements, and a row is the maintainer's call.
  * **Lengths after the close** (before it in brackets): `Store.lean` 775 (new), `Exec.lean` 455
    (820), `Exact.lean` 194 (158), `BLAS.lean` 730 (1492), `BLAS/MatrixKernels.lean` 653 (new),
    `Dense.lean` 401 (695), `Sparse.lean` 448 (744), `GramSchmidtProgram.lean` 891 (839),
    `HutchPlusPlusProgram.lean` 976 (1270). Net, the library loses about 450 lines.

## Changes for the guarantees (2026-10-23)

The change of section "Guarantees", approved by the maintainer the same day, on
`computation/stage1`:

* **New file `Computation/Model.lean`** (layer 0): `ProgFamily`, `ProgFamily.inst`,
  `ProgFamily.substOracle`, `storedInterp`, `MatrixFree`, `StoredEntries`, and
  `exec_exactInterp_eq_of_exec_eq_some_of_cnt_load_le`.
* **`RandomMatrix/Tape.lean`**: `Computation.Dist.law`, `Computation.tapeLaw` (with its probability
  instance), `Computation.hasLaw_apply_of_hasLaw_tapeLaw` and `Computation.MatrixFreeProb`. It
  lives with the tape laws, since `Dist.law` needs the Rademacher law of the Probability layer.
* **The invariants of the run** (`Exec.lean`, section "Invariants of the run"):
  `Instr.shape_of_run_eq_some`, `snd_of_cmpStep_eq_some`, `cnt_le_of_exec_eq_some`,
  `cur_eq_of_exec_eq_some`, `curW_eq_of_exec_eq_some`, `shape_eq_of_exec_eq_some`,
  `peak_le_of_exec_eq_some`, `peakW_le_of_exec_eq_some`, `store_eq_of_exec_eq_some_of_cnt_le`,
  `pos_eq_of_exec_eq_some_of_cnt_le`, `exec_eq_of_exec_eq_some_of_cnt_load_le`.
  `RunsWithin.mono` (`RunsWithin.lean`).
* **Interpretations of the implementations.** `denseInterp A ξ p₀` is now
  `storedInterp (N * N) (fun e => (flatten A).getD e 0) ξ p₀`, and `cooInterp pattern vals ξ p₀`
  is `storedInterp pattern.length vals ξ p₀` (its unused `N` argument is gone): both have no
  oracle, where they had the exact oracle of the matrix, which the substituted program never
  calls. The certificates keep their statements. New: `MatrixFree.storedEntries_substOracle_denseImpl`
  and `MatrixFree.storedEntries_substOracle_cooImpl`, the composition at the level of the models.
* **Instances and renames.** `runsWithin_gramSchmidtProg` (now for every oracle and tape) and
  `runsWithin_hutchppProg` are private; the results are `matrixFree_gramSchmidtProg` and
  `matrixFree_hutchppProg`. `measureReal_not_runsWithin_hutchppProg_le_of_hasLaw_iidSequence` is
  private; the result is `matrixFreeProb_hutchppProg`, whose tape has the law `tapeLaw` (the old
  statement assumed a law on the Gaussian tape only). `runsWithin_substOracle_hutchppProg_denseImpl`
  and `runsWithin_substOracle_hutchppProg_cooImpl` are replaced by
  `storedEntries_substOracle_hutchppProg_denseImpl` and
  `storedEntries_substOracle_hutchppProg_cooImpl`, proved from the composition theorems; the
  sparse pattern is a parameter of the result (public). Result ids move with the results
  (`gram-schmidt-program`, `hutchpp-program`, `hutchpp-program-tail`, `hutchpp-program-dense`,
  `hutchpp-program-sparse`); new: `matrix-free-dense-substitution`, `matrix-free-coo-substitution`.
  The old names were never released (no `v0.1` tag), so there are no aliases.
* **Checks.** E3 is the lint of G52 and E4 asks for a result in a model (`docs/rules/rules.toml`,
  docs/contributing/programs.md); E1 accepts `ProgFamily` definitions and `Fin`-families of handles and index
  expressions; the E3 allowlist (the COO pattern) is gone, since the pattern is a parameter of the
  instance. New fixtures in `scripts/Programs.lean` for the three gaps, and the new
  `scripts/AccessModelFixtures.lean`, which proves the instance forms of the cheating realisations
  false (run by `scripts/stage_check.sh` and CI).



## First-order programs and target statements (2026-10-23)

**Approved by the maintainer on 2026-10-23**, after two independent audits of the access models,
in his words: "yeah go for both". The two changes:

1. **Target statements are library definitions.** Each result the library wants is a
   `def … : Prop`, written and reviewed by the library, of the form
   "∃ prog : Prog, Model prog cost mem spec". A result is `theorem foo : Target`. The prover
   supplies a program and a proof, and nothing else: no hypothesis, parameter or postcondition.
2. **The witness is a finite first-order program**: one syntax tree for all sizes, the sizes
   variables of the program, the literals fixed in the tree, no Lean function inside the term.
   The run is defined on this syntax. The PHOAS builder stays as surface syntax, compiled once by
   a computable function; the theorems are about the compiled tree, so the compiler is not
   trusted.

**The maintainer's decisions on the questions of this section, 2026-10-23** (F12 records each):
* Q2: library algorithms get **named-program targets**, stated about the registered compiled tree,
  so that the claim and the emitted code are about the same tree; existential targets are not
  used for library results for now. In his words: "named for stuff in our library for now. we
  will just keep this in mind when we are setting goals for the community."
* Q1: the uniform sparse model comes later, as a small stage of its own.
* Q3: changes to target definitions and to `docs/targets.toml` need the maintainer's approval;
  agents never edit `*Targets.lean` files or the registry.
* Q4: the complex comparisons `lt` and `le` fail on incomparable values.
* Q5: a target with declared inputs computed from the sizes carries a registry flag and a
  docstring marker.

So change 1 is implemented in its named form: a target is "Model (registered tree) cost mem
spec"; the existential form "∃ prog : Prog, Model prog cost mem spec" of the approval is kept
as the future form for community goals (F1).

This section is the design. Until its migration (F11) lands, sections "Guarantees" and §§1–11
describe the code as it is; F10 is the classification after the migration.

**What was elaborated.** Every Lean definition and statement of F2 to F8 was elaborated against
the library at `4a095ad` in a scratch file (`fo/FirstOrder.lean` in the design's scratch
directory, not in the repository), under the scratch names noted in F7. Proved there, with only
`propext`, `Classical.choice` and `Quot.sound`:
* the bridge `FStmt.exec_eq_exec_toStmt` and `Prog.exec_eq_exec_toStmt` (the run on first-order
  syntax is the current run of the instantiated statement), about 70 lines;
* the compilation of `gramSchmidtProg`, `hutchppProg` and dense Hutch++ (`hutchppProg` with its
  oracle calls replaced by `denseImpl`), each with `rfl` (69, 173 and 221 nodes);
* their instantiation equations (`c.toStmt N n = F.inst N n`), each by `rfl`;
* four of the five targets of F8 (`MatrixFreeGramSchmidt`, `MatrixFreeHutchpp`,
  `MatrixFreeProbHutchpp`, `StoredEntriesDenseHutchpp`), in the named form, from the existing
  public results with no change to any existing proof; the sparse target is stated, and its proof
  needs one induction lemma (F5);
* the constructor normal forms of the three registered trees (by `Meta.reduce`; neither the
  builder nor the compiler occurs in them), their hashes, and the closures of the named targets
  with the trees as leaves (the builder is then outside the closure);
* the lint (the result is a theorem whose type is the target constant) and the closure hash of
  F1, with three rejected fixtures (an axiom, and two of the audit's cheats) and two hash
  fixtures (an edit under an `irreducible_def`, an edit of a ForMathlib definition in a Mathlib
  namespace, each changing the hash).

The whole scratch file elaborates in about 12 seconds.

*Revised the same day after a bounded review of the first version (`59c5e27`)*: the closure walk
of F1 item 3 followed definitions, inductive types and constructors only, so the value under an
`irreducible_def` (an opaque whose type names the definition) was neither reached nor hashed, and
`hansonWrightConstant`, `subgaussianRangeFinderFactor` and `subgaussianEmbeddingDim` in the tail
target could have been weakened with no change of hash; and it told library constants by name
prefix, so ForMathlib definitions in Mathlib namespaces were not hashed. Both are fixed (F1), with
the lint's further points (a) and (b), the trusted base (F10), the emitter and the bookkeeping
(F11), and Q1, Q2 and the new Q5. The maintainer then decided Q1 to Q5 (above), and the targets
are restated in the named form.

### F1. Targets

**Form (named, approved 2026-10-23).** A target is a closed `Prop` in the library about a
**registered tree**, a library constant of type `Prog P ι r b` (a compiled program, F5):
```lean
def MatrixFreeHutchpp : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (o : ι) (d : Dist) (𝕜 : Type) [RCLike 𝕜],
    MatrixFree (𝕜 := 𝕜) p (hutchppProg.compiled p o d) valid X inputs cost mem post
```
with `valid`, `X`, `inputs`, `cost`, `mem` and `post` written out in the target (F8). The prover
chooses nothing: not the program, which is the library's registered tree, and not the statement.
The quantifiers are part of the review:
* **the tree's arguments are names only**: the tag type and the oracle-name type, tags, oracle
  names, distributions, and (for the sparse target only, F8) the public pattern. They carry no
  size and no data;
* **the sizes, the declared inputs, the matrix or the entries, and the tape** are quantified
  inside the model, after the tree is fixed. The field `𝕜` and the parameters of the guarantee
  (`r`, `δ`, `τ` of the tail, with their hypotheses `0 < δ`, `0 ≤ τ`, written by the library)
  are quantified outside, but the tree does not take them as arguments, so one tree serves them
  all.

**The registered tree.** The registry records, per tree, the hash of its **constructor normal
form**: the `FStmt` term after full evaluation (`Meta.reduce`, types and proofs kept), a term
built from the constructors of `FStmt`, `Instr`, `IExp`, `Cell`, `Arg`, `BinOp`, `UnOp`, `CmpOp`,
`Dist`, literals and the tree's name arguments. It does not depend on the builder that produced
it. The closure walk of item 3 below treats a registered tree as a leaf hashed by its normal form,
so an edit of a kernel or of the builder that leaves the tree unchanged changes no hash, and any
change of the tree needs a registry diff. The emitter prints the registered tree (F11, step C),
so the claim and the emitted code are about the same tree. In the scratch the three trees
(Gram–Schmidt, Hutch++, dense Hutch++) reduce in about a second together, and with them as leaves
the closure of `MatrixFreeHutchpp` no longer contains `hutchppProg` (181 constants, against 230
when the walk follows the tree's definition).

The sparse tree is the exception until Q1: `cooImpl` folds over the pattern, so for a symbolic
pattern the tree has no closed normal form. Its target is about `hutchppProg.compiledCoo p o d
pattern` with the ordinary closure walk, which then takes in the builder, `cooImpl` and the
compiler (241 constants), so it is frozen as code rather than as a tree. The uniform sparse
stage (Q1) makes it a registered tree like the others.

**The future form, for community goals** (not implemented now). For a result open to any
algorithm (a complexity claim the library sets as a goal) the target is existential,
`∀ names, ∃ prog : Prog P ι r b, ∀ 𝕜, Model p prog …`, with only names before `∃ prog`. All of
this section applies to it except the registered tree, and a named target implies it in one
line (`⟨_, h⟩`). The library defines none until it sets such goals.

**The verification criterion.** A published cost result is a theorem whose type is the target
constant itself: `info.type == .const T us`, syntactically, with no binder. The lint
(`scripts/Targets.lean`, rule E3 rewritten, F9):
1. every target listed in the registry `docs/targets.toml` has exactly one proof: a **theorem**
   (`ConstantInfo.thmInfo`, so neither an `axiom` nor an `opaque`) whose type is `.const T us`
   (fixture `axHutchpp : MatrixFreeHutchpp`, an axiom, is rejected);
2. every theorem outside the Computation core with a `Result:` id whose statement mentions a run
   or a budget is one of these. The constants that count as a run or a budget: the models on
   `Prog`, `Prog.exec`, `FStmt.exec`, `Prog.RunsWithin`, and equally the current ones,
   `RunsWithin`, `Computation.exec`, `Stmt`, `ProgFamily.inst` and the `ProgFamily` models. So a
   theorem of the old form, or of audit 2's form (a bare `exec`), cannot reach the explorer
   without the lint;
3. the **closure hash** of each target matches the registry. The closure is every library
   constant the target's statement reaches, of **every kind**: definitions and opaques (type and
   value), theorems, axioms and quotients (type), inductive types (type, numbers of parameters and
   indices, the mutual block, the constructors), constructors and recursors (type). The walk
   follows the constants of every type, the values of definitions and opaques, the mutual blocks
   and the constructors. An `irreducible_def c := v` is `def c := wrapped.1` with
   `opaque wrapped : {x // x = definition}` and `def definition := v`: the opaque's type leads to
   `definition`, whose value is hashed. A constant is a **library constant by its module**, as in
   `scripts/Audit.lean` (its module is an `NLAlib` module), not by its name, so ForMathlib
   definitions in Mathlib namespaces (`Matrix.compound`, `RCLike.toComplex`, `IsUniformApproxOn`)
   are hashed. Mathlib itself is not hashed but pinned: the registry records the Lean toolchain
   (`leanprover/lean4:v4.33.1` today) and the Mathlib revision of `lake-manifest.json`
   (`0df444a…` today), and the lint fails if either differs from the build's.

Item 3 is what makes the trivial check sufficient. Without it a prover could keep the type
`MatrixFreeHutchpp` and weaken the target by editing a definition it unfolds to, such as
`hutchppCount`, or the value `1/196` under `hansonWrightConstant`. The closure of the five
targets of F8 has 94 named library constants besides the targets (computed in the scratch,
listed in F10). The hash is `mixHash` over the names and elaborated expressions. Scratch
fixtures, both passing: setting the definition under `hansonWrightConstant` to `1/197` changes the
hash of `MatrixFreeProbHutchpp`, and an edit of `Matrix.compound` (ForMathlib, namespace `Matrix`)
changes the hash of a definition that uses it. In the library the same two fixtures run as
`scripts/Targets.lean` tests, on copies of a target.

**The registry entry** of a target: its name, its file, the closure hash, the registered trees
it names with their normal-form hashes, the flag `precomputed` (Q5), the pretty-printed
statement (the target unfolded one level, so that a diff of the registry shows what a statement
says, not only that a hash changed), the review date, and once for the file the toolchain and the
Mathlib revision. A toolchain or Mathlib bump changes every hash with no change of statement; it
is one registry diff, which the printed statements make reviewable, and it needs the maintainer's
re-approval like any other (Q3). Targets live in files of their own,
`<Topic>/<Spec>Targets.lean` (for example `Estimation/Trace/HutchPlusPlusTargets.lean`, which also
receives `hutchppCount`), so that a proof file can be owned by an agent while the statements it
proves cannot change without a registry diff (Q3).

**Why the audit's reading-level cheats cannot prove a target** (scratch file `audit1/cheat1.lean`;
the second and third are fixtures of the scratch lint):
* *A size that encodes the datum, with a postcondition of the prover's*
  (`matrixFree_sizeTraceProg`: `n 0` carries $\mathbf{A}$, `litIdx` writes it, and the
  postcondition `ComputesTrace` is an implication `A = decode (n 0) → …`). Under a target the
  prover chooses neither the sizes (`r` and their meaning are in the target), nor the size
  condition, nor the postcondition: `MatrixFreeHutchpp` demands
  `st.store.read p 0 0 = some (hutchpp A S G)` for every $\mathbf{A}$, which a program that reads
  only sizes cannot meet. Its type `MatrixFree … ComputesTrace` is not a registered constant, so
  the lint rejects it as a result.
* *A vacuous outer hypothesis* (`matrixFree_vacuous`, `hall : ∀ N A, A.trace = 0`). The type
  `(∀ N A, A.trace = 0) → MatrixFreeHutchpp` is a `∀`, not the constant: rejected (fixture
  `vacuousHutchpp`). Every hypothesis inside a target is the library's.
* *An outer parameter unrolled into a literal* (`matrixFree_literalTraceProg`, `A₀` before the
  program). The type `∀ A₀, MatrixFreeHutchpp` is rejected (fixture `outerHutchpp`). Inside the
  target the program is the registered tree, whose literals are fixed in the registry before any
  matrix is quantified (and, in the future existential form, chosen before the matrix).
* *A program of the prover's.* Under a named target there is none: the tree is the library's,
  and replacing it changes its normal-form hash.
* *A claim phrased through `exec`* (audit 2, `exec_copyTrace`). It proves no registered target,
  so it is not a published result whatever it says. Publication is opt-in through the registry,
  so E3 has nothing left to cover (G52).

**Names.** A target is an UpperCamelCase `Prop` named model first, then the specification:
`MatrixFreeGramSchmidt`, `MatrixFreeHutchpp`, `MatrixFreeProbHutchpp`,
`StoredEntriesDenseHutchpp`, `StoredEntriesCooHutchpp`. Its proof is the lowerCamelCase of the
same name (`theorem matrixFreeHutchpp : MatrixFreeHutchpp`), which is the head of its
conclusion (N2). The result ids `gram-schmidt-program`, `hutchpp-program`,
`hutchpp-program-tail`, `hutchpp-program-dense` and `hutchpp-program-sparse` move to these
theorems.

### F2. The first-order syntax

**Choice: intrinsically scoped syntax with de Bruijn levels**, a type-level guarantee rather than
a well-formedness predicate. `FStmt P ι nb ni` is a statement with `nb` handles and `ni` index
variables in scope. It reuses `IExp`, `Cell`, `Instr` and `Arg` of `Syntax.lean` at
`VB := Fin nb`, `VI := Fin ni`, so the two sorts stay separate, as D11 requires. A handle or index
out of scope is a type error, so no scoping predicate appears in any statement. Levels rather
than indices: a binder adds variable `nb` (`Fin.last nb`), and the variables around it keep
their numbers, so a term moves under a binder with no shifting, and the handle of a buffer is its
position in the store.
```lean
inductive FStmt (P ι : Type) : ℕ → ℕ → Type where
  | skip {nb ni : ℕ} : FStmt P ι nb ni
  | seq {nb ni : ℕ} (s t : FStmt P ι nb ni) : FStmt P ι nb ni
  | instr {nb ni : ℕ} (i : Instr P (Fin nb) (Fin ni)) : FStmt P ι nb ni
  | apply {nb ni : ℕ} (o : ι) (p : P) (dst : Fin nb) (dOff : IExp (Fin ni)) (src : Fin nb)
      (sOff cols : IExp (Fin ni)) : FStmt P ι nb ni
  | rom {nb ni : ℕ} (p : P) (dst : Cell (Fin nb) (Fin ni)) (i : IExp (Fin ni)) : FStmt P ι nb ni
  | alloc {nb ni : ℕ} (p : P) (len : IExp (Fin ni)) (body : FStmt P ι (nb + 1) ni) :
      FStmt P ι nb ni
  | loop {nb ni : ℕ} (n : IExp (Fin ni)) (body : FStmt P ι nb (ni + 1)) : FStmt P ι nb ni
  | whileFuel {nb ni : ℕ} (fuel : IExp (Fin ni)) (p : P) (c : CmpOp)
      (x y : Cell (Fin nb) (Fin ni)) (body : FStmt P ι nb ni) : FStmt P ι nb ni
  | ite {nb ni : ℕ} (p : P) (c : CmpOp) (x y : Cell (Fin nb) (Fin ni)) (t e : FStmt P ι nb ni) :
      FStmt P ι nb ni
  | named {nb ni : ℕ} (name : String) (args : List (Arg (Fin nb) (Fin ni)))
      (body : FStmt P ι nb ni) : FStmt P ι nb ni

/-- **A program**: `b` declared buffers (handles `0, …, b-1`), the oracle dimension `N` (index
`0`) and `r` further sizes (indices `1, …, r`). One finite tree for all sizes. -/
abbrev Prog (P ι : Type) (r b : ℕ) : Type := FStmt P ι b (r + 1)
```
How each construct binds and refers:

| construct | binds | refers to |
|---|---|---|
| sizes | `N` is index `0`, size `i` is index `i + 1`: the free index variables of a `Prog` | |
| declared buffers | handles `0, …, b-1`: the free handles of a `Prog` | |
| `alloc p len body` | handle `nb` in `body` (its stack position at run time) | `len : IExp (Fin ni)` |
| `loop n body` | index `ni` in `body`, the iteration index | `n` |
| `whileFuel fuel p c x y body` | nothing | `fuel`, the cells `x`, `y` |
| `ite p c x y t e` | nothing | the cells `x`, `y` |
| `named name args body` | nothing; a label for the emitter, runs as `body` | `args` |
| `apply o p dst dOff src sOff cols` | nothing | two handles, three index expressions |
| `rom`, and the instructions (`lit`, `litIdx`, `bin`, `un`, `copy`, `draw`, `convert`) | nothing | cells and index expressions in scope |

* **Literals** are closed: `Instr.lit p dst (q : ℚ)` holds a rational fixed in the tree and
  interpreted per tag by `sem.lit p q` (a format semantics rounds it or fails). `litIdx` writes the
  value of an index expression over the sizes and loop indices, charged as one literal (G4).
  `IExp.const n` is a closed natural number. No literal can depend on a size: the tree is fixed
  before the sizes.
* **Draws and conversions** bind nothing: `draw p d dst` reads the tape of `d` at its current
  position; `convert p q dst src` reads at tag `p` and writes at tag `q`.
* **`scope`** of the builder is not a node: it closes the continuation, so its allocations are
  nested in the compiled tree exactly as they are in the builder's statement.

The structural maps used by the run (the substitution of index expressions for variables, and
the value of an index expression in an environment):
```lean
def IExp.subst {α β : Type} (σ : α → IExp β) : IExp α → IExp β
def IExp.evalIn {α : Type} (ρ : α → ℕ) : IExp α → ℕ
theorem IExp.eval_subst (σ : α → IExp ℕ) (e : IExp α) :
    (e.subst σ).eval = e.evalIn fun v => (σ v).eval
def Cell.subst (f : VB → VB') (σ : VI → IExp VI') (c : Cell VB VI) : Cell VB' VI'
def Instr.subst (f : VB → VB') (σ : VI → IExp VI') : Instr P VB VI → Instr P VB' VI'
def Arg.subst (f : VB → VB') (σ : VI → IExp VI') : Arg VB VI → Arg VB' VI'
```

### F3. The run on first-order syntax

The run takes an environment of handles `ρB : Fin nb → ℕ` and of index values
`ρI : Fin ni → ℕ`. Its leaves are the clauses of `exec` with each index expression evaluated in
the environment; `alloc` binds `st.store.size`, `loop` binds the iteration index. Every charge,
memory and failure rule is the one of `exec`, clause for clause:
```lean
def FStmt.exec : {nb ni : ℕ} → FStmt P ι nb ni → (Fin nb → ℕ) → (Fin ni → ℕ) →
    St P K C → Option (St P K C)
  | _, _, .skip, _, _, st => some st
  | _, _, .seq s t, ρB, ρI, st => (s.exec ρB ρI st).bind (t.exec ρB ρI)
  | _, _, .instr i, ρB, ρI, st =>
      let i' := i.subst ρB fun v => .const (ρI v)
      (i'.run I.sem I.tape st.store st.pos).map fun r =>
        { st with store := r.1, pos := r.2, cnt := st.cnt + I.charge i'.kind }
  | _, _, .apply o p d dOff s sOff cols, ρB, ρI, st =>
      let L := I.height o * cols.evalIn ρI
      if ρB d ≠ ρB s ∨ dOff.evalIn ρI + L ≤ sOff.evalIn ρI ∨ sOff.evalIn ρI + L ≤ dOff.evalIn ρI then
        (st.store.readBlock p (ρB s) (sOff.evalIn ρI) L).bind fun X =>
          (I.oracle o (cols.evalIn ρI) X).bind fun Y =>
            (st.store.writeBlock p (ρB d) (dOff.evalIn ρI) Y).map fun s' => { st with
              store := s'
              cnt := st.cnt + (I.charge (.load p o) + cols.evalIn ρI • I.charge (.matvec p o)) }
      else none
  | _, _, .rom p d i, ρB, ρI, st => (I.rom (i.evalIn ρI)).bind fun v =>
      (st.store.write p (ρB d.buf) (d.idx.evalIn ρI) v).map fun s' =>
        { st with store := s', cnt := st.cnt + I.charge (.rom p) }
  | nb, _, .alloc p len body, ρB, ρI, st =>
      let n := len.evalIn ρI
      (body.exec (Fin.snoc (α := fun _ => ℕ) ρB st.store.size) ρI { st with
          store := st.store.push (p, Array.replicate n none),
          cur := Function.update st.cur p (st.cur p + n),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + n)),
          curW := st.curW + n * I.width p,
          peakW := max st.peakW (st.curW + n * I.width p) }).map
        fun st₂ => { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - n)
          curW := st₂.curW - n * I.width p }
  | _, _, .loop n body, ρB, ρI, st =>
      (List.range (n.evalIn ρI)).foldlM
        (fun st i => body.exec ρB (Fin.snoc (α := fun _ => ℕ) ρI i) st) st
  | _, _, .whileFuel fuel p c x y body, ρB, ρI, st =>
      ((List.range (fuel.evalIn ρI)).foldlM (fun (s : St P K C × Bool) _ =>
        if s.2 then (cmpStep I p c (x.subst ρB fun v => .const (ρI v))
            (y.subst ρB fun v => .const (ρI v)) s.1).bind fun r =>
          if r.1 then (body.exec ρB ρI r.2).map fun st' => (st', true) else some (r.2, false)
        else some s) (st, true)).bind fun r => if r.2 then none else some r.1
  | _, _, .ite p c x y t e, ρB, ρI, st =>
      (cmpStep I p c (x.subst ρB fun v => .const (ρI v)) (y.subst ρB fun v => .const (ρI v))
        st).bind fun r => if r.1 then t.exec ρB ρI r.2 else e.exec ρB ρI r.2
  | _, _, .named _ _ body, ρB, ρI, st => body.exec ρB ρI st

def Prog.exec (prog : Prog P ι r b) (N : ℕ) (n : Fin r → ℕ) (st : St P K C) : Option (St P K C) :=
  FStmt.exec I prog (fun j => (j : ℕ)) (Fin.cons N n) st
```
(`I : Interp P ι K C` is an explicit section variable, as for `exec`.)
The leaves are written out, not delegated to `exec`, so that neither `exec` nor the PHOAS `Stmt`
is in the closure of a target (F10). The copies cannot drift apart from `exec`: the bridge below is
a theorem, and a difference between them makes its proof fail.

**The bridge.** `FStmt.toStmt` instantiates a first-order statement as a statement of the current
syntax at `VB := ℕ`, `VI := ℕ`: handles renamed by `ρB`, index variables replaced by index
expressions `σ`, a loop variable by `.var i`. `Prog.toStmt` instantiates the sizes as constants,
so that `Prog.toStmt prog N n` has the shape that `ProgFamily.inst` builds today.
```lean
def FStmt.toStmt : {nb ni : ℕ} → FStmt P ι nb ni → (Fin nb → ℕ) → (Fin ni → IExp ℕ) →
    Stmt P ι ℕ ℕ
def Prog.toStmt (prog : Prog P ι r b) (N : ℕ) (n : Fin r → ℕ) : Stmt P ι ℕ ℕ :=
  FStmt.toStmt prog (fun j => (j : ℕ)) (Fin.cons (.const N) fun i => .const (n i))

theorem FStmt.exec_eq_exec_toStmt {nb ni : ℕ} (s : FStmt P ι nb ni) (ρB : Fin nb → ℕ)
    (σ : Fin ni → IExp ℕ) (st : St P K C) :
    s.exec I ρB (fun v => (σ v).eval) st = exec I (s.toStmt ρB σ) st
theorem Prog.exec_eq_exec_toStmt (prog : Prog P ι r b) (N : ℕ) (n : Fin r → ℕ) (st : St P K C) :
    prog.exec I N n st = exec I (prog.toStmt N n) st
```
Both are proved (with `Instr.run_subst_congr`, `Instr.kind_subst`, `cmpStep_subst_congr`: a leaf
depends on its index expressions only through their values). Every lemma and every invariant of
`exec` (G9, G10, G13, G14, G29) therefore holds for `Prog.exec` by one rewrite. `toStmt` is proof
infrastructure: no target mentions it.

**`whileFuel`, stated exactly.** The loop tests at most `fuel` times and fails if every test it
makes holds. So a successful run executes the body at most `fuel − 1` times, and the loop fails if
the body runs `fuel` times. The docstring of `Stmt.whileFuel` ("at most `fuel` times") is off by
one; it is corrected in step A, and `FStmt.whileFuel` is documented with this text.

### F4. Subprograms: macro expansion, specifications proved once

**Choice: macro expansion at build time.** A kernel (`dot`, `axpy`, …, `gramSchmidtProg`) stays a
builder function. Each call is expanded into the caller's tree when the caller is compiled, and
the `named` node keeps the label for the emitter. The first-order syntax has no call construct,
and its run has no argument passing, so the trusted base gains nothing.

**Reuse of specifications.** A kernel specification is proved once, about the current run of the
builder's statement at `VB := ℕ`, `VI := ℕ` (as `exec_dot`, `exec_gramSchmidtProg` are today).
A target's proof goes through the bridge: `Prog.exec c = exec (c.toStmt N n)`, and
`c.toStmt N n = F.inst N n` by `rfl` (F5). In `F.inst N n` a kernel call is the Lean application
whose specification is already proved. Measured cost, on the existing programs: no new lemma,
one `rfl` instantiation equation per compiled program, and term growth by the expanded kernels
(Hutch++ is 173 nodes, dense Hutch++ 221).

**What is not needed.** No substitution lemma on first-order syntax: proofs never reason about an
expanded copy directly. Such a lemma (`(k.subst σ).exec ρ = k.exec (eval ∘ σ)`, about 150 lines)
would be needed only for proofs written natively on first-order syntax.

**Alternative, recorded.** A `call` construct with a table of closed first-order subprograms. A
specification would then be proved once on the callee's tree, with a call lemma, and trees would
be smaller. It would add argument passing (handles, index expressions, cells) to the trusted run,
about 60 lines, and the proofs would move off the builder. Worth it only if expanded trees become
too large (none is, Lanczos included) or proofs move to first-order syntax.

### F5. The compiler

```lean
def IExp.scope? (ni : ℕ) : IExp ℕ → Option (IExp (Fin ni))
def Cell.scope? (nb ni : ℕ) (c : Cell ℕ ℕ) : Option (Cell (Fin nb) (Fin ni))
def Instr.scope? (nb ni : ℕ) : Instr P ℕ ℕ → Option (Instr P (Fin nb) (Fin ni))
def Arg.scope? (nb ni : ℕ) : Arg ℕ ℕ → Option (Arg (Fin nb) (Fin ni))
/-- A statement at `VB := ℕ`, `VI := ℕ`, read with handles and indices as de Bruijn levels; a
binder is applied to the next level, once; `none` if a variable is out of scope. -/
def Stmt.compile : Stmt P ι ℕ ℕ → (nb ni : ℕ) → Option (FStmt P ι nb ni)
/-- A family compiled once, at symbolic sizes: `N` is `.var 0`, size `i` is `.var (i + 1)`,
declared buffer `j` is handle `j`. -/
def ProgFamily.compile (F : ProgFamily P ι r b) : Option (Prog P ι r b) :=
  (F ℕ ℕ (.var 0) (fun i => .var (i + 1)) fun j => j).compile b (r + 1)
```
A library program is `(ProgFamily.compile F).get h`, with `h` by `rfl` (checked for the three
programs). Named `<spec>Prog.compiled`, for example `hutchppProg.compiled p o d : Prog P ι 2 1`;
its instantiation equation `hutchppProg.toStmt_compiled` is `rfl`.

**Size-dependent host computation is excluded by construction.** The compiler calls the family
once, on the variables `.var 0, .var 1, …` and the handles `0, …, b-1`, never on a value of a
size. Whatever Lean code the builder runs, it runs once, on syntax, and yields one tree. Even a
builder that inspects the syntax it is given (matches on `.var 0`, or type-cases at `VI := ℕ`
with `Classical`) produces one fixed tree, and the theorem is about that tree. The compiler can
also reject: a forged handle (`forgeNat`) is out of scope, and compilation returns `none`.

**The compiler is not trusted, and a general correctness lemma is neither provable nor needed.**
"`(F.compile).get h` instantiates to `F.inst N n`" for every family `F` is parametricity in
`VB`, `VI`, and it is false for a family that type-cases on its sorts. What the reuse of existing
proofs needs is the equation for each library program, and it is `rfl`. A builder that recurses
on host data is the exception: `cooImpl` folds over the pattern, so compiling sparse Hutch++ for
a symbolic pattern needs an induction on the pattern, proving that compilation succeeds and
instantiates to `cooImpl` (about 100 to 150 lines, step B). That proof is the only one in the
migration that is not mechanical.

### F6. Size-dependent constants

The tree is fixed before the sizes, so a constant that depends on a size is never a literal. Two
ways, in order of preference:
1. **Computed by the program, and counted.** Every constant built from rational literals, index
   values (`litIdx`), the field operations, square roots and comparisons: $1/\ell$ in Hutch++
   (`litIdx ℓ`, one division), $\sqrt{N}$, $\log_2 N$ by a loop of comparisons, a bisection to any
   precision. These are counted like any other operation.
2. **A declared input of the target.** A constant the semantics cannot compute exactly (cosines
   of Chebyshev nodes, tabulated quadrature weights) is a declared buffer whose contents the target
   gives as a function of the sizes, for example `inputs N n _ := ![nodes (n 0)]`. It is visible in
   the target, reviewed with it and hashed in its closure, and counted as memory from the start
   (G15), but its computation is uncounted host work. The target's docstring says so ("given the
   $q$ Chebyshev nodes").

A third way, new operations (`cos`, `log`) in `UnOp` with a semantics and a contract, is a later
change of the semantics, not a design point here.

### F7. Models on programs

The models keep their shape. `ProgFamily` becomes `Prog`, and `RunsWithin` gets its first-order
form. In the scratch file these are `Scratch.ProgRunsWithin`, `Scratch.MatrixFree`,
`Scratch.StoredEntries` and `Scratch.MatrixFreeProb`; the names below are the final ones.
```lean
def Prog.RunsWithin (I : Interp P ι K C) (prog : Prog P ι r b) (N : ℕ) (n : Fin r → ℕ)
    (st₀ : St P K C) (c : C) (m : P → ℕ) (Q : St P K C → Prop) : Prop :=
  ∃ st, prog.exec I N n st₀ = some st ∧ st.cnt ≤ st₀.cnt + c ∧
    (∀ q, st.peak q + I.romSize q ≤ m q) ∧ Q st
theorem Prog.runsWithin_iff : prog.RunsWithin I N n st₀ c m Q ↔
    RunsWithin I (prog.toStmt N n) st₀ c m Q

def MatrixFree (p : P) (prog : Prog P ι r b) (valid : ℕ → (Fin r → ℕ) → Prop)
    (X : ℕ → (Fin r → ℕ) → Type)
    (inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option 𝕜))
    (cost : ℕ → (Fin r → ℕ) → OpCount P ι) (mem : ℕ → (Fin r → ℕ) → P → ℕ)
    (post : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) 𝕜 → (Dist → ℕ → ℝ) →
      St P 𝕜 (OpCount P ι) → Prop) : Prop :=
  ∀ N n, valid N n → ∀ (x : X N n) (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ),
    prog.RunsWithin (exactInterp (fun _ => A) ξ) N n
      (inputState p (List.ofFn (inputs N n x))) (cost N n) (mem N n) (post N n x A ξ)
```
`StoredEntries` and `MatrixFreeProb` (in `RandomMatrix/Tape.lean`) change the same way:
`(prog.inst N n)` becomes `prog.RunsWithin … N n`. The `ProgFamily` models are kept as proof
infrastructure, renamed `ProgFamily.MatrixFree`, `ProgFamily.StoredEntries` and
`ProgFamily.MatrixFreeProb` (with the composition theorems
`ProgFamily.MatrixFree.storedEntries_substOracle_denseImpl` and `…_cooImpl`). Each gets one
transfer lemma, which generalises the scratch proofs:
```lean
theorem ProgFamily.MatrixFree.prog (h : F.MatrixFree p valid X inputs cost mem post)
    (c : Prog P ι r b) (hc : ∀ N n, c.toStmt N n = F.inst N n) :
    MatrixFree p c valid X inputs cost mem post
```

### F8. The targets of the existing results

Written out as elaborated, in the named form (the scratch names `gramSchmidtProgram`,
`hutchppProgram`, `denseHutchppProgram`, `cooHutchppProgram` are the library's
`gramSchmidtProg.compiled`, `hutchppProg.compiled`, `hutchppProg.compiledDense`,
`hutchppProg.compiledCoo`; the sparse one stated, not yet proved):
```lean

/-- Rank-revealing modified Gram–Schmidt in place. -/
def MatrixFreeGramSchmidt : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (𝕜 : Type) [RCLike 𝕜],
    MatrixFree (𝕜 := 𝕜) p (gramSchmidtProg.compiled (ι := ι) p) (fun _ _ => True)
      (fun N n => Matrix (Fin N) (Fin (n 0)) 𝕜)
      (fun _ _ Y => ![(flatten Y).map some]) (fun N n => gramSchmidtCount p N (n 0))
      (fun N n q => if q = p then N * n 0 + 3 else 0)
      (fun _ _ Y _ _ st => Holds st.store p 0 0 (gramSchmidtQ Y))

/-- Hutch++, matrix-free. -/
def MatrixFreeHutchpp : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (o : ι) (d : Dist) (𝕜 : Type) [RCLike 𝕜],
    MatrixFree (𝕜 := 𝕜) p (hutchppProg.compiled p o d) (fun _ n => 0 < n 1) (fun _ _ => Unit)
      (fun _ _ _ => ![Array.replicate 1 none]) (fun N n => hutchppCount p o d N (n 0) (n 1))
      (fun N n q => if q = p then 2 * N * (n 0 + n 1) + 4 else 0)
      (fun N n _ A ξ st => st.store.read p 0 0 = some
        (hutchpp A (tapeMatrix (ξ d) 0 N (n 0)) (tapeMatrix (ξ d) (N * n 0) N (n 1))))

/-- The Gaussian tail of Hutch++ that draws its own test matrices. -/
def MatrixFreeProbHutchpp : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (o : ι) (r : ℕ) (δ : ℝ), 0 < δ → ∀ τ : ℝ, 0 ≤ τ →
    MatrixFreeProb (𝕜 := ℝ) p (hutchppProg.compiled p o .gaussian)
      (fun _ n => 0 < n 0 ∧ 0 < n 1 ∧ subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2) ≤ n 0)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none])
      (fun N n => hutchppCount p o .gaussian N (n 0) (n 1))
      (fun N n q => if q = p then 2 * N * (n 0 + n 1) + 4 else 0)
      (fun _ _ _ A st => ∃ v, st.store.read p 0 0 = some v ∧ |A.trace - v| < τ)
      (fun _ n _ A => δ + 2 * Real.exp (-(hansonWrightConstant *
        min (n 1 * τ ^ 2 / (subgaussianRangeFinderFactor 1 * frobNorm (A - truncatedSVD A r) ^ 2))
          (n 1 * τ / (√(subgaussianRangeFinderFactor 1) * frobNorm (A - truncatedSVD A r))))))

/-- Dense Hutch++, from `N²` stored entries. -/
def StoredEntriesDenseHutchpp : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (o : ι) (d : Dist) (𝕜 : Type) [RCLike 𝕜],
    StoredEntries (𝕜 := 𝕜) p (hutchppProg.compiledDense p o d) (fun _ n => 0 < n 1)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none]) (fun N _ => N * N)
      (fun N n => substCount (denseCost N) (hutchppCount p o d N (n 0) (n 1)))
      (fun N n q => (if q = p then 2 * N * (n 0 + n 1) + 4 else 0) + 1 +
        if q = p then N * N else 0)
      (fun N n _ vals ξ st => st.store.read p 0 0 = some
        (hutchpp (Matrix.of fun (i j : Fin N) => vals (i + N * j)) (tapeMatrix (ξ d) 0 N (n 0))
          (tapeMatrix (ξ d) (N * n 0) N (n 1))))

/-- Sparse Hutch++ for a public COO pattern; the tree is a function of the pattern (Q1). -/
def StoredEntriesCooHutchpp : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (o : ι) (d : Dist) (pattern : List (ℕ × ℕ))
    (𝕜 : Type) [RCLike 𝕜],
    StoredEntries (𝕜 := 𝕜) p (hutchppProg.compiledCoo p o d pattern)
      (fun N n => 0 < n 1 ∧ ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none]) (fun _ _ => pattern.length)
      (fun N n => substCount (cooCost N pattern.length) (hutchppCount p o d N (n 0) (n 1)))
      (fun N n q => (if q = p then 2 * N * (n 0 + n 1) + 4 else 0) + 1 +
        if q = p then pattern.length else 0)
      (fun N n _ vals ξ st => st.store.read p 0 0 = some
        (hutchpp (cooMatrix pattern vals) (tapeMatrix (ξ d) 0 N (n 0))
          (tapeMatrix (ξ d) (N * n 0) N (n 1))))
```
The registered trees, compiled once (F5):
```lean
def gramSchmidtProg.compiled (p : P) : Prog P ι 1 1 :=
  (ProgFamily.compile fun _ _ N n h => (gramSchmidtProg p N (n 0) (h 0)).run).get rfl
def hutchppProg.compiled (p : P) (o : ι) (d : Dist) : Prog P ι 2 1 :=
  (ProgFamily.compile fun _ _ N n h => (hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run).get rfl
def hutchppProg.compiledDense (p : P) (o : ι) (d : Dist) : Prog P ι 2 1 :=
  (ProgFamily.compile fun _ _ N n h =>
    ((hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run).substOracle (denseImpl N)).get rfl
def hutchppProg.compiledCoo (p : P) (o : ι) (d : Dist) (pattern : List (ℕ × ℕ)) : Prog P ι 2 1 :=
  (ProgFamily.compile fun _ _ N n h =>
    ((hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run).substOracle (cooImpl N pattern)).getD .skip
```
(`getD .skip` for the sparse tree, whose compilation succeeds for every pattern by the induction
of F5, not by `rfl`.) A proof, as in the scratch file:
```lean
theorem matrixFreeHutchpp : MatrixFreeHutchpp := by
  intro P ι _ p o d 𝕜 _ N n hv x A ξ
  rw [Prog.runsWithin_iff, hutchppProg.toStmt_compiled]
  exact matrixFree_hutchppProg (𝕜 := 𝕜) p o d N n hv x A ξ   -- the ProgFamily-level lemma
```
The tail target is about the same tree at `d := .gaussian`, with `simp only` through the event of
the measure; the dense target is about `hutchppProg.compiledDense`. The existing results become
the `ProgFamily`-level lemmas these proofs call.

One tree serves every `RCLike 𝕜`, every target rank and every accuracy: the tree's arguments are
the tags, the oracle name, the distribution and (sparse only) the pattern.

### F9. Rules and checks

| rule | before | after |
|---|---|---|
| E1 (programs generic in `VB`, `VI`, no host data) | error, hygiene since the Guarantees change | **retired**. The witness is a `Prog`, first-order and scoped by its type; a builder that is not generic still compiles to one tree, which is what the theorem is about. Its fixtures move: `forgeNat` becomes a compiler fixture (`compile` returns `none`), the others are dropped |
| E3 (results are instances of an access model) | the lint of G52 | **the target lint** (F1): each registered target has one proof whose type is the constant; every `Result:` theorem about runs is one, except a rounded program theorem (a leading `IsRelErrSem … I.sem` hypothesis on the interpretation `I` the conclusion runs under, or a rounded access model; approved by the maintainer 2026-11-07); the closure hashes match `docs/targets.toml`. Fixtures: the three cheats of audit 1 stated against a target, audit 2's `exec_copyTrace`, and an edit to `hutchppCount` (the hash changes) |
| E4 (every `<spec>Prog` has a result in a model) | completeness | every registered target is proved; every `<spec>Prog` has a registered tree named by a registered target. Completeness, not soundness |
| E9 (a callee closes its allocations) | error, hygiene | **warning**. Memory is the target's `mem`, so a leaking callee makes a proof fail or a target larger, never a claim false |
| E2, E5, E6, E8 | hygiene | unchanged; E2 matters for the emitter and the `Float` runner only |

docs/contributing/programs.md is rewritten accordingly, and §11 gains one rule: an agent does not edit a
`*Targets.lean` file or `docs/targets.toml`. Enforcement is in F12, Q3.

### F10. Guarantees, re-classified

The table of section "Guarantees", item by item, after the migration. "Same" keeps the class and
the basis, except that the run is `FStmt.exec` and the basis reaches it through the bridge
(`Prog.exec_eq_exec_toStmt`, P).

| # | class before | class after | what changes |
|---|---|---|---|
| G1–G3, G5, G6, G8 | P | P | same |
| G4, G7 | P, D | P, D | same |
| G9, G10 | P | P | the invariants of `exec`, through the bridge |
| G11, G12 | D | D | same: index arithmetic, loop iterations and control are not counted |
| G13–G16 | P | P | through the bridge |
| G17 | D | D | plus an audit item: the declared buffers are not counted in bit memory (`inputState` sets `curW` and `peakW` to $0$). Harmless while every interpretation has width $0$; fixed with `RunsWithinBits` (D17), whose initial state counts them |
| G18 | D | D | same; the COO index storage, pending Q1 |
| G19 | P, D | P, D | scoping is now by type (P); a builder callee's open `alloc` scopes over the caller's block, faithfully compiled; E9 a warning (D) |
| G20 | P | P | strengthened: no handle out of scope exists in a `Prog`. Audit item: an oracle call whose block is empty (`cols = 0`, or `N = 0`) reads and writes nothing, succeeds and is charged one load; in the current syntax it did so even on a handle with no buffer, which a `Prog` cannot name (D) |
| G21 | P | P | audit item, decided (Q4): under `ComplexOrder` the comparisons `lt` and `le` of two complex numbers with different imaginary parts were `false`, so a branch on them was taken silently; after step A they fail, as division by zero does; `eq` is exact |
| G22–G24, G26 | P | P | same |
| G25 | P | P | the docstring corrected (F3): a successful `whileFuel` runs its body at most `fuel − 1` times |
| G27 | P | P | strengthened: the program is bound before the sizes as well; one tree for every size and datum |
| G28–G30, G33 | P | P | same (G29 through the bridge) |
| G31 | P | P | the tree's arguments are names only (tags, oracle names, distributions, the sparse pattern), reviewed in the target; the tree depends on them, harmlessly |
| G32 | D | D | same |
| G34 | D | **P**, D | uniformity: one finite tree for all sizes; literals fixed in it; no host computation that chooses the program from the sizes (the witness is a tree, and the compiler calls the builder once, on variables). Left as D: index arithmetic uncounted (G11), which is host arithmetic on sizes during the run: `IExp.evalIn` (offsets, loop bounds, `%` with `a % 0 = a`) and the index literal `litIdx`, charged as one literal whatever its value (G4); the sparse target is non-uniform in its public pattern (Q1). (Corrected by the final audits, 2026-10-24: the first version said "no host computation on sizes", which overstated it) |
| G35 | T (parametricity) | **removed** | the witness contains no Lean function; parametricity is used nowhere, not even as hygiene |
| G36–G38, G40, G41 | P | P | same |
| G39 | T | T | same (`Dist.law`) |
| G42, G46, G49 | D | D | same |
| G43 | P | P | `FStmt.exec` is structural |
| G44, G45 | P | P | program substitution is proof infrastructure; no target mentions it |
| G47 | P | P | the targets of F8 |
| G48 | T | T | same (the specifications) |
| G50, G51 | T | T | the emitter and the `Float` runner read the builder; an emitter of `Prog` trees is a later, small tool |
| G52 | T (E3, coverage) | T (the target lint) | what is published is what the registry lists; no coverage claim is left |
| G53, G54 | T | T | same (audit; E4 as in F9); G53 rests on the kernel replay since the final audits (G61) |
| G55 | D | D | hygiene: E2, E5, E6, E8, E9 (a warning); E1 retired |
| **G56** (new) | | T | a published cost result is a theorem whose type is literally a registered target: no hypothesis, parameter or postcondition of the prover's. Script: one comparison of expressions |
| **G57** (new) | | T | the target and every library constant it reaches are frozen: the closure hash in the registry, with the toolchain and Mathlib pinned. Script, and the maintainer's review of the registry (Q3). (T) only with the closure walk of F1 item 3 (every constant kind, library membership by module); the walk of `59c5e27` skipped opaques and would not have frozen an `irreducible_def` |
| **G58** (new) | | P | the program of a result is first-order and scoped by its type (`Prog P ι r b`), checked by Lean's kernel; under a named target it is the registered tree, frozen by its normal-form hash |
| **G59** (new) | | D | the compiler and the builder are untrusted: theorems are about the compiled tree, and a non-parametric builder only yields a tree the proof must handle. A consequence of the design, not a theorem |
| **G60** (new) | | P | the run on first-order syntax agrees with the current run of the instantiated statement (`FStmt.exec_eq_exec_toStmt`), so the existing lemmas and invariants apply |
| **G61** (final audits) | | T | every constant of the package's `.olean` files (every `lean_lib`) is accepted by the kernel: `scripts/Replay.lean` replays them all through Lean core's `Environment.replay` (as `lean4checker`) onto a base read only from `.lake/packages/` and the toolchain, so no proof elaborated under `debug.skipKernelTC` or added without checking survives, in the library or in a module it could import; in `NLAlib` an `unsafe` or `partial` constant, an axiom or a use of `sorryAx`, `ofReduceBool`, `ofReduceNat` or `trustCompiler` fails it; the `.olean` files are those of the current sources (`lake build --no-build --rehash`); `scripts/Audit.lean` fails on an `unsafe` or `partial` constant. Script: about 200 lines over Lean core's replay, with fixtures (`scripts/replay_fixtures.sh`) |
| **G62** (final audits) | | D | rule S9: no `unsafe`, `partial`, `implemented_by`, `extern`, `set_option debug.…` or kernel option in the sources or `lakefile.toml`. Hygiene: G61 is the guarantee |

**Count.** 60 items, one removed (G35): 40 (P) (G4, G7, G19 partly (D)), 9 (T) (G39, G48,
G50–G54, G56, G57), 10 (D) (G11, G12, G17, G18, G32, G42, G46, G49, G55, G59). The final audits
add G61 (T) and G62 (D), and make G34 partly (D). Non-uniformity, advice
and parametricity are no longer issues; G34 is (P) and G35 is gone.

**The trusted base, exactly.** Base item 1 (kernel and axioms) is unchanged. Base item 3 (the
statement of each result) shrinks to the review of each target, done once per target, in the
registry. Base item 2 becomes the closure of the targets: the library definitions their statements
unfold to. For the five targets of F8 the scratch computation (with the walk of F1 item 3) lists
94 named constants besides the targets: 90 below and the four models. Besides these come the
hygienic `definition` constants holding the values of the three `irreducible_def`s, and the
matchers, recursors and structural-recursion helpers of the inductive types. Grouped:
* **Syntax**: `IExp`, `Cell` (`buf`, `idx`), `Instr`, `BinOp`, `UnOp`, `CmpOp`, `Dist` (with its
  derived `instDecidableEqDist`, used by the tape positions), `Arg` (labels only), `FStmt`, `Prog`;
* **Substitution and evaluation used by the run**: `IExp.subst`, `IExp.evalIn`, `IExp.eval`,
  `Cell.subst`, `Instr.subst`, and Mathlib's `Fin.snoc`, `Fin.cons`;
* **The run**: `FStmt.exec`, `Prog.exec`, `Instr.run`, `Instr.kind`, `cmpStep`, `Store`,
  `Store.read`, `Store.write`, `Store.readBlock`, `Store.writeBlock`, `St` and its fields,
  `Interp` and its fields, `ScalarSem` and its fields, `OpKind`, `OpCount`;
* **Budget and models**: `Prog.RunsWithin`, `MatrixFree`, `MatrixFreeProb`, `StoredEntries`,
  `inputState`;
* **Interpretations and layout**: `exactSem`, `exactInterp`, `storedInterp`, `matOracle`,
  `flatten`, `unflatten`, `tapeMatrix`, `Holds`, `Dist.law`, `tapeLaw`;
* **Count and memory formulas**: `gramSchmidtCount`, `hutchppCount`, `denseCost`, `cooCost`, and
  the count substitutions `substCount`, `substKind`, `substCountG`;
* **Specifications**: `gramSchmidtQ`, `hutchpp` (with `rangeProjector`, `girardHutchinson`,
  `rsvd`), `cooMatrix`; for the tail, `frobNorm`, `truncatedSVD` (with `IsSVD`, `svdU`, `svdV`,
  `singularValues`, `HasOrthonormalCols`), `subgaussianEmbeddingDim`,
  `subgaussianRangeFinderFactor`, `hansonWrightConstant`, `subgaussianJLConstant` (reached through
  `subgaussianEmbeddingDim`), `iidSequence`, `rademacherMeasure`, and the values of the three
  `irreducible_def`s;
* **the targets themselves**, and the registered trees they name. A tree is read for what it is
  (the program the result is about, printed by the emitter), not trusted for soundness: whatever
  it is, the theorem proves that it meets the statement. With the trees as leaves the builders,
  kernels and compiler are outside the closure, except for the sparse target until Q1 (F1).

**Additions of the final audits (2026-10-24)**, which the paragraph above left out. Besides the
kernel, the axioms and the closures, a target's meaning rests on:
* the kernel having checked every constant (G61): before the audits only the elaborator's call of
  the kernel did, which `set_option debug.skipKernelTC true` switches off; now `scripts/Replay.lean`;
* the link between a registered tree and its normal form: `Meta.reduce` in the script until the
  final audits, now the kernel (`theorem _ : tree = nf := Eq.refl _`, checked at every run of the
  lint);
* the emitter (`NLAlibTools/NumPy.lean`), the only remaining trusted link between a registered
  tree and the code a reader runs (G50);
* the target lint's own tools: `sha256sum` (or `shasum -a 256`) and the parser of the TOML subset
  the registry is written in (`parseRegistry`);
* the pins: until the final audits the registry pinned the toolchain and the Mathlib revision but
  not the rest of `lake-manifest.json` (Batteries, Aesop, Qq, …) or `lakefile.toml` (the options
  every file is built with); now their SHA-256;
* G17's audit item: the declared buffers are not counted in bit memory (`inputState` sets `curW`
  and `peakW` to $0$), harmless while every interpretation has width $0$;
* G57's maintainer layer (Q3), which is a plan until `docs/targets.approved` exists and branch
  protection with code-owner review is on: until then the approval item of the lint fails on
  every branch, and nothing but review stops a merge.

Out of the base, where they were before: the PHOAS `Stmt`, `Builder` and `exec` (no target
reaches them); `ProgFamily` and `ProgFamily.inst`; program substitution (`Stmt.subst`,
`Stmt.substOracle`); the compiler and `toStmt`; certificates, kernel specifications and every
proof. Mathlib's notions (`Matrix`, `Finsupp`, `Measure.infinitePi`, `HasLaw`, `gaussianReal`,
`Measure.real`) are read as Mathlib's. The audit's smaller items are each recorded above (G17,
G20, G21, G25).

### F11. Migration

Every existing proof carries over unchanged. The realisations, the kernel specifications, the
certificates and the substitution theorem stay statements about `exec` on the builder's
statement, reached through the bridge and the `rfl` instantiation equations. Rework is limited to
the sparse instantiation (F5), the fixtures and the scripts. Three steps, with disjoint files; B
and C run in parallel after A.

**Step A: the core** (one agent; about 600 lines, all elaborated in the scratch file):
1. `Computation/Syntax.lean` (+110): `IExp.subst`, `IExp.evalIn`, `Cell.subst`, `Instr.subst`,
   `Arg.subst`, `FStmt`, `Prog`; the `whileFuel` docstring corrected. `IExp.eval_subst` goes to
   `Exec.lean`, next to `IExp.eval`. Mechanical.
2. `Computation/Compile.lean` (new, about 110): `IExp.scope?`, `Cell.scope?`, `Instr.scope?`,
   `Arg.scope?`, `Stmt.compile`, `ProgFamily.compile`, `FStmt.toStmt`, `Prog.toStmt`.
   Mechanical.
3. `Computation/FirstOrder.lean` (new, about 250): `FStmt.exec`, `Prog.exec`, the bridge with its
   three congruence lemmas (proved), `Prog.RunsWithin`, `Prog.runsWithin_iff`, and the run
   invariants for `Prog.exec` (one line each through the bridge: counts grow, memory freed, shape
   kept, peaks grow, a run that charges nothing writes nothing, the oracle the only access).
   Mechanical from the scratch.
4. `Computation/Model.lean` (+80): `MatrixFree` and `StoredEntries` on `Prog`; the `ProgFamily`
   models renamed into namespace `ProgFamily`; the transfer lemmas `ProgFamily.MatrixFree.prog`,
   `ProgFamily.StoredEntries.prog`. Renames mechanical, transfer lemmas about 10 lines each.
5. `Computation/Dense.lean`, `Computation/Sparse.lean`: the composition theorems renamed into
   `ProgFamily.MatrixFree`. Mechanical.
6. `RandomMatrix/Tape.lean` (+40): `MatrixFreeProb` on `Prog`, `ProgFamily.MatrixFreeProb`, its
   transfer lemma.
7. `Computation/Exact.lean`, `Computation/Contract.lean` (about 20, Q4): `exactSem` fails on
   `lt` and `le` unless both arguments are real (`im = 0`); the comparison clauses of
   `isRelErrSem_exactSem` (for $\Bbbk = \mathbb{R}$) get a one-line proof that every real is
   real.

**Step B: the targets and their proofs** (topic files; 450 to 530 lines):
1. `Matrix/Factorizations/GramSchmidtTargets.lean` (new, about 50): `gramSchmidtCount` (moved),
   `MatrixFreeGramSchmidt`.
2. `Matrix/Factorizations/GramSchmidtProgram.lean` (+30): `gramSchmidtProg.compiled`, its `rfl`
   equation, `matrixFreeGramSchmidt`; `matrixFree_gramSchmidtProg` becomes the
   `ProgFamily`-level lemma (name kept, no result id). Mechanical.
3. `Estimation/Trace/HutchPlusPlusTargets.lean` (new, about 130): `hutchppCount` (moved), the four
   Hutch++ targets.
4. `Estimation/Trace/HutchPlusPlusProgram.lean` (+250): `hutchppProg.compiled`, the compiled dense
   program, the per-pattern sparse program, their equations, the four proofs. The three `rfl`
   equations and four proofs are mechanical (80 lines). **Rework**: the sparse compilation, an
   induction on the pattern through `List.forM` in `cooImpl` (150 to 200 lines). It moves to
   `Sparse.lean`, as a lemma about `cooImpl`, if Q1 is declined.

**Step C: checks, tools and documents** (scripts, tools and docs; about 700 written, 200
deleted):
1. `scripts/Targets.lean` (new, about 260): the lint, the normal forms of the registered trees,
   and the closure walk and hash of F1, reading `docs/targets.toml`; `--update` rewrites the
   hashes and printed statements for review. Also the Q5 check (a target whose `inputs` are not
   built from `Array.replicate` and the declared data carries the flag and the marker) and the
   approval check of Q3.
   Fixtures: an axiom of a target's type; the three cheats of audit 1 against a target; audit 2's
   `exec_copyTrace` (flagged by item 2); a target whose count is edited, one whose
   `irreducible_def` value is edited, one whose ForMathlib dependency is edited (each a hash
   change); a toolchain mismatch.
2. `docs/targets.toml` (new): the five entries of F1, the three registered trees with their
   normal-form hashes, and the pinned toolchain and Mathlib revision; `docs/targets.approved`
   (Q3); `.github/CODEOWNERS` (Q3). The hashes and printed statements are filled in after step B lands.
3. `scripts/Programs.lean` (−150, +40): E1 and the old E3 removed, E9 a warning, E4 re-pointed.
4. `scripts/AccessModelFixtures.lean` (about 60 changed): the `not_` theorems restated for the
   models on `Prog`, the fixture programs written as trees.
5. `NLAlibTools/NumPy.lean` (about 120 changed): **an emitter of `FStmt` trees** (levels printed
   as `b0, b1, …` and `i0, i1, …`, sizes as the function's parameters), so that the code emitted
   for a result is printed from the very tree the result is about. With E1 retired nothing keeps a
   builder parametric, and the current emitter instantiates the builder at `String`, a third
   instantiation that could differ from the compiled tree. The builder path is retired; the
   differential tests of §8 run on the tree emitter. The `Float` runner may keep running the
   builder for convenience, with a `#guard` that it agrees with `Prog.exec` under a `Float`
   interpretation on the §6 rows.
6. `docs/rules/rules.toml` (E1 retired, E3 and E4 rewritten, E9 a warning), the generated
   DIGEST and RULES files, docs/contributing/programs.md and §11, `scripts/stage_check.sh` (runs
   `scripts/Targets.lean`), and this note's changes sections.
7. Bookkeeping for the five moved result ids (`gram-schmidt-program`, `hutchpp-program`,
   `hutchpp-program-tail`, `hutchpp-program-dense`, `hutchpp-program-sparse`):
   the explorer metadata (each id's
   declaration, statement and file), and a rename map `docs/renames/2026-10-computation.json`
   (N12: the old instances to the target theorems).

Total about 1,750 to 1,850 lines written and 200 deleted. Not needed: a change to any proof of a
realisation or a kernel. Lanczos (stage 1b) starts from its targets: the library writes `MatrixFreeLanczos` and
`MatrixFreeLanczosBasis` first, and the proof agent receives them as fixed statements.

### F12. Decisions of the maintainer (approved 2026-10-23)

The first version of this section asked five questions, each a change of an approved decision
beyond the two changes. The maintainer decided all five the same day.

* **Q1. A uniform sparse model** (changes D14 and G34). **Decided: yes, later, as a small stage
  of its own.** With the pattern unrolled into the program, the sparse tree is a function of
  the pattern, which the target quantifies outside the model, so the program is non-uniform in
  the pattern, as D14 approved ("public, unrolled"), and has no closed normal form (F1). Making it uniform needs an
  index read: a binder `romIdx i body` that binds a new index variable to entry `i` of
  read-only index data, counted (`.romIdx p`) and counted in memory. The pattern then becomes
  data bound after the program, its storage is counted ($2\,\mathit{nnz}$ cells for COO), and
  `cooImpl` takes no host data. It is the first construct that addresses memory by a data value
  (G34's "no construct turns a cell into an index" would no longer hold), and out-of-range
  indices fail, as every access does. Two consequences to record. The `StoredEntries` model
  gains its first library-written validity predicate on data: the index data in range (entries
  below `N`). And the index data are kept apart from the values: their own `Interp` field (`romIdx`
  next to `rom`), their own count kind, and their own memory (`romIdxSize`), so that a count of
  value reads and a count of index reads stay distinguishable and both are bounded. Size about
  300 lines; it also removes step B's only non-mechanical proof and makes the sparse tree a
  registered tree. Until then, the interim target `StoredEntriesCooHutchpp` of F8.
* **Q2. Named-program targets for library results** (affects E1's stated purpose in G55, "the
  emitted NumPy is the program the result is about"). **Decided: named targets about the
  registered compiled tree**, in his words: "named for stuff in our library for now. we will just
  keep this in mind when we are setting goals for the community." So the claim and the emitted
  code are about the same tree (F1, "The registered tree"; the tree emitter of F11, step C).
  Existential targets are not used for library results; they are the future form for community
  goals (F1). The first version's alternative, existential targets with the witness checked by
  inspecting the proof term, was rejected by the review as fragile (`theorem t : T := other`, or a
  witness passed through `Exists.elim`, defeats it).
* **Q3. Who may change targets and the registry.** **Decided: changes to target definitions and to
  `docs/targets.toml` need the maintainer's approval; agents never edit `*Targets.lean` files or
  the registry.** Enforcement, in three layers, as fits this repository (GitHub, `ci.yml`):
  * `.github/CODEOWNERS` assigns `docs/targets.toml`, `docs/targets.approved` and
    `NLAlib/**/*Targets.lean` to the maintainer, and branch protection on `main` requires a
    code-owner review: no change to them merges without his approval. This is the binding layer
    (a repository setting the maintainer turns on);
  * `docs/targets.approved` holds the SHA-256 of `docs/targets.toml`, and the maintainer updates
    it in the commit that approves a registry change. `scripts/Targets.lean`, in CI on every
    branch and in `scripts/stage_check.sh`, fails if the registry's hash differs from it, and the
    closure hashes already fail on any edit of a target or of what it unfolds to. So an
    unapproved edit fails the checks on the branch where an agent made it, before any review;
  * CONTRIBUTING ("AI agents") states the rule for agents, and agent briefs list the protected paths.
  A toolchain or Mathlib bump that changes every hash is one registry diff, approved the same way,
  with the printed statements showing that no statement changed.
* **Q4. Complex comparisons** (changes `exactSem`, D2). **Decided: `lt` and `le` fail on
  incomparable values.** `exactSem` fails on `lt` and `le` unless both arguments are real, so a
  branch on an incomparable pair is a failure the proof must exclude, as division by zero is
  (step A, item 7; G21). No current program uses `lt` or `le`.
* **Q5. Declared inputs computed from the sizes** (F6, option 2). **Decided: such a target carries
  a registry flag and a docstring marker.** The flag is `precomputed = ["nodes"]` in its registry
  entry; the marker is a docstring sentence `Precomputed: the $q$ Chebyshev nodes.`;
  `scripts/Targets.lean` requires both whenever a target's `inputs` is not built from
  `Array.replicate` and the declared data alone, and the explorer shows the flag next to the
  cost. None of the five targets of F8 has such an input.

## Changes during the migration (2026-10-23)

**Step A (the core) landed** as planned in F11, with these departures, each forced by the build
or the checks:
* **`ProgFamily.compile` lives in `Computation/Model.lean`**, next to `ProgFamily`, not in
  `Computation/Compile.lean`. The import order is `Syntax`, `Compile` (the compiler of statements
  and `toStmt`), `FirstOrder` (the run, the bridge, `Prog.RunsWithin`), then `Model`, which
  defines `ProgFamily` and needs `FirstOrder` for the models on `Prog`; so `Compile` cannot see
  `ProgFamily`. `Compile.lean` holds the rest of item 2.
* **The statements of five public results changed in text, not in meaning.** The models they
  conclude were renamed into namespace `ProgFamily` (item 4), with unchanged bodies, so
  `matrixFree_gramSchmidtProg` and `matrixFree_hutchppProg` now conclude `ProgFamily.MatrixFree`,
  `matrixFreeProb_hutchppProg` concludes `ProgFamily.MatrixFreeProb`, and
  `storedEntries_substOracle_hutchppProg_denseImpl` and `…_cooImpl` conclude
  `ProgFamily.StoredEntries` (in `GramSchmidtProgram.lean` and `HutchPlusPlusProgram.lean`, step
  B's files, touched only for this and for two docstring references to the renamed composition
  theorems). The composition theorems are now `ProgFamily.MatrixFree.storedEntries_substOracle_denseImpl`
  and `…_cooImpl` (item 5), with their result ids `matrix-free-dense-substitution` and
  `matrix-free-coo-substitution` unchanged. Every result id stays on the declaration that carried
  it until step B moves the five program ids to the targets.
* **Step C's files touched so that the checks stay green**, each a few lines:
  `scripts/Programs.lean` (the models list includes the three `ProgFamily` models until step B;
  `Compile` and `FirstOrder` are theory modules; a statement mentioning `Prog.RunsWithin`, or
  `Prog.exec` or `FStmt.exec` with a measure, is about runs, so E3 covers the new forms in the
  meantime); `scripts/AccessModelFixtures.lean` (the four `not_` fixtures and `matrixFreeProb_iff`
  are stated with the `ProgFamily` models, their meaning unchanged); `scripts/check_rules.py`
  (E8 exempts `Compile.lean` and `FirstOrder.lean`, whose matches on `named` are the core's, as
  in `Exec.lean` and `Subst.lean`); docs/contributing/vocabulary.md, the access-model row, cites the renamed
  composition theorems (rule V6).
* **Q4 made**: `exactSem` fails on `lt` and `le` unless both arguments have imaginary part $0$;
  `isRelErrSem_exactSem` keeps its statement, its two comparison clauses proved by
  `RCLike.im_to_real`. No proof in the library depended on the old clauses.
* The `whileFuel` docstrings (`Stmt.whileFuel`, `FStmt.whileFuel`, `FStmt.exec`) say the run
  tests at most `fuel` times and fails if every test holds, so a successful run executes the body
  at most `fuel - 1` times (F3).
* The run invariants for programs (item 3) are the nine of `Exec.lean`, each through the bridge:
  `Prog.cnt_le_of_exec_eq_some`, `Prog.cur_eq_of_exec_eq_some`, `Prog.curW_eq_of_exec_eq_some`,
  `Prog.shape_eq_of_exec_eq_some`, `Prog.peak_le_of_exec_eq_some`,
  `Prog.peakW_le_of_exec_eq_some`, `Prog.store_eq_of_exec_eq_some_of_cnt_le`,
  `Prog.pos_eq_of_exec_eq_some_of_cnt_le`, `Prog.exec_eq_of_exec_eq_some_of_cnt_load_le`.

Sizes: `Syntax.lean` +101, `Exec.lean` +6, `Compile.lean` 139 (new), `FirstOrder.lean` 305 (new),
`Model.lean` +103, `Tape.lean` +49, `Exact.lean` and `Contract.lean` +5, `Dense.lean` +1,
`Sparse.lean` unchanged in length.

**Step C (checks, tools and documents) landed** after step B (`f571a5f`), as planned in F11, with
these departures:
* **The closure hash is SHA-256, not `mixHash`.** `mixHash` over `Expr.hash` is a 64-bit
  non-cryptographic combination, so a determined prover could search for a weakened statement with
  the registry's hash. `scripts/Targets.lean` hashes a canonical serialisation instead: every
  constant of the closure in name order, each with its kind, universe parameters, type and what
  its kind carries (F1 item 3), each distinct subterm once (equal subterms are first made
  pointer-equal, so a term with sharing serialises in linear size), binder names, binder
  annotations and metadata left out. A registered tree is hashed the same way, by its type and its
  constructor normal form; a normal form must contain no library definition outside its types and
  proofs (the three trees contain none). The SHA-256 is computed by `sha256sum` (or
  `shasum -a 256`), as for `docs/targets.approved`.
* **Item 2 of the lint follows the statement's definitions.** A `Result:` theorem is flagged when
  its statement reaches a run or a budget through the library definitions it unfolds to, not only
  when it mentions one, so `theorem t : T` for a `Prop` `T` of the prover's that unfolds to a
  model is flagged unless `T` is registered (fixture `fixUnregistered`). The Computation layer
  (`NLAlib/Computation`, whose theorems are about every program) is outside item 2.
* **Item 1 also checks the file and the conclusion**: a target is a `Prop` definition in the
  `*Targets.lean` file its entry names, and concludes a model on `Prog`; every registered tree is
  named by a target, and every tree a target lists occurs in its statement.
* **`--update` is an environment variable**, `TARGETS_UPDATE=1 lake env lean scripts/Targets.lean`
  (a script run by `lake env lean` takes no arguments); it rewrites the hashes, the printed
  statements and the pins, and never `docs/targets.approved`. `TARGETS_REGISTRY` and
  `TARGETS_APPROVED` name other files, for tests. The registry entries carry `reviewed =
  "2026-10-23"`, the date the maintainer approved the statements of F8. The maintainer's approval
  commit adds `docs/targets.approved`; until then the lint fails on its last item, as designed.
* **E4 is checked by `scripts/Programs.lean` against the registry**: every `<spec>Prog` is called
  by the definition of a tree that a registered target lists. That every target is proved is item
  1 of E3. A compiled tree is a program for E2 and not a caller for E9 (it runs its builder once,
  at the top).
* **E8 exempts theorems**: a theorem's statement or proof may mention `named` (step B's one-step
  compile equation of `cooImpl` constructs `FStmt.named`); the rule is about programs, whose named
  nodes the emitter prints as calls.
* **CI runs on every branch** (`push` without a branch filter), so that an unapproved registry
  change fails where it is made (Q3). `.github/CODEOWNERS` assigns the registry, the approval file,
  the `*Targets.lean` files and itself to `@tchen01`; branch protection is the maintainer's to
  switch on.
* **The tree emitter** (`NLAlibTools/NumPy.lean`) prints `hutchppProg.compiled` as
  `hutchpp(A, i0, i1, i2, b0)` (levels as names, the sizes and the declared buffers as parameters);
  the builder emitter is gone. Its differential test runs the emitted code under NumPy, when it is
  installed, and agrees with the Lean `Float` run of the same tree to six digits on the two §6
  rows, in both modes. The `Float` runner keeps the builder, with `#guard`s that it agrees with
  `Prog.exec` of the registered tree (output, counts and peak).
* **The access-model fixtures are trees** (`litTree`, `leakTree`, `copyTree`, `drawTree`), each
  `not_` theorem stated with the models on `Prog`.
* **Bookkeeping**: the explorer metadata has no entry for the five moved
  ids (it is generated from the extraction); the rename map
  `docs/renames/2026-10-computation.json` records the five id moves and step A's renames.

**Step B and the closing pass** added these departures:
* **The builders and the registered trees are in two new files**, `GramSchmidtProgramTree.lean`
  and `HutchPlusPlusProgramTree.lean`, upstream of the target files and of the files that prove
  them. The targets (`*Targets.lean`) must name the trees, and the proofs import the targets; with
  the trees left in `GramSchmidtProgram.lean` and `HutchPlusPlusProgram.lean` that is an import
  cycle. The proof files import the tree files and keep the results about the builders.
* **The CODEOWNERS handle `@tchen01` is a guess**, from the maintainer's repository account,
  pending his confirmation; it is a one-line change in `.github/CODEOWNERS`.
* **Reminder of the departures above that touch statements or checks**: `ProgFamily.compile` in
  `Model.lean`; the one-token `ProgFamily` renames in five statements; SHA-256 over a canonical
  serialisation in place of `mixHash`; E8 exempting theorem bodies; CI on every branch.
* **`HutchPlusPlusProgram.lean` line 1237**: a value marker began a docstring line, which
  `scripts/check_constants.py` rejects; the line is rewrapped, with no change of mathematics.

## Final audits, 2026-10-24

Two independent audits of the closed migration (branch `computation/stage1` at `0bd2567`), each
looking for a way to publish a false cost result that every check accepts. Their findings, merged,
and what was done.

**Blocking, the whole library.** In a `module` file built with `--wfail`,
`unsafe def anything.{u} (α : Sort u) : α := anything α` followed by
`set_option debug.skipKernelTC true in theorem matrixFreeHutchppForged : MatrixFreeHutchpp :=
anything _` elaborates with no warning: the elaborator does not send the theorem to the kernel,
which would reject a safe theorem using an unsafe constant. The target lint accepted it (a
theorem of the target's type) and `scripts/Audit.lean` reported only the three standard axioms,
since an unsafe definition is not an axiom. The same two lines forge any theorem of the library,
not only a target. Fixed three ways:
* **Kernel replay** (G61), `scripts/Replay.lean`: it reads the `.olean` files of every `NLAlib`
  module, all three parts of each (`.olean`, `.olean.server`, `.olean.private`, so private
  declarations and proofs are included), imports as the base the modules they import outside the
  library, and replays every constant into the base through the kernel with Lean core's
  `Environment.replay` (`lean4checker` is built on it; no new dependency). `replay` skips `unsafe`
  and `partial` constants, so the script fails on any, except the compiler's `f._unsafe_rec`, the
  `partial` copy of a safe recursive definition `f` that Lean adds for code generation (13 in the
  library), which no safe constant can use: a use fails the replay as an unknown constant. On the
  library: 11760 constants of 420 modules onto 279 base imports, 0 violations, 2 min 20 s, 5.6 GB;
  with `NLAlibTools`, 11871 constants of 424 modules, 0 violations. On the forged module (built
  outside the library): rejected, "unknown constant `anything`", and `anything` flagged; a variant
  naming the unsafe helper `helper._unsafe_rec` beside a safe `helper` is rejected the same way.
  So no earlier round contains such a forgery. CI runs it (with `NLAlibTools`), and so does
  `scripts/stage_check.sh`.
* **Rule S9** (G62): no `unsafe`, `partial`, `implemented_by`, `extern`, `set_option debug.…`, a
  kernel option or `skipKernelTC` in the code of `NLAlib/` and `NLAlibScaffold/`, and no `debug.`,
  kernel or trust option or `moreLeanArgs` in `lakefile.toml`; with fixtures. The library has none.
* **`scripts/Audit.lean`** fails on an `unsafe` or `partial` constant of an `NLAlib` module (the
  `_unsafe_rec` auxiliaries excepted, as above).

**Non-blocking.**
1. *Item 2 of the target lint did not follow constructors*: a `Result:` theorem stated through a
   structure (`structure Wrapped : Prop where h : MatrixFreeHutchpp`), `Nonempty` of one, an
   inductive `Prop` or a class instance was not flagged. `reachesRun` now walks the mutual block
   and the constructors of inductive types, as the closure walk does, and item 2 reads every
   constant of a proposition with a result id (instances included) and every definition of type
   `Prop` with a result id. Fixtures for each.
2. *Pins*: the registry pinned the toolchain and the Mathlib revision only. It now records the
   SHA-256 of `lake-manifest.json` (every dependency's revision) and of `lakefile.toml` (the options
   every file is built with) and checks them.
3. *CODEOWNERS* covered only the registry, the approval file, the `*Targets.lean` files and
   itself. It now also covers `scripts/Targets.lean`, `scripts/Audit.lean`,
   `scripts/Programs.lean`, `scripts/Replay.lean`, `scripts/stage_check.sh`, `.github/workflows/`,
   `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`. The handle `@tchen01` is still
   unconfirmed, and says so.
4. *The link between a registered tree and its normal form was `Meta.reduce`*, in the script. The
   lint now sends `theorem _ : tree = nf := Eq.refl _` to the kernel for each registered tree at
   every run (`kernelTreeEq`; fixture: a different normal form is rejected). The emitter is the
   one trusted link left between a tree and the code a reader runs.
5. *Hash brittleness*: tree normal forms kept the proofs of `Fin` bounds and of `ℚ` literals, and
   closures hashed the numbered `_proof_` auxiliaries and hygienic names
   (`NLAlib.definition._@.<module>.<hash>._hygCtx._hyg.2` of each `irreducible_def`), so unrelated
   edits changed hashes and invited rubber-stamped re-approvals. Every proof is now one token
   (`proofToken`) in the walk and in the serialisation: two terms that differ only in proofs are
   definitionally equal, and what a proof proves is fixed by the rest of the term, so the frozen
   meaning is the same; a constant used only inside proofs leaves the closure (the closures shrank
   from 172, 182, 214, 187, 241 constants to 161, 164, 184, 171, 228). Hygienic names are written
   without their macro scopes and numbered in the walk's order, which depends on the terms only: a
   bijection of the closure, so no two constants are identified. Each tree's printed normal form,
   the tree hash's input, is in the registry beside the printed statements (fixture: an edit of a
   proof keeps the hash). The registry was regenerated by the script's update mode; every hash
   changed and no printed statement did:

   | entry | before | after |
   |---|---|---|
   | tree `gramSchmidtProg.compiled` | `4d22e7f3…` | `4fed8241…` |
   | tree `hutchppProg.compiled` | `e18325ae…` | `c1d476df…` |
   | tree `hutchppProg.compiledDense` | `fc064ae8…` | `57ebf1ea…` |
   | `MatrixFreeGramSchmidt` | `9fdbc85f…` | `f4bfd4a9…` |
   | `MatrixFreeHutchpp` | `4f2a455e…` | `8389c47d…` |
   | `MatrixFreeProbHutchpp` | `64a762d1…` | `86d55a87…` |
   | `StoredEntriesDenseHutchpp` | `de87b161…` | `5405ea52…` |
   | `StoredEntriesCooHutchpp` | `36c3c747…` | `b30850f8…` |

   The new registry is not approved: `docs/targets.approved` is the maintainer's.
6. *Documents*. The docstrings of `MatrixFreeHutchpp` ("$2N(k + \ell) + 4$ cells at tag $p$
   besides the output") and `MatrixFreeGramSchmidt` say or suggest that the memory bound leaves out
   the declared buffer, but the proved bound counts it (G15, G16: the declared buffers count from
   the start). They are target files, so the rewording is a pending maintainer item;
   the statements are right. `IExp.mod` by zero returns the dividend, now
   documented at the constructor. G34 overstated "no host computation on sizes": `IExp.evalIn` and
   `litIdx` are uncounted host arithmetic on sizes (D), corrected in F10. The trusted base of F10
   gains the additions listed there: the kernel replay, `Meta.reduce` until item 4 (now the
   kernel), the emitter, `sha256sum` and the TOML subset parser, the manifest until item 2 (now
   pinned), G17, and G57's maintainer layer, a plan until `docs/targets.approved` and branch
   protection exist. New items G61 (the replay, T) and G62 (rule S9, D).

**Replay audit, 2026-10-24** (on `328eb35`). An audit of `scripts/Replay.lean` itself. The replay
trusted as its base every import outside its roots, modules built by this package included:
`NLAlibScaffold` in CI and `NLAlibTools` locally (the stage check ran with the default root
`NLAlib`). Fixture FxA, an honest module importing FxBase, whose theorem `1 = 2` was added with
`env.addDeclCore … (doCheck := false)` (no `set_option`, no `unsafe`, no axiom), replayed with 0
violations. In the library, a lemma forged that way in `NLAlibScaffold` and reached by `NLAlib`
through an `NLAlibTools` import passed every check: P3 reads direct `NLAlibScaffold` imports only,
nothing forbade importing `NLAlibTools`, S9's pattern missed the `doCheck := false` form, and
`scripts/Audit.lean` sees no axiom. Blocking; fixed four ways:
1. *The base is trusted by location.* After computing the base, the replay resolves every module
   of its import closure through the search path (`findOLean`, as `importModules` does) and fails
   unless the `.olean` lies under `.lake/packages/` of the working directory (the dependencies) or
   under the running toolchain's `lib/lean`; the package's own `.lake/build` is never trusted.
   FxA now fails ("1 base modules are read from outside the dependencies … and the toolchain …:
   FxBase (read from …)"); a replay rooted at `NLAlibTools` alone fails on the 215 `NLAlib`
   modules it would read from `.lake/build`.
2. *Every library is replayed.* The roots are every `lean_lib` of `lakefile.toml`, read by the
   script (a library setting `roots` or `globs` is refused); `REPLAY_ROOTS` only serves fixtures.
   Strict are `NLAlib` and, recursively, every library one of its modules imports: there an
   `unsafe` or `partial` constant is an error (the `_unsafe_rec` auxiliaries excepted).
3. *The stage check replays as CI does*: both run the script with no environment variables, after
   building `NLAlib`, `NLAlibScaffold` and `NLAlibTools`.
4. *Rule P12*: an `NLAlib` file, the root `NLAlib.lean` included, imports no other `lean_lib` of
   `lakefile.toml` (`NLAlibTools`, `NLAlibScaffold`, or one added later), with fixtures; P3 stays
   as the scaffold rule. S9 also matches `addDeclCore`, `addDeclWithoutChecking` and `doCheck`.

Non-blocking, all done:
* (a) *Axioms in strict libraries.* In a strict module the replay also fails on an axiom and on a
  constant whose type or value uses `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat` or
  `Lean.trustCompiler`, as defence in depth beside `scripts/Audit.lean` (which follows axioms
  through every dependency). At this toolchain `native_decide` adds an auxiliary axiom
  (`….nd._native.native_decide.ax_1_1`), which is caught as an axiom; elsewhere these are counted
  (2 in `NLAlibTools`, which uses `sorry`).
* (b) *Freshness.* The script read whatever `.olean` files it found. Lake at this toolchain has
  `lake build --no-build` (exit code 3 when a target is out of date) and `--rehash` (hash every
  file instead of trusting Lake's `.hash` files); CI and the stage check run
  `lake build --no-build --rehash NLAlib NLAlibScaffold NLAlibTools` just before the replay.
  Tested: a byte appended to `NLAlibTools/Float.olean` is caught through its dependents (plain
  `--no-build` misses it); a change of a module nothing depends on, such as the root
  `NLAlib.olean`, is not, since Lake does not compare an output with the hash its trace records,
  but the replay still kernel-checks what that file contains. In CI, lean-action runs with
  `use-github-cache: false`: no `.lake` is restored from the GitHub cache, so the package is built
  from its sources at every run (Mathlib's `.olean` files still come from `lake exe cache get`,
  under `.lake/packages`, in the trusted base). Chosen over rebuilding unconditionally after the
  restore: the same build without downloading the cache first, and sound, since a restored
  `.lake` could hold outputs whose traces match the sources while their contents do not.
  **Build reuse update (2026-11-14).** The cold-build-only CI policy above is replaced by
  provenance-checked build reuse, described in [CI build reuse](../contributing/checks.md#ci-build-reuse).
  Generic GitHub `.lake` caches remain disabled. Only immutable artifacts from completed,
  successful main-push CI runs can supply outputs; their recorded revision, compatibility and
  archive digest are verified before restore. Lake rehashes inputs and rebuilds changes and
  dependents, then every audit and the full replay still run. The trusted producer and immutable
  artifact bind restored output bytes to the recorded source, addressing the trace-only gap
  above without skipping the replay or trusting PR-produced build outputs.
* (c) `scripts/stage_check.sh` runs `lake exe mk_all --lib NLAlib --check`, so no `NLAlib` module
  is unreachable from `NLAlib.lean`, hence unreplayed and unaudited (CI already did).
* (d) The docstrings say that a hand-named `partial` `f._unsafe_rec` beside a safe `f` is counted
  as an auxiliary, and is harmless: any use of it fails the replay as an unknown constant (FxD).

The auditor's fixtures are now `scripts/replay_fixtures/` (seven modules) with
`scripts/replay_fixtures.sh`, run by CI and the stage check and covered by CODEOWNERS; each is compiled into a temporary
directory and replayed alone, and must fail for its own reason: FxA (base read from outside the
dependencies), FxBase and FxB (the kernel: declaration type mismatch), FxC (an `unsafe` constant;
the kernel: unknown constant), FxD (the kernel: unknown constant `helper._unsafe_rec`), FxE and
FxF (an axiom); FxF, not strict, passes with 0 violations. On the package: 11871 constants of 425
modules under `NLAlib`, `NLAlibScaffold` and `NLAlibTools` (strict: `NLAlib`) onto 280 base
imports (5118 modules, all from the dependencies or the toolchain), 15 auxiliaries `_unsafe_rec`,
0 violations.
