# A program logic for runs: specifications that compose by fixed rules

> **Earlier design.** This note records an earlier design of the operations core and keeps its
> vocabulary (`Impl.Meets`, `Impl.Triple`, `Impl.program`, `opsImpl%`, `cert_intro`,
> `Interp.Meets`), much of which has since been replaced. The current vocabulary is described in
> `NLAlib/Ops/README.md`.

2026-11-08. Design note; **status: reviewed, approve with changes (Fable,
`reports/Review-Fable-ProgLogic-Design.md`; the COMPDYN session, owner of S2,
`reports/Review-COMPDYN-ProgLogic.md`); the changes are applied in this revision (§12)**. Branch
`design/prog-logic` from `origin/main` @ `7cbea9d1`. Decision sheet: harness
`state/decisions/PROG-LOGIC.json` (ids PG1–PG9 below). Targets: harness
`pilot/prog-logic-targets.json` (ids PL1–PL110, provable statements and two re-proofs); jobs:
harness `pilot/prog-logic-jobs.json` (J1–J9, the pilot gate and the S2/W4 migration). Scaffold:
`NLAlibScaffold/Computation/ProgramLogic.lean`,
`NLAlibScaffold/Matrix/Computation/ProgramLogicKernels.lean`,
`NLAlibScaffold/Matrix/Computation/SpectralBisectionProgramTreeSpec.lean`,
`NLAlibScaffold/Matrix/Computation/SpectralBisectionNode/CompressSpec.lean`. This note extends
`docs/design/Computation-CertifiedRoutines.md` (CERT-ROUTINES); it does not replace it.

The maintainer's goal (2026-11-08): "this stuff should all be written in a modular, reusable
way. We should go back through S2 to clean it up ... I somehow feel like the hard part should be
figuring out the math, and then the program bit is procedural as long as nothing is broken."

The design goal follows from it. Once the mathematics of a routine is proved, its program proof
is routine. It composes the specifications of the sub-routines by fixed rules. It does not unfold
another routine, thread a frame chain by hand or repeat distinctness bookkeeping. The rules must
be easy enough to apply that a small prover model does program proofs reliably.

## Summary

* **What it costs today (§1).** The S2 program proofs of `NLAlib.eighProg` are about 12,500
  lines of run-walking in 25 files. Every block is walked twice: once for success
  (`exists_exec_*`, in `*Success.lean` files) and once for correctness (`holds_of_exec_*`). Each
  walk splits `exec_seq` by hand, `change`s the goal into the unfolded statement tree, splits
  distinctness facts out of `Nodup` lists, and chains read-unchanged facts across the steps.
  There is no general Hoare or weakest-precondition layer on main. `EighWeight.Triple` is one,
  but it is specific to eigh and covers the cost only. CERT-ROUTINES' `IsBlockRoutine.bind`
  composes footprints only.
* **Choice (§2, PG1).** The logic has three parts:
  * a **weakest precondition `Wp` by definition**, since `exec` is deterministic and
    `Option`-valued, so it needs no inductive judgement and no soundness proof;
  * **relational Hoare triples** stated with it, for routine specifications;
  * a **block-level frame rule** in place of a separation logic.

  Every rule is a three- to ten-line consequence of a run equation of `Exec.lean`. The logic has
  **two modes**, `total` and `liberal`. One specification proved for every mode yields both of
  S2's lemmas: refinement and success. Success-only hypotheses go under `m.Needs` in the
  precondition; correctness-only hypotheses guard the value clause of the postcondition (PG2).
* **The specification (§3).** `Spec m I pre s fp post` is a triple whose postcondition also says
  `Modifies fp st.store st'.store`: same shape, and every cell disjoint from the blocks `fp` reads
  the same. `RoutineSpec` adds `ExecutionComposable` for builders. Footprints use one canonical
  block form, `matBlock`. Counts are optional clauses: `Costs` (exact) and `CostsLe` (a weighted
  bound, for EP7). Both thread additively. Budgets come from the static cost of the compiled
  tree, as CERT-ROUTINES CR7 decided. The arithmetic assumptions are two records,
  `IsControlExactSem` (indices, flags, `≤`) and `IsRoutineSem` (that plus the standard model).
  Handles are relative to the size of the store, which the precondition fixes.
* **Rules (§4).** The scaffold has 108 sorried statements and 7 one-line proofs; it builds:
  * footprints, read sets and canonical blocks (24);
  * modes, with the `Mode.Needs` algebra (9, of which 5 are proved);
  * application, consequence and the mode bridges (7);
  * statement rules (9);
  * the six instruction specifications and the draw loop (7);
  * invariant rules, scoped scratch, and allocation states (7);
  * builder rules (10);
  * specification rules (21), including:
    * seq, frame, ite and two-armed ite;
    * loop with per-iteration footprints;
    * `bindIdx`;
    * alloc by named states;
    * the call rule;
    * `RoutineSpec.stmt` and `RoutineSpec.ins`;
    * transport across run equivalence and index normal forms;
  * counts (9);
  * a budget bridge (1);
  * certificate and kernel bridges, with the arithmetic records (5);
  * the S2 `eighWhen` rule (1);
  * the pilot's four statements and the gate-3 statement (Split's scratch prefix).

  Tactics: `spec_step`, `spec_call` and `fp_omega [facts]`. The last normalises products, so
  `r * k` and `k * r` are one atom. It was tested on the S2 goals that plain `omega` fails (§5).
* **Migration (§7).** Pilot: `NLAlib.eighCompressBlock`. Both of its lemmas are re-derived, with
  statements unchanged, from one mode-generic specification. Gate (job J1):
  * the two walks, 180 lines, become the specification plus two corollaries, at most 90 lines;
  * the net diff is reported, with moved text excluded;
  * Split's eight-alloc prefix is proved by named states with default heartbeats.

  The estimate for all of S2 is **2,350–3,255 fewer lines (19–26%)**. A complete fold of the
  `*Success.lean` files would give about 4,000. CGS2 and Lanczos-reorth are second consumers,
  about 500 lines. **No registered target statement changes**, and no re-pin is needed.
* **Who (PG9, as the COMPDYN session proposed).** The COMPDYN/S2 session builds W0–W3 in one
  builder lane. This pipeline reviews the W0–W1 statements and keeps the note and the sheet. W4
  splits by owner: the EIGH weight goes to COMPDYN, CGS2 and Lanczos-reorth to the reorth owner.

## 1. Motivation: what S2's program proofs cost

Inventory of `origin/main` @ `7cbea9d1`. Proof lengths are in lines; nd/ne/nm/fr are rough match
counts inside a proof (`Nodup`, `≠`, `∉`, read-equality facts).

### 1.1 The blocks and their lemmas

The blocks are `Builder` definitions in `Matrix/Computation/SpectralBisectionProgramTree.lean`:
Sign :99, Leaf :123, Child :134, Deflate :146, Compress :163, Split :178, Clamp :206, Node :228,
DownLevel :278, BottomLevel :309, UpLevel :322, `eighProg` :373, `eighProg.compiled` :414.

| block | success (`exists_exec_*`) | correctness (`holds_of_exec_*`) | nd/ne/nm/fr |
|---|---|---|---|
| Sign | SignStep:708 (50) + Body:604 (104), Tail:532 (72), Step:420 (61) | SignStep:343 (77), Body:243 (100), Step:43 (60) | 0/25/0/6; 0/25/0/11 |
| Leaf | DownLevelSuccess:176 (59) | Deflate:139 (75) | 0/2/0/3; 0/9/1/6 |
| Child | NodeSuccess:88 (67) | Deflate:236 (64) | –; 0/0/0/2 |
| Deflate | Deflate:724 (17) + `_facts`:624 (100) | Deflate:419 (99) | 2/2/5/7; 2/1/4/11 |
| **Compress** | Compress:381 (96) | Compress:91 (84) | 2/5/4/14; 2/4/5/21 |
| Split | SplitSuccess:605 (23) + `_ex`:505 (100), Mid:338 (120), Tail:246 (86) | Split:667 (63) + `_frame`:551 (116), body:359 (121) | 11/7/12/7; 7/8/6/7 |
| Clamp | `exec_eighClampBlock_bind` Clamp:96 (75) + `_lits`:51 (45), both jobs | same | 0/10/0/3 |
| Node | NodeSuccess:859 (76), setup:723 (107), branch:291/197 | Node:749 (56) + `_frame`:632 (117), branch:221 (95), setup:448 (93) | 3/0/4/4; 4/2/2/6 |
| Down slot | DownLevelSuccess:344 (77), :476 (114) | DownSlot:721 (114) | –; 1/11/1/17 |
| DownLevel | DownLevelSuccess:834 (101) + `_slots`, `_window`, `_tol` | DownLevel:710 (32) + :605 (105), :329 (108) | 2/10/2/30; 1/3/0/3 |
| BottomLevel | BottomLevel:251 (87) | BottomLevel:189 (44) | 1/0/1/2; 0/0/0/6 |
| Up shift/split/node/slot | UpLevelSuccess:83/193/284/373 (54/91/89/60) | UpSlot:218/333/677/800 (57/77/100/83) | 2/6/1/13; 2/9/1/11 |
| UpLevel | UpLevelSuccess:433 (81) | UpLevel:155 (82) | 0/6/1/8; 0/5/1/8 |
| driver | Program: DownLoop:147 (103), UpLoop:250 (62), Passes:312 (97), Body:649 (97), `exists_exec_eighProg`:759 (50) | Refinement: :44 (105), :149 (66), :405 (76), :499 (79), `holds_of_exec_eighProg`:653 (81) | 1/13/6/13; 7/5/7/19 |

File sizes: the `SpectralBisectionNode/` files (Compress 476, Deflate 740, NodeSuccess 934,
SignStep 757, Split 729, SplitSuccess 627, Setup 540) with `SpectralBisectionNode.lean` 804 come
to 5,607 lines. The walks of `SpectralBisectionProgram/` (DownLevelSuccess 934, UpSlot 882,
DownSlot 834, DownLevel 741, Refinement 733, UpLevelSuccess 513, BottomLevel 337, Levels 327,
UpLevel 236, Transfer 366) with `SpectralBisectionProgram.lean` 874 come to 6,777 lines.
`SpectralBisectionClamp.lean` is 170. The walks total about 12,550 lines. The cost side is
separate: FrameRules 966, Weight 727, Count 731, CountTree 470.

The counts EP6 and EP7 (`docs/design/Computation-EighProgram.md`) are proved separately.
`eighProg.cnt_le_of_exec_compiled` (Count:702) uses the static cost.
`eighProg.weight_le_of_exec_compiled` (Weight:710) uses `EighWeight.Triple`: a partial,
cost-and-one-buffer Hoare triple with generic rules (FrameRules:97–239) and a CPS
`BuilderFrame` family (:381–760).

### 1.2 One block in detail: `eighCompressBlock`

The block is five statements: a conjugate transpose, two product kernel calls, an average and a
shift. `exists_exec_eighCompressBlock` (Compress.lean:381–476) spends its 96 lines as follows:

1. 15 distinctness facts split out of `[Qa, Ma, Qh, C1, C2, C3].Nodup` and 8 more out of
   `hcells`, by a `simp only … at` and two `obtain` patterns.
2. Shapes of the four scratch buffers destructured from `∀ X ∈ […], ∃ len, …`.
3. For each of the five steps, a private success lemma (`compress_exists_zconjTranspose`,
   `compress_exists_kcall`, …; the private helpers are 206 lines, :175–:380, in the same file). Each step is then *also* run through
   the corresponding correctness lemma (`holds_of_exec_zconjTranspose` …), because the next step
   needs the values. The machine parameters are instantiated with dummies (`toNat := fun _ => 0`,
   …) only to satisfy the correctness lemma's signature.
4. A `change` of the goal into the unfolded tree
   `.seq (.named _ _ _) (.seq (.kcall …) …)`, then `exec_seq`/`Option.bind` splitting with
   `Option.exists_bind_eq_some_of_exists`.
5. Hand chains of read-unchanged facts across the steps, such as
   `hkeep : … (hfr₃ …).trans ((hfr₂ …).trans (hfr₁ …))`, used for each cell a later step reads.

`holds_of_exec_eighCompressBlock` (84 lines) walks the same tree again with steps 1, 4 and 5 and
the correctness lemmas. Its frame conclusion (`∀ q b i, b ∉ […] → blockDisjoint … → read =`) is a
five-link `rw` chain.

None of this is mathematics. Each line restates a fact that a rule could carry. The success lemma
calls the correctness lemma to learn the values, so the two walks are one walk done twice.

### 1.3 What the library has, and why it does not suffice

* `exec` (Exec.lean:343) has one-step equations `exec_seq`, `exec_loop`, `exec_bindIdx`,
  `exec_alloc`, `exec_ite`, `exec_instr`, `exec_kcall` (KernelCall:73) and the
  `exists_of_exec_seq_*` inversions (Loops.lean). There is no notion of a specification.
* `Stmt.named` is a label (Syntax.lean:251). The only black box is `kcall`. An in-model routine
  is reused by re-walking it, or by its two lemmas, whose hypotheses name absolute buffer
  numbers.
* `alloc` binds handle `st.store.size` (Exec.lean:368). Lemmas take absolute numbers plus
  `Nodup` hypotheses instead of numbers relative to a base.
* CERT-ROUTINES (`RoutineFrames.lean`, 582 lines) gives the footprint layer: `IsBlockRoutine`,
  `IsBlockRoutine.bind`, `IsFramed`, `ReadsDecoded`, `Writable` and the `writeBlocks` algebra. Its
  `.bind` composes footprints only: the precondition of the second routine must already hold on
  the initial store (`hpre : ∀ s, pre₁ s → pre₂ s`), so routine 1's output cannot feed routine 2.
  `IsFramed` reads whole buffers, which is too coarse for a block that reads `Ma` at `mo` and
  writes `Ma` at `co`. The note itself (§8.3 item 2) reports that `IsFramed` cannot express the
  Lanczos-FRO frame. Of `RoutineFrames.lean`, the eigh proofs use only `blockDisjoint_iff`.
* Duplicated helpers re-prove library run lemmas locally (inventory):
  * five alloc inversions (Split:489, :506, SpectralBisectionNode:576, Transfer:193,
    SplitSuccess:38);
  * a seq inversion (DownSlot:41 ≡ `exec_seq_of_exec_eq_some`);
  * seq-instr success (Program:409/419/429, DownLevelSuccess:45/55 ≡ `exec_seq_instr_*`);
  * loop 0/1 (four files);
  * loop shape/read (seven lemmas);
  * loop success (four lemmas ≡ `exists_exec_loop_eq_some_of_forall`);
  * bindIdx (two lemmas ≡ `exec_bindIdx_of_read`);
  * in Krylov, `exec_scope_of_exec_eq_some` ×2, `exec_exact_step`/`exec_exact_loop` ×3 and
    `exec_rounded_compiled` ×5.

### 1.4 Lessons from S2 (COMPDYN session, owner of S2)

L1 `bindIdx` is strict since HARDENING (PR #70): a rule must yield `k ≤ bound` as a fact and
require it only for success. L2 Specifications carry the size of the store (`st.store.size = b`)
and how scoped allocation grows it. L3 Frames ran into `maxHeartbeats` until reads went through a
*named state*: goals must mention named states, not push chains. L4 Counts were the most
duplicated work (EP6/EP7): thread them additively, charge-agnostically. L5 Rule E8: no
`Stmt.named` construction outside `NAMED_FILES`. L6 One public home for duplicated helpers. L7
The compiled tree needs `maxRecDepth` for `rfl`. L8 Bundle the index and literal assumptions in
one record. The design answers each of these:
* L1: §4.2 (`wp_bindIdx_of_read`) and §4.7 (`Spec.bindIdx_of_read`).
* L2: §3.4 (`Triple.alloc`, `Spec.allocBind`).
* L3: §4.1, the application rule, for calls; §4.7, named-state allocation, for alloc chains.
* L4: §3.5 (`Costs`, `CostsLe`, `Spec.withCharge` in both modes).
* L5: §6.
* L6: §7.5.
* L7: §7.4.
* L8: §3.3 (`IsControlExactSem`, `IsRoutineSem`).

The reviews added tape positions (§4.7), nonlinear footprints (§5) and correctness-only
hypotheses (§2.2).

## 2. Design options and the choice

### 2.1 The options

| | (A) wp by definition + triples | (B) Hoare triples as primitives | (C) separation logic | (D) Lean core `Std.Do` / `mvcgen` | (E) generalize `EighWeight.Triple` |
|---|---|---|---|---|---|
| what | `Wp m I s Q st := m.Sat Q (exec I s st)`; triples defined from it; frame by `Modifies` | inductive or axiomatic triple judgement with a soundness proof | heap assertions, `∗`, the frame rule as primitive | reflect `exec` as `StateT St Option`, use `Std.Do.Triple`, `@[spec]`, `mvcgen` | add values and success to the existing cost triple |
| cost to prove the rules | lowest: each rule is an equation of `exec` (3–10 lines), no soundness | soundness induction over `Stmt` (L–H) | assertion algebra over `Store`, plus soundness (H) | monadic re-presentation of `exec` and an equivalence proof (H); the API changes between Lean releases | medium; triples stay partial and per-buffer |
| weak-model use | `rw [wp_seq]; refine h.wp_of …; intro st₁ …`, each step one call, named states | same once proved | needs `∗` reasoning; heavy for small models | `mvcgen` automates VCs, but VCs are about unfolded `exec` terms | per-buffer frames multiply |
| frames, disjointness | block footprints, `blockDisjoint` → `omega` | same | ideal in principle; blocks in one flat array of arrays need fractional blocks | none built in | one buffer only |
| fits `exec`, `ExecCharge`, `StaticCost`, `RunsWithin` | directly (§3.5–3.6) | directly | needs adapters | needs a bridge for each | cost only |

### 2.2 Choice

**(A)**, with a small frame rule (`Spec.frame`) in place of a separation logic. The reasons:

1. `exec` is a deterministic function into `Option`. So its weakest precondition is a definition,
   and every rule is an `iff` or implication between `Option.bind` terms. There is no soundness
   theorem to prove, nothing can be unsound, and each rule is S. This is how Bedrock2 (Erbsen et
   al. 2021) states its program logic: a weakest-precondition function computed from the
   semantics, with `straightline` tactics on top. `Std.Do` in Lean core also defines `Triple`
   from `wp` (`Std/Do/Triple/Basic.lean`).
2. A proof is a sequence of rule applications. Each application introduces the *next state as a
   named variable* with the routine's postcondition as hypotheses (§4.1). This answers L3
   directly: no goal ever contains a store push chain or an unfolded tree.
3. A separation logic would make disjointness primitive. Here the store is an array of buffers,
   and S2's operands are blocks inside a shared buffer (`Ma` at `mo` and at `co`, `Qa` at `qo` and
   `qo + 2kk_+`). Points-to assertions for that need offsets anyway. Block footprints with
   `blockDisjoint_iff` reduce every disjointness goal to linear arithmetic, which `omega` closes.
   The frame rule (Reynolds 2002; O'Hearn, Reynolds and Yang 2001) survives as one lemma,
   `Spec.frame`, over predicates that read only some blocks (`ReadsOnly`). That covers the "small
   axioms + frame" style without an assertion language.
4. (D) is attractive for its automation, but our programs are a deep embedding interpreted by
   `exec`, not shallow monadic code. `mvcgen` would generate verification conditions over
   unfolded `exec` terms, which is the cost we remove. We port its idea instead: specifications
   are lemmas applied by a tactic (§5).

**Mode-generic specifications (PG2).** S2 deliberately splits correctness (refinement for *every*
semantics, `holds_of_exec_*`, no `IsRelErrSem`) from success (under the standard model). The
target proof consumes both. A total triple under `IsRelErrSem` would force that hypothesis onto
about 40 refinement lemmas. Two separate calculi would double the walks again. So the logic has a
mode `m : Mode` (`total | liberal`) and a requirement former `m.Needs A`, which is `A` at
`total` and `True` at `liberal`. A specification is proved once, for every `m`, with success-only
hypotheses wrapped in `m.Needs`. At `liberal` it is the refinement lemma; at `total` it is
success plus the same postcondition. Leaf rules carry `m.Needs` exactly where success needs
something (`wp_bindIdx_of_read`: `m.Needs (k ≤ bound)`; `Triple.whileFuel`: fuel). Every other
rule is mode-generic and proved once by `cases m` (S). A mode-generic proof never splits on the
mode: it passes requirements on with `Mode.needs_and`, `Mode.Needs.mono` and `Mode.Needs.elim`.

**Correctness-only hypotheses.** The reverse case also occurs: a hypothesis needed for the value,
not for success. In `eighCompressBlock`, the cells `two` and `sg` must lie outside the output
block for the value to be right, but the shift succeeds wherever its cell is
(Compress.lean:264). `exists_exec_eighCompressBlock` (:381) does not assume it. Such a hypothesis
**guards the value clause of the postcondition** (`A → Q`), not the precondition. Then the total
instance needs nothing new, and the liberal corollary discharges the guard. The rule:

* success-only hypotheses go under `m.Needs` in `pre`;
* correctness-only hypotheses go as guards in `post`;
* everything else is a plain hypothesis.

The certificate bridges are total-only, because a certificate asserts success. A mode-generic
proof uses them at `liberal` through `Triple.liberal`, and then their preconditions (writability
included) must be proved in both modes.

## 3. The objects

All in namespace `NLAlib.Computation`, final home `NLAlib/Computation/ProgramLogic.lean` (one
file; Exec.lean is 1,158 lines and stays the semantics). Exact Lean statements are in the
scaffold. The definitions are given here verbatim.

### 3.1 Footprints and read sets

```lean
def Modifies (fp : List (ℕ × ℕ × ℕ)) (s s' : Store P K) : Prop :=
  s'.shape = s.shape ∧
    ∀ q b i, (∀ x ∈ fp, blockDisjoint (b, i, 1) x = true) → s'.read q b i = s.read q b i

def ReadsOnly (F : Store P K → Prop) (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ s s', F s → (∀ x ∈ rs, s'.shape[x.1]? = s.shape[x.1]?) →
    (∀ q, ∀ x ∈ rs, ∀ j < x.2.2, s'.read q x.1 (x.2.1 + j) = s.read q x.1 (x.2.1 + j)) → F s'

def BlocksDisjoint (rs fp : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ x ∈ rs, ∀ y ∈ fp, blockDisjoint x y = true
```

`Modifies` is the frame style of the kernel contracts (`IsMatMulKernel.holds_of_kcallStore_eq_some`
concludes `∀ q b' i, blockDisjoint (b', i, 1) c = true → read = read`) and of every S2 lemma. It is
not CERT-ROUTINES' `writeBlocks` equation. Partially written, uninitialized scratch (S2's
`Qh, C1, C2, C3` at `2n²` cells, written on `2rk`) is not a block write of the start store:
`writeBlock` writes `some`, and the unwritten cells stay `none`. `Modifies.of_writeBlocks` bridges
the two. `ReadsOnly` is the block analogue of `IsFramed`. It separates shape dependence (only the
read buffers' shape entries) from value dependence (only the read cells). That is the
distinction CERT-ROUTINES §8.3 item 2 found missing.

### 3.2 Modes, the weakest precondition, triples

```lean
inductive Mode where
  | total
  | liberal

def Mode.Needs : Mode → Prop → Prop
  | .total, A => A
  | .liberal, _ => True

def Mode.Sat {α : Type} : Mode → (α → Prop) → Option α → Prop
  | .total, Q, o => ∃ x, o = some x ∧ Q x
  | .liberal, Q, o => ∀ x, o = some x → Q x

def St.addCnt (st : St P K C) (c : C) : St P K C := { st with cnt := st.cnt + c }

def Wp (m : Mode) (I : Interp P ι K C) (s : Stmt P ι ℕ ℕ) (Q : St P K C → Prop)
    (st : St P K C) : Prop :=
  m.Sat Q (exec I s st)

def Triple (m : Mode) (I : Interp P ι K C) (pre : St P K C → Prop) (s : Stmt P ι ℕ ℕ)
    (post : St P K C → St P K C → Prop) : Prop :=
  ∀ st, pre st → Wp m I s (post st) st
```

Postconditions are relations between the start and the final state. Frames, counts, the size of
the store and the tape positions are then stated against the start state with no ghost
variables. Ghost values (the stored matrix, the cell values) are ordinary universally quantified
parameters of the specification lemma.

### 3.3 The arithmetic records (L8)

In the Matrix layer, next to `ScalarSem.DecidesFlags` (`Matrix/Computation/InterpMachine.lean`):

```lean
structure IsControlExactSem (dec : P → K → ℝ) (B : ℕ) (sem : ScalarSem P K) (p : P) : Prop where
  index : IsIndexExactSem dec B sem
  flags : sem.DecidesFlags p
  cmp_le : ∀ x y : K, sem.cmp p .le x y = some (decide (dec p x ≤ dec p y))

structure IsRoutineSem (u : P → ℝ) (dec : P → K → ℝ) (safe : P → ℝ → Prop) (B : ℕ)
    (sem : ScalarSem P K) (p : P) : Prop where
  relErr : IsRelErrSem u dec safe sem
  control : IsControlExactSem dec B sem p
```

`IsControlExactSem.mono` lowers the literal bound: node lemmas need literals up to `k ≤ n`, the
program up to `n + 4`. It bundles what S2's refinement threads by hand in both modes: `hflag`,
`hcmp`, `hlit`, `htn` (Refinement.lean:652–655, DownLevel.lean:466–470). It does not assume the
standard model, which liberal lemmas must not assume. A mode-generic specification takes
`m.Needs (IsRelErrSem u dec safe I.sem)` and `IsControlExactSem` unwrapped. `safe` is a
parameter, so the specifications survive F3 step 2 (bounded formats, success on the
good-sample event) without being rewritten (§7.2).

### 3.4 Specifications, relative handles and scratch

```lean
def Spec (m : Mode) (I : Interp P ι K C) (pre : St P K C → Prop) (s : Stmt P ι ℕ ℕ)
    (fp : List (ℕ × ℕ × ℕ)) (post : St P K C → St P K C → Prop) : Prop :=
  Triple m I pre s fun st st' => Modifies fp st.store st'.store ∧ post st st'

structure RoutineSpec (m : Mode) (I : Interp P ι K C) (pre : St P K C → Prop)
    (r : Builder P ι ℕ ℕ Unit) (fp : List (ℕ × ℕ × ℕ)) (post : St P K C → St P K C → Prop) :
    Prop where
  composable : ExecutionComposable I r
  spec : Spec m I pre r.run fp post
```

These fields cover the brief:

* **Success.** In mode `total`.
* **Correctness.** `post`.
* **Frame.** `Modifies fp`, which includes the shape, so the size of the store is kept (L2).
* **Count.** An optional clause in `post` (§3.5).
* **Operand blocks.** A specification names its inputs as blocks of read predicates. Its
  footprint `fp` names its outputs and its scratch. Distinctness is stated at block level
  (CERT-ROUTINES CR4 a).
* **Scratch the routine allocates.** Its handles are relative: `Spec.alloc` fixes the handle as
  `b` with `hb : ∀ st, pre st → st.store.size = b`. Every operand of the caller is a block of a
  buffer below `b` (`Writable.lt_size`). So the eight scratch buffers of `eighSplitBlock` are
  `b, b+1, …, b+7`, and their disjointness from each other and from the operands is `omega`. No
  `Nodup` list appears.
* **Scratch the caller passes and reuses (SG6).** `eighCompressBlock` is called twice on the
  same `Qh, C1, C2, C3`. The scratch blocks are part of the footprint, with no postcondition on
  their contents. A second call needs only `Writable` of them. `Writable.of_modifies` keeps it
  through the first call by `Modifies`' shape clause. The frame rule does not apply here: its
  `BlocksDisjoint` side goal is false for a block that was just written.
* **Canonical blocks.** `matBlock b off rows cols width := (b, off, rows * cols * width)` is the
  footprint form of a stored matrix in every kernel and routine specification
  (`readsOnly_entryLayoutHolds`, `IsMatMulKernel.spec_kcall`, the adapters, the pilot). Equal
  blocks are then syntactically equal (`Modifies.mono` membership is syntactic). The layout
  lemmas are `blockDisjoint_of_fst_ne` (different buffers), `blockDisjoint_of_add_le` (packed
  one after another) and `matBlock_comm`. S2's own layout bounds (`eighSplit_bounds_split`,
  `eighLoc_bounds`, Levels.lean:195/:318) supply the linear facts `fp_omega` takes.

### 3.5 Counts (L4) and charges

```lean
def Costs (c : C) (st st' : St P K C) : Prop := st'.cnt = st.cnt + c
```

`Costs.trans : Costs c₁ st st₁ → Costs c₂ st₁ st₂ → Costs (c₁ + c₂) st st₂` holds in any
`AddMonoid`, and `Costs.list_sum` handles loops. A cost `c` is a term in `I.charge`, so one lemma
serves every charge. At `charge := Finsupp.single k 1` it is the count, which is the EP6/EP7
pattern. Counts are **an optional clause of `post`, not a field of `Spec`**:

* CERT-ROUTINES CR7 decided that cost and memory are syntactic. `FStmt.staticCost` bounds them
  for every successful run of a compiled tree (`Prog.runsWithin_staticCost_of_exec_eq_some`), so
  a budget needs only success, which `Triple.prog_runsWithin` provides.
* The certificates (`IsBlockRoutine`, `IsMatvecRoutine`, `IsOrthRoutine`) carry no counts and
  plug in unchanged.
* S2's refinement lemmas are generic in `C`, and an exact count in every block would be new work
  where the static cost suffices.

Exact counts are for the blocks where the static cost is too crude: EP7's weighted kernel count,
where `bindIdx` takes a supremum over all values. `Spec.withCharge` transfers a total
specification whose postcondition ignores the count to any other charge. It wraps
`exists_exec_withCharge_eq_some` (ExecCharge:110).

**Weighted bounds (EP7).** `CostsLe w c st st' := w st'.cnt ≤ w st.cnt + c` holds for an additive
weight `w : C →+ ℕ`, such as `Finsupp.weight (OpKind.kernelWeight T)`. It comes with `trans`,
`mono`, `list_sum` and `of_costs`. The supremum over an index binder's values enters through
`Spec.bindIdx_of_read`'s range fact `k ≤ bound`. `Spec.withCharge` holds in **both modes**:
success, the store and the tape positions do not depend on the charge, and the liberal half
transfers back.

### 3.6 Budgets

```lean
theorem Triple.prog_runsWithin {I : Interp P ι K (OpCount P ι)} {r b : ℕ} (prog : Prog P ι r b)
    (N : ℕ) (n : Fin r → ℕ) {pre} {post} (h : Triple .total I pre (prog.toStmt N n) post)
    {st} (hpre : pre st) (hsize : st.store.size = b) :
    prog.RunsWithin I N n st (prog.staticCost I.charge I.width N n).count
      (fun p => max (st.peak p) (st.cur p +
        (prog.staticCost I.charge I.width N n).cells p) + I.romSize p) (post st)
```

`Prog.RunsWithin` is the form the target statements consume (the `MatrixFree*` access models).
Peak memory is not part of `Spec`. The static cost gives it, and a per-block peak clause would
only duplicate `StaticCost.Bounds`.

## 4. The rules

Each rule is proved once, in `ProgramLogic.lean`. The ids are the targets of
`pilot/prog-logic-targets.json`.

### 4.1 Application, consequence, modes

* `Triple.wp_of (h : Triple m I pre s post) (hpre : pre st) (hQ : ∀ st', post st st' → Q st') :
  Wp m I s Q st`. This is **the application rule**, the step every program proof repeats. The
  continuation goal is `∀ st', post st st' → …`, so after `intro st₁ ⟨hfp₁, hpost₁⟩` the next
  state is a variable and everything known about it is hypotheses.
* `Triple.conseq`, `wp_mono`, `Spec.conseq` (with a larger footprint).
* `Triple.liberal` (total ⇒ liberal); `Triple.total_of_liberal` (liberal + success ⇒ total, by
  determinism); `Spec.total_of_liberal`.
* `Triple.exists_exec`, `Triple.holds_of_exec`: the two corollary shapes of S2's lemma pairs.
* `Mode.Sat.mono`, `Mode.sat_some`, `Mode.sat_bind`, `Mode.sat_map`, `Mode.needs_liberal`,
  `Mode.needs_of`.

### 4.2 Statements

Each is an `iff` with `exec`'s equation, so it is S.

```lean
theorem wp_skip : Wp m I .skip Q st ↔ Q st
theorem wp_seq : Wp m I (.seq s t) Q st ↔ Wp m I s (Wp m I t Q) st
theorem wp_instr (i) : Wp m I (.instr i) Q st ↔
    m.Sat (fun r => Q ({ st with store := r.1, pos := r.2, cnt := st.cnt + I.charge i.kind }))
      (i.run I.sem I.tape st.store st.pos)
theorem wp_alloc (p len body) : Wp m I (.alloc p len body) Q st ↔
    Wp m I (body st.store.size) (fun st₂ => Q (st₂.release p len.eval (I.width p)))
      (st.allocate p len.eval (I.width p))
theorem wp_ite (p c x y) : Wp m I (.ite p c x y s t) Q st ↔
    m.Sat (fun r => if r.1 then Wp m I s Q r.2 else Wp m I t Q r.2) (cmpStep I p c x y st)
theorem wp_ite_of_read (hx : read x = some a) (hy : read y = some b)
    (hr : I.sem.cmp p c a b = some r) : Wp m I (.ite p c x y s t) Q st ↔
      if r then Wp m I s Q (st.addCnt (I.charge (.cmp p)))
      else Wp m I t Q (st.addCnt (I.charge (.cmp p)))
theorem wp_kcall (o p dims ins outs) : Wp m I (.kcall o p dims ins outs) Q st ↔
    m.Sat (fun s => Q ({ st with store := s } |>.addCnt
      (I.charge (.kcall p o (dims.map IExp.eval))))) (I.kcallStore o p … st.store)
theorem wp_named (name args) : Wp m I (.named name args s) Q st ↔ Wp m I s Q st
```

**bindIdx (L1).** The body is proved at every converted value with `k ≤ bound` as a
*hypothesis*. The bound is an obligation only in mode `total`:

```lean
theorem wp_bindIdx_of_read (hx : st.store.read p x.buf x.idx.eval = some v)
    (h : m.Sat (fun k => m.Needs (k ≤ bound.eval) ∧
      (k ≤ bound.eval → Wp m I (body k) Q (st.addCnt (I.charge (.toNat p)))))
      (I.sem.toNat p v)) :
    Wp m I (.bindIdx p x bound body) Q st
```

### 4.3 Composite rules

```lean
theorem Triple.seq (h₁ : Triple m I pre s mid) (h₂ : Triple m I pre₂ t post)
    (hmid : ∀ st st₁, pre st → mid st st₁ → pre₂ st₁) :
    Triple m I pre (.seq s t) fun st st₂ => ∃ st₁, mid st st₁ ∧ post st₁ st₂

theorem Triple.loop (Inv : St P K C → ℕ → St P K C → Prop) (h0 : ∀ st, pre st → Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ k < n.eval,
      Triple m I (Inv st₀ k) (body k) fun _ st' => Inv st₀ (k + 1) st') :
    Triple m I pre (.loop n body) fun st₀ st' => Inv st₀ n.eval st'

theorem Triple.whileFuel (Inv : St P K C → ℕ → St P K C → Prop)
    (h0 : ∀ st, pre st → m.Needs (0 < fuel.eval) ∧ Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ j st, Inv st₀ j st →
      m.Sat (fun r => r.1 = true → m.Needs (j + 1 < fuel.eval) ∧
        Wp m I body (Inv st₀ (j + 1)) r.2) (cmpStep I p c x y st)) :
    Triple m I pre (.whileFuel fuel p c x y body) fun st₀ st' =>
      ∃ j stj, Inv st₀ j stj ∧ cmpStep I p c x y stj = some (false, st')

theorem Triple.alloc (h : Triple m I pre' (body b) post') (hb : ∀ st, pre st → st.store.size = b)
    (hpre : ∀ st, pre st → pre' (st.allocate p len.eval (I.width p)))
    (hpost : ∀ st st₂, pre st → post' (st.allocate p len.eval (I.width p)) st₂ →
      post st (st₂.release p len.eval (I.width p))) :
    Triple m I pre (.alloc p len body) post
```

The invariant is relational (`Inv st₀ k st`), so the per-iteration count, frame and size are
stated against the loop's start. `whileFuel` has no variant. The fuel is the variant, and the
invariant's index `j` counts the tests. In mode `liberal` running out of fuel is a failed run, so
the fuel obligation is `m.Needs`. S2 uses no `whileFuel` (`exec_whileFuel_*` is unused). The rule
is for the Newton–Schulz and HDIAG consumers.

### 4.4 Builders

* `wp_run_bind (hx : ExecutionComposable I x) : Wp m I (x >>= f).run Q st ↔ Wp m I x.run
  (Wp m I (f ()).run Q) st`.
* `wp_run_allocBind`: `Builder.alloc p len >>= f` runs the rest of the block on the fresh handle,
  with the postcondition read after release. `rfl` to `wp_alloc`.
* `wp_run_pure`.
* `executionComposable_{stmt, ins, scope, named, forRange, ifThenElse, bindIdx}`: each builder
  combinator except `alloc` emits one statement before its continuation
  (`executionComposable_single` with `rfl`).

With these, a builder proof never `change`s into the unfolded tree (§1.2 step 4).

### 4.5 Specifications

```lean
theorem Spec.seq (h₁ : Spec m I pre s fp post) (h₂ : Spec m I pre₂ t fp₂ post₂)
    (hmid : ∀ st st₁, pre st → Modifies fp st.store st₁.store → post st st₁ → pre₂ st₁) :
    Spec m I pre (.seq s t) (fp ++ fp₂) fun st st₂ => ∃ st₁, post st st₁ ∧ post₂ st₁ st₂

theorem Spec.frame (h : Spec m I pre s fp post) (hF : ReadsOnly F rs)
    (hd : BlocksDisjoint rs fp) :
    Spec m I (fun st => pre st ∧ F st.store) s fp fun st st' => post st st' ∧ F st'.store

theorem RoutineSpec.wp_bind (h : RoutineSpec m I pre r fp post) (hpre : pre st)
    (hk : ∀ st', Modifies fp st.store st'.store → post st st' → Wp m I (f ()).run Q st') :
    Wp m I (r >>= f).run Q st
```

The others:

* `Spec.ite`: the comparison outcome `r` is fixed by the precondition. The arms are specified on
  `st.addCnt (I.charge (.cmp p))`.
* `Spec.loop`: an invariant, with one footprint for all iterations.
* `Spec.alloc`: the body may modify the fresh block `(b, 0, len)`; the allocation's footprint is
  the body's below it.
* `RoutineSpec.wp_run`: the last call of a block.
* `RoutineSpec.bind`: two specified routines form one. This extends `IsBlockRoutine.bind` so that
  the output of the first feeds the second.
* `RoutineSpec.scope`: a scope around a specified routine is specified alike.

`ReadsOnly.of_spec_post` is the pointwise frame used inside a walk: one call per kept fact, with
the side goal `BlocksDisjoint rs fp` closed by `fp_omega`. The read-set lemmas are:

* `readsOnly_read`;
* `readsOnly_writable`;
* `readsOnly_readsDecoded`;
* `readsOnly_holdsDecoded`;
* `readsOnly_entryLayoutHolds`, so `pairLayout.Holds` gets one too;
* `ReadsOnly.and`, `ReadsOnly.mono`, `ReadsOnly.push`, `ReadsOnly.pop`;
* `IsFramed.of_modifies`, so buffer-framed preconditions from CERT-ROUTINES keep working.

### 4.6 Existing contracts as specifications

| contract | bridge | form |
|---|---|---|
| kernel call (any) | `wp_kcall`, `Modifies.of_kcallStore` | output blocks `kcallBlocks outs (I.kshape o ds).2` |
| `IsMatMulKernel` | `IsMatMulKernel.spec_kcall` (Matrix layer) | mode-generic `Spec`, footprint `matBlock` of the output, writability under `md.Needs` (the liberal half needs none), `Costs` one call, `PosKept` |
| `IsBlockRoutine` | `IsBlockRoutine.routineSpec` | `RoutineSpec .total` with `pre ∧ WritableBlocks`, footprint `outs` |
| `IsMatvecRoutine` | `IsMatvecRoutine.routineSpec` | per input `x`: footprint the destination block, post the decoded error bound |
| `IsOrthRoutine` | `IsOrthRoutine.routineSpec` (Matrix layer) | per `V`, `w`: footprint the two output blocks, post `IsOrthErr` on the decoded outputs |
| `EighWeight.Triple` | none at first (PG4) | it is a liberal triple whose post is a weight bound on one buffer; re-expressed in wave 4 |

**Wrap, not replace (PG4).** `IsBlockRoutine`, `IsMatvecRoutine`, `IsOrthRoutine` and the kernel
contracts stay as they are. They are statements of *certificates* and appear in consumer
theorems (CERT-ROUTINES CR2 a: additive). Bridges turn each into a `RoutineSpec`, so a consumer
proof uses the call rule. `IsBlockRoutine.bind` becomes a corollary of `RoutineSpec.bind`.
`EighWeight.Triple` and `BuilderFrame` stay until the S2 walks are migrated. Their generic rules
(FrameRules:97–239 and the generic part of :381–480, about 300 lines) are then instances of
`Triple .liberal` with a weight postcondition. The block lemmas `triple_eighSplitBlock` and the
rest are re-proved in wave 4.

### 4.7 Rules for S2's patterns (added by the reviews)

All are in the scaffold. Statements are given in full there.

**Call sites.**
* `RoutineSpec.stmt (h : Spec m I pre s fp post) : RoutineSpec m I pre (Builder.stmt s) fp post`,
  and `RoutineSpec.ins`. A kernel call in a builder (`stmt (.kcall …)`) is then one `spec_call`.
* `RoutineSpec.congr` and `Spec.of_normIdx_eq` transport a specification across run equivalence
  and index normal forms. This covers Compress called at `.const k - kpe` (SplitSuccess.lean:87–93)
  and the `BuilderEquiv` rewrites (DownSlot.lean:394–426).

**Allocation by named states (L3).**
* `Spec.allocBind` specifies `Builder.alloc p len >>= f`. The rest of the block is specified at
  the relative handle `b`, from a state `st₁` given by the *equation*
  `st₁ = st.allocate p len.eval (I.width p)`, not by a pushed term.
* The allocation-state lemmas are `St.size_allocate`, `St.writable_allocate` and
  `St.read_release_of_lt`.
* `Modifies.pop_top` drops the fresh block from the footprint after the pop.
* Eight nested allocations are eight applications. Each introduces a named state with
  hypotheses, so no push chain or nested release lambda reaches a goal. Job J1's third gate
  measures this on Split's prefix.

**Loops with data-dependent footprints.**
* `Spec.loopFp` and `RoutineSpec.forRange` take one footprint per iteration, `fp : ℕ → List …`
  (which may depend on ghost sizes read before the loop), and conclude
  `(List.range n).flatMap fp`.
* `Spec.bindIdx_of_read` specifies an index binder whose body footprint depends on the
  converted value. Its postcondition records `k ≤ bound`.
* `Spec.ite_cases` is the two-armed conditional, for when the branch is not fixed by the
  precondition.
* `spec_eighWhen` is S2's guarded block (`forRange (1 - (1 - e))`).
* The bridge from `Modifies` to S2's window frames (`EighSlotWindow`, `EighNodeWindow`) is
  S2-local and planned in J4.

**Instructions and the tape.**
* `spec_lit`, `spec_litIdx`, `spec_bin`, `spec_un`, `spec_copy` and `spec_draw`: footprint the
  destination cell, postcondition the cell's value, `Costs` of one charge, `PosKept`. `spec_draw`
  advances the position instead.
* `spec_forRange_draw`: a loop of draws into a block holds the next `n` tape values and advances
  the position by `n`.
* `PosKept st st'` is the common clause.

### 4.8 Rules added after the shifted-QR end-to-end test

The test (one shifted QR step written and proved from the playbook) found four missing rules.
* `spec_scalarBlock` (`StraightLine.lean`) specifies a straight-line block of scalar operations
  as one function update of the word function (`evalOps`, `storeFn`): no precondition in the
  liberal mode; in the total mode the cells read are defined when read (`OpsDefined`, so
  temporaries need no initialisation), the operations succeed (`OpsOk`) and the written cells
  are writable. Footprint one cell per operation; post the evaluated words, `Costs` of one charge
  per operation, `PosKept`.
* `RoutineSpec.sub` is the builder form of `Spec.sub`.
* `RunEquiv` (`RunEquiv.lean`) transports a specification between builders that differ only in
  index expressions of equal values, by one congruence rule per builder form (tactic
  `run_equiv`, transport `RoutineSpec.of_runEquiv`), instead of `exec_eq_of_normIdx_eq … rfl` on
  whole statements, which exhausted the kernel. Index-generic specifications (`(xo : IExp ℕ)`,
  stated on `xo.eval`) remain the default and need no transport.
* `Spec.whileFuel` and `RoutineSpec.whileFuel` (`RoutineWhile.lean`) give `whileFuel` an
  invariant and a footprint. The total mode needs fuel for the first test (`hf0`), the comparison
  defined and fuel for each test that holds, and concludes success.

## 5. Tactic support

Four macros in `ProgramLogic.lean`, plain `macro`/`macro_rules` (the precedent is
`FrameRules.lean:484`, `frame_side`):

* `fp_omega [h₁, …]` adds the facts `hᵢ` as named hypotheses. It unfolds `BlocksDisjoint`,
  `matBlock`, `List.Nodup` and `blockDisjoint_iff` **in the goal and those facts only**, never the
  whole context (S2 proofs have 40+ hypotheses). It normalises products with `ring_nf`, so
  `r * k` and `k * r` become one atom, and closes with `omega`. Nonlinear bounds are supplied as
  facts, for example `Nat.mul_le_mul hr hk`, or S2's layout lemmas. Only the goal and the passed
  facts are normalised (`n * n` becomes `n ^ 2`), so **every hypothesis with a product that the
  goal needs must be passed**: `fp_omega [Nat.mul_le_mul …, hlen]`, not a context `hlen`.
* `fp_close` is its closing step.
* `spec_step h`: `rw [wp_seq]` if possible, then `Triple.wp_of h`. Side goals closed by
  `assumption` or `fp_omega` are removed.
* `spec_call h`: `RoutineSpec.wp_bind h`, or `RoutineSpec.wp_run h` for the last call. Side goals
  are tried only on the goals the `refine` creates (`<;>`), never on sibling goals.

Tested on the scaffold, by `lake env lean` on a test file:

* `2*(n*n)*d + 2*(n*n) ≤ 2*(n*n)*(d+1)`;
* `k ≤ n → r ≤ k → 2*(n*n) ≤ l → 2*(r*k) ≤ l`, with `fp_omega [Nat.mul_le_mul (hr.trans hk) hk, hl]`;
* `2*(r*k) ≤ l → k*r*2 ≤ l`;
* Split's packed `Qa` blocks `(Qa, qo, 2*(k*kp))` and `(Qa, qo + 2*(k*kp), 2*(k*(k-kp)))`;
* the blocks of depths `d` and `d + 1` in `Ma`;
* the pilot's input-against-scratch footprint from `hbufs : [Qa, Ma, Qh, C1, C2, C3].Nodup`;
* relative handles `[b, b+1, b+2, b+3].Nodup`;
* a cell against an output block, converting `2 * (r * r)` to `matBlock` form.

The first three are the goals the COMPDYN review found plain `omega` fails. All eight close.

The shape of a program proof (the pilot, PL107):

```lean
theorem spec_eighCompressBlock … : RoutineSpec md I pre (eighCompressBlock …) fp post := by
  unfold eighCompressBlock                      -- the goal is now `(x >>= f).run` form
  refine ⟨…composable…, fun st hpre => ?_⟩
  obtain ⟨hQ, hA, htwo, hσ, hneeds⟩ := hpre
  obtain ⟨htwo0, hW⟩ := Mode.needs_and.mp hneeds
  spec_call (spec_zconjTranspose md hsem p k r Q (by fp_omega [hbufs]))
  intro st₁ hfp₁ ⟨hQh, hpos₁⟩
  spec_call (RoutineSpec.stmt (hmm.spec_kcall hL md p (Qh, 0) (Ma, mo) (C1, 0) _ A))
  · exact ⟨hQh, hA.of_spec_post … (by fp_omega [hbufs]), …, hW.mono … |>.of_modifies hfp₁⟩
  intro st₂ hfp₂ ⟨hC1, hcost₂, hpos₂⟩
  …
```

**The frame discipline**, stated once for contributors:

* *values* are carried by `ReadsOnly.of_spec_post … (by fp_omega [facts])`;
* *shapes and writability* by `Writable.of_modifies hfpᵢ` (or `WritableBlocks.of_modifies`);
* *requirements* are split with `Mode.needs_and` and passed on with `Mode.Needs.mono`.

The goal is always `Wp md I rest Q stᵢ` on a named state. An automated `spec_frame`, which would
search the hypotheses, is deferred until J1 counts the frame calls (§8, R4). Footprint
inference by recursion over `Stmt` would need a recursor in `Exec.lean` or a NAMED_FILES entry
(E8), so it is out of scope.

## 6. Placement and house rules

| declaration(s) | home | reason |
|---|---|---|
| §3–§5 except the Matrix bridges | `NLAlib/Computation/ProgramLogic.lean` (footprints, modes, triples, statement and builder rules) and `NLAlib/Computation/RoutineSpec.lean` (specifications, counts, instructions, certificate bridges, tactics), split at implementation to stay under the 1,500-line ceiling | the logic of the run; Computation imports only Mathlib, ForMathlib, Computation (E5) |
| `IsBlockRoutine.routineSpec`, `IsMatvecRoutine.routineSpec` | `ProgramLogic.lean` | it imports `RoutineFrames` and `MatvecRoutine`; the certificates' files must not import the logic (no cycle) |
| `readsOnly_entryLayoutHolds`, `IsMatMulKernel.spec_kcall` | `NLAlib/Matrix/Computation/KernelContracts.lean` | API of the layout and the kernel contract |
| `IsOrthRoutine.routineSpec` | `NLAlib/Matrix/Computation/OrthRoutine.lean` | API of the certificate |
| `spec_eighCompressBlock` and the other S2 block specifications | each block's file, next to its two lemmas | the block's API |
| `spec_z*` (pair kernels) | `NLAlib/Matrix/Computation/PairKernels/*.lean` | the kernels' API |
| `IsControlExactSem`, `IsRoutineSem` | `NLAlib/Matrix/Computation/InterpMachine.lean` | next to `ScalarSem.DecidesFlags`, which they bundle |
| `spec_eighWhen` | `NLAlib/Matrix/Computation/SpectralBisectionProgramTree.lean` (or the first S2 file using it) | the API of `eighWhen` |
| duplicated helpers (§1.3) | deleted for the library lemma, or moved to `ProgramLogic.lean`/`Loops.lean` (L6) | one public home |

* **E8.** No declaration *constructs* `Stmt.named`. `wp_named` and `executionComposable_named`
  are theorems that mention it, which rule E8 allows ("a theorem may mention it"). The scaffold
  passes `check_rules.py --files`. No check, rule data or allowlist changes. **No exemption is
  needed**, unlike `NonInterference.lean`, which defines a recursor over `Stmt` and so needed its
  NAMED_FILES entry. `ProgramLogic.lean` defines no recursor: `Wp` is defined from `exec`.
* **E5, P1.** `ProgramLogic.lean` imports `RoutineFrames`, `IndexBinder`, `Loops`, `Contract`,
  `StaticCost`, `ExecCharge` and `MatvecRoutine`, all in Computation.
* **The scaffold.** As for HDIAG and SHIFTED-QR, this branch adds a `NLAlibScaffold` `lean_lib`
  entry to `lakefile.toml`. **That entry must not reach main.** Each statement moves into
  `NLAlib` when proved.
* **Vocabulary rows** (`docs/contributing/vocabulary.md`, in the implementation PR):
  * "program specification": `Computation.Wp`, `Computation.Triple`, `Computation.Spec`,
    `Computation.RoutineSpec`, `Computation.Mode`;
  * "footprint, read set": `Computation.Modifies`, `Computation.ReadsOnly`,
    `Computation.BlocksDisjoint`;
  * "exact count": `Computation.Costs`.

  Each has the Mathlib bridge "none (searched: Mathlib has no program logic; Lean core
  `Std.Do.Triple` is for shallow monadic programs, §2.1 D)".
* **Related frame notions on main.** `Store.frame_of_writeBlocks_eq_some` (RoutineFrames:174)
  is the read half of `Modifies.of_writeBlocks`, used in its proof. `Store.BlockFrame s₀ p T dst
  dOff L s` (Store.lean:721) is a one-block `Modifies` with one scratch buffer and a value clause.
  The implementation adds a one-line bridge, and the vocabulary row lists both.
* **Mathlib deviations.** None: Mathlib has no notion to deviate from. `Std.Do` is not Mathlib;
  §2.2 records why it is not used.
* **Contributor guide.** `docs/contributing/programs.md` gets a paragraph after "A routine used
  inside a larger one is certified once …". A program proof states a `RoutineSpec` per block,
  proves it by `spec_call`/`spec_step` and the rules of `ProgramLogic.lean`, and derives the
  success and refinement lemmas from it. CERT-ROUTINES' §4 checklist gets the bridge line.

## 7. Migration plan

### 7.1 Principles

1. **Registered target statements do not change.** `NLAlib.MatrixFreeRoundedProbEigh`
   (`RandomMatrix/Computation/SpectralBisectionTargets.lean:82`) and its tree
   `eighProg.compiled` are untouched. No block definition changes, so no tree hash changes. Only
   proofs and internal lemmas migrate. **No re-pin is needed.** `stage_check.sh`'s closure-hash
   check confirms this on each PR.
2. **Adapter first, re-proof later.** An existing pair `holds_of_exec_X` and `exists_exec_X`
   gives `spec_X` by `Spec.total_of_liberal` (S). So a consumer migrates before its callee is
   re-proved, and the migration can stop at any block.
3. **Bottom-up within S2, statements unchanged where consumed.** Each block gets `spec_X`
   (mode-generic). Its old two lemmas become two-line corollaries with unchanged statements
   (`Triple.holds_of_exec` at `liberal` and `Triple.exists_exec` at `total`, plus the
   `Modifies`-to-old-frame conversion). They are deleted once no consumer uses them; deleting an
   internal lemma needs no approval.

### 7.2 Block map and the estimate

Savings are net of the specifications that replace the walks, and exclude text that only moves.
They are revised after both reviews: the first estimate's own table summed to about 3.6k
including a helper sweep that does not depend on the logic.

| block | rules used | today (both walks + helpers) | saving (net) |
|---|---|---|---|
| pair kernels (`zconjTranspose`, `zhermAvg`, `zhermShift`, `zmirror`, …) | adapters, then `Spec.loopFp` | ≈ 900 in `PairKernels/` | −60 (glue) |
| Sign (Newton–Schulz test/step) | `RoutineSpec.forRange`, `spec_kcall`, `Spec.ite_cases` | ≈ 525 | 150–225 |
| Deflate, Leaf, Child | `Spec.allocBind`, call rule, `Spec.loopFp` | ≈ 620 | 200–270 |
| **Compress (pilot)** | call rule ×5, `RoutineSpec.stmt` | 180 + 206 helpers (158 move) | ≈ 100 (walks 180 → ≤ 90) |
| Split | `Spec.allocBind` ×8, call rule, `spec_litIdx` ×4 | ≈ 630 | 300–410 |
| Clamp | `spec_lit`, `Spec.ite_cases` | 120, already one walk | 30–50 |
| Node | call rule, `Spec.bindIdx_of_read`, `spec_eighWhen` ×3 | ≈ 740 | 250–360 |
| Down slot, DownLevel | `Spec.loopFp`, window bridge, one `DownSlotsInv` for both modes | ≈ 830 + the duplicated invariant | 500–700 |
| BottomLevel | `RoutineSpec.forRange` | 131 | 30–50 |
| Up shift/split/node/slot, UpLevel | call rule, `RoutineSpec.forRange`, instruction specs | ≈ 1,000 | 350–450 |
| driver (`eighProg`, passes, loops) | `RoutineSpec.forRange`, `Spec.allocBind` ×11 | ≈ 1,100 | 300–500 |
| helpers whose removal needs the logic (§7.5) | deleted | — | ≈ 200 |

**Estimated S2 saving: 2,350–3,255 lines (19–26% of 12,550).** The range is the sum of the
rows.

* *Low end:* the rows' low ends. Every leaf that has no mode-generic specification (the other
  pair kernels, the instruction-level success steps) keeps a separate success proof.
* *High end:* the high ends, with the two `DownSlotsInv` copies merged (COMPDYN: 500–700 if
  per-slot footprints land).
* *About 4,000 (Fable's "plausible for a complete W3"):* this needs every `*Success.lean` file
  folded *entirely*, which needs every leaf specified mode-generically. It is not the planning
  figure.

The helper sweep that does not depend on the logic (part of it done in the S2 clean-up,
Stage-COMPDYN-S2-Hardening.md:283–297) is not counted. The cost side (FrameRules, Weight: 1,693)
is W4: about 300 lines, with `CostsLe`.

**W3 sequencing with F3 step 2.**
* W3 folds the success walks together with F3 step 2 of the EIGH follow-ups (bounded formats:
  success re-proved on the good-sample event, Plan-EIGH-Followups.md:121), in the same lane.
* W3's specifications take `safe` as a parameter (not `fun _ _ => True`) and put the range facts
  under `m.Needs`, so they are written once.
* The pilot keeps `fun _ _ => True` because the statement of `exists_exec_eighCompressBlock`
  does.

### 7.3 The pilot: `eighCompressBlock`

Why this block:

* It is the representative cost case. Its two walks are 180 lines, with 206 lines of private
  helpers, and it has all of §1.2's waste.
* Its sub-blocks are already specified in frame style.
* It has two consumers: Split.lean:258, :268, and SplitSuccess.lean:223, :232, :287, :303.

**Targets.**
* PL104–PL106: the adapters `spec_zconjTranspose`, `spec_zhermAvg` and `spec_zhermShift`
  (scaffold, statements exact, canonical `matBlock` footprints). Their success halves are the
  private helpers of Compress.lean (:200, :266, and `exists_exec_zhermAvg` in HermAvg.lean),
  *moved* unchanged to `PairKernels/`. The case of an empty matrix is direct (`exec_loop` on
  `List.range 0`).
* PL107: `spec_eighCompressBlock` (scaffold `CompressSpec.lean`). Its precondition is:
  * the inputs as `pairLayout.Holds` and the two cells;
  * `md.Needs (dec p c₂ ≠ 0 ∧ WritableBlocks st.store p fp)`, with the footprint
    `[matBlock Qh 0 r k 2, matBlock C1 0 r k 2, matBlock C2 0 r r 2, matBlock C3 0 r r 2,
    matBlock Ma co.eval r r 2]`.

  Its parameters are `hmm`, `hbufs` and `hcells`. Its postcondition is `PosKept` and the value
  clause, **guarded** by the old `hcocells`.
* PL108 `holds_of_exec_eighCompressBlock` and PL109 `exists_exec_eighCompressBlock`, **statements
  unchanged**, re-proved from PL107:
  * PL108 at `liberal`, with the guard discharged by its `hcocells`;
  * PL109 at `total`, which needs no `hcocells`, since its statement has none.

  PL109 derives `WritableBlocks fp` from `hscr`, `hcolen`, `hk` and `hr` with `writable_of_shape_eq`
  and `fp_omega [Nat.mul_le_mul …, hlen]`. The bounds are nonlinear, so the products are
  supplied, and the context bound `hlen` (from `hscr`) is passed too (§5).

**B1, resolved from the code.** The two reviews disagreed about whether the first PL76 (now
PL107) had exactly the hypotheses of the two lemmas.
* `exists_exec_eighCompressBlock` (Compress.lean:381–395) has **no `hcocells`**. Its shift
  helper succeeds wherever the cell lies (:264).
* The first PL76 took `hcocells` as an unguarded parameter, so its total instance needed a
  hypothesis PL109 lacks.
* The COMPDYN review was right. Fable's "exactly the union" overlooked that `hcocells` occurs
  only at :91.

Moving `hcocells` into a guard of the value clause (PG2's correctness-only rule) keeps **both
statements unchanged** with no restatement. The same applies to `spec_zhermShift`'s cell
condition.

**The gate (job J1).**
1. *Walks:* PL107 + PL108 + PL109 ≤ 90 lines, against today's two walks of 180
   (Compress.lean:91–174, :381–476).
2. *Net diff:* `git diff --numstat` over `NLAlib/`, excluding `ProgramLogic*.lean`, reported.
   The adapters' glue (PL104–PL106 minus moved text) is reported separately as the per-kernel
   cost of entering the logic. Moved helpers count as neither saved nor added. The expected net
   saving for the block is about 100 lines.
3. *Alloc chains (L3):* PL110 `spec_eighSplitBlock_of_body` (scaffold `SplitAllocSpec.lean`):
   a specification of the split body at the scratch handles $b, \dots, b + 7$ gives the split
   block's. It is proved by `Spec.allocBind` ×8 with named states, replacing the eight
   `alloc_inv_node` steps (Split.lean:589–596). Compress has no allocations, so gates 1 and 2 do
   not test L3.

All three run with stage_check 0 and default heartbeats. The design returns to PG1 only if
gate 1 fails.

**Measured (J1, feat/prog-logic).**
1. *Walks:* PL107 + PL108 + PL109 = 45 + 21 + 24 = **90 lines** (≤ 90: pass), against 180; the
   two old statements unchanged and included in the count.
2. *Net diff* (`git diff --numstat origin/main -- NLAlib/`, the logic files excluded):
   `Compress.lean` +68 −386; `PairKernels/{Arithmetic,HermAvg,Hermitian}.lean` +359, of which
   about 175 lines are moved text (the conjugate-transpose and shift success halves, the block
   write, the mirror success step) and about 185 are the adapters' glue: the three
   specifications and the liberal frames of `zconjTranspose`, `zmirror` and `zhermShift`. The
   frame of `zhermShift` had to be proved anew: its old refinement lemma gives the frame only
   under the cell's disjointness, which the specification guards. Net for the block with its
   adapters: **+41 lines**; without the moved text the walks and helpers saved about 145 lines and
   the glue cost about 185. The glue is paid once per kernel; Split reuses it twice.
3. *Alloc chains:* PL110 `spec_eighSplitBlock_of_body` proved by `spec_allocBind_iterate`
   (one rule application per allocation, named states, `Function.iterate` for the eight
   allocations and releases) in 8 proof lines at default heartbeats: pass. Its use in place of the
   eight `alloc_inv_node` steps of `holds_of_exec_eighSplitBlock_frame` waits for J2, where the
   split body gets a specification with a block footprint (the old body lemma's frame is the
   node window, not a footprint).

### 7.4 `maxRecDepth` and the compiled tree (L7)

The logic works on builder runs and statement constructors, never on `eighProg.compiled`'s
normal form. Only the existing transfer `eighProg.toStmt_compiled` (`rfl` under `maxRecDepth
10000`, SpectralBisectionProgram:814) touches the tree. It is unchanged.

### 7.5 One home for the duplicated helpers (L6)

In wave 1, each lemma of §1.3 is replaced by its library form where one exists
(`exec_seq_of_exec_eq_some`, `exec_seq_instr_*`, `exists_exec_loop_eq_some_of_forall`,
`exec_bindIdx_of_read`, `exec_alloc_of_exec_eq_some`). The rest move to `Loops.lean` (loop 0/1,
loop shape/read) as public lemmas. `scripts/Duplicates.lean` is the check. The Krylov copies
(`exec_scope_of_exec_eq_some` ×2, `exec_exact_*` ×3) go in the same sweep. `exec_rounded_compiled`
×5 are distinct theorems with the same name in different namespaces, so they stay.

### 7.6 Second consumers: CGS2 and Lanczos-reorth, and CR2

* **CGS2** (`ClassicalGramSchmidtProgram.lean`, 603 lines after the CERT pilot). Prove
  `exec_cgsPass_*` as `Spec.loop` specifications. Then `exists_exec_cgs2` and
  `IsRelErrSem.isOrthRoutine_cgs2` follow by `RoutineSpec.bind` and `Spec.alloc`. Estimate −150.
* **Lanczos-reorth** (`LanczosReorthProgramRoundedStep.lean` 817, `…RoundedLoop.lean` 643):
  * `exec_workPhase`, `exec_commitPhase` and `exec_stepBody` become specifications using
    `IsMatvecRoutine.routineSpec` and `IsOrthRoutine.routineSpec`;
  * `exec_lanczosReorthLoop` becomes `Spec.loop` with the relational invariant
    `StoreContext k st₀ st`.

  Estimate −350.
* **The `ReadsOnly` mechanism for CR2 item 2.** A zero-length block `(k, 0, 0)` in a read set
  carries the shape of buffer `k` and nothing else, and is `blockDisjoint` from every block. So
  the Lanczos `hpreFrame` becomes `ReadsOnly pre [(0,0,0), …, (6,0,0), (7, 0, len₇)]`: the shape
  of buffers 0–6 and the values of buffer 7. That is the whole argument for PG7 (a).
* **CR2 (CERT-ROUTINES §8.3).** Item 1 (`IsOrthRoutine` at block-level disjointness) is
  independent and can land first; `IsOrthRoutine.routineSpec` is stated for today's `run` and
  changes its three `≠` hypotheses to `BlocksDisjoint` with it. Item 2 is the `hpreFrame` to
  `IsFramed` change. **This design changes its recommendation:** use `ReadsOnly pre rs` (block
  read set, shape per read buffer) in place of `IsFramed pre ro`. It separates the shape
  dependence on buffers 0–7 from the value dependence on buffer 7, the gap §8.3 found.
  `ReadsOnly.of_modifies` then carries `pre` across each phase, with the side goal discharged by
  `fp_omega`. Item 3 (`hmv : ∀ t < q`) is unaffected. None of the three touches a registered
  target (§8.3).
* **Coordination.** T119 (CERT-ROUTINES implementation, ORACLE-MODEL stage A) has no pending
  change to `RoutineFrames.lean` or `Exec.lean` (`design/oracle-model` and
  `feat/rounded-krylov-oracles` diff empty on both, checked 2026-11-08). The COMPDYN session
  confirms nothing pending on S2. This note adds `ProgramLogic.lean` beside `RoutineFrames.lean`
  and changes neither.

## 8. Risks

| id | risk | mitigation |
|---|---|---|
| R1 | Relational postconditions grow: the composite post of `Spec.seq` is `∃ st₁, post₁ ∧ post₂`; nested ten deep, it is unreadable | Specifications are proved with the application rule and the call rule (named states, flat hypotheses), not by folding `Spec.seq`; `Spec.seq` is for library-level composition of two routines, followed by `Spec.conseq` to a stated post |
| R2 | Contributors have not written mode-generic proofs before | Leaf rules show where `m.Needs` enters; the pilot is the worked example; `Spec.total_of_liberal` lets a block keep two proofs if it must |
| R3 | `simp only … at *` in `fp_omega` disturbs hypotheses in large contexts | `try` reverts it on failure; the frame steps call it on small goals; a `fp_omega` variant that only touches the goal is kept as an option for the pilot to choose |
| R4 | Frame calls stay one per fact (no frame automation) | Each is one line with `fp_omega`; an automated `spec_frame` is deferred until the pilot shows how many there are |
| R5 | Performance (L3): `Modifies` over long footprints, `blockDisjoint` unfolding | Footprints are short concrete lists; `blockDisjoint_iff` unfolds to `omega` atoms; the pilot runs with default heartbeats as part of its gate |
| R6 | The pilot's footprint lengths (exact block sizes) differ from the frames of the old lemmas (whole scratch buffers) | PL108 converts `Modifies` to the old buffer frame (a cell outside the scratch buffers is disjoint from every scratch block); checked by hand for compress |
| R7 | Scope creep into a separation logic | Out of scope (§2.2); the frame rule is one lemma |
| R8 | Packed offsets are nonlinear (`2*(n*n)*d + 2*n*lo + 2*(k*kp)`) | `fp_omega` normalises products and takes supplied facts; S2's layout lemmas supply the bounds; tested on the review's failing goals (§5) |
| R9 | `IsOrthRoutine.routineSpec` (PL102) proved before CR2 item 1 changes `IsOrthRoutine` | PL102 is ordered after CR2 item 1, or restated with `BlocksDisjoint` first |
| R10 | `NLAlib.EighWeight.Triple` and `NLAlib.Computation.Triple` are both open in FrameRules | Qualify or rename in J7 |
| R11 | Window-predicate frames of the slot loops are S2-specific | A `Modifies`-to-window bridge, S2-local, in J4 |

## 9. Waves

Targets (PL, `pilot/prog-logic-targets.json`) are provable statements; jobs (J,
`pilot/prog-logic-jobs.json`) are migration work that names existing declarations.

| wave | content | items | depends on |
|---|---|---|---|
| W0 | modes, `Wp`, triples, application/consequence, statement rules, builder rules (§4.1–§4.4); `Triple.whileFuel` to the strongest prover | 34 targets | — |
| W1 | footprints, read sets, canonical blocks, `Spec`, `RoutineSpec` and their rules (§4.5, §4.7), instruction specs, counts, budget, bridges, records | 68 targets | W0 |
| W2 | adapters, `spec_eighCompressBlock`, the two re-proofs, the gate-3 statement; then J1 (moves, deletions, the three gates) | PL104–PL110, J1 | W1; PL107 after `RoutineSpec.stmt` and the `Mode.Needs` algebra |
| W3 | S2 blocks bottom-up with F3 step 2: Split, Sign/Deflate/Clamp/Node (with `spec_eighWhen`, PL103), Down, Up, driver | PL103, J2–J6 | J1 gates |
| W4 | EIGH weight (`CostsLe`); CGS2 and Lanczos-reorth, CR2 item 2 with `ReadsOnly` | J7–J9 | W3; CR2 item 1; `feat/lanczos-reorth` landed |

Owners follow PG9.

* The COMPDYN/S2 session builds W0–W3 in its one builder lane, so W0–W1 are built only in
  `Computation` and the Matrix/S2 closure is never built twice at once.
* This pipeline reviews the W0–W1 statements before they are proved, and keeps the note and the
  sheet.
* J7 goes to the COMPDYN session. J8–J9 go to the owner of the reorth work, after
  `feat/lanczos-reorth` has landed.

## 10. Material

* C. A. R. Hoare, "An axiomatic basis for computer programming", *CACM* 12(10), 1969: triples,
  the rules of sequence, consequence and iteration with an invariant [Hoare1969].
* E. W. Dijkstra, *A Discipline of Programming*, 1976: weakest and weakest liberal
  preconditions, here the two modes [Dijkstra1976].
* J. C. Reynolds, "Separation logic: a logic for shared mutable data structures", LICS 2002, and
  P. O'Hearn, J. Reynolds, H. Yang, "Local reasoning about programs that alter data structures",
  CSL 2001: the frame rule, here `Spec.frame` over block read sets [Reynolds2002,
  OHearnReynoldsYang2001].
* A. Erbsen et al., "Integration verification across software and hardware for a simple
  embedded system", PLDI 2021 (Bedrock2): a low-level imperative language with flat memory, a
  weakest precondition computed from the semantics, and `straightline` tactics. This is the
  closest model for (A) and for §5.
* Lean core `Std.Do` (`Std/Do/Triple/Basic.lean`, toolchain v4.33.1) and its `mvcgen` tactic:
  `Triple` defined from `wp`, `@[spec]` lemmas. It is for shallow monadic code (§2.2). Mathlib
  has no program logic (searched: `Hoare`, `wp`, `Triple`, `separation`).
* In the library: `EighWeight.Triple`/`BuilderFrame` (`FrameRules.lean`), a liberal cost triple
  and a CPS builder frame. Their rule set (seq, alloc, ite, bindIdx, loop) is the shape reused
  here. CERT-ROUTINES' `RoutineFrames.lean` gives the footprint algebra that `Modifies.of_writeBlocks`
  bridges to.

Not reproduced: assertion languages, separating conjunction, fractional permissions,
concurrency, and verification-condition generation by metaprogramming.

The bibliography keys are added to `docs/references.bib` with the implementation, only if a
library docstring cites them; the note cites them here only.

## 11. Open questions (decision sheet PG1–PG9)

| id | question | options | recommendation | why |
|---|---|---|---|---|
| APPROVE | Approve the design, the scaffold (108 sorried statements: 102 library rules and bridges, the `eighWhen` rule, four pilot statements, the gate-3 statement; plus two re-proofs, 110 targets; nine jobs) and the pilot gates? | a / b not yet | a | Additive; every rule S–M except `whileFuel` and the pilot (L); no target re-pin; both reviews' blocking items applied |
| PG1 | Style of the logic | **a wp by definition + relational triples + block frame rule** / b primitive Hoare judgement with soundness / c separation logic / d `Std.Do` + `mvcgen` | a | `exec` is deterministic, so the rules are run equations (S each) and nothing needs a soundness proof; named states fix L3 |
| PG2 | Total vs liberal | **a mode-generic specs (`Mode`, `m.Needs` for success-only hypotheses, guards in `post` for correctness-only ones, the `Mode.Needs` algebra)** / b total only / c two separate calculi | a | One walk yields S2's two lemmas with statements unchanged |
| PG3 | Counts in the specification | **a optional `Costs`/`CostsLe` clauses in `post`, budgets from `staticCost` (CR7)** / b a mandatory cost field / c no count support | a | Certificates and refinement lemmas carry no counts; exact or weighted counts only where EP7 needs them |
| PG4 | Replace or wrap `IsBlockRoutine`, the typed certificates and `EighWeight.Triple` | **a wrap: bridges to `RoutineSpec` now, `EighWeight.Triple` re-expressed in W4** / b replace / c leave separate | a | Certificates are consumer-facing statements (CR2 a); bridges are S–M each |
| PG5 | Footprint form | **a `Modifies` (frame style) with canonical `matBlock` blocks, bridged from `writeBlocks`** / b CERT-ROUTINES' `writeBlocks` equation | a | Uninitialized partially-written scratch is not a block write; every S2 and kernel lemma is already in frame style |
| PG6 | Scope of the S2 migration | **a pilot first (J1: walks 180 → ≤ 90, net diff reported, Split's 8-alloc prefix), then all blocks bottom-up with F3 step 2** / b all blocks now / c pilot only | a | Measures before spending; 2,350–3,255 lines expected |
| PG7 | CR2 item 2 (`hpreFrame`) | **a `ReadsOnly` with zero-length blocks for shape-only buffers** / b `IsFramed` as in CERT §8.3 | a | Separates shape from value dependence, the gap §8.3 found |
| PG8 | Tactics | **a `spec_step`, `spec_call`, `fp_omega [facts]` (ring-normalised, goal-only)** / b none / c a frame-search tactic now | a | Cheap, house-rule safe, tested on S2's nonlinear goals; frame search deferred |
| PG9 | Who implements | a this pipeline / b the COMPDYN session for everything / c split W0–W2 here, W3 by COMPDYN / **d (COMPDYN's proposal) the COMPDYN/S2 session builds W0–W3 in one lane; this pipeline reviews the W0–W1 statements and keeps the note and sheet; W4 by owner (EIGH weight: COMPDYN; CGS2/Lanczos-reorth: the reorth owner)** | d | Rules and their hardest consumer are tuned together by the session that knows S2; no concurrent edits to S2 with F3 step 2; one builder lane for the heavy closure |

## 12. Review record

**Fable, 2026-11-08** (`reports/Review-Fable-ProgLogic-Design.md`): approve with changes; 0 false,
0 ill-posed statements among the 76.

Applied:
* (1) `RoutineSpec.stmt`/`.ins`.
* (2) `Mode.needs_and`, `Mode.Needs.mono`, `Mode.Needs.elim`.
* (3) the gate on the walks, 180 → ≤ 90, with moved text excluded (J1 gate 1).
* (4) the jobs out of the targets: `pilot/prog-logic-jobs.json`. The counts are now 109
  targets (S 77, M 30, L 2) and 9 jobs.
* (5) `Modifies.pop_top`, used by `Spec.alloc`.
* (6) the adapters' empty-matrix case and the moved success halves, in the outlines.
* (7) the `ring_nf` normalisation in `fp_omega`.
* (8) `Writable.of_modifies`, `WritableBlocks.of_modifies` and the frame discipline (§5).
* (9) the frame notions on main (§6).
* (10) tactic hygiene: `<;>`-scoped side goals, and `unfold` first.
* (11) dependencies in the targets.
* (12) PL102 ordered after CR2 item 1 (R9).
* (13) the name clash (R10).
* (14) the `ReadsOnly` mechanism (§7.6).
* (15) the estimate (§7.2).
* (16) the helper count of 206 lines.
* (17) `whileFuel` to the strongest prover.

Fable's claim that the first PL76's hypotheses were "exactly the union" of the two lemmas' was
corrected by B1 below.

**The COMPDYN session, 2026-11-08** (`reports/Review-COMPDYN-ProgLogic.md`): sound with changes.

Blocking, applied:
* **B1**: `hcocells` moved into a guard of the value clause, so both statements are unchanged.
  The rule for correctness-only hypotheses is in §2.2. Resolved from Compress.lean:381–395
  (§7.3).
* **B2**: `spec_kcall`'s writability is under `md.Needs`. The total-only bridges are documented
  (§2.2, ProgramLogicKernels.lean).
* **B3**: canonical `matBlock` blocks, the layout lemmas, and `fp_omega [facts]` (products
  normalised, `Nodup` unfolded, goal-only), tested on the review's goals (§5).
* **B4**: the gates of J1.

Major items:

| item | became a statement | went into the plan |
|---|---|---|
| M1 | `Spec.allocBind` with named states; `Modifies.pop_top`; `St.size_allocate`, `St.writable_allocate`, `St.read_release_of_lt` | J1 gate 3 measures it on Split |
| M2 | `Spec.loopFp`, `RoutineSpec.forRange`, `Spec.bindIdx_of_read`, `spec_eighWhen` | the window bridge (J4) |
| M3 | `RoutineSpec.stmt`/`.ins`, `RoutineSpec.congr`, `Spec.of_normIdx_eq`, the six instruction specifications | — |
| M4 | `IsControlExactSem` with `.mono`; `IsRoutineSem` with `safe` and `p` | — |
| M5 | `CostsLe` with `trans`/`mono`/`of_costs`/`list_sum`; `Spec.withCharge` in both modes | the `bindIdx`-supremum use (J7) |
| M6 | `spec_draw`, `spec_forRange_draw`, `PosKept` | — |
| M7 | — | the estimate revised to 2,350–3,255 lines (§7.2; corrected to the sum of the rows in the delta pass); W3 scheduled with F3 step 2; W3 specifications take `safe` |

Minor items:
* m1: `Spec.ite_cases`.
* m2: the goal-only `fp_omega`.
* m3: `whileFuel` not counted toward S2.
* m4, m5: noted (§5, §6).
* m6: added to J6.
* m7: `Triple.of_agreeOn` deferred until a `RunsWithin.subst` consumer needs it.
* m8: canonical blocks.

**PG9** is recorded as the COMPDYN session's proposal (d).

**Fable delta check of 15b511c0, 2026-11-08**: GO for W0/W1; 38 new or changed statements, 0 false,
0 ill-posed; B1 resolution confirmed. Non-blocking items applied:
* D1: the fact-passing rule for `fp_omega`, in its docstring, in §5 and in PL109's outline.
* D2: the estimate stated as the sum of the §7.2 rows, 2,350–3,255 (19–26%).
* D3 (a): gate 3 has its statement, PL110 `spec_eighSplitBlock_of_body`.
* D3 (b), the coordinator's D4: `spec_forRange_draw`'s outline names the liberal inversion.
