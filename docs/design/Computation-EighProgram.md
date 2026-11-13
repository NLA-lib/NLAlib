# Design note: the bounded index binder, and EIGH as a program (stage COMPDYN S2)

Status (2026-11-08): all 63 statements proved, sorry-free, and in `NLAlib/` (§8, "End-of-stage
status"); the target and tree are in the registry, pending the maintainer's re-pin. Design text,
2026-11-06: Branch `design/compdyn-s2` (worktree `~/nlalib-design-compdyn-s2`),
from `design/compdyn-s1cd` d610ab95 with `cleanup/hdiag` (bd81bd1d, pushed as `feat/hdiag`) merged
(§11). Parent note: `docs/design/Computation-DynamicPrograms.md` (approved, sheet `COMPDYN.json`):
§4.1 data-dependent sizes (Q1, Q2, M1, M2), §4.2 recursion by levels (Q3), §4.6 costs (Q8), §6 the
EIGH sketch (M4 packed blocks, M5 inputs), §7 refinement shape and effort. Pilot: S1c/S1d,
`docs/design/Computation-SignDeflatePrograms.md` (its 65 targets are being proved in a separate
dispatch; this stage cites them). Shallow specification: hdiag's `NLAlib.eigh`
(`NLAlib/Matrix/Computation/SpectralBisection.lean`) and its theorems EV6, EV7, EV8
(`NLAlib/Eigensolvers/SpectralBisection/Global.lean`, EV8 in `…/BoundedFormat.lean`), as tightened
by HDIAG-BOUNDS (EV7' absorbed into EV7). Skeleton: 63 statements, in `NLAlibScaffold/` during
the stage and now in `NLAlib/` (§8) (`~/nlalib-harness/pilot/compdyn-s2-targets.json`) (TT1–TT3 restated against the tightened bounds, §7.4). Decision
sheet: `~/nlalib-harness/state/decisions/COMPDYN-S2.json` (RP, D1 to D7).

This stage finishes what the maintainer asked for on 2026-11-05: [Shah2024]'s Hermitian eigensolver
EIGH as a genuine program of the model of computation, with [Shah2024, Theorem 4.2] proved for the
program.

## 0. Summary

| | |
|---|---|
| S2a (language) | `Stmt.bindIdx p x bound body` / `FStmt.bindIdx`: read the cell `x` once at tag `p`, convert by the new `ScalarSem.toNat` (default `none`), clamp to the index expression `bound`, bind as an index variable; one charged `OpKind.toNat p`. `StaticCost` takes the supremum of the body over the range of the bound (`StaticCost.supRange`). Contracts `IsExactToNat` (the floor of the decoding, $0$ below zero: M1) and, new, `MulShrinks` (§2.3, D4). Every structural site repaired, proved in `NLAlib/` (`--wfail`). Tool: the index normal form `Stmt.normIdx` (§2.4). |
| Statement changes | `exec_subst_sim` and `RunsWithin.subst` gain `htoNat : I'.sem.toNat = I.sem.toNat` (anticipated by §4.1 of the parent note) and `hcostToNat` (the analogue of `hcostCmp`); their one caller, `RunsWithin.substOracle`, discharges both, so its statement is unchanged. No other statement changes (§2.2). Flagged for the maintainer (D5). |
| Re-pin | the second approved re-pin (Q9 (c)): the nine closure hashes change, nothing else (§2.5). Needs the maintainer's sign-off before merge (RP). |
| `eighProg` | One builder, compiled by `rfl` into `NLAlib.eighProg.compiled : Prog P ι 2 4` (sizes $N$; $\ell_0$, $F$). Level arenas for $D + 1 = \ell_0 + 2$ depths, a downward pass of $D$ levels, the spent level, an upward pass of $D$ levels; every node a packed block at word offset $2n^2 d + 2n\,lo$ (M4); sizes, kinds and $k_+$ stored as integer literals and read back by `bindIdx`; tests on sizes by trip counts $0$/$1$ of loops (D2); the sign step inlined from the pilot's test and step blocks with the shallow step limit, so a run never fails for want of steps (D1); static sample positions per level (D3). About 430 lines (`SpectralBisectionProgramTree.lean`), with 300 lines of vocabulary (`SpectralBisectionTape.lean`). No Lean function of data in the tree (F2). |
| Refinement | (a) **partial equality**: under kernels that are routines on pairs, a semantics that decides flags, `IsExactIntLit` up to $N + 4$ and `IsExactToNat`, every successful run writes exactly `NLAlib.eigh (eighTapeMachine I p mmR qrR) F ℓ₀ A R₀ ε β (eighSlotTree …)`; no correctly rounded `fl` is needed (the pilot's finding, §4). (b) **success**: under the standard model with every value in range, $u < 1$, $\ell_0 \ge 1$ and $\varepsilon, R_0 \ge 0$, every run succeeds. |
| Transfer | `NLAlib.MatrixFreeRoundedProbEigh` (proposed target, `NLAlib/RandomMatrix/Computation/SpectralBisectionTargets.lean`): EV6 for the registered tree, via the sampler rewrite and a lazy-sampling lemma (§6); the program forms of EV7 (bits) and EV8 (a bounded binary format, for the runs that succeed, D6), against the tightened bounds (§7.4). Shah's Theorem 4.2 for a program of the model. |
| Skeleton | 63 statements: S 25, M 29, L 8, H 1 (§8). |
| Calibration | S2a: about 350 lines (353 insertions, 56 deletions), proved (estimate 900 – 1,500: below); S2b definitions about 880 lines, statements about 1,850 scaffold lines; S2 projected 7,750 – 9,550 lines, the middle of §7.2's 6,400 – 11,000 for the S2 rows (§10). |

## 1. Files

| File | Content | Lines |
|---|---|---|
| `NLAlib/Computation/{Syntax,Exec,FirstOrder,Compile,Subst,StaticCost}.lean` (amended) | `bindIdx`, `ScalarSem.toNat`, `OpKind.toNat`, `toNatStep`, the run, the bridge, the compiler, `Stmt.subst` and the simulation, `StaticCost.supRange`, the index normal form `Stmt.normIdx` (in `FirstOrder.lean`) | +290 |
| `NLAlib/Computation/{Contract,Exact,Grid,BinaryFloatSem}.lean` (amended) | `IsExactToNat`, `MulShrinks`; `failSem`'s sixth component; `toNat` of `exactSem`, `gridSem`, `binaryFloatSem` | +30 |
| `NLAlib/Estimation/Trace/HutchPlusPlusProgram.lean`, `NLAlibTools/{NumPy,KrylovSmoke,KrylovOracleSmoke}.lean` (amended) | the compile lemma's binder case; the emitter's binder; `toNat` in the smoke tests | +24 |
| `NLAlib/Matrix/Computation/SpectralBisectionProgramTree.lean` (new) | `eighWhen`, `eighEqInd`, `eighSignBlock`, the node blocks, the three levels, `eighProg`, `.compiled`, `eighCount` | 428 |
| `NLAlib/Matrix/Computation/SpectralBisectionTape.lean` (new) | `ScalarSem.tapeUnif`, `uniformUnif`, `eighTapeMachine`, `eighTapeSample`, `eighLoc`, `eighSlotTree`, `eighLevelParams`, `EighArenas` and its predicates, `eighIdealSample`, `eighIdealTree` | 301 |
| `NLAlib/RandomMatrix/Computation/SpectralBisectionTargets.lean` (new, proposed) | `EighData`, `MatrixFreeRoundedProbEigh` | 117 |
| `NLAlibScaffold/` (new files), `NLAlibScaffold.lean` | the skeleton, §8 (removed at the clean-up, 6b757e18; the statements are in the `NLAlib/` files of §8's table) | 1,854 |

## 2. S2a: the bounded index binder

### 2.1 The construct

```lean
-- Stmt                                         -- FStmt (binds index variable `ni`)
| bindIdx (p : P) (x : Cell VB VI) (bound : IExp VI) (body : VI → Stmt P ι VB VI)
-- ScalarSem, a defaulted field (every `where` construction still elaborates)
toNat : P → K → Option ℕ := fun _ _ => none
-- OpKind
| toNat (p : P)
-- the run: one charged conversion, then the body at the clamped value
| .bindIdx p x bound body, st => (toNatStep I p x st).bind fun r =>
    exec (body (min r.1 bound.eval)) r.2
-- StaticCost: the conversion, then the supremum of the body over k ≤ bound
| .bindIdx p _ bound body, ρI => (step (charge (.toNat p))).seq
    (supRange (bound.evalIn ρI + 1) fun k => body.staticCost charge width (Fin.snoc ρI k))
```

As approved (Q1 (a), Q2 (a), OQ1 clamp). `toNatStep` mirrors `cmpStep` (a read, the conversion,
the charge), so the invariants, the bridge and the simulation treat the binder as a comparison
followed by a loop body. `StaticCost.supRange m f` folds `StaticCost.branch` over $f(0), \ldots,
f(m - 1)$, and `StaticCost.Bounds.supRange` is the one new lemma it needs. `Stmt.StraightLine`
excludes the binder (two runs can bind different values).

`IsExactToNat dec sem : ∀ p x, sem.toNat p x = some ⌊dec p x⌋₊` is the separate contract (M1): total,
$0$ below zero, so the program's binder is hdiag's `M.toNat` with no case split. The library's
semantics get the conversion of their decodings: `exactSem` the floor of a real value (failing on a
non-real one, as its comparisons do), `gridSem` the floor of the rounded decoding,
`binaryFloatSem` the floor of the value. `failSem` (an anonymous constructor) gets its sixth
component. Witnesses: §8, BI4 to BI6.

### 2.2 Repairs and statement changes

One case at each structural site of §4 of the parent note: `exec` and its lemma `exec_bindIdx`; the
invariants `runInv_of_exec_eq_some`, `exec_eq_of_exec_eq_some_of_cnt_load_le`,
`shape_usage_eq_of_exec` (vacuous: not straight-line), `Stmt.StraightLine`; `FStmt.exec`, the bridge
`FStmt.exec_eq_exec_toStmt` (with `toNatStep_subst_congr`), `FStmt.exec_bindIdx`; `Stmt.compile`,
`FStmt.toStmt`; `Stmt.subst`, `substKind`, `toNatStep_sim`, `simRun_bindIdx`; `FStmt.staticCost` and
`FStmt.bounds_staticCost_of_exec_eq_some`; the Hutch++ compile lemma `compile_substOracle_cooImpl`;
the tools `KrylovSmoke` (`opcode`, `kinds`, `mem_kinds`, two budget lemmas), `KrylovOracleSmoke` (two
budget lemmas) and the NumPy emitter (`i{ni} = min(max(int(np.floor(x)), 0), bound)`). All proved.

**Statement changes** (D5). The simulation needs the concrete interpretation to convert as the
abstract one and the substituted count to charge a conversion as itself:
* `exec_subst_sim` and `RunsWithin.subst` (result `computation-substitution`) gain
  `htoNat : I'.sem.toNat = I.sem.toNat` (§4.1 of the parent note: "needs `htoNat` … beside
  `hcmp`") and `hcostToNat : ∀ p, cost (.toNat p) = Finsupp.single (.toNat p) 1` (beside
  `hcostCmp` and `hcostRom`).
* Their only caller, `RunsWithin.substOracle` (result `computation-oracle-substitution`), supplies
  both (`by rw [hsem]`, `fun _ => rfl`): **its statement is unchanged**, and so are all of its
  callers'.

Without the two hypotheses `RunsWithin.subst` is false (a binder whose concrete conversion fails),
so the change is forced by the approved Q1 (a); no other statement of the library changes.

### 2.3 `MulShrinks` (D4, in place of M3's correctly rounded `fl`)

`MulShrinks dec sem : ∀ p x y z, sem.bin p .mul x y = some z → |dec p y| ≤ 1 → |dec p z| ≤ |dec p x|`.
The parent note's M3 asked for a correctly rounded `fl` for EIGH. The pilot showed that the equality
refinement needs no contract on the rounding (the machine of a semantics is a function of the stored
operands, §2.2 there), and the only place EIGH needs more than the standard model is the clause
$\lvert \overline{\mathrm{unif}(s, v)} \rvert \le \bar s$ of `NLAlib.IsUnifSampler`: the shift
$\mathrm{fl}(s\rho(v))$ must stay in the window. `MulShrinks` is exactly that clause, true of every
monotone rounding exact on stored values (IEEE, `gridSem`: BI8), and weaker than correct rounding.

### 2.4 The index normal form

The pilot's run lemmas of the kernels are stated at constant sizes (`.const n`). Inside `eighProg`
every size is an index variable bound by a binder or a loop. `Stmt.normIdx` replaces every index
expression, under every binder, by the constant of its value; `exec_normIdx` (M) says a statement
runs as its normal form, and `exec_eq_of_normIdx_eq` turns it into ten one-line congruences
(`exec_zcopy_congr`, …, `exec_newtonSchulzStepBlock_congr`), each a normal-form computation. This
is a general tool: any later program that calls a kernel at a computed size uses it.

### 2.5 The re-pin

By the documented path, run into a copy of the registry (`TARGETS_REGISTRY`) so that the diff could
be checked first: `TARGETS_UPDATE=1 lake env lean scripts/Targets.lean`. Only the nine target
closure hashes changed (the `ScalarSem` field, the `OpKind` and `Stmt`/`FStmt` constructors are in
every target's closure); the seven tree hashes, the printed statements and normal forms and the
toolchain, Mathlib and manifest pins are unchanged. The tool also rewrote the `lakefile_sha256` pin
to the lakefile with the scaffold entry; that line was restored, as in S1 (the pin matches again
once the clean-up removes the scaffold library). The registry was then replaced by the checked copy
and `docs/targets.approved` rewritten (`sha256sum`), under the approval of Q9 (c), pending the
maintainer's sign-off (RP):

| target | old closure hash | new closure hash |
|---|---|---|
| `MatrixFreeGramSchmidt` | `af26a2cc59a18852…` | `803740ecf5bda027…` |
| `MatrixFreeHutchpp` | `f30f4f842aac163e…` | `6cb6c7ef3a3e0b94…` |
| `MatrixFreeProbHutchpp` | `d9a85ec8490dc567…` | `f15f97400d04881e…` |
| `StoredEntriesDenseHutchpp` | `771e016ca68b29ac…` | `f875bf2c0626616d…` |
| `StoredEntriesCooHutchpp` | `62fcf12585da26e2…` | `25b9142e7748322f…` |
| `StoredEntriesConjugateGradient` | `74f03a01c2627964…` | `fe5dfa37a8a75b53…` |
| `StoredEntriesLanczos` | `3067f8e5a70ba8b5…` | `9c35bcc669cc4c91…` |
| `MatrixFreeConjugateGradient` | `d22d5e3483281f66…` | `381197470600e824…` |
| `MatrixFreeLanczos` | `903a3da3d2951891…` | `c4744e2b3f3edef4…` |

New `docs/targets.approved`: `bc9f33e5dd503e2ad18281e360f466b1745660608dc7f7fafb94efb7f31b84f8`. The old
hashes are those of the S1 re-pin (`7bff66e4…` approved).

## 3. EIGH as a program

### 3.1 Interface (§6.1 of the parent note, M5)

`eighProg.compiled p mm qr : Prog P ι 2 4`. Sizes: $N = n$ (index $0$), the depth counter $\ell_0$
and the sign step limit $F$. Declared buffers: $0$ the matrix ($2n^2$ words, interleaved,
column-major), $1$ the stored $R_0$, $\varepsilon$, $\beta$, $2$ the output $\mathbf{U}$ ($2n^2$
words), $3$ the eigenvalues ($n$ cells). Kernel names `mm`, `qr`.

### 3.2 Layout

The nodes of depth $d$ partition a part of $[0, n)$ into ranges $[lo, lo + k)$
(`eighLoc_bounds`, `eighLoc_disjoint`); the node at $[lo, lo + k)$ is stored at **slot** $lo$ of
level $d$. Arenas, one level per depth $0, \ldots, D$ ($D = \ell_0 + 1$): node matrices `Ma`,
outputs `Ua`, bases `Qa` (complex $n \times n$ blocks: the node's $k \times k$ block at word
$2n^2 d + 2n\,lo$, packed, disjoint across a level since $k^2 \le kn$, M4), eigenvalues `Ea`, sizes
`Sz`, kinds `Kd`, splits `Kp` ($n$ cells per level), windows and tolerances `Lv` (two cells per
level). Memory $O(n^2 \ell_0)$, a function of the sizes.

### 3.3 The passes

* **Initialisation**: the constants $1$, $\mathrm{fl}(2)$ (`litIdx 2`, hdiag's `M.ofNat 2`),
  $\mathrm{fl}(1/2) = \mathrm{fl}(1/\mathrm{fl}(2))$, $-1$ and the stored $\sqrt{1/2} =
  \mathrm{fl}(\sqrt{\mathrm{fl}(1/2)})$ (`ScalarSem.sqrtHalf`, the square root of cell $2$; cells
  $0$ to $4$ of `c`); every size cell the literal $0$, the root's $n$; $\mathbf{A}$, $R_0$,
  $\varepsilon$ at depth $0$.
* **Downward level** $d < D$ (`eighDownLevel`): the next window and tolerance exactly as
  `eighNextParams` at $\ell = \ell_0 + d$; the level's $n$ uniform and $4n^2$ Gaussian draws; for
  each slot, the stored size (a binder clamped to $n - lo$) and, for $k \ge 1$, a leaf when $k \le 1$
  (identity, diagonal real parts) or when $R \le \mathrm{fl}(\varepsilon R_0)$ (one counted
  comparison; identity, zeros), else the node step.
* **Node step** (`eighNodeBlock`, `NLAlib.eighStep` line by line): $\sigma = \mathrm{fl}(R/\mathrm{fl}(2))$,
  the shift $c = \mathrm{fl}(\mathrm{fl}(R/\mathrm{fl}(\ell))\,v)$ from the node's seed, $\mathbf{W} =
  \mathbf{A} - c\mathbf{I}$, the sign at $(\beta, \mathrm{fl}(\mathrm{fl}(2)R))$ (`eighSignBlock`), the
  projectors, the rounded trace $t$ and $k_+ = \min(\lfloor\mathrm{fl}(t + \mathrm{fl}(1/2))\rfloor_+,
  k)$ **by a binder**; then one child (positive side if $k_+ = k$, negative if $k_+ = 0$) or a split:
  deflation on the stored samples (`eighDeflateBlock`: $\widetilde{\mathbf{G}}$ from the level's
  Gaussian words times the stored $\sqrt{1/2}$ of cell $4$ of `c`, read only, `mm`, `qr`, the first
  $r$ columns), the two
  compressions (`eighCompressBlock`), the children's sizes, the kind and $k_+$.
* **Spent level** $D$ (`eighBottomLevel`): every node gets $(\mathbf{I}, \mathbf{0})$, `eighAux` at
  budget $0$.
* **Upward level** $d = D - 1, \ldots, 0$ (`eighUpLevel`): by the stored kind (a binder clamped to
  $4$), a one-child node copies its child's $\mathbf{U}$ and adds $\pm\sigma$; a split reads $k_+$
  and writes $\mathrm{mm}(\mathbf{Q}_+, \mathbf{U}_+)$, $\mathrm{mm}(\mathbf{Q}_-, \mathbf{U}_-)$
  into the two column blocks of its output (column-major, so `Matrix.fromCols` reindexed by
  `finSumFinEquiv` is the concatenation of the two packed blocks) and the shifted eigenvalues.
* **Output**: the root's $\mathbf{U}$ and eigenvalues copied to buffers $2$, $3$.

### 3.4 Choices

* **D1, the sign step never fails.** The pilot's `newtonSchulzSignProg` runs `whileFuel (F + 1)` and
  fails when no iterate passes; hdiag's `newtonSchulzLoop F` returns the $F$-th iterate. Inside EIGH
  a failure would make success depend on a statement the HDIAG stage has not made (the pilot's TR1,
  that the test passes within $N_* + 1$ steps, at every node), and the transfer would need the
  probability of that event, which hdiag bounds only inside the proof of EV6. `eighSignBlock` reuses
  the pilot's set-up, test and step blocks (`newtonSchulzTestBlock`, `newtonSchulzStepBlock`) and
  replaces the loop by $F$ iterations of "if the flag is set, step and test" (one counted comparison
  each): exactly `newtonSchulzLoop`, so the program **succeeds on every run** under the standard
  model and the transfer is a direct application of the shallow theorems. Cost: $F$ comparisons per
  node, the steps only while the test fails.
* **D2, tests on sizes by trip counts.** `eighWhen e b` is `forRange (1 - (1 - e)) fun _ => b`, which
  runs $b$ once if $e \ge 1$ and never otherwise (truncated subtraction); `eighEqInd c m` is the
  indicator of $c = m$. Loop bounds are index expressions, free in the model as every loop's, and no
  new construct is added (OQ8 stays closed). The alternative, comparing stored sizes by `ite` on
  cells, would need a comparison contract in the equality refinement.
* **D3, static sample positions.** Every downward level draws exactly $n$ uniform and $4n^2$
  Gaussian values, whatever the data. So the node at slot $lo$ of depth $d$ reads its seed at uniform
  position $nd + lo$ and entry $(i, j)$ of its test matrix of side $s$ at the complex sample
  $2n^2 d + n(2(lo + j) + s) + i$ (`eighTapeSample`), independent of every other node's. A program
  that drew only what each node uses ($1 + 4k^2$ per split) would read data-dependent positions, and
  the lazy-sampling argument would have to follow the draw counter through the run. Cost: $O(n^2)$
  draws per level, within the $O(T_{\mathrm{MM}}(n))$ of the level.

## 4. The refinement (§7.1 of the parent note)

The machine of a run is `eighTapeMachine I p mmR qrR`: the machine of the semantics
(`ScalarSem.toFloatMachine`), its conversion the semantics' (`none` read as $0$), its black boxes
the kernel routines, its samplers reading the stored tape at a position (`ScalarSem.tapeUnif`,
`ScalarSem.tapeNormal`); seeds and Gaussian samples are positions (`Su = Sg = ℕ`). The tree of
samples is `eighSlotTree M n F R₀ β 0 0 root`, the positions of each node's slot along the shallow
recursion.

* **(a) Partial equality** (`holds_of_exec_eighProg`, `eighProg.holds_of_exec_compiled`):
  kernels that are routines on pairs (`IsMatMulKernel`, `IsQRKernel`), `DecidesFlags` (the sign
  flag), `IsExactIntLit dec I.sem (N + 4)` and `IsExactToNat dec I.sem` (sizes and kinds read back
  through cells, M1, M2) ⟹ every successful run ends with buffers $2$, $3$ holding exactly
  `eigh M F ℓ₀ A R₀ ε β (eighSlotTree …)`. No contract on the rounding.
* **(b) Success** (`exists_exec_eighProg`, `eighProg.exists_exec_compiled`): the standard model at
  $u$ with every value in range, $u(p) < 1$, the two exactness contracts, routines on pairs,
  $\ell_0 \ge 1$ and $\bar\varepsilon, \bar R_0 \ge 0$ ⟹ every run succeeds: every division is by
  $\mathrm{fl}(2)$, $\mathrm{fl}(\ell)$, $\mathrm{fl}(4k)$ or $\mathrm{fl}(2R) \ne 0$ at a node whose
  window test failed, the sign step never fails (D1), the conversion is total.

The proof follows the levels: the arenas hold the nodes of a depth (`EighArenas.LevelHolds`), the
downward level produces the next depth and the records of the node steps (`RecordHolds`), and the
upward level turns the outputs of depth $d + 1$ into those of depth $d$ (`OutHolds`, `eighAux` with
the remaining budget). The vocabulary of the recursion is `eighLoc` (slot and node at a path) with
its lemmas ET1 to ET6.

## 5. Counts (Q8)

* **Static** (`eighProg.cnt_le_of_exec_compiled`): at most `eighCount p mm qr N ℓ₀ F`, which charges,
  per slot visit, the kernel calls of a node of every size $k \le N$ and every split $k_+ \le k$
  (the supremum of `bindIdx` is bounded by the sum), and $1024(F + 2)(\ell_0 + 2)(N + 1)^3$ of each
  scalar kind; peak memory $64(N + 1)^2(\ell_0 + 3)$ cells. Sound for every successful run under every
  semantics, loose by about $N^2$ on the kernels (§4.6 of the parent note).
* **Weighted** (`eighProg.weight_le_of_exec_compiled`, L): for a monotone superadditive cost $T$ of a
  kernel call by its largest dimension (a convex $T$ with $T(0) = 0$), the weighted kernel count is
  at most $(\ell_0 + 1)(2F + 12)\,T(N)$: per level the node sizes sum to at most $N$, each node making
  at most $2F + 12$ calls. This is the operation count of [Shah2024, Theorem 4.2], proved by an
  invariant of the run, not by `StaticCost`.

## 6. Samples (§7.1, the lazy-sampling lemma)

* **Positions to values** (`eigh_eighTapeMachine_eq_eigh_eighIdealTree`, L): for a tape
  $\rho \circ \xi$ with $\rho$ independent of the position (as the pilot's DEFLATE target, D7
  there), `eigh` on the tape machine with the slot tree equals `eigh` on the **ideal machine**
  (samplers `ScalarSem.uniformUnif`, `ScalarSem.gaussianNormal` of $\rho$) with the tree of ideal
  samples `eighIdealTree`: the static positions of each existing node at depth below $D$, on its seed
  and leading block, and positions beyond the program's draws, indexed by the path, elsewhere. Two
  general lemmas: `eigh` sees samples only through the samplers (ES1) and only at the nodes it
  reaches (ES2).
* **Lazy sampling** (`iIndepFun_eighIdealTree`, H): on the ideal tape the ideal tree is independent
  with law `eighSampleLaw` at every path. The positions a node reads are decided by earlier samples
  and disjoint from every other node's. The only H of the stage: a general lemma about adaptively
  chosen disjoint blocks of an i.i.d. sequence, then this instance; hdiag's
  `countable_range_eighNodeAt`, `measurableSet_eighNodeAt_eq` give the measurability.
* **The ideal machine is accurate** (`isAccurate_eighIdealMachine`): the pilot's IM1 and IM3 with
  `isUnifSampler_uniformUnif` (from `MulShrinks`), at the machine roundoff
  $u_{\mathrm M} = (c(\mathrm{uniform}) + 1)u$ and $c_{\mathrm N} = 2(c(\mathrm{gaussian}) + 3)$, when
  the tape range covers the seeds, $1 \le 2\Omega$ (Fable review: without it the tape contract does
  not constrain the rounding of a seed, and the statement fails at $\Omega = 0$); the targets' `pre`
  gives $\Omega \ge 160$.

## 7. Transfer: Theorem 4.2 for the program

### 7.1 The target

`NLAlib.MatrixFreeRoundedProbEigh` (`MatrixFreeRoundedProb` of the registered tree): for every
interpretation meeting the standard model at $u$ with every value in range, `IsExactIntLit` up to
$N + 4$, `IsExactToNat`, `MulShrinks`, and kernels meeting `IsMatMulErr`, `IsQRErr` at $u$, floor
$0$, range $\Omega$; every tape rounding meeting `IsTapeRounding` at range $2\Omega$, independent of
the position, with countable ranges and measurable fibres; and the hypotheses of EV6 at
$u_{\mathrm M}$ and $c_{\mathrm N}$: the probability that the run fails or returns no approximate
diagonalization with residual $2\varepsilon R_0$ and $\mathbf{U}$ within $\varepsilon/3$ of unitary is
at most $\theta$. Proof `matrixFreeRoundedProbEigh` (M): (b), (a), §6, EV6. Its contracts are
satisfiable: `gridSem` meets the four semantic contracts (`isRelErrSem_gridSem`,
`isExactIntLit_gridSem`, BI5, BI8), up to one bridge: `isExactIntLit_gridSem` is stated at the
identity decoding, the others at $x \mapsto \mathrm{fl}_p(x)$, so a two-line restatement at the grid
decoding is needed before a non-vacuity witness of the whole hypothesis set (with `exactMM`,
`exactQR`, `isTapeRounding_id`) can be a theorem (Fable review, later). The S2 statements cite the
pilot's S1c/S1d statements, sorried here; the S2 merge waits for S1cd to land.

### 7.2 EV7: the bit count

`matrixFreeRoundedProb_eighProg_of_logb_le` (M): the same model with EV7's two precision
conditions (`hbits`, `hbits'`) at $u_{\mathrm M}$ and $\beta$ in EV7's window
$\hat\beta/(1 + 2^{-6}) \le \beta \le \hat\beta$: $\log_2(1/\varepsilon) +
\tfrac32\log_2(1/\theta) + O(\log n + \log\log(1/\varepsilon))$ bits for the program, with
$n^{2.5}\max(\mu_{\mathrm{MM}}, \sqrt n)$ in place of the earlier $n^5\mu_{\mathrm{MM}}$.

### 7.3 EV8: a bounded binary format (D6)

`measureReal_exists_exec_eighProg_and_not_isApproxDiagonalization_le_of_exponentBits_le` (M): for every
interpretation whose semantics meets the floor model `IsFloorRelErrSem` at the constants of a binary
format (unit roundoff $2^{-p}$, floor the smallest normal number, range the largest finite number
$\Omega_F$), with `MulShrinks`, exact literals up to $N + 4$, the exact floor conversion, stored
values in range, kernels at range $\Omega_F/2$ and a tape rounding at range $\Omega_F$, the
probability that the run **succeeds** and its output is bad is at most $\theta$, under EV8's
hypotheses at the machine roundoff $u_{\mathrm M} = (c(\mathrm{uniform}) + 1)2^{-p}$. The ideal
machine's `IsAccurate` is no longer a hypothesis: `isAccurate_eighIdealMachine_floor` derives it
(floor $\tau$ kept, range halved for the normal sampler, $c_{\mathrm N} = 3(c(\mathrm{gaussian}) +
3)$), and `binaryFloatSem` (with its square root) meets the scalar contracts
(`isFloorRelErrSem_binaryFloatSem`, `mulShrinks_binaryFloatSem`, `isIndexExactSem_binaryFloatSem`).
Before, the hypothesis was the machine's `IsAccurate` at the format's constants, and
`binaryFloatSem` had no square root, so every run failed and the event was empty. Success is still
not claimed: `binaryFloatSem` fails out of range, and hdiag does not show that every operation of a
run stays in range (its contract `IsRoundingOf` constrains nothing out of range). The full form
needs that range analysis (D6).

### 7.4 Restatement against the tightened HDIAG bounds

On merging main (HDIAG with the tightened EV6/EV7/EV8, PR #67's $n \ge 1$), TT1–TT3 were restated
as listed in `Review-Fable-HDIAG-Bounds-Stage.md` ("S2 restatements"): TT1 takes $\beta \le
\hat\beta$, $N_*$ at $\theta/(12n\ell(\ell + 1))$, $146n\ell(\ell + 1)\nu u_{\mathrm M} \le
\theta\beta$, the stopping condition $2048(n + N_* + 1)\nu u_{\mathrm M} \le \beta$, deflation
with the factor $16$ and the new range; TT2 takes the former TT4's hypotheses (EV7 verbatim), and
TT4 with its file `SpectralBisectionProgramSharp.lean` is deleted; TT3 takes EV8's window, $N_*$,
`hbits`, `hbits'` and the cube in `hexp`; all three take $1 \le N$.

### 7.5 Placement

The target definition is in `NLAlib/RandomMatrix/Computation/` (layer 2, where `MatrixFreeRoundedProb`
is, as the pilot's D1); its proof and the samples file import `NLAlib/Eigensolvers` and live there
(`NLAlib/Eigensolvers/SpectralBisectionSamples.lean`, `…/SpectralBisectionProgram.lean`). The
`Eigensolvers` folder has no LAYER entry yet (board T105, maintainer): `check_rules` P1 reports those
files, expected. Registration (D7): one `[[target]]` and one `[[tree]]` in `docs/targets.toml` by
the maintainer once the proof exists. (Done, pending the re-pin: §8, "End-of-stage status".)

## 8. Skeleton

63 statements, S 25, M 29, L 8, H 1, in `~/nlalib-harness/pilot/compdyn-s2-targets.json` (waves
0 to 10). External dependencies: the pilot's statements (PK, PP, IM, SG, LP of
`Computation-SignDeflatePrograms.md`), cited by name; they are being proved now.

| ids | statements | file (`NLAlib/…`; `NLAlibScaffold/…` during the stage) | difficulty |
|---|---|---|---|
| BI1–BI3 | `exec_bindIdx_of_read`, `exec_bindIdx_eq_none`, `IsExactIntLit.toNat_eq_of_lit_eq_some` | `Computation/IndexBinder.lean` (BI3 in `Computation/Contract.lean`) | S |
| BI4–BI8 | `isExactToNat_{exactSem,gridSem,binaryFloatSem}`, `mulShrinks_exactSem`, `mulShrinks_gridSem` | `Computation/Contract.lean` (`exactSem`), `Computation/Grid.lean` (`gridSem`), `Computation/BinaryFloatSem.lean` | S ×4, M |
| NI1, NI2 | `exec_normIdx`, `exec_eq_of_normIdx_eq` | `Computation/IndexBinder.lean` | M, S |
| EC1–EC10 | `exec_{zcopy,zidentity,zneg,zconjTranspose,zhermShift,zhermScale,zhermAvg,ztraceRe}_congr`, `exec_newtonSchulz{Test,Step}Block_congr` | `Computation/BLASCongr.lean` (EC1–EC8), `Matrix/Computation/NewtonSchulzSignProgram/Blocks.lean` (EC9, EC10) | S |
| SB1–SB3 | `holds_of_exec_eighSignLoop`, `holds_of_exec_eighSignBlock`, `exists_exec_eighSignBlock` | `Matrix/Computation/SpectralBisectionNode/SignStep.lean` | M |
| EN1–EN10 | leaf, child, deflate (value, success), compress (value, success), split (value, success), node (value, success) | `Matrix/Computation/SpectralBisectionNode/{Deflate,Compress,Split,SplitSuccess}.lean`, node value in `SpectralBisectionNode.lean`, node success in `…/NodeSuccess.lean` | M, S, M, M, M, M, M, M, L, M |
| ET1–ET6 | `eighNodeAt_eighSlotTree`, `eighSlotTree_append_of_eighLoc`, `eighLoc_params`, `eighLoc_append_singleton`, `eighLoc_bounds`, `eighLoc_disjoint` | `Matrix/Computation/SpectralBisection/Levels.lean` | M |
| EL1–EL6 | down level (value, success), spent level (value, success), up level (value, success) | `Matrix/Computation/SpectralBisectionProgram/{DownLevel,DownLevelSuccess,BottomLevel,UpLevel,UpLevelSuccess}.lean` | L, L, M, S, L, M |
| EP1–EP7 | builder (a), (b); tree: `toStmt_compiled`, (a), (b), static counts, weighted counts | `Matrix/Computation/SpectralBisectionProgram/Refinement.lean` (EP1), `Matrix/Computation/SpectralBisectionProgram.lean` (EP2–EP5), `…/SpectralBisectionProgram/Count.lean` (EP6), `…/Weight.lean` (EP7) | L, L, S, S, S, M, L |
| ES1–ES4 | `eigh_toFloatMachine_map_samples`, `eigh_congr_samples`, `eigh_eighTapeMachine_eq_eigh_eighIdealTree`, `iIndepFun_eighIdealTree` | `Eigensolvers/SpectralBisectionSamples.lean` (ES1–ES3), `…/SpectralBisectionSamples/Lazy.lean` (ES4) | M, M, L, H |
| IA1–IA4 | `isUnifSampler_uniformUnif`, `isAccurate_eighIdealMachine`, `countable_range_uniformUnif`, `countable_range_gaussianNormal` | `Eigensolvers/SpectralBisectionSamples/IdealMachine.lean` | M, M, S, S |
| TT1–TT3 | `matrixFreeRoundedProbEigh`, `matrixFreeRoundedProb_eighProg_of_logb_le`, the bounded format | `Eigensolvers/SpectralBisectionProgram.lean` | M |

**Statement fix (SB2).** `holds_of_exec_eighSignBlock` now takes `hX : ∃ len, st.store.shape[X]? =
some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len`, as SB3 and the pilot's SG6/SG7 (the pilot's SG6
and DF2 were false without it: the output block could be one of the scratch buffers that the
`scope` pops). Its one caller, EN9 `holds_of_exec_eighNodeBlock`, supplies it from the allocation
of `B` ($2k^2$ cells at tag `p`); EN9's statement is unchanged.

**Statement fix (EN7).** `holds_of_exec_eighSplitBlock` was false: the split writes the cell `sq`
(the stored $\sqrt{1/2}$, a division then a square root), which lies outside the arenas, while the
frame claimed every cell outside depths $d$, $d + 1$ unchanged. Counterexample: any successful run
(they exist, EN8) from a state where the cell `sq` is uninitialised (`none`, e.g. a freshly
allocated scratch cell, as at its one use in `eighNodeBlock`) ends with `sq` holding
$\mathrm{fl}(\sqrt{\mathrm{fl}(1/2)})$. A second defect: if `sq` is the cell `two` (or `one`,
`sg`, `nsg`), the compressions use $\sqrt{1/2}$ in place of $\mathrm{fl}(2)$ and the value claims
fail. Fix: the frame exempts the cell `sq`; new hypotheses `hsqc` (the cells `one`, `two`, `sg`,
`nsg` differ from `sq`) and `hcl` (the five cells lie in existing buffers, so that the split's
scratch allocations cannot alias them). EN7 has no callers (EN9 uses the private precise form), so
nothing downstream changes. *Superseded by the program change below: the weakening is gone.*

**Program change (the hoist of $\sqrt{1/2}$; Fable audit, `Audit-Fable-Corrections.md` item 10).**
`eighProg` computes $\mathrm{fl}(\sqrt{\mathrm{fl}(1/2)})$ once, into a fifth constants cell
(`c` has $5$ cells; `ins (.un p .sqrt ⟨c, 4⟩ ⟨c, 2⟩)` right after the other constants), and passes
it down as a read-only cell: `eighDownLevel` and `eighNodeBlock` take a new last cell argument
`sqh` (instantiated `⟨c, 4⟩`), `eighSplitBlock` reads it as `sq` and no longer contains
`div sq one two; sqrt sq sq` (its now unused argument `one` is dropped), and the node's scratch `t`
shrinks from $8$ to $7$ cells. The rounding sequence is unchanged: cell $2$ is
$\mathrm{fl}(\mathrm{fl}(1)/\mathrm{fl}(2))$ from the same literals at the same tag, so cell $4$ is
exactly `ScalarSem.sqrtHalf p`, the value every split computed before, and the deflations multiply
the same Gaussian words by the same stored value; the equality refinement to hdiag's `eigh` (EP1,
`eighTapeMachine`'s `tapeNormal`, which uses `sqrtHalf`) is untouched. Each split saves a division
and a square root; the run adds one square root in total. `eighProg.compiled` still compiles by
`rfl`; the static bound `eighCount` is unchanged (EP6's `decide +kernel` re-run).

**EN7 strengthened (the weakening removed).** `holds_of_exec_eighSplitBlock` now has the plain arena
frame, "every cell outside depths $d$, $d + 1$ of the arenas is unchanged", with no exemption of
`sq` and no `hsqc`; `sq` is a hypothesis cell like the others: `hsq : st.store.read p sq.buf
sq.idx.eval = some (I.sem.sqrtHalf p)`, with `hcells` over `[two, sg, nsg, sq]`. `hcl` is gone too
(every one of the four cells is read with a value, so it lies in an existing buffer), as are `one`
and `hone`. `htwo` now states the value, `= some (M.ofNat 2)` (it was `= I.sem.lit p 2`, whose
`some` the deleted division used to supply; the new form covers that case and no longer needs the
literal to exist). Follow-on restatements, forced by the new signatures: EN8 `exists_exec_eighSplitBlock`
(no `one`/`hone`; `hsq` is the read above instead of "the cell `sq` is writable"); EN9, EN10
(the node block takes `⟨c, 4⟩`; `hc` gains `st.store.read p c 4 = some (I.sem.sqrtHalf p)`);
EL1, EL2 (the same fifth conjunct of `hc`, and `⟨c, 4⟩`). EP1, EP2 and the tree theorems are stated
on `eighProg` and do not change; EP1/EP2 supply the fifth conjunct from the initialisation.

**Statement fix (EL1).** `holds_of_exec_eighDownLevel` now takes `hnext : ∀ lo < n, ReadsIdx
I.sem st.store p H.Sz (n * (d + 1) + lo) 0`: the size cells of depth $d + 1$ start at $0$. Without
it the statement was false, since `NLAlib.EighArenas.LevelHolds` at $d + 1$ asks every slot that
starts no node to read $0$, and the level writes only the size cells of the children. Counterexample:
$n = 1$, $d = 0$, $D = 1$, the root of size $1$ (a leaf), the initial cell $1$ of `Sz` the literal
$1$: no node is at depth $1$, the run writes no size cell, so cell $1$ still reads $1$. The caller
EP1 `holds_of_exec_eighProg` supplies it without a change of statement: the initialisation writes
$0$ to every size cell and then $n$ to cell $0$ only, and level $d$ writes only cells of depths $d$
and $d + 1$ (its frame), so the downward loop's invariant carries "the size cells of every depth
$e > d$ read $0$". EL2 `exists_exec_eighDownLevel` does not need it and is unchanged.
The proof also needed a finer frame of the node step: the helper (not a target)
`holds_of_exec_eighNodeBlock_frame` now says that of the size cells of depth $d + 1$ in the node's
range only the children's slots ($lo$, and $lo + k_+$ for a split) may change; EN9's statement is
unchanged.

**Statement fix (EP7).** `eighProg.weight_le_of_exec_compiled` now takes `hlit : IsExactIntLit dec
I.sem (N + 4)` and `htn : IsExactToNat dec I.sem` (Fable audit item 12). Without them it is false:
with `lit 0` decoding to $1 + \delta$ every slot reads back a size $\ge 1$, the binder's clamp gives
$n - lo$, and a level makes $\Theta(n^2)$ kernel work. The sizes, kinds and $k_+$ are control data in
rounded cells, so every data-dependent count is conditional on the literal round-trip; EP6 (static)
stays semantics-free by charging the supremum. The contracts are those of TT1's `Contracts`.

### Hypotheses strengthened for proof convenience (statement believed true as originally written)

**EL2 `exists_exec_eighDownLevel`** now takes the constants as EL1 does (cell $2$ of `c` holds
$\mathrm{fl}(1/\mathrm{fl}(2))$ of the machine and cell $3$ holds $-1$, instead of some value each)
and EL1's tape positions `hpos` ($nd$ uniform, $4n^2 d$ Gaussian). The weaker version is believed
true, but its proof needs a frame of each node step (the later slots read sizes and blocks of
depth $d$ that an earlier node step must not change), and the only frame available,
`holds_of_exec_eighNodeBlock_frame`, comes with the value statement and needs the exact constants
and the samples at their tape positions; a frame-only node lemma would duplicate the node-step
proof. EP2 `exists_exec_eighProg` supplies both without a change of statement: `eighProg`
computes cell $2$ as $\mathrm{fl}(1/\mathrm{fl}(2))$ and cell $3$ as $-1$ from the literals $1$ and
$2$, and every level advances the tape positions by $n$ and $4n^2$ (EL1).

**EP2 `exists_exec_eighProg`** now takes `hpos : st.pos .uniform = 0 ∧ st.pos .gaussian = 0` (the
tape positions at $0$, as EP1). The statement without it is believed true, but its proof goes
through EL2, whose `hpos` asks the exact tape positions $nd$ and $4n^2 d$ at level $d$ (above); the
downward loop gets them from the positions at $0$ and EL1's advance by $n$ and $4n^2$ per level.
Its one caller, EP5 `eighProg.exists_exec_compiled`, supplies it from `inputState` (tape positions
$0$, as EP4 does for EP1); EP5's statement is unchanged, and TT1–TT3, which call EP5, are untouched.
The proof does not use `hbufs` (success does not need the four buffers distinct). It also needs the
finer frame of EL1's proof: of the cells of depth $d$ only the records (bases, outputs,
eigenvalues, kinds, splits) change, so the sizes, node matrices and parameters of every depth
survive to the upward pass, whose level $d$ reads them (`NLAlib.EighArenas.LevelHolds` at $d$).
That is the private `ep2_holds_of_exec_eighDownLevel` (EL1's proof, with the frame stated finer),
of which EL1 is now a corollary; EL1's statement is unchanged.

**EP1 `holds_of_exec_eighProg`**: proved with its statement unchanged (no hypothesis added). It
supplies EL1's `hnext` and the five constants of `hc` from the initialisation, as the outline says
(the downward loop's invariant carries "the size cells of every depth $e > d$ read $0$"), and it
uses EP2's private `ep2_holds_of_exec_eighDownLevel` (EL1's proof with the finer frame) for the
same reason as EP2: the upward level $d$ reads `NLAlib.EighArenas.LevelHolds` at $d$, which
EL1's stated frame does not keep through level $d$ itself. The private `ep1_` helpers split the
proof into the downward pass, the spent level with the upward pass, and the body after the eleven
allocations (`ep1_prog_eq` states the tree of the scope by `rfl`), so that each piece elaborates
within the 4 GB worker limit.

### End-of-stage status (2026-11-08, `cleanup/compdyn-s2`)

**Proved.** All 63 statements are proved, with no `sorry`. The dispatch (2026-11-07 00:11–03:34)
proved 50; the other 13 (EN6, EN7, EN9, EN10, EL1, EL2, EL5, EL6, EP1, EP2, EP6, EP7, ES4) were
proved by follow-up agents on `prove/compdyn-s2-*` branches and integrated on `integrate/compdyn-s2` (ES4) and
`integrate/compdyn-s2-final` (the others), with the statement fixes and strengthenings above. TT1–TT3 were
restated against the tightened HDIAG bounds (§7.4) at the merge of `origin/main` (5960c3fa) and
proved there by composing EP1/EP2 and the refinement with the new EV6, EV7, EV8; `#print axioms`
at that commit gave `propext`, `Classical.choice`, `Quot.sound`.

**Hardening.** The hardening stage (`docs/design/Computation-Hardening.md`, Stage 2b) then changed
the environment under the program: `bindIdx` fails above its bound, `toNat` fails below $0$, and
`Prog.RunsWithin` asks `st₀.store.size = b`. The one site of `eighProg` that relied on the old
clamping binder is the split index $\lfloor\mathrm{fl}(t + \mathrm{fl}(1/2))\rfloor$: the node step
now runs an explicit, counted clamp `NLAlib.eighClampBlock` before its binder (two literals into
dead cells of `t`, two comparisons, at most one copy), proved in
`Matrix/Computation/SpectralBisectionClamp.lean` (`exec_eighClampBlock_bind`; 40926974). The
shallow `eighStep` is unchanged (`kp := min k (M.toNat …)`), so the equality refinement to `eigh`
is the same statement. As recorded in that commit, the value-side lemmas from the node step up to
`eighProg.holds_of_exec_compiled` gain `hcmp` (the comparison `le` exact at `dec`) and the node
lemmas the exactness of literals up to the node size; TT1 and TT2 discharge `hcmp` by
`hsem.cmp_le`, TT3 takes it as a hypothesis. EP6's constants are unchanged (re-checked by kernel
`decide`); EP7 is unchanged. TT1–TT3 then take the model's new arguments `dec B cost mem`, with
`B := N + 4`, `cost := eighCount p mm qr N ℓ F` and `mem := 4N² + N + 3 + 64(N + 1)²(ℓ + 3)`
(`Computation-Hardening.md` §2.3, §2.4; b228ea6f). Fable's review of Stage 2b
(`reports/Review-Fable-Hardening-Stage2.md` §3) checked the clamp: counted, exactly refined, and
not a weakening.

**Where it lives.** The statements moved from `NLAlibScaffold/` into `NLAlib/` (D8: docstrings
without `Proof:` lines) and the large files were split (F10), with statements unchanged:
36d32068 (the Computation lemmas: `Computation/{Loops,IndexBinder,BLASCongr}.lean`, and
`Contract`, `Grid`), 10b17ab6 (SIGN/DEFLATE, see `Computation-SignDeflatePrograms.md`), bb7ccf8f
(EIGH: `Matrix/Computation/SpectralBisectionNode.lean` and 7 files under
`SpectralBisectionNode/`, `Matrix/Computation/SpectralBisectionProgram.lean` and 13 files under
`SpectralBisectionProgram/`, `Matrix/Computation/SpectralBisectionClamp.lean`,
`Eigensolvers/SpectralBisectionSamples.lean` with `SpectralBisectionSamples/{Lazy,IdealMachine}.lean`,
and `Eigensolvers/SpectralBisectionProgram.lean`). The table above gives the file of each id.
6b757e18 removed `NLAlibScaffold`; `lakefile.toml` is main's byte for byte, and the elaborated
types of all 865 scaffold constants are identical in `NLAlib`. The definitions of §1
(`SpectralBisectionProgramTree.lean`, `SpectralBisectionTape.lean`,
`RandomMatrix/Computation/SpectralBisectionTargets.lean`) are where §1 says. The `Eigensolvers`
folder now has its layer entry (`docs/rules/layers.toml`), so §7.5's P1 errors are gone.

**Registration (D7).** `docs/targets.toml` has the `[[tree]]` `NLAlib.eighProg.compiled` and the
`[[target]]` `NLAlib.MatrixFreeRoundedProbEigh`, with the witness
`NLAlib.matrixFreeRoundedProbEigh_nonVacuous`
(`RandomMatrix/Computation/RoundedTargetWitnesses.lean`: `gridSem t` with $u = 2^{-t} > 0$ and $t$
chosen from $N$, the grid kernels `gridMM`/`gridQR`, tape rounding `roundNearest t`) and its
`witness_sem` (1f43e0a9). The hash, statement and normal form are empty and `reviewed = ""`: the
maintainer re-pins (`TARGETS_UPDATE=1 lake env lean scripts/Targets.lean`, then
`docs/targets.approved`). Registering the tree needed `set_option maxRecDepth 100000` on the
registry check's `run_cmd` (eb0bda85, for the maintainer's review).


### Statement changes at the clean-up (2026-11-08)

The golf and integration passes changed no target, no headline theorem (TT1–TT3, TR2, TR3) and no
definition. They changed these helper statements, each to a stronger or the same proposition:

- **Unused hypotheses dropped** (rule T13, `#lint` unusedArguments; every caller updated):
  `Computation.isAccurate_toFloatMachine`, `FloatMachine.IsAccurate.mono` (`0 ≤ u`);
  `holds_of_exec_newtonSchulzTestBlock`, `exists_exec_newtonSchulzTestBlock` (`V ≠ X`,
  `blockDisjoint f X`); `exists_exec_eighDownLevel`, `eighProg.exists_exec_compiled`
  (`0 ≤ dec p ε`, which the prose of EP (b) lists but no proof used); `exists_exec_eighProg`
  (`0 ≤ dec p ε`, `[A, par, U, dv].Nodup`); `holds_of_exec_eighBottomLevel`,
  `exists_exec_eighBottomLevel` (`IsExactToNat`); `holds_of_exec_eighUpLevel`,
  `exists_exec_eighUpLevel` (`IsExactToNat`, `two.buf ∉ H.handles`);
  `holds_of_exec_eighDownLevel`, `levelHolds_succ_of_exec_eighDownLevel`,
  `holds_of_exec_eighSlotBody`, `holds_of_exec_eighNodeBlock(_frame)`,
  `holds_of_exec_eighSplitBlock(_frame)` (`d < D`); `holds_of_exec_eighCompressBlock`,
  `exists_exec_eighCompressBlock` (a block disjointness); `exists_exec_eighSplitBlock(_ex)`
  (`u p < 1`).
- **Unused instance arguments omitted** (`[Inhabited K]`): `eighProg.cnt_le_of_exec_compiled`,
  `eighProg.weight_le_of_exec_compiled`, `deflateProg.cnt_le_of_exec_compiled`,
  `newtonSchulzSignProg.cnt_le_of_exec_compiled`, `IsRelErrSem.decidesFlags`, the pair-kernel
  lemmas `exists_exec_z{copy,mirror,neg,zero}`, `holds_of_exec_zcopy`.
- **`let` inlined** (same proposition, rule N2): `decodeMatrix_{add,sub,mul}Parts_toFloatMachine_exactSem`,
  `eigh_eighTapeMachine_eq_eigh_eighIdealTree`, and `boxTest_toFloatMachine_exactSem_iff`, renamed
  `all_finRange_toFloatMachine_exactSem_iff`.
- **Renames**: the stage-prefixed helpers (`el1_`, `el2_`, `el5_`, `ep1_`, `ep2_`, `ep6_`, `ep7_`) got
  grammar names or became private; TT3 is now
  `measureReal_exists_exec_eighProg_and_not_isApproxDiagonalization_le_of_exponentBits_le` (N15).
  The full maps are in the clean-up commits (`git log` of `cleanup/compdyn-s2`).
- **Shared homes**: the instruction-inversion lemmas `exists_of_exec_seq_*` and
  `read_of_exec_loop_lit` (`Computation/Loops`), `Store.read_pop_pop_pop_of_lt` and relatives
  (`Computation/Store`), `FStmt.mapTags` (`Computation/FirstOrder`, rule E8).

## 9. Decisions (sheet `COMPDYN-S2.json`)

RP the re-pin (sign-off); D1 the sign step with the shallow step limit; D2 tests on sizes by trip
counts; D3 static sample positions; D4 `MulShrinks` for M3; D5 the statement change of
`RunsWithin.subst`; D6 EV8 for successful runs only; D7 the target's placement and registration.

## 10. Calibration (§7.2 of the parent note)

| Part | §7.2 estimate | This stage, definitions | statements (scaffold) | proofs (outlined; realistic ×1.5–2) |
|---|---|---|---|---|
| S2a `bindIdx`, `toNat`, `supRange`, all structural cases | 900 – 1,500 | **353 inserted lines, proved** (language, repairs, tools, `normIdx`) | 306 (BI, NI, EC) | 300; 450 – 600 |
| Node step | 1,200 – 2,000 | 220 (blocks, sign) | 526 | 790; 1,200 – 1,600 |
| Level passes, arenas, invariant | 2,500 – 4,000 | 210 (levels, program) + 300 (vocabulary) | 506 | 1,350; 2,000 – 2,700 |
| Lazy sampling and success | 1,000 – 2,000 | (in the vocabulary) | 236 | 730; 1,100 – 1,500 |
| Assembly, target, weighted counts | 800 – 1,500 | 117 (target) + 30 (`eighCount`) | 280 | 330; 500 – 650 |
| **S2** | **6,400 – 11,000** | **about 1,200** | **about 1,850** | **3,500 outlined; 5,250 – 7,050** |

The statements move into `NLAlib/` with their docstrings minus the `Proof:` lines (D8 of
`docs/rules/DIGEST.md`), about 1,300 lines, so S2 lands at about 1,250 + 1,300 + 5,250 to 7,050 =
**7,750 to 9,550 lines**, inside §7.2's 6,400 to 11,000 for the S2 rows, in its middle. Findings:
* **S2a is well below its row** (about 350 lines against 900 to 1,500): every structural case is a few
  lines because `toNatStep` mirrors `cmpStep`, and the binder's body is a loop body; §7.2 priced
  25 to 35 cases at 20 to 60 lines, the actual cases are 5 to 15 lines.
* **The node step is in its row**, as the pilot predicted (two SIGN-sized blocks and the binder).
* **The level passes are below their row** because the recursion vocabulary (`eighLoc`,
  `eighSlotTree`, `EighArenas`) is definitions that make the invariant a statement, and because D3
  makes the samples static: the "hardest part" becomes six M lemmas about `eighLoc` and four L level
  lemmas.
* **Lazy sampling stays the risk**: one H statement (600+ lines realistic, Fable review);
  without D3 it would have followed the draw counter through the whole run.
* S1 (S1a to S1d) plus S2: about 1,200 + 5,300 to 6,400 + 7,750 to 9,550 = **14,000 to 17,000
  lines**, inside the 12,000 to 20,000 of §7.2.

## 11. The merge of `cleanup/hdiag`

`design/compdyn-s1cd` carried copies of six hdiag definition files from `design/hdiag`
(`Matrix/Computation/{Primitives,Deflation,NewtonSchulzSign,EntrywiseRounding}.lean`,
`Polynomial/Approximation/NewtonSchulz.lean`, `RandomMatrix/Gaussian/Complex.lean`; definitions
only). Merging `cleanup/hdiag` (bd81bd1d) gave add/add conflicts in these six and in `NLAlib.lean`.
Resolution: every one of the six takes `cleanup/hdiag`'s file (each declaration of the pilot's copy is
there, byte-identical as Fable confirmed, and its imports are a superset); `NLAlib.lean` keeps both
import lists; the pilot's `KernelContracts.lean` unification (it imports `Primitives.lean` and uses
`NLAlib.MatMulMap`, `QRMap`, `IsMatMulErr`, `IsQRErr`) is kept as is. The merge builds (`--wfail`).
Replaying `Deflation.lean` prints two `PANIC at Lean.Expr.appArg!` infos (lines 216 and 345); they
are in hdiag's file as pushed and do not fail the build.

## 12. Checks

At the design stage (skeleton commit ed1ad86c, with the scaffold library); the end-of-stage checks
are in the stage report (`reports/Stage-COMPDYN-S2-Hardening.md`, harness).

| check | result |
|---|---|
| `lake build --wfail NLAlib NLAlibTools` | passes (4,312 jobs) |
| `lake build NLAlibScaffold` | passes, `sorry` warnings only |
| `scripts/check_rules.py` | 8 errors, all P1 on `NLAlib/Eigensolvers` (no LAYER entry; T105, expected); E8 and S4 found on the way were fixed |
| `scripts/check_refs.py`, `scripts/check_constants.py`, `scripts/check_latex.mjs` (KaTeX) | 0 problems |
| `lake exe mk_all --check` (NLAlib, NLAlibTools) | no update necessary |
| `scripts/Targets.lean` | 1 violation: the `lakefile_sha256` pin (the scaffold entry), expected; closure hashes, trees, statements and approval match after the re-pin |
| `scripts/Programs.lean` | 3 violations, all E4 for the unregistered `newtonSchulzSignProg`, `deflateProg`, `eighProg`, expected |
| `bin/check-skeleton --strict` | 63 targets, 0 names missing an import, 0 unresolved |
