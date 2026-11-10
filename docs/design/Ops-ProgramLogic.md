# The program-logic layer of the new core (`NLAlib/Ops/Logic`)

Status: **phase A** (design and statement skeleton), 2026-11-10, branch `feat/ops-logic` (from
`feat/ops-core` at `16cf312a`). Owner: the logic-layer lane (tooling plan §1 tactics, §2 builder,
notation, named states, templates). Nothing here is proved yet: every theorem of
`NLAlib/Ops/Logic/*.lean` is stated and elaborates, with `sorry`; the builder is implemented and
tested. Phase B proves the statements, implements the tactics, and rewrites the three yardstick
examples (gemm, MGS, CGS) to measure the line counts projected in §14.

Read with: `NLAlib/Ops/README.md` (the core), `reports/Ops-Tooling-Plan.md`,
`docs/design/Computation-Operations-BuilderBrief.md`, `reports/Review-COMPDYN-OpsCore.md`
(K2, K3, M2, S2 table), and the old playbook `docs/contributing/programs.md` "Proving a program"
(origin/main), whose ideas (mode-generic specs, frame-carry of bundles, `fp_omega`, named
allocation chains, `spec_scalarBlock`, cheap index transport, `whileFuel` with an invariant) are
re-implemented here, not ported.

Nothing in this layer is in the trusted base: every definition is a predicate on runs of the
existing evaluator (`Wp`, `EqOff`, `RunsFromW`), every rule is a theorem about it, every tactic
builds ordinary proof terms, and the builder is a macro whose output is a plain `Stmt` term.

---

## Amendment after review (2026-11-10)

Reviews: `reports/Review-Core-OpsLogic.md` (core lane, with Lean counterexamples) and Fable's.
Both approve after these fixes. Changes to the statements (the sections below are updated where
they state a signature; where they are not, this list wins):

* **False statements fixed.** `writes_fill₂`, `writes_fillRel₂` take `hL : L.Valid` (two entries
  shared a cell otherwise; refuted in Lean). `writes_scalarBlock` is stated for `.total` with the
  room unconditional (the catalog's scalar contracts are total-only; a liberal statement was
  refuted). `writes_fillRel`, `writes_fillRel₂` take `[Nonempty K]`.
* **Modes, honestly.** The rules are mode-generic, but the catalog states `IsScalar`/`IsBlas1`
  in total mode only: a proof that calls the catalog is a total proof, and its liberal corollary
  comes by `Writes.of_total` under the same hypotheses. "One proof gives both modes" holds only
  for programs over contracts stated for every mode.
* **Syntax.** `as` and `reads` are non-reserved in the tactics (`&" as "`, `&" reads "`).
* **Root.** No module of `Logic/` is imported by `NLAlib.lean` until `Logic/` is sorry-free;
  it is built by explicit targets.
* **M1.** `Mem.eq_updBlocks_of_eqOff` and `Impl.meets_of_writes` no longer ask `Fp.Apart`
  (overlapping outputs read back the same cells); apartness only for reading back a call.
* **M2/M3. Facts across an allocation.** `Store.ReadsOnly` reads cells only (no shape);
  `Store.Below L s s'` (same lengths and cells below `L`) with `Below.keep`, `Below.readBlock`,
  `below_push`, `EqOff.below`. `writes_alloc(s)`: the body is proved for every `s₁` with the
  declared lengths and `Below L m.store s₁`; the postcondition is asked of every store of length
  `L` that agrees below `L` with the final one, so no `pop`/`take` appears in a goal.
* **M4.** `Writes.seq_le`: the continuation is proved against the declared footprint.
* **M5.** `alloc as` states the `lens` list of the nested `.alloc`s it sees (the builder emits
  them), so `writes_allocs` applies by `change` to `Stmt.allocs`.
* **Scalar blocks and tags.** `ScalarIns Op` carries the operation itself (any tag), the rule
  takes `ScalarCall I o g` per instruction (`IsScalar.scalarCall` gives it at a tag), so mixed
  precision is one block. The builder will emit plain nested calls; the tactic `change`s them
  into `Stmt.scalarBlock` (D7).
* **More rules.** `writes_ite_holds`, `writes_bindIdx_holds` (the test or index under
  `md.Holds`), `writes_frame`, `writes_whileStrict`.
* **Bridge.** `Store.HoldsMat.readBlock`, `Store.holdsMat_of_readBlock` (dense matrix ↔ flat
  block, `rows = ld`), for `meets_of_writes`.
* **Tactics.** `frame` ends with `all_goals fail` and normalises lengths; `fp_mem`, `fp_sub`,
  `disjoint` use `idx`; `fpNF` covers `Fp.above`, `Fp.cells`, `MatLayout.fp`,
  `MatLayout.upto`; `idx` has no `nlinarith` (`idx!` has it; D10a); `idxNF` side conditions by
  `omega`; `Mem.readBlocks_cons_eq_some` is not a simp lemma. `keep` is lazy: facts are
  transported where used against the running frame, not after every step (finding 8).
* **Builder.** Errors on a dimension declared twice or also an operand, and on a binder that
  shadows a name of the header; `X_off` documented; the offset convention is frozen (§12).
  The printer (D17) comes first in phase B.
* **D12 changed.** `RunsFromWL` goes in the core's `Counted.lean` (core lane, complete rule set).
  `Logic/Count.lean` keeps its statements unproved until then and will consume the core's.
* Duplicates of core lemmas removed (`EqOff.of_le`, `EqOff.upd_of_mem`); `disj_of_cols` takes
  no `Valid`; `col_fp` takes `j < L.cols`.

---

## 0. Summary

**The diagnosis** (README "For the logic layer", measured): calls are one line already
(`wp_call`), but whole run proofs barely shrank (gemm 94→96, MGS 136→127, CGS 333→329) because
the rest of a run proof is spent on, in order: frames of update chains, scratch lengths after
`alloc`, index facts, certificate destructuring, named states, positional trees. One more cost
the README does not list but every example pays: the **invariant shape**
`∃ s', m' = ⟨s', pos⟩ ∧ S.EqOff F s' ∧ …` and the hand-composed frame of a round
(`(hfr.mono …).upd (Or.inl (Or.inr ⟨rfl, by omega, by omega⟩)) _ …`).

**The design** in one paragraph. One judgment, `Writes md I τ c ρ F P m` := `Wp` with a frame
("the run of `c` writes only the cells `F` and ends in `P`"). Every rule (call, alloc, loop, fill,
`whileFuel`, `ite`, `bindIdx`, scalar block, certificate) is restated for it, mode-generic, in a
**named-state form**: the continuation receives a fresh memory `m'`, the frame
`m.store.EqOff F m'.store` and the postcondition, never a chain of updates. Footprints are
predicates with a normal form (`fpNF`), so membership, inclusion and disjointness are one tactic
each (`fp_mem`, `fp_sub`, `disjoint`) on top of an index tactic (`idx`) that handles the products
of sizes. A step tactic (`step h as m₁ with x hx`) combines the call rule, the side goals, the
running frame, the lengths and the kept facts. A builder (`ops% [n, k] (Q, w) → (w, R) { … }`)
writes programs with names and elaborates to the same `Stmt` term as the positional tree, by
`rfl`.

**Deliverables of phase A** (commit on `feat/ops-logic`, see the report):

| File | Content | Statements |
|---|---|---|
| `Logic/Attr.lean` | simp sets `fpNF`, `idxNF`, `decodeNF` | |
| `Logic/Builder.lean` | `ops%`, `opsImpl%` (implemented) | |
| `Logic/Footprint.lean` | `Fp`, `Fp.blocks`, `Fp.Disj`, `Fp.Apart`, `Store.ReadsOnly`, `EqOff.keep`, `EqOff.trans'`, `Mem.eq_updBlocks_of_eqOff`; `fp_mem`, `disjoint` | 33 |
| `Logic/Index.lean` | `Idx.*` lemmas; `idx` | 7 |
| `Logic/Writes.lean` | `Writes` and its rules; `writes_call*`, `writes_alloc(s)`, `writes_ite`, `writes_bindIdx*`, `Wp.named`, `Impl.meets_of_writes` | 20 |
| `Logic/Layout.lean` | `HoldsVec`, `MatLayout`, `HoldsMat`, `HoldsMatUpto`, decoding | 18 |
| `Logic/Loop.lean` | `writes_loop`, `writes_loop₂`, `writes_fill(₂)`, `writes_fillRel(₂)`, `writes_whileFuel`, `writes_ifPos/ifZero` | 9 |
| `Logic/Scalar.lean` | `ScalarIns`, `Stmt.scalarBlock`, `ScalarIns.evalBlock`, `writes_scalarBlock` | 3 |
| `Logic/Count.lean` | `RunsFromW.of_writes`, `RunsFromWL` + rules, closed forms; `count_eval` | 9 |
| `Logic/TapeMeas.lean` | `Tape.PastAt`, `pastEntry`, `pastWindow`, `fun_prop` leaves | 3 |
| `Logic/Tactic.lean` | `step`, `frame`, `fp_sub`, `checkpoint`, `alloc as`, `loop_inv`, `keep`, `cert_intro`, `decode` | (syntax) |
| `Examples/Built.lean` | builder = hand-written trees for `mgs`, `mgsImpl`, `gemm`, `cgs`, and the other constructs, by `rfl` | 5 examples |
| `Examples/CgsWrites.lean` | `cgsCol_writes`, `cgs_spec_writes` (statements), `splitB` (S2 block in the builder, `rfl`) | 2 + 1 example |

102 theorem statements in `Logic/` (76 with `sorry`, 26 proved by one line), 2 in
`Examples/CgsWrites.lean`; about 30 definitions; 9 tactic syntaxes besides `fp_mem`, `disjoint`,
`idx`, `count_eval`. Every file elaborates with `lake build` (no error, no warning but `sorry`).
Provisional implementations of `fp_mem`, `fp_sub`, `disjoint`, `frame`, `idx` pass four probes
(a chain of updates against a block footprint, a running frame plus a write, `i n + n ≤ k n` from
`i < k`, disjointness of a block and another buffer).

**Projected program-logic lines** (§14): gemm 96 → about 40, MGS 127 → about 50, CGS 329 →
about 120, with the contract and the certificate included in the new count (they were extra
before). These are targets to be measured in phase B, not measurements.

---

## 1. Which piece removes which cost

| Cost today (README order) | Where it shows | Removed by |
|---|---|---|
| Frames of update chains | `(hfr.mono …).upd (Or.inl (Or.inr ⟨rfl, by omega, by omega⟩)) _ …` in every round and every exit (`wp_mgs_step`, `wp_cgsCol`, `wp_cgs`) | the round is proved against a fresh memory with the frame of *this* round only (§2, §6); `frame` and `fp_sub` prove what is left; `Store.EqOff.trans'` composes |
| Invariant shape `∃ s', m' = ⟨s', pos⟩ ∧ EqOff …` | every `wp_loop` | the standard invariant form of `writes_loop` and the fill rules: the rule carries the frame, the invariant is only the mathematics (§6) |
| Scratch lengths after alloc | `hlen`, `hlR`, `hlt`, `hlw` (4 lines × 2 per proof) | `writes_alloc(s)`: the body is proved for every store with the declared lengths; `alloc as t` names the handle; the running frame gives `len_eq` once (§5) |
| Index facts | `i * n + n ≤ k * n` ten times, `div_mod_of_lt`, tape positions | `idx` (discharger of every side goal), `Idx.*`; the 2-D loop rules index by `(i, j)`, so no quotient/remainder (§4, §6) |
| Certificate destructuring | 4–6 lines per certificate, and the final `eq_updBlock₂`/`peel` | `Impl.meets_of_writes` (the equation is built once in the core lemma) and `cert_intro` with the builder's header (§9) |
| Named states | stores pushed through 5–40 updates by `store_simp` | every step is named (`Writes.then_`); `Wp.named`/`checkpoint` for chain-mode proofs (§2, §5) |
| Positional trees | `.var 5 + .var 6 * .var 1 + .var 7` | the builder (§12) |
| Counts | `RunsFromW` has no tactic, no partial-correctness form | `count_eval`, `RunsFromWL`, `RunsFromW.of_writes` (§10) |
| Reads of facts across calls | `hfr.readBlock_of fact (by store_side)` per fact per call | `keep` (frame-carry, §3) inside `step` |
| Decoding | `fun i hi => Store.getD_drop_take qs _ _ _ hi default` per call | `decode`, `vec_drop_take`, `HoldsVec`/`HoldsMat` (§8) |

---

## 2. The judgment `Writes`, modes, and named states

```lean
-- Logic/Writes.lean
def Writes (md : Mode) (I : Interp Op Tst K) (τ : Tape K) (c : Stmt Op Tst) (ρ : Env) (F : Fp)
    (P : Mem K → Prop) (m : Mem K) : Prop :=
  Wp md I τ c ρ (fun m' => m.store.EqOff F m'.store ∧ P m') m
```

`EqOff` is the core's frame (same shape, same cells off `F`). `P` may mention `m` (closed over):
"the block reads `xs` from `m` and writes `ys` related to them".

**Rules of composition** (`namespace Writes`):

```lean
theorem wp    (h : Writes md I τ c ρ F P m) (hQ : ∀ m', m.store.EqOff F m'.store → P m' → Q m') :
    Wp md I τ c ρ Q m
theorem then_ (h : Writes md I τ c ρ F P m)
    (k : ∀ m', m.store.EqOff F m'.store → P m' → Wp md I τ c' ρ Q m') :
    Wp md I τ (.seq c c') ρ Q m                                   -- the named step
theorem seq   (h : Writes md I τ c ρ F P m)
    (h' : ∀ m', m.store.EqOff F m'.store → P m' → Writes md I τ c' ρ G P' m') :
    Writes md I τ (.seq c c') ρ (F ⊔ G) P' m
theorem mono  (h : Writes md I τ c ρ F P m) (hF : F ≤ G)
    (hP : ∀ m', m.store.EqOff F m'.store → P m' → P' m') : Writes md I τ c ρ G P' m
theorem and   (h : Writes … F P m) (h' : Writes … G P' m) : Writes … F (fun m' => P m' ∧ P' m') m
theorem keep  (h : Writes md I τ c ρ F P m) (hP : Store.ReadsOnly G P₀) (hD : Fp.Disj F G)
    (hp : P₀ m.store) : Writes md I τ c ρ F (fun m' => P m' ∧ P₀ m'.store) m
theorem skip  (h : P m) : Writes md I τ .skip ρ ⊥ P m
theorem of_total (h : Writes .total I τ c ρ F P m) : Writes md I τ c ρ F P m
```

**Named states.** `then_` and `seq` hand the continuation a *variable* `m'`. After a step the
goal mentions `m'`, not `((m.upd z v).updBlock w ys).advance 0`; reads at `m'` come from the
step's postcondition (the blocks it wrote, read back) or from facts about `m` kept across the
frame (`keep`). This is the old core's `allocBind_named`/`wp_bind_keep` discipline as a property
of every rule rather than a separate lemma. A proof that still builds a chain (the chain form of
`wp_call`, kept for three-line blocks and for exact final equations) is turned into a name by

```lean
theorem Wp.named (P : Mem K → Prop) (hP : P m) (h : ∀ m', P m' → Wp md I τ c ρ Q m') :
    Wp md I τ c ρ Q m
```

with the tactic `checkpoint m₁` choosing `P` = running frame ∧ the read facts of the context
restated (each by `store_simp`), and generalising.

**Modes.** One proof gives both statements. Every rule takes `md`; what is needed only for
success is a hypothesis under `md.Needs` (`Mode.Needs md p := md = .total → p`), and what a
successful run tells is in the postcondition. In liberal mode the `Needs` hypotheses are `trivial`
(`Mode.needs_liberal`), so a liberal corollary costs nothing, and it is never a result alone (the
core's `wp_abort_liberal` vacuity, README §9). `Writes.of_total` moves a total block into any
mode. Comparisons whose outcome is fixed by the values (`IsCmp`) stay outside `Needs` (old
playbook item 2): the outcome is the same in both modes.

**Positions.** `EqOff` speaks of the store only; the position of the tape is part of `P`
(`m'.pos = m.pos + k`). A block without windows says `m'.pos = m.pos`.

---

## 3. Footprints, disjointness, frame-carry

```lean
-- Logic/Footprint.lean
abbrev Fp := ℕ → ℕ → Prop                        -- ordered by ≤ (inclusion), joined by ⊔
def Fp.blocks : List (ℕ × ℕ) → List ℕ → Fp      -- the output blocks of a call
def Fp.Disj (F G : Fp) : Prop := ∀ b i, F b i → G b i → False
def Fp.Apart : List (ℕ × ℕ) → List ℕ → Prop      -- the output blocks are pairwise disjoint
def Fp.above (L : ℕ) : Fp := fun b _ => L ≤ b    -- scratch buffers from the handle L on (Writes.lean)
def Fp.cells (zs : List (ℕ × ℕ)) : Fp           -- single cells (Scalar.lean)
-- normal form: inBlock_apply, inBuf_apply, sup_apply, bot_apply, le_iff, disj_iff,
--   blocks_cons/nil, MatLayout.cell, and the propositional simp lemmas, all tagged @[fpNF]
theorem Fp.disj_inBlock_of_ne (h : b ≠ b') : Disj (inBlock b o n) (inBlock b' o' n')
theorem Fp.disj_inBlock_of_le (h : o + n ≤ o') : Disj (inBlock b o n) (inBlock b o' n')
theorem Fp.inBlock_le_inBlock (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n') : inBlock b o n ≤ inBlock b o' n'
theorem Fp.inBlock_add : inBlock b o n ⊔ inBlock b (o + n) n' = inBlock b o (n + n')   -- @[fpNF]

def Store.ReadsOnly (G : Fp) (P : Store K → Prop) : Prop :=
  ∀ s s', s'.shape = s.shape → (∀ b i, G b i → s'.get b i = s.get b i) → P s → P s'
theorem Store.readsOnly_readBlock (b o n xs) : ReadsOnly (inBlock b o n) (·.readBlock b o n = some xs)
theorem Store.readsOnly_get, readsOnly_shape, ReadsOnly.and, ReadsOnly.mono
theorem Store.EqOff.keep (h : EqOff F s s') (hP : ReadsOnly G P) (hD : Fp.Disj F G) (hp : P s) : P s'
theorem Store.EqOff.trans' (h : EqOff F s s') (h' : EqOff G s' s'') : EqOff (F ⊔ G) s s''
theorem Store.EqOff.upd_of_mem (h : EqOff F s s') (hF : F b i) (v) : EqOff F s (s'.upd b i v)
theorem Store.EqOff.updBlock_of_le (h : EqOff F s s') (hF : inBlock b o xs.length ≤ F) :
    EqOff F s (s'.updBlock b o xs)
theorem Store.EqOff.of_le (h : EqOff G s s') (hF : G ≤ F) : EqOff F s s'
theorem Mem.eqOff_updBlocks (h : s.EqOff F m.store) (hF : Fp.blocks zs (ys.map length) ≤ F) :
    s.EqOff F (m.updBlocks zs ys).store
theorem Mem.eq_updBlocks_of_eqOff (h : m.store.EqOff (Fp.blocks zs ls) m'.store)
    (hap : Fp.Apart zs ls) (hr : m'.readBlocks zs ls = some ys) (hpos : m'.pos = m.pos) :
    m' = m.updBlocks zs ys                       -- generalises eq_updBlock₂ to n blocks
theorem Mem.readBlocks_cons_eq_some : … ↔ ∃ x xs, readBlock … = some x ∧ readBlocks … ∧ X = x :: xs
theorem Mem.readBlocks_updBlocks (hap) (hz : m.Room zs (ys.map length)) :
    (m.updBlocks zs ys).readBlocks zs (ys.map length) = some ys
```

**Why predicates and not lists of blocks** (decision D3): `EqOff` already takes a predicate,
`peel`/`pop` are stated on it, and a loop footprint is naturally a family `fun i => inBlock R o i`.
The cost of predicates, membership proofs, is what `fp_mem` removes: `fpNF` turns any footprint
built from the constructors above into a disjunction of linear (or, with `idx`, nonlinear)
constraints on `(b, i)`, and handles are numbers, so different buffers are disequalities.

**Disjointness at scale (100 buffers).** Handles come in two kinds: the operands of the frame,
an injective family `B : ι → ℕ` (`hB.eq_iff` turns `B x = B y` into `x = y`, decided by
`decide` on a `DecidableEq ι`), and the scratch handles `L + i` above every live handle
(`writes_allocs`: `b < L` for the operands). `disjoint [hB.eq_iff]` therefore reduces any
disjointness of blocks to constructor disequalities and `omega` on `L + i` vs `B x < L`; the
`Examples/Loops` hundred-buffer fixture is the acceptance test (phase B). No `Or.inl (Or.inr …)`
chain is written by hand.

**Frame-carry.** A fact read by a later step rides across a step if it reads only cells off the
step's footprint: `Writes.keep`, or, inside `step`, the tactic `keep`, which restates every
hypothesis of the forms `s.readBlock b o n = some xs`, `s.get b i = some v`, `s.HoldsVec …`,
`s.HoldsMat …` for the new memory when `disjoint` proves the side condition, and leaves the
others alone. Bundles are not needed as data: the context is the bundle.

**Block-level disjointness in one buffer** (review K3: S2 calls `mm` with input and output in
one arena): disjointness is cell-level here, so two blocks of one buffer are apart by
`disj_inBlock_of_le` or `MatLayout.disj_of_cols`; the catalog's buffer-level `OutApart` stays a
catalog policy (decision D4 of the core lane).

---

## 4. Index arithmetic (`idx`)

```lean
-- Logic/Index.lean
theorem Idx.mul_add_le_mul (h : i < k) (n) : i * n + n ≤ k * n
theorem Idx.mul_add_le_mul' (h : i < k) (n) : n * i + n ≤ n * k
theorem Idx.add_lt_mul (hi : i < m) (hj : j < p) : i * p + j < m * p
theorem Idx.div_add (hj : j < p) : (i * p + j) / p = i          -- @[idxNF]
theorem Idx.mod_add (hj : j < p) : (i * p + j) % p = j          -- @[idxNF]
theorem Idx.mul_le_mul_of_le (h : i ≤ k) (n) : i * n ≤ k * n
theorem Idx.pos_add_le (h : i < k) : p + i * w + w ≤ p + k * w  -- tape positions
```

**`idx [facts]`.** Goal: `≤ < = ≠` between sums of products of variables and numerals, with
`/` and `%` by a size. Method: `omega` (it treats a product of variables as an atom, so
`i * n + j < 5` from `i * n + n ≤ 5`, `j < n` already works); then *product generation*: for each
hypothesis `i < k` / `i ≤ k` and each product `i * n` / `n * i` in the goal, add
`Idx.mul_add_le_mul`; `ring_nf` the products into monomials (atoms for `omega`); rewrite `idxNF`;
`omega` again; `nlinarith` last (provisional implementation: `omega`, `idxNF`, `nlinarith`; it
proves the probe `i < k ⊢ i * n + n ≤ k * n`). **Failure**: never leaves a goal; fails with
"idx: the index fact is not proved" and the goal. **Scale**: product generation is restricted to
the hypotheses on loop variables and to products present in the goal, so the number of facts
stays linear (review: `omega` times out at about 100 facts; decision D10).

`idx` is wired into `store_side` (phase B: one line in `StoreSimp.lean`, so `wp_call` and `step`
pick it up at once, as the README says), `fp_mem`, `disjoint` and `decode`. The S2 slot layout
probe of the review (`(s.upd b (n*d + i) v).get b (n*(d+1) + j)`, `i, j < n`) is a phase B
acceptance test.

---

## 5. Calls, scratch, branches, indices

**The call rule with a footprint** (mode-generic, any number of outputs):

```lean
theorem writes_call (hI : I.Meets md o (R.spec adm)) (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some b)
    (hnd : d.length = R.nd) (hk : R.win d = k) (hls : R.outLens d = ls) (hadm : adm d a b)
    (hap : Fp.Apart b ls)
    (hpre : md.Needs (m.Live (a ++ b) ∧ (∃ xs, m.readBlocks a (R.inLens d) = some xs ∧
      R.dom d xs (τ.window R.stream m.pos k)) ∧ m.Room b ls)) :
    Writes md I τ (.call o ds ins outs) ρ (Fp.blocks b ls)
      (fun m' => m'.pos = m.pos + k ∧ ∃ xs ys, m.readBlocks a (R.inLens d) = some xs ∧
        m'.readBlocks b ls = some ys ∧ R.rel d xs (τ.window R.stream m.pos k) ys) m
```

Shapes (what `step` applies, chosen by the shape of `hb`): `writes_call1` (one block, read back
with `readBlock`), `writes_call_cell` (one cell, `get`), `writes_call2` (two blocks, disjoint),
`writes_call_bin` (a functional operation of two cells: the written cell holds the computed `w`).
The outputs must be pairwise apart to be read back (decision D4); the chain-form `wp_call_rel`
stays for the rest.

**Scratch buffers as named states** (M2):

```lean
theorem writes_alloc (hn : len.eval ρ.idx = some n)
    (h : ∀ s₁ : Store K, s₁.length = m.store.length + 1 → s₁.len m.store.length = n →
      (∀ b, b < m.store.length → s₁.len b = m.store.len b) →
      (∀ b off k, b < m.store.length → s₁.readBlock b off k = m.store.readBlock b off k) →
      Writes md I τ body (ρ.pushBuf m.store.length) (F ⊔ Store.inBuf m.store.length)
        (fun m' => P ⟨m'.store.pop, m'.pos⟩) ⟨s₁, m.pos⟩) :
    Writes md I τ (.alloc len body) ρ F P m

def Stmt.allocs : List IExp → Stmt Op Tst → Stmt Op Tst      -- nested .alloc, as the builder writes
theorem writes_allocs (hn : IExp.evalList ρ.idx lens = some ns)
    (h : ∀ s₁, s₁.length = m.store.length + ns.length →
      (∀ i (hi : i < ns.length), s₁.len (m.store.length + i) = ns[i]) →
      (∀ b, b < m.store.length → s₁.len b = m.store.len b) →
      (∀ b off k, b < m.store.length → s₁.readBlock b off k = m.store.readBlock b off k) →
      Writes md I τ body ⟨ρ.idx, ρ.buf ++ (List.range ns.length).map (m.store.length + ·)⟩
        (F ⊔ Fp.above m.store.length) (fun m' => P ⟨m'.store.take m.store.length, m'.pos⟩) ⟨s₁, m.pos⟩) :
    Writes md I τ (Stmt.allocs lens body) ρ F P m
```

The body is proved for *every* store with the declared lengths that agrees with the caller's
below `L = m.store.length`: no `push` appears in the goal, the lengths are hypotheses, the reads
of the caller's blocks transfer by one rewrite, and the frame after the pops is the caller's
(`EqOff.pop` once, inside the rule). Seven or eight buffers (S2 nodes) are one application.
Tactic: `alloc as t₁ … tₖ` applies the rule, introduces `s₁` as the new store of the memory, the
handles `tᵢ := L + i` with `htᵢ`, and the length and read facts under fixed names; the
footprint's `inBuf tᵢ` parts are added by `fp_sub` at the end.

**Branches and indices.**

```lean
theorem writes_ite (hd) (ha) (hc : I.test q d a m = some c)
    (h : Writes md I τ (if c then t else e) ρ F P m) : Writes md I τ (.ite q ds ins t e) ρ F P m
theorem writes_bindIdx (ha) (hB : bound.eval ρ.idx = some B) (hv : I.index q a m = some v)
    (hle : v ≤ B) (h : Writes md I τ body (ρ.pushIdx v) F P m) :
    Writes md I τ (.bindIdx q ins bound body) ρ F P m
theorem writes_bindIdx_of_isIndex (hI : I.IsIndex q f) (ha) (hB)
    (hr : m.readBlocks a (a.map fun _ => 1) = some xs) (hf : f xs.flatten = some v) (hle : v ≤ B)
    (h : Writes md I τ body (ρ.pushIdx v) F P m) : Writes md I τ (.bindIdx q ins bound body) ρ F P m
```

---

## 6. Loops: the standard invariant form

Every loop rule takes a **footprint family** `F i` (what the first `i` rounds may write,
increasing) and an **invariant family** `P i` (mathematics only). A round is proved from a fresh
`m'` with `m.store.EqOff (F i) m'.store` and `P i m'`, and writes `F (i + 1)` *from `m'`*; the
rule composes the frames (`trans'`, monotonicity). So a round never rebuilds the frame from the
start of the loop (today's `(hfr.mono …).upd … |>.updBlock …`).

```lean
-- Logic/Loop.lean
theorem writes_loop (hn : n.eval ρ.idx = some N) (F : ℕ → Fp) (hF : ∀ i < N, F i ≤ F (i + 1))
    (P : ℕ → Mem K → Prop) (h0 : P 0 m)
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (F i) m'.store → P i m' →
      Writes md I τ body (ρ.pushIdx i) (F (i + 1)) (P (i + 1)) m') :
    Writes md I τ (.loop n body) ρ (F N) (P N) m

theorem writes_loop₂ (hn₁ : n₁.eval ρ.idx = some M) (hn₂ : ∀ i, n₂.eval (ρ.pushIdx i).idx = some N)
    (F : ℕ → ℕ → Fp) (hF : ∀ i < M, ∀ j < N, F i j ≤ F i (j + 1)) (hrow : ∀ i < M, F i N ≤ F (i + 1) 0)
    (P : ℕ → ℕ → Mem K → Prop) (h0 : P 0 0 m) (hnext : ∀ i < M, ∀ m', P i N m' → P (i + 1) 0 m')
    (hstep : ∀ i < M, ∀ j < N, ∀ m', m.store.EqOff (F i j) m'.store → P i j m' →
      Writes md I τ body ((ρ.pushIdx i).pushIdx j) (F i (j + 1)) (P i (j + 1)) m') :
    Writes md I τ (.loop n₁ (.loop n₂ body)) ρ (F M 0) (P M 0) m
```

**The fill rules** (the pattern "written six times", tooling plan): round `i` writes one cell.
The round proves only that cell; the rule proves the frame, the prefix and the position.

```lean
theorem writes_fill (hn) (v : ℕ → K) (pos : ℕ → ℕ) (hpos : m.pos = pos 0)
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (inBlock b o i) m'.store → m'.store.HoldsVec b o i v →
      m'.pos = pos i → Writes md I τ body (ρ.pushIdx i) (inBlock b (o + i) 1)
        (fun m'' => m''.store.get b (o + i) = some (v i) ∧ m''.pos = pos (i + 1)) m') :
    Writes md I τ (.loop n body) ρ (inBlock b o N) (fun m' => m'.store.HoldsVec b o N v ∧ m'.pos = pos N) m
theorem writes_fillRel …      -- values known by a relation R i x (outputs of relational calls)
theorem writes_fill₂ (L : MatLayout) …      -- 2-D, by columns of a layout (the Gaussian test matrix)
theorem writes_fillRel₂ (L : MatLayout) …   -- 2-D relational (gemm, a table of dot products)
```

The 2-D rules index by `(j, i)`; the footprint after `(j, i)` is `L.upto j i`, the invariant is
`HoldsMatUpto L A j i`: there is no linear index `q`, so no `q / p`, `q % p` (gemm's
`div_mod_of_lt` disappears).

```lean
theorem writes_whileFuel (hn : fuel.eval ρ.idx = some N) (F : ℕ → Fp) (hF : ∀ i < N, F i ≤ F (i + 1))
    (G : Fp) (Inv : ℕ → Mem K → Prop) (P : Mem K → Prop) (h0 : Inv 0 m)
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (F i) m'.store → Inv i m' →
      md.Holds (I.testAt q ds ins (ρ.pushIdx i) m') fun c =>
        if c then Writes md I τ body (ρ.pushIdx i) (F (i + 1)) (Inv (i + 1)) m'
        else Writes md I τ k (ρ.pushIdx i) G P m')
    (hcap : ∀ m', m.store.EqOff (F N) m'.store → Inv N m' → Writes md I τ k (ρ.pushIdx N) G P m') :
    Writes md I τ (.whileFuel fuel q ds ins body k) ρ (F N ⊔ G) P m
theorem writes_ifPos, writes_ifZero
```

**`loop_inv F P with i hi m' hfr hP`.** Goal: `Writes … (.loop …)` (or two nested loops, or a
`whileFuel`); for the fill rules `loop_inv fill v pos` / `fillRel R pos` / `fill₂ L A pos`. It
applies the matching rule (by the shape of the tree and the keyword), evaluates the bounds,
proves the monotonicity of `F` by `fp_sub`, closes `P 0 m` by `simp`/`exact` if it can, and
leaves the round with the names given. Failure: the tree is not a loop of that kind, or a
monotonicity goal fails (`fp_sub`'s message).

---

## 7. Straight-line scalar blocks

```lean
-- Logic/Scalar.lean
structure ScalarIns where (op : ScalarOp) (ins : List Operand) (out : Operand)
def Stmt.scalarBlock [Has ScalarOp Op] : List ScalarIns → Stmt Op Tst   -- right-nested calls
def Store.cellFn (s : Store K) : ℕ × ℕ → Option K
def Machine.eval (M : Machine K) : ScalarOp → List K → Option K
def ScalarIns.evalBlock (M) (ρ) : List ScalarIns → (ℕ × ℕ → Option K) → Option (List ((ℕ × ℕ) × K))
def Mem.updCells (m : Mem K) : List ((ℕ × ℕ) × K) → Mem K
theorem writes_scalarBlock (hS : IsScalar M I)
    (hev : ScalarIns.evalBlock M ρ xs m.store.cellFn = some ws)
    (hroom : md.Needs (∀ w ∈ ws, w.1.2 < m.store.len w.1.1)) :
    Writes md I τ (Stmt.scalarBlock xs) ρ (Fp.cells (ws.map Prod.fst)) (fun m' => m' = m.updCells ws) m
theorem get_updCells (hz : ws.reverse.lookup z = some v) (hl) : (m.updCells ws).store.get z.1 z.2 = some v
theorem get_updCells_of_notMem (hz : z ∉ ws.map Prod.fst) : … = m.store.get z.1 z.2
```

The machine is total (`StdModel.div` puts the zero-divisor condition on the arithmetic contract),
so the old `OpsOk` disappears; `OpsDefined` is the evaluation succeeding (cells read hold words,
cells written earlier in the block need no initialisation). Lesson kept from the old core: one
output word per lemma (`evalBlock` unfolded and one `Function.update_apply` chain per output),
never one `simp` over a 36-instruction block. The builder will emit `Stmt.scalarBlock` literally
for a `scalar { t := a * b; … }` block (decision D7), so the rule applies syntactically.

---

## 8. Layouts and decoding

```lean
-- Logic/Layout.lean
def Store.HoldsVec (s) (b o n : ℕ) (v : ℕ → K) : Prop := ∀ i < n, s.get b (o + i) = some (v i)
structure MatLayout where (buf off rows cols ld : ℕ)          -- by columns: (i, j) ↦ off + j*ld + i
def MatLayout.cell, MatLayout.Valid (rows ≤ ld), MatLayout.fp, MatLayout.upto (fill footprint)
def Store.HoldsMat (s) (L) (A : ℕ → ℕ → K), Store.HoldsMatUpto (s) (L) (A) (j i)
theorem Store.holdsVec_iff_readBlock : s.HoldsVec b o n v ↔ s.readBlock b o n = some ((List.range n).map v)
theorem Store.holdsVec_of_readBlock (h : s.readBlock b o n = some xs) : s.HoldsVec b o n (vec xs)
theorem Store.readsOnly_holdsVec, readsOnly_holdsMat, HoldsVec.snoc, HoldsMat.col, holdsMat_of_cols
theorem MatLayout.fp_le_inBlock (hL : L.Valid) : L.fp ≤ inBlock L.buf L.off (L.cols * L.ld)
theorem MatLayout.disj_of_cols (hL) (h : j₁ + n₁ ≤ j₂) : Disj (columns j₁…) (columns j₂…)
theorem MatLayout.upto_zero/upto_col/upto_succ/upto_cols                 -- the fill footprint algebra
theorem vec_drop_take (h : i < n) : vec ((xs.drop a).take n) i = vec xs (a + i)    -- @[decodeNF]
def decVec (dec) (n) (v : ℕ → K) : Fin n → ℝ;  def decMat (dec) (r c) (A) : Matrix (Fin r) (Fin c) ℝ
theorem decVec_apply, decMat_apply                                                 -- @[decodeNF]
```

A matrix stored by rows is the layout of its transpose (`gemm`'s `C`). **`decode`**: rewrites
`decodeNF` with `idx` as discharger; goal: an equation or a predicate of layer 1 about decoded
stored values; leaves the mathematical goal, fails if nothing rewrites. Complex interleaved pairs
(S2's `pairLayout`) are decision D9.

---

## 9. Certificates and templates

```lean
theorem Impl.meets_of_writes {R : Impl Op Tst} {B : BlockRel K}
    (h : ∀ d ins outs τ m xs, d.length = B.nd → adm d ins outs → m.Live (ins ++ outs) →
      m.readBlocks ins (B.inLens d) = some xs → B.dom d xs (τ.window B.stream m.pos (B.win d)) →
      m.Room outs (B.outLens d) →
      R.Fits d.length ins.length outs.length ∧ Fp.Apart outs (B.outLens d) ∧
        Writes .total I τ R.body (Env.frame d (ins ++ outs)) (Fp.blocks outs (B.outLens d))
          (fun m' => m'.pos = m.pos + B.win d ∧ ∃ ys, m'.readBlocks outs (B.outLens d) = some ys ∧
            B.rel d xs (τ.window B.stream m.pos (B.win d)) ys) m) :
    R.Meets I .total (B.spec adm)
```

The equation `m' = (m.updBlocks outs ys).advance _` of `BlockRel.Post` is built inside, once
(`Mem.eq_updBlocks_of_eqOff`), so no certificate ends with `eq_updBlock₂`, `peel`, `pop`. Scratch
is invisible (popped inside the body's rules); an in-place output written only in part (CGS's `R`)
is read back whole because it was readable before (`EqOff.isSome_readBlock`).

**`cert_intro [n, k] (Q, w) → (w', R) reads (qs, ws)`** (the builder's header): goal
`R.Meets I .total (B.spec adm)`. Applies `meets_of_writes`; splits `d` into the named dimensions
(by `B.nd`, `List.length_eq_*`), unfolds `adm` (`admNF`) into named operands and their
disequalities, splits the reads (`Mem.readBlocks_cons_eq_some`) into `hQ : m.store.readBlock Q.1
Q.2 (k * n) = some qs`, …, and the room (`Mem.room_cons`); proves `Fits` by `rfl` and `Apart` by
`disjoint`; leaves the `Writes` goal of the body. Failure: the header does not match `B.nd`, or
`adm` does not name the operands (a catalog predicate not tagged `admNF`).

**Contract/implementation template** (tooling plan §2; decision D5). A command

```lean
ops_contract mgsRel (dec : K → ℝ) (ε : Blas1Err) [n, k] (Q : k * n, w : n) → (w' : n, R : k + 1)
  rel MgsOut dec ε n k Q w w' R
  adm (ok : ℕ → Prop) := ok n ∧ Q.1 ≠ w.1 ∧ Q.1 ≠ R.1 ∧ w.1 ≠ R.1 ∧ w' = w
```

generating `mgsRel : BlockRel K` with its `match`es and `@[simps (attr := storeNF)]`, the
`@[admNF]` predicate, the `meets_intro` lemma in named form, the bridge lemma `runs_intro` (the
abstract theorem's destructuring), and a `#check`-able implementation skeleton
`opsImpl% [n, k] (Q, w) → (w', R) { sorry-free stub: abort }`. Its output is ordinary definitions
and lemmas, checked like hand-written ones. Phase B builds `cert_intro` first and the command
only after three contracts are written with the tactic.

---

## 10. Counts

```lean
-- Logic/Count.lean
theorem RunsFromW.of_writes (h : Writes .total I τ s ρ F P st.mem) :
    RunsFromW I W τ s ρ st (staticPeak W s ρ.idx)
      fun c m' => c ≤ staticCost s ρ.idx ∧ st.mem.store.EqOff F m'.store ∧ P m'
def RunsFromWL (I W τ s ρ st p) (Q : Count Op Tst → Mem K → Prop) : Prop :=
  ∀ st', exec I W τ s ρ st = some st' → ∃ c, St.Reach st st' c p ∧ Q c st'.mem
theorem RunsFromWL.skip, seq, call, loop, bindIdx (at every value ≤ B), of_runsFromW
theorem Count.sum_range_nsmul (p c) : ∑ _j ∈ range p, c = p • c
theorem Count.sum_range_id_nsmul (p c) : ∑ j ∈ range p, j • c = (p * (p - 1) / 2) • c
```

`RunsFromWL` is the liberal counted judgment the README lists as missing: `Table.AccountsW` for a
large implementation with data-dependent counts is proved through its rules instead of by
unfolding `exec` (the `Split` fixture is the acceptance test). **`count_eval`**: goal
`staticCost s idx = C` (or `≤`), or `Count.push T c = C`, `C` in closed form; unfolds
`staticCost`/`useCost`, evaluates indices, distributes `•` and `Count.push` (`map_add`,
`map_nsmul`, the profile's cost lemmas), rewrites the two sums, closes by `abel` after `ring_nf`
on coefficients; fails with the remaining goal.

---

## 11. Measurability for `fun_prop`

`Measurable[Tape.past ξ q] X` is out of reach of `fun_prop` because the σ-algebra on `Ω` is not
an instance. The synonym `Tape.PastAt ξ q := Ω` carries `past ξ q` as an instance;
`Tape.measurable_past_iff` (`Iff.rfl`) moves between the two; the leaves are the constants
`Tape.pastEntry ξ q i s` and `Tape.pastWindow ξ q s p k`, registered `@[fun_prop]` with the side
condition `i < q` / `p + k ≤ q` (discharged by `fun_prop (disch := omega)`). A random variable is
written with the leaves (the same term up to `rfl`). The attribute accepts the statements
(checked); phase B proves them from `TapeLaw.measurable_entry`, `measurable_windowFn_past`.

---

## 12. The builder

**Output type**: `ops% …` is a term of type `Stmt Op Tst`; `opsImpl% …` of type `Impl Op Tst`
(`Impl.mk nd nin nout tree`). The translation is a macro (`Logic/Builder.lean`): names are
resolved to positions at elaboration, and the result is the constructor term itself. So:

* the evaluator lane runs builder output directly (it *is* a `Stmt`; nothing to compile);
* `staticCost`, `link`, every rule see exactly the positional tree;
* the equality with a hand-written tree is `rfl` and is checked syntactically, not by a kernel
  computation (old M4: a compiled tree's `rfl` needed `maxRecDepth 100000`).

**Syntax.**

```
ops% [n, k] (Q, w) → (w, R) {              -- dimensions, inputs, outputs (Env.frame order)
  let t ← alloc 1;                         -- Stmt.alloc, scoped over the rest of the block
  for j < k {                              -- Stmt.loop
    call (Has.inj Blas1Op.dot) [n] (Q[j * n], w) → (R[j]);
    call (Has.inj ScalarOp.neg) [] (R[j]) → (t);
    call (Has.inj Blas1Op.axpy) [n] (t, Q[j * n], w) → (w)
  };
  call (Has.inj Blas1Op.nrm2) [n] (w) → (R[k])
}
-- also: let v ← index q (ins) ≤ bound;  if q [dims] (ins) { … } else { … };
--       while i < fuel, q [dims] (ins) { … } then { … };  ifPos e { … };  ifZero e { … };
--       skip;  abort;  { … }
```

**Scope rules.** Index variables: the dimensions, then one offset variable per operand
(`X_off`), then the binders (`for`, `index`, `while`, and an anonymous one for `ifPos`/`ifZero`,
whose body is a one-round loop). Buffer variables: the operands, then `alloc`. Inner binders
shadow; a name repeated in the header is one in-place operand and denotes its *first* occurrence
(MGS `(Q, w) → (w, R)`); to address the output copy, name the input copy differently (CGS
`(A, R₀) → (Q, R)`) — decision D6. **Offsets**: `X[e]` for an operand is `.var X_off + e₁ + e₂ +
…` with the summands of `e` added from the left, a parenthesised summand kept whole
(`C[(i * p + j)]` is `.var oC + (…)`, `R[j * p + i]` is `.var oR + .var j * .var p + .var i`);
`X` alone is `.var X_off`; for scratch `X[e]` is `e` and `X` is `.const 0`. These conventions
are what the hand-written trees of the examples use, so all of them are reproduced by `rfl`.

**Errors** at the offending name: unknown index variable, unknown buffer, a buffer used as an
index, an index used as a buffer; "not an index expression"; nesting deeper than 10 000. The
keywords `call`, `alloc`, `index`, `abort`, `ifPos`, `ifZero` are non-reserved (`&"…"`), so they
stay usable as identifiers; `for`, `let`, `if`, `while`, `then`, `else`, `skip` are Lean's
tokens already. Total `meta` definitions with a depth bound (no `partial`, rule S9).

**Checked** (`Examples/Built.lean`, `Examples/CgsWrites.lean`): `mgs`, `mgsImpl`, `gemm`, `cgs`
(whole algorithm, two allocs, three loops), a program with `index`/`if`/`while`/`ifPos`, and the
S2 block `splitB` are each `rfl`-equal to the positional tree.

**Not yet** (phase B, decisions D7, D17): scalar sugar `t := R[j] * x` and `scalar { … }`
emitting `Stmt.scalarBlock`; short operation names from the catalog (`dot` for
`Has.inj Blas1Op.dot`, by `abbrev`s in the catalog, still `rfl`); a printer back to names
(`#ops_print gemm [m, n, p] (A, B) → (C)`) for review; `frame` sub-procedures.

---

## 13. `step`, and the contract of every tactic

`step h [facts] as m₁ with x hx` is the call step on the footprint rules. Goal:
`Wp md I τ (.seq (.call o ds ins outs) c) ρ Q m`, `Wp … (.call …) … m`, or `Writes …` of either
(then `Writes.seq` and the footprints are joined). It

1. applies `Writes.then_` (or `seq`) and the rule for the shape of the outputs (`writes_call_cell`,
   `writes_call1`, `writes_call2`, `writes_call`, `writes_call_bin` for `IsFn` of `.bin`);
2. evaluates dimensions and operands by `rfl`, the shapes by `wp_shape`;
3. discharges `hadm` (`wp_adm`), `hap` (`disjoint`), `hpre` (`wp_side` with `idx` and the
   lengths of the running frame), unifying the inputs read with the reads in the context
   (`readBlock … = some qs` found by `assumption` after `keep`);
4. introduces `m₁`, its frame `hfr₁`, the outputs `x` and the relation `hx` (reduced by
   `storeNF`), and the fact that the inputs read are the known ones (substituted);
5. updates the running frame `hfr : m₀.store.EqOff F m.store` to `hfr.trans' hfr₁`, restates
   `hlen : ∀ b, m₁.store.len b = m₀.store.len b`, and runs `keep`.

**Failure**: any side goal it cannot discharge makes it fail with the goal and its name; `step!`
leaves the side goals instead, named (`hadm`, `hap`, `hpre`), for debugging. `wp_call` (chain
form) stays.

| Tactic | Goal shape | Leaves | Fails when |
|---|---|---|---|
| `step h [ts] as m₁ with x hx` | `Wp`/`Writes` of a call, or of a call followed by more | the continuation at `m₁` with `x`, `hx` | a side goal is not discharged (named in the message) |
| `frame [ts]` | `s.EqOff F s'`, `s'` a chain of `upd`/`updBlock`/`updBlocks`/`advance` over `s` or over a store with a frame hypothesis | nothing | a write is not in `F` (the membership goal is shown) |
| `fp_mem [ts]` | `F b i`, `¬ F b i` | nothing | the arithmetic after `fpNF` is not proved |
| `fp_sub [ts]` | `F ≤ G` | nothing | same |
| `disjoint [ts]` | `Fp.Disj F G`, `Fp.Apart zs ls`, `b ≠ b'`, `∀ j < n, ¬ F b (o + j)` | nothing | same |
| `idx [ts]` | offset arithmetic, `/`, `%` | nothing | not proved by omega, products, `idxNF`, nlinarith |
| `checkpoint m₁` | `Wp … m`, `m` a chain | the goal at `m₁` with `hfr₁`, reads restated | `frame` fails on the chain |
| `alloc as t₁ … tₖ` | `Writes … (.alloc …)` / `(Stmt.allocs …)` | the body at a fresh store with handles, lengths, reads | the tree is not an allocation of `k` buffers |
| `loop_inv F P with …` (and `fill`, `fillRel`, `fill₂`, `fillRel₂`) | `Writes … (.loop …)`, two loops, `whileFuel` | the start (if not closed) and the round | the tree is not a loop of that kind; monotonicity fails |
| `keep` | after a step | nothing; restates reads off the footprint | never (a fact it cannot carry stays as it is) |
| `cert_intro [ds] (ins) → (outs) reads (xs)` | `R.Meets I .total (B.spec adm)` | the body as `Writes` with named facts | header and contract do not match |
| `decode` | layer-1 goals about stored values | the mathematical goal | nothing to decode |
| `count_eval` | `staticCost s idx = C`, `Count.push T c = C` | nothing | the closed form does not match |

All of them build kernel-checked terms; none can prove a false goal. "Fail loudly": no tactic
ends in `try` around its last step, and none leaves goals it did not name (the review's
`store_simp!` item: phase B adds `store_simp!`, which fails without progress).

---

## 14. Worked example: classical Gram–Schmidt in the new style

**The program** (`Examples/Built.lean`, `rfl`-equal to `cgs` of `Examples/CgsQR.lean`):

```lean
def cgsB : Stmt Op Tst := ops% [n, p] (A, R₀) → (Q, R) {
  let t ← alloc 1;
  let v ← alloc n;
  for j < p {
    for i < j {
      call (Has.inj Blas1Op.dot) [n] (Q[i * n], A[j * n]) → (R[j * p + i])
    };
    call (Has.inj Blas1Op.copy) [n] (A[j * n]) → (v);
    for i < j {
      call (Has.inj ScalarOp.neg) [] (R[j * p + i]) → (t);
      call (Has.inj Blas1Op.axpy) [n] (t, Q[i * n], v) → (v)
    };
    call (Has.inj Blas1Op.nrm2) [n] (v) → (R[j * p + j]);
    call (Has.inj Blas1Op.scal) [n] (R[j * p + j], v) → (v);
    call (Has.inj Blas1Op.copy) [n] (v) → (Q[j * n])
  }
}
```

**The column** (statement in `Examples/CgsWrites.lean`, proof sketched; it replaces
`wp_cgsDots`, `wp_cgsProj`, `wp_cgsCol`, 117 lines):

```lean
theorem cgsCol_writes (hS hJ hneg hok hH hl hq ha hR hQ ht hvl) :
    Writes .total J τ cgsCol (cgsEnv H n p oA oQ oR j) (cgsColFp H n p oQ oR j)
      (fun m' => m'.pos = pos ∧ ∃ rp ρ qj,
        m'.store.readBlock (H .R) (oR + j * p) (j + 1) = some (rp ++ [ρ]) ∧
        m'.store.readBlock (H .Q) (oQ + j * n) n = some qj ∧ CgsCol dec ε n j qs a rp ρ qj)
      ⟨s, pos⟩ := by
  -- r_ij := q_iᵀ a_j for i < j: a relational fill of R[j p, j p + j)
  loop_inv fillRel (fun i x => IsDotErr dec (ε.dot n) n (fun l => vec qs (i * n + l)) (vec a) x)
    (fun _ => pos) as m₁ ⟨rp, hrp, hd⟩
  · step hJ.dot [hH.eq_iff] with v hv
    exact ⟨⟨v, ‹_›, by decode at hv ⊢; exact hv⟩, rfl⟩
  -- v := a_j
  step hJ.copy [hH.eq_iff] as m₂ with w₀ hw₀
  -- v := v - r_ij q_i for i < j
  loop_inv (fun _ => inBuf (H .t) ⊔ inBuf (H .v))
    (fun i m' => ∃ w, m'.store.readBlock (H .v) 0 n = some w ∧
      AxpyChain dec ε.axpy n (fun i l => vec qs (i * n + l)) rp (vec a) i (vec w)) as m₃ ⟨w, hw, hc⟩
  · step (hS .neg) as m'
    step hJ.axpy [hH.eq_iff] as m'' with zs hzl hzs
    exact ⟨zs, ‹_›, hc.step (hneg _) (by decode at hzs ⊢; exact hzs)⟩
  step hJ.nrm2 [hH.eq_iff] as m₄ with ρ hρ
  step hJ.scal [hH.eq_iff] as m₅ with zs hzl hzs
  step hJ.copy [hH.eq_iff] as m₆ with qj hqj
  exact ⟨hpos, rp, ρ, qj, by keep, ‹_›, ⟨hd, w, hc, hρ, hqj ▸ hzs⟩⟩   -- footprint: fp_sub, by `step`
```

What is gone: the two loop lemmas with their `∃ s', …` invariants, `hin : i * n + n ≤ j * n`
(twice, `idx`), `hlen`/`hlive`/`hrq`/`hra`/`hgr` (running frame and `keep`), the
`Store.getD_drop_take` congruences (`decode`), the eight-line frame chain at the end (`fp_sub`
against the running frame), `Store.readBlock_upd_concat` (the fill rule).

**The algorithm and its certificate** (replaces `wp_cgs`, `CgsCols.succ`, `cgsH`,
`cgsH_injective`, `cgs_spec`, about 190 lines):

```lean
theorem cgs_spec … : cgsImpl.Meets J .total ((cgsRel dec ε).spec (CgsOperands ok)) := by
  cert_intro [n, p] (A, R₀) → (Q, R) reads (as, r₀)
  alloc as t v
  loop_inv (fun j => inBlock Q.1 Q.2 (j * n) ⊔ inBlock R.1 R.2 (j * p) ⊔ inBuf t ⊔ inBuf v)
    (fun j m' => m'.pos = m.pos ∧ CgsCols dec ε n p Q R as j m'.store)
    with j hj m₁ hfr ⟨hpos, hcols⟩
  · obtain ⟨qs, hqs, -⟩ := hcols
    refine (cgsCol_writes hS hJ hneg hok (cgsH_injective …) (by store_simp) hqs (by keep)
      (by idx) (by idx) (by store_simp) (by store_simp)).mono (by fp_sub)
      fun m₂ hfr₂ ⟨hpos₂, rp, ρ, qj, hR', hQ', hcol⟩ => ⟨hpos₂.trans hpos, hcols.succ hR' hQ' hcol⟩
  · obtain ⟨qs, hqs, hc⟩ := hcols
    exact ⟨rfl, by disjoint, hpos, [qs, rs], by store_simp, cgsOut_of_cols hc⟩
```

`CgsCols` keeps its meaning but is stated with `HoldsMatUpto` of the layout `⟨Q, oQ, n, p, n⟩`
(by columns), so `CgsCols.succ` loses its `take`/`drop` arithmetic (35 → about 12 lines).

**Counts and the abstract theorem.** `staticCost_cgs` by `count_eval` to
`(p * (p - 1) / 2) • (dot + neg + axpy) + p • (copy + nrm2 + scal + copy)` (closed form, instead of
the `Finset.sum` the corollaries carry today); `runs_cgs_rounded` is the bridge plus `cert_intro`'s
companion lemma for the destructuring (`map_length_eq_two` disappears).

**MGS** (127 today): `cert_intro [n, k] (Q, w) → (w', R) reads (qs, ws)`; `alloc as t`;
`loop_inv` with `F j = inBlock w.1 w.2 n ⊔ inBlock R.1 R.2 j ⊔ inBuf t` and `P j` = the
recurrence; three `step`s and a three-line `exact` in the round; one `step` and a two-line exit.
`MgsInv`, `wp_mgs_step`, `wp_mgs` (77 lines) become one proof of about 20 lines.

**gemm** (96 today): `cert_intro [m, n, p] (A, B) → (C) reads (as, bs)`; `loop_inv fillRel₂`
on the layout `⟨C.1, C.2, p, m, p⟩` (rows of `C` are columns of `Cᵀ`) with `R j i x :=
GemmEntry … i j x`; one `step hJ.dot` and one `exact` in the round. `GemmInv`, `div_mod_of_lt`,
`wp_gemm` and the destructuring of `gemm_spec` disappear.

**Projected program-logic lines** (same count as the README: declarations of the program-logic
part, docstrings included; now *including* the contract and the certificate, which today are an
extra 38 / 45 / 81 lines; mathematics unchanged and not counted):

| | today: run proofs + certificate | projected | of which statements (contract, defs, theorem headers) |
|---|---|---|---|
| gemm | 96 + 38 = 134 | about 40 | about 25 |
| modified Gram–Schmidt | 127 + 45 = 172 | about 50 | about 30 |
| classical Gram–Schmidt | 329 + 81 = 410 | about 120 | about 60 |

Against the reviews' baseline (gemm 105, MGS 160, CGS 400 for the program-logic part alone) that
is a factor of 2.5 to 3.5. More important than the count (memory: judge by difficulty): every
remaining line is either a statement, an invariant (mathematics), a `step`, or an `exact` of the
mathematical relation. No frame, length, index or destructuring line is written by hand. A line
that still needs thought after phase B is a missing rule, and goes in the "missing
infrastructure" log.

---

## 15. Scale: an S2-flavoured block

`splitB` (`Examples/CgsWrites.lean`, `rfl`-equal to its positional tree): read `k₊ ≤ k` from a
cell, allocate the `k × k` test matrix `G`, fill it from the tape (2-D), allocate `Y`, call a
kernel `Y := M G`, copy the first `k₊` columns out (a loop over a data-dependent count).

```lean
def splitB (toNat : Tst) (draw mm copy : Op) : Stmt Op Tst :=
  ops% [k] (Mat, c) → (Out) {
    let kp ← index toNat (c) ≤ k;
    let G ← alloc k * k;
    for j < k { for i < k { call draw [] () → (G[j * k + i]) } };
    let Y ← alloc k * k;
    call mm [k, k, k] (Mat, G) → (Y);
    for j < kp { call copy [k] (Y[j * k]) → (Out[j * k]) }
  }
```

Proof sketch (contracts: `IsToNat` for the index, `drawRel` for `draw`, a functional `of2`
contract for `mm` with `IsMatMulErr`, `copyRel`):

```lean
theorem splitB_writes … :
    Writes .total I τ (splitB toNat draw mm copy) (Env.frame [k] [Mat, c, Out])
      (inBlock Out.1 Out.2 (k * k))
      (fun m' => m'.pos = m.pos + k * k ∧ ∃ Y, IsMatMulErr … (decMat dec k k Mt)
        (decMat dec k k (gauss m.pos)) Y ∧
        m'.store.HoldsMat ⟨Out.1, Out.2, k, kp x, k⟩ Y) m := by
  refine writes_bindIdx_of_isIndex hToNat rfl rfl hc (hToNat.index_eq hx) (clamp_le …) ?_
  alloc as G
  refine (writes_fill₂ ⟨G, 0, k, k, k⟩ rfl (fun _ => rfl) (gauss m.pos) (m.pos + ·) rfl
    fun j hj i hi m' hfr hG hpos => ?_).seq fun m₁ hfr₁ ⟨hG, hpos₁⟩ => ?_
  · step hDraw as m'' with g hg; exact ⟨by rw [hg]; decode, by idx⟩
  alloc as Y
  step hmm as m₂ with y hy
  loop_inv (fun j => inBlock Out.1 Out.2 (j * k))
    (fun j m' => m'.store.HoldsMatUpto ⟨Out.1, Out.2, k, kp x, k⟩ (cols y) j 0) with j hj m₃ hfr hP
  · step hcopy [hY] as m₄ with ys hys; exact hP.snoc_col hys
  exact ⟨by idx, _, hy, hP.cols⟩
```

About 20 lines for a block with an index binder, two scratch buffers, a 2-D fill from the tape,
a kernel call and a data-dependent loop. The counts at the data-dependent `k₊`: the same block
under `RunsFromW.bindIdx` (charged at the value read) and `RunsFromW.of_writes` for the rest
(static), giving `Count.test toNat [] + k² • draw + mm[k,k,k] + k₊ • copy[k]`. What it needs
that is not in this layer: the catalog entries `mm` (with `IsMatMulErr`), `toNat` already exists
(`IsToNat`), the coupling of rounded draws to Gaussians (review M5).

---

## 16. Placement, consumers, material

* **Placement.** All new declarations are in `NLAlib/Ops/Logic/` (namespace `NLAlib.Ops`), next
  to `NLAlib/Ops/Logic.lean` (the `Wp` rules); the examples in `NLAlib/Ops/Examples/`. Additions
  outside the new files in phase B: one line in `StoreSimp.lean` (`idx` in `store_side`), and
  `store_simp!` there. `Fp.cells` lives in `Scalar.lean` and `Stmt.allocs`, `Fp.above` in
  `Writes.lean` (their only users); they move to `Footprint.lean` if a second user appears.
* **Consumers.** Every algorithm proof of the port (CG, Lanczos, Hutch, NoisyPower, EIGH/S2,
  shifted QR) through `Writes` and the tactics; the evaluator lane through the builder's output;
  the target linter (it reads plain `Stmt` terms). The yardstick (a fresh model with the playbook
  and the catalog) uses the builder, `step`, `loop_inv`, `alloc as`, `cert_intro`.
* **Material.** Old core (`origin/main`): `ProgramLogic`, `RoutineSpec` (mode-generic specs,
  `Needs`), `RoutineAlloc` (`allocBind_named`, `spec_allocBind_chain`), `StraightLine`
  (`spec_scalarBlock`, one lemma per output), `RunEquiv` (the 25-minute kernel `rfl`: avoided by
  construction, the builder output is the tree), `RoutineWhile`; `docs/contributing/programs.md`
  "Proving a program". Reused as ideas; no code ported.

---

## 17. Open decisions for the maintainer

Each with options and a recommendation.

* **D1. Name of the judgment.** (a) `Writes` ("`c` writes only `F` and establishes `P`"); (b)
  `Spec` (old `RoutineSpec`); (c) `Blk`. *Recommend (a)*: it says what the footprint means, and
  `Spec` collides in reading with `BlockRel.spec` and `Contract.spec`.
* **D2. Named states by default.** (a) `step` always names the new memory (chain form only via
  `wp_call`); (b) chains by default, `checkpoint` on demand. *Recommend (a)*: chains are what made
  `store_simp` slow and what the review flags at 40 calls; named states cost nothing in a step.
* **D3. Footprints as predicates** (as `EqOff` has them) with a normal form, or as explicit lists
  of blocks with decidable membership (the old core). *Recommend predicates*: no change to the
  core, loop families are natural; lists only as `Fp.blocks` for call outputs.
* **D4. Outputs read back only when apart.** `writes_call` requires `Fp.Apart` of the outputs (the
  catalog's `adm` gives it: `OutApart`, `MgsOperands`, `CgsOperands`). Overlapping outputs keep
  the chain form. Alternative: read back the last-written value of every cell. *Recommend
  requiring apartness.*
* **D5. Contract template.** (a) tactic `cert_intro` only; (b) also the command `ops_contract`
  generating the contract, `admNF` predicate, intro/bridge lemmas and an implementation stub.
  *Recommend (a) now, (b) after three contracts are written with (a)* — a generator is worth it
  only once its output shape is stable.
* **D6. In-place operands in the builder.** (a) a repeated name denotes its first occurrence (MGS
  as written today) and a distinct name addresses the second (CGS: `R₀`, `R`); (b) repeated names
  are an error, always name both copies. *Recommend (a)*, with the playbook rule "name the input
  copy `X₀` when the program reads the output copy".
* **D7. Scalar sugar in the builder** (`t := R[j] * x`, `scalar { … }` emitting
  `Stmt.scalarBlock`). It hard-codes the `ScalarOp` names (`Has.inj ScalarOp.mul`). *Recommend
  yes* (phase B); and catalog `abbrev`s `dot`, `axpy`, … for operation names.
* **D8. Matrix layout.** (a) by columns with a leading dimension, by rows as the transpose
  (BLAS/LAPACK); (b) general strides `off + i * rs + j * cs`. *Recommend (a)*; (b) when a program
  needs a non-unit row stride.
* **D9. Complex interleaved pairs** (`pairLayout`, S2). *Recommend: add with the S2 catalog*
  (`zcopy`, complex `mm`), not now.
* **D10. Power of `idx`.** (a) omega + product generation from loop-variable bounds, `nlinarith`
  only in `idx!`; (b) `nlinarith` in the default. *Recommend (a)*: predictable time; `nlinarith`
  is the slow path the review measured.
* **D11. Measurability**: the synonym `Tape.PastAt` with constant leaves (no core change) vs a
  Mathlib `Filtration` on `Ω` with instances (core change in `TapeLaw`). *Recommend the synonym.*
* **D12. `RunsFromWL`** in the logic layer (`Logic/Count.lean`) vs the core (`Counted.lean`).
  *Recommend the logic layer*: it is a derived judgment, not trusted.
* **D13. Keep `wp_call` (chain form)** next to `step`? *Recommend keep* (three-line blocks, exact
  final equations); the playbook teaches `step` first.
* **D14. Rule S9 and `meta` code.** The builder uses total definitions with a depth bound to pass
  S9 (`partial` is flagged even in `meta` code, which never reaches the kernel). (a) keep the
  bound; (b) exempt `meta` definitions from S9. *Recommend (b)* in the rules data (`exempt`), and
  keep (a) until then.
* **D15. `Logic.lean` and `Logic/`.** A file and a directory of the same name. (a) keep; (b)
  move `Logic.lean` to `Logic/Wp.lean`. *Recommend (b)* in phase B (cleaner, one rename).
* **D16. The `Tactic.lean` aggregator flag (P2)** for files of tactics only, as for the core's
  `Attr.lean`: an allowlist entry (data) rather than moving tactics into theorem files.
  *Recommend the allowlist entry.*
* **D17. A printer back to names** (review K2) for reviewing builder output: `#ops_print t [header]`
  printing the tree with names. *Recommend phase B, small.*

---

## 18. Phase B plan

1. Prove `Footprint`, `Index`, `Writes` (calls, alloc, branches, `meets_of_writes`) and `Loop`
   (`writes_loop` first; the others as corollaries of it). Wire `idx` into `store_side`; add
   `store_simp!`.
2. Implement `step`, `keep`, `alloc as`, `loop_inv`, `cert_intro`, `checkpoint`; harden `frame`,
   `fp_mem`, `disjoint`, `idx` (product generation) with the probes: the S2 slot offset, the
   hundred-buffer fixture, the K3 layouts.
3. Rewrite gemm, MGS, CGS in the new style next to the old proofs; measure lines and elaboration
   time; then delete the old proofs (no compatibility).
4. Scalar block, layouts, `decode`, `count_eval`, `RunsFromWL` (Split fixture), `TapeMeas`
   (Hutch's law-level step), builder sugar (D7) and printer (D17).
5. Playbook section "Proving a program" for the new core, written for the yardstick reader.

Risk: `step` is a macro over several `first` alternatives; elaboration time per call is measured
on CGS (today 0.2 s more per call than the hand-written rule); if a call costs more than 0.5 s,
the shape is chosen by a small elaborator that inspects `hb` instead of trying rules in turn.
