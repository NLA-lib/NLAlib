/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.GolubKahan.Band.StoredExtension
public import NLAlib.Matrix.Factorizations.BasisExtensionContract
public import NLAlib.Ops.Blas.Sampling
public import NLAlib.Ops.Catalog.OperatorPair
public import NLAlib.Ops.Cert

/-!
# Block Golub–Kahan bidiagonalization with full reorthogonalization as one fixed program

The driver is written against three groups of operations and does no arithmetic of its own:
the extension of a stored basis by a block (`NLAlib.Ops.OrthOp.extend`), the products with a
matrix $\mathbf{A}$ and with $\mathbf{A}^{\mathsf{H}}$ (`NLAlib.Ops.OperatorPairOp`), and scalar
draws from a tape stream. With $N = qb$:

```
draw Ω (n × b);  V block 0, G := extend(∅, Ω)
for j < q:  U block j,   block column j of R := extend(U blocks < j, A · (V block j))
            V block j+1, block column j of S := extend(V blocks ≤ j, Aᴴ · (U block j))
```

Full reorthogonalization is the fact that every extension is against all stored columns of its
side. A concrete orthogonalization scheme is an implementation of `extend` proved against the
contract (`NLAlib.Ops.extendRel`, `NLAlib.Ops.exactExtendRel`) and substituted by linking. The
stored-run predicates of this file are related to the pure relations
`NLAlib.IsBlockGolubKahan` and `NLAlib.IsBlockGolubKahanErr` in
`NLAlib/Krylov/GolubKahan/Band/Run.lean`. Design: `docs/design/LowRank-BlockLanczos.md` §3.

**Storage.** All blocks are column-major, one word per entry. `U` has `q * b * m` words and `V`
has `(q + 1) * b * n`; a new block is written by `extend` directly after the stored columns of
its side. `G` holds the `b * b` coefficients of the start block. `R` and `S` are packed by block
column: block column `j` of `R` is the `(j * b + b) × b` coefficient block of the extension of
the `j * b` stored columns of `U`, at the offset `b * b * (j * (j + 1) / 2)`, and block column
`j` of `S` is the `((j + 1) * b + b) × b` block of the extension of the `(j + 1) * b` stored
columns of `V`, at the offset `b * b * (j * (j + 3) / 2)`. The scratch block of
`max m n * b` words holds the drawn block and then the products; it is released at the end.

## Main definitions

* `NLAlib.Krylov.GolubKahan.Band.applyColumns`, `NLAlib.Krylov.GolubKahan.Band.step`,
  `NLAlib.Krylov.GolubKahan.Band.solve`, `NLAlib.Krylov.GolubKahan.Band.program`: the program.
* `NLAlib.Krylov.GolubKahan.Band.coefOffsetR`, `NLAlib.Krylov.GolubKahan.Band.coefOffsetS`,
  `NLAlib.Krylov.GolubKahan.Band.outLens`: the packed layout.
* `NLAlib.Krylov.GolubKahan.Band.IsStoredRun`, `NLAlib.Krylov.GolubKahan.Band.IsExactStoredRun`,
  `NLAlib.Krylov.GolubKahan.Band.IsRoundedStoredRun`, `NLAlib.Krylov.GolubKahan.Band.StoredOut`:
  the relation between the stored blocks of a run, block by block.
* `NLAlib.Krylov.GolubKahan.Band.solveRel`, `NLAlib.Krylov.GolubKahan.Band.Rounded.solveRel`:
  the contracts of the program.
* `NLAlib.Krylov.GolubKahan.Band.AppliesColumns`, `NLAlib.Krylov.GolubKahan.Band.stepFp`,
  `NLAlib.Krylov.GolubKahan.Band.StoredPrefix`: the form in which the driver uses a product, the
  cells of a block step, and the loop invariant.

## Main results

* `NLAlib.Krylov.GolubKahan.Band.extendPred_of_eq_zero`: an extension of the empty basis does not
  depend on the name of the empty column type.
* `NLAlib.Krylov.GolubKahan.Band.coefOffsetR_succ`,
  `NLAlib.Krylov.GolubKahan.Band.coefOffsetS_succ`: consecutive block columns are adjacent.
* `NLAlib.Krylov.GolubKahan.Band.writes_applyColumns_of`,
  `NLAlib.Krylov.GolubKahan.Band.writes_applyColumns`,
  `NLAlib.Krylov.GolubKahan.Band.writes_applyColumns_error`: a block of products.
* `NLAlib.Krylov.GolubKahan.Band.writes_step_of`, `NLAlib.Krylov.GolubKahan.Band.writes_steps`,
  `NLAlib.Krylov.GolubKahan.Band.StoredPrefix.succ`,
  `NLAlib.Krylov.GolubKahan.Band.StoredPrefix.exists_storedOut`,
  `NLAlib.Krylov.GolubKahan.Band.solve_writes_of`, `NLAlib.Krylov.GolubKahan.Band.solve_spec_of`:
  one proof of the driver for any contracts of the products and of the extension, of which the
  exact and the rounded theorems are instances.
* `NLAlib.Krylov.GolubKahan.Band.solve_writes`, `NLAlib.Krylov.GolubKahan.Band.solve_spec`:
  total execution under the exact contracts; the stored blocks are exact extensions.
* `NLAlib.Krylov.GolubKahan.Band.Rounded.solve_writes`,
  `NLAlib.Krylov.GolubKahan.Band.Rounded.solve_spec`: total execution under the rounded
  contracts, with the executed history.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.GolubKahan.Band

open Ops

variable {K Op Tst : Type}

/-! ### The program -/

/-- Apply the operation `o` (a product with a fixed `m × n` matrix) to each of the `b` columns
of the column-major block `X`, writing the `b` products as the column-major block `Y`. Input
and output are in different buffers. -/
def applyColumns (o : Op) : Impl Op Tst := opsImpl% [m, n, b] (X) → (Y) {
  for c < b {
    call o [m, n] (X[c * n]) → (Y[c * m])
  }
}

variable [Has OrthOp Op] [Has OperatorPairOp Op]

/-- Block step `j`: the products of $\mathbf{A}$ with block `j` of `V` are extended against the
`j * b` stored columns of `U`, giving block `j` of `U` and block column `j` of `R`; then the
products of $\mathbf{A}^{\mathsf{H}}$ with block `j` of `U` are extended against the
`(j + 1) * b` stored columns of `V`, giving block `j + 1` of `V` and block column `j` of `S`.
The scratch block `W` holds the products. -/
def step : Impl Op Tst := opsImpl% [m, n, b, j] (U, V, R, S, W) → () {
  run (applyColumns (Has.inj OperatorPairOp.matvec)).body [m, n, b] (V[j * b * n], W);
  call (Has.inj OrthOp.extend) [m, j * b, b] (U, W) →
    (U[j * b * m], W, R[b * b * (j * (j + 1) / 2)]);
  run (applyColumns (Has.inj OperatorPairOp.rmatvec)).body [n, m, b] (U[j * b * m], W);
  call (Has.inj OrthOp.extend) [n, (j + 1) * b, b] (V, W) →
    (V[(j + 1) * b * n], W, S[b * b * (j * (j + 3) / 2)])
}

variable [Has SampleOp Op]

/-- Block Golub–Kahan bidiagonalization with full reorthogonalization, at the dimensions
`[m, n, b, q]`: draw the `n × b` start block from the stream into the scratch block, extend the
empty basis by it (block `0` of `V` and the start coefficients `G`), and run `q` block steps.
The outputs are `U` (`q * b * m` words), `V` (`(q + 1) * b * n`), `G` (`b * b`) and the packed
coefficients `R` and `S`. The scratch block has `max m n * b` words. -/
def solve (stream : ℕ) : Impl Op Tst := opsImpl% [m, n, b, q] () → (U, V, G, R, S) {
  let W ← alloc ((m + (n - m)) * b);
  run (sampleVector stream).body [n * b] (W);
  call (Has.inj OrthOp.extend) [n, 0, b] (V, W) → (V, W, G);
  for j < q {
    run step.body [m, n, b, j] (U, V, R, S, W)
  }
}

/-- The fixed program: four dimensions `[m, n, b, q]` and the five output buffers `U`, `V`,
`G`, `R`, `S`. -/
def program (stream : ℕ) : Program Op Tst 4 5 :=
  (solve stream).program 5 []
    [⟨0, .const 0⟩, ⟨1, .const 0⟩, ⟨2, .const 0⟩, ⟨3, .const 0⟩, ⟨4, .const 0⟩]

/-! ### The packed layout -/

/-- The offset of block column $j$ of the packed coefficients of the left basis: block column
$i$ has $(ib + b)b$ words, so the offset is $b^2 j(j+1)/2$. -/
def coefOffsetR (b j : ℕ) : ℕ := b * b * (j * (j + 1) / 2)

/-- The offset of block column $j$ of the packed coefficients of the right basis: block column
$i$ has $((i+1)b + b)b$ words, so the offset is $b^2 j(j+3)/2$. -/
def coefOffsetS (b j : ℕ) : ℕ := b * b * (j * (j + 3) / 2)

/-- Block column $j + 1$ of the packed coefficients of the left basis starts where block column
$j$, of $(jb + b)b$ words, ends. -/
theorem coefOffsetR_succ (b j : ℕ) :
    coefOffsetR b (j + 1) = coefOffsetR b j + (j * b + b) * b := by
  have h : (j + 1) * (j + 1 + 1) = j * (j + 1) + 2 * (j + 1) := by ring
  rw [coefOffsetR, coefOffsetR, h, Nat.add_mul_div_left _ _ (by norm_num)]
  ring

/-- Block column $j + 1$ of the packed coefficients of the right basis starts where block
column $j$, of $((j+1)b + b)b$ words, ends. -/
theorem coefOffsetS_succ (b j : ℕ) :
    coefOffsetS b (j + 1) = coefOffsetS b j + ((j + 1) * b + b) * b := by
  have h : (j + 1) * (j + 1 + 3) = j * (j + 3) + 2 * (j + 2) := by ring
  rw [coefOffsetS, coefOffsetS, h, Nat.add_mul_div_left _ _ (by norm_num)]
  ring

/-- Block $i$ of $b$ columns of length $n$ ends before block $j$ starts, $i < j$. -/
theorem block_le {i j : ℕ} (h : i < j) (b n : ℕ) : i * b * n + b * n ≤ j * b * n := by
  have := Nat.mul_le_mul_right n (Idx.mul_add_le_mul h b)
  rwa [Nat.add_mul] at this

/-- The offsets of the packed coefficients of the left basis are monotone. -/
theorem coefOffsetR_mono (b : ℕ) {i j : ℕ} (h : i ≤ j) : coefOffsetR b i ≤ coefOffsetR b j :=
  Nat.mul_le_mul_left _ (Nat.div_le_div_right (Nat.mul_le_mul h (Nat.add_le_add_right h 1)))

/-- The offsets of the packed coefficients of the right basis are monotone. -/
theorem coefOffsetS_mono (b : ℕ) {i j : ℕ} (h : i ≤ j) : coefOffsetS b i ≤ coefOffsetS b j :=
  Nat.mul_le_mul_left _ (Nat.div_le_div_right (Nat.mul_le_mul h (Nat.add_le_add_right h 3)))

/-- The lengths of the five output blocks `U`, `V`, `G`, `R`, `S` at the dimensions
`[m, n, b, q]`. -/
def outLens (m n b q : ℕ) : List ℕ :=
  [q * b * m, (q + 1) * b * n, b * b, coefOffsetR b q, coefOffsetS b q]

/-! ### The relation between the stored blocks -/

/-- A predicate on the matrices of a run at the dimensions $(m, n, b, q)$: the start block
$\mathbf{\Omega}$, the bases $\mathbf{U}$ ($m \times qb$) and $\mathbf{V}$
($n \times (q+1)b$), the start coefficients $\mathbf{G}$ and the block columns of the
coefficients of the left and of the right basis. -/
abbrev RunPred (m n b q : ℕ) : Type :=
  Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin (q * b)) ℝ →
    Matrix (Fin n) (Fin ((q + 1) * b)) ℝ → Matrix (Fin b) (Fin b) ℝ →
    ((j : ℕ) → Matrix (Fin (j * b + b)) (Fin b) ℝ) →
    ((j : ℕ) → Matrix (Fin ((j + 1) * b + b)) (Fin b) ℝ) → Prop

/-- **The stored blocks of a run are related block by block**, for an extension predicate `Ext`
and relations `Mv`, `Rmv` between a block and the block of its computed products with
$\mathbf{A}$ and with $\mathbf{A}^{\mathsf{H}}$. Block $0$ of $\mathbf{V}$ and $\mathbf{G}$
extend the empty basis by $\mathbf{\Omega}$; the empty basis is the prefix of zero blocks of
$\mathbf{V}$, with column type `Fin (0 * b)`, as in `NLAlib.IsBlockGolubKahan`. For every
$j < q$: block $j$ of $\mathbf{U}$ and
block column $j$ of the left coefficients extend the first $j$ blocks of $\mathbf{U}$ by a
product block of block $j$ of $\mathbf{V}$; block $j + 1$ of $\mathbf{V}$ and block column $j$
of the right coefficients extend the first $j + 1$ blocks of $\mathbf{V}$ by a product block of
block $j$ of $\mathbf{U}$. The upper part of a coefficient block column is the coefficient block
against the old columns and its lower $b$ rows the block against the new ones. -/
structure IsStoredRun {m n b q : ℕ} (Ext : ExtendPred ℝ)
    (Mv : Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin b) ℝ → Prop)
    (Rmv : Matrix (Fin m) (Fin b) ℝ → Matrix (Fin n) (Fin b) ℝ → Prop)
    (Ω : Matrix (Fin n) (Fin b) ℝ) (U : Matrix (Fin m) (Fin (q * b)) ℝ)
    (V : Matrix (Fin n) (Fin ((q + 1) * b)) ℝ) (G : Matrix (Fin b) (Fin b) ℝ)
    (R : (j : ℕ) → Matrix (Fin (j * b + b)) (Fin b) ℝ)
    (S : (j : ℕ) → Matrix (Fin ((j + 1) * b + b)) (Fin b) ℝ) : Prop where
  /-- The start block: block $0$ of $\mathbf{V}$ extends the empty basis, the prefix of zero
  blocks of $\mathbf{V}$, by $\mathbf{\Omega}$. -/
  start : Ext n (0 * b) b (blockPrefix b V 0) Ω (blockCols b V 0) 0 G
  /-- Block $j$ of $\mathbf{U}$ extends the first $j$ blocks of $\mathbf{U}$ by the products of
  $\mathbf{A}$ with block $j$ of $\mathbf{V}$. -/
  left : ∀ j < q, ∃ W, Mv (blockCols b V j) W ∧
    Ext m (j * b) b (blockPrefix b U j) W (blockCols b U j) (coefTop (R j)) (coefBot (R j))
  /-- Block $j + 1$ of $\mathbf{V}$ extends the first $j + 1$ blocks of $\mathbf{V}$ by the
  products of $\mathbf{A}^{\mathsf{H}}$ with block $j$ of $\mathbf{U}$. -/
  right : ∀ j < q, ∃ W, Rmv (blockCols b U j) W ∧
    Ext n ((j + 1) * b) b (blockPrefix b V (j + 1)) W (blockCols b V (j + 1))
      (coefTop (S j)) (coefBot (S j))

/-- An extension of the empty basis is an extension of every basis with no columns: a predicate
`Ext` on the matrices of a basis extension that holds at the basis with column type `Fin 0`, as
returned by a call at the dimensions `[n, 0, b]`, holds at every basis $\mathbf{Q}$ and
coefficient block $\mathbf{H}$ with column and row type `Fin k`, $k = 0$; in particular at
`Fin (0 * b)`, the form of the start block in
`NLAlib.Krylov.GolubKahan.Band.IsStoredRun`. -/
theorem extendPred_of_eq_zero (Ext : ExtendPred ℝ) {n k b : ℕ} (hk : k = 0)
    (Q : Matrix (Fin n) (Fin k) ℝ) (H : Matrix (Fin k) (Fin b) ℝ)
    {W Q' : Matrix (Fin n) (Fin b) ℝ} {R : Matrix (Fin b) (Fin b) ℝ}
    (h : Ext n 0 b 0 W Q' 0 R) : Ext n k b Q W Q' H R := by
  subst hk
  have hQ : Q = 0 := by
    ext i j
    exact j.elim0
  have hH : H = 0 := by
    ext i j
    exact i.elim0
  rw [hQ, hH]
  exact h

/-- The stored blocks of an exact run: every extension is exact (`NLAlib.IsBasisExtension`) and
the extended blocks are the products $\mathbf{A}\mathbf{V}_j$ and
$\mathbf{A}^{\mathsf{H}}\mathbf{U}_j$ of the stored blocks. -/
def IsExactStoredRun {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b q : ℕ) : RunPred m n b q :=
  IsStoredRun (fun _ _ _ Q W Q' H R => IsBasisExtension Q W Q' H R)
    (fun X W => W = A * X) (fun X W => W = Aᴴ * X)

/-- The stored blocks of a rounded run, the executed history: every extension is a rounded
extension with parameters $(\eta_0, \mu, \varepsilon)$ (`NLAlib.IsBasisExtensionErr`) of a
computed product block $\mathbf{W}$, whose column $c$ satisfies
$\|\mathbf{A}\mathbf{x}_c - \mathbf{w}_c\| \le \delta\|\mathbf{x}_c\|$ for the products with
$\mathbf{A}$ and $\|\mathbf{A}^{\mathsf{H}}\mathbf{x}_c - \mathbf{w}_c\| \le
\delta'\|\mathbf{x}_c\|$ for the products with $\mathbf{A}^{\mathsf{H}}$, $\mathbf{x}_c$ the
column of the stored block and the norm the Euclidean norm. -/
def IsRoundedStoredRun {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (δ δ' η₀ μ ε : ℝ) (b q : ℕ) :
    RunPred m n b q :=
  IsStoredRun (fun _ _ _ Q W Q' H R => IsBasisExtensionErr η₀ μ ε Q W Q' H R)
    (fun X W => ∀ c, ‖WithLp.toLp 2 (A *ᵥ X.col c - W.col c)‖ ≤ δ * ‖WithLp.toLp 2 (X.col c)‖)
    (fun X W => ∀ c, ‖WithLp.toLp 2 (Aᴴ *ᵥ X.col c - W.col c)‖ ≤ δ' * ‖WithLp.toLp 2 (X.col c)‖)

variable [Inhabited K]

/-- The run predicate `Run` holds of the decoded words: the window `ω` of the tape (the start
block), the words `us`, `vs`, `gs` of the bases and of the start coefficients, and the packed
coefficient words `rs`, `ss`, whose block column `j` starts at the offset
`NLAlib.Krylov.GolubKahan.Band.coefOffsetR` resp.
`NLAlib.Krylov.GolubKahan.Band.coefOffsetS`. -/
def StoredOut (dec : K → ℝ) (m n b q : ℕ) (Run : RunPred m n b q)
    (ω us vs gs rs ss : List K) : Prop :=
  Run (decodeMatrix dec n b ω) (decodeMatrix dec m (q * b) us)
    (decodeMatrix dec n ((q + 1) * b) vs) (decodeMatrix dec b b gs)
    (fun j => decodeMatrix dec (j * b + b) b (rs.drop (coefOffsetR b j)))
    (fun j => decodeMatrix dec ((j + 1) * b + b) b (ss.drop (coefOffsetS b j)))

/-- The dimensions are `[m, n, b, q]` with the row and column numbers of the matrix, there is no
input operand, and the five outputs are in distinct buffers. -/
@[admNF] def SolveOperands (m n : ℕ) : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d.headD 0 = m ∧ d.getD 1 0 = n ∧ ins = [] ∧ ∃ U V G R S,
    outs = [U, V, G, R, S] ∧ [U.1, V.1, G.1, R.1, S.1].Nodup

/-- The contract of the program for a run predicate: at the dimensions `[m, n, b, q]` the call
reads the window of `n * b` words of the stream and writes the five output blocks, whose decoded
matrices satisfy the run predicate with the decoded window as start block. -/
@[simps (attr := storeNF)]
def solveRelOf (stream : ℕ) (dec : K → ℝ) (m n : ℕ) (Run : (b q : ℕ) → RunPred m n b q) :
    BlockRel K where
  nd := 4
  stream := stream
  win d := d.getD 1 0 * d.getD 2 0
  inLens _ := []
  outLens d := outLens (d.headD 0) (d.getD 1 0) (d.getD 2 0) (d.getD 3 0)
  rel d _ ω Y := match Y with
    | [us, vs, gs, rs, ss] =>
        StoredOut dec m n (d.getD 2 0) (d.getD 3 0) (Run _ _) ω us vs gs rs ss
    | _ => False

/-- The exact contract of the program: the stored blocks are an exact run for $\mathbf{A}$ from
the drawn start block. -/
def solveRel (stream : ℕ) (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BlockRel K :=
  solveRelOf stream dec m n (IsExactStoredRun A)

/-! ### Products of a block -/

omit [Has OrthOp Op] [Has OperatorPairOp Op] [Has SampleOp Op] in
/-- A block of products, for any contract of one product. If the operation `o` meets a
contract `Rm` with the operand shape of a product with an `r × c` matrix (one input block of
length `c`, one output block of length `r` in another buffer, no window) whose relation gives
`rel` of the decoded input and output vectors, the loop over the `b` columns of the readable
block `xs` writes a block `ys` with `rel` of every pair of decoded columns. The position of the
tape does not move. Zero dimensions are included. -/
theorem writes_applyColumns_of {dec : K → ℝ} {r c b : ℕ} {Rm : BlockRel K}
    {rel : (Fin c → ℝ) → (Fin r → ℝ) → Prop} {I : Interp Op Tst K} {o : Op}
    (hA : I.Meets .total o (Rm.spec (MatvecOperands r c)))
    (hnd : Rm.nd = 2) (hwin : Rm.win [r, c] = 0) (hin : Rm.inLens [r, c] = [c])
    (hout : Rm.outLens [r, c] = [r]) (hdom : ∀ xs w, Rm.dom [r, c] xs w)
    (hrel : ∀ xs w ys, Rm.rel [r, c] [xs] w [ys] → rel (decv dec c xs) (decv dec r ys))
    {τ : Tape K} {μ : Mem K} {x y : ℕ × ℕ} {xs : List K} (hxy : x.1 ≠ y.1)
    (hl : μ.Live [x, y]) (hx : μ.store.readBlock x.1 x.2 (b * c) = some xs)
    (hy : y.2 + b * r ≤ μ.store.len y.1) :
    Writes .total I τ (applyColumns o).body (Env.frame [r, c, b] [x, y])
      (Store.inBlock y.1 y.2 (b * r))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock y.1 y.2 (b * r) = some ys ∧
        ∀ j, rel ((decodeMatrix dec c b xs).col j) ((decodeMatrix dec r b ys).col j)) μ := by
  let region : ℕ → Fp := fun j => Store.inBlock y.1 (y.2 + j * r) r
  let result : ℕ → Store K → Prop := fun j s => ∃ yc,
    s.readBlock y.1 (y.2 + j * r) r = some yc ∧
      rel (decv dec c ((xs.drop (j * c)).take c)) (decv dec r yc)
  unfold applyColumns
  dsimp only
  refine (writes_loop_disjoint region result rfl (fun j hj => Fp.inBlock_le_inBlock (by omega)
    (by have := Idx.mul_add_le_mul hj r; omega)) ?_ ?_ ?_).mono le_rfl ?_
  · intro i _ j _ hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact Fp.disj_inBlock_of_le (by have := Idx.mul_add_le_mul h r; omega)
    · exact (Fp.disj_inBlock_of_le (by have := Idx.mul_add_le_mul h r; omega)).symm
  · rintro j _ s s' hg ⟨yc, h, hp⟩
    exact ⟨yc, Store.readsOnly_readBlock _ _ _ _ s s' hg h, hp⟩
  · intro j hj μ' hfr
    have hxc : μ'.store.readBlock x.1 (x.2 + j * c) c = some ((xs.drop (j * c)).take c) :=
      Store.readBlock_sub (hfr.readBlock_of hx fun i _ hF => hxy hF.1) (Idx.mul_add_le_mul hj c)
    have hreads : μ'.readBlocks [(x.1, x.2 + j * c)] (Rm.inLens [r, c]) =
        some [(xs.drop (j * c)).take c] := by
      rw [hin]
      exact Mem.readBlocks_of_cons hxc rfl
    have hl' : μ'.Live ([(x.1, x.2 + j * c)] ++ [(y.1, y.2 + j * r)]) := by
      simpa only [List.cons_append, List.nil_append, Mem.live_cons, Mem.live_nil] using
        hl.congr hfr.length_eq
    refine (writes_call1 hA (d := [r, c]) (k := 0) (l := r) rfl rfl rfl hnd.symm hwin hout
      ⟨rfl, by simpa using hxy⟩ fun _ => ⟨hl', ⟨_, hreads, hdom _ _⟩, ?_⟩).mono le_rfl ?_
    · have := Idx.mul_add_le_mul hj r
      change y.2 + j * r + r ≤ μ'.store.len y.1
      rw [hfr.len_eq]
      omega
    · rintro μ'' - ⟨hpos, xs', yc, hxs', hyc, hr⟩
      obtain rfl := Option.some.inj (hxs'.symm.trans hreads)
      exact ⟨by simpa using hpos, yc, hyc, hrel _ _ _ hr⟩
  · rintro μ' - ⟨hpos, hcols⟩
    obtain ⟨ys, hys⟩ := exists_readBlock_of_columns b fun j hj => (hcols j hj).imp fun _ h => h.1
    refine ⟨hpos, ys, hys, fun j => ?_⟩
    obtain ⟨yc, hyc, hr⟩ := hcols j j.2
    obtain rfl := readBlock_drop_take_eq hys hyc (Idx.mul_add_le_mul j.2 r)
    rw [← decv_drop_take, ← decv_drop_take]
    exact hr

omit [Has OrthOp Op] [Has OperatorPairOp Op] [Has SampleOp Op] in
/-- A block of exact products: if the operation `o` meets the exact contract of the product with
$\mathbf{A}$, the loop over the `b` columns of the readable block `xs` writes a block that
decodes to $\mathbf{A}\mathbf{X}$, $\mathbf{X}$ the decoded input block. The output is in
another buffer; the position of the tape does not move. Zero dimensions are included. -/
theorem writes_applyColumns {dec : K → ℝ} {m n b : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Interp Op Tst K} {o : Op}
    (hA : I.Meets .total o ((matvecRel dec A).spec (MatvecOperands m n)))
    {τ : Tape K} {μ : Mem K} {x y : ℕ × ℕ} {xs : List K} (hxy : x.1 ≠ y.1)
    (hl : μ.Live [x, y]) (hx : μ.store.readBlock x.1 x.2 (b * n) = some xs)
    (hy : y.2 + b * m ≤ μ.store.len y.1) :
    Writes .total I τ (applyColumns o).body (Env.frame [m, n, b] [x, y])
      (Store.inBlock y.1 y.2 (b * m))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock y.1 y.2 (b * m) = some ys ∧
        decodeMatrix dec m b ys = A * decodeMatrix dec n b xs) μ := by
  refine (writes_applyColumns_of (rel := fun x y => y = A *ᵥ x) hA rfl rfl rfl rfl
    (fun _ _ => trivial) (fun _ _ _ h => h) hxy hl hx hy).mono le_rfl ?_
  rintro μ' - ⟨hpos, ys, hys, hcol⟩
  refine ⟨hpos, ys, hys, ?_⟩
  ext i j
  have h := congrFun (hcol j) i
  simpa [Matrix.col_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h

omit [Has OrthOp Op] [Has OperatorPairOp Op] [Has SampleOp Op] in
/-- A block of rounded products: if the operation `o` meets the normwise contract of the product
with $\mathbf{A}$ at the allowance $\delta$, the loop over the `b` columns of the readable block
`xs` writes a block whose decoded column $c$ satisfies
$\|\mathbf{A}\mathbf{x}_c - \mathbf{w}_c\| \le \delta\|\mathbf{x}_c\|$ in the Euclidean norm,
$\mathbf{x}_c$ the decoded column of the input. The output is in another buffer; the position
of the tape does not move. -/
theorem writes_applyColumns_error {dec : K → ℝ} {m n b : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {δ : ℝ} {I : Interp Op Tst K} {o : Op}
    (hA : I.Meets .total o ((matvecErrorRel dec A δ).spec (MatvecOperands m n)))
    {τ : Tape K} {μ : Mem K} {x y : ℕ × ℕ} {xs : List K} (hxy : x.1 ≠ y.1)
    (hl : μ.Live [x, y]) (hx : μ.store.readBlock x.1 x.2 (b * n) = some xs)
    (hy : y.2 + b * m ≤ μ.store.len y.1) :
    Writes .total I τ (applyColumns o).body (Env.frame [m, n, b] [x, y])
      (Store.inBlock y.1 y.2 (b * m))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock y.1 y.2 (b * m) = some ys ∧
        ∀ c, ‖WithLp.toLp 2 (A *ᵥ (decodeMatrix dec n b xs).col c -
          (decodeMatrix dec m b ys).col c)‖ ≤
            δ * ‖WithLp.toLp 2 ((decodeMatrix dec n b xs).col c)‖) μ :=
  writes_applyColumns_of
    (rel := fun x y => ‖WithLp.toLp 2 (A *ᵥ x - y)‖ ≤ δ * ‖WithLp.toLp 2 x‖) hA rfl rfl rfl rfl
    (fun _ _ => trivial) (fun _ _ _ h => h) hxy hl hx hy

/-! ### The driver for any contracts of the products and of the extension -/

/-- **The loop over the columns of a block computes a related block**: on a readable block `xs`
of `b` columns of length `c` and an output block of `b` columns of length `r` in another buffer,
`NLAlib.Krylov.GolubKahan.Band.applyColumns` with the operation `o` writes only the output
block, does not move the tape, and leaves a block whose decoded matrix is related by `Rel` to
the decoded input. It is the form in which the driver uses the products with $\mathbf{A}$ and
$\mathbf{A}^{\mathsf{H}}$, exact or rounded. -/
def AppliesColumns (dec : K → ℝ) (I : Interp Op Tst K) (o : Op) (r c b : ℕ)
    (Rel : Matrix (Fin c) (Fin b) ℝ → Matrix (Fin r) (Fin b) ℝ → Prop) : Prop :=
  ∀ (τ : Tape K) (μ : Mem K) (x y : ℕ × ℕ) (xs : List K), x.1 ≠ y.1 → μ.Live [x, y] →
    μ.store.readBlock x.1 x.2 (b * c) = some xs → y.2 + b * r ≤ μ.store.len y.1 →
    Writes .total I τ (applyColumns o).body (Env.frame [r, c, b] [x, y])
      (Store.inBlock y.1 y.2 (b * r))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock y.1 y.2 (b * r) = some ys ∧
        Rel (decodeMatrix dec c b xs) (decodeMatrix dec r b ys)) μ

/-- The cells that block step `j` may write: block `j` of `U`, block `j + 1` of `V`, block
column `j` of `R` and of `S`, and the scratch buffer. -/
def stepFp (m n b j : ℕ) (U V R S W : ℕ × ℕ) : Fp :=
  Fp.blocks [(U.1, U.2 + j * b * m), (V.1, V.2 + (j + 1) * b * n),
      (R.1, R.2 + coefOffsetR b j), (S.1, S.2 + coefOffsetS b j)]
    [b * m, b * n, (j * b + b) * b, ((j + 1) * b + b) * b] ⊔ Store.inBuf W.1

/-- The cells of block step `j < q` are in the output blocks of a run of `q` steps or in the
scratch buffers. -/
theorem stepFp_le {m n b j q L : ℕ} {U V G R S W : ℕ × ℕ} (hj : j < q) (hW : L ≤ W.1) :
    stepFp m n b j U V R S W ≤ Fp.blocks [U, V, G, R, S] (outLens m n b q) ⊔ Fp.above L := by
  have h1 := block_le hj b m
  have h2 := block_le (Nat.add_lt_add_right hj 1) b n
  have h3 := coefOffsetR_mono b (show j + 1 ≤ q from hj)
  have h4 := coefOffsetR_succ b j
  have h5 := coefOffsetS_mono b (show j + 1 ≤ q from hj)
  have h6 := coefOffsetS_succ b j
  unfold stepFp outLens
  refine sup_le (sup_le ?_ (sup_le ?_ (sup_le ?_ (sup_le ?_ bot_le))))
    fun B _ hB => Or.inr (by rw [show B = W.1 from hB]; exact hW)
  · exact le_sup_of_le_left (le_sup_of_le_left (Fp.inBlock_le_inBlock (by omega) (by omega)))
  · exact le_sup_of_le_left (le_sup_of_le_right (le_sup_of_le_left
      (Fp.inBlock_le_inBlock (by omega) (by omega))))
  · exact le_sup_of_le_left (le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right
      (le_sup_of_le_left (Fp.inBlock_le_inBlock (by omega) (by omega))))))
  · exact le_sup_of_le_left (le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right
      (le_sup_of_le_right (le_sup_of_le_left (Fp.inBlock_le_inBlock (by omega) (by omega)))))))

omit [Has SampleOp Op] in
/-- One block step, for any contracts. On the `j * b` stored columns `us` of `U` and the
`(j + 1) * b` stored columns `vs` of `V`, in five distinct buffers with room for the blocks of
the step, the step writes only the cells of
`NLAlib.Krylov.GolubKahan.Band.stepFp` and leaves block `j` of `U` as a stored extension by a
block related by `Mv` to block `j` of `V`, and block `j + 1` of `V` as a stored extension by a
block related by `Rmv` to block `j` of `U`. -/
theorem writes_step_of {dec : K → ℝ} {m n b j : ℕ} {Ext : ExtendPred ℝ}
    {ok : ℕ → ℕ → ℕ → Prop} {Mv : Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin b) ℝ → Prop}
    {Rmv : Matrix (Fin m) (Fin b) ℝ → Matrix (Fin n) (Fin b) ℝ → Prop} {I : Interp Op Tst K}
    (hMv : AppliesColumns dec I (Has.inj OperatorPairOp.matvec) m n b Mv)
    (hRmv : AppliesColumns dec I (Has.inj OperatorPairOp.rmatvec) n m b Rmv)
    (hO : I.Meets .total (Has.inj OrthOp.extend) ((extendRelOf dec ok Ext).spec ExtendOperands))
    (hokU : ok m (j * b) b) (hokV : ok n ((j + 1) * b) b) {τ : Tape K} {μ : Mem K}
    {U V R S W : ℕ × ℕ} {us vs : List K} (hbuf : [U.1, V.1, R.1, S.1, W.1].Nodup)
    (hl : μ.Live [U, V, R, S, W]) (hu : μ.store.readBlock U.1 U.2 (j * b * m) = some us)
    (hv : μ.store.readBlock V.1 V.2 ((j + 1) * b * n) = some vs)
    (hUr : U.2 + j * b * m + b * m ≤ μ.store.len U.1)
    (hVr : V.2 + (j + 1) * b * n + b * n ≤ μ.store.len V.1)
    (hRr : R.2 + coefOffsetR b j + (j * b + b) * b ≤ μ.store.len R.1)
    (hSr : S.2 + coefOffsetS b j + ((j + 1) * b + b) * b ≤ μ.store.len S.1)
    (hWm : W.2 + b * m ≤ μ.store.len W.1) (hWn : W.2 + b * n ≤ μ.store.len W.1) :
    Writes .total I τ step.body (Env.frame [m, n, b, j] [U, V, R, S, W])
      (stepFp m n b j U V R S W)
      (fun μ' => μ'.pos = μ.pos ∧
        ProductExtAt dec Ext Mv μ'.store (j * b) (V.1, V.2 + j * b * n) U
          (R.1, R.2 + coefOffsetR b j) ∧
        ProductExtAt dec Ext Rmv μ'.store ((j + 1) * b) (U.1, U.2 + j * b * m) V
          (S.1, S.2 + coefOffsetS b j)) μ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hbuf
  obtain ⟨hUL, hVL, hRL, hSL, hWL⟩ : U.1 < μ.store.length ∧ V.1 < μ.store.length ∧
      R.1 < μ.store.length ∧ S.1 < μ.store.length ∧ W.1 < μ.store.length := by simpa using hl
  have hUW : U.1 ≠ W.1 := by omega
  have hVW : V.1 ≠ W.1 := by omega
  have hjn : j * b * n + b * n ≤ (j + 1) * b * n := by
    rw [Nat.add_mul, Nat.one_mul, Nat.add_mul]
  have hxs := Store.readBlock_sub hv hjn
  have hl₁ : μ.Live [(V.1, V.2 + j * b * n), W] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    exact ⟨hVL, hWL⟩
  unfold step
  dsimp only
  refine Writes.seq_le ((hMv τ μ (V.1, V.2 + j * b * n) W _ hVW hl₁ hxs hWm).in_frame rfl rfl hl₁)
    (le_sup_of_le_right (Fp.inBlock_le_inBuf _ _ _)) fun μ₁ hfr₁ ⟨hp₁, ys, hys, hrel⟩ => ?_
  have hlen₁ := hfr₁.len_eq
  have hL₁ := hfr₁.length_eq
  refine Writes.seq_le (writes_extend_product hO (X := (V.1, V.2 + j * b * n)) rfl rfl rfl hUW
    (by omega) (by omega) hokU
    (by simp only [Mem.live_cons, Mem.live_nil, and_true, hL₁]; exact ⟨hUL, hWL, hRL⟩)
    (hfr₁.readBlock_of hu fun i _ hF => hUW hF.1) hys (by rw [hlen₁]; exact hUr)
    (by rw [hlen₁]; exact hWm) (by rw [hlen₁]; exact hRr)
    (hfr₁.readBlock_of hxs fun i _ hF => hVW hF.1) hrel
    fun i _ hF => by simp only [fpNF] at hF; omega)
    (by unfold stepFp; fp_sub) fun μ₂ hfr₂ ⟨hp₂, hL⟩ => ?_
  obtain ⟨us', hus'⟩ := hL.extAt.exists_readBlock
  have hlen₂ : ∀ B, μ₂.store.len B = μ.store.len B := fun B => (hfr₂.len_eq B).trans (hlen₁ B)
  have hL₂ := hfr₂.length_eq.trans hL₁
  have hl₃ : μ₂.Live [(U.1, U.2 + j * b * m), W] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true, hL₂]
    exact ⟨hUL, hWL⟩
  refine Writes.seq_le ((hRmv τ μ₂ (U.1, U.2 + j * b * m) W _ hUW hl₃ hus'
    (by rw [hlen₂]; exact hWn)).in_frame
    rfl rfl hl₃) (le_sup_of_le_right (Fp.inBlock_le_inBuf _ _ _))
    fun μ₃ hfr₃ ⟨hp₃, ys', hys', hrel'⟩ => ?_
  have hlen₃ : ∀ B, μ₃.store.len B = μ.store.len B := fun B => (hfr₃.len_eq B).trans (hlen₂ B)
  have hv₃ : μ₃.store.readBlock V.1 V.2 ((j + 1) * b * n) = some vs :=
    hfr₃.readBlock_of (hfr₂.readBlock_of (hfr₁.readBlock_of hv fun i _ hF => hVW hF.1)
      fun i _ hF => by simp only [fpNF] at hF; omega) fun i _ hF => hVW hF.1
  refine (writes_extend_product hO (X := (U.1, U.2 + j * b * m)) rfl rfl rfl hVW (by omega)
    (by omega) hokV
    (by simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₃.length_eq, hL₂]
        exact ⟨hVL, hWL, hSL⟩)
    hv₃ hys' (by rw [hlen₃]; exact hVr) (by rw [hlen₃]; exact hWn) (by rw [hlen₃]; exact hSr)
    (hfr₃.readBlock_of hus' fun i _ hF => hUW hF.1) hrel'
    fun i _ hF => by simp only [fpNF] at hF; omega).mono (by unfold stepFp; fp_sub) ?_
  rintro μ₄ hfr₄ ⟨hp₄, hR⟩
  refine ⟨by rw [hp₄, hp₃, hp₂, hp₁], hL.keep (hfr₃.trans' hfr₄) ?_ ?_ ?_, hR⟩ <;>
    intro i hi hF <;> simp only [fpNF] at hF <;> omega

/-- **The stored blocks after `j` block steps**: the first `j` blocks of `U`, the first `j + 1`
blocks of `V` and the first `j` block columns of the packed coefficients are readable; block
`0` of `V` with the coefficients `G` is a stored extension of the empty basis by
$\mathbf{\Omega}$; for every `i < j`, block `i` of `U` is a stored extension by a block related
by `Mv` to block `i` of `V`, and block `i + 1` of `V` a stored extension by a block related by
`Rmv` to block `i` of `U`. The loop invariant of the driver. -/
structure StoredPrefix (dec : K → ℝ) (Ext : ExtendPred ℝ) {m n b : ℕ}
    (Mv : Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin b) ℝ → Prop)
    (Rmv : Matrix (Fin m) (Fin b) ℝ → Matrix (Fin n) (Fin b) ℝ → Prop)
    (Ω : Matrix (Fin n) (Fin b) ℝ) (U V G R S : ℕ × ℕ) (j : ℕ) (s : Store K) : Prop where
  /-- The first `j` blocks of `U` are readable. -/
  readU : ∃ us, s.readBlock U.1 U.2 (j * b * m) = some us
  /-- The first `j + 1` blocks of `V` are readable. -/
  readV : ∃ vs, s.readBlock V.1 V.2 ((j + 1) * b * n) = some vs
  /-- The first `j` block columns of the left coefficients are readable. -/
  readR : ∃ rs, s.readBlock R.1 R.2 (coefOffsetR b j) = some rs
  /-- The first `j` block columns of the right coefficients are readable. -/
  readS : ∃ ss, s.readBlock S.1 S.2 (coefOffsetS b j) = some ss
  /-- Block `0` of `V` extends the empty basis by the start block. -/
  start : ExtAt dec Ext s n 0 b V G (· = Ω)
  /-- Block `i` of `U` extends the first `i` blocks by products of block `i` of `V`. -/
  left : ∀ i < j, ProductExtAt dec Ext Mv s (i * b) (V.1, V.2 + i * b * n) U
    (R.1, R.2 + coefOffsetR b i)
  /-- Block `i + 1` of `V` extends the first `i + 1` blocks by products of block `i` of `U`. -/
  right : ∀ i < j, ProductExtAt dec Ext Rmv s ((i + 1) * b) (U.1, U.2 + i * b * m) V
    (S.1, S.2 + coefOffsetS b i)

/-- The stored start block is the stored prefix of no block step. -/
theorem StoredPrefix.zero {dec : K → ℝ} {Ext : ExtendPred ℝ} {m n b : ℕ}
    {Mv : Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin b) ℝ → Prop}
    {Rmv : Matrix (Fin m) (Fin b) ℝ → Matrix (Fin n) (Fin b) ℝ → Prop}
    {Ω : Matrix (Fin n) (Fin b) ℝ} {U V G R S : ℕ × ℕ} {s : Store K}
    (h : ExtAt dec Ext s n 0 b V G (· = Ω)) :
    StoredPrefix dec Ext Mv Rmv Ω U V G R S 0 s := by
  obtain ⟨vs, hvs⟩ := h.exists_readBlock
  exact ⟨⟨[], by simp⟩, ⟨vs, by simpa using hvs⟩, ⟨[], by simp [coefOffsetR]⟩,
    ⟨[], by simp [coefOffsetS]⟩, h, fun i hi => absurd hi (Nat.not_lt_zero i),
    fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- The round of the loop invariant: a run that writes only the cells of block step `j`
and leaves the two stored extensions of that step turns the stored prefix of `j` steps into
the stored prefix of `j + 1` steps. The scratch buffer is above the five output buffers, which
are distinct. -/
theorem StoredPrefix.succ {dec : K → ℝ} {Ext : ExtendPred ℝ} {m n b j : ℕ}
    {Mv : Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin b) ℝ → Prop}
    {Rmv : Matrix (Fin m) (Fin b) ℝ → Matrix (Fin n) (Fin b) ℝ → Prop}
    {Ω : Matrix (Fin n) (Fin b) ℝ} {U V G R S W : ℕ × ℕ} {s s' : Store K}
    (h : StoredPrefix dec Ext Mv Rmv Ω U V G R S j s) (hbuf : [U.1, V.1, G.1, R.1, S.1].Nodup)
    (hlt : ∀ z ∈ [U, V, G, R, S], z.1 < W.1) (hfr : s.EqOff (stepFp m n b j U V R S W) s')
    (hL : ProductExtAt dec Ext Mv s' (j * b) (V.1, V.2 + j * b * n) U
      (R.1, R.2 + coefOffsetR b j))
    (hR : ProductExtAt dec Ext Rmv s' ((j + 1) * b) (U.1, U.2 + j * b * m) V
      (S.1, S.2 + coefOffsetS b j)) :
    StoredPrefix dec Ext Mv Rmv Ω U V G R S (j + 1) s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hbuf
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
  have hR1 := coefOffsetR_succ b j
  have hS1 := coefOffsetS_succ b j
  have hjn : (j + 1) * b * n = j * b * n + b * n := by ring
  have hjm : (j + 1) * b * m = j * b * m + b * m := by ring
  have hj2 : (j + 1 + 1) * b * n = (j + 1) * b * n + b * n := by ring
  obtain ⟨us', hus'⟩ := hL.extAt.exists_readBlock_basis
  obtain ⟨vs', hvs'⟩ := hR.extAt.exists_readBlock_basis
  obtain ⟨rc, hrc⟩ := hL.extAt.exists_readBlock_coef
  obtain ⟨sc, hsc⟩ := hR.extAt.exists_readBlock_coef
  obtain ⟨rs, hrs⟩ := h.readR
  obtain ⟨ss, hss⟩ := h.readS
  have hrs' := hfr.readBlock_of hrs fun t ht hF => by simp only [stepFp, fpNF] at hF; omega
  have hss' := hfr.readBlock_of hss fun t ht hF => by simp only [stepFp, fpNF] at hF; omega
  refine ⟨⟨us', by rw [hjm]; exact hus'⟩, ⟨vs', by rw [hj2]; exact hvs'⟩,
    ⟨rs ++ rc, by rw [hR1]; exact Store.readBlock_add hrs' hrc⟩,
    ⟨ss ++ sc, by rw [hS1]; exact Store.readBlock_add hss' hsc⟩,
    h.start.keep hfr (fun t ht hF => by simp only [stepFp, fpNF] at hF; omega)
      (fun t ht hF => by simp only [stepFp, fpNF] at hF; omega), fun i hi => ?_, fun i hi => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have h1 := block_le hi b n
      have h2 := block_le hi b m
      have h3 := coefOffsetR_mono b (show i + 1 ≤ j from hi)
      have h4 := coefOffsetR_succ b i
      refine (h.left i hi).keep hfr ?_ ?_ ?_ <;>
        intro t ht hF <;> simp only [stepFp, fpNF] at hF <;> omega
    · exact hL
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have h1 := block_le (Nat.add_lt_add_right hi 1) b n
      have h2 := block_le hi b m
      have h3 := coefOffsetS_mono b (show i + 1 ≤ j from hi)
      have h4 := coefOffsetS_succ b i
      refine (h.right i hi).keep hfr ?_ ?_ ?_ <;>
        intro t ht hF <;> simp only [stepFp, fpNF] at hF <;> omega
    · exact hR

/-- Readback of the stored prefix of all `q` steps: the five output blocks are readable
and their decoded matrices are related block by block, with the decoded window `ω` as start
block. -/
theorem StoredPrefix.exists_storedOut {dec : K → ℝ} {Ext : ExtendPred ℝ} {m n b q : ℕ}
    {Mv : Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin b) ℝ → Prop}
    {Rmv : Matrix (Fin m) (Fin b) ℝ → Matrix (Fin n) (Fin b) ℝ → Prop}
    {U V G R S : ℕ × ℕ} {μ : Mem K} {ω : List K}
    (h : StoredPrefix dec Ext Mv Rmv (decodeMatrix dec n b ω) U V G R S q μ.store) :
    ∃ us vs gs rs ss,
      μ.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
      StoredOut dec m n b q (IsStoredRun Ext Mv Rmv) ω us vs gs rs ss := by
  obtain ⟨us, hus⟩ := h.readU
  obtain ⟨vs, hvs⟩ := h.readV
  obtain ⟨rs, hrs⟩ := h.readR
  obtain ⟨ss, hss⟩ := h.readS
  obtain ⟨gs, hgs⟩ := h.start.exists_readBlock_coef
  rw [Nat.zero_add] at hgs
  refine ⟨us, vs, gs, rs, ss, Mem.readBlocks_of_cons hus (Mem.readBlocks_of_cons hvs
    (Mem.readBlocks_of_cons hgs (Mem.readBlocks_of_cons hrs (Mem.readBlocks_of_cons hss rfl)))),
    ?_⟩
  unfold StoredOut
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨W, rfl, hE⟩ := h.start.exists_start (N := (q + 1) * b)
      (Nat.le_mul_of_pos_left b (Nat.succ_pos q)) hvs hgs
    exact extendPred_of_eq_zero Ext (Nat.zero_mul b) _ _ hE
  · have h1 := Idx.mul_add_le_mul hi b
    exact (h.left i hi).exists_blocks (X := V) (C := R) rfl h1 hus hrs
      (by rw [← coefOffsetR_succ]; exact coefOffsetR_mono b hi) hvs rfl
      (by rw [Nat.add_mul, Nat.one_mul]; omega)
  · exact (h.right i hi).exists_blocks (i := i + 1) (X := U) (C := S) rfl
      (Idx.mul_add_le_mul (Nat.add_lt_add_right hi 1) b) hvs hss
      (by rw [← coefOffsetS_succ]; exact coefOffsetS_mono b hi) hus rfl
      (Idx.mul_add_le_mul hi b)

omit [Has SampleOp Op] in
/-- The loop of block steps, for any contracts. From the stored start block, on five
distinct output buffers with room for the output lengths and a scratch buffer above them with
room for a block of either side, the `q` framed block steps write only cells of a footprint
that contains the cells of every step, do not move the tape, and leave the stored prefix of
`q` steps. The loop is given by its evaluated bound, dimensions and operands. -/
theorem writes_steps {dec : K → ℝ} {m n b q : ℕ} {Ext : ExtendPred ℝ}
    {ok : ℕ → ℕ → ℕ → Prop} {Mv : Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin b) ℝ → Prop}
    {Rmv : Matrix (Fin m) (Fin b) ℝ → Matrix (Fin n) (Fin b) ℝ → Prop} {I : Interp Op Tst K}
    (hMv : AppliesColumns dec I (Has.inj OperatorPairOp.matvec) m n b Mv)
    (hRmv : AppliesColumns dec I (Has.inj OperatorPairOp.rmatvec) n m b Rmv)
    (hO : I.Meets .total (Has.inj OrthOp.extend) ((extendRelOf dec ok Ext).spec ExtendOperands))
    (hokU : ∀ j < q, ok m (j * b) b) (hokV : ∀ j < q, ok n ((j + 1) * b) b) {τ : Tape K}
    {ρ : Env} {N : IExp} {ds : List IExp} {args : List Operand} {μ : Mem K}
    {U V G R S W : ℕ × ℕ} {Ω : Matrix (Fin n) (Fin b) ℝ} {F : Fp}
    (hN : N.eval ρ.idx = some q)
    (hd : ∀ j, IExp.evalList (ρ.pushIdx j).idx ds = some [m, n, b, j])
    (ha : ∀ j, Operand.evalList (ρ.pushIdx j) args = some [U, V, R, S, W])
    (hbuf : [U.1, V.1, G.1, R.1, S.1].Nodup) (hlt : ∀ z ∈ [U, V, G, R, S], z.1 < W.1)
    (hl : μ.Live [U, V, R, S, W]) (hz : μ.Room [U, V, G, R, S] (outLens m n b q))
    (hWm : W.2 + b * m ≤ μ.store.len W.1) (hWn : W.2 + b * n ≤ μ.store.len W.1)
    (h0 : StoredPrefix dec Ext Mv Rmv Ω U V G R S 0 μ.store)
    (hF : ∀ j < q, stepFp m n b j U V R S W ≤ F) :
    Writes .total I τ (.loop N (.frame ds args step.body)) ρ F
      (fun μ' => μ'.pos = μ.pos ∧ StoredPrefix dec Ext Mv Rmv Ω U V G R S q μ'.store) μ := by
  have hbuf' : [U.1, V.1, R.1, S.1, W.1].Nodup := by
    have hb := hbuf
    have hw := hlt
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true] at hb ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hw
    omega
  simp only [outLens, Mem.room_cons, Mem.room_nil, and_true] at hz
  refine writes_loop hN (fun _ => F) (fun _ _ => le_rfl)
    (fun j μ' => μ'.pos = μ.pos ∧ StoredPrefix dec Ext Mv Rmv Ω U V G R S j μ'.store)
    ⟨rfl, h0⟩ fun j hj μ' hfr ⟨hp, hpre⟩ => ?_
  obtain ⟨us, hus⟩ := hpre.readU
  obtain ⟨vs, hvs⟩ := hpre.readV
  have h1 := block_le hj b m
  have h2 := block_le (Nat.add_lt_add_right hj 1) b n
  have h3 := coefOffsetR_mono b (show j + 1 ≤ q from hj)
  have h4 := coefOffsetR_succ b j
  have h5 := coefOffsetS_mono b (show j + 1 ≤ q from hj)
  have h6 := coefOffsetS_succ b j
  have hlen := hfr.len_eq
  have hl' := hl.congr hfr.length_eq
  refine ((writes_step_of hMv hRmv hO (hokU j hj) (hokV j hj) hbuf' hl' hus hvs
    (by rw [hlen]; omega) (by rw [hlen]; omega) (by rw [hlen]; omega) (by rw [hlen]; omega)
    (by rw [hlen]; exact hWm) (by rw [hlen]; exact hWn)).in_frame (hd j) (ha j) hl').mono
    (hF j hj) fun μ'' hfr' ⟨hp', hL, hR⟩ => ⟨hp'.trans hp, hpre.succ hbuf hlt hfr' hL hR⟩

/-- Total execution of the driver, for any contracts. If the loops over the columns of a
block with `matvec` and `rmatvec` compute blocks related by `Mv` and `Rmv` to their inputs,
`extend` meets the contract of a basis extension for the predicate `Ext` at the dimensions of
the run, and the draws return the words of the tape, then on five live output blocks in
distinct buffers with room for the output lengths the program terminates, writes only the
output blocks, consumes exactly $nb$ samples and releases its scratch; the stored blocks decode
to matrices related block by block (`NLAlib.Krylov.GolubKahan.Band.IsStoredRun`), from the
start block decoded from the window of the tape. The exact and the rounded theorem are
instances. -/
theorem solve_writes_of {dec : K → ℝ} {m n b q : ℕ} {Ext : ExtendPred ℝ}
    {ok : ℕ → ℕ → ℕ → Prop} {Mv : Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin b) ℝ → Prop}
    {Rmv : Matrix (Fin m) (Fin b) ℝ → Matrix (Fin n) (Fin b) ℝ → Prop} {I : Interp Op Tst K}
    (hMv : AppliesColumns dec I (Has.inj OperatorPairOp.matvec) m n b Mv)
    (hRmv : AppliesColumns dec I (Has.inj OperatorPairOp.rmatvec) n m b Rmv)
    (hO : I.Meets .total (Has.inj OrthOp.extend) ((extendRelOf dec ok Ext).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) (hok₀ : ok n 0 b) (hokU : ∀ j < q, ok m (j * b) b)
    (hokV : ∀ j < q, ok n ((j + 1) * b) b) {τ : Tape K} {μ : Mem K} {U V G R S : ℕ × ℕ}
    (hbuf : [U.1, V.1, G.1, R.1, S.1].Nodup) (hl : μ.Live [U, V, G, R, S])
    (hz : μ.Room [U, V, G, R, S] (outLens m n b q)) :
    Writes .total I τ (solve stream).body (Env.frame [m, n, b, q] [U, V, G, R, S])
      (Fp.blocks [U, V, G, R, S] (outLens m n b q))
      (fun μ' => μ'.pos = μ.pos + n * b ∧ ∃ us vs gs rs ss,
        μ'.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
        StoredOut dec m n b q (IsStoredRun Ext Mv Rmv) (τ.window stream μ.pos (n * b))
          us vs gs rs ss) μ := by
  obtain ⟨hUL, hVL, hGL, hRL, hSL⟩ : U.1 < μ.store.length ∧ V.1 < μ.store.length ∧
      G.1 < μ.store.length ∧ R.1 < μ.store.length ∧ S.1 < μ.store.length := by simpa using hl
  refine writes_allocs_preserving_post (lens := [(.var 0 + (.var 1 - .var 0)) * .var 2])
    (ns := [(m + (n - m)) * b]) rfl (fun hBelow hp => ⟨hp.1, ?_⟩)
    fun s₁ hlength hlens hBelow => ?_
  · obtain ⟨us, vs, gs, rs, ss, hr, hout⟩ := hp.2
    exact ⟨us, vs, gs, rs, ss, (Mem.readBlocks_eq_of_below hBelow hl).trans hr, hout⟩
  have hlen : s₁.length = μ.store.length + 1 := by simpa using hlength
  have hW : s₁.len μ.store.length = (m + (n - m)) * b := by simpa using hlens 0 (by simp)
  have hz₀ : (Mem.mk s₁ μ.pos).Room [U, V, G, R, S] (outLens m n b q) :=
    (Mem.room_eq_of_below (μ := μ) (μ' := ⟨s₁, μ.pos⟩) hBelow hl).mpr hz
  have hWm : b * m ≤ (m + (n - m)) * b := by
    rw [Nat.mul_comm b m]
    exact Nat.mul_le_mul_right b (by omega)
  have hWn : b * n ≤ (m + (n - m)) * b := by
    rw [Nat.mul_comm b n]
    exact Nat.mul_le_mul_right b (by omega)
  have hnb : n * b = b * n := Nat.mul_comm n b
  have hne := hbuf
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hne
  have hLive : (Mem.mk s₁ μ.pos).Live [(μ.store.length, 0)] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    omega
  refine Writes.seq_le ((writes_sampleVector hSample stream (y := (μ.store.length, 0))
    (n := n * b) (show 0 + n * b ≤ s₁.len μ.store.length by omega)).in_frame rfl rfl hLive)
    (Fp.inBlock_le_sup_above le_rfl) fun μ₁ hfr₁ ⟨hω, hp₁⟩ => ?_
  have hz₁ := hz₀.congr hfr₁.len_eq
  have hW₁ := (hfr₁.len_eq μ.store.length).trans hW
  have hL₁ := hfr₁.length_eq.trans hlen
  have hb1 := block_le (show 0 < q + 1 by omega) b n
  have hzz := hz₁
  simp only [outLens, Mem.room_cons, Mem.room_nil, and_true] at hzz
  refine Writes.seq_le (writes_extend hO (Q := V) (W := (μ.store.length, 0)) (C := G)
    (qs := []) (ws := τ.window stream μ.pos (n * b)) rfl rfl (by rw [Nat.zero_mul]; rfl)
    hVL.ne (by omega) hGL.ne' hok₀
    (by simp only [Mem.live_cons, Mem.live_nil, and_true, hL₁]; omega)
    (by rw [Nat.zero_mul]; rfl) (by rw [← hnb]; exact hω) (by omega)
    (show 0 + b * n ≤ μ₁.store.len μ.store.length by omega)
    (by rw [Nat.zero_add]; exact hzz.2.2.1)) ?_ fun μ₂ hfr₂ ⟨hp₂, hstart⟩ => ?_
  · unfold outLens
    refine sup_le ?_ (sup_le (Fp.inBlock_le_sup_above le_rfl) (sup_le ?_ bot_le))
    · exact le_sup_of_le_left (le_sup_of_le_right (le_sup_of_le_left
        (Fp.inBlock_le_inBlock (by omega) (by omega))))
    · exact le_sup_of_le_left (le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_left
        (Fp.inBlock_le_inBlock le_rfl (by rw [Nat.zero_add])))))
  have hlen₂ : ∀ B, μ₂.store.len B = μ₁.store.len B := hfr₂.len_eq
  refine (writes_steps hMv hRmv hO hokU hokV (W := (μ.store.length, 0)) rfl (fun _ => rfl)
    (fun _ => rfl) hbuf hl
    (by simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₂.length_eq, hL₁]; omega)
    (hz₁.congr hlen₂) (by rw [hlen₂]; change 0 + b * m ≤ μ₁.store.len μ.store.length; omega)
    (by rw [hlen₂]; change 0 + b * n ≤ μ₁.store.len μ.store.length; omega)
    (StoredPrefix.zero hstart)
    fun j hj => stepFp_le hj le_rfl).mono le_rfl ?_
  rintro μ₃ - ⟨hp₃, hpre⟩
  exact ⟨by rw [hp₃, hp₂, hp₁], hpre.exists_storedOut⟩

/-- The driver meets the contract of a run predicate from its block specification. -/
theorem solve_spec_of {dec : K → ℝ} {m n : ℕ} {Run : (b q : ℕ) → RunPred m n b q}
    {I : Interp Op Tst K} (stream : ℕ)
    (h : ∀ (b q : ℕ) (τ : Tape K) (μ : Mem K) (U V G R S : ℕ × ℕ),
      [U.1, V.1, G.1, R.1, S.1].Nodup → μ.Live [U, V, G, R, S] →
      μ.Room [U, V, G, R, S] (outLens m n b q) →
      Writes .total I τ (solve stream).body (Env.frame [m, n, b, q] [U, V, G, R, S])
        (Fp.blocks [U, V, G, R, S] (outLens m n b q))
        (fun μ' => μ'.pos = μ.pos + n * b ∧ ∃ us vs gs rs ss,
          μ'.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
          StoredOut dec m n b q (Run b q) (τ.window stream μ.pos (n * b)) us vs gs rs ss) μ) :
    (solve (Op := Op) (Tst := Tst) stream).Triple I .total
      ((solveRelOf stream dec m n Run).spec (SolveOperands m n)) := by
  refine Impl.meets_of_writes fun d ins outs τ μ X hnd hadm hl hr hdom hz => ?_
  obtain ⟨m', n', b, q, rfl⟩ := List.length_eq_four.mp hnd
  obtain ⟨hm, hn, rfl, U, V, G, R, S, rfl, hbuf⟩ := hadm
  obtain rfl : m' = m := hm
  obtain rfl : n' = n := hn
  refine ⟨⟨rfl, rfl, rfl⟩, (h b q τ μ U V G R S hbuf (by simpa using hl) hz).mono le_rfl ?_⟩
  rintro μ' - ⟨hpos, us, vs, gs, rs, ss, hread, hout⟩
  exact ⟨hpos, [us, vs, gs, rs, ss], hread, hout⟩

/-! ### Exact execution -/

/-- Total execution under the exact contracts. If `matvec` and `rmatvec` are the exact
products with $\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$, `extend` meets the exact contract of a
basis extension and the draws return the words of the tape, then for all dimensions
$(m, n, b, q)$, on five live output blocks in distinct buffers with room for the output lengths,
the program terminates, writes only the output blocks, consumes exactly $nb$ samples and
releases its scratch; the stored blocks decode to matrices that are an exact run for
$\mathbf{A}$ from the start block $\mathbf{\Omega}$ decoded from the window of the tape: every
stored block is an exact extension of the stored columns before it by the products of the
previous block. No rank or nonbreakdown hypothesis is needed. -/
theorem solve_writes {dec : K → ℝ} {m n b q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Interp Op Tst K} (hA : IsExactMatvecPair dec A I)
    (hO : I.Meets .total (Has.inj OrthOp.extend) ((exactExtendRel dec).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) {τ : Tape K} {μ : Mem K} {U V G R S : ℕ × ℕ}
    (hbuf : [U.1, V.1, G.1, R.1, S.1].Nodup) (hl : μ.Live [U, V, G, R, S])
    (hz : μ.Room [U, V, G, R, S] (outLens m n b q)) :
    Writes .total I τ (solve stream).body (Env.frame [m, n, b, q] [U, V, G, R, S])
      (Fp.blocks [U, V, G, R, S] (outLens m n b q))
      (fun μ' => μ'.pos = μ.pos + n * b ∧ ∃ us vs gs rs ss,
        μ'.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
        StoredOut dec m n b q (IsExactStoredRun A b q) (τ.window stream μ.pos (n * b))
          us vs gs rs ss) μ :=
  solve_writes_of (Ext := fun _ _ _ Q W Q' H R => IsBasisExtension Q W Q' H R)
    (ok := fun _ _ _ => True)
    (fun _ _ _ _ _ hxy hl hx hy => writes_applyColumns hA.matvec hxy hl hx hy)
    (fun _ _ _ _ _ hxy hl hx hy => writes_applyColumns hA.rmatvec hxy hl hx hy)
    hO hSample stream trivial (fun _ _ => trivial) (fun _ _ => trivial) hbuf hl hz

/-- The program meets its exact contract in total mode: under the exact contracts of the
two products with $\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$, of the basis extension and of the
draws, on five output blocks in distinct buffers the program writes blocks that decode to an
exact run for $\mathbf{A}$ from the drawn start block, and advances the tape by the $nb$ words
of that block. -/
theorem solve_spec {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Interp Op Tst K} (hA : IsExactMatvecPair dec A I)
    (hO : I.Meets .total (Has.inj OrthOp.extend) ((exactExtendRel dec).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) :
    (solve (Op := Op) (Tst := Tst) stream).Triple I .total
      ((solveRel stream dec A).spec (SolveOperands m n)) :=
  solve_spec_of stream fun _ _ _ _ _ _ _ _ _ hbuf hl hz =>
    solve_writes hA hO hSample stream hbuf hl hz

/-! ### Rounded execution -/

namespace Rounded

/-- The rounded contract of the program: the stored blocks are a rounded run for $\mathbf{A}$
with product allowances $\delta$, $\delta'$ and extension parameters
$(\eta_0, \mu, \varepsilon)$, from the drawn start block. -/
def solveRel (stream : ℕ) (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (δ δ' η₀ μ ε : ℝ) : BlockRel K :=
  solveRelOf stream dec m n (IsRoundedStoredRun A δ δ' η₀ μ ε)

/-- Total execution under the rounded contracts, with the executed history. If `matvec` and
`rmatvec` meet the normwise contracts of the products with $\mathbf{A}$ and
$\mathbf{A}^{\mathsf{H}}$ at the allowances $\delta$, $\delta'$, `extend` meets the rounded
contract of a basis extension with parameters $(\eta_0, \mu, \varepsilon)$ at the dimensions of
the run, and the draws return the words of the tape, then on five live output blocks in distinct
buffers with room for the output lengths the program terminates, writes only the output blocks,
consumes exactly $nb$ samples and releases its scratch; the stored blocks decode to a rounded
run: every stored block is a rounded extension of the stored columns before it by a computed
product block within the product allowance. There is no orthogonality, rank or nonbreakdown
hypothesis. -/
theorem solve_writes {dec : K → ℝ} {m n b q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {δ δ' η₀ μ ε : ℝ} {ok : ℕ → ℕ → ℕ → Prop} {I : Interp Op Tst K}
    (hA : IsMatvecPair dec A δ δ' I)
    (hO : I.Meets .total (Has.inj OrthOp.extend)
      ((extendRel dec η₀ μ ε ok).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) (hok₀ : ok n 0 b)
    (hokU : ∀ j < q, ok m (j * b) b) (hokV : ∀ j < q, ok n ((j + 1) * b) b)
    {τ : Tape K} {ν : Mem K} {U V G R S : ℕ × ℕ}
    (hbuf : [U.1, V.1, G.1, R.1, S.1].Nodup) (hl : ν.Live [U, V, G, R, S])
    (hz : ν.Room [U, V, G, R, S] (outLens m n b q)) :
    Writes .total I τ (solve stream).body (Env.frame [m, n, b, q] [U, V, G, R, S])
      (Fp.blocks [U, V, G, R, S] (outLens m n b q))
      (fun ν' => ν'.pos = ν.pos + n * b ∧ ∃ us vs gs rs ss,
        ν'.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
        StoredOut dec m n b q (IsRoundedStoredRun A δ δ' η₀ μ ε b q)
          (τ.window stream ν.pos (n * b)) us vs gs rs ss) ν :=
  solve_writes_of (Ext := fun _ _ _ Q W Q' H R => IsBasisExtensionErr η₀ μ ε Q W Q' H R)
    (fun _ _ _ _ _ hxy hl hx hy => writes_applyColumns_error hA.matvec hxy hl hx hy)
    (fun _ _ _ _ _ hxy hl hx hy => writes_applyColumns_error hA.rmatvec hxy hl hx hy)
    hO hSample stream hok₀ hokU hokV hbuf hl hz

/-- The program meets its rounded contract in total mode, at the dimensions `[m, n, b, q]`
at which the basis extension is admitted for every block of the run. -/
theorem solve_spec {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {δ δ' η₀ μ ε : ℝ} {ok : ℕ → ℕ → ℕ → Prop} {I : Interp Op Tst K}
    (hA : IsMatvecPair dec A δ δ' I)
    (hO : I.Meets .total (Has.inj OrthOp.extend)
      ((extendRel dec η₀ μ ε ok).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) (hok : ∀ k b, ok m k b ∧ ok n k b) :
    (solve (Op := Op) (Tst := Tst) stream).Triple I .total
      ((solveRel stream dec A δ δ' η₀ μ ε).spec (SolveOperands m n)) :=
  solve_spec_of stream fun _ _ _ _ _ _ _ _ _ hbuf hl hz =>
    solve_writes hA hO hSample stream (hok _ _).2 (fun _ _ => (hok _ _).1)
      (fun _ _ => (hok _ _).2) hbuf hl hz

end Rounded

end NLAlib.Krylov.GolubKahan.Band
