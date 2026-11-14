/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.BlockRel
public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Ops.Logic.EntryLayout

/-!
# Catalog: extension of a stored basis by a block

`NLAlib.Ops.OrthOp.extend [n, k, b] [Q, W] [Q', W, C]` orthogonalizes a block against a stored
basis. All blocks are column-major, one word per entry.

* `Q` is the stored basis: `k` columns of length `n`, read only.
* `W` is the block: `b` columns of length `n`. It is an input and an output: the operation may
  use it as workspace, and its contract says nothing of the words left there.
* `Q'` is the new block of `b` columns. Its operand is the end of `Q`: the same buffer, at the
  offset of `Q` plus `k * n`. So the basis and the new block are one contiguous stored block of
  `k + b` columns, which is the basis of the next call.
* `C` is the coefficient block of `k + b` rows and `b` columns: its first `k` rows are the
  coefficients $\mathbf{H}$ of the block against the old columns and its last `b` rows the
  coefficients $\mathbf{R}$ against the new ones.

The three buffers of `Q`, `W` and `C` are distinct. The admission `NLAlib.Ops.ExtendOperands` is
a predicate on the evaluated handles and offsets, so the adjacency of `Q'` and `Q` is an equation
between two operands. A block of length zero (`k = 0`, the first block of a basis) is read and
written as the empty list at any offset of a live buffer.

The mathematical contract is a parameter of `NLAlib.Ops.extendRelOf`: a predicate on the decoded
matrices $\mathbf{Q}$, $\mathbf{W}$, $\mathbf{Q}'$, $\mathbf{H}$, $\mathbf{R}$. This file is in
the operation core, which does not import the matrix layer; the exact and the rounded contract
of a basis extension are instances stated where the matrix predicates are available.

## Main definitions

* `NLAlib.Ops.OrthOp`: the operation.
* `NLAlib.Ops.ExtendOperands`: the admitted operands.
* `NLAlib.Ops.decodeMatrix`, `NLAlib.Ops.coefTop`, `NLAlib.Ops.coefBot`: a stored block as a
  matrix, and the two parts of the coefficient block.
* `NLAlib.Ops.ExtendPred`, `NLAlib.Ops.ExtendOut`, `NLAlib.Ops.extendRelOf`: the contract of
  the operation for a given predicate on the decoded matrices.

## Main results

* `NLAlib.Ops.decv_drop_take`: a column of a stored block, decoded, is the column of the decoded
  block.
* `NLAlib.Ops.extendRelOf_rel_mono`, `NLAlib.Ops.Interp.Meets.extendRelOf_mono`: a contract with
  a weaker predicate and fewer admitted dimensions is met.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Operations that orthogonalize a block against a stored basis. -/
inductive OrthOp where
  /-- `extend [n, k, b] [Q, W] [Q', W, C]` extends the stored basis `Q` (`k` columns of length
  `n`) by the block `W` (`b` columns): the new block `Q'` is written directly after `Q` in the
  same buffer, `W` is overwritten, and `C` receives the `(k + b) × b` coefficients. -/
  | extend
  deriving DecidableEq

variable {K 𝕜 Op Tst : Type}

/-- The admitted operands of a basis extension at the dimensions `[n, k, b]`: the inputs are the
basis `Q` and the block `W`; the outputs are the new block at the end of the basis (the buffer of
`Q` at the offset of `Q` plus `k * n`), the block `W` again, and the coefficients `C`; the
buffers of `Q`, `W` and `C` are distinct. -/
@[admNF] def ExtendOperands : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => ∃ Q W C, ins = [Q, W] ∧
    outs = [(Q.1, Q.2 + d.getD 1 0 * d.headD 0), W, C] ∧ Q.1 ≠ W.1 ∧ Q.1 ≠ C.1 ∧ W.1 ≠ C.1

/-- The upper part of a coefficient block of $k + b$ rows: its first $k$ rows, the coefficients
$\mathbf{H}$ against the old columns. -/
def coefTop {k b : ℕ} (C : Matrix (Fin (k + b)) (Fin b) 𝕜) : Matrix (Fin k) (Fin b) 𝕜 :=
  C.submatrix (Fin.castAdd b) id

/-- The lower part of a coefficient block of $k + b$ rows: its last $b$ rows, the coefficients
$\mathbf{R}$ against the new columns. -/
def coefBot {k b : ℕ} (C : Matrix (Fin (k + b)) (Fin b) 𝕜) : Matrix (Fin b) (Fin b) 𝕜 :=
  C.submatrix (Fin.natAdd k) id

variable [Inhabited K]

/-- A column-major block of words, one word per entry, decoded as a matrix of `n` rows and `k`
columns: the entry $(i, j)$ is the decoded word at the position `j * n + i`. Words missing from
a short block are the default word. -/
def decodeMatrix (dec : K → 𝕜) (n k : ℕ) (xs : List K) : Matrix (Fin n) (Fin k) 𝕜 :=
  ((EntryCodec.scalar K).matrix n k xs).map dec

/-- The entry $(i, j)$ of a decoded block is the decoded word at the position `j * n + i`. -/
theorem decodeMatrix_apply (dec : K → 𝕜) (n k : ℕ) (xs : List K) (i : Fin n) (j : Fin k) :
    decodeMatrix dec n k xs i j = dec (vec xs (j * n + i)) := by
  simp [decodeMatrix, EntryCodec.matrix]

/-- Column $c$ of a decoded block of $b$ columns of length $n$ is the decoded vector of its
words $cn, \dots, cn + n - 1$. -/
theorem decv_drop_take {dec : K → ℝ} {n b : ℕ} (ws : List K) (c : Fin b) :
    decv dec n ((ws.drop (c * n)).take n) = (decodeMatrix dec n b ws).col c := by
  funext i
  rw [Matrix.col_apply, decodeMatrix_apply]
  exact congrArg dec (vec_drop_take i.isLt)

/-- A predicate on the matrices of a basis extension with `n` rows, `k` old columns and `b` new
columns: the basis $\mathbf{Q}$, the block $\mathbf{W}$, the new block $\mathbf{Q}'$ and the
coefficients $\mathbf{H}$ and $\mathbf{R}$. -/
abbrev ExtendPred (𝕜 : Type) : Type :=
  (n k b : ℕ) → Matrix (Fin n) (Fin k) 𝕜 → Matrix (Fin n) (Fin b) 𝕜 → Matrix (Fin n) (Fin b) 𝕜 →
    Matrix (Fin k) (Fin b) 𝕜 → Matrix (Fin b) (Fin b) 𝕜 → Prop

/-- The predicate `P` holds of the decoded blocks of a basis extension: the basis words `qs`,
the block words `ws` read by the call, the words `qs'` of the new block and the coefficient words
`cs`, whose first `k` rows decode to $\mathbf{H}$ and last `b` rows to $\mathbf{R}$. -/
def ExtendOut (dec : K → 𝕜) (P : ExtendPred 𝕜) (n k b : ℕ) (qs ws qs' cs : List K) : Prop :=
  P n k b (decodeMatrix dec n k qs) (decodeMatrix dec n b ws) (decodeMatrix dec n b qs')
    (coefTop (decodeMatrix dec (k + b) b cs)) (coefBot (decodeMatrix dec (k + b) b cs))

/-- **The contract of a basis extension** for the predicate `P` on the decoded matrices, at the
dimensions `[n, k, b]`: the call reads the basis (`k * n` words) and the block (`b * n` words),
and writes the new block (`b * n` words), `b * n` unspecified words over the block, and the
coefficients (`(k + b) * b` words), with `P` of the decoded basis, input block, new block and
coefficients. It succeeds at the dimensions admitted by `ok`. -/
@[simps (attr := storeNF)]
def extendRelOf (dec : K → 𝕜) (ok : ℕ → ℕ → ℕ → Prop) (P : ExtendPred 𝕜) : BlockRel K where
  nd := 3
  inLens d := [d.getD 1 0 * d.headD 0, d.getD 2 0 * d.headD 0]
  outLens d := [d.getD 2 0 * d.headD 0, d.getD 2 0 * d.headD 0,
    (d.getD 1 0 + d.getD 2 0) * d.getD 2 0]
  dom d _ _ := ok (d.headD 0) (d.getD 1 0) (d.getD 2 0)
  rel d X _ Y := match X, Y with
    | [qs, ws], [qs', _, cs] =>
        ExtendOut dec P (d.headD 0) (d.getD 1 0) (d.getD 2 0) qs ws qs' cs
    | _, _ => False

/-- The relation of a basis extension is monotone in the predicate on the decoded matrices. -/
theorem extendRelOf_rel_mono {dec : K → 𝕜} {ok ok' : ℕ → ℕ → ℕ → Prop}
    {P P' : ExtendPred 𝕜} (hP : ∀ n k b Q W Q' H R, P n k b Q W Q' H R → P' n k b Q W Q' H R)
    {d : List ℕ} {X : List (List K)} {w : List K} {Y : List (List K)}
    (h : (extendRelOf dec ok P).rel d X w Y) : (extendRelOf dec ok' P').rel d X w Y := by
  simp only [extendRelOf] at h ⊢
  split at h
  · exact hP _ _ _ _ _ _ _ _ h
  · exact h.elim

/-- An operation that meets the contract of a basis extension for the predicate `P` at the
dimensions `ok` meets it for every weaker predicate and every smaller set of dimensions. -/
theorem Interp.Meets.extendRelOf_mono {dec : K → 𝕜} {ok ok' : ℕ → ℕ → ℕ → Prop}
    {P P' : ExtendPred 𝕜} {I : Interp Op Tst K} {o : Op}
    (h : I.Meets .total o ((extendRelOf dec ok P).spec ExtendOperands))
    (hok : ∀ n k b, ok' n k b → ok n k b)
    (hP : ∀ n k b Q W Q' H R, P n k b Q W Q' H R → P' n k b Q W Q' H R) :
    I.Meets .total o ((extendRelOf dec ok' P').spec ExtendOperands) := by
  refine h.mono ?_ ?_
  · rintro d ins outs τ m ⟨hnd, hadm, hn⟩
    refine ⟨hnd, hadm, fun hm => ?_⟩
    obtain ⟨hl, ⟨xs, hx, hdom⟩, hz⟩ := hn hm
    exact ⟨hl, ⟨xs, hx, hok _ _ _ hdom⟩, hz⟩
  · rintro d ins outs τ m m' _ ⟨xs, hr, hz, ys, hlen, hrel, rfl⟩
    exact ⟨xs, hr, hz, ys, hlen, extendRelOf_rel_mono hP hrel, rfl⟩

end NLAlib.Ops
