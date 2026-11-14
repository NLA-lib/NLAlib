/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.BasisExtensionContract
public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.IndependentLoop
public import NLAlib.Ops.Logic.Tactic

/-!
# A stored basis extension

A call of `NLAlib.Ops.OrthOp.extend` leaves three blocks in the store: the basis of `k` columns,
the `b` new columns directly after it, and the coefficient block. This file names that state as
a predicate on the store, `NLAlib.Krylov.GolubKahan.Band.ExtAt`, proves the call rule that
establishes it and the frame rule that keeps it, and reads it back from a longer stored basis
and from a packed coefficient buffer in the vocabulary of `NLAlib.blockPrefix` and
`NLAlib.blockCols`. The driver `NLAlib.Krylov.GolubKahan.Band.solve` is proved from these rules.

## Main definitions

* `NLAlib.Krylov.GolubKahan.Band.ExtAt`: the store holds a basis extension.
* `NLAlib.Krylov.GolubKahan.Band.ProductExtAt`: the store holds a basis extension by a block
  related to a stored block.

## Main results

* `NLAlib.Krylov.GolubKahan.Band.decodeMatrix_take`,
  `NLAlib.Krylov.GolubKahan.Band.blockCols_decodeMatrix`,
  `NLAlib.Krylov.GolubKahan.Band.blockPrefix_decodeMatrix`,
  `NLAlib.Krylov.GolubKahan.Band.decv_drop_take`: blocks and columns of a decoded block.
* `NLAlib.Krylov.GolubKahan.Band.readBlock_take_eq`,
  `NLAlib.Krylov.GolubKahan.Band.readBlock_drop_take_eq`,
  `NLAlib.Krylov.GolubKahan.Band.exists_readBlock_of_columns`: parts of a block that was read.
* `NLAlib.Krylov.GolubKahan.Band.writes_extend`: the call rule of a basis extension.
* `NLAlib.Krylov.GolubKahan.Band.ExtAt.mono`, `NLAlib.Krylov.GolubKahan.Band.ExtAt.keep`: a
  weaker property of the extended block, and the frame rule.
* `NLAlib.Krylov.GolubKahan.Band.ExtAt.exists_blocks`,
  `NLAlib.Krylov.GolubKahan.Band.ExtAt.exists_start`: readback from the whole stored basis.
* `NLAlib.Krylov.GolubKahan.Band.writes_extend_product`,
  `NLAlib.Krylov.GolubKahan.Band.ProductExtAt.keep`,
  `NLAlib.Krylov.GolubKahan.Band.ProductExtAt.exists_blocks`: the same three rules for an
  extension by a block related to a stored block.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.GolubKahan.Band

open Ops

variable {K Op Tst : Type} [Inhabited K]

/-! ### Blocks of a decoded block -/

/-- The position of the entry $(i, j)$ of a column-major block of $c$ columns of length $r$ is
below $cr$. -/
theorem entry_lt {r c : ℕ} (i : Fin r) (j : Fin c) : (j : ℕ) * r + i < c * r := by
  have h := Nat.mul_le_mul_right r (Nat.succ_le_of_lt j.2)
  rw [Nat.succ_mul] at h
  omega

/-- A decoded block of $c$ columns of length $r$ reads only its first $cr$ words. -/
theorem decodeMatrix_take (dec : K → ℝ) {r c l : ℕ} (xs : List K) (h : c * r ≤ l) :
    decodeMatrix dec r c (xs.take l) = decodeMatrix dec r c xs := by
  ext i j
  have hlt := entry_lt i j
  simp only [decodeMatrix_apply, vec, List.getD_eq_getElem?_getD]
  rw [List.getElem?_take_of_lt (by omega)]

/-- Block $i$ of a decoded block of $N$ columns stored as consecutive blocks of $b$ columns is
the decoded block of the words from the offset $ibr$ on. -/
theorem blockCols_decodeMatrix (dec : K → ℝ) {r N b i : ℕ} (xs : List K) (h : i * b + b ≤ N) :
    blockCols b (decodeMatrix dec r N xs) i = decodeMatrix dec r b (xs.drop (i * b * r)) := by
  ext x c
  have hc : i * b + (c : ℕ) < N := by omega
  simp only [blockCols, Matrix.of_apply, dif_pos hc, decodeMatrix_apply, vec,
    List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 3
  ring

/-- The first $i$ blocks of a decoded block of $N$ columns stored as consecutive blocks of $b$
columns are the decoded block of $ib$ columns of the same words. -/
theorem blockPrefix_decodeMatrix (dec : K → ℝ) {r N b i : ℕ} (xs : List K) (h : i * b ≤ N) :
    blockPrefix b (decodeMatrix dec r N xs) i = decodeMatrix dec r (i * b) xs := by
  ext x d
  have hd : (d : ℕ) < N := by omega
  simp only [blockPrefix, Matrix.of_apply, dif_pos hd, decodeMatrix_apply]

/-- Column $j$ of a decoded block of $b$ columns of length $r$ is the decoded vector of its
words $jr, \dots, jr + r - 1$. -/
theorem decv_drop_take (dec : K → ℝ) {r b : ℕ} (xs : List K) (j : Fin b) :
    decv dec r ((xs.drop (j * r)).take r) = (decodeMatrix dec r b xs).col j := by
  ext i
  simp only [decv, vec, Matrix.col_apply, decodeMatrix_apply]
  rw [Store.getD_drop_take _ _ _ _ i.2]

/-! ### Parts of a block that was read -/

omit [Inhabited K] in
/-- A block read at the start of a longer block that was read is its prefix. -/
theorem readBlock_take_eq {s : Store K} {B o N n : ℕ} {full sub : List K}
    (hfull : s.readBlock B o N = some full) (hsub : s.readBlock B o n = some sub)
    (hn : n ≤ N) : sub = full.take n := by
  have h := Store.readBlock_sub hfull (o := 0) (n := n) (by omega)
  rw [Nat.add_zero, hsub] at h
  simpa using h

omit [Inhabited K] in
/-- A block read inside a longer block that was read is the corresponding part. -/
theorem readBlock_drop_take_eq {s : Store K} {B o N a n : ℕ} {full sub : List K}
    (hfull : s.readBlock B o N = some full) (hsub : s.readBlock B (o + a) n = some sub)
    (hn : a + n ≤ N) : sub = (full.drop a).take n :=
  Option.some.inj (hsub.symm.trans (Store.readBlock_sub hfull hn))

omit [Inhabited K] in
/-- Consecutive readable blocks of the same length are one readable block. -/
theorem exists_readBlock_of_columns {s : Store K} {B o r : ℕ} (b : ℕ)
    (h : ∀ j < b, ∃ ys, s.readBlock B (o + j * r) r = some ys) :
    ∃ ys, s.readBlock B o (b * r) = some ys := by
  induction b with
  | zero => exact ⟨[], by simp⟩
  | succ b ih =>
    obtain ⟨ys, hys⟩ := ih fun j hj => h j (by omega)
    obtain ⟨y, hy⟩ := h b (by omega)
    exact ⟨ys ++ y, by rw [Nat.succ_mul]; exact Store.readBlock_add hys hy⟩

/-! ### The stored extension -/

/-- **The store holds a basis extension** with `r` rows: the `k` columns at the operand `Q`, the
`b` columns directly after them and the `(k + b) × b` coefficient block at the operand `C` are
readable, and their decoded matrices satisfy the extension predicate `Ext` with a block
$\mathbf{W}$ that has the property `P`. -/
def ExtAt (dec : K → ℝ) (Ext : ExtendPred ℝ) (s : Store K) (r k b : ℕ) (Q C : ℕ × ℕ)
    (P : Matrix (Fin r) (Fin b) ℝ → Prop) : Prop :=
  ∃ qs qs' cs W, s.readBlock Q.1 Q.2 (k * r) = some qs ∧
    s.readBlock Q.1 (Q.2 + k * r) (b * r) = some qs' ∧
    s.readBlock C.1 C.2 ((k + b) * b) = some cs ∧ P W ∧
    Ext r k b (decodeMatrix dec r k qs) W (decodeMatrix dec r b qs')
      (coefTop (decodeMatrix dec (k + b) b cs)) (coefBot (decodeMatrix dec (k + b) b cs))

/-- A stored extension by a block with the property `P` is one by a block with any weaker
property. -/
theorem ExtAt.mono {dec : K → ℝ} {Ext : ExtendPred ℝ} {s : Store K} {r k b : ℕ} {Q C : ℕ × ℕ}
    {P P' : Matrix (Fin r) (Fin b) ℝ → Prop} (h : ExtAt dec Ext s r k b Q C P)
    (hP : ∀ W, P W → P' W) : ExtAt dec Ext s r k b Q C P' := by
  obtain ⟨qs, qs', cs, W, hq, hq', hc, hW, hE⟩ := h
  exact ⟨qs, qs', cs, W, hq, hq', hc, hP W hW, hE⟩

/-- The new block of a stored extension is readable. -/
theorem ExtAt.exists_readBlock {dec : K → ℝ} {Ext : ExtendPred ℝ} {s : Store K} {r k b : ℕ}
    {Q C : ℕ × ℕ} {P : Matrix (Fin r) (Fin b) ℝ → Prop} (h : ExtAt dec Ext s r k b Q C P) :
    ∃ qs', s.readBlock Q.1 (Q.2 + k * r) (b * r) = some qs' := by
  obtain ⟨_, qs', _, _, _, hq', _⟩ := h
  exact ⟨qs', hq'⟩

/-- The basis and the new block of a stored extension are one readable block. -/
theorem ExtAt.exists_readBlock_basis {dec : K → ℝ} {Ext : ExtendPred ℝ} {s : Store K}
    {r k b : ℕ} {Q C : ℕ × ℕ} {P : Matrix (Fin r) (Fin b) ℝ → Prop}
    (h : ExtAt dec Ext s r k b Q C P) :
    ∃ xs, s.readBlock Q.1 Q.2 (k * r + b * r) = some xs := by
  obtain ⟨qs, qs', _, _, hq, hq', _⟩ := h
  exact ⟨qs ++ qs', Store.readBlock_add hq hq'⟩

/-- The coefficient block of a stored extension is readable. -/
theorem ExtAt.exists_readBlock_coef {dec : K → ℝ} {Ext : ExtendPred ℝ} {s : Store K}
    {r k b : ℕ} {Q C : ℕ × ℕ} {P : Matrix (Fin r) (Fin b) ℝ → Prop}
    (h : ExtAt dec Ext s r k b Q C P) :
    ∃ cs, s.readBlock C.1 C.2 ((k + b) * b) = some cs := by
  obtain ⟨_, _, cs, _, _, _, hc, _⟩ := h
  exact ⟨cs, hc⟩

/-- Frame rule of a stored extension: a run that writes no cell of the `k + b` stored
columns and none of the coefficient block keeps the extension. -/
theorem ExtAt.keep {dec : K → ℝ} {Ext : ExtendPred ℝ} {s s' : Store K} {F : Fp} {r k b : ℕ}
    {Q C : ℕ × ℕ} {P : Matrix (Fin r) (Fin b) ℝ → Prop} (h : ExtAt dec Ext s r k b Q C P)
    (hfr : s.EqOff F s') (hQ : ∀ i < k * r + b * r, ¬ F Q.1 (Q.2 + i))
    (hC : ∀ i < (k + b) * b, ¬ F C.1 (C.2 + i)) : ExtAt dec Ext s' r k b Q C P := by
  obtain ⟨qs, qs', cs, W, hq, hq', hc, hW, hE⟩ := h
  refine ⟨qs, qs', cs, W, hfr.readBlock_of hq fun i hi => hQ i (by omega),
    hfr.readBlock_of hq' fun i hi => ?_, hfr.readBlock_of hc hC, hW, hE⟩
  rw [Nat.add_assoc]
  exact hQ (k * r + i) (by omega)

/-- The call rule of a basis extension. On a readable basis `qs` of `k` columns at `Q` and a
readable block `ws` of `b` columns at `W`, in three distinct buffers with room for the new block
directly after the basis and for the coefficients at `C`, a call of an operation that meets the
contract of a basis extension for the predicate `Ext` at admitted dimensions `[r, k, b]` writes
only its three output blocks, does not move the tape, and leaves a stored extension by the
decoded block `ws`. -/
theorem writes_extend {dec : K → ℝ} {Ext : ExtendPred ℝ} {ok : ℕ → ℕ → ℕ → Prop}
    {I : Interp Op Tst K} {o : Op}
    (hO : I.Meets .total o ((extendRelOf dec ok Ext).spec ExtendOperands))
    {τ : Tape K} {ρ : Env} {ds : List IExp} {ins outs : List Operand} {r k b : ℕ}
    {Q W C : ℕ × ℕ} {μ : Mem K} {qs ws : List K}
    (hd : IExp.evalList ρ.idx ds = some [r, k, b]) (ha : Operand.evalList ρ ins = some [Q, W])
    (hb : Operand.evalList ρ outs = some [(Q.1, Q.2 + k * r), W, C])
    (hQW : Q.1 ≠ W.1) (hQC : Q.1 ≠ C.1) (hWC : W.1 ≠ C.1) (hok : ok r k b)
    (hl : μ.Live [Q, W, C]) (hq : μ.store.readBlock Q.1 Q.2 (k * r) = some qs)
    (hw : μ.store.readBlock W.1 W.2 (b * r) = some ws)
    (hQr : Q.2 + k * r + b * r ≤ μ.store.len Q.1) (hWr : W.2 + b * r ≤ μ.store.len W.1)
    (hCr : C.2 + (k + b) * b ≤ μ.store.len C.1) :
    Writes .total I τ (.call o ds ins outs) ρ
      (Fp.blocks [(Q.1, Q.2 + k * r), W, C] [b * r, b * r, (k + b) * b])
      (fun μ' => μ'.pos = μ.pos ∧
        ExtAt dec Ext μ'.store r k b Q C (· = decodeMatrix dec r b ws)) μ := by
  have hreads : μ.readBlocks [Q, W] ((extendRelOf dec ok Ext).inLens [r, k, b]) =
      some [qs, ws] := Mem.readBlocks_of_cons hq (Mem.readBlocks_of_cons hw rfl)
  have hlive : μ.Live ([Q, W] ++ [(Q.1, Q.2 + k * r), W, C]) := by
    simp only [List.cons_append, List.nil_append, Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.1, hl.2.1, hl.2.2⟩
  have hap : Fp.Apart [(Q.1, Q.2 + k * r), W, C] [b * r, b * r, (k + b) * b] :=
    ⟨Fp.disj_sup_right.mpr ⟨Fp.disj_inBlock_of_ne hQW,
      Fp.disj_sup_right.mpr ⟨Fp.disj_inBlock_of_ne hQC, Fp.disj_bot_right _⟩⟩,
      Fp.disj_sup_right.mpr ⟨Fp.disj_inBlock_of_ne hWC, Fp.disj_bot_right _⟩,
      Fp.disj_bot_right _, trivial⟩
  refine (writes_call hO (ls := [b * r, b * r, (k + b) * b]) hd ha hb rfl rfl rfl
    ⟨Q, W, C, rfl, rfl, hQW, hQC, hWC⟩ hap
    fun _ => ⟨hlive, ⟨[qs, ws], hreads, hok⟩, hQr, hWr, hCr, trivial⟩).mono le_rfl ?_
  rintro μ' hfr ⟨hpos, xs, ys, hxs, hys, hrel⟩
  obtain rfl : xs = [qs, ws] := Option.some.inj (hxs.symm.trans hreads)
  obtain ⟨y₁, ys', hy₁, hys', rfl⟩ := Mem.readBlocks_cons_eq_some.mp hys
  obtain ⟨y₂, ys'', -, hys'', rfl⟩ := Mem.readBlocks_cons_eq_some.mp hys'
  obtain ⟨y₃, ys₃, hy₃, hys₃, rfl⟩ := Mem.readBlocks_cons_eq_some.mp hys''
  obtain rfl : ys₃ = [] := by simpa [Mem.readBlocks] using hys₃.symm
  refine ⟨by simpa using hpos, qs, y₁, y₃, _, hfr.readBlock_of hq fun i hi hF => ?_, hy₁, hy₃,
    rfl, hrel⟩
  simp only [fpNF] at hF
  omega

/-! ### Readback -/

/-- Readback of a stored extension from the whole stored basis and from a longer
coefficient buffer. If the basis of the extension is the first `i` blocks of `b` columns of a
readable block `full` of `N` columns, and its coefficient block starts at the offset `o` of a
readable block `cfull`, the extension predicate holds of the first `i` blocks and of block `i`
of the decoded `full` and of the decoded coefficient words from the offset `o` on. -/
theorem ExtAt.exists_blocks {dec : K → ℝ} {Ext : ExtendPred ℝ} {s : Store K}
    {r k b i N o L : ℕ} {Q C : ℕ × ℕ} {P : Matrix (Fin r) (Fin b) ℝ → Prop}
    {full cfull : List K} (h : ExtAt dec Ext s r k b Q (C.1, C.2 + o) P) (hk : k = i * b)
    (hN : i * b + b ≤ N) (hq : s.readBlock Q.1 Q.2 (N * r) = some full)
    (hc : s.readBlock C.1 C.2 L = some cfull) (hL : o + (k + b) * b ≤ L) :
    ∃ W, P W ∧ Ext r (i * b) b (blockPrefix b (decodeMatrix dec r N full) i) W
      (blockCols b (decodeMatrix dec r N full) i)
      (coefTop (decodeMatrix dec (i * b + b) b (cfull.drop o)))
      (coefBot (decodeMatrix dec (i * b + b) b (cfull.drop o))) := by
  subst hk
  obtain ⟨qs, qs', cs, W, hqs, hqs', hcs, hP, hE⟩ := h
  have hN' := Nat.mul_le_mul_right r hN
  rw [Nat.add_mul] at hN'
  obtain rfl := readBlock_take_eq hq hqs (by omega)
  obtain rfl := readBlock_drop_take_eq hq hqs' hN'
  obtain rfl := readBlock_drop_take_eq hc hcs hL
  rw [decodeMatrix_take _ _ le_rfl, decodeMatrix_take _ _ le_rfl,
    decodeMatrix_take dec (cfull.drop o) (Nat.mul_comm b (i * b + b)).le] at hE
  rw [blockPrefix_decodeMatrix _ _ (by omega), blockCols_decodeMatrix _ _ hN]
  exact ⟨W, hP, hE⟩

/-- Readback of the first stored extension, of the empty basis: block `0` of the decoded
stored basis `vs` of `N` columns and the decoded `b × b` coefficient block extend the empty
basis, with zero coefficients against it. -/
theorem ExtAt.exists_start {dec : K → ℝ} {Ext : ExtendPred ℝ} {s : Store K} {n b N : ℕ}
    {V G : ℕ × ℕ} {P : Matrix (Fin n) (Fin b) ℝ → Prop} {vs gs : List K}
    (h : ExtAt dec Ext s n 0 b V G P) (hN : b ≤ N)
    (hv : s.readBlock V.1 V.2 (N * n) = some vs)
    (hg : s.readBlock G.1 G.2 (b * b) = some gs) :
    ∃ W, P W ∧ Ext n 0 b 0 W (blockCols b (decodeMatrix dec n N vs) 0) 0
      (decodeMatrix dec b b gs) := by
  obtain ⟨qs, qs', cs, W, -, hqs', hcs, hP, hE⟩ := h
  have hN' := Nat.mul_le_mul_right n hN
  obtain rfl := readBlock_drop_take_eq hv hqs' (by omega)
  obtain rfl : gs = cs := by
    rw [Nat.zero_add, hg] at hcs
    exact Option.some.inj hcs
  have hQ : decodeMatrix dec n 0 qs = 0 := Subsingleton.elim _ _
  have hT : coefTop (decodeMatrix dec (0 + b) b gs) = 0 := Subsingleton.elim _ _
  have hB : coefBot (decodeMatrix dec (0 + b) b gs) = decodeMatrix dec b b gs := by
    ext i c
    simp [coefBot, decodeMatrix_apply]
  have hC : decodeMatrix dec n b ((vs.drop (0 * n)).take (b * n)) =
      blockCols b (decodeMatrix dec n N vs) 0 := by
    rw [decodeMatrix_take _ _ le_rfl, blockCols_decodeMatrix _ _ (by omega)]
    simp
  rw [hQ, hT, hB, hC] at hE
  exact ⟨W, hP, hE⟩

/-! ### An extension by a block related to a stored block -/

/-- **The store holds an extension by a block related to a stored block**: the block of `b`
columns of length `c` at the operand `X` is readable, and the store holds a basis extension
(`NLAlib.Krylov.GolubKahan.Band.ExtAt`) of the `k` columns at `Q`, with coefficients at `C`, by
a block that is related by `Rel` to the decoded block at `X`. In the driver `Rel` is the
relation between a block and the block of its computed products with the matrix. -/
def ProductExtAt (dec : K → ℝ) (Ext : ExtendPred ℝ) {r c b : ℕ}
    (Rel : Matrix (Fin c) (Fin b) ℝ → Matrix (Fin r) (Fin b) ℝ → Prop) (s : Store K) (k : ℕ)
    (X Q C : ℕ × ℕ) : Prop :=
  ∃ xs, s.readBlock X.1 X.2 (b * c) = some xs ∧
    ExtAt dec Ext s r k b Q C (Rel (decodeMatrix dec c b xs))

/-- The extension of an extension by a related block, with the relation forgotten. -/
theorem ProductExtAt.extAt {dec : K → ℝ} {Ext : ExtendPred ℝ} {r c b : ℕ}
    {Rel : Matrix (Fin c) (Fin b) ℝ → Matrix (Fin r) (Fin b) ℝ → Prop} {s : Store K} {k : ℕ}
    {X Q C : ℕ × ℕ} (h : ProductExtAt dec Ext Rel s k X Q C) :
    ExtAt dec Ext s r k b Q C fun _ => True := by
  obtain ⟨_, _, hE⟩ := h
  exact hE.mono fun _ _ => trivial

/-- Frame rule of an extension by a related block: a run that writes no cell of the related
block, of the `k + b` stored columns or of the coefficient block keeps it. -/
theorem ProductExtAt.keep {dec : K → ℝ} {Ext : ExtendPred ℝ} {r c b : ℕ}
    {Rel : Matrix (Fin c) (Fin b) ℝ → Matrix (Fin r) (Fin b) ℝ → Prop} {s s' : Store K}
    {F : Fp} {k : ℕ} {X Q C : ℕ × ℕ} (h : ProductExtAt dec Ext Rel s k X Q C)
    (hfr : s.EqOff F s') (hX : ∀ i < b * c, ¬ F X.1 (X.2 + i))
    (hQ : ∀ i < k * r + b * r, ¬ F Q.1 (Q.2 + i))
    (hC : ∀ i < (k + b) * b, ¬ F C.1 (C.2 + i)) : ProductExtAt dec Ext Rel s' k X Q C := by
  obtain ⟨xs, hx, hE⟩ := h
  exact ⟨xs, hfr.readBlock_of hx hX, hE.keep hfr hQ hC⟩

/-- The call rule of a basis extension by a related block. On a readable basis `qs` of `k`
columns at `Q` and a readable block `ws` of `b` columns at `W`, in three distinct buffers with
room for the new block directly after the basis and for the coefficients at `C`, let the decoded
`ws` be related by `Rel` to the decoded readable block `xs` at `X`, no cell of which is an output
cell of the call. Then a call of an operation that meets the contract of a basis extension for
the predicate `Ext` at admitted dimensions `[r, k, b]` writes only its three output blocks, does
not move the tape, and leaves a stored extension by a block related to the block at `X`. -/
theorem writes_extend_product {dec : K → ℝ} {Ext : ExtendPred ℝ} {ok : ℕ → ℕ → ℕ → Prop}
    {I : Interp Op Tst K} {o : Op}
    (hO : I.Meets .total o ((extendRelOf dec ok Ext).spec ExtendOperands))
    {τ : Tape K} {ρ : Env} {ds : List IExp} {ins outs : List Operand} {r c k b : ℕ}
    {Rel : Matrix (Fin c) (Fin b) ℝ → Matrix (Fin r) (Fin b) ℝ → Prop}
    {X Q W C : ℕ × ℕ} {μ : Mem K} {xs qs ws : List K}
    (hd : IExp.evalList ρ.idx ds = some [r, k, b]) (ha : Operand.evalList ρ ins = some [Q, W])
    (hb : Operand.evalList ρ outs = some [(Q.1, Q.2 + k * r), W, C])
    (hQW : Q.1 ≠ W.1) (hQC : Q.1 ≠ C.1) (hWC : W.1 ≠ C.1) (hok : ok r k b)
    (hl : μ.Live [Q, W, C]) (hq : μ.store.readBlock Q.1 Q.2 (k * r) = some qs)
    (hw : μ.store.readBlock W.1 W.2 (b * r) = some ws)
    (hQr : Q.2 + k * r + b * r ≤ μ.store.len Q.1) (hWr : W.2 + b * r ≤ μ.store.len W.1)
    (hCr : C.2 + (k + b) * b ≤ μ.store.len C.1)
    (hx : μ.store.readBlock X.1 X.2 (b * c) = some xs)
    (hrel : Rel (decodeMatrix dec c b xs) (decodeMatrix dec r b ws))
    (hX : ∀ i < b * c, ¬ Fp.blocks [(Q.1, Q.2 + k * r), W, C] [b * r, b * r, (k + b) * b]
      X.1 (X.2 + i)) :
    Writes .total I τ (.call o ds ins outs) ρ
      (Fp.blocks [(Q.1, Q.2 + k * r), W, C] [b * r, b * r, (k + b) * b])
      (fun μ' => μ'.pos = μ.pos ∧ ProductExtAt dec Ext Rel μ'.store k X Q C) μ := by
  refine (writes_extend hO hd ha hb hQW hQC hWC hok hl hq hw hQr hWr hCr).mono le_rfl ?_
  rintro μ' hfr ⟨hpos, hE⟩
  refine ⟨hpos, xs, hfr.readBlock_of hx hX, hE.mono fun W hW => ?_⟩
  subst hW
  exact hrel

/-- Readback of an extension by a related block from the whole stored blocks. If the
related block is block `t` of a readable block `xfull` of `M` columns, the basis is the first
`i` blocks of a readable block `full` of `N` columns, and the coefficient block starts at the
offset `o` of a readable block `cfull`, then block `i` of the decoded `full` and the decoded
coefficient words from `o` on extend the first `i` blocks of the decoded `full` by a block
related to block `t` of the decoded `xfull`. -/
theorem ProductExtAt.exists_blocks {dec : K → ℝ} {Ext : ExtendPred ℝ} {r c b : ℕ}
    {Rel : Matrix (Fin c) (Fin b) ℝ → Matrix (Fin r) (Fin b) ℝ → Prop} {s : Store K}
    {k i N o L a t M : ℕ} {X Q C : ℕ × ℕ} {full cfull xfull : List K}
    (h : ProductExtAt dec Ext Rel s k (X.1, X.2 + a) Q (C.1, C.2 + o)) (hk : k = i * b)
    (hN : i * b + b ≤ N) (hq : s.readBlock Q.1 Q.2 (N * r) = some full)
    (hc : s.readBlock C.1 C.2 L = some cfull) (hL : o + (k + b) * b ≤ L)
    (hx : s.readBlock X.1 X.2 (M * c) = some xfull) (ha : a = t * b * c)
    (hM : t * b + b ≤ M) :
    ∃ W, Rel (blockCols b (decodeMatrix dec c M xfull) t) W ∧
      Ext r (i * b) b (blockPrefix b (decodeMatrix dec r N full) i) W
        (blockCols b (decodeMatrix dec r N full) i)
        (coefTop (decodeMatrix dec (i * b + b) b (cfull.drop o)))
        (coefBot (decodeMatrix dec (i * b + b) b (cfull.drop o))) := by
  obtain ⟨xs, hxs, hE⟩ := h
  subst ha
  obtain ⟨W, hW, hE'⟩ := hE.exists_blocks hk hN hq hc hL
  have hM' := Nat.mul_le_mul_right c hM
  rw [Nat.add_mul] at hM'
  obtain rfl := readBlock_drop_take_eq hx hxs hM'
  rw [decodeMatrix_take _ _ le_rfl] at hW
  rw [blockCols_decodeMatrix _ _ hM]
  exact ⟨W, hW, hE'⟩

end NLAlib.Krylov.GolubKahan.Band
