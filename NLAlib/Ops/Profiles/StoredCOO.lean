/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.StoredOperator
public import NLAlib.Ops.Blas.ScalarProducts
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Scalar
public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.VectorUpdate
public import NLAlib.Ops.AllocationFree
public import NLAlib.Ops.Workspace

/-!
# Scalar lowering of an explicit coordinate matrix

The coordinate pattern is a fixed public configuration. One tree serves every runtime
shape and every supplied value block for that pattern. Entries outside the current shape
are skipped by explicit size guards; repeated positions accumulate in storage.

## Main definitions

* `NLAlib.Ops.StoredCOO.entries` emits guarded scalar updates for a fixed pattern.
* `NLAlib.Ops.StoredCOO.matvec` initializes the output and applies those updates.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Ops.StoredCOO

variable {Op Tst : Type} [Has ScalarOp Op]

/-- One guarded coordinate update using the shared scalar-product step. -/
def entry (row col p : ℕ) : Stmt Op Tst :=
  .ifPos (.var 0 - .const row) (.ifPos (.var 1 - .const col)
    (.frame [] [⟨0, .var 2 + .const p⟩, ⟨1, .var 3 + .const col⟩,
      ⟨3, .const 0⟩, ⟨2, .var 4 + .const row⟩] ScalarProducts.step.body))

/-- Scalar updates for a fixed pattern, beginning at value offset `p`.
The environment has dimensions `[rows,cols]`, operands `[data,x,y]` and a fresh
one-cell temporary buffer at slot three. All guards use declared runtime dimensions. -/
def entries : List (ℕ × ℕ) → ℕ → Stmt Op Tst
  | [], _ => .skip
  | (row, col) :: tail, p => .seq (entry row col p) (entries tail (p + 1))

/-- Initialize all destination rows and apply the fixed coordinate list using one temporary.
The output is required to be spatially separate from matrix values and the input vector. -/
def matvec (pattern : List (ℕ × ℕ)) : Impl Op Tst where
  nd := 2
  nin := 2
  nout := 1
  body := .alloc (.const 1) (.seq
    (.loop (.var 0) (.call (Has.inj (ScalarOp.lit 0)) [] []
      [⟨2, .var 4 + .var 5⟩])) (entries pattern 0))

variable {K : Type} [Semiring K]

private def action (cols : ℕ) : List (ℕ × ℕ) → List K → (ℕ → K) → ℕ → K
  | [], _, _, _ => 0
  | (r, c) :: tail, vals, x, i =>
      (if r = i ∧ c < cols then vals.getD 0 0 * x c else 0) +
        action cols tail vals.tail x i

private def accumulated (rows cols : ℕ) :
    List (ℕ × ℕ) → List K → (ℕ → K) → (ℕ → K) → ℕ → K
  | [], _, _, v => v
  | (r, c) :: tail, vals, x, v => accumulated rows cols tail vals.tail x
      (if r < rows ∧ c < cols then
        Function.update v r (v r + vals.getD 0 0 * x c) else v)

private theorem accumulated_eq (rows cols : ℕ) (pattern : List (ℕ × ℕ)) (vals : List K)
    (x v : ℕ → K) (i : ℕ) (hi : i < rows) :
    accumulated rows cols pattern vals x v i = v i + action cols pattern vals x i := by
  induction pattern generalizing vals v with
  | nil => simp [accumulated, action]
  | cons rc tail ih =>
    rcases rc with ⟨r, c⟩
    simp only [accumulated, ih, action]
    by_cases h : r < rows ∧ c < cols
    · rw [if_pos h]
      by_cases he : i = r
      · subst i
        simp [h.2, add_assoc]
      · simp [Function.update_of_ne he, Ne.symm he]
    · rw [if_neg h]
      have he : ¬ (r = i ∧ c < cols) := by omega
      simp [he]

private theorem cooMatrix_cons (rows cols : ℕ) (r c : ℕ) (tail : List (ℕ × ℕ))
    (a : K) (vals : List K) :
    StoredOperator.cooMatrix ((r, c) :: tail) rows cols (a :: vals) =
      Matrix.of (fun (i : Fin rows) (j : Fin cols) =>
        if (r, c) = ((i : ℕ), (j : ℕ)) then a else 0) +
        StoredOperator.cooMatrix tail rows cols vals := by
  ext i j
  simp [StoredOperator.cooMatrix, Finset.sum_range_succ', add_comm]

private theorem single_mulVec (rows cols r c : ℕ) (a : K) (x : ℕ → K) (i : Fin rows) :
    (Matrix.of (fun (i : Fin rows) (j : Fin cols) =>
      if (r, c) = ((i : ℕ), (j : ℕ)) then a else 0) *ᵥ fun j => x j) i =
        if r = i ∧ c < cols then a * x c else 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul]
  by_cases hr : r = i
  · subst r
    by_cases hc : c < cols
    · rw [Finset.sum_eq_single ⟨c, hc⟩]
      · simp [hc]
      · intro b _ hb
        have he : c ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
        simp [he]
      · simp
    · have he : ∀ b : Fin cols, c ≠ (b : ℕ) := fun b h => hc (h ▸ b.isLt)
      simp [hc, he]
  · simp [hr]

private theorem cooMatrix_mulVec (rows cols : ℕ) (pattern : List (ℕ × ℕ))
    (vals : List K) (x : ℕ → K) (hlen : vals.length = pattern.length) (i : Fin rows) :
    (StoredOperator.cooMatrix pattern rows cols vals *ᵥ fun j => x j) i =
      action cols pattern vals x i := by
  induction pattern generalizing vals with
  | nil => simp [StoredOperator.cooMatrix, Matrix.mulVec, dotProduct, action]
  | cons rc tail ih =>
    rcases rc with ⟨r, c⟩
    cases vals with
    | nil => simp at hlen
    | cons a vals =>
      rw [cooMatrix_cons, Matrix.add_mulVec, Pi.add_apply, single_mulVec,
        ih vals (by simpa using hlen)]
      simp [action]

variable {𝕜 : Type} [RCLike 𝕜] {I : Interp Op Tst 𝕜} {tape : Tape 𝕜} {m : Mem 𝕜}

private theorem writes_entry_valid (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {rows cols row col p : ℕ} {data x y : ℕ × ℕ} {t : ℕ}
    (hr : row < rows) (hc : col < cols) (a b : 𝕜) (v : ℕ → 𝕜)
    (hl : m.Live [data, x, y, (t, 0)])
    (hA : m.store.readBlock data.1 (data.2 + p) 1 = some [a])
    (hX : m.store.readBlock x.1 (x.2 + col) 1 = some [b])
    (hV : m.store.HoldsVec y.1 y.2 rows v)
    (hTY : Fp.Disj (Store.inBlock t 0 1) (Store.inBlock y.1 y.2 rows))
    (ht : 1 ≤ m.store.len t) (hy : y.2 + rows ≤ m.store.len y.1) :
    Writes .total I tape (entry row col p)
      ⟨[rows, cols, data.2, x.2, y.2], [data.1, x.1, y.1, t]⟩
      (Store.inBlock y.1 y.2 rows ⊔ Store.inBlock t 0 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.HoldsVec y.1 y.2 rows
        (Function.update v row (v row + a * b))) m := by
  unfold entry
  refine writes_ifPos rfl ?_
  rw [if_pos (Nat.sub_pos_iff_lt.mpr hr)]
  refine writes_ifPos rfl ?_
  rw [if_pos (Nat.sub_pos_iff_lt.mpr hc)]
  have hA' : m.store.readBlock y.1 (y.2 + row) 1 = some [v row] := by
    simp [Store.readBlock, hV row hr]
  have hl' : m.Live [(data.1, data.2 + p), (x.1, x.2 + col), (t, 0), (y.1, y.2 + row)] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl data (by simp), hl x (by simp), hl (t, 0) (by simp), hl y (by simp), trivial⟩
  have hcell : Store.inBlock y.1 (y.2 + row) 1 ≤ Store.inBlock y.1 y.2 rows :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  refine ((ScalarProducts.writes_step hS a b (v row) hl' hA hX hA'
    (hTY.mono le_rfl hcell) (by simpa using ht)
    (by change y.2 + row + 1 ≤ m.store.len y.1; omega)).in_frame
      rfl rfl hl').mono (sup_le le_sup_right (hcell.trans le_sup_left)) ?_
  intro m' hfr ⟨hp, hout⟩
  have hg : m'.store.get y.1 (y.2 + row) = some (v row + a * b) := by
    simpa using Store.get_of_readBlock hout Nat.zero_lt_one (0 : 𝕜)
  exact ⟨hp, hV.update_of_frame (by simpa only [sup_comm] using hfr) hTY hg⟩

private theorem writes_entry (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {rows cols row col p : ℕ} {data x y : ℕ × ℕ} {t : ℕ}
    (a : 𝕜) (xs v : ℕ → 𝕜) (hl : m.Live [data, x, y, (t, 0)])
    (hA : m.store.readBlock data.1 (data.2 + p) 1 = some [a])
    (hX : m.store.HoldsVec x.1 x.2 cols xs) (hV : m.store.HoldsVec y.1 y.2 rows v)
    (hTY : Fp.Disj (Store.inBlock t 0 1) (Store.inBlock y.1 y.2 rows))
    (ht : 1 ≤ m.store.len t) (hy : y.2 + rows ≤ m.store.len y.1) :
    Writes .total I tape (entry row col p)
      ⟨[rows, cols, data.2, x.2, y.2], [data.1, x.1, y.1, t]⟩
      (Store.inBlock y.1 y.2 rows ⊔ Store.inBlock t 0 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.HoldsVec y.1 y.2 rows
        (if row < rows ∧ col < cols then
          Function.update v row (v row + a * xs col) else v)) m := by
  by_cases hr : row < rows
  · by_cases hc : col < cols
    · simpa only [if_pos (show row < rows ∧ col < cols from ⟨hr, hc⟩)] using
        writes_entry_valid (tape := tape) hS hr hc a (xs col) v hl hA
        (by simp [Store.readBlock, hX col hc]) hV hTY ht hy
    · unfold entry
      refine writes_ifPos rfl ?_
      rw [if_pos (Nat.sub_pos_iff_lt.mpr hr)]
      refine writes_ifPos rfl ?_
      rw [if_neg (by omega)]
      exact ⟨rfl, by simpa only [and_false, hc, if_false] using hV⟩
  · unfold entry
    refine writes_ifPos rfl ?_
    rw [if_neg (by omega)]
    exact ⟨rfl, by simpa only [false_and, hr, if_false] using hV⟩

private theorem writes_entries (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {rows cols p : ℕ} {data x y : ℕ × ℕ} {t : ℕ} (pattern : List (ℕ × ℕ))
    (vals : List 𝕜) (xs v : ℕ → 𝕜) (hl : m.Live [data, x, y, (t, 0)])
    (hD : m.store.readBlock data.1 (data.2 + p) pattern.length = some vals)
    (hX : m.store.HoldsVec x.1 x.2 cols xs) (hV : m.store.HoldsVec y.1 y.2 rows v)
    (hDD : Fp.Disj (Store.inBlock y.1 y.2 rows ⊔ Store.inBlock t 0 1)
      (Store.inBlock data.1 (data.2 + p) pattern.length))
    (hDX : Fp.Disj (Store.inBlock y.1 y.2 rows ⊔ Store.inBlock t 0 1)
      (Store.inBlock x.1 x.2 cols))
    (hTY : Fp.Disj (Store.inBlock t 0 1) (Store.inBlock y.1 y.2 rows))
    (ht : 1 ≤ m.store.len t) (hy : y.2 + rows ≤ m.store.len y.1) :
    Writes .total I tape (entries pattern p)
      ⟨[rows, cols, data.2, x.2, y.2], [data.1, x.1, y.1, t]⟩
      (Store.inBlock y.1 y.2 rows ⊔ Store.inBlock t 0 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.HoldsVec y.1 y.2 rows
        (accumulated rows cols pattern vals xs v)) m := by
  induction pattern generalizing p vals v m with
  | nil => exact (Writes.skip ⟨rfl, hV⟩).mono bot_le (fun _ _ h => h)
  | cons rc tail ih =>
    rcases rc with ⟨row, col⟩
    have hlen := Store.length_of_readBlock hD
    cases vals with
    | nil => simp at hlen
    | cons a vals =>
      have hlen' : vals.length = tail.length := by simpa using hlen
      have hHead : m.store.readBlock data.1 (data.2 + p) 1 = some [a] := by
        simpa using Store.readBlock_sub hD (o := 0) (n := 1) (by simp)
      have hTail : m.store.readBlock data.1 (data.2 + (p + 1)) tail.length = some vals := by
        simpa [Nat.add_assoc, ← hlen'] using
          Store.readBlock_sub hD (o := 1) (n := tail.length) (by simp; omega)
      have hsub : Store.inBlock data.1 (data.2 + (p + 1)) tail.length ≤
          Store.inBlock data.1 (data.2 + p) (tail.length + 1) :=
        Fp.inBlock_le_inBlock (by omega) (by omega)
      refine Writes.seq_le (writes_entry hS a xs v hl hHead hX hV hTY ht hy) le_rfl ?_
      intro m₁ hfr ⟨hp, hV₁⟩
      have hTail₁ := hfr.keep (Store.readsOnly_readBlock _ _ _ vals)
        (hDD.mono le_rfl hsub) hTail
      have hX₁ := hfr.keep (Store.readsOnly_holdsVec _ _ _ xs) hDX hX
      refine (ih (m := m₁) vals _ (hl.congr hfr.length_eq) hTail₁ hX₁ hV₁
        (hDD.mono le_rfl hsub) (by simpa only [hfr.len_eq] using ht)
        (by simpa only [hfr.len_eq] using hy)).mono le_rfl ?_
      intro m₂ _ ⟨hp₂, hV₂⟩
      exact ⟨hp₂.trans hp, by
        simpa only [accumulated, List.tail_cons, List.getD_cons_zero] using hV₂⟩

private theorem writes_zero (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {rows cols : ℕ} {data x y : ℕ × ℕ} {t : ℕ} (hy : y.2 + rows ≤ m.store.len y.1) :
    Writes .total I tape (.loop (.var 0) (.call (Has.inj (ScalarOp.lit 0)) [] []
      [⟨2, .var 4 + .var 5⟩]))
      ⟨[rows, cols, data.2, x.2, y.2], [data.1, x.1, y.1, t]⟩
      (Store.inBlock y.1 y.2 rows)
      (fun m' => m'.store.HoldsVec y.1 y.2 rows (fun _ => 0) ∧ m'.pos = m.pos) m := by
  refine writes_fill rfl (fun _ => 0) (fun _ => m.pos) rfl ?_
  intro i hi m' hfr _ hp
  refine (writes_call_const (hS (.lit 0)) rfl trivial (by
    change y.2 + i < m'.store.len y.1
    rw [hfr.len_eq]
    omega)).mono le_rfl ?_
  intro m'' _ ⟨hp', hw⟩
  exact ⟨by simpa [RCLikeBlas.machine] using hw, hp'.trans hp⟩

/-- The guarded scalar COO implementation is total on disjoint readable data and input
vectors. Every coordinate pattern is admitted; out-of-shape entries are ignored and
repeated coordinates add. One scoped scalar temporary is released before returning. -/
theorem writes_matvec (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (pattern : List (ℕ × ℕ)) {rows cols : ℕ} {data x y : ℕ × ℕ} (vals xs : List 𝕜)
    (hl : m.Live [data, x, y])
    (hD : m.store.readBlock data.1 data.2 pattern.length = some vals)
    (hX : m.store.readBlock x.1 x.2 cols = some xs)
    (hYD : Fp.Disj (Store.inBlock y.1 y.2 rows) (Store.inBlock data.1 data.2 pattern.length))
    (hYX : Fp.Disj (Store.inBlock y.1 y.2 rows) (Store.inBlock x.1 x.2 cols))
    (hy : y.2 + rows ≤ m.store.len y.1) :
    Writes .total I tape (matvec pattern).body (Env.frame [rows, cols] [data, x, y])
      (Store.inBlock y.1 y.2 rows)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock y.1 y.2 rows =
        some (List.ofFn fun i : Fin rows =>
          ∑ j : Fin cols, StoredOperator.cooMatrix pattern rows cols vals i j *
            xs.getD j 0)) m := by
  apply writes_allocs_readBlock (lens := [.const 1]) (ns := [1]) rfl (hl y (by simp))
  intro store hlength hlens hBelow
  have hlen : store.length = m.store.length + 1 := by simpa using hlength
  have ht : store.len m.store.length = 1 := by simpa using hlens 0 (by simp)
  have hdLive : data.1 < m.store.length := hl data (by simp)
  have hxLive : x.1 < m.store.length := hl x (by simp)
  have hyLive : y.1 < m.store.length := hl y (by simp)
  have hLive : (Mem.mk store m.pos).Live [data, x, y, (m.store.length, 0)] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨by omega, by omega, by omega, by omega, trivial⟩
  have hData : store.readBlock data.1 data.2 pattern.length = some vals := by kept
  have hInput : store.HoldsVec x.1 x.2 cols (fun i => xs.getD i 0) := by
    have hRead : store.readBlock x.1 x.2 cols = some xs := by kept
    exact fun i hi => Store.get_of_readBlock hRead hi 0
  have hcap : y.2 + rows ≤ store.len y.1 := by
    simpa only [(hBelow y.1 hyLive).1] using hy
  refine Writes.seq_le (writes_zero hS hcap) le_sup_left ?_
  intro m₁ hfr ⟨hV, hp⟩
  have hD₁ := hfr.keep (Store.readsOnly_readBlock _ _ _ vals) hYD hData
  have hX₁ := hfr.keep (Store.readsOnly_holdsVec _ _ _ (fun i => xs.getD i 0)) hYX hInput
  have hTD : Fp.Disj (Store.inBlock m.store.length 0 1)
      (Store.inBlock data.1 data.2 pattern.length) :=
    Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hdLive))
  have hTX : Fp.Disj (Store.inBlock m.store.length 0 1) (Store.inBlock x.1 x.2 cols) :=
    Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hxLive))
  have hTY : Fp.Disj (Store.inBlock m.store.length 0 1) (Store.inBlock y.1 y.2 rows) :=
    Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hyLive))
  refine (writes_entries hS pattern vals (fun i => xs.getD i 0) (fun _ => 0)
    (hLive.congr hfr.length_eq)
    (by simpa only [Nat.add_zero] using hD₁) hX₁ hV
    (Fp.disj_sup_left.mpr ⟨by simpa only [Nat.add_zero] using hYD,
      by simpa only [Nat.add_zero] using hTD⟩)
    (Fp.disj_sup_left.mpr ⟨hYX, hTX⟩) hTY (by simpa only [hfr.len_eq] using ht.ge)
    (by simpa only [hfr.len_eq] using hcap)).mono (by fp_sub) ?_
  intro m₂ _ ⟨hp₂, hv⟩
  refine ⟨hp₂.trans hp, ?_⟩
  rw [Store.readBlock_eq_some_iff]
  refine ⟨by simp, fun i hi => ?_⟩
  have h := hv i hi
  rw [accumulated_eq _ _ _ _ _ _ _ hi, zero_add,
    ← cooMatrix_mulVec rows cols pattern vals (fun i => xs.getD i 0)
      (Store.length_of_readBlock hD) ⟨i, hi⟩] at h
  simpa [Matrix.mulVec, dotProduct, List.getD_eq_getElem?_getD, hi] using h

/-- The scalar leaf realizes the declared COO matrix-vector contract. The pattern is fixed
before runtime dimensions and values; the output-separation admission is spatial. -/
theorem meets_matvec (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (pattern : List (ℕ × ℕ)) :
    (matvec (Op := Op) (Tst := Tst) pattern).Triple I .total
      ((StoredOperator.cooFunctions pattern .matvec).rel.spec
        (StoredOperator.OutApart (fun _ _ => pattern.length))) := by
  refine Impl.meets_of_writes fun d ins outs tape mem vals hnd hadm hl hread _ hroom => ?_
  obtain ⟨rows, cols, rfl⟩ := List.length_eq_two.mp hnd
  obtain ⟨data, x, ds, xs, rfl, hD, hX, rfl⟩ := Mem.readBlocks_two hread
  obtain ⟨y, rfl, hy⟩ := Mem.room_one hroom
  have hSep : Fp.Disj (Store.inBlock y.1 y.2 rows)
      (Store.inBlock data.1 data.2 pattern.length ⊔ Store.inBlock x.1 x.2 cols) := by
    simpa [StoredOperator.OutApart, Fp.blocks] using hadm
  refine ⟨⟨rfl, rfl, rfl⟩, (writes_matvec hS pattern ds xs hl hD hX
    (Fp.disj_sup_right.mp hSep).1 (Fp.disj_sup_right.mp hSep).2 hy).mono ?_ ?_⟩
  · change Store.inBlock y.1 y.2 rows ≤ Store.inBlock y.1 y.2 rows ⊔ ⊥
    exact le_sup_left
  intro mem' _ h
  let out := List.ofFn fun i : Fin rows =>
    ∑ j : Fin cols, StoredOperator.cooMatrix pattern rows cols ds i j * xs.getD j 0
  refine ⟨h.1, [out], ?_, ?_⟩
  · exact Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩
  · rfl

/-- The fixed coordinate sequence contains no allocation instructions. -/
theorem entries_allocationFree (pattern : List (ℕ × ℕ)) (p : ℕ) :
    (entries (Op := Op) (Tst := Tst) pattern p).allocationFree = true := by
  induction pattern generalizing p with
  | nil => rfl
  | cons rc tail ih =>
    rcases rc with ⟨row, col⟩
    simp [entries, entry, Stmt.ifPos, Stmt.allocationFree, ScalarProducts.step, ih]

/-- The COO scalar implementation reserves exactly one cell above caller storage,
independently of pattern length, dimensions and duplicate coordinates. -/
theorem matvec_peak_zero (pattern : List (ℕ × ℕ)) (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (matvec (Tst := Tst) pattern).body idx = 1 := by
  unfold matvec
  rw [stmtPeak_alloc]
  change 1 + stmtPeak (fun (_ : Op) _ => 0) _ idx = 1
  rw [stmtPeak_zero_of_allocationFree (by
    simpa [Stmt.allocationFree] using entries_allocationFree (Op := Op) (Tst := Tst) pattern 0)]

/-- A common primitive-workspace ceiling is added once to the one stored temporary. -/
theorem matvec_peak_le (pattern : List (ℕ × ℕ)) (W : Op → List ℕ → ℕ) (w : ℕ)
    (hW : ∀ o d, W o d ≤ w) (idx : List ℕ) :
    stmtPeak W (matvec (Tst := Tst) pattern).body idx ≤ 1 + w := by
  simpa only [matvec_peak_zero] using
    stmtPeak_le_zero_add W w hW (matvec (Tst := Tst) pattern).body idx

end NLAlib.Ops.StoredCOO
