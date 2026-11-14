/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Rotation
public import NLAlib.Ops.Logic.IndependentLoop
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Eigensolvers.ShiftedQR.Storage

/-!
# Scalar Givens row and column loops

Interleaved matrix entries use the existing pair layout in column-major order. One scoped
scratch block is reused by every entry-pair rotation in a row or column loop.

## Main results

* `NLAlib.ShiftedQR.rotateRowsWithScratch`: a scalar loop on two adjacent rows.
* `NLAlib.ShiftedQR.rotateColumnsWithScratch`: a scalar loop on two adjacent columns.
* `NLAlib.ShiftedQR.machineRowRotation`, `NLAlib.ShiftedQR.machineColRotation`: the rotations
  the loops compute on any machine; in exact arithmetic the Givens products
  (`NLAlib.ShiftedQR.machineRowRotation_eq`, `NLAlib.ShiftedQR.machineColRotation_eq`).
* `NLAlib.ShiftedQR.rotateRows_writes_word`, `NLAlib.ShiftedQR.rotateColumns_writes_word`: the
  loops on any machine; the exact theorems are their corollaries.
* `NLAlib.ShiftedQR.rotateRows_writes`: the exact left Givens product with scoped scratch.
* `NLAlib.ShiftedQR.rotateColumns_writes`: the exact right adjoint product with scoped scratch.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Apply one Givens rotation to adjacent rows of an interleaved square matrix, using ten
caller-owned scratch words. The dimension and first row are the two size arguments. -/
def rotateRowsWithScratch : Impl Op Tst := opsImpl% [n, k] (A, C, S, T) → (A) {
  for j < n {
    run rotateLeftWithScratch.body []
      (C, S, A[2 * (j * n + k)], A[2 * (j * n + k + 1)], T,
        A[2 * (j * n + k)], A[2 * (j * n + k + 1)])
  }
}

/-- Apply the adjoint Givens rotation on the right to adjacent columns, using ten caller-owned
scratch words. The dimension and first column are the two size arguments. -/
def rotateColumnsWithScratch : Impl Op Tst := opsImpl% [n, k] (A, C, S, T) → (A) {
  for i < n {
    run rotateRightWithScratch.body []
      (C, S, A[2 * (k * n + i)], A[2 * ((k + 1) * n + i)], T,
        A[2 * (k * n + i)], A[2 * ((k + 1) * n + i)])
  }
}

/-- A row rotation allocates and releases one ten-word scratch block for the entire loop. -/
def rotateRows : Impl Op Tst := opsImpl% [n, k] (A, C, S) → (A) {
  let T ← alloc 10;
  run rotateRowsWithScratch.body [n, k] (A, C, S, T, A)
}

/-- A column rotation allocates and releases one ten-word scratch block for the entire loop. -/
def rotateColumns : Impl Op Tst := opsImpl% [n, k] (A, C, S) → (A) {
  let T ← alloc 10;
  run rotateColumnsWithScratch.body [n, k] (A, C, S, T, A)
}

/-- The rows $i, j$ of $\mathbf{H}$ rotated pairwise by the coefficient words $(c, s)$ on the
machine `M`, as the scalar row rotation computes them: row $i$ is the computed
$c\mathbf{H}_{i\cdot} + s\mathbf{H}_{j\cdot}$, row $j$ the computed
$-\bar s\mathbf{H}_{i\cdot} + \bar c\mathbf{H}_{j\cdot}$ (`NLAlib.ShiftedQR.linearComplex`,
conjugation by negation of the words), the other rows are kept. -/
def machineRowRotation {n : ℕ} (M : Machine ℝ) (i j : Fin n) (c s : ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun r t => if r = i then linearComplex M c s (H i t) (H j t)
    else if r = j then linearComplex M ⟨M.neg s.re, s.im⟩ ⟨c.re, M.neg c.im⟩ (H i t) (H j t)
    else H r t

/-- The columns $i, j$ of $\mathbf{H}$ rotated pairwise by the adjoint of the rotation of the
coefficient words $(c, s)$ on the machine `M`, as the scalar column rotation computes them:
column $i$ is the computed $\bar c\mathbf{H}_{\cdot i} + \bar s\mathbf{H}_{\cdot j}$, column $j$
the computed $-s\mathbf{H}_{\cdot i} + c\mathbf{H}_{\cdot j}$, the other columns are kept. -/
def machineColRotation {n : ℕ} (M : Machine ℝ) (i j : Fin n) (c s : ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun r t => if t = i then linearComplex M ⟨c.re, M.neg c.im⟩ ⟨s.re, M.neg s.im⟩
      (H r i) (H r j)
    else if t = j then linearComplex M ⟨M.neg s.re, M.neg s.im⟩ c (H r i) (H r j)
    else H r t

section MachineRotation

variable {n : ℕ} {M : Machine ℝ} {i j : Fin n} {c s : ℂ} {H : Matrix (Fin n) (Fin n) ℂ}

/-- Row $i$ of the machine row rotation. -/
theorem machineRowRotation_apply_left (t : Fin n) :
    machineRowRotation M i j c s H i t = linearComplex M c s (H i t) (H j t) := by
  simp [machineRowRotation]

/-- Row $j$ of the machine row rotation. -/
theorem machineRowRotation_apply_right (hij : i ≠ j) (t : Fin n) :
    machineRowRotation M i j c s H j t =
      linearComplex M ⟨M.neg s.re, s.im⟩ ⟨c.re, M.neg c.im⟩ (H i t) (H j t) := by
  simp [machineRowRotation, Ne.symm hij]

/-- The machine row rotation keeps the rows other than $i, j$. -/
theorem machineRowRotation_apply_of_ne {r : Fin n} (hri : r ≠ i) (hrj : r ≠ j) (t : Fin n) :
    machineRowRotation M i j c s H r t = H r t := by
  simp [machineRowRotation, hri, hrj]

/-- Column $i$ of the machine column rotation. -/
theorem machineColRotation_apply_left (r : Fin n) :
    machineColRotation M i j c s H r i =
      linearComplex M ⟨c.re, M.neg c.im⟩ ⟨s.re, M.neg s.im⟩ (H r i) (H r j) := by
  simp [machineColRotation]

/-- Column $j$ of the machine column rotation. -/
theorem machineColRotation_apply_right (hij : i ≠ j) (r : Fin n) :
    machineColRotation M i j c s H r j =
      linearComplex M ⟨M.neg s.re, M.neg s.im⟩ c (H r i) (H r j) := by
  simp [machineColRotation, Ne.symm hij]

/-- The machine column rotation keeps the columns other than $i, j$. -/
theorem machineColRotation_apply_of_ne {t : Fin n} (hti : t ≠ i) (htj : t ≠ j) (r : Fin n) :
    machineColRotation M i j c s H r t = H r t := by
  simp [machineColRotation, hti, htj]

/-- In exact arithmetic the machine row rotation is the left Givens product. -/
theorem machineRowRotation_eq (hM : ExactModel id M) (hij : i ≠ j) :
    machineRowRotation M i j c s H = givens i j c s * H := by
  have hneg (r : ℝ) : M.neg r = -r := hM.neg r
  ext r t
  by_cases hri : r = i
  · subst hri
    rw [machineRowRotation_apply_left, givens_mul_apply_left hij, linearComplex_eq hM]
  by_cases hrj : r = j
  · subst hrj
    have hs : (⟨M.neg s.re, s.im⟩ : ℂ) = -star s := by
      apply Complex.ext <;> simp [hneg]
    have hc : (⟨c.re, M.neg c.im⟩ : ℂ) = star c := by
      apply Complex.ext <;> simp [hneg]
    rw [machineRowRotation_apply_right hij, givens_mul_apply_right hij, linearComplex_eq hM,
      hs, hc]
  rw [machineRowRotation_apply_of_ne hri hrj, givens_mul_apply_of_ne hri hrj]

end MachineRotation

/-- The view of one complex matrix entry in the shared interleaved layout. -/
def rotationEntry (a : ℕ × ℕ) (n : ℕ) (p : Fin n × Fin n) : ℕ × ℕ :=
  (a.1, a.2 + 2 * (p.2 * n + p.1))

/-- The two words belonging to an entry lie inside the full matrix footprint. -/
private theorem rotationEntry_le (a : ℕ × ℕ) (n : ℕ) (p : Fin n × Fin n) :
    Store.inBlock (rotationEntry a n p).1 (rotationEntry a n p).2 2 ≤
      Store.inBlock a.1 a.2 (2 * (n * n)) := by
  have h := Idx.add_lt_mul p.2.isLt p.1.isLt
  rintro b j ⟨rfl, hlo, hhi⟩
  refine ⟨rfl, ?_, ?_⟩ <;> dsimp [rotationEntry] at * <;> omega

/-- Different mathematical matrix entries have disjoint stored component pairs. -/
private theorem rotationEntry_disj {a : ℕ × ℕ} {n : ℕ} {p q : Fin n × Fin n}
    (hpq : p ≠ q) :
    Fp.Disj (Store.inBlock (rotationEntry a n p).1 (rotationEntry a n p).2 2)
      (Store.inBlock (rotationEntry a n q).1 (rotationEntry a n q).2 2) := by
  have h := (EntryCodec.pair ℝ).disj_entryBlock_matrix (b := a.1) (off := a.2) hpq
  simpa only [EntryCodec.entryBlock, EntryCodec.pair, rotationEntry, Nat.mul_comm 2] using h

/-- Reading a stored complex pair supplies each actual component. -/
private theorem rotationEntry_get {a : ℕ × ℕ} {z : ℂ} {s : Store ℝ}
    (h : s.readBlock a.1 a.2 2 = some [z.re, z.im]) :
    s.get a.1 a.2 = some z.re ∧ s.get a.1 (a.2 + 1) = some z.im := by
  constructor
  · simpa using Store.get_of_readBlock h (j := 0) (by omega) (0 : ℝ)
  · simpa using Store.get_of_readBlock h (j := 1) (by omega) (0 : ℝ)

/-- The two matrix entries updated by one rotation round. -/
private def rotationPairRegion {n : ℕ} (a : ℕ × ℕ)
    (p q : Fin n → Fin n × Fin n) (j : ℕ) : Fp := if hj : j < n then
  Store.inBlock (rotationEntry a n (p ⟨j, hj⟩)).1 (rotationEntry a n (p ⟨j, hj⟩)).2 2 ⊔
  Store.inBlock (rotationEntry a n (q ⟨j, hj⟩)).1 (rotationEntry a n (q ⟨j, hj⟩)).2 2 else ⊥

/-- A prefix of pair updates remains inside the original matrix block. -/
private theorem rotationPrefix_le {n : ℕ} (a : ℕ × ℕ)
    (p q : Fin n → Fin n × Fin n) (i : ℕ) :
    Fp.loopPrefix (rotationPairRegion a p q) i ≤
      Store.inBlock a.1 a.2 (2 * (n * n)) := by
  rintro b j ⟨k, _, hk⟩
  by_cases hkn : k < n
  · simp only [rotationPairRegion, dif_pos hkn] at hk
    exact sup_le (rotationEntry_le a n _) (rotationEntry_le a n _) b j hk
  · simp only [rotationPairRegion, dif_neg hkn] at hk
    exact hk.elim

/-- Earlier pair updates and separate scratch preserve an untouched matrix entry. -/
private theorem rotationPrefix_read {n : ℕ} {a : ℕ × ℕ}
    {p q : Fin n → Fin n × Fin n} {i : ℕ} {scratch : Fp} {s s' : Store ℝ}
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : HoldsMatrix a H s)
    (hfr : s.EqOff (Fp.loopPrefix (rotationPairRegion a p q) i ⊔ scratch) s')
    (hs : Fp.Disj scratch (Store.inBlock a.1 a.2 (2 * (n * n))))
    (r : Fin n × Fin n)
    (hr : ∀ j : Fin n, j < i → r ≠ p j ∧ r ≠ q j) :
    s'.readBlock (rotationEntry a n r).1 (rotationEntry a n r).2 2 =
      some [(H r.1 r.2).re, (H r.1 r.2).im] := by
  refine hfr.keep (Store.readsOnly_readBlock _ _ _ _) ?_ (hH.read_entry r.1 r.2)
  refine Fp.disj_sup_left.mpr ⟨?_, hs.mono le_rfl (rotationEntry_le a n r)⟩
  rintro b x ⟨j, hji, hx⟩ he
  by_cases hj : j < n
  · simp only [rotationPairRegion, dif_pos hj] at hx
    rcases hx with hx | hx
    · exact rotationEntry_disj (hr ⟨j, hj⟩ hji).1.symm b x hx he
    · exact rotationEntry_disj (hr ⟨j, hj⟩ hji).2.symm b x hx he
  · simp only [rotationPairRegion, dif_neg hj] at hx
    exact hx.elim

/-- Matrix and scratch separation preserves a coefficient pair throughout the loop. -/
private theorem rotationPrefix_coefficient {n : ℕ} {a c : ℕ × ℕ}
    {p q : Fin n → Fin n × Fin n} {i : ℕ} {scratch : Fp} {s s' : Store ℝ} {z : ℂ}
    (hfr : s.EqOff (Fp.loopPrefix (rotationPairRegion a p q) i ⊔ scratch) s')
    (hc : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock c.1 c.2 2))
    (hs : Fp.Disj scratch (Store.inBlock c.1 c.2 2))
    (hr : s.readBlock c.1 c.2 2 = some [z.re, z.im]) :
    s'.readBlock c.1 c.2 2 = some [z.re, z.im] :=
  hfr.keep (Store.readsOnly_readBlock _ _ _ _)
    (Fp.disj_sup_left.mpr ⟨hc.mono (rotationPrefix_le a p q i) le_rfl, hs⟩) hr

/-- Unpack the two actual output blocks of a scalar pair routine. -/
private theorem rotationPair_reads {m : Mem ℝ} {x y : ℕ × ℕ} {u v : ℂ}
    (h : m.readBlocks [x, y] [2, 2] = some [[u.re, u.im], [v.re, v.im]]) :
    m.store.readBlock x.1 x.2 2 = some [u.re, u.im] ∧
    m.store.readBlock y.1 y.2 2 = some [v.re, v.im] := by
  obtain ⟨xs, ys, hx, hy, he⟩ := Mem.readBlocks_cons_eq_some.mp h
  obtain ⟨hxs, hys⟩ := List.cons.inj he
  cases hxs
  cases hys
  obtain ⟨zs, ws, hz, _, he⟩ := Mem.readBlocks_cons_eq_some.mp hy
  obtain ⟨hzs, _⟩ := List.cons.inj he
  cases hzs
  exact ⟨hx, hz⟩

/-- The matrix, coefficients and capacities needed by one pair kernel survive its prefix. -/
private theorem rotationLoop_inputs {n : ℕ} {a c s t : ℕ × ℕ}
    {p q : Fin n → Fin n × Fin n} {i : Fin n} {m m' : Mem ℝ}
    {H : Matrix (Fin n) (Fin n) ℂ} {cv sv : ℂ}
    (hH : HoldsMatrix a H m.store)
    (hc : m.store.readBlock c.1 c.2 2 = some [cv.re, cv.im])
    (hs : m.store.readBlock s.1 s.2 2 = some [sv.re, sv.im])
    (hca : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock c.1 c.2 2))
    (hsa : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock s.1 s.2 2))
    (hta : t.1 ≠ a.1) (htc : t.1 ≠ c.1) (hts : t.1 ≠ s.1)
    (ht : t.2 + 10 ≤ m.store.len t.1)
    (hd : ∀ j : Fin n, j < i →
      p i ≠ p j ∧ p i ≠ q j ∧ q i ≠ p j ∧ q i ≠ q j)
    (hfr : m.store.EqOff (Fp.loopPrefix (rotationPairRegion a p q) i ⊔
      Store.inBlock t.1 t.2 10) m'.store) :
    m'.store.readBlock c.1 c.2 2 = some [cv.re, cv.im] ∧
    m'.store.readBlock s.1 s.2 2 = some [sv.re, sv.im] ∧
    m'.store.readBlock (rotationEntry a n (p i)).1 (rotationEntry a n (p i)).2 2 =
      some [(H (p i).1 (p i).2).re, (H (p i).1 (p i).2).im] ∧
    m'.store.readBlock (rotationEntry a n (q i)).1 (rotationEntry a n (q i)).2 2 =
      some [(H (q i).1 (q i).2).re, (H (q i).1 (q i).2).im] ∧
    t.2 + 10 ≤ m'.store.len t.1 ∧
    (rotationEntry a n (p i)).2 + 2 ≤ m'.store.len a.1 ∧
    (rotationEntry a n (q i)).2 + 2 ≤ m'.store.len a.1 := by
  have htc' := Fp.disj_inBlock_of_ne (o := t.2) (n := 10)
    (o' := c.2) (n' := 2) htc
  have hts' := Fp.disj_inBlock_of_ne (o := t.2) (n := 10)
    (o' := s.2) (n' := 2) hts
  have hta' := Fp.disj_inBlock_of_ne (o := t.2) (n := 10)
    (o' := a.2) (n' := 2 * (n * n)) hta
  have hx := rotationPrefix_read hH hfr hta' (p i) (fun j hj =>
    ⟨(hd j hj).1, (hd j hj).2.1⟩)
  have hy := rotationPrefix_read hH hfr hta' (q i) (fun j hj =>
    ⟨(hd j hj).2.2.1, (hd j hj).2.2.2⟩)
  have hxl := Store.lt_len_of_get (rotationEntry_get hx).2
  have hyl := Store.lt_len_of_get (rotationEntry_get hy).2
  refine ⟨rotationPrefix_coefficient hfr hca htc' hc,
    rotationPrefix_coefficient hfr hsa hts' hs, hx, hy, ?_, ?_, ?_⟩
  · rw [hfr.len_eq]
    exact ht
  · exact hxl
  · exact hyl

/-- Every argument of the pair call is live when its actual words and scratch capacity exist. -/
private theorem rotationPair_live {m : Mem ℝ} {c s x y t : ℕ × ℕ} {cv sv xv yv : ℂ}
    (hc : m.store.readBlock c.1 c.2 2 = some [cv.re, cv.im])
    (hs : m.store.readBlock s.1 s.2 2 = some [sv.re, sv.im])
    (hx : m.store.readBlock x.1 x.2 2 = some [xv.re, xv.im])
    (hy : m.store.readBlock y.1 y.2 2 = some [yv.re, yv.im])
    (ht : t.2 + 10 ≤ m.store.len t.1) : m.Live [c, s, x, y, t, x, y] := by
  have hcl := Store.lt_length_of_get (rotationEntry_get hc).1
  have hsl := Store.lt_length_of_get (rotationEntry_get hs).1
  have hxl := Store.lt_length_of_get (rotationEntry_get hx).1
  have hyl := Store.lt_length_of_get (rotationEntry_get hy).1
  have htl : t.1 < m.store.length := Store.lt_length_of_lt_len (by omega : t.2 < _)
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

omit [Has ScalarOp Op] in
/-- Collect independent pair updates and reconstruct the entire matrix. The body theorem
uses the actual prefix frame, while unchanged entries are retained by that same frame. -/
private theorem writes_rotationLoop {I : Interp Op Tst ℝ} {τ : Tape ℝ} {m : Mem ℝ}
    {ρ : Env} {bound : IExp} {body : Stmt Op Tst} {n : ℕ} {a : ℕ × ℕ}
    {H G : Matrix (Fin n) (Fin n) ℂ} (p q : Fin n → Fin n × Fin n)
    (scratch : Fp) (hH : HoldsMatrix a H m.store)
    (hn : bound.eval ρ.idx = some n)
    (hd : ∀ i j, i ≠ j → p i ≠ p j ∧ p i ≠ q j ∧ q i ≠ p j ∧ q i ≠ q j)
    (hs : Fp.Disj scratch (Store.inBlock a.1 a.2 (2 * (n * n))))
    (hkeep : ∀ r c, (∀ i, (r, c) ≠ p i ∧ (r, c) ≠ q i) → G r c = H r c)
    (hstep : ∀ (i : Fin n) (m' : Mem ℝ),
      m.store.EqOff (Fp.loopPrefix (rotationPairRegion a p q) i ⊔ scratch) m'.store →
      Writes .total I τ body (ρ.pushIdx i)
        (Store.inBlock (rotationEntry a n (p i)).1 (rotationEntry a n (p i)).2 2 ⊔
          Store.inBlock (rotationEntry a n (q i)).1 (rotationEntry a n (q i)).2 2 ⊔ scratch)
        (fun m'' => m''.pos = m'.pos ∧
          m''.store.readBlock (rotationEntry a n (p i)).1 (rotationEntry a n (p i)).2 2 =
            some [(G (p i).1 (p i).2).re, (G (p i).1 (p i).2).im] ∧
          m''.store.readBlock (rotationEntry a n (q i)).1 (rotationEntry a n (q i)).2 2 =
            some [(G (q i).1 (q i).2).re, (G (q i).1 (q i).2).im]) m') :
    Writes .total I τ (.loop bound body) ρ
      (Store.inBlock a.1 a.2 (2 * (n * n)) ⊔ scratch)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a G m'.store) m := by
  classical
  let region := rotationPairRegion a p q
  let result (j : ℕ) (s : Store ℝ) : Prop := if hj : j < n then
    s.readBlock (rotationEntry a n (p ⟨j, hj⟩)).1 (rotationEntry a n (p ⟨j, hj⟩)).2 2 =
      some [(G (p ⟨j, hj⟩).1 (p ⟨j, hj⟩).2).re, (G (p ⟨j, hj⟩).1 (p ⟨j, hj⟩).2).im] ∧
    s.readBlock (rotationEntry a n (q ⟨j, hj⟩)).1 (rotationEntry a n (q ⟨j, hj⟩)).2 2 =
      some [(G (q ⟨j, hj⟩).1 (q ⟨j, hj⟩).2).re, (G (q ⟨j, hj⟩).1 (q ⟨j, hj⟩).2).im]
    else True
  have hsub (j : ℕ) (hj : j < n) : region j ≤ Store.inBlock a.1 a.2 (2 * (n * n)) := by
    simp only [region, rotationPairRegion, dif_pos hj]
    exact sup_le (rotationEntry_le a n _) (rotationEntry_le a n _)
  have hloop := writes_loop_disjoint_prefix_scratch (I := I) (τ := τ) (m := m)
    (md := .total) (body := body)
    (F := Fp.loopPrefix region n ⊔ scratch) (scratch := scratch) region result hn
    (fun j hj b x hx => Or.inl ⟨j, hj, hx⟩) le_sup_right
    (fun i hi j hj hij => ?_) (fun i hi => hs.mono le_rfl (hsub i hi))
    (fun i hi => ?_) (fun i hi m' hfr => ?_)
  · refine hloop.mono (sup_le ?_ le_sup_right) fun m' hfr ⟨hp, hr⟩ => ⟨hp, ?_⟩
    · rintro b x ⟨i, hi, hx⟩
      exact Or.inl (hsub i hi b x hx)
    have hentry (r c : Fin n) :
        m'.store.readBlock (rotationEntry a n (r, c)).1
          (rotationEntry a n (r, c)).2 2 = some [(G r c).re, (G r c).im] := by
      by_cases he : ∃ i, (r, c) = p i ∨ (r, c) = q i
      · obtain ⟨i, hi⟩ := he
        have h := hr i i.isLt
        simp only [result, dif_pos i.isLt] at h
        rcases hi with hi | hi
        · simpa only [← hi] using h.1
        · simpa only [← hi] using h.2
      · have hne : ∀ i, (r, c) ≠ p i ∧ (r, c) ≠ q i := by
          intro i
          exact ⟨fun h => he ⟨i, Or.inl h⟩, fun h => he ⟨i, Or.inr h⟩⟩
        rw [hkeep r c hne]
        exact hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by
          refine Fp.disj_sup_left.mpr ⟨?_, hs.mono le_rfl (rotationEntry_le a n _)⟩
          rintro b x ⟨j, hj, hx⟩ he
          simp only [region, rotationPairRegion, dif_pos hj] at hx
          rcases hx with hx | hx
          · exact rotationEntry_disj (hne ⟨j, hj⟩).1.symm b x hx he
          · exact rotationEntry_disj (hne ⟨j, hj⟩).2.symm b x hx he)
          (hH.read_entry r c)
    apply HoldsMatrix.of_get
    · intro r c
      exact (rotationEntry_get (hentry r c)).1
    · intro r c
      exact (rotationEntry_get (hentry r c)).2
  · rcases hd ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (Fin.mk.inj h)) with ⟨h₁, h₂, h₃, h₄⟩
    simp only [region, rotationPairRegion, dif_pos hi, dif_pos hj,
      Fp.disj_sup_left, Fp.disj_sup_right]
    exact ⟨⟨rotationEntry_disj h₁, rotationEntry_disj h₃⟩,
      ⟨rotationEntry_disj h₂, rotationEntry_disj h₄⟩⟩
  · simp only [result, region, rotationPairRegion, dif_pos hi]
    exact Store.ReadsOnly.and
      (Store.readsOnly_readBlock _ _ _ _) (Store.readsOnly_readBlock _ _ _ _)
  · simpa only [region, rotationPairRegion, result, dif_pos hi] using hstep ⟨i, hi⟩ m' hfr

/-- All row rounds touch different pairs because their column coordinates differ. -/
private theorem rotationRows_disjoint {n : ℕ} (r t : Fin n) (i j : Fin n) (hij : i ≠ j) :
    (r, i) ≠ (r, j) ∧ (r, i) ≠ (t, j) ∧ (t, i) ≠ (r, j) ∧ (t, i) ≠ (t, j) :=
  ⟨fun h => hij (congrArg Prod.snd h), fun h => hij (congrArg Prod.snd h),
    fun h => hij (congrArg Prod.snd h), fun h => hij (congrArg Prod.snd h)⟩

/-- All column rounds touch different pairs because their row coordinates differ. -/
private theorem rotationColumns_disjoint {n : ℕ} (r t : Fin n) (i j : Fin n) (hij : i ≠ j) :
    (i, r) ≠ (j, r) ∧ (i, r) ≠ (j, t) ∧ (i, t) ≠ (j, r) ∧ (i, t) ≠ (j, t) :=
  ⟨fun h => hij (congrArg Prod.fst h), fun h => hij (congrArg Prod.fst h),
    fun h => hij (congrArg Prod.fst h), fun h => hij (congrArg Prod.fst h)⟩

/-- The scalar right kernel gives the two changed columns of the adjoint matrix product. -/
private theorem rotationColumns_values {n : ℕ} {r t : Fin n} (hrt : r ≠ t)
    (c s : ℂ) (H : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (H * (givens r t c s)ᴴ) i r = star c * H i r + star s * H i t ∧
    (H * (givens r t c s)ᴴ) i t = -s * H i r + c * H i t := by
  rw [conjTranspose_givens, mul_givens_apply_left hrt, mul_givens_apply_right hrt]
  simp only [star_neg, star_star]
  constructor <;> ring

/-- In exact arithmetic the machine column rotation is the right adjoint Givens product. -/
theorem machineColRotation_eq {n : ℕ} {M : Machine ℝ} {i j : Fin n} {c s : ℂ}
    {H : Matrix (Fin n) (Fin n) ℂ} (hM : ExactModel id M) (hij : i ≠ j) :
    machineColRotation M i j c s H = H * (givens i j c s)ᴴ := by
  have hneg (r : ℝ) : M.neg r = -r := hM.neg r
  ext r t
  by_cases hti : t = i
  · subst hti
    have hc : (⟨c.re, M.neg c.im⟩ : ℂ) = star c := by
      apply Complex.ext <;> simp [hneg]
    have hs : (⟨s.re, M.neg s.im⟩ : ℂ) = star s := by
      apply Complex.ext <;> simp [hneg]
    rw [machineColRotation_apply_left, (rotationColumns_values hij c s H r).1,
      linearComplex_eq hM, hc, hs]
  by_cases htj : t = j
  · subst htj
    have hn : (⟨M.neg s.re, M.neg s.im⟩ : ℂ) = -s := by
      apply Complex.ext <;> simp [hneg]
    rw [machineColRotation_apply_right hij, (rotationColumns_values hij c s H r).2,
      linearComplex_eq hM, hn]
  rw [machineColRotation_apply_of_ne hti htj, conjTranspose_givens]
  exact (mul_givens_apply_of_ne hti htj (star c) (-s) H r).symm

/-- Scalar pair rotations on any machine store the machine row rotation
(`NLAlib.ShiftedQR.machineRowRotation`) of the rows $k, k + 1$. The matrix and coefficients are
disjoint, and a separate ten-word buffer is reused for all columns. The two coefficient views may
overlap each other. [GolubVanLoan2013, §5.1.8]. -/
theorem rotateRowsWithScratch_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ}
    {n k : ℕ} {a c s t : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {cv sv : ℂ}
    (hk : k + 1 < n) (hH : HoldsMatrix a H m.store)
    (hc : m.store.readBlock c.1 c.2 2 = some [cv.re, cv.im])
    (hs : m.store.readBlock s.1 s.2 2 = some [sv.re, sv.im])
    (hca : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock c.1 c.2 2))
    (hsa : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock s.1 s.2 2))
    (hta : t.1 ≠ a.1) (htc : t.1 ≠ c.1) (hts : t.1 ≠ s.1)
    (ht : t.2 + 10 ≤ m.store.len t.1) :
    Writes .total I τ rotateRowsWithScratch.body (Env.frame [n, k] [a, c, s, t, a])
      (Store.inBlock a.1 a.2 (2 * (n * n)) ⊔ Store.inBlock t.1 t.2 10)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a
        (machineRowRotation M (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ cv sv H) m'.store) m := by
  let r : Fin n := ⟨k, by omega⟩
  let r' : Fin n := ⟨k + 1, hk⟩
  have hrr : r ≠ r' := by intro h; have := congrArg Fin.val h; dsimp [r, r'] at this; omega
  change Writes .total I τ (.loop _ _) _ _ _ m
  refine writes_rotationLoop (fun j => (r, j)) (fun j => (r', j))
    (Store.inBlock t.1 t.2 10) hH rfl (rotationRows_disjoint r r')
    (Fp.disj_inBlock_of_ne hta) ?_ ?_
  · intro i j hne
    exact machineRowRotation_apply_of_ne
      (fun hir => (hne j).1 (Prod.ext hir rfl))
      (fun hir => (hne j).2 (Prod.ext hir rfl)) j
  · intro j m' hfr
    obtain ⟨hc', hs', hx, hy, ht', hxl, hyl⟩ := rotationLoop_inputs hH hc hs hca hsa
      hta htc hts ht (fun i hi => rotationRows_disjoint r r' j i (by
        intro he; have := congrArg Fin.val he; omega)) hfr
    have hw := writes_rotateLeftWithScratch_word (τ := τ) (m := m')
      (x := rotationEntry a n (r, j)) (y := rotationEntry a n (r', j))
      hS htc hts hta hta
      (rotationEntry_disj (fun h => hrr (congrArg Prod.fst h)))
      (rotationEntry_get hc').1 (rotationEntry_get hc').2
      (rotationEntry_get hs').1 (rotationEntry_get hs').2
      (rotationEntry_get hx).1 (rotationEntry_get hx).2
      (rotationEntry_get hy).1 (rotationEntry_get hy).2 ht' hxl hyl
    have hl := rotationPair_live hc' hs' hx hy ht'
    refine (writes_frame rfl (by simp [Operand.evalList, Operand.eval, Env.frame,
      Env.pushIdx, IExp.eval, rotationEntry, r, r', Nat.add_assoc]) hl hw).mono ?_ ?_
    · simp only [Fp.blocks, sup_bot_eq, sup_comm]
      exact le_rfl
    · intro m'' _ hp
      refine ⟨hp.1, ?_⟩
      dsimp only [r, r'] at hp hrr ⊢
      simpa only [machineRowRotation_apply_left, machineRowRotation_apply_right hrr] using
        rotationPair_reads hp.2

/-- Exact scalar pair rotations implement multiplication by the Givens matrix on the left.
The matrix and coefficients are disjoint, and a separate ten-word buffer is reused for all
columns. The two coefficient views may overlap each other. [GolubVanLoan2013, §5.1.8]. -/
theorem rotateRowsWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n k : ℕ} {a c s t : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {cv sv : ℂ}
    (hk : k + 1 < n) (hH : HoldsMatrix a H m.store)
    (hc : m.store.readBlock c.1 c.2 2 = some [cv.re, cv.im])
    (hs : m.store.readBlock s.1 s.2 2 = some [sv.re, sv.im])
    (hca : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock c.1 c.2 2))
    (hsa : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock s.1 s.2 2))
    (hta : t.1 ≠ a.1) (htc : t.1 ≠ c.1) (hts : t.1 ≠ s.1)
    (ht : t.2 + 10 ≤ m.store.len t.1) :
    Writes .total I τ rotateRowsWithScratch.body (Env.frame [n, k] [a, c, s, t, a])
      (Store.inBlock a.1 a.2 (2 * (n * n)) ⊔ Store.inBlock t.1 t.2 10)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a
        (givens (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ cv sv * H) m'.store) m := by
  refine (rotateRowsWithScratch_writes_word hS hk hH hc hs hca hsa hta htc hts ht).mono le_rfl
    fun _ _ ⟨hp, hm⟩ => ⟨hp, ?_⟩
  rwa [machineRowRotation_eq hE (Fin.ne_of_val_ne (Nat.succ_ne_self k).symm)] at hm

/-- Scalar pair rotations on any machine store the machine column rotation
(`NLAlib.ShiftedQR.machineColRotation`) of the columns $k, k + 1$. The matrix and coefficients
are disjoint, and a separate ten-word buffer is reused for all rows. The two coefficient views
may overlap each other. [GolubVanLoan2013, §5.1.8]. -/
theorem rotateColumnsWithScratch_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ}
    {n k : ℕ} {a c s t : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {cv sv : ℂ}
    (hk : k + 1 < n) (hH : HoldsMatrix a H m.store)
    (hc : m.store.readBlock c.1 c.2 2 = some [cv.re, cv.im])
    (hs : m.store.readBlock s.1 s.2 2 = some [sv.re, sv.im])
    (hca : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock c.1 c.2 2))
    (hsa : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock s.1 s.2 2))
    (hta : t.1 ≠ a.1) (htc : t.1 ≠ c.1) (hts : t.1 ≠ s.1)
    (ht : t.2 + 10 ≤ m.store.len t.1) :
    Writes .total I τ rotateColumnsWithScratch.body (Env.frame [n, k] [a, c, s, t, a])
      (Store.inBlock a.1 a.2 (2 * (n * n)) ⊔ Store.inBlock t.1 t.2 10)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a
        (machineColRotation M (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ cv sv H) m'.store) m := by
  let r : Fin n := ⟨k, by omega⟩
  let r' : Fin n := ⟨k + 1, hk⟩
  have hrr : r ≠ r' := by intro h; have := congrArg Fin.val h; dsimp [r, r'] at this; omega
  change Writes .total I τ (.loop _ _) _ _ _ m
  refine writes_rotationLoop (fun j => (j, r)) (fun j => (j, r'))
    (Store.inBlock t.1 t.2 10) hH rfl (rotationColumns_disjoint r r')
    (Fp.disj_inBlock_of_ne hta) ?_ ?_
  · intro i j hne
    exact machineColRotation_apply_of_ne
      (fun hjr => (hne i).1 (Prod.ext rfl hjr))
      (fun hjr => (hne i).2 (Prod.ext rfl hjr)) i
  · intro j m' hfr
    obtain ⟨hc', hs', hx, hy, ht', hxl, hyl⟩ := rotationLoop_inputs hH hc hs hca hsa
      hta htc hts ht (fun i hi => rotationColumns_disjoint r r' j i (by
        intro he; have := congrArg Fin.val he; omega)) hfr
    have hw := writes_rotateRightWithScratch_word (τ := τ) (m := m')
      (x := rotationEntry a n (j, r)) (y := rotationEntry a n (j, r'))
      hS htc hts hta hta
      (rotationEntry_disj (fun h => hrr (congrArg Prod.snd h)))
      (rotationEntry_get hc').1 (rotationEntry_get hc').2
      (rotationEntry_get hs').1 (rotationEntry_get hs').2
      (rotationEntry_get hx).1 (rotationEntry_get hx).2
      (rotationEntry_get hy).1 (rotationEntry_get hy).2 ht' hxl hyl
    have hl := rotationPair_live hc' hs' hx hy ht'
    refine (writes_frame rfl (by simp [Operand.evalList, Operand.eval, Env.frame,
      Env.pushIdx, IExp.eval, rotationEntry, r, r']) hl hw).mono ?_ ?_
    · simp only [Fp.blocks, sup_bot_eq, sup_comm]
      exact le_rfl
    · intro m'' _ hp
      refine ⟨hp.1, ?_⟩
      dsimp only [r, r'] at hp hrr ⊢
      simpa only [machineColRotation_apply_left, machineColRotation_apply_right hrr] using
        rotationPair_reads hp.2

/-- Exact scalar pair rotations implement multiplication by the adjoint Givens matrix on the right.
The matrix and coefficients are disjoint, and a separate ten-word buffer is reused for all
rows. The two coefficient views may overlap each other. [GolubVanLoan2013, §5.1.8]. -/
theorem rotateColumnsWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n k : ℕ} {a c s t : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {cv sv : ℂ}
    (hk : k + 1 < n) (hH : HoldsMatrix a H m.store)
    (hc : m.store.readBlock c.1 c.2 2 = some [cv.re, cv.im])
    (hs : m.store.readBlock s.1 s.2 2 = some [sv.re, sv.im])
    (hca : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock c.1 c.2 2))
    (hsa : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock s.1 s.2 2))
    (hta : t.1 ≠ a.1) (htc : t.1 ≠ c.1) (hts : t.1 ≠ s.1)
    (ht : t.2 + 10 ≤ m.store.len t.1) :
    Writes .total I τ rotateColumnsWithScratch.body (Env.frame [n, k] [a, c, s, t, a])
      (Store.inBlock a.1 a.2 (2 * (n * n)) ⊔ Store.inBlock t.1 t.2 10)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a
        (H * (givens (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ cv sv)ᴴ) m'.store) m := by
  refine (rotateColumnsWithScratch_writes_word hS hk hH hc hs hca hsa hta htc hts ht).mono le_rfl
    fun _ _ ⟨hp, hm⟩ => ⟨hp, ?_⟩
  rwa [machineColRotation_eq hE (Fin.ne_of_val_ne (Nat.succ_ne_self k).symm)] at hm

/-- A scoped row rotation on any machine stores the machine row rotation
(`NLAlib.ShiftedQR.machineRowRotation`) and releases its scratch. The matrix and each coefficient
view are spatially disjoint; the coefficient views may overlap. [GolubVanLoan2013, §5.1.8]. -/
theorem rotateRows_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ}
    {n k : ℕ} {a c s : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {cv sv : ℂ}
    (hk : k + 1 < n) (hH : HoldsMatrix a H m.store)
    (hc : m.store.readBlock c.1 c.2 2 = some [cv.re, cv.im])
    (hs : m.store.readBlock s.1 s.2 2 = some [sv.re, sv.im])
    (hca : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock c.1 c.2 2))
    (hsa : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock s.1 s.2 2)) :
    Writes .total I τ rotateRows.body (Env.frame [n, k] [a, c, s, a])
      (Store.inBlock a.1 a.2 (2 * (n * n)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a
        (machineRowRotation M (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ cv sv H) m'.store) m := by
  have hal : a.1 < m.store.length := Store.lt_length_of_get
    (hH.get_re (⟨0, by omega⟩ : Fin n) ⟨0, by omega⟩)
  have hcl : c.1 < m.store.length := Store.lt_length_of_get (rotationEntry_get hc).1
  have hsl : s.1 < m.store.length := Store.lt_length_of_get (rotationEntry_get hs).1
  apply writes_allocs_preserving_post (lens := [.const 10]) (ns := [10]) rfl
    (fun hBelow hp => ⟨hp.1, hp.2.of_below hBelow hal⟩)
  intro store hlen hlens hBelow
  have hlen' : store.length = m.store.length + 1 := by simpa using hlen
  let t : ℕ × ℕ := (m.store.length, 0)
  let m₁ : Mem ℝ := ⟨store, m.pos⟩
  have ht : t.2 + 10 ≤ store.len t.1 := by
    have h := hlens 0 (by simp)
    simpa [t] using h.ge
  have hl : m₁.Live [a, c, s, t, a] := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz | hz | hz | hz <;> subst z
    · change a.1 < store.length
      omega
    · change c.1 < store.length
      omega
    · change s.1 < store.length
      omega
    · change m.store.length < store.length
      omega
    · change a.1 < store.length
      omega
  have hw := rotateRowsWithScratch_writes_word hS (τ := τ) (m := m₁) hk (hH.of_below hBelow hal)
    ((hBelow.readBlock hcl _ _).trans hc) ((hBelow.readBlock hsl _ _).trans hs) hca hsa
    (by dsimp [t]; omega) (by dsimp [t]; omega) (by dsimp [t]; omega) ht
  refine (writes_frame rfl rfl hl hw).mono ?_ (fun _ _ h => h)
  exact sup_le le_sup_left (Fp.inBlock_le_sup_above le_rfl)

/-- A scoped row rotation computes the exact left Givens product and releases its scratch.
The matrix and each coefficient view are spatially disjoint; the coefficient views may overlap.
[GolubVanLoan2013, §5.1.8]. -/
theorem rotateRows_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n k : ℕ} {a c s : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {cv sv : ℂ}
    (hk : k + 1 < n) (hH : HoldsMatrix a H m.store)
    (hc : m.store.readBlock c.1 c.2 2 = some [cv.re, cv.im])
    (hs : m.store.readBlock s.1 s.2 2 = some [sv.re, sv.im])
    (hca : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock c.1 c.2 2))
    (hsa : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock s.1 s.2 2)) :
    Writes .total I τ rotateRows.body (Env.frame [n, k] [a, c, s, a])
      (Store.inBlock a.1 a.2 (2 * (n * n)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a
        (givens (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ cv sv * H) m'.store) m := by
  refine (rotateRows_writes_word hS hk hH hc hs hca hsa).mono le_rfl
    fun _ _ ⟨hp, hm⟩ => ⟨hp, ?_⟩
  rwa [machineRowRotation_eq hE (Fin.ne_of_val_ne (Nat.succ_ne_self k).symm)] at hm

/-- A scoped column rotation on any machine stores the machine column rotation
(`NLAlib.ShiftedQR.machineColRotation`) and releases its scratch. The matrix and each
coefficient view are spatially disjoint; the coefficient views may overlap.
[GolubVanLoan2013, §5.1.8]. -/
theorem rotateColumns_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ}
    {n k : ℕ} {a c s : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {cv sv : ℂ}
    (hk : k + 1 < n) (hH : HoldsMatrix a H m.store)
    (hc : m.store.readBlock c.1 c.2 2 = some [cv.re, cv.im])
    (hs : m.store.readBlock s.1 s.2 2 = some [sv.re, sv.im])
    (hca : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock c.1 c.2 2))
    (hsa : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock s.1 s.2 2)) :
    Writes .total I τ rotateColumns.body (Env.frame [n, k] [a, c, s, a])
      (Store.inBlock a.1 a.2 (2 * (n * n)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a
        (machineColRotation M (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ cv sv H) m'.store) m := by
  have hal : a.1 < m.store.length := Store.lt_length_of_get
    (hH.get_re (⟨0, by omega⟩ : Fin n) ⟨0, by omega⟩)
  have hcl : c.1 < m.store.length := Store.lt_length_of_get (rotationEntry_get hc).1
  have hsl : s.1 < m.store.length := Store.lt_length_of_get (rotationEntry_get hs).1
  apply writes_allocs_preserving_post (lens := [.const 10]) (ns := [10]) rfl
    (fun hBelow hp => ⟨hp.1, hp.2.of_below hBelow hal⟩)
  intro store hlen hlens hBelow
  have hlen' : store.length = m.store.length + 1 := by simpa using hlen
  let t : ℕ × ℕ := (m.store.length, 0)
  let m₁ : Mem ℝ := ⟨store, m.pos⟩
  have ht : t.2 + 10 ≤ store.len t.1 := by
    have h := hlens 0 (by simp)
    simpa [t] using h.ge
  have hl : m₁.Live [a, c, s, t, a] := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz | hz | hz | hz <;> subst z
    · change a.1 < store.length
      omega
    · change c.1 < store.length
      omega
    · change s.1 < store.length
      omega
    · change m.store.length < store.length
      omega
    · change a.1 < store.length
      omega
  have hw := rotateColumnsWithScratch_writes_word hS (τ := τ) (m := m₁) hk (hH.of_below hBelow hal)
    ((hBelow.readBlock hcl _ _).trans hc) ((hBelow.readBlock hsl _ _).trans hs) hca hsa
    (by dsimp [t]; omega) (by dsimp [t]; omega) (by dsimp [t]; omega) ht
  refine (writes_frame rfl rfl hl hw).mono ?_ (fun _ _ h => h)
  exact sup_le le_sup_left (Fp.inBlock_le_sup_above le_rfl)

/-- A scoped column rotation computes the exact right adjoint Givens product and releases
its scratch.
The matrix and each coefficient view are spatially disjoint; the coefficient views may overlap.
[GolubVanLoan2013, §5.1.8]. -/
theorem rotateColumns_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n k : ℕ} {a c s : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {cv sv : ℂ}
    (hk : k + 1 < n) (hH : HoldsMatrix a H m.store)
    (hc : m.store.readBlock c.1 c.2 2 = some [cv.re, cv.im])
    (hs : m.store.readBlock s.1 s.2 2 = some [sv.re, sv.im])
    (hca : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock c.1 c.2 2))
    (hsa : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock s.1 s.2 2)) :
    Writes .total I τ rotateColumns.body (Env.frame [n, k] [a, c, s, a])
      (Store.inBlock a.1 a.2 (2 * (n * n)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a
        (H * (givens (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ cv sv)ᴴ) m'.store) m := by
  refine (rotateColumns_writes_word hS hk hH hc hs hca hsa).mono le_rfl
    fun _ _ ⟨hp, hm⟩ => ⟨hp, ?_⟩
  rwa [machineColRotation_eq hE (Fin.ne_of_val_ne (Nat.succ_ne_self k).symm)] at hm

end NLAlib.ShiftedQR
