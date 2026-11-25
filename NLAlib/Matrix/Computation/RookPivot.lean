/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.RookPivotStep

/-!
# Bounded stored rook selection

The actual search alternates active column and row scans. Only strict magnitude growth
continues; equal maxima finish immediately, preventing cycles caused by stable tie choices.
A stored completion guard makes remaining bounded iterations no-ops. Caller output cells
receive the two exact absolute indices only after search workspace has finished.

## Main definitions

* `NLAlib.Computation.rookPivotChoice`: bounded actual rook selection with two index outputs.

## Main results

* `NLAlib.Computation.exec_rookPivotChoice`: termination, mutual maxima and two output writes.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Initialize the zero/completion words and both absolute current coordinates of a rook
search in a caller-owned workspace. -/
def initializeRookPivot {P ι VB VI : Type} (tag : P) (scratch : VB) (k : IExp VI) :
    Builder P ι VB VI Unit := do
  ins (.lit tag ⟨scratch, 0⟩ 0)
  ins (.lit tag ⟨scratch, 1⟩ 0)
  ins (.litIdx tag ⟨scratch, 2⟩ k)
  ins (.litIdx tag ⟨scratch, 3⟩ k)

/-- Select a mutual active row and column maximum by alternating scans starting at column `k`.
Seven workspace words are scoped. The conservative `n²+1` bound is sufficient because every
continuation strictly increases the current column's maximum. Equal magnitudes stop, and
completed iterations change no stored word. The final two copies are the only caller writes. -/
def rookPivotChoice {P ι VB VI : Type} (tag : P) (n k : IExp VI)
    (A : VB) (off : IExp VI) (rowIndex colIndex : Cell VB VI) :
    Builder P ι VB VI Unit := scope do
  let scratch ← alloc tag 7
  initializeRookPivot tag scratch k
  forRange (n * n + 1) fun _ => rookPivotStep tag n k A off scratch
  ins (.copy tag rowIndex ⟨scratch, 2⟩)
  ins (.copy tag colIndex ⟨scratch, 3⟩)

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The rook selector releases all search and row-packing workspace before a following builder. -/
theorem executionComposable_rookPivotChoice (I : Interp P ι K C) (tag : P)
    (n k : IExp ℕ) (A : ℕ) (off : IExp ℕ) (rowIndex colIndex : Cell ℕ ℕ) :
    ExecutionComposable I (rookPivotChoice tag n k A off rowIndex colIndex) :=
  executionComposable_single I (fun _ => rfl)

namespace RookPivot

private structure State {N : ℕ} (base : Store P ℝ) (tag : P)
    (M : Matrix (Fin N) (Fin N) ℝ) (k : Fin N) (scratch t : ℕ) (s : Store P ℝ) : Prop where
  frame : Store.BlockFrame base tag scratch scratch 0 0 s (fun _ => none)
  zero : s.read tag scratch 0 = some 0
  values : ∃ r c : Fin N, k ≤ r ∧ k ≤ c ∧
    s.read tag scratch 2 = some (r.val : ℝ) ∧
    s.read tag scratch 3 = some (c.val : ℝ) ∧
    ((s.read tag scratch 1 = some 1 ∧
      (∀ i : Fin N, k ≤ i → |M i c| ≤ |M r c|) ∧
      (∀ j : Fin N, k ≤ j → |M r j| ≤ |M r c|)) ∨
    (s.read tag scratch 1 = some 0 ∧ ∃ visited : Finset (Fin N),
      visited.card = t ∧ ∀ j ∈ visited, rookColumnMagnitude M k j < rookColumnMagnitude M k c))

private theorem State.complete {N : ℕ} {base s : Store P ℝ} {tag : P}
    {M : Matrix (Fin N) (Fin N) ℝ} {k : Fin N} {scratch t : ℕ}
    (hs : State base tag M k scratch t s) (ht : N < t) :
    ∃ r c : Fin N, k ≤ r ∧ k ≤ c ∧
      s.read tag scratch 2 = some (r.val : ℝ) ∧
      s.read tag scratch 3 = some (c.val : ℝ) ∧
      (∀ i : Fin N, k ≤ i → |M i c| ≤ |M r c|) ∧
      (∀ j : Fin N, k ≤ j → |M r j| ≤ |M r c|) := by
  obtain ⟨r, c, hkr, hkc, hr, hc, hdone | hnot⟩ := hs.values
  · exact ⟨r, c, hkr, hkc, hr, hc, hdone.2⟩
  · obtain ⟨-, visited, hcard, -⟩ := hnot
    have hle := visited.card_le_univ
    simp only [Fintype.card_fin, hcard] at hle
    omega

private theorem exec_initialize (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch : ℕ) (n k : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hsh : st.store.shape[scratch]? = some (tag, 7)) :
    ∃ out, exec I (initializeRookPivot tag scratch k).run st = some out ∧
      State st.store tag M ⟨k.eval, hk⟩ scratch 0 out.store := by
  have hF : Store.BlockFrame st.store tag scratch scratch 0 0 st.store (fun _ => none) :=
    ⟨rfl, fun _ _ _ _ _ => rfl, by omega⟩
  obtain ⟨s₁, hw₁⟩ := hF.exists_write_eq_some (0 : ℝ) hsh (by omega : 0 < 7)
  have hF₁ := hF.write_scratch (by omega) hw₁
  obtain ⟨s₂, hw₂⟩ := hF₁.exists_write_eq_some (0 : ℝ) hsh (by omega : 1 < 7)
  have hF₂ := hF₁.write_scratch (by omega) hw₂
  obtain ⟨s₃, hw₃⟩ := hF₂.exists_write_eq_some (k.eval : ℝ) hsh (by omega : 2 < 7)
  have hF₃ := hF₂.write_scratch (by omega) hw₃
  obtain ⟨s₄, hw₄⟩ := hF₃.exists_write_eq_some (k.eval : ℝ) hsh (by omega : 3 < 7)
  let cnt₁ := st.cnt + I.charge (.lit tag)
  let cnt₂ := cnt₁ + I.charge (.lit tag)
  let cnt₃ := cnt₂ + I.charge (.lit tag)
  let cnt₄ := cnt₃ + I.charge (.lit tag)
  let out : St P ℝ C := { st with store := s₄, cnt := cnt₄ }
  refine ⟨out, ?_, hF₃.write_scratch (by omega) hw₄, ?_,
    ⟨k.eval, hk⟩, ⟨k.eval, hk⟩, le_rfl, le_rfl, ?_,
    Store.read_of_write_eq_some hw₄, Or.inr ⟨?_, ∅, by simp, by simp⟩⟩
  · change exec I (.seq (.instr (.lit tag ⟨scratch, 0⟩ 0))
      (.seq (.instr (.lit tag ⟨scratch, 1⟩ 0))
        (.seq (.instr (.litIdx tag ⟨scratch, 2⟩ k))
          (.seq (.instr (.litIdx tag ⟨scratch, 3⟩ k)) .skip)))) st = some out
    rw [exec_seq_instr_lit I (by simp [hI, exactSem]) hw₁,
      exec_seq_instr_lit I (by simp [hI, exactSem]) hw₂,
      exec_seq_instr_litIdx I (by simp [hI, exactSem]) hw₃,
      exec_seq_instr_litIdx I (by simp [hI, exactSem]) hw₄, exec_skip]
  · rw [Store.read_of_write_eq_some_of_ne hw₄ (Or.inr (by omega : 0 ≠ 3)),
      Store.read_of_write_eq_some_of_ne hw₃ (Or.inr (by omega : 0 ≠ 2)),
      Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by omega : 0 ≠ 1))]
    exact Store.read_of_write_eq_some hw₁
  · rw [Store.read_of_write_eq_some_of_ne hw₄ (Or.inr (by omega : 2 ≠ 3))]
    exact Store.read_of_write_eq_some hw₃
  · rw [Store.read_of_write_eq_some_of_ne hw₄ (Or.inr (by omega : 1 ≠ 3)),
      Store.read_of_write_eq_some_of_ne hw₃ (Or.inr (by omega : 1 ≠ 2))]
    exact Store.read_of_write_eq_some hw₂

private theorem state_after_search {N k : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (hk : k < N) (htail : N - k ≤ N) (base out : Store P ℝ) (tag : P) (scratch t : ℕ)
    (c : Fin N) (hkc : (⟨k, hk⟩ : Fin N) ≤ c) (visited : Finset (Fin N))
    (hcard : visited.card = t)
    (hv : ∀ j ∈ visited, rookColumnMagnitude M ⟨k, hk⟩ j < rookColumnMagnitude M ⟨k, hk⟩ c)
    (r d : Fin (N - k))
    (hf : Store.BlockFrame base tag scratch scratch 0 0 out (fun _ => none))
    (hz : out.read tag scratch 0 = some 0)
    (hr : out.read tag scratch 2 = some ((k + r.val : ℕ) : ℝ))
    (hc : out.read tag scratch 3 = some (if
      |M ((Fin.natAdd_castLEEmb (htail)) r) c| <
        |M ((Fin.natAdd_castLEEmb (htail)) r)
          ((Fin.natAdd_castLEEmb (htail)) d)|
      then ((k + d.val : ℕ) : ℝ) else c.val))
    (hd : out.read tag scratch 1 = some (if
      |M ((Fin.natAdd_castLEEmb (htail)) r) c| <
        |M ((Fin.natAdd_castLEEmb (htail)) r)
          ((Fin.natAdd_castLEEmb (htail)) d)| then (0 : ℝ) else 1))
    (hcm : ∀ i : Fin (N - k), |M ((Fin.natAdd_castLEEmb (htail)) i) c| ≤
      |M ((Fin.natAdd_castLEEmb (htail)) r) c|)
    (hrm : ∀ j : Fin (N - k),
      |M ((Fin.natAdd_castLEEmb (htail)) r)
        ((Fin.natAdd_castLEEmb (htail)) j)| ≤
      |M ((Fin.natAdd_castLEEmb (htail)) r)
        ((Fin.natAdd_castLEEmb (htail)) d)|) :
    State base tag M ⟨k, hk⟩ scratch (t + 1) out := by
  let r' := (Fin.natAdd_castLEEmb (htail)) r
  let d' := (Fin.natAdd_castLEEmb (htail)) d
  have hrval : r'.val = k + r.val := Fin.val_natAdd_castLEEmb_sub k (htail) r
  have hdval : d'.val = k + d.val := Fin.val_natAdd_castLEEmb_sub k (htail) d
  have hkr : (⟨k, hk⟩ : Fin N) ≤ r' := by change k ≤ r'.val; rw [hrval]; omega
  have hkd : (⟨k, hk⟩ : Fin N) ≤ d' := by change k ≤ d'.val; rw [hdval]; omega
  have hcolmax : ∀ i : Fin N, (⟨k, hk⟩ : Fin N) ≤ i → |M i c| ≤ |M r' c| := by
    intro i hi
    have hmem : i ∈ Set.range (Fin.natAdd_castLEEmb (htail)) := by
      rw [Fin.range_natAdd_castLEEmb]
      change N - (N - k) ≤ i.val
      rw [Nat.sub_sub_self hk.le]
      exact hi
    obtain ⟨j, rfl⟩ := hmem
    exact hcm j
  have hrowmax : ∀ j : Fin N, (⟨k, hk⟩ : Fin N) ≤ j → |M r' j| ≤ |M r' d'| := by
    intro j hj
    have hmem : j ∈ Set.range (Fin.natAdd_castLEEmb (htail)) := by
      rw [Fin.range_natAdd_castLEEmb]
      change N - (N - k) ≤ j.val
      rw [Nat.sub_sub_self hk.le]
      exact hj
    obtain ⟨i, rfl⟩ := hmem
    exact hrm i
  change out.read tag scratch 3 =
    some (if |M r' c| < |M r' d'| then ((k + d.val : ℕ) : ℝ) else c.val) at hc
  change out.read tag scratch 1 = some (if |M r' c| < |M r' d'| then (0 : ℝ) else 1) at hd
  refine ⟨hf, hz, ?_⟩
  by_cases hlt : |M r' c| < |M r' d'|
  · have hgt : rookColumnMagnitude M ⟨k, hk⟩ c < rookColumnMagnitude M ⟨k, hk⟩ d' :=
      rookColumnMagnitude_lt_of_lt M ⟨k, hk⟩ c r' d' hkr
        (by simpa only [Real.norm_eq_abs] using hcolmax)
        (by simpa only [Real.norm_eq_abs] using hlt)
    have hnot : c ∉ visited := fun hc => (lt_irrefl _ (hv c hc)).elim
    have hcard' := Finset.card_insert_of_notMem hnot
    have hv' : ∀ j ∈ insert c visited,
        rookColumnMagnitude M ⟨k, hk⟩ j < rookColumnMagnitude M ⟨k, hk⟩ d' := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hgt
      · exact (hv j hj).trans hgt
    refine ⟨r', d', hkr, hkd, ?_, ?_, Or.inr ⟨?_, insert c visited, ?_, hv'⟩⟩
    · simpa only [hrval] using hr
    · simpa only [hlt, ↓reduceIte, ← hdval] using hc
    · simpa only [hlt, ↓reduceIte] using hd
    · rw [hcard', hcard]
  · refine ⟨r', c, hkr, hkc, ?_, ?_, Or.inl ⟨?_, hcolmax, ?_⟩⟩
    · simpa only [hrval] using hr
    · simpa only [hlt, ↓reduceIte] using hc
    · simpa only [hlt, ↓reduceIte] using hd
    · intro j hj
      exact (hrowmax j hj).trans (le_of_not_gt hlt)

private theorem exec_notDone (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch A : ℕ) (n k off : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (c : Fin n.eval) (hkc : (⟨k.eval, hk⟩ : Fin n.eval) ≤ c)
    (hM : Holds st.store tag A off.eval M)
    (hz : st.store.read tag scratch 0 = some 0)
    (hd : st.store.read tag scratch 1 = some 0)
    (hc : st.store.read tag scratch 3 = some (c.val : ℝ))
    (hsh : st.store.shape[scratch]? = some (tag, 7)) (hAS : A ≠ scratch)
    {base : Store P ℝ} (hF : Store.BlockFrame base tag scratch scratch 0 0 st.store (fun _ => none))
    (visited : Finset (Fin n.eval)) (t : ℕ) (hcard : visited.card = t)
    (hv : ∀ j ∈ visited,
      rookColumnMagnitude M ⟨k.eval, hk⟩ j < rookColumnMagnitude M ⟨k.eval, hk⟩ c) :
    ∃ out, exec I (bindIdx tag ⟨scratch, 3⟩ n fun col =>
      rookPivotSearch tag n k A off scratch (.var col)).run st = some out ∧
      State base tag M ⟨k.eval, hk⟩ scratch (t + 1) out.store := by
  let ready : St P ℝ C := { st with cnt := st.cnt + I.charge (.toNat tag) }
  obtain ⟨out, r, d, he, hf, hz', hr', hc', hd', hcm, hrm⟩ := exec_search I hI tag ready
    scratch A n k off (.var c.val) M hk (Nat.sub_le _ _) c.isLt hM hz hd hc hsh hAS hF
  refine ⟨out, ?_, ?_⟩
  · change exec I (.seq (.bindIdx tag ⟨scratch, 3⟩ n _) .skip) st = _
    have hto : I.sem.toNat tag (c.val : ℝ) = some c.val := by simp [hI, exactSem]
    rw [exec_seq_skip, exec_bindIdx_of_read I hc hto
      c.isLt.le]
    exact he
  · exact state_after_search M hk (Nat.sub_le n.eval k.eval) base out.store tag scratch t c hkc
      visited hcard hv r d
      hf hz' hr' hc' hd' hcm hrm

private theorem exec_step (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (base : Store P ℝ) (scratch A : ℕ) (n k off : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : Holds base tag A off.eval M)
    (hsh : base.shape[scratch]? = some (tag, 7)) (hAS : A ≠ scratch)
    (t : ℕ) (st : St P ℝ C) (hs : State base tag M ⟨k.eval, hk⟩ scratch t st.store) :
    ∃ out, exec I (rookPivotStep tag n k A off scratch).run st = some out ∧
      State base tag M ⟨k.eval, hk⟩ scratch (t + 1) out.store := by
  let tested : St P ℝ C := { st with cnt := st.cnt + I.charge (.cmp tag) }
  have hrun : (rookPivotStep tag n k A off scratch : Builder P ι ℕ ℕ Unit).run =
      .seq (.ite tag .eq ⟨scratch, 1⟩ ⟨scratch, 0⟩
        (bindIdx tag ⟨scratch, 3⟩ n fun c => rookPivotSearch tag n k A off scratch (.var c)).run
        .skip) .skip := rfl
  obtain ⟨r, c, hkr, hkc, hr, hc, hdone | hnot⟩ := hs.values
  · have hcmp : cmpStep I tag .eq ⟨scratch, 1⟩ ⟨scratch, 0⟩ st = some (false, tested) := by
      simp [cmpStep, IExp.eval, hdone.1, hs.zero, hI, exactSem, tested]
    refine ⟨tested, ?_, hs.frame, hs.zero, r, c, hkr, hkc, hr, hc, Or.inl hdone⟩
    simp only [hrun, exec_seq_skip, exec_ite, hcmp, Option.bind_some, Bool.false_eq_true,
      ↓reduceIte, exec_skip]
  · obtain ⟨hd, visited, hcard, hv⟩ := hnot
    have hcmp : cmpStep I tag .eq ⟨scratch, 1⟩ ⟨scratch, 0⟩ st = some (true, tested) := by
      simp [cmpStep, IExp.eval, hd, hs.zero, hI, exactSem, tested]
    have hMst : Holds st.store tag A off.eval M := by
      intro i j
      rw [hs.frame.read_of_ne hAS (by omega)]
      exact hM i j
    obtain ⟨out, he, hs'⟩ := exec_notDone I hI tag tested scratch A n k off M hk c hkc
      hMst hs.zero hd hc (hs.frame.1.symm ▸ hsh) hAS hs.frame visited t hcard hv
    refine ⟨out, ?_, hs'⟩
    simp only [hrun, exec_seq_skip, exec_ite, hcmp, Option.bind_some, ↓reduceIte]
    exact he

private theorem exec_outputs (I : Interp P ι ℝ C) (tag : P)
    (initial : Store P ℝ) (st : St P ℝ C) (rowIndex colIndex : Cell ℕ ℕ)
    (r c : ℝ)
    (hF : Store.BlockFrame (initial.push (tag, Array.replicate 7 none)) tag
      initial.size initial.size 0 0 st.store (fun _ => none))
    (hr : st.store.read tag initial.size 2 = some r)
    (hc : st.store.read tag initial.size 3 = some c)
    (hwR : Writable initial tag rowIndex.buf rowIndex.idx.eval 1)
    (hwC : Writable initial tag colIndex.buf colIndex.idx.eval 1) :
    ∃ (out : St P ℝ C) (mid : Store P ℝ), exec I (do
      ins (.copy tag rowIndex ⟨initial.size, 2⟩)
      ins (.copy tag colIndex ⟨initial.size, 3⟩)).run st = some out ∧
      initial.writeBlock tag rowIndex.buf rowIndex.idx.eval #[r] = some mid ∧
      mid.writeBlock tag colIndex.buf colIndex.idx.eval #[c] = some out.store.pop := by
  have hpop : st.store.pop = initial := hF.pop_eq (Y := (#[] : Array ℝ))
    (by simp [Store.writeBlock])
    (by simp) (by omega)
  have hR := hwR.lt_size (by omega : 0 < 1)
  have hC := hwC.lt_size (by omega : 0 < 1)
  obtain ⟨lenR, hlenR, hltR⟩ := hwR 0 (by omega)
  obtain ⟨lenC, hlenC, hltC⟩ := hwC 0 (by omega)
  have hlenR' : st.store.shape[rowIndex.buf]? = some (tag, lenR) := by
    rw [hF.1, Store.getElem?_shape_push_of_lt _ hR]; exact hlenR
  have hlenC' : st.store.shape[colIndex.buf]? = some (tag, lenC) := by
    rw [hF.1, Store.getElem?_shape_push_of_lt _ hC]; exact hlenC
  obtain ⟨s₁, hs₁, he₁, hsh₁, -, -⟩ := exec_scalar_copy I tag st rowIndex
    ⟨initial.size, 2⟩ r hr ⟨lenR, hlenR', by simpa using hltR⟩
  let first : St P ℝ C := { st with store := s₁, cnt := st.cnt + I.charge (.copy tag) }
  obtain ⟨s₂, hs₂, he₂, -, -, -⟩ := exec_scalar_copy I tag first colIndex
    ⟨initial.size, 3⟩ c
    (by rw [Store.read_of_write_eq_some_of_ne hs₁
      (Or.inl (by change initial.size ≠ rowIndex.buf; omega))]; exact hc)
    ⟨lenC, hsh₁.symm ▸ hlenC', by simpa using hltC⟩
  have hsize : st.store.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using congrArg Array.size hF.1
  have hs₁b : st.store.writeBlock tag rowIndex.buf rowIndex.idx.eval #[r] = some s₁ := by
    simpa [Store.writeBlock, List.range_succ] using hs₁
  have hs₂b : s₁.writeBlock tag colIndex.buf colIndex.idx.eval #[c] = some s₂ := by
    simpa [Store.writeBlock, List.range_succ] using hs₂
  have hp₁ := Store.writeBlock_pop_of_lt hs₁b (by omega)
  rw [hpop] at hp₁
  have hp₂ := Store.writeBlock_pop_of_lt hs₂b (by
    rw [Store.size_of_write_eq_some hs₁]; omega)
  refine ⟨{ first with store := s₂, cnt := first.cnt + I.charge (.copy tag) },
    s₁.pop, ?_, hp₁, hp₂⟩
  rw [exec_run_bind I (b := ins (.copy tag rowIndex ⟨initial.size, 2⟩))
    (fun _ => rfl), he₁, Option.bind_some]
  exact he₂

private def Result {N : ℕ} (tag : P) (initial : Store P ℝ)
    (M : Matrix (Fin N) (Fin N) ℝ) (k : Fin N) (rowIndex colIndex : Cell ℕ ℕ)
    (final : Store P ℝ) : Prop :=
  ∃ (r c : Fin N) (mid : Store P ℝ),
    initial.writeBlock tag rowIndex.buf rowIndex.idx.eval #[(r.val : ℝ)] = some mid ∧
    mid.writeBlock tag colIndex.buf colIndex.idx.eval #[(c.val : ℝ)] = some final ∧
    k ≤ r ∧ k ≤ c ∧ (∀ i : Fin N, k ≤ i → |M i c| ≤ |M r c|) ∧
    (∀ j : Fin N, k ≤ j → |M r j| ≤ |M r c|)

private theorem composable_initialize (I : Interp P ι ℝ C) (tag : P)
    (scratch : ℕ) (k : IExp ℕ) : ExecutionComposable I (initializeRookPivot tag scratch k) := by
  intro f st
  change exec I (.seq (.instr (.lit tag ⟨scratch, 0⟩ 0))
    (.seq (.instr (.lit tag ⟨scratch, 1⟩ 0))
      (.seq (.instr (.litIdx tag ⟨scratch, 2⟩ k))
        (.seq (.instr (.litIdx tag ⟨scratch, 3⟩ k)) (f ()).run)))) st =
    (exec I (.seq (.instr (.lit tag ⟨scratch, 0⟩ 0))
      (.seq (.instr (.lit tag ⟨scratch, 1⟩ 0))
        (.seq (.instr (.litIdx tag ⟨scratch, 2⟩ k))
          (.seq (.instr (.litIdx tag ⟨scratch, 3⟩ k)) .skip)))) st).bind
      (fun s => exec I (f ()).run s)
  simp only [exec_seq, exec_skip, Option.bind_assoc, Option.bind_some]

private theorem exec_body (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st σ : St P ℝ C) (n k : IExp ℕ) (A : ℕ) (off : IExp ℕ)
    (rowIndex colIndex : Cell ℕ ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hM : Holds st.store tag A off.eval M)
    (hwR : Writable st.store tag rowIndex.buf rowIndex.idx.eval 1)
    (hwC : Writable st.store tag colIndex.buf colIndex.idx.eval 1)
    (hσ : σ.store = st.store.push (tag, Array.replicate 7 none)) :
    ∃ out, exec I (do
      initializeRookPivot tag st.store.size k
      forRange (n * n + 1) fun _ => rookPivotStep tag n k A off st.store.size
      ins (.copy tag rowIndex ⟨st.store.size, 2⟩)
      ins (.copy tag colIndex ⟨st.store.size, 3⟩)).run σ = some out ∧
      Result tag st.store M ⟨k.eval, hk⟩ rowIndex colIndex out.store.pop := by
  have hA := Store.lt_size_of_read_eq_some (hM ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)
  have hMσ : Holds σ.store tag A off.eval M := by
    intro i j
    rw [hσ, Store.read_push_of_lt hA]
    exact hM i j
  have hsh : σ.store.shape[st.store.size]? = some (tag, 7) := by
    rw [hσ]; exact Store.getElem?_shape_push_size _ _ _
  obtain ⟨mid, he₁, hs₁⟩ := exec_initialize I hI tag σ st.store.size n k M hk hsh
  obtain ⟨searched, he₂, hs₂⟩ := exists_exec_loop_eq_some_of_forall I (n := n * n + 1)
    (fun t s => State σ.store tag M ⟨k.eval, hk⟩ st.store.size t s.store) hs₁
    (fun t _ s hs => exec_step I hI tag σ.store st.store.size A n k off M hk hMσ hsh
      (Nat.ne_of_lt hA) t s hs)
  have hbound : n.eval < (n * n + 1).eval := by
    change n.eval < n.eval * n.eval + 1
    nlinarith
  obtain ⟨r, c, hkr, hkc, hr, hc, hcm, hrm⟩ := hs₂.complete hbound
  obtain ⟨out, written, he₃, hw₁, hw₂⟩ := exec_outputs I tag st.store searched
    rowIndex colIndex (r.val : ℝ) (c.val : ℝ) (hσ ▸ hs₂.frame) hr hc hwR hwC
  refine ⟨out, ?_, r, c, written, hw₁, hw₂, hkr, hkc, hcm, hrm⟩
  rw [composable_initialize I tag st.store.size k, he₁, Option.bind_some]
  rw [exec_run_bind I (b := forRange (n * n + 1) fun _ =>
    rookPivotStep tag n k A off st.store.size) (fun _ => rfl)]
  have he₂' : exec I (forRange (n * n + 1) fun _ =>
      rookPivotStep tag n k A off st.store.size).run mid = some searched := by
    change exec I (.seq (.loop (n * n + 1) _) .skip) mid = _
    rw [exec_seq_skip]
    exact he₂
  rw [he₂', Option.bind_some]
  exact he₃

end RookPivot

/-- The actual bounded rook search succeeds on every nonempty active square. Its exact
absolute indices are mutual active column and row maxima. Strict magnitude growth proves
termination within the fixed bound, including tied and zero matrices. The only net effects
are two singleton writes; the source is retained. A zero rook pivot clears its selected active
row and column, without claiming that the entire remaining square is zero. -/
theorem exec_rookPivotChoice (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (n k : IExp ℕ) (A : ℕ) (off : IExp ℕ)
    (rowIndex colIndex : Cell ℕ ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hM : Holds st.store tag A off.eval M)
    (hwR : Writable st.store tag rowIndex.buf rowIndex.idx.eval 1)
    (hwC : Writable st.store tag colIndex.buf colIndex.idx.eval 1)
    (hAR : A ≠ rowIndex.buf) (hAC : A ≠ colIndex.buf)
    (hRC : rowIndex.buf ≠ colIndex.buf ∨ rowIndex.idx.eval ≠ colIndex.idx.eval) :
    ∃ (out : St P ℝ C) (r c : Fin n.eval) (mid : Store P ℝ),
      exec I (rookPivotChoice tag n k A off rowIndex colIndex).run st = some out ∧
      st.store.writeBlock tag rowIndex.buf rowIndex.idx.eval #[(r.val : ℝ)] = some mid ∧
      mid.writeBlock tag colIndex.buf colIndex.idx.eval #[(c.val : ℝ)] = some out.store ∧
      k.eval ≤ r.val ∧ k.eval ≤ c.val ∧ Holds out.store tag A off.eval M ∧
      out.store.read tag rowIndex.buf rowIndex.idx.eval = some (r.val : ℝ) ∧
      out.store.read tag colIndex.buf colIndex.idx.eval = some (c.val : ℝ) ∧
      (∀ i : Fin n.eval, k.eval ≤ i.val → |M i c| ≤ |M r c|) ∧
      (∀ j : Fin n.eval, k.eval ≤ j.val → |M r j| ≤ |M r c|) ∧
      (M r c = 0 → (∀ i : Fin n.eval, k.eval ≤ i.val → M i c = 0) ∧
        (∀ j : Fin n.eval, k.eval ≤ j.val → M r j = 0)) ∧
      (∀ i : Fin n.eval, k.eval ≤ i.val → |M i c / M r c| ≤ 1) := by
  let Q := RookPivot.Result tag st.store M ⟨k.eval, hk⟩ rowIndex colIndex
  obtain ⟨out, he, r, c, written, hw₁, hw₂, hkr, hkc, hcm, hrm⟩ := exists_exec_alloc I tag 7
    (fun scratch => ((do
      initializeRookPivot tag scratch k
      forRange (n * n + 1) fun _ => rookPivotStep tag n k A off scratch
      ins (.copy tag rowIndex ⟨scratch, 2⟩)
      ins (.copy tag colIndex ⟨scratch, 3⟩)) : Builder P ι ℕ ℕ Unit).run) st Q
    (fun σ hσ => RookPivot.exec_body I hI tag st σ n k A off rowIndex colIndex M hk hM
      hwR hwC hσ)
  refine ⟨out, r, c, written, ?_, hw₁, hw₂, hkr, hkc, ?_, ?_, ?_, hcm, hrm, ?_, ?_⟩
  · change exec I (.seq (.alloc tag 7 _) .skip) st = some out
    rw [exec_seq_skip]; exact he
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hAC),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hAR)]
    exact hM i j
  · rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (by
      rcases hRC with hb | hi
      · exact Or.inl hb
      · right; simp only [Array.size_singleton]; omega)]
    simpa using Store.read_of_writeBlock_eq_some_of_lt hw₁ (by simp : 0 < #[(r.val : ℝ)].size)
  · simpa using Store.read_of_writeBlock_eq_some_of_lt hw₂ (by simp : 0 < #[(c.val : ℝ)].size)
  · intro hz
    constructor
    · intro i hi
      exact abs_eq_zero.mp (le_antisymm (by simpa only [hz, abs_zero] using hcm i hi)
        (abs_nonneg _))
    · intro j hj
      exact abs_eq_zero.mp (le_antisymm (by simpa only [hz, abs_zero] using hrm j hj)
        (abs_nonneg _))
  · intro i hi
    by_cases hp : M r c = 0
    · simp only [hp, div_zero, abs_zero, zero_le_one]
    · rw [abs_div]
      exact (div_le_one (abs_pos.mpr hp)).mpr (hcm i hi)

end NLAlib.Computation
