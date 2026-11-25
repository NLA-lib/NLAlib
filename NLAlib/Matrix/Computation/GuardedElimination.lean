/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.LU
public import NLAlib.Computation.MatrixStorage
public import NLAlib.Computation.StridedWrites

/-!
# Elimination steps with zero pivot guards

A zero pivot is handled by actual stored comparisons. The Schur update skips it, matching
field inversion at zero in the total mathematical elimination step. Factor materialization
uses zero multipliers and a unit lower diagonal in that branch, without division.

## Main definitions

* `NLAlib.Computation.zeroUpperRow`, `NLAlib.Computation.zeroLowerColumn`:
  the shared division-free zero-pivot operations.
* `NLAlib.Computation.luColumnZero`: their scoped combined branch.

## Main results

* `NLAlib.Computation.exec_schurStepTotal`: exact successful Schur elimination for every matrix.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Eliminate a stored diagonal pivot when nonzero; skip it when zero. A scoped literal zero
makes the test an actual scalar comparison. This realizes the total elimination convention
in which inversion at zero is zero. [GolubVanLoan2013, §3.2]. -/
def schurStepTotal {P ι VB VI : Type} (p : P) (n : IExp VI) (R : VB)
    (off k : IExp VI) : Builder P ι VB VI Unit := scope do
  let zbuf ← alloc p 1
  ins (.lit p ⟨zbuf, 0⟩ 0)
  ifThenElse p .eq ⟨R, off + k + n * k⟩ ⟨zbuf, 0⟩ (pure ())
    (schurStep p n R off k)

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The zero-guarded Schur step releases its test word before its continuation. -/
theorem executionComposable_schurStepTotal (I : Interp P ι K C) (p : P)
    (n : IExp ℕ) (R : ℕ) (off k : IExp ℕ) :
    ExecutionComposable I (schurStepTotal p n R off k) :=
  executionComposable_single I (fun _ => rfl)

/-- Materialize the pivot row of the upper factor from a packed square residual: write zero
before the diagonal, then copy its diagonal and remaining row entries. This is the upper-row
operation used by zero-pivot factor materialization; it performs no division. -/
def zeroUpperRow {P ι VB VI : Type} (p : P) (n k : IExp VI) (S U : VB)
    (so uo : IExp VI) : Builder P ι VB VI Unit := scope do
  forRange k fun j => ins (.lit p ⟨U, uo + k + n * .var j⟩ 0)
  forRange (n - k) fun j => ins (.copy p ⟨U, uo + k + n * (k + .var j)⟩
    ⟨S, so + k + n * (k + .var j)⟩)

private def pivotRowValue {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (r : Fin N) (j : ℕ) : ℝ := if hj : j < N then M r ⟨j, hj⟩ else 0

private theorem exec_zeroUpperRow_parts (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (p : P) (st : St P ℝ C) (n k : IExp ℕ) (S U : ℕ) (so uo : IExp ℕ)
    (M D : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : Holds st.store p S so.eval M) (hD : Holds st.store p U uo.eval D) (hSU : S ≠ U) :
    ∃ (mid out : St P ℝ C),
      exec I (zeroUpperRow p n k S U so uo).run st = some out ∧
      mid.store.shape = st.store.shape ∧ out.store.shape = mid.store.shape ∧
      (∀ j < k.eval, mid.store.read p U (uo.eval + k.eval + n.eval * j) = some 0) ∧
      (∀ j < n.eval - k.eval, out.store.read p U
        (uo.eval + k.eval + n.eval * k.eval + n.eval * j) =
          some (pivotRowValue M ⟨k.eval, hk⟩ (k.eval + j))) ∧
      (∀ q b idx, (b ≠ U ∨ ∀ j < k.eval, idx ≠ uo.eval + k.eval + n.eval * j) →
        mid.store.read q b idx = st.store.read q b idx) ∧
      (∀ q b idx, (b ≠ U ∨ ∀ j < n.eval - k.eval,
        idx ≠ uo.eval + k.eval + n.eval * k.eval + n.eval * j) →
        out.store.read q b idx = mid.store.read q b idx) := by
  have hcapacity : ∀ σ : St P ℝ C, σ.store.shape = st.store.shape → ∀ j < n.eval,
      ∃ len, σ.store.shape[U]? = some (p, len) ∧ uo.eval + k.eval + n.eval * j < len := by
    intro σ hs j hj
    obtain ⟨len, hlen, hlt⟩ := hD.writable (k.eval + n.eval * j)
      (Nat.add_mul_lt_mul_of_lt_of_lt hk hj)
    exact ⟨len, hs ▸ hlen, by simpa only [Nat.add_assoc] using hlt⟩
  obtain ⟨mid, hr₁, hsh₁, hread₁, hframe₁⟩ := exec_strided_writes I p st k U
    (uo.eval + k.eval) n.eval (by omega) (fun _ => 0)
    (fun j => ins (.lit p ⟨U, uo + k + n * .var j⟩ 0)) (by
      intro j hj σ hs _
      obtain ⟨store, hw, hr, _⟩ := exec_scalar_lit I p σ ⟨U, uo + k + n * .var j⟩ 0 0
        (by rw [hI]; simp only [exactSem, Rat.cast_zero])
        (by simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_var] using
          hcapacity σ hs j (hj.trans hk))
      exact ⟨_, hr, by simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_var] using hw⟩)
  have hM' : Holds mid.store p S so.eval M := fun i j =>
    (hframe₁ p S _ (Or.inl hSU)).trans (hM i j)
  obtain ⟨out, hr₂, hsh₂, hread₂, hframe₂⟩ := exec_strided_writes I p mid (n - k) U
    (uo.eval + k.eval + n.eval * k.eval) n.eval (by omega)
    (fun j => pivotRowValue M ⟨k.eval, hk⟩ (k.eval + j))
    (fun j => ins (.copy p ⟨U, uo + k + n * (k + .var j)⟩
      ⟨S, so + k + n * (k + .var j)⟩)) (by
      intro j hj σ hs hf
      have hj' : k.eval + j < n.eval := by change j < n.eval - k.eval at hj; omega
      have hsrc : σ.store.read p S (so + k + n * (k + .var j)).eval =
          some (pivotRowValue M ⟨k.eval, hk⟩ (k.eval + j)) := by
        rw [hf p S _ hSU]
        simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_var, pivotRowValue,
          dif_pos hj'] using hM' ⟨k.eval, hk⟩ ⟨k.eval + j, hj'⟩
      obtain ⟨store, hw, hr, _⟩ := exec_scalar_copy I p σ
        ⟨U, uo + k + n * (k + .var j)⟩ ⟨S, so + k + n * (k + .var j)⟩ _ hsrc
        (by simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_var] using
          hcapacity σ (hs.trans hsh₁) (k.eval + j) hj')
      exact ⟨_, hr, by simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_var,
        Nat.mul_add, Nat.add_assoc] using hw⟩)
  refine ⟨mid, out, ?_, hsh₁, hsh₂, hread₁, hread₂, hframe₁, hframe₂⟩
  change exec I (.seq _ .skip) st = some out
  rw [exec_seq_skip, exec_run_bind I (b := forRange k fun j =>
    ins (.lit p ⟨U, uo + k + n * .var j⟩ 0)) (fun _ => rfl)]
  have hr₁' : exec I (forRange k fun j => ins (.lit p ⟨U, uo + k + n * .var j⟩ 0)).run st =
      some mid := by rw [show (forRange k _).run = .seq (.loop k _) .skip from rfl,
      exec_seq_skip]; exact hr₁
  rw [hr₁', Option.bind_some]
  change exec I (.seq (.loop (n - k) _) .skip) mid = some out
  rw [exec_seq_skip]
  exact hr₂

private theorem holds_zeroUpperRow {N k U off : ℕ} (hk : k < N)
    (M D : Matrix (Fin N) (Fin N) ℝ) {s mid out : Store P ℝ} {p : P}
    (hD : Holds s p U off D)
    (hread₁ : ∀ j < k, mid.read p U (off + k + N * j) = some 0)
    (hread₂ : ∀ j < N - k, out.read p U (off + k + N * k + N * j) =
      some (pivotRowValue M ⟨k, hk⟩ (k + j)))
    (hframe₁ : ∀ q b idx, (b ≠ U ∨ ∀ j < k, idx ≠ off + k + N * j) →
      mid.read q b idx = s.read q b idx)
    (hframe₂ : ∀ q b idx, (b ≠ U ∨ ∀ j < N - k, idx ≠ off + k + N * k + N * j) →
      out.read q b idx = mid.read q b idx) :
    Holds out p U off (D.updateRow ⟨k, hk⟩ (fun j => if j.val < k then 0 else M ⟨k, hk⟩ j)) := by
  intro i j
  by_cases hir : i = ⟨k, hk⟩
  · subst i
    rw [Matrix.updateRow_self]
    by_cases hj : j.val < k
    · rw [if_pos hj, hframe₂ p U _ (Or.inr ?_)]
      · exact hread₁ j hj
      · intro t ht he
        have hflat : k + N * j.val = k + N * (k + t) :=
          Nat.add_left_cancel (by simpa only [Nat.mul_add, Nat.add_assoc] using he)
        have he' := (Nat.add_mul_eq_add_mul_iff_of_lt hk hk).mp hflat
        omega
    · rw [if_neg hj]
      have ht : j.val - k < N - k := by have := j.isLt; omega
      have hsum : k + (j.val - k) = j.val := Nat.add_sub_of_le (Nat.le_of_not_gt hj)
      simpa only [Nat.add_assoc, ← Nat.mul_add, hsum, pivotRowValue, dif_pos j.isLt] using
        hread₂ (j.val - k) ht
  · rw [Matrix.updateRow_ne hir, hframe₂ p U _ (Or.inr ?_),
      hframe₁ p U _ (Or.inr ?_), hD i j]
    · intro t ht he
      have hflat : i.val + N * j.val = k + N * t :=
        Nat.add_left_cancel (by simpa only [Nat.add_assoc] using he)
      exact hir (Fin.ext ((Nat.add_mul_eq_add_mul_iff_of_lt i.isLt hk).mp hflat).1)
    · intro t ht he
      apply hir
      have hflat : i.val + N * j.val = k + N * (k + t) :=
        Nat.add_left_cancel (by simpa only [Nat.mul_add, Nat.add_assoc] using he)
      exact Fin.ext ((Nat.add_mul_eq_add_mul_iff_of_lt i.isLt hk).mp hflat).1

private theorem exec_zeroUpperRow (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (p : P) (st : St P ℝ C) (n k : IExp ℕ) (S U : ℕ) (so uo : IExp ℕ)
    (M D : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : Holds st.store p S so.eval M) (hD : Holds st.store p U uo.eval D) (hSU : S ≠ U) :
    let D' := D.updateRow ⟨k.eval, hk⟩
      (fun j => if j.val < k.eval then 0 else M ⟨k.eval, hk⟩ j)
    ∃ out, exec I (zeroUpperRow p n k S U so uo).run st = some out ∧
      st.store.writeBlock p U uo.eval (flatten D') = some out.store ∧
      Holds out.store p U uo.eval D' := by
  dsimp only
  obtain ⟨mid, out, hr, hshape₁, hshape₂, hread₁, hread₂, hframe₁, hframe₂⟩ :=
    exec_zeroUpperRow_parts I hI p st n k S U so uo M D hk hM hD hSU
  have hfinal := holds_zeroUpperRow hk M D hD hread₁ hread₂ hframe₁ hframe₂
  have hbound : ∀ t < n.eval, uo.eval + k.eval + n.eval * t <
      uo.eval + n.eval * n.eval := fun t ht => by
    have hh := Nat.add_mul_lt_mul_of_lt_of_lt hk ht
    omega
  refine ⟨out, hr, ?_, hfinal⟩
  apply Store.writeBlock_eq_some_of_read (hshape₂.trans hshape₁)
  · intro t ht
    exact hfinal.read_flatten t (by simpa only [size_flatten] using ht)
  · intro q b idx hout
    simp only [size_flatten] at hout
    rw [hframe₂ q b idx (hout.imp_right (fun hi t ht => by
      have hb := hbound (k.eval + t) (by omega)
      simp only [Nat.mul_add] at hb
      omega))]
    exact hframe₁ q b idx (hout.imp_right (fun hi t ht => by
      have hb := hbound t (ht.trans hk)
      omega))

/-- Materialize the lower factor's column for a zero pivot: zero the packed column, then
write its diagonal literal one. The emitted instructions perform no division. -/
def zeroLowerColumn {P ι VB VI : Type} (p : P) (n k : IExp VI) (L : VB)
    (lo : IExp VI) : Builder P ι VB VI Unit := scope do
  forRange n fun i => ins (.lit p ⟨L, lo + n * k + .var i⟩ 0)
  ins (.lit p ⟨L, lo + k + n * k⟩ 1)

private theorem holds_zeroColumn {N k L off : ℕ} (hk : k < N)
    (B : Matrix (Fin N) (Fin N) ℝ) {s s' : Store P ℝ} {p : P}
    (hB : Holds s p L off B)
    (hread : ∀ i < N, s'.read p L (off + N * k + i) = some 0)
    (hframe : ∀ q b idx, (q ≠ p ∨ b ≠ L ∨ idx < off + N * k ∨
      off + N * k + N ≤ idx) → s'.read q b idx = s.read q b idx) :
    Holds s' p L off (B.updateCol ⟨k, hk⟩ (fun _ => 0)) := by
  intro i j
  by_cases hj : j = ⟨k, hk⟩
  · subst j
    simpa only [Matrix.updateCol_self, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hread i i.isLt
  · rw [Matrix.updateCol_ne hj, hframe p L _ (Or.inr (Or.inr ?_)), hB i j]
    have hj' : j.val ≠ k := fun he => hj (Fin.ext he)
    rcases lt_or_gt_of_ne hj' with hlt | hgt
    · have hh := Nat.add_mul_lt_mul_of_lt_of_lt i.isLt hlt
      exact Or.inl (by omega)
    · have hh := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hgt)
      right
      nlinarith

private theorem holds_oneColumn {N k L off : ℕ} (hk : k < N)
    (B : Matrix (Fin N) (Fin N) ℝ) {s s' : Store P ℝ} {p : P}
    (hB : Holds s p L off (B.updateCol ⟨k, hk⟩ (fun _ => 0)))
    (hw : s.write p L (off + k + N * k) 1 = some s') :
    Holds s' p L off (B.updateCol ⟨k, hk⟩ (fun i => if i = ⟨k, hk⟩ then 1 else 0)) := by
  intro i j
  by_cases hi : i = ⟨k, hk⟩
  · subst i
    by_cases hj : j = ⟨k, hk⟩
    · subst j
      simpa only [Matrix.updateCol_self, if_pos rfl, if_true] using Store.read_of_write_eq_some hw
    · rw [Matrix.updateCol_ne hj, Store.read_of_write_eq_some_of_ne hw (Or.inr ?_)]
      · simpa only [Matrix.updateCol_ne hj] using hB ⟨k, hk⟩ j
      · intro he
        have hflat : k + N * j.val = k + N * k :=
          Nat.add_left_cancel (by simpa only [Nat.add_assoc] using he)
        exact hj (Fin.ext ((Nat.add_mul_eq_add_mul_iff_of_lt hk hk).mp hflat).2)
  · rw [Store.read_of_write_eq_some_of_ne hw (Or.inr ?_)]
    · by_cases hj : j = ⟨k, hk⟩
      · subst j
        simpa only [Matrix.updateCol_self, if_neg hi] using hB i ⟨k, hk⟩
      · simpa only [Matrix.updateCol_ne hj] using hB i j
    · intro he
      have hflat : i.val + N * j.val = k + N * k :=
        Nat.add_left_cancel (by simpa only [Nat.add_assoc] using he)
      exact hi (Fin.ext ((Nat.add_mul_eq_add_mul_iff_of_lt i.isLt hk).mp hflat).1)

private theorem exec_zeroLowerColumn (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (p : P) (st : St P ℝ C) (n k : IExp ℕ) (L : ℕ) (lo : IExp ℕ)
    (B : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hB : Holds st.store p L lo.eval B) :
    let B' := B.updateCol ⟨k.eval, hk⟩ (fun i => if i = ⟨k.eval, hk⟩ then 1 else 0)
    ∃ out, exec I (zeroLowerColumn p n k L lo).run st = some out ∧
      st.store.writeBlock p L lo.eval (flatten B') = some out.store ∧
      Holds out.store p L lo.eval B' := by
  dsimp only
  have hcol : Writable st.store p L (lo + n * k).eval n.eval := by
    intro i hi
    obtain ⟨len, hlen, hlt⟩ := hB.writable (i + n.eval * k.eval)
      (Nat.add_mul_lt_mul_of_lt_of_lt hi hk)
    exact ⟨len, hlen, by simpa only [IExp.eval_add, IExp.eval_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hlt⟩
  obtain ⟨s₀, hr₁, hshape, hread, hframe⟩ := exec_forRange_zero I hI p st n L (lo + n * k) hcol
  have hB₀ := holds_zeroColumn hk B hB hread hframe
  let mid : St P ℝ C := { st with store := s₀, cnt := st.cnt + n.eval • I.charge (.lit p) }
  obtain ⟨len, hlen, hlt⟩ := hB.writable (k.eval + n.eval * k.eval)
    (Nat.add_mul_lt_mul_of_lt_of_lt hk hk)
  obtain ⟨s₁, hw, hr₂, hs, _⟩ := exec_scalar_lit I p mid ⟨L, lo + k + n * k⟩ 1 1
    (by rw [hI]; simp only [exactSem, Rat.cast_one])
    ⟨len, hshape ▸ hlen, by simpa only [IExp.eval_add, IExp.eval_mul, Nat.add_assoc] using hlt⟩
  have hB₁ := holds_oneColumn hk B hB₀ hw
  let out : St P ℝ C := { mid with store := s₁, cnt := mid.cnt + I.charge (.lit p) }
  refine ⟨out, ?_, ?_, hB₁⟩
  · change exec I (.seq _ .skip) st = _
    rw [exec_seq_skip, exec_run_bind I (b := forRange n fun i =>
      ins (.lit p ⟨L, lo + n * k + .var i⟩ 0)) (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂
  · apply Store.writeBlock_eq_some_of_read (hs.trans hshape)
    · intro t ht
      exact hB₁.read_flatten t (by simpa only [size_flatten] using ht)
    · intro q b idx hout
      simp only [size_flatten] at hout
      have hend := Nat.mul_le_mul_left n.eval (Nat.succ_le_of_lt hk)
      have hpiv := Nat.add_mul_lt_mul_of_lt_of_lt hk hk
      have hend' : n.eval * k.eval + n.eval ≤ n.eval * n.eval := by nlinarith
      rw [Store.read_of_write_eq_some_of_ne hw (by
        change b ≠ L ∨ idx ≠ lo.eval + k.eval + n.eval * k.eval
        omega)]
      exact hframe q b idx (Or.inr (by simp only [IExp.eval_add, IExp.eval_mul]; omega))

/-- Materialize a zero-pivot lower column and upper row, releasing both inner scopes before
returning. This branch writes zero multipliers and a unit lower diagonal, and copies the
upper pivot row with its left prefix cleared. It performs no division or pivot test; the
caller selects it after testing the stored pivot. [GolubVanLoan2013, §3.2]. -/
def luColumnZero {P ι VB VI : Type} (p : P) (n k : IExp VI) (S L U : VB)
    (so lo uo : IExp VI) : Builder P ι VB VI Unit := scope do
  zeroLowerColumn p n k L lo
  zeroUpperRow p n k S U so uo

/-- Materialize one LU column and row with an actual zero-pivot guard. A zero pivot writes
zero lower multipliers and a unit diagonal without division, and copies the upper row with
its left prefix cleared. Nonzero pivots call the original LU column routine. Both factor
blocks must be initialized and separate from the residual and each other.
[GolubVanLoan2013, §3.2]. -/
def luColumnTotal {P ι VB VI : Type} (p : P) (n k : IExp VI) (S L U : VB)
    (so lo uo : IExp VI) : Builder P ι VB VI Unit := scope do
  let zbuf ← alloc p 1
  ins (.lit p ⟨zbuf, 0⟩ 0)
  ifThenElse p .eq ⟨S, so + k + n * k⟩ ⟨zbuf, 0⟩
    (luColumnZero p n k S L U so lo uo)
    (luColumn p n k S L U so lo uo)

/-- The zero-guarded LU column releases its test word before its continuation. -/
theorem executionComposable_luColumnTotal (I : Interp P ι K C) (p : P)
    (n k : IExp ℕ) (S L U : ℕ) (so lo uo : IExp ℕ) :
    ExecutionComposable I (luColumnTotal p n k S L U so lo uo) :=
  executionComposable_single I (fun _ => rfl)

private theorem exec_luColumnZero (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (p : P) (st : St P ℝ C) (n k : IExp ℕ) (S L U : ℕ) (so lo uo : IExp ℕ)
    (M B D : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : Holds st.store p S so.eval M) (hB : Holds st.store p L lo.eval B)
    (hD : Holds st.store p U uo.eval D) (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    let B' := B.updateCol ⟨k.eval, hk⟩ (fun i => if i = ⟨k.eval, hk⟩ then 1 else 0)
    let D' := D.updateRow ⟨k.eval, hk⟩
      (fun j => if j.val < k.eval then 0 else M ⟨k.eval, hk⟩ j)
    ∃ out, exec I (luColumnZero p n k S L U so lo uo).run st = some out ∧
      st.store.writeBlocks p [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
        [flatten B', flatten D'] = some out.store ∧
      Holds out.store p L lo.eval B' ∧ Holds out.store p U uo.eval D' := by
  dsimp only
  obtain ⟨mid, hr₁, hw₁, hBL⟩ := exec_zeroLowerColumn I hI p st n k L lo B hk hB
  have hM' : Holds mid.store p S so.eval M := fun i j =>
    (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hSL)).trans (hM i j)
  have hD' : Holds mid.store p U uo.eval D := fun i j =>
    (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hLU.symm)).trans (hD i j)
  obtain ⟨out, hr₂, hw₂, hDU⟩ := exec_zeroUpperRow I hI p mid n k S U so uo M D hk hM' hD' hSU
  refine ⟨out, ?_, Store.writeBlocks_pair_eq_some_iff.mpr
    ⟨size_flatten _, size_flatten _, mid.store, hw₁, hw₂⟩, ?_, hDU⟩
  · change exec I (.seq _ .skip) st = some out
    rw [exec_seq_skip, exec_run_bind I (b := zeroLowerColumn p n k L lo) (fun _ => rfl),
      hr₁, Option.bind_some]
    exact hr₂
  · intro i j
    exact (Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hLU)).trans (hBL i j)

private theorem pop_factorBlocks {N L U lo uo : ℕ} {initial s sf : Store P ℝ} {p : P}
    {Lw Uw : Array ℝ} (hpop : s.pop = initial) (hsize : s.size = initial.size + 1)
    (hL : L < initial.size) (hU : U < initial.size)
    (hw : s.writeBlocks p [(L, lo, N * N), (U, uo, N * N)] [Lw, Uw] = some sf) :
    initial.writeBlocks p [(L, lo, N * N), (U, uo, N * N)] [Lw, Uw] = some sf.pop := by
  obtain ⟨hLs, hUs, mid, hwL, hwU⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
  have hmid := Store.size_of_writeBlock_eq_some hwL
  have hwL' := Store.writeBlock_pop_of_lt hwL (fun _ => by omega)
  have hwU' := Store.writeBlock_pop_of_lt hwU (fun _ => by omega)
  exact Store.writeBlocks_pair_eq_some_iff.mpr
    ⟨hLs, hUs, mid.pop, by simpa only [hpop] using hwL', hwU'⟩

private theorem exec_luColumnTotal_body (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (p : P) (initial : Store P ℝ) (st : St P ℝ C) (n k : IExp ℕ)
    (S L U : ℕ) (so lo uo : IExp ℕ) (M B D : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hM : Holds initial p S so.eval M)
    (hB : Holds initial p L lo.eval B) (hD : Holds initial p U uo.eval D)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U)
    (hst : st.store = initial.push (p, Array.replicate 1 none)) :
    let r : Fin n.eval := ⟨k.eval, hk⟩
    let B' := B.updateCol r (fun i => if i < r then 0 else if i = r then 1 else M i r / M r r)
    let D' := D.updateRow r (fun j => if j < r then 0 else M r j)
    ∃ out, exec I (do
      ins (.lit p ⟨initial.size, 0⟩ 0)
      ifThenElse p .eq ⟨S, so + k + n * k⟩ ⟨initial.size, 0⟩
        (luColumnZero p n k S L U so lo uo) (luColumn p n k S L U so lo uo)).run st = some out ∧
      initial.writeBlocks p [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
        [flatten B', flatten D'] = some out.store.pop := by
  dsimp only
  let r : Fin n.eval := ⟨k.eval, hk⟩
  have hSb := Store.lt_size_of_read_eq_some (hM r r)
  have hLb := Store.lt_size_of_read_eq_some (hB r r)
  have hUb := Store.lt_size_of_read_eq_some (hD r r)
  obtain ⟨s₀, hw₀⟩ := Store.exists_write_eq_some_of_getElem?_shape (0 : ℝ)
    (hst ▸ Store.getElem?_shape_push_size initial p 1) (by omega : 0 < 1)
  let ready : St P ℝ C := { st with store := s₀, cnt := st.cnt + I.charge (.lit p) }
  let tested : St P ℝ C := { ready with cnt := ready.cnt + I.charge (.cmp p) }
  have after {buf off : ℕ} {A : Matrix (Fin n.eval) (Fin n.eval) ℝ}
      (hA : Holds initial p buf off A) (hb : buf < initial.size) : Holds s₀ p buf off A := by
    intro i j
    rw [Store.read_of_write_eq_some_of_ne hw₀ (Or.inl (Nat.ne_of_lt hb)), hst,
      Store.read_push_of_lt hb]
    exact hA i j
  have hM₀ := after hM hSb
  have hB₀ := after hB hLb
  have hD₀ := after hD hUb
  have hpiv : s₀.read p S (so.eval + k.eval + n.eval * k.eval) = some (M r r) := hM₀ r r
  have hcmp : cmpStep I p .eq ⟨S, so + k + n * k⟩ ⟨initial.size, 0⟩ ready =
      some (decide (M r r = 0), tested) := by
    simp only [cmpStep, ready, IExp.eval_add, IExp.eval_mul, IExp.eval_zero, hpiv,
      Store.read_of_write_eq_some hw₀, Option.bind_some, hI, exactSem, Option.map_some]
    rfl
  have hbranch : ∃ out, exec I (.ite p .eq ⟨S, so + k + n * k⟩ ⟨initial.size, 0⟩
      (luColumnZero p n k S L U so lo uo).run (luColumn p n k S L U so lo uo).run) ready =
        some out ∧ s₀.writeBlocks p
        [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
        [flatten (B.updateCol r (fun i => if i < r then 0 else if i = r then 1
          else M i r / M r r)), flatten (D.updateRow r (fun j => if j < r then 0 else M r j))] =
          some out.store := by
    rw [exec_ite, hcmp, Option.bind_some]
    by_cases hp : M r r = 0
    · obtain ⟨out, hr, hw, _, _⟩ := exec_luColumnZero I hI p tested n k S L U so lo uo
        M B D hk hM₀ hB₀ hD₀ hSL hSU hLU
      have hcol : (fun i : Fin n.eval => if i < r then 0 else if i = r then 1
          else M i r / M r r) = (fun i => if i = r then 1 else 0) := by
        funext i
        by_cases he : i = r
        · subst i; simp
        · by_cases hil : i < r <;> simp [hil, he, hp]
      refine ⟨out, ?_, ?_⟩
      · simpa only [hp, decide_true, ↓reduceIte] using hr
      · rw [hcol]
        simpa only [tested, ready, r, Fin.lt_def] using hw
    · obtain ⟨out, hr, hw, _, _⟩ := exec_luColumn I hI p tested n k S L U so lo uo
        M B D hk hM₀ hp hB₀ hD₀ hSL hSU hLU
      exact ⟨out, by simpa only [hp, decide_false, Bool.false_eq_true, ↓reduceIte] using hr, hw⟩
  obtain ⟨out, hr, hw⟩ := hbranch
  have hpop : s₀.pop = initial := by
    rw [Store.pop_of_write_top hw₀ (by simp only [hst, Array.size_push]; omega), hst]
    exact Array.pop_push
  have hsize : s₀.size = initial.size + 1 :=
    (Store.size_of_write_eq_some hw₀).trans (by simp only [hst, Array.size_push])
  refine ⟨out, ?_, pop_factorBlocks hpop hsize hLb hUb hw⟩
  change exec I (.seq (.instr (.lit p ⟨initial.size, 0⟩ 0))
    (.seq (.ite p .eq ⟨S, so + k + n * k⟩ ⟨initial.size, 0⟩
      (luColumnZero p n k S L U so lo uo).run (luColumn p n k S L U so lo uo).run) .skip)) st = _
  rw [exec_seq_instr_lit I (by rw [hI]; simp only [exactSem, Rat.cast_zero]) hw₀, exec_seq_skip]
  exact hr

/-- Zero guarding makes exact factor-column materialization succeed for every stored
residual, including a zero pivot with a nonzero entry below it. The lower column is the total
formula with division by zero equal to zero, and the upper row is the stored pivot row with
its left prefix zeroed. Both factor blocks are initialized and distinct from one another
and from the residual. The only net writes are those two full factor blocks; all workspace
is scoped. This local execution statement alone does not assert that an arbitrary residual
admits an LU factorization. [GolubVanLoan2013, §3.2]. -/
theorem exec_luColumnTotal (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (p : P) (st : St P ℝ C) (n k : IExp ℕ) (S L U : ℕ) (so lo uo : IExp ℕ)
    (M B D : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : Holds st.store p S so.eval M) (hB : Holds st.store p L lo.eval B)
    (hD : Holds st.store p U uo.eval D) (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    let r : Fin n.eval := ⟨k.eval, hk⟩
    let B' := B.updateCol r (fun i => if i < r then 0 else if i = r then 1 else M i r / M r r)
    let D' := D.updateRow r (fun j => if j < r then 0 else M r j)
    ∃ out, exec I (luColumnTotal p n k S L U so lo uo).run st = some out ∧
      st.store.writeBlocks p [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
        [flatten B', flatten D'] = some out.store ∧
      Holds out.store p L lo.eval B' ∧ Holds out.store p U uo.eval D' := by
  dsimp only
  obtain ⟨out, hr, hw⟩ := exists_exec_alloc I p 1 (fun zbuf => ((do
    ins (.lit p ⟨zbuf, 0⟩ 0)
    ifThenElse p .eq ⟨S, so + k + n * k⟩ ⟨zbuf, 0⟩
      (luColumnZero p n k S L U so lo uo) (luColumn p n k S L U so lo uo)) :
        Builder P ι ℕ ℕ Unit).run) st
    (fun s => st.store.writeBlocks p
      [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
      [flatten (B.updateCol ⟨k.eval, hk⟩ (fun i => if i < ⟨k.eval, hk⟩ then 0 else
        if i = ⟨k.eval, hk⟩ then 1 else M i ⟨k.eval, hk⟩ / M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)),
        flatten (D.updateRow ⟨k.eval, hk⟩ (fun j => if j < ⟨k.eval, hk⟩ then 0
          else M ⟨k.eval, hk⟩ j))] = some s)
    (fun σ hσ => exec_luColumnTotal_body I hI p st.store σ n k S L U so lo uo
      M B D hk hM hB hD hSL hSU hLU hσ)
  obtain ⟨_, _, mid, hwL, hwU⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
  refine ⟨out, ?_, hw, ?_, ?_⟩
  · change exec I (.seq (.alloc p 1 _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hwU (Or.inl hLU)]
    simpa only [Nat.add_assoc] using (Store.read_of_writeBlock_eq_some_of_lt hwL
      (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)).trans
      (getElem?_flatten _ i j)
  · intro i j
    simpa only [Nat.add_assoc] using (Store.read_of_writeBlock_eq_some_of_lt hwU
      (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)).trans
      (getElem?_flatten _ i j)

/-- A diagonal pivot guard makes exact Schur elimination succeed for every stored square
matrix, including a zero pivot with nonzero entries below it. Zero pivots skip the arithmetic;
nonzero pivots execute the actual rank-one kernel. Its only net store effect is the full
matrix block write of the total mathematical elimination step. No factorization or rank
conclusion is asserted for an arbitrary zero pivot. [GolubVanLoan2013, §3.2]. -/
theorem exec_schurStepTotal (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (R : ℕ) (off k : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : Holds st.store p R off.eval M) :
    ∃ out, exec I (schurStepTotal p n R off k).run st = some out ∧
      st.store.writeBlock p R off.eval (flatten (eliminationStep M ⟨k.eval, hk⟩)) =
        some out.store ∧ Holds out.store p R off.eval (eliminationStep M ⟨k.eval, hk⟩) := by
  let r : Fin n.eval := ⟨k.eval, hk⟩
  let E := eliminationStep M r
  have hRb := Store.lt_size_of_read_eq_some (hM r r)
  have hbody : ∀ σ : St P ℝ (OpCount P ι),
      σ.store = st.store.push (p, Array.replicate 1 none) →
      ∃ out, exec I (do
        ins (.lit p ⟨st.store.size, 0⟩ 0)
        ifThenElse p .eq ⟨R, off + k + n * k⟩ ⟨st.store.size, 0⟩
          (pure ()) (schurStep p n R off k)).run σ = some out ∧
        st.store.writeBlock p R off.eval (flatten E) = some out.store.pop := by
    intro σ hσ
    obtain ⟨s₀, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape (0 : ℝ)
      (hσ ▸ Store.getElem?_shape_push_size st.store p 1) (by omega : 0 < 1)
    let ready : St P ℝ (OpCount P ι) :=
      { σ with store := s₀, cnt := σ.cnt + I.charge (.lit p) }
    let tested : St P ℝ (OpCount P ι) :=
      { ready with cnt := ready.cnt + I.charge (.cmp p) }
    have hM₀ : Holds s₀ p R off.eval M := fun i j => by
      rw [Store.read_of_write_eq_some_of_ne hw (Or.inl (Nat.ne_of_lt hRb)), hσ,
        Store.read_push_of_lt hRb]
      exact hM i j
    have hpiv : s₀.read p R (off.eval + k.eval + n.eval * k.eval) = some (M r r) := hM₀ r r
    have hcmp : cmpStep I p .eq ⟨R, off + k + n * k⟩ ⟨st.store.size, 0⟩ ready =
        some (decide (M r r = 0), tested) := by
      simp only [cmpStep, ready, IExp.eval_add, IExp.eval_mul, IExp.eval_zero,
        hpiv, Store.read_of_write_eq_some hw, Option.bind_some, hI, exactSem,
        Option.map_some]
      rfl
    have hpop : s₀.pop = st.store := by
      rw [Store.pop_of_write_top hw (by simp only [hσ, Array.size_push]; omega), hσ]
      exact Array.pop_push
    by_cases hp : M r r = 0
    · refine ⟨tested, ?_, ?_⟩
      · change exec I (.seq (.instr (.lit p ⟨st.store.size, 0⟩ 0))
          (.seq (.ite p .eq ⟨R, off + k + n * k⟩ ⟨st.store.size, 0⟩
            .skip (schurStep p n R off k).run) .skip)) σ = some tested
        rw [exec_seq_instr_lit I (by rw [hI]; simp [exactSem]) hw, exec_seq_skip,
          exec_ite, hcmp]
        simp only [hp, decide_true, Option.bind_some, ↓reduceIte, exec_skip]
      · rw [show tested.store.pop = st.store from hpop]
        simpa only [E, eliminationStep_eq_self_of_apply_self_eq_zero hp] using
          hM.writeBlock_self
    · obtain ⟨out, hr, hm, _⟩ := exec_schurStep I hI hc p tested n R off k M hk hM₀ hp
      refine ⟨out, ?_, ?_⟩
      · change exec I (.seq (.instr (.lit p ⟨st.store.size, 0⟩ 0))
          (.seq (.ite p .eq ⟨R, off + k + n * k⟩ ⟨st.store.size, 0⟩
            .skip (schurStep p n R off k).run) .skip)) σ = some out
        rw [exec_seq_instr_lit I (by rw [hI]; simp [exactSem]) hw, exec_seq_skip, exec_ite, hcmp]
        simpa only [hp, decide_false, Option.bind_some, Bool.false_eq_true, ↓reduceIte] using hr
      · have hh := Store.writeBlock_pop_of_lt hm (fun _ => by
          have hs : s₀.size = st.store.size + 1 :=
            (Store.size_of_write_eq_some hw).trans (by simp [hσ])
          change R + 1 < s₀.size
          omega)
        have hpop' : tested.store.pop = st.store := hpop
        simpa only [hpop'] using hh
  obtain ⟨out, hr, hw⟩ := exists_exec_alloc I p 1 (fun zbuf => ((do
    ins (.lit p ⟨zbuf, 0⟩ 0)
    ifThenElse p .eq ⟨R, off + k + n * k⟩ ⟨zbuf, 0⟩
      (pure ()) (schurStep p n R off k)) : Builder P ι ℕ ℕ Unit).run) st
    (fun s => st.store.writeBlock p R off.eval (flatten E) = some s) hbody
  refine ⟨out, ?_, hw, fun i j => ?_⟩
  · change exec I (.seq (.alloc p 1 _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · simpa only [Nat.add_assoc] using (Store.read_of_writeBlock_eq_some_of_lt hw
      (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)).trans
      (getElem?_flatten E i j)

end NLAlib.Computation
