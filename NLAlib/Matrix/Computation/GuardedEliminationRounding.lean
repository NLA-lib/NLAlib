/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.GuardedElimination
public import NLAlib.Matrix.Computation.LUColumnRounding
public import NLAlib.Matrix.Computation.SchurRounding
public import NLAlib.Matrix.Computation.SchurTotalRoundingTrace

/-!
# Rounded elimination with actual zero-pivot guards

The existing guarded materialization writes zero multipliers and an exact unit diagonal when
the decoded pivot is zero, avoiding division. Otherwise it executes the rounded LU column.
The guarded Schur step likewise skips a decoded zero pivot and otherwise executes the
saved-pivot rounded update. Both success theorems retain their complete block frames.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_luColumnTotal`: total rounded materialization.
* `NLAlib.Computation.IsRelErrSem.exec_schurStepTotal`: total rounded Schur execution.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

namespace GuardedEliminationRounding

private def pivotRowValue {N : ℕ} (z : K) (M : Matrix (Fin N) (Fin N) K)
    (r : Fin N) (j : ℕ) : K := if hj : j < N then M r ⟨j, hj⟩ else z

private theorem exec_zeroUpperRow_parts (I : Interp P ι K C) (p : P) (z o : K)
    (hz : I.sem.lit p 0 = some z) (_ho : I.sem.lit p 1 = some o)
    (st : St P K C) (n k : IExp ℕ) (S U : ℕ) (so uo : IExp ℕ)
    (M D : Matrix (Fin n.eval) (Fin n.eval) K) (hk : k.eval < n.eval)
    (hM : Holds st.store p S so.eval M) (hD : Holds st.store p U uo.eval D) (hSU : S ≠ U) :
    ∃ (mid out : St P K C),
      exec I (zeroUpperRow p n k S U so uo).run st = some out ∧
      mid.store.shape = st.store.shape ∧ out.store.shape = mid.store.shape ∧
      (∀ j < k.eval, mid.store.read p U (uo.eval + k.eval + n.eval * j) = some z) ∧
      (∀ j < n.eval - k.eval, out.store.read p U
        (uo.eval + k.eval + n.eval * k.eval + n.eval * j) =
          some (pivotRowValue z M ⟨k.eval, hk⟩ (k.eval + j))) ∧
      (∀ q b idx, (b ≠ U ∨ ∀ j < k.eval, idx ≠ uo.eval + k.eval + n.eval * j) →
        mid.store.read q b idx = st.store.read q b idx) ∧
      (∀ q b idx, (b ≠ U ∨ ∀ j < n.eval - k.eval,
        idx ≠ uo.eval + k.eval + n.eval * k.eval + n.eval * j) →
        out.store.read q b idx = mid.store.read q b idx) := by
  have hcapacity : ∀ σ : St P K C, σ.store.shape = st.store.shape → ∀ j < n.eval,
      ∃ len, σ.store.shape[U]? = some (p, len) ∧ uo.eval + k.eval + n.eval * j < len := by
    intro σ hs j hj
    obtain ⟨len, hlen, hlt⟩ := hD.writable (k.eval + n.eval * j)
      (Nat.add_mul_lt_mul_of_lt_of_lt hk hj)
    exact ⟨len, hs ▸ hlen, by simpa only [Nat.add_assoc] using hlt⟩
  obtain ⟨mid, hr₁, hsh₁, hread₁, hframe₁⟩ := exec_strided_writes I p st k U
    (uo.eval + k.eval) n.eval (by omega) (fun _ => z)
    (fun j => ins (.lit p ⟨U, uo + k + n * .var j⟩ 0)) (by
      intro j hj σ hs _
      obtain ⟨store, hw, hr, _⟩ := exec_scalar_lit I p σ ⟨U, uo + k + n * .var j⟩ 0 z hz
        (by simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_var] using
          hcapacity σ hs j (hj.trans hk))
      exact ⟨_, hr, by simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_var] using hw⟩)
  have hM' : Holds mid.store p S so.eval M := fun i j =>
    (hframe₁ p S _ (Or.inl hSU)).trans (hM i j)
  obtain ⟨out, hr₂, hsh₂, hread₂, hframe₂⟩ := exec_strided_writes I p mid (n - k) U
    (uo.eval + k.eval + n.eval * k.eval) n.eval (by omega)
    (fun j => pivotRowValue z M ⟨k.eval, hk⟩ (k.eval + j))
    (fun j => ins (.copy p ⟨U, uo + k + n * (k + .var j)⟩
      ⟨S, so + k + n * (k + .var j)⟩)) (by
      intro j hj σ hs hf
      have hj' : k.eval + j < n.eval := by change j < n.eval - k.eval at hj; omega
      have hsrc : σ.store.read p S (so + k + n * (k + .var j)).eval =
          some (pivotRowValue z M ⟨k.eval, hk⟩ (k.eval + j)) := by
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

private theorem holds_zeroUpperRow {N k U off : ℕ} (hk : k < N) (z : K)
    (M D : Matrix (Fin N) (Fin N) K) {s mid out : Store P K} {p : P}
    (hD : Holds s p U off D)
    (hread₁ : ∀ j < k, mid.read p U (off + k + N * j) = some z)
    (hread₂ : ∀ j < N - k, out.read p U (off + k + N * k + N * j) =
      some (pivotRowValue z M ⟨k, hk⟩ (k + j)))
    (hframe₁ : ∀ q b idx, (b ≠ U ∨ ∀ j < k, idx ≠ off + k + N * j) →
      mid.read q b idx = s.read q b idx)
    (hframe₂ : ∀ q b idx, (b ≠ U ∨ ∀ j < N - k, idx ≠ off + k + N * k + N * j) →
      out.read q b idx = mid.read q b idx) :
    Holds out p U off (D.updateRow ⟨k, hk⟩ (fun j => if j.val < k then z else M ⟨k, hk⟩ j)) := by
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

private theorem exec_zeroUpperRow (I : Interp P ι K C) (p : P) (z o : K)
    (hz : I.sem.lit p 0 = some z) (ho : I.sem.lit p 1 = some o)
    (st : St P K C) (n k : IExp ℕ) (S U : ℕ) (so uo : IExp ℕ)
    (M D : Matrix (Fin n.eval) (Fin n.eval) K) (hk : k.eval < n.eval)
    (hM : Holds st.store p S so.eval M) (hD : Holds st.store p U uo.eval D) (hSU : S ≠ U) :
    let D' := D.updateRow ⟨k.eval, hk⟩
      (fun j => if j.val < k.eval then z else M ⟨k.eval, hk⟩ j)
    ∃ (out : St P K C) (W : Array K), exec I (zeroUpperRow p n k S U so uo).run st = some out ∧
      W.size = n.eval * n.eval ∧
      st.store.writeBlock p U uo.eval W = some out.store ∧
      Holds out.store p U uo.eval D' := by
  dsimp only
  obtain ⟨mid, out, hr, hshape₁, hshape₂, hread₁, hread₂, hframe₁, hframe₂⟩ :=
    exec_zeroUpperRow_parts I p z o hz ho st n k S U so uo M D hk hM hD hSU
  have hfinal := holds_zeroUpperRow hk z M D hD hread₁ hread₂ hframe₁ hframe₂
  have hbound : ∀ t < n.eval, uo.eval + k.eval + n.eval * t <
      uo.eval + n.eval * n.eval := fun t ht => by
    have hh := Nat.add_mul_lt_mul_of_lt_of_lt hk ht
    omega
  obtain ⟨W, hWs, hflat, -, -⟩ := hfinal.exists_array
  refine ⟨out, W, hr, hWs, ?_, hfinal⟩
  apply Store.writeBlock_eq_some_of_read (hshape₂.trans hshape₁)
  · intro t ht
    exact hflat t (hWs ▸ ht)
  · intro q b idx hout
    rw [hWs] at hout
    rw [hframe₂ q b idx (hout.imp_right (fun hi t ht => by
      have hb := hbound (k.eval + t) (by omega)
      simp only [Nat.mul_add] at hb
      omega))]
    exact hframe₁ q b idx (hout.imp_right (fun hi t ht => by
      have hb := hbound t (ht.trans hk)
      omega))

private theorem holds_zeroColumn {N k L off : ℕ} (hk : k < N) (z : K)
    (B : Matrix (Fin N) (Fin N) K) {s s' : Store P K} {p : P}
    (hB : Holds s p L off B)
    (hread : ∀ i < N, s'.read p L (off + N * k + i) = some z)
    (hframe : ∀ q b idx, (q ≠ p ∨ b ≠ L ∨ idx < off + N * k ∨
      off + N * k + N ≤ idx) → s'.read q b idx = s.read q b idx) :
    Holds s' p L off (B.updateCol ⟨k, hk⟩ (fun _ => z)) := by
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

private theorem holds_oneColumn {N k L off : ℕ} (hk : k < N) (z o : K)
    (B : Matrix (Fin N) (Fin N) K) {s s' : Store P K} {p : P}
    (hB : Holds s p L off (B.updateCol ⟨k, hk⟩ (fun _ => z)))
    (hw : s.write p L (off + k + N * k) o = some s') :
    Holds s' p L off (B.updateCol ⟨k, hk⟩ (fun i => if i = ⟨k, hk⟩ then o else z)) := by
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

private theorem exec_zeroLowerColumn (I : Interp P ι K C) (p : P) (z o : K)
    (hz : I.sem.lit p 0 = some z) (ho : I.sem.lit p 1 = some o)
    (st : St P K C) (n k : IExp ℕ) (L : ℕ) (lo : IExp ℕ)
    (B : Matrix (Fin n.eval) (Fin n.eval) K) (hk : k.eval < n.eval)
    (hB : Holds st.store p L lo.eval B) :
    let B' := B.updateCol ⟨k.eval, hk⟩ (fun i => if i = ⟨k.eval, hk⟩ then o else z)
    ∃ (out : St P K C) (W : Array K), exec I (zeroLowerColumn p n k L lo).run st = some out ∧
      W.size = n.eval * n.eval ∧
      st.store.writeBlock p L lo.eval W = some out.store ∧
      Holds out.store p L lo.eval B' := by
  dsimp only
  have hcol : Writable st.store p L (lo + n * k).eval n.eval := by
    intro i hi
    obtain ⟨len, hlen, hlt⟩ := hB.writable (i + n.eval * k.eval)
      (Nat.add_mul_lt_mul_of_lt_of_lt hi hk)
    exact ⟨len, hlen, by simpa only [IExp.eval_add, IExp.eval_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hlt⟩
  obtain ⟨s₀, hr₁, hshape, hread, hframe⟩ :=
    exec_forRange_literal_zero I p z hz st n L (lo + n * k) hcol
  have hB₀ := holds_zeroColumn hk z B hB hread hframe
  let mid : St P K C := { st with store := s₀, cnt := st.cnt + n.eval • I.charge (.lit p) }
  obtain ⟨len, hlen, hlt⟩ := hB.writable (k.eval + n.eval * k.eval)
    (Nat.add_mul_lt_mul_of_lt_of_lt hk hk)
  obtain ⟨s₁, hw, hr₂, hs, _⟩ := exec_scalar_lit I p mid ⟨L, lo + k + n * k⟩ 1 o ho
    ⟨len, hshape ▸ hlen, by simpa only [IExp.eval_add, IExp.eval_mul, Nat.add_assoc] using hlt⟩
  have hB₁ := holds_oneColumn hk z o B hB₀ hw
  let out : St P K C := { mid with store := s₁, cnt := mid.cnt + I.charge (.lit p) }
  obtain ⟨W, hWs, hflat, -, -⟩ := hB₁.exists_array
  refine ⟨out, W, ?_, hWs, ?_, hB₁⟩
  · change exec I (.seq _ .skip) st = _
    rw [exec_seq_skip, exec_run_bind I (b := forRange n fun i =>
      ins (.lit p ⟨L, lo + n * k + .var i⟩ 0)) (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂
  · apply Store.writeBlock_eq_some_of_read (hs.trans hshape)
    · intro t ht
      exact hflat t (hWs ▸ ht)
    · intro q b idx hout
      rw [hWs] at hout
      have hend := Nat.mul_le_mul_left n.eval (Nat.succ_le_of_lt hk)
      have hpiv := Nat.add_mul_lt_mul_of_lt_of_lt hk hk
      have hend' : n.eval * k.eval + n.eval ≤ n.eval * n.eval := by nlinarith
      rw [Store.read_of_write_eq_some_of_ne hw (by
        change b ≠ L ∨ idx ≠ lo.eval + k.eval + n.eval * k.eval
        omega)]
      exact hframe q b idx (Or.inr (by simp only [IExp.eval_add, IExp.eval_mul]; omega))

private theorem exec_luColumnZero (I : Interp P ι K C) (p : P) (z o : K)
    (hz : I.sem.lit p 0 = some z) (ho : I.sem.lit p 1 = some o)
    (st : St P K C) (n k : IExp ℕ) (S L U : ℕ) (so lo uo : IExp ℕ)
    (M B D : Matrix (Fin n.eval) (Fin n.eval) K) (hk : k.eval < n.eval)
    (hM : Holds st.store p S so.eval M) (hB : Holds st.store p L lo.eval B)
    (hD : Holds st.store p U uo.eval D) (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    let B' := B.updateCol ⟨k.eval, hk⟩ (fun i => if i = ⟨k.eval, hk⟩ then o else z)
    let D' := D.updateRow ⟨k.eval, hk⟩
      (fun j => if j.val < k.eval then z else M ⟨k.eval, hk⟩ j)
    ∃ (out : St P K C) (WL WU : Array K),
      exec I (luColumnZero p n k S L U so lo uo).run st = some out ∧
      WL.size = n.eval * n.eval ∧ WU.size = n.eval * n.eval ∧
      st.store.writeBlocks p [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
        [WL, WU] = some out.store ∧
      Holds out.store p L lo.eval B' ∧ Holds out.store p U uo.eval D' := by
  dsimp only
  obtain ⟨mid, WL, hr₁, hLs, hw₁, hBL⟩ := exec_zeroLowerColumn I p z o hz ho st n k L lo B hk hB
  have hM' : Holds mid.store p S so.eval M := fun i j =>
    (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hSL)).trans (hM i j)
  have hD' : Holds mid.store p U uo.eval D := fun i j =>
    (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hLU.symm)).trans (hD i j)
  obtain ⟨out, WU, hr₂, hUs, hw₂, hDU⟩ :=
    exec_zeroUpperRow I p z o hz ho mid n k S U so uo M D hk hM' hD' hSU
  refine ⟨out, WL, WU, ?_, hLs, hUs, Store.writeBlocks_pair_eq_some_iff.mpr
    ⟨hLs, hUs, mid.store, hw₁, hw₂⟩, ?_, hDU⟩
  · change exec I (.seq _ .skip) st = some out
    rw [exec_seq_skip, exec_run_bind I (b := zeroLowerColumn p n k L lo) (fun _ => rfl),
      hr₁, Option.bind_some]
    exact hr₂
  · intro i j
    exact (Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hLU)).trans (hBL i j)

private theorem pop_factorBlocks {N L U lo uo : ℕ} {initial s sf : Store P K} {p : P}
    {Lw Uw : Array K} (hpop : s.pop = initial) (hsize : s.size = initial.size + 1)
    (hL : L < initial.size) (hU : U < initial.size)
    (hw : s.writeBlocks p [(L, lo, N * N), (U, uo, N * N)] [Lw, Uw] = some sf) :
    initial.writeBlocks p [(L, lo, N * N), (U, uo, N * N)] [Lw, Uw] = some sf.pop := by
  obtain ⟨hLs, hUs, mid, hwL, hwU⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
  have hmid := Store.size_of_writeBlock_eq_some hwL
  have hwL' := Store.writeBlock_pop_of_lt hwL (fun _ => by omega)
  have hwU' := Store.writeBlock_pop_of_lt hwU (fun _ => by omega)
  exact Store.writeBlocks_pair_eq_some_iff.mpr
    ⟨hLs, hUs, mid.pop, by simpa only [hpop] using hwL', hwU'⟩


/-- The materialized column, error witnesses and complete original factor footprint. -/
private def ColumnResult {N : ℕ} (dec : P → K → ℝ) (u : P → ℝ) (p : P)
    (initial : Store P K) (L U lo uo : ℕ) (r : Fin N)
    (M B D : Matrix (Fin N) (Fin N) ℝ) (final : Store P K) : Prop :=
  ∃ (WL WU : Array K) (v : Fin N → ℝ),
    WL.size = N * N ∧ WU.size = N * N ∧
    initial.writeBlocks p [(L, lo, N * N), (U, uo, N * N)] [WL, WU] = some final ∧
    HoldsDecoded final dec p L lo (B.updateCol r v) ∧
    HoldsDecoded final dec p U uo (D.updateRow r (fun j => if j < r then 0 else M r j)) ∧
    (∀ i, i < r → v i = 0) ∧ v r = 1 ∧
    ∀ i, r < i → RelErr (u p) (M i r / M r r) (v i)

private theorem exec_zeroDecoded {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (p : P) (st : St P K C)
    (S L U : ℕ) (so lo uo : IExp ℕ) (M B D : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hM : HoldsDecoded st.store dec p S so.eval M)
    (hp : M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ = 0)
    (hB : HoldsDecoded st.store dec p L lo.eval B) (hD : HoldsDecoded st.store dec p U uo.eval D)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    ∃ out, exec I (luColumnZero p n k S L U so lo uo).run st = some out ∧
      ColumnResult dec u p st.store L U lo.eval uo.eval ⟨k.eval, hk⟩ M B D out.store := by
  classical
  let r : Fin n.eval := ⟨k.eval, hk⟩
  choose Mw hMw hdMw using hM
  choose Bw hBw hdBw using hB
  choose Dw hDw hdDw using hD
  change Matrix (Fin n.eval) (Fin n.eval) K at Mw Bw Dw
  obtain ⟨z, hz⟩ := h.lit_ok p 0 trivial
  have hdz : dec p z = 0 := by
    obtain ⟨δ, -, hd⟩ := h.lit_err p 0 z hz
    simpa only [Rat.cast_zero, zero_mul] using hd
  obtain ⟨o, ho, hdo⟩ := hi.intLit p 1 (by omega)
  obtain ⟨out, WL, WU, hr, hLs, hUs, hw, hL, hU⟩ := exec_luColumnZero I p z o hz
    (by simpa only [Nat.cast_one] using ho) st n k S L U so lo uo Mw Bw Dw hk
    hMw hBw hDw hSL hSU hLU
  change Holds out.store p L lo.eval
    (Matrix.updateCol Bw r (fun i => if i = r then o else z)) at hL
  change Holds out.store p U uo.eval
    (Matrix.updateRow Dw r (fun j => if j < r then z else Mw r j)) at hU
  let v : Fin n.eval → ℝ := fun i => if i = r then 1 else 0
  refine ⟨out, hr, WL, WU, v, hLs, hUs, hw, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨_, hL i j, ?_⟩
    change dec p ((Matrix.updateCol Bw r (fun i => if i = r then o else z)) i j) =
      (B.updateCol r v) i j
    by_cases hj : j = r
    · subst j
      rw [Matrix.updateCol_self, Matrix.updateCol_self]
      by_cases hir : i = r <;> simp only [hir, ↓reduceIte, v, hdz, hdo, Nat.cast_one]
    · rw [Matrix.updateCol_ne hj, Matrix.updateCol_ne hj, hdBw]
  · intro i j
    refine ⟨_, hU i j, ?_⟩
    change dec p ((Matrix.updateRow Dw r (fun j => if j < r then z else Mw r j)) i j) =
      (D.updateRow r (fun j => if j < r then 0 else M r j)) i j
    by_cases hir : i = r
    · subst i
      rw [Matrix.updateRow_self, Matrix.updateRow_self]
      by_cases hj : j < r <;> simp only [hj, ↓reduceIte, hdz, hdMw]
    · rw [Matrix.updateRow_ne hir, Matrix.updateRow_ne hir, hdDw]
  · intro i hir
    change (if i = r then 1 else 0) = 0
    exact if_neg (show i ≠ r from hir.ne)
  · change (if r = r then 1 else 0) = 1
    exact if_pos rfl
  · intro i hri
    change RelErr (u p) (M i r / M r r) (if i = r then 1 else 0)
    refine ⟨0, by simpa only [abs_zero] using h.nonneg (p := p) trivial, ?_⟩
    rw [if_neg (Ne.symm hri.ne)]
    simp only [show M r r = 0 from hp, div_zero, zero_mul]

private theorem ColumnResult.pop {N L U lo uo : ℕ} {dec : P → K → ℝ} {u : P → ℝ}
    {p : P} {initial base final : Store P K} {r : Fin N}
    {M B D : Matrix (Fin N) (Fin N) ℝ}
    (h : ColumnResult dec u p initial L U lo uo r M B D final)
    (hpop : initial.pop = base) (hsize : initial.size = base.size + 1)
    (hL : L < base.size) (hU : U < base.size) :
    ColumnResult dec u p base L U lo uo r M B D final.pop := by
  obtain ⟨WL, WU, v, hLs, hUs, hw, hF, hG, hv0, hv1, hdiv⟩ := h
  have hsz : final.size = initial.size :=
    Store.size_eq_of_shape_eq (Store.shape_of_writeBlocks_eq_some hw)
  refine ⟨WL, WU, v, hLs, hUs, pop_factorBlocks hpop hsize hL hU hw, ?_, ?_, hv0, hv1, hdiv⟩
  · intro i j
    obtain ⟨w, hr, hd⟩ := hF i j
    exact ⟨w, (Store.read_pop_of_lt (by omega)).trans hr, hd⟩
  · intro i j
    obtain ⟨w, hr, hd⟩ := hG i j
    exact ⟨w, (Store.read_pop_of_lt (by omega)).trans hr, hd⟩

private theorem exec_columnBranch {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (p : P)
    (ready tested : St P K C) (S L U zbuf : ℕ) (so lo uo : IExp ℕ)
    (M B D : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : HoldsDecoded tested.store dec p S so.eval M)
    (hB : HoldsDecoded tested.store dec p L lo.eval B)
    (hD : HoldsDecoded tested.store dec p U uo.eval D)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) (hs : tested.store = ready.store)
    (hcmp : cmpStep I p .eq ⟨S, so + k + n * k⟩ ⟨zbuf, 0⟩ ready =
      some (decide (M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ = 0), tested)) :
    ∃ out, exec I (.ite p .eq ⟨S, so + k + n * k⟩ ⟨zbuf, 0⟩
      (luColumnZero p n k S L U so lo uo).run (luColumn p n k S L U so lo uo).run) ready =
        some out ∧ ColumnResult dec u p ready.store L U lo.eval uo.eval ⟨k.eval, hk⟩ M B D
          out.store := by
  rw [exec_ite, hcmp, Option.bind_some]
  by_cases hp : M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ = 0
  · obtain ⟨out, hr, hR⟩ := exec_zeroDecoded I h n k hi p tested S L U so lo uo
      M B D hk hM hp hB hD hSL hSU hLU
    exact ⟨out, by simpa only [hp, decide_true, ↓reduceIte] using hr, hs ▸ hR⟩
  · obtain ⟨out, WL, WU, v, hr, hRs⟩ := h.exec_luColumn I n k hi p tested S L U so lo uo
      M B D hk hM hp hB hD hSL hSU hLU
    exact ⟨out, by simpa only [hp, decide_false, Bool.false_eq_true, ↓reduceIte] using hr,
      WL, WU, v, hs ▸ hRs⟩

private theorem exec_luColumnTotal_body {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (p : P)
    (initial : Store P K) (st : St P K C) (S L U : ℕ) (so lo uo : IExp ℕ)
    (M B D : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : HoldsDecoded initial dec p S so.eval M)
    (hB : HoldsDecoded initial dec p L lo.eval B) (hD : HoldsDecoded initial dec p U uo.eval D)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U)
    (hst : st.store = initial.push (p, Array.replicate 1 none)) :
    ∃ out, exec I (do
      ins (.lit p ⟨initial.size, 0⟩ 0)
      ifThenElse p .eq ⟨S, so + k + n * k⟩ ⟨initial.size, 0⟩
        (luColumnZero p n k S L U so lo uo) (luColumn p n k S L U so lo uo)).run st = some out ∧
      ColumnResult dec u p initial L U lo.eval uo.eval ⟨k.eval, hk⟩ M B D out.store.pop := by
  let r : Fin n.eval := ⟨k.eval, hk⟩
  obtain ⟨sw, hsw, -⟩ := hM r r
  obtain ⟨lw, hlw, -⟩ := hB r r
  obtain ⟨uw, huw, -⟩ := hD r r
  have hSb := Store.lt_size_of_read_eq_some hsw
  have hLb := Store.lt_size_of_read_eq_some hlw
  have hUb := Store.lt_size_of_read_eq_some huw
  obtain ⟨z, hz⟩ := h.lit_ok p 0 trivial
  have hdz : dec p z = 0 := by
    obtain ⟨δ, -, hd⟩ := h.lit_err p 0 z hz
    simpa only [Rat.cast_zero, zero_mul] using hd
  obtain ⟨s₀, hw₀⟩ := Store.exists_write_eq_some_of_getElem?_shape z
    (hst ▸ Store.getElem?_shape_push_size initial p 1) (by omega : 0 < 1)
  let ready : St P K C := { st with store := s₀, cnt := st.cnt + I.charge (.lit p) }
  let tested : St P K C := { ready with cnt := ready.cnt + I.charge (.cmp p) }
  have after {buf off : ℕ} {A : Matrix (Fin n.eval) (Fin n.eval) ℝ}
      (hA : HoldsDecoded initial dec p buf off A) (hb : buf < initial.size) :
      HoldsDecoded s₀ dec p buf off A := by
    intro i j
    obtain ⟨w, hr, hd⟩ := hA i j
    refine ⟨w, ?_, hd⟩
    rw [Store.read_of_write_eq_some_of_ne hw₀ (Or.inl (Nat.ne_of_lt hb)), hst,
      Store.read_push_of_lt hb]
    exact hr
  have hM₀ := after hM hSb
  have hB₀ := after hB hLb
  have hD₀ := after hD hUb
  obtain ⟨pw, hpw, hdp⟩ := hM₀ r r
  change s₀.read p S (so.eval + k.eval + n.eval * k.eval) = some pw at hpw
  have hcmp : cmpStep I p .eq ⟨S, so + k + n * k⟩ ⟨initial.size, 0⟩ ready =
      some (decide (M r r = 0), tested) := by
    simp only [cmpStep, ready, IExp.eval_add, IExp.eval_mul, IExp.eval_zero, hpw,
      Store.read_of_write_eq_some hw₀, Option.bind_some, h.cmp_eq, hdp, hdz]
    rfl
  obtain ⟨out, hr, hR⟩ := exec_columnBranch I h n k hi p ready tested S L U initial.size
    so lo uo M B D hk hM₀ hB₀ hD₀ hSL hSU hLU rfl hcmp
  have hpop : s₀.pop = initial := by
    rw [Store.pop_of_write_top hw₀ (by simp only [hst, Array.size_push]; omega), hst]
    exact Array.pop_push
  have hsize : s₀.size = initial.size + 1 :=
    (Store.size_of_write_eq_some hw₀).trans (by simp only [hst, Array.size_push])
  refine ⟨out, ?_, hR.pop hpop hsize hLb hUb⟩
  change exec I (.seq (.instr (.lit p ⟨initial.size, 0⟩ 0))
    (.seq (.ite p .eq ⟨S, so + k + n * k⟩ ⟨initial.size, 0⟩
      (luColumnZero p n k S L U so lo uo).run (luColumn p n k S L U so lo uo).run) .skip)) st = _
  rw [exec_seq_instr_lit I hz hw₀, exec_seq_skip]
  exact hr


end GuardedEliminationRounding

/-- The actual zero-guarded LU materialization succeeds for every decoded residual under the
standard model with every scalar result in range and exact integer literals through the
matrix size. A zero pivot takes the branch that writes zero multipliers without division.
The decoded lower column has exact triangular zeros and unit diagonal, and each entry below
it is a relative-error approximation to the total quotient (zero when the pivot is zero).
The upper row is copied with its left prefix cleared. All three blocks are initialized and
in distinct buffers; only the two factor blocks are written, and scratch buffers are released.
No upper bound on the unit roundoff is required. [Higham2002, §2.2; GolubVanLoan2013, §3.2]. -/
theorem IsRelErrSem.exec_luColumnTotal {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (p : P) (st : St P K C)
    (S L U : ℕ) (so lo uo : IExp ℕ) (M B D : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hM : HoldsDecoded st.store dec p S so.eval M)
    (hB : HoldsDecoded st.store dec p L lo.eval B) (hD : HoldsDecoded st.store dec p U uo.eval D)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    let r : Fin n.eval := ⟨k.eval, hk⟩
    ∃ (out : St P K C) (WL WU : Array K) (v : Fin n.eval → ℝ),
      exec I (luColumnTotal p n k S L U so lo uo).run st = some out ∧
      WL.size = n.eval * n.eval ∧ WU.size = n.eval * n.eval ∧
      st.store.writeBlocks p [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
        [WL, WU] = some out.store ∧
      HoldsDecoded out.store dec p L lo.eval (B.updateCol r v) ∧
      HoldsDecoded out.store dec p U uo.eval (D.updateRow r (fun j => if j < r then 0 else M r j)) ∧
      (∀ i, i < r → v i = 0) ∧ v r = 1 ∧
      ∀ i, r < i → RelErr (u p) (M i r / M r r) (v i) := by
  obtain ⟨out, hr, WL, WU, v, hs⟩ := exists_exec_alloc I p 1 (fun zbuf => ((do
    ins (.lit p ⟨zbuf, 0⟩ 0)
    ifThenElse p .eq ⟨S, so + k + n * k⟩ ⟨zbuf, 0⟩
      (luColumnZero p n k S L U so lo uo)
      (luColumn p n k S L U so lo uo)) : Builder P ι ℕ ℕ Unit).run) st
    (GuardedEliminationRounding.ColumnResult dec u p st.store L U lo.eval uo.eval
      ⟨k.eval, hk⟩ M B D)
    (fun σ hσ => GuardedEliminationRounding.exec_luColumnTotal_body I h n k hi p st.store
      σ S L U so lo uo M B D hk hM hB hD hSL hSU hLU hσ)
  refine ⟨out, WL, WU, v, ?_, hs⟩
  change exec I (.seq (.alloc p 1 _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

/-- The actual zero-guarded Schur step succeeds for every stored decoded square matrix
in the standard relative-error model with every scalar result in range. A decoded zero pivot
skips the update and leaves the decoded matrix unchanged; a nonzero pivot executes the saved
row/column rank-one routine. The only net store effect is one full matrix block write, and
all scratch is released. Arithmetic charges are arbitrary and no upper bound on roundoff or
nonsingularity premise is required. [Higham2002, §2.2; GolubVanLoan2013, §3.2]. -/
theorem IsRelErrSem.exec_schurStepTotal {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (R : ℕ) (off k : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : HoldsDecoded st.store dec p R off.eval M) :
    ∃ (out : St P K C) (W : Array K), exec I (schurStepTotal p n R off k).run st = some out ∧
      W.size = n.eval * n.eval ∧ st.store.writeBlock p R off.eval W = some out.store ∧
      HoldsDecoded out.store dec p R off.eval (unflatten n.eval n.eval (W.map (dec p))) ∧
      (M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ = 0 → unflatten n.eval n.eval (W.map (dec p)) = M) := by
  obtain ⟨out, W, hr, hWs, hw, hM', hcases⟩ :=
    h.exec_schurStepTotal_trace I p st n R off k M hk hM
  refine ⟨out, W, hr, hWs, hw, hM', fun hz => ?_⟩
  rcases hcases with hzero | hnonzero
  · exact hzero.2
  · exact (hnonzero.1 hz).elim

end NLAlib.Computation
