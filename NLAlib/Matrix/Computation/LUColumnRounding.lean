/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.LU
public import NLAlib.Computation.Contract

/-!
# Rounded LU column materialization

The actual stored LU column routine uses exact index controls to choose triangular zeros,
a unit diagonal and rounded divisions below it. The result proves successful execution and
the complete two-factor output frame for arbitrary scalar words and arithmetic charges.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_luColumn`: rounded success and division witnesses.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

namespace LUColumnRounding

open LUColumn

private def lowerWord {N : ℕ} (z o : K) (qv : Fin N → K) (r i : Fin N) : K :=
  if i < r then z else if i = r then o else qv i

private def upperWord {N : ℕ} (z : K) (M : Matrix (Fin N) (Fin N) K)
    (r i : Fin N) : K := if i < r then z else M r i

private structure ColumnWords (I : Interp P ι K C) (dec : P → K → ℝ) (p : P)
    {N : ℕ} (M : Matrix (Fin N) (Fin N) K) (r : Fin N)
    (z o cw : K) (iw qv : Fin N → K) : Prop where
  zero : I.sem.lit p 0 = some z
  one : I.sem.lit p 1 = some o
  pivot_lit : I.sem.lit p r.val = some cw
  pivot_dec : dec p cw = r.val
  index_lit : ∀ i, I.sem.lit p i.val = some (iw i)
  index_dec : ∀ i, dec p (iw i) = i.val
  divide : ∀ i, I.sem.bin p .div (M i r) (M r r) = some (qv i)
  lt : ∀ x y, I.sem.cmp p .lt x y = some (decide (dec p x < dec p y))
  eq : ∀ x y, I.sem.cmp p .eq x y = some (decide (dec p x = dec p y))

private theorem exec_luEntry {P ι : Type} [DecidableEq P] {C : Type} [AddMonoid C]
    (I : Interp P ι K C) {dec : P → K → ℝ} (p : P) (st : St P K C)
    (n k i : IExp ℕ) (S L U ctrl : ℕ) (so lo uo : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) K) (hk : k.eval < n.eval) (hi : i.eval < n.eval)
    (z o cw : K) (iw qv : Fin n.eval → K)
    (hcw : ColumnWords I dec p M ⟨k.eval, hk⟩ z o cw iw qv)
    (hM : Holds st.store p S so.eval M)
    (hc : st.store.read p ctrl 1 = some cw)
    (hctrl : st.store.shape[ctrl]? = some (p, 2))
    (hL : Writable st.store p L lo.eval (n.eval * n.eval))
    (hU : Writable st.store p U uo.eval (n.eval * n.eval))
    (hSC : S ≠ ctrl) (hSL : S ≠ L) :
    ∃ (out : St P K C) (s₁ s₂ : Store P K),
      exec I (luColumnEntry p n k i S L U ctrl so lo uo).run st = some out ∧
      st.store.write p ctrl 0 (iw ⟨i.eval, hi⟩) = some s₁ ∧
      s₁.write p L (lo.eval + i.eval + n.eval * k.eval)
        (lowerWord z o qv ⟨k.eval, hk⟩ ⟨i.eval, hi⟩) = some s₂ ∧
      s₂.write p U (uo.eval + k.eval + n.eval * i.eval)
        (upperWord z M ⟨k.eval, hk⟩ ⟨i.eval, hi⟩) = some out.store := by
  obtain ⟨s₁, hs₁⟩ := Store.exists_write_eq_some_of_getElem?_shape (iw ⟨i.eval, hi⟩) hctrl
    (by omega : 0 < 2)
  obtain ⟨lenL, hlenL, hltL⟩ := hL (i.eval + n.eval * k.eval)
    (Nat.add_mul_lt_mul_of_lt_of_lt hi hk)
  obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_getElem?_shape
    (i := lo.eval + i.eval + n.eval * k.eval)
    (lowerWord z o qv ⟨k.eval, hk⟩ ⟨i.eval, hi⟩)
    ((Store.shape_of_write_eq_some hs₁).symm ▸ hlenL) (by simpa [Nat.add_assoc] using hltL)
  obtain ⟨lenU, hlenU, hltU⟩ := hU (k.eval + n.eval * i.eval)
    (Nat.add_mul_lt_mul_of_lt_of_lt hk hi)
  obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_getElem?_shape
    (i := uo.eval + k.eval + n.eval * i.eval)
    (upperWord z M ⟨k.eval, hk⟩ ⟨i.eval, hi⟩)
    (((Store.shape_of_write_eq_some hs₂).trans (Store.shape_of_write_eq_some hs₁)).symm ▸ hlenU)
    (by simpa [Nat.add_assoc] using hltU)
  have hc₁ : s₁.read p ctrl 1 = some cw :=
    (Store.read_of_write_eq_some_of_ne hs₁ (Or.inr (by omega : 1 ≠ 0))).trans hc
  have hr₁ := Store.read_of_write_eq_some hs₁
  have hM₁ : Holds s₁ p S so.eval M := hM.write hs₁ (fun h => (hSC h.symm).elim)
  have hM₂ : Holds s₂ p S so.eval M := hM₁.write hs₂ (fun h => (hSL h.symm).elim)
  have hSrc := hM₁ ⟨i.eval, hi⟩ ⟨k.eval, hk⟩
  have hPiv := hM₁ ⟨k.eval, hk⟩ ⟨k.eval, hk⟩
  have hUpper := hM₂ ⟨k.eval, hk⟩ ⟨i.eval, hi⟩
  have hll : s₁.write p L (lo.eval + i.eval + n.eval * k.eval)
      (lowerWord z o qv ⟨k.eval, hk⟩ ⟨i.eval, hi⟩) = some s₂ := hs₂
  have huu : s₂.write p U (uo.eval + k.eval + n.eval * i.eval)
      (upperWord z M ⟨k.eval, hk⟩ ⟨i.eval, hi⟩) = some s₃ := hs₃
  have hlit := hcw.index_lit ⟨i.eval, hi⟩
  have hdi := hcw.index_dec ⟨i.eval, hi⟩
  have hdc := hcw.pivot_dec
  have hdiv := hcw.divide ⟨i.eval, hi⟩
  by_cases hik : i.eval < k.eval
  · let count := st.cnt + I.charge (.lit p) + I.charge (.cmp p) +
      I.charge (.lit p) + I.charge (.lit p)
    refine ⟨{ st with store := s₃, cnt := count }, s₁, s₂, ?_, hs₁, hs₂, hs₃⟩
    simp only [lowerWord, upperWord, Fin.lt_def, hik, if_true] at hll huu
    simp [run_luColumnEntry, exec, Instr.run, Instr.kind, IExp.eval, hcw.zero, hcw.one, hlit,
      hcw.lt, hcw.eq, hdi, hdc,
      hs₁, hll, huu, hr₁, hc₁, cmpStep, hik, count]
  · by_cases heq : i.eval = k.eval
    · let count := st.cnt + I.charge (.lit p) + I.charge (.cmp p) +
        I.charge (.cmp p) + I.charge (.lit p) + I.charge (.copy p)
      refine ⟨{ st with store := s₃, cnt := count }, s₁, s₂,
        ?_, hs₁, hs₂, hs₃⟩
      simp [lowerWord, upperWord, heq] at hll huu
      simp only [heq] at hs₁ hr₁ hUpper hlit hdi
      simp [run_luColumnEntry, exec, Instr.run, Instr.kind,
        IExp.eval, hcw.zero, hcw.one, hlit, hcw.lt, hcw.eq, hdi, hdc, hs₁, hll, huu,
        hr₁, hc₁, cmpStep, heq, hUpper, count]
    · let count := st.cnt + I.charge (.lit p) + I.charge (.cmp p) +
        I.charge (.cmp p) + I.charge (.bin p .div) + I.charge (.copy p)
      refine ⟨{ st with store := s₃, cnt := count }, s₁, s₂,
        ?_, hs₁, hs₂, hs₃⟩
      simp only [lowerWord, upperWord, Fin.lt_def, Fin.ext_iff, hik, heq, if_false] at hll huu
      simp [run_luColumnEntry, exec, Instr.run, Instr.kind,
        IExp.eval, hcw.zero, hcw.one, hlit, hcw.lt, hcw.eq, hdi, hdc, hs₁, hll, huu,
        hr₁, hc₁, cmpStep, hik, heq,
        hSrc, hPiv, hUpper, hdiv, count]

private theorem exists_exec_luColumn_loop {P ι : Type} [DecidableEq P]
    {C : Type} [AddMonoid C] (I : Interp P ι K C) {dec : P → K → ℝ}
    (p : P) (st : St P K C) (n k : IExp ℕ) (S L U ctrl : ℕ) (so lo uo : IExp ℕ)
    (M B D : Matrix (Fin n.eval) (Fin n.eval) K) (hk : k.eval < n.eval)
    (z o cw : K) (iw qv : Fin n.eval → K)
    (hcw : ColumnWords I dec p M ⟨k.eval, hk⟩ z o cw iw qv)
    (hM : Holds st.store p S so.eval M)
    (hB : Holds st.store p L lo.eval B) (hD : Holds st.store p U uo.eval D)
    (hc : st.store.read p ctrl 1 = some cw)
    (hctrl : st.store.shape[ctrl]? = some (p, 2))
    (hSC : S ≠ ctrl) (hLC : L ≠ ctrl) (hUC : U ≠ ctrl)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    ∃ out, exec I (.loop n fun i =>
        (luColumnEntry p n k (.var i) S L U ctrl so lo uo).run) st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ q b idx, b ≠ ctrl →
        (b ≠ L ∨ idx < lo.eval ∨ lo.eval + n.eval * n.eval ≤ idx) →
        (b ≠ U ∨ idx < uo.eval ∨ uo.eval + n.eval * n.eval ≤ idx) →
        out.store.read q b idx = st.store.read q b idx) ∧
      Holds out.store p L lo.eval (B.updateCol ⟨k.eval, hk⟩ (lowerWord z o qv ⟨k.eval, hk⟩)) ∧
      Holds out.store p U uo.eval (D.updateRow ⟨k.eval, hk⟩ (upperWord z M ⟨k.eval, hk⟩)) := by
  let r : Fin n.eval := ⟨k.eval, hk⟩
  let R := fun t (σ : St P K C) => σ.store.shape = st.store.shape ∧
    (∀ q b idx, b ≠ ctrl →
      (b ≠ L ∨ idx < lo.eval ∨ lo.eval + n.eval * n.eval ≤ idx) →
      (b ≠ U ∨ idx < uo.eval ∨ uo.eval + n.eval * n.eval ≤ idx) →
      σ.store.read q b idx = st.store.read q b idx) ∧
    σ.store.read p ctrl 1 = some cw ∧
    Holds σ.store p L lo.eval (columnPrefix B r (lowerWord z o qv r) t) ∧
    Holds σ.store p U uo.eval (rowPrefix D r (upperWord z M r) t)
  have h0 : R 0 st := ⟨rfl, fun _ _ _ _ _ _ => rfl, hc,
    fun i j => by simpa only [columnPrefix, Nat.not_lt_zero, and_false, if_false] using hB i j,
    fun i j => by simpa only [rowPrefix, Nat.not_lt_zero, and_false, if_false] using hD i j⟩
  obtain ⟨out, hr, hsh, hfr, -, hBL, hDU⟩ := exists_exec_loop_eq_some_of_forall I R h0
    (fun t ht σ hR => by
      obtain ⟨hsh, hfr, hc, hBL, hDU⟩ := hR
      have hMσ : Holds σ.store p S so.eval M := fun i j =>
        (hfr p S _ hSC (Or.inl hSL) (Or.inl hSU)).trans (hM i j)
      obtain ⟨out, s₁, s₂, hr, h₁, h₂, h₃⟩ := exec_luEntry I p σ n k (.var t)
        S L U ctrl so lo uo M hk ht z o cw iw qv hcw hMσ hc (hsh ▸ hctrl) hBL.writable hDU.writable
        hSC hSL
      have hB₁ := hBL.write h₁ (fun h => (hLC h.symm).elim)
      have hD₁ := hDU.write h₁ (fun h => (hUC h.symm).elim)
      have hB₂ := holds_replaceEntry (r := ⟨t, ht⟩) (c := r) hB₁ h₂
      have hD₂ := hD₁.write h₂ (fun h => (hLU h).elim)
      refine ⟨out, hr,
        (Store.shape_of_write_eq_some h₃).trans ((Store.shape_of_write_eq_some h₂).trans
          ((Store.shape_of_write_eq_some h₁).trans hsh)), ?_, ?_, ?_, ?_⟩
      · intro q b idx hbC hbL hbU
        have htL := Nat.add_mul_lt_mul_of_lt_of_lt ht hk
        have htU := Nat.add_mul_lt_mul_of_lt_of_lt hk ht
        rw [Store.read_of_write_eq_some_of_ne h₃ (by
            rcases hbU with hbU | hbU | hbU
            · exact Or.inl hbU
            · exact Or.inr (by dsimp; omega)
            · exact Or.inr (by dsimp; omega)),
          Store.read_of_write_eq_some_of_ne h₂ (by
            rcases hbL with hbL | hbL | hbL
            · exact Or.inl hbL
            · exact Or.inr (by dsimp; omega)
            · exact Or.inr (by dsimp; omega)),
          Store.read_of_write_eq_some_of_ne h₁ (Or.inl hbC)]
        exact hfr q b idx hbC hbL hbU
      · rw [Store.read_of_write_eq_some_of_ne h₃ (Or.inl hUC.symm),
          Store.read_of_write_eq_some_of_ne h₂ (Or.inl hLC.symm),
          Store.read_of_write_eq_some_of_ne h₁ (Or.inr (by omega : 1 ≠ 0))]
        exact hc
      · have hB₃ := hB₂.write h₃ (fun h => (hLU h.symm).elim)
        change Holds out.store p L lo.eval
          (replaceEntry (columnPrefix B r (lowerWord z o qv r) t) ⟨t, ht⟩ r
            ((lowerWord z o qv r) ⟨t, ht⟩)) at hB₃
        rw [replaceEntry_columnPrefix B r ⟨t, ht⟩ (lowerWord z o qv r)] at hB₃
        exact hB₃
      · have hD₃ := holds_replaceEntry (r := r) (c := ⟨t, ht⟩) hD₂ h₃
        change Holds out.store p U uo.eval
          (replaceEntry (rowPrefix D r (upperWord z M r) t) r ⟨t, ht⟩
            ((upperWord z M r) ⟨t, ht⟩)) at hD₃
        rw [replaceEntry_rowPrefix D r ⟨t, ht⟩ (upperWord z M r)] at hD₃
        exact hD₃)
  refine ⟨out, hr, hsh, hfr, fun i j => ?_, fun i j => ?_⟩
  · simpa only [columnPrefix, i.isLt, and_true, Matrix.updateCol_apply] using hBL i j
  · simpa only [rowPrefix, j.isLt, and_true, Matrix.updateRow_apply] using hDU i j

private theorem factor_writeBlocks {N : ℕ} {initial final : Store P K} {p : P}
    {L U lo uo : ℕ} {B D : Matrix (Fin N) (Fin N) K} (hLU : L ≠ U)
    (hsh : final.shape = initial.shape) (hB : Holds final p L lo B)
    (hD : Holds final p U uo D)
    (hfr : ∀ q b idx, (b ≠ L ∨ idx < lo ∨ lo + N * N ≤ idx) →
      (b ≠ U ∨ idx < uo ∨ uo + N * N ≤ idx) →
      final.read q b idx = initial.read q b idx) :
    ∃ (WL WU : Array K), WL.size = N * N ∧ WU.size = N * N ∧
      initial.writeBlocks p [(L, lo, N * N), (U, uo, N * N)] [WL, WU] = some final := by
  obtain ⟨WL, hLs, hLflat, -, -⟩ := hB.exists_array
  obtain ⟨WU, hUs, hUflat, -, -⟩ := hD.exists_array
  refine ⟨WL, WU, hLs, hUs, ?_⟩
  refine Store.writeBlocks_eq_some_of_read
    (bs := [(L, lo, N * N), (U, uo, N * N)]) (ys := [WL, WU])
    (.cons hLs (.cons hUs .nil)) ?_ hsh ?_ ?_
  · simp [List.pairwise_cons, blockDisjoint, hLU]
  · intro k x y hx hy t ht
    rcases k with _ | k
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      subst x; subst y
      exact hLflat t ht
    · rcases k with _ | k
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx hy
        subst x; subst y
        exact hUflat t ht
      · simp at hx
  · intro q b idx hout
    exact hfr q b idx (hout _ List.mem_cons_self)
      (hout _ (List.mem_cons_of_mem _ List.mem_cons_self))

private theorem exists_exec_luColumn_body {P ι : Type} [DecidableEq P]
    {C : Type} [AddMonoid C] (I : Interp P ι K C) {dec : P → K → ℝ}
    (p : P) (st : St P K C) (n k : IExp ℕ) (S L U ctrl : ℕ) (so lo uo : IExp ℕ)
    (M B D : Matrix (Fin n.eval) (Fin n.eval) K) (hk : k.eval < n.eval)
    (z o cw : K) (iw qv : Fin n.eval → K)
    (hcw : ColumnWords I dec p M ⟨k.eval, hk⟩ z o cw iw qv)
    (hM : Holds st.store p S so.eval M)
    (hB : Holds st.store p L lo.eval B) (hD : Holds st.store p U uo.eval D)
    (hctrl : st.store.shape[ctrl]? = some (p, 2))
    (hSC : S ≠ ctrl) (hLC : L ≠ ctrl) (hUC : U ≠ ctrl)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    ∃ out, exec I (do
        ins (.litIdx p ⟨ctrl, 1⟩ k)
        forRange n fun i => luColumnEntry p n k (.var i) S L U ctrl so lo uo).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ q b idx, b ≠ ctrl →
        (b ≠ L ∨ idx < lo.eval ∨ lo.eval + n.eval * n.eval ≤ idx) →
        (b ≠ U ∨ idx < uo.eval ∨ uo.eval + n.eval * n.eval ≤ idx) →
        out.store.read q b idx = st.store.read q b idx) ∧
      Holds out.store p L lo.eval (B.updateCol ⟨k.eval, hk⟩ (lowerWord z o qv ⟨k.eval, hk⟩)) ∧
      Holds out.store p U uo.eval (D.updateRow ⟨k.eval, hk⟩ (upperWord z M ⟨k.eval, hk⟩)) := by
  obtain ⟨s₁, h₁⟩ := Store.exists_write_eq_some_of_getElem?_shape cw hctrl
    (by omega : 1 < 2)
  let start : St P K C := { st with store := s₁, cnt := st.cnt + I.charge (.lit p) }
  obtain ⟨out, hr, hsh, hfr, hBL, hDU⟩ := exists_exec_luColumn_loop I p start n k S L U ctrl
    so lo uo M B D hk z o cw iw qv hcw (hM.write h₁ (fun h => (hSC h.symm).elim))
    (hB.write h₁ (fun h => (hLC h.symm).elim)) (hD.write h₁ (fun h => (hUC h.symm).elim))
    (Store.read_of_write_eq_some h₁) ((Store.shape_of_write_eq_some h₁).symm ▸ hctrl)
    hSC hLC hUC hSL hSU hLU
  refine ⟨out, ?_, hsh.trans (Store.shape_of_write_eq_some h₁), ?_, hBL, hDU⟩
  · change exec I (.seq (.instr (.litIdx p ⟨ctrl, 1⟩ k)) (.seq (.loop n _) .skip)) st = some out
    rw [exec_seq_instr_litIdx I hcw.pivot_lit h₁, exec_seq_skip]
    exact hr
  · intro q b idx hbC hbL hbU
    exact (hfr q b idx hbC hbL hbU).trans
      (Store.read_of_write_eq_some_of_ne h₁ (Or.inl hbC))

private theorem exec_luColumn_words {P ι : Type} [DecidableEq P] {C : Type} [AddMonoid C]
    (I : Interp P ι K C) {dec : P → K → ℝ} (p : P) (st : St P K C)
    (n k : IExp ℕ) (S L U : ℕ) (so lo uo : IExp ℕ)
    (M B D : Matrix (Fin n.eval) (Fin n.eval) K) (hk : k.eval < n.eval)
    (z o cw : K) (iw qv : Fin n.eval → K)
    (hcw : ColumnWords I dec p M ⟨k.eval, hk⟩ z o cw iw qv)
    (hM : Holds st.store p S so.eval M)
    (hB : Holds st.store p L lo.eval B) (hD : Holds st.store p U uo.eval D)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    let r : Fin n.eval := ⟨k.eval, hk⟩
    let B' := B.updateCol r (lowerWord z o qv r)
    let D' := D.updateRow r (upperWord z M r)
    ∃ (out : St P K C) (WL WU : Array K), exec I (luColumn p n k S L U so lo uo).run st = some out ∧
      WL.size = n.eval * n.eval ∧ WU.size = n.eval * n.eval ∧
      st.store.writeBlocks p [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
        [WL, WU] = some out.store ∧
      Holds out.store p L lo.eval B' ∧ Holds out.store p U uo.eval D' := by
  dsimp only
  let r : Fin n.eval := ⟨k.eval, hk⟩
  let B' := B.updateCol r (lowerWord z o qv r)
  let D' := D.updateRow r (upperWord z M r)
  have hSsize := Store.lt_size_of_read_eq_some (hM r r)
  have hLsize := Store.lt_size_of_read_eq_some (hB r r)
  have hUsize := Store.lt_size_of_read_eq_some (hD r r)
  have halloc := exists_exec_alloc I p 2 (fun ctrl => ((do
      ins (.litIdx p ⟨ctrl, 1⟩ k)
      forRange n fun i => luColumnEntry p n k (.var i) S L U ctrl so lo uo) :
        Builder P ι ℕ ℕ Unit).run) st
    (fun store => ∃ (WL WU : Array K),
      WL.size = n.eval * n.eval ∧ WU.size = n.eval * n.eval ∧
      st.store.writeBlocks p
      [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)] [WL, WU] =
        some store ∧ Holds store p L lo.eval B' ∧ Holds store p U uo.eval D') (by
      intro σ hσ
      have pushH {buf off : ℕ} {A : Matrix (Fin n.eval) (Fin n.eval) K}
          (h : Holds st.store p buf off A) (hb : buf < st.store.size) :
          Holds σ.store p buf off A := fun i j => by
        rw [hσ, Store.read_push_of_lt hb]; exact h i j
      obtain ⟨out, hr, hsh, hfr, hBL, hDU⟩ := exists_exec_luColumn_body I p σ n k S L U
        st.store.size so lo uo M B D hk z o cw iw qv hcw (pushH hM hSsize) (pushH hB hLsize)
        (pushH hD hUsize) (hσ ▸ Store.getElem?_shape_push_size st.store p 2)
        (Nat.ne_of_lt hSsize) (Nat.ne_of_lt hLsize) (Nat.ne_of_lt hUsize) hSL hSU hLU
      have hsize : out.store.size = st.store.size + 1 := by
        simpa only [Store.size_shape, hσ, Array.size_push] using congrArg Array.size hsh
      have hBLpop : Holds out.store.pop p L lo.eval B' := fun i j => by
        rw [Store.read_pop_of_lt (by omega)]; exact hBL i j
      have hDUpop : Holds out.store.pop p U uo.eval D' := fun i j => by
        rw [Store.read_pop_of_lt (by omega)]; exact hDU i j
      have hpopshape : Store.shape out.store.pop = st.store.shape := by
        rw [Store.shape_pop, hsh, hσ]
        simp only [Store.shape, Array.map_push, Array.pop_push]
      have hpopframe : ∀ q b idx,
          (b ≠ L ∨ idx < lo.eval ∨ lo.eval + n.eval * n.eval ≤ idx) →
          (b ≠ U ∨ idx < uo.eval ∨ uo.eval + n.eval * n.eval ≤ idx) →
          Store.read out.store.pop q b idx = st.store.read q b idx := by
        intro q b idx hbL hbU
        by_cases hb : b < st.store.size
        · rw [Store.read_pop_of_lt (by omega), hfr q b idx (by omega) hbL hbU,
            hσ, Store.read_push_of_lt hb]
        · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
            Store.read_eq_none_of_size_le (by omega)]
      obtain ⟨WL, WU, hLs, hUs, hw⟩ :=
        factor_writeBlocks hLU hpopshape hBLpop hDUpop hpopframe
      exact ⟨out, hr, WL, WU, hLs, hUs, hw, hBLpop, hDUpop⟩)
  obtain ⟨out, hr, WL, WU, hLs, hUs, hw, hBL, hDU⟩ := halloc
  refine ⟨out, WL, WU, ?_, hLs, hUs, hw, hBL, hDU⟩
  change exec I (.seq (.alloc p 2 _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr


end LUColumnRounding

/-- With a nonzero decoded pivot, readable decoded source and initialized separate factors,
the actual LU column routine succeeds under standard relative-error semantics with every
scalar result in range. Exact integer literals through the matrix size select the triangular
branches and write the exact unit diagonal. Above-diagonal entries are zero; each lower
entry has relative error at most $u_p$ from division by the original pivot. The upper row is
copied with its left prefix cleared. The only store effects are the two full factor writes,
in lower-then-upper order. Arithmetic charges and the word carrier are arbitrary.
[Higham2002, §2.2; GolubVanLoan2013, §3.2]. -/
theorem IsRelErrSem.exec_luColumn {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (p : P) (st : St P K C)
    (S L U : ℕ) (so lo uo : IExp ℕ)
    (M B D : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : HoldsDecoded st.store dec p S so.eval M)
    (hp : M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ ≠ 0)
    (hB : HoldsDecoded st.store dec p L lo.eval B)
    (hD : HoldsDecoded st.store dec p U uo.eval D)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    let r : Fin n.eval := ⟨k.eval, hk⟩
    ∃ (out : St P K C) (WL WU : Array K) (v : Fin n.eval → ℝ),
      exec I (luColumn p n k S L U so lo uo).run st = some out ∧
      WL.size = n.eval * n.eval ∧ WU.size = n.eval * n.eval ∧
      st.store.writeBlocks p [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
        [WL, WU] = some out.store ∧
      HoldsDecoded out.store dec p L lo.eval (B.updateCol r v) ∧
      HoldsDecoded out.store dec p U uo.eval (D.updateRow r (fun j => if j < r then 0 else M r j)) ∧
      (∀ i, i < r → v i = 0) ∧ v r = 1 ∧
      ∀ i, r < i → RelErr (u p) (M i r / M r r) (v i) := by
  classical
  dsimp only
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
  obtain ⟨cw, hcw, hdcw⟩ := hi.intLit p k.eval (by omega)
  choose iw hiw hdiw using fun i : Fin n.eval => hi.intLit p i.val i.isLt.le
  choose qv hqv using fun i : Fin n.eval =>
    h.bin_ok p .div (Mw i r) (Mw r r) trivial (fun _ => by rwa [hdMw]) trivial
  have hctx : LUColumnRounding.ColumnWords I dec p Mw r z o cw iw qv :=
    ⟨hz, by simpa only [Nat.cast_one] using ho, hcw, hdcw, hiw, hdiw, hqv,
      h.cmp_lt p, h.cmp_eq p⟩
  obtain ⟨out, WL, WU, hr, hLs, hUs, hw, hL, hU⟩ :=
    LUColumnRounding.exec_luColumn_words I p st n k S L U
    so lo uo Mw Bw Dw hk z o cw iw qv hctx hMw hBw hDw hSL hSU hLU
  let v : Fin n.eval → ℝ := fun i => dec p (LUColumnRounding.lowerWord z o qv r i)
  have hv0 : ∀ i, i < r → v i = 0 := fun i hi => by
    simp only [v, LUColumnRounding.lowerWord, if_pos hi, hdz]
  have hv1 : v r = 1 := by
    simpa only [v, LUColumnRounding.lowerWord, lt_irrefl, if_false, if_true, Nat.cast_one] using hdo
  refine ⟨out, WL, WU, v, hr, hLs, hUs, hw, ?_, ?_, hv0, hv1, ?_⟩
  · intro i j
    refine ⟨_, hL i j, ?_⟩
    change dec p ((Matrix.updateCol Bw r (LUColumnRounding.lowerWord z o qv r)) i j) =
      (B.updateCol r v) i j
    by_cases hj : j = r
    · subst j
      rw [Matrix.updateCol_self, Matrix.updateCol_self]
    · rw [Matrix.updateCol_ne hj, Matrix.updateCol_ne hj, hdBw]
  · intro i j
    refine ⟨_, hU i j, ?_⟩
    change dec p ((Matrix.updateRow Dw r (LUColumnRounding.upperWord z Mw r)) i j) =
      (D.updateRow r (fun j => if j < r then 0 else M r j)) i j
    by_cases hir : i = r
    · subst i
      rw [Matrix.updateRow_self, Matrix.updateRow_self]
      by_cases hj : j < r <;> simp only [LUColumnRounding.upperWord, hj, ↓reduceIte, hdz, hdMw]
    · rw [Matrix.updateRow_ne hir, Matrix.updateRow_ne hir, hdDw]
  · intro i hri
    change RelErr (u p) (M i r / M r r) (dec p (LUColumnRounding.lowerWord z o qv r i))
    rw [LUColumnRounding.lowerWord]
    split_ifs with hlt heq
    · exact (not_lt_of_ge hri.le hlt).elim
    · exact (hri.ne heq.symm).elim
    simpa only [RelErr, BinOp.realOp, hdMw] using
      h.bin_err p .div (Mw i r) (Mw r r) (qv i) trivial (hqv i)

/-- A rounded quotient of two decoded values whose magnitudes are ordered has magnitude at
most $1+u$. This includes the total quotient at a zero denominator and requires no upper bound
on $u$. It is the multiplier estimate after a maximal-column pivot choice under the standard
model [Higham2002, §9.3]. -/
theorem abs_le_one_add_of_relErr_div {u a b z : ℝ} (h : RelErr u (a / b) z)
    (hab : |a| ≤ |b|) : |z| ≤ 1 + u := by
  obtain ⟨δ, hδ, he⟩ := h
  have hu : 0 ≤ u := (abs_nonneg δ).trans hδ
  have hratio : |a / b| ≤ 1 := by
    by_cases hb : b = 0
    · simp only [hb, div_zero, abs_zero, zero_le_one]
    · rw [abs_div, div_le_one (abs_pos.mpr hb)]
      exact hab
  have hfac : |1 + δ| ≤ 1 + u :=
    (abs_add_le 1 δ).trans (add_le_add (by norm_num) hδ)
  calc
    |z| = |a / b| * |1 + δ| := by rw [he, abs_mul]
    _ ≤ |a / b| * (1 + u) := mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
    _ ≤ 1 * (1 + u) := mul_le_mul_of_nonneg_right hratio (by linarith)
    _ = 1 + u := one_mul _

end NLAlib.Computation
