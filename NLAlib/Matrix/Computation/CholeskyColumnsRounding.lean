/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyColumns
public import NLAlib.Matrix.Computation.CholeskyRounding
public import NLAlib.Computation.CopyStride

/-!
# Rounded Cholesky columns from a stored residual

The actual builder copies the residual column, rounds its diagonal square root, then divides
its lower suffix. The packed column frame includes the unchanged copied upper prefix.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_choleskyColumnOfResidual`: success and local witnesses.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- A copied column followed by a diagonal singleton and normalized suffix write has one
packed column as its complete net store effect, for arbitrary word carriers. -/
theorem writeBlock_column_of_normalize
    {s s₁ s₂ mid : Store P K} {p : P} {L off N k : ℕ}
    (xs : Fin N → K) (d : K) (ws : ℕ → K) (hk : k < N)
    (hshape : s₁.shape = s.shape)
    (hread : ∀ i : Fin N, s₁.read p L (off + i) = some (xs i))
    (hframe : ∀ q b i, (b ≠ L ∨ i < off ∨ off + N ≤ i) →
      s₁.read q b i = s.read q b i)
    (hm : s₁.writeBlock p L (off + k) #[d] = some mid)
    (hf : mid.writeBlock p L (off + (k + 1))
      ((List.range (N - (k + 1))).toArray.map ws) = some s₂) :
    s.writeBlock p L off (Array.ofFn fun i : Fin N =>
      if i.val < k then xs i else if i.val = k then d else ws (i.val - (k + 1))) = some s₂ := by
  apply Store.writeBlock_eq_some_of_read
    ((Store.shape_of_writeBlock_eq_some hf).trans
      ((Store.shape_of_writeBlock_eq_some hm).trans hshape))
  · intro j hj
    have hj' : j < N := by simpa using hj
    simp only [Array.getElem?_ofFn, hj', ↓reduceDIte]
    by_cases hjk : j < k
    · rw [if_pos hjk, Store.read_of_writeBlock_eq_some_of_ne hf (by simp; omega),
        Store.read_of_writeBlock_eq_some_of_ne hm (by simp; omega), hread ⟨j, hj'⟩]
    · rw [if_neg hjk]
      by_cases hje : j = k
      · subst j
        rw [if_pos rfl, Store.read_of_writeBlock_eq_some_of_ne hf (by simp)]
        have hd := Store.read_of_writeBlock_eq_some_of_lt (j := 0) hm (by simp)
        simpa using hd
      · rw [if_neg hje]
        have ht : j - (k + 1) < N - (k + 1) := by omega
        have hd := Store.read_of_writeBlock_eq_some_of_lt (j := j - (k + 1)) hf
          (by simpa using ht)
        simpa [show off + (k + 1) + (j - (k + 1)) = off + j by omega, ht] using hd
  · intro q b i hout
    simp only [Array.size_ofFn] at hout
    rw [Store.read_of_writeBlock_eq_some_of_ne hf (by simp; omega),
      Store.read_of_writeBlock_eq_some_of_ne hm (by simp; omega), hframe q b i hout]

/-- Under the standard model with every result in range and roundoff less than one, the
actual copied-column builder succeeds at a positive decoded pivot. The only net write is
the full column, with its original upper prefix, a positive rounded square root, and lower
entries rounded from division by that actual square root. Carriers and charges are arbitrary.
[Higham2002, §2.2; GolubVanLoan2013, §4.2]. -/
theorem IsRelErrSem.exec_choleskyColumnOfResidual {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (R L : ℕ) (ro lo k : IExp ℕ)
    (B : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hB : HoldsDecoded st.store dec p R ro.eval B) (hRL : R ≠ L)
    (hp : 0 < B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩) (hu : u p < 1)
    (hL : Writable st.store p L (lo.eval + n.eval * k.eval) n.eval) :
    ∃ (out : St P K C) (W : Fin n.eval → K),
      exec I (choleskyColumnOfResidual p n R L ro lo k).run st = some out ∧
      st.store.writeBlock p L (lo.eval + n.eval * k.eval) (Array.ofFn W) = some out.store ∧
      (∀ i, i.val < k.eval → dec p (W i) = B i ⟨k.eval, hk⟩) ∧
      0 < dec p (W ⟨k.eval, hk⟩) ∧
      RelErr (u p) (Real.sqrt (B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)) (dec p (W ⟨k.eval, hk⟩)) ∧
      ∀ i, k.eval < i.val → RelErr (u p)
        (B i ⟨k.eval, hk⟩ / dec p (W ⟨k.eval, hk⟩)) (dec p (W i)) := by
  classical
  choose Mw hMw hdMw using hB
  change Matrix (Fin n.eval) (Fin n.eval) K at Mw
  let r : Fin n.eval := ⟨k.eval, hk⟩
  obtain ⟨s₁, hr₁, hsh₁, hrds, hfr₁⟩ := exec_copyv_block I p st n R L
    (ro + n * k) (lo + n * k) (fun i hi => ⟨Mw ⟨i, hi⟩ r, by
      simpa only [IExp.eval_add, IExp.eval_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hMw ⟨i, hi⟩ r⟩) hRL hL
  have hread : ∀ i : Fin n.eval,
      s₁.store.read p L (lo.eval + n.eval * k.eval + i.val) = some (Mw i r) := by
    intro i
    exact (hrds i i.isLt).trans (by simpa only [IExp.eval_add, IExp.eval_mul,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hMw i r)
  have hdiag : Writable s₁.store p L (lo + k + n * k).eval 1 := by
    intro i hi
    have hh := hL k.eval hk
    rw [hsh₁]
    simpa [show i = 0 by omega, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  let xs : ℕ → ℝ := fun i => if hi : i < n.eval then B ⟨i, hi⟩ r else 0
  obtain ⟨out, d, ws, hr₂, hw, hdpos, hdrel, hwrel⟩ := h.exec_choleskyColumn I p s₁
    ⟨R, ro + k + n * k⟩ ⟨L, lo + k + n * k⟩ L
    (lo + (k + 1) + n * k) (n - (k + 1)) (B r r)
    (fun i => xs (k.eval + 1 + i)) hp hu
    ⟨Mw r r, (hfr₁ p R _ (Or.inl hRL)).trans (by simpa only [IExp.eval_add,
      IExp.eval_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hMw r r), hdMw r r⟩
    (by
      intro i hi
      have hi' : k.eval + 1 + i < n.eval := by change i < n.eval - (k.eval + 1) at hi; omega
      exact ⟨Mw ⟨k.eval + 1 + i, hi'⟩ r,
        by simpa [IExp.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hread ⟨k.eval + 1 + i, hi'⟩, by simpa [xs, hi'] using hdMw ⟨k.eval + 1 + i, hi'⟩ r⟩)
    hdiag (by simp [blockDisjoint_iff])
  obtain ⟨_, _, mid, hm, hf⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
  let W : Fin n.eval → K := fun i =>
    if i.val < k.eval then Mw i r else if i.val = k.eval then d else ws (i.val - (k.eval + 1))
  have hwrite := writeBlock_column_of_normalize (fun i => Mw i r) d ws hk hsh₁ hread
    (by simpa only [IExp.eval_add, IExp.eval_mul] using hfr₁)
    (by simpa [IExp.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm)
    (by simpa [IExp.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf)
  refine ⟨out, W, ?_, hwrite, ?_, ?_, ?_, ?_⟩
  · change exec I (.seq _ .skip) st = some out
    rw [exec_seq_skip]
    have hcomp : ExecutionComposable I (copyv p R (ro + n * k) L (lo + n * k) n) :=
      executionComposable_single I (fun _ => rfl)
    rw [hcomp, hr₁, Option.bind_some]
    exact hr₂
  · intro i hi
    simp only [W, if_pos hi, hdMw, r]
  · simpa [W, r] using hdpos
  · simpa [W, r] using hdrel
  · intro i hi
    have ht : i.val - (k.eval + 1) < n.eval - (k.eval + 1) := by omega
    have he : k.eval + 1 + (i.val - (k.eval + 1)) = i.val := by omega
    simpa [W, show ¬i.val < k.eval by omega, show i.val ≠ k.eval by omega,
      r, xs, he, i.isLt] using hwrel (i.val - (k.eval + 1)) ht

/-- Replacing the upper prefix of a packed column by one word preserves a single full-column
net write. Shapes and all outside cells determine the complete frame. -/
theorem writeBlock_column_prefix {s s₁ s₂ : Store P K}
    {p : P} {L off N k : ℕ} (xs : Fin N → K) (z : K) (hk : k ≤ N)
    (hw : s.writeBlock p L off (Array.ofFn xs) = some s₁)
    (hsh : s₂.shape = s₁.shape) (hr : ∀ i < k, s₂.read p L (off + i) = some z)
    (hf : ∀ q b i, (q ≠ p ∨ b ≠ L ∨ i < off ∨ off + k ≤ i) →
      s₂.read q b i = s₁.read q b i) :
    s.writeBlock p L off (Array.ofFn fun i : Fin N => if i.val < k then z else xs i) =
      some s₂ := by
  apply Store.writeBlock_eq_some_of_read (hsh.trans (Store.shape_of_writeBlock_eq_some hw))
  · intro i hi
    have hi' : i < N := by simpa using hi
    simp only [Array.getElem?_ofFn, hi', ↓reduceDIte]
    by_cases hik : i < k
    · rw [if_pos hik, hr i hik]
    · rw [if_neg hik, hf p L (off + i) (by omega)]
      simpa [hi'] using Store.read_of_writeBlock_eq_some_of_lt hw
        (j := i) (by simpa using hi')
  · intro q b i hout
    simp only [Array.size_ofFn] at hout
    rw [hf q b i (by omega)]
    exact Store.read_of_writeBlock_eq_some_of_ne hw (by simpa only [Array.size_ofFn] using hout)

/-- The actual full driver's copied-column operation followed by explicit upper zeroing
succeeds and writes a triangular column. The diagonal and lower arithmetic witnesses are
unchanged by those exact decoded zero literals. -/
theorem IsRelErrSem.exec_choleskyColumnOfResidual_zero_upper {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (R L : ℕ) (ro lo k : IExp ℕ)
    (B : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hB : HoldsDecoded st.store dec p R ro.eval B) (hRL : R ≠ L)
    (hp : 0 < B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩) (hu : u p < 1)
    (hL : Writable st.store p L (lo.eval + n.eval * k.eval) n.eval) :
    ∃ (out : St P K C) (W : Fin n.eval → K),
      exec I (do
        choleskyColumnOfResidual p n R L ro lo k
        forRange k fun i => ins (.lit p ⟨L, lo + n * k + IExp.var i⟩ 0)).run st = some out ∧
      st.store.writeBlock p L (lo.eval + n.eval * k.eval) (Array.ofFn W) = some out.store ∧
      (∀ i, i.val < k.eval → dec p (W i) = 0) ∧
      0 < dec p (W ⟨k.eval, hk⟩) ∧
      RelErr (u p) (Real.sqrt (B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)) (dec p (W ⟨k.eval, hk⟩)) ∧
      ∀ i, k.eval < i.val → RelErr (u p)
        (B i ⟨k.eval, hk⟩ / dec p (W ⟨k.eval, hk⟩)) (dec p (W i)) := by
  obtain ⟨s₁, W, hrun, hw, -, hdpos, hdrel, hrel⟩ :=
    h.exec_choleskyColumnOfResidual I p st n R L ro lo k B hk hB hRL hp hu hL
  obtain ⟨z, hz⟩ := h.lit_ok p 0 trivial
  have hdz : dec p z = 0 := by
    obtain ⟨δ, -, hd⟩ := h.lit_err p 0 z hz
    simpa only [Rat.cast_zero, zero_mul] using hd
  obtain ⟨store, hzero, hsh, hr, hf⟩ := exec_forRange_literal_zero I p z hz s₁ k L (lo + n * k)
    (fun i hi => by
      have hh := (hL.of_shape_eq (Store.shape_of_writeBlock_eq_some hw)) i (by omega)
      simpa only [IExp.eval_add, IExp.eval_mul] using hh)
  let out : St P K C := { s₁ with store := store, cnt := s₁.cnt + k.eval • I.charge (.lit p) }
  have hwrite := writeBlock_column_prefix W z (Nat.le_of_lt hk) hw hsh
    (by simpa only [IExp.eval_add, IExp.eval_mul] using hr)
    (by simpa only [IExp.eval_add, IExp.eval_mul] using hf)
  refine ⟨out, (fun i => if i.val < k.eval then z else W i), ?_, hwrite, ?_, ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := choleskyColumnOfResidual p n R L ro lo k) (fun _ => rfl),
      hrun, Option.bind_some]
    exact hzero
  · intro i hi
    simp only [if_pos hi, hdz]
  · simpa only [lt_self_iff_false, if_false] using hdpos
  · simpa only [lt_self_iff_false, if_false] using hdrel
  · intro i hi
    simpa only [lt_self_iff_false, if_false, if_neg (show ¬i.val < k.eval by omega)] using hrel i hi

end NLAlib.Computation
