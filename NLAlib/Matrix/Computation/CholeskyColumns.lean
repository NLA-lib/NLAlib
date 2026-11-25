/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.Cholesky
public import NLAlib.Computation.BLAS.Frames
public import NLAlib.Matrix.Factorizations.Cholesky

/-!
# Cholesky columns from a stored residual

A residual matrix supplies one column of a Cholesky factor. Copy its column to the factor's
output buffer, then normalize the diagonal and its suffix. The residual remains unchanged.
This is the column operation used by the full stored Cholesky loop.

## Main results

* `NLAlib.Computation.exec_choleskyColumnOfResidual`: exact success and one full column write.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Copy a stored residual column and normalize its diagonal and lower suffix. Entries above
the diagonal are copied as stored; the Cholesky invariant ensures they are zero.
The residual and factor buffers are distinct. [GolubVanLoan2013, §4.2]. -/
def choleskyColumnOfResidual {P ι VB VI : Type} (p : P) (n : IExp VI) (R L : VB)
    (ro lo k : IExp VI) : Builder P ι VB VI Unit := scope do
  copyv p R (ro + n * k) L (lo + n * k) n
  choleskyColumn p ⟨R, ro + k + n * k⟩ ⟨L, lo + k + n * k⟩
    L (lo + (k + 1) + n * k) (n - (k + 1))

variable {P ι : Type} [DecidableEq P]

private theorem column_write_of_normalize
    {s s₁ s₂ mid : Store P ℝ} {p : P} {L off N k : ℕ} {a : ℝ}
    (xs : ℕ → ℝ) (hk : k < N) (ha : xs k = a)
    (hshape : s₁.shape = s.shape)
    (hread : ∀ i < N, s₁.read p L (off + i) = some (xs i))
    (hframe : ∀ q b i, (b ≠ L ∨ i < off ∨ off + N ≤ i) →
      s₁.read q b i = s.read q b i)
    (hm : s₁.writeBlock p L (off + k) #[Real.sqrt a] = some mid)
    (hf : mid.writeBlock p L (off + (k + 1))
      ((List.range (N - (k + 1))).toArray.map fun i =>
        xs (k + 1 + i) / Real.sqrt a) = some s₂) :
    s.writeBlock p L off (Array.ofFn fun i : Fin N =>
      if (i : ℕ) < k then xs i else xs i / Real.sqrt a) = some s₂ := by
  apply Store.writeBlock_eq_some_of_read
    ((Store.shape_of_writeBlock_eq_some hf).trans
      ((Store.shape_of_writeBlock_eq_some hm).trans hshape))
  · intro j hj
    have hj' : j < N := by simpa using hj
    simp only [Array.getElem?_ofFn, hj', ↓reduceDIte]
    by_cases hjk : j < k
    · rw [if_pos hjk, Store.read_of_writeBlock_eq_some_of_ne hf (by simp; omega),
        Store.read_of_writeBlock_eq_some_of_ne hm (by simp; omega), hread j hj']
    · rw [if_neg hjk]
      by_cases hje : j = k
      · subst j
        rw [Store.read_of_writeBlock_eq_some_of_ne hf (by simp)]
        have hd := Store.read_of_writeBlock_eq_some_of_lt (j := 0) hm (by simp)
        simpa [ha, Real.div_sqrt] using hd
      · have ht : j - (k + 1) < N - (k + 1) := by omega
        have hd := Store.read_of_writeBlock_eq_some_of_lt (j := j - (k + 1)) hf
          (by simpa using ht)
        simpa [show k + 1 + (j - (k + 1)) = j by omega,
          show off + (k + 1) + (j - (k + 1)) = off + j by omega, ht] using hd
  · intro q b i hout
    simp only [Array.size_ofFn] at hout
    rw [Store.read_of_writeBlock_eq_some_of_ne hf (by simp; omega),
      Store.read_of_writeBlock_eq_some_of_ne hm (by simp; omega), hframe q b i hout]

/-- A stored residual matrix with a positive diagonal pivot supplies one factor column.
The full column is written: its entries above the diagonal are copied unchanged and its
remaining entries are divided by the positive square root of the pivot. All other store
cells, including the residual matrix, are unchanged. No previous factor columns need be
initialized. [GolubVanLoan2013, §4.2]. -/
theorem exec_choleskyColumnOfResidual (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (R L : ℕ) (ro lo k : IExp ℕ)
    (B : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hB : Holds st.store p R ro.eval B) (hRL : R ≠ L)
    (hp : 0 < B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)
    (hL : Writable st.store p L (lo.eval + n.eval * k.eval) n.eval) :
    ∃ out : St P ℝ (OpCount P ι),
      exec I (choleskyColumnOfResidual p n R L ro lo k).run st = some out ∧
      st.store.writeBlock p L (lo.eval + n.eval * k.eval)
        (Array.ofFn fun i : Fin n.eval => if (i : ℕ) < k.eval then B i ⟨k.eval, hk⟩
          else B i ⟨k.eval, hk⟩ / Real.sqrt (B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)) =
            some out.store := by
  let a := B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩
  let xs : ℕ → ℝ := fun i => if hi : i < n.eval then B ⟨i, hi⟩ ⟨k.eval, hk⟩ else 0
  obtain ⟨s₁, hr₁, hsh₁, hrds, hfr₁, _⟩ := exec_copyv_frame I hc p st n R L
    (ro + n * k) (lo + n * k) xs
    (fun i hi => by
      simpa [xs, hi, IExp.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hB ⟨i, hi⟩ ⟨k.eval, hk⟩) hRL hL
  have hdiag : Writable s₁.store p L (lo + k + n * k).eval 1 := by
    intro i hi
    have := hL k.eval hk
    rw [hsh₁]
    simpa [show i = 0 by omega, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  have hxs : ∀ i < (n - (k + 1)).eval,
      s₁.store.read p L ((lo + (k + 1) + n * k).eval + i) = some (xs (k.eval + 1 + i)) := by
    intro i hi
    have hi' : k.eval + 1 + i < n.eval := by
      change i < n.eval - (k.eval + 1) at hi
      omega
    simpa [IExp.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hrds (k.eval + 1 + i) hi'
  have hpread : s₁.store.read p R (ro + k + n * k).eval = some a := by
    rw [hfr₁ p R _ (Or.inl hRL)]
    exact hB ⟨k.eval, hk⟩ ⟨k.eval, hk⟩
  obtain ⟨out, hr₂, hw, _⟩ := exec_choleskyColumn I hI hc p s₁
    ⟨R, ro + k + n * k⟩ ⟨L, lo + k + n * k⟩ L
    (lo + (k + 1) + n * k) (n - (k + 1)) a
    (fun i => xs (k.eval + 1 + i)) hp hpread hxs hdiag
    (by simp [blockDisjoint_iff])
  obtain ⟨_, _, mid, hm, hf⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
  have hwrite := column_write_of_normalize (a := a) (N := n.eval)
    (off := lo.eval + n.eval * k.eval) xs hk (by simp [xs, hk, a]) hsh₁
    (by simpa [IExp.eval] using hrds) (by simpa [IExp.eval] using hfr₁)
    (by simpa [IExp.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm)
    (by simpa [IExp.eval, xs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf)
  refine ⟨out, ?_, ?_⟩
  swap
  · simpa [xs, a] using hwrite
  change exec I (.seq _ .skip) st = some out
  rw [exec_seq_skip]
  have hcomp : ExecutionComposable I (copyv p R (ro + n * k) L (lo + n * k) n) :=
    executionComposable_single I (fun _ => rfl)
  rw [hcomp, hr₁, Option.bind_some]
  exact hr₂

/-- On the exact elimination residual of a positive definite matrix, the stored column
operation writes exactly the corresponding column of its mathematical Cholesky factor.
Positive definiteness supplies the positive pivot and zero entries above it.
[GolubVanLoan2013, §4.2]. -/
theorem exec_choleskyColumnOfResidual_of_posDef (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (R L : ℕ) (ro lo k : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hA : A.PosDef) (hk : k.eval < n.eval)
    (hR : Holds st.store p R ro.eval (gaussState A k.eval)) (hRL : R ≠ L)
    (hL : Writable st.store p L (lo.eval + n.eval * k.eval) n.eval) :
    ∃ out : St P ℝ (OpCount P ι),
      exec I (choleskyColumnOfResidual p n R L ro lo k).run st = some out ∧
      st.store.writeBlock p L (lo.eval + n.eval * k.eval)
        (Array.ofFn fun i => choleskyLower A i ⟨k.eval, hk⟩) = some out.store := by
  obtain ⟨out, hr, hw⟩ := exec_choleskyColumnOfResidual I hI hc p st n R L ro lo k
    (gaussState A k.eval) hk hR hRL (hA.gaussState_apply_self_pos ⟨k.eval, hk⟩) hL
  refine ⟨out, hr, ?_⟩
  convert hw using 3
  funext i
  by_cases hik : (i : ℕ) < k.eval
  · have hz := gaussState_apply_eq_zero_of_lt_left A
      (fun l _ => (hA.gaussState_apply_self_pos l).ne') hik ⟨k.eval, hk⟩
    simp only [if_pos hik, hz, choleskyLower, Matrix.of_apply,
      if_neg (show ¬(⟨k.eval, hk⟩ : Fin n.eval) ≤ i by exact not_le.mpr hik)]
  · simp only [if_neg hik, choleskyLower, Matrix.of_apply,
      if_pos (show (⟨k.eval, hk⟩ : Fin n.eval) ≤ i by exact Nat.le_of_not_gt hik),
      RCLike.re_to_real, RCLike.ofReal_real_eq_id, id_eq]

end NLAlib.Computation
