/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.MatrixBlockCopy

/-!
# Full matrix frames for rectangular scatter

A packed rectangular result replaces a view of a stored square matrix. The resulting full
matrix remains initialized, its exterior entries are retained, and its words determine one
full packed matrix write. This is shared by panel rank-one and trailing GEMM updates.

## Main results

* `NLAlib.Computation.exec_scatterMatrixBlock_into_matrix`: full matrix output after scatter.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] {N m n : ℕ}

private theorem holds_after_rectangle {initial final : Store P K} {p : P}
    {R off row col : ℕ} (M : Matrix (Fin N) (Fin N) K)
    (B : Matrix (Fin m) (Fin n) K) (hrow : row + m ≤ N) (hcol : col + n ≤ N)
    (hM : Holds initial p R off M)
    (hread : ∀ i j, final.read p R (off + row + i.val + N * (col + j.val)) = some (B i j))
    (hframe : ∀ q b t, (b ≠ R ∨ ∀ i < m, ∀ j < n,
      t ≠ off + row + i + N * (col + j)) → final.read q b t = initial.read q b t) :
    ∃ M' : Matrix (Fin N) (Fin N) K, Holds final p R off M' ∧
      (∀ i j, M' (Fin.castLE hrow (Fin.natAdd row i))
        (Fin.castLE hcol (Fin.natAdd col j)) = B i j) ∧
      ∀ i j, (i.val < row ∨ row + m ≤ i.val ∨ j.val < col ∨ col + n ≤ j.val) →
        M' i j = M i j := by
  let M' : Matrix (Fin N) (Fin N) K := fun i j =>
    if h : row ≤ i.val ∧ i.val < row + m ∧ col ≤ j.val ∧ j.val < col + n then
      B ⟨i.val - row, by omega⟩ ⟨j.val - col, by omega⟩ else M i j
  refine ⟨M', ?_, ?_, ?_⟩
  · intro i j
    by_cases h : row ≤ i.val ∧ i.val < row + m ∧ col ≤ j.val ∧ j.val < col + n
    · dsimp only [M']
      rw [dif_pos h]
      have he := hread ⟨i.val - row, by omega⟩ ⟨j.val - col, by omega⟩
      simpa only [Nat.add_assoc, Nat.add_sub_of_le h.1, Nat.add_sub_of_le h.2.2.1] using he
    · dsimp only [M']
      rw [dif_neg h, hframe p R (off + i.val + N * j.val) (Or.inr ?_)]
      · exact hM i j
      · intro a ha b hb he
        let ii : Fin N := ⟨row + a, by omega⟩
        let jj : Fin N := ⟨col + b, by omega⟩
        have hi : i.val + N * j.val = ii.val + N * jj.val := by
          dsimp only [ii, jj]
          omega
        have hpair := finProdFinEquiv.injective
          (show finProdFinEquiv (j, i) = finProdFinEquiv (jj, ii) from Fin.ext hi)
        have hie := congrArg (fun a : Fin N × Fin N => a.2.val) hpair
        have hje := congrArg (fun a : Fin N × Fin N => a.1.val) hpair
        exact h (by dsimp only [ii, jj] at hie hje; omega)
  · intro i j
    have h : row ≤ row + i.val ∧ row + i.val < row + m ∧
        col ≤ col + j.val ∧ col + j.val < col + n := by omega
    dsimp only [M', Fin.castLE, Fin.natAdd]
    rw [dif_pos h]
    congr 1 <;> apply Fin.ext <;> simp
  · intro i j hout
    have h : ¬(row ≤ i.val ∧ i.val < row + m ∧ col ≤ j.val ∧ j.val < col + n) := by omega
    exact dif_neg h

/-- Scattering a packed rectangle inside an initialized square matrix determines its complete
new contents and one full original-store matrix write. Every exterior matrix entry is retained.
The scalar carrier and interpretation are arbitrary; no zero or encoding definition is needed.
Empty rectangles and empty matrices impose no source/destination separation. -/
theorem exec_scatterMatrixBlock_into_matrix (I : Interp P ι K C) (p : P) (st : St P K C)
    (size m n : IExp ℕ) (src : ℕ) (so : IExp ℕ) (R : ℕ) (off row col : IExp ℕ)
    (M : Matrix (Fin size.eval) (Fin size.eval) K)
    (B : Matrix (Fin m.eval) (Fin n.eval) K)
    (hrow : row.eval + m.eval ≤ size.eval) (hcol : col.eval + n.eval ≤ size.eval)
    (hM : Holds st.store p R off.eval M) (hB : Holds st.store p src so.eval B)
    (hne : 0 < m.eval * n.eval → src ≠ R) :
    ∃ (out : St P K C) (W : Array K) (M' : Matrix (Fin size.eval) (Fin size.eval) K),
      W.size = size.eval * size.eval ∧
      exec I (scatterMatrixBlock p m n size src so R off row col).run st = some out ∧
      st.store.writeBlock p R off.eval W = some out.store ∧ Holds out.store p R off.eval M' ∧
      (∀ i j, M' (Fin.castLE hrow (Fin.natAdd row.eval i))
        (Fin.castLE hcol (Fin.natAdd col.eval j)) = B i j) ∧
      ∀ i j, (i.val < row.eval ∨ row.eval + m.eval ≤ i.val ∨
        j.val < col.eval ∨ col.eval + n.eval ≤ j.val) → M' i j = M i j := by
  obtain ⟨out, hr, hshape, hreads, hframe⟩ := exec_scatterMatrixBlock I p st m n size
    src so R off row col B (by omega) hne hB (by
      intro i hi j hj
      let ii : Fin size.eval := ⟨row.eval + i, by omega⟩
      let jj : Fin size.eval := ⟨col.eval + j, by omega⟩
      obtain ⟨len, hlen, hlt⟩ := hM.writable (ii.val + size.eval * jj.val)
        (Nat.add_mul_lt_mul_of_lt_of_lt ii.isLt jj.isLt)
      exact ⟨len, hlen, by simpa only [ii, jj, Nat.add_assoc] using hlt⟩)
  obtain ⟨M', hM', hcoords, houtside⟩ := holds_after_rectangle M B hrow hcol hM hreads hframe
  obtain ⟨W, hsize, hflat, _, _⟩ := hM'.exists_array
  refine ⟨out, W, M', hsize, hr, ?_, hM', hcoords, houtside⟩
  apply Store.writeBlock_eq_some_of_read hshape
  · intro t ht
    exact hflat t (by simpa only [hsize] using ht)
  · intro q b t ht
    apply hframe q b t
    rcases ht with hb | hlo | hhi
    · exact Or.inl hb
    · exact Or.inr (fun i hi j hj he => by omega)
    · refine Or.inr (fun i hi j hj he => ?_)
      have hi' : row.eval + i < size.eval := by omega
      have hj' : col.eval + j < size.eval := by omega
      have hbound := Nat.add_mul_lt_mul_of_lt_of_lt hi' hj'
      rw [hsize] at hhi
      omega

end NLAlib.Computation
