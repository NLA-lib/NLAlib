/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.StridedWrites
public import NLAlib.Computation.MatrixStorage
public import NLAlib.Computation.ScalarFrames

/-!
# Copying rectangular matrix views

A rectangular view with a physical leading dimension is copied to another such view. Packed
panel gathering and trailing-block scattering are special cases. Copies use no arithmetic on
words, and the complete destination-gap frame is retained.

## Main results

* `NLAlib.Computation.exec_copyMatrixBlock`: actual rectangular copies and their complete frame.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Copy an `m × n` rectangular view between two distinct buffers with independent physical
leading dimensions and row/column starts. Both views are column major. -/
def copyMatrixBlock {P ι VB VI : Type} (p : P) (m n : IExp VI) (src dst : VB)
    (so sld sr sc dest dld dr dc : IExp VI) : Builder P ι VB VI Unit :=
  forRange n fun j => forRange m fun i =>
    ins (.copy p ⟨dst, dest + dr + IExp.var i + dld * (dc + IExp.var j)⟩
      ⟨src, so + sr + IExp.var i + sld * (sc + IExp.var j)⟩)

/-- Gather a rectangular matrix view into packed column-major storage. -/
def gatherMatrixBlock {P ι VB VI : Type} (p : P) (m n ld : IExp VI) (src : VB)
    (so row col : IExp VI) (dst : VB) (doff : IExp VI) : Builder P ι VB VI Unit :=
  copyMatrixBlock p m n src dst so ld row col doff m 0 0

/-- Scatter a packed rectangular matrix into a matrix view with a physical leading dimension. -/
def scatterMatrixBlock {P ι VB VI : Type} (p : P) (m n ld : IExp VI) (src : VB)
    (so : IExp VI) (dst : VB) (doff row col : IExp VI) : Builder P ι VB VI Unit :=
  copyMatrixBlock p m n src dst so m 0 0 doff ld row col

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

private theorem exec_copyMatrixBlock_of_pos (I : Interp P ι K C) (p : P) (st : St P K C)
    (m n : IExp ℕ) (src dst : ℕ) (so sld sr sc dest dld dr dc : IExp ℕ)
    (M : Matrix (Fin m.eval) (Fin n.eval) K) (hmpos : 0 < m.eval) (hld : m.eval ≤ dld.eval)
    (hne : 0 < m.eval * n.eval → src ≠ dst)
    (hread : ∀ i j, st.store.read p src
      (so.eval + sr.eval + i.val + sld.eval * (sc.eval + j.val)) = some (M i j))
    (hcap : ∀ i < m.eval, ∀ j < n.eval, ∃ len, st.store.shape[dst]? = some (p, len) ∧
      dest.eval + dr.eval + i + dld.eval * (dc.eval + j) < len) :
    ∃ out, exec I (copyMatrixBlock p m n src dst so sld sr sc dest dld dr dc).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i j, out.store.read p dst
        (dest.eval + dr.eval + i.val + dld.eval * (dc.eval + j.val)) = some (M i j)) ∧
      ∀ q b t, (b ≠ dst ∨ ∀ i < m.eval, ∀ j < n.eval,
        t ≠ dest.eval + dr.eval + i + dld.eval * (dc.eval + j)) →
          out.store.read q b t = st.store.read q b t := by
  let body : ℕ → Stmt P ι ℕ ℕ := fun j => (forRange m fun i =>
    ins (.copy p ⟨dst, dest + dr + IExp.var i + dld * (dc + IExp.var j)⟩
      ⟨src, so + sr + IExp.var i + sld * (sc + IExp.var j)⟩)).run
  let R := fun k (σ : St P K C) => σ.store.shape = st.store.shape ∧
    (∀ i : Fin m.eval, ∀ j : Fin n.eval, j.val < k → σ.store.read p dst
      (dest.eval + dr.eval + i.val + dld.eval * (dc.eval + j.val)) = some (M i j)) ∧
    ∀ q b t, (b ≠ dst ∨ ∀ i < m.eval, ∀ j < k,
      t ≠ dest.eval + dr.eval + i + dld.eval * (dc.eval + j)) →
        σ.store.read q b t = st.store.read q b t
  have h0 : R 0 st := ⟨rfl, fun _ _ hj => (Nat.not_lt_zero _ hj).elim,
    fun _ _ _ _ => rfl⟩
  obtain ⟨out, hrun, hshape, hfinal, hframe⟩ := exists_exec_loop_eq_some_of_forall I (n := n)
      (body := body) R h0 (by
    intro j hj σ hσ
    obtain ⟨hshape, hprefix, hframe⟩ := hσ
    let value : ℕ → K := fun i => if hi : i < m.eval then M ⟨i, hi⟩ ⟨j, hj⟩
      else M ⟨0, hmpos⟩ ⟨j, hj⟩
    obtain ⟨next, hr, hs, hrd, hfr⟩ := exec_strided_writes I p σ m dst
      (dest.eval + dr.eval + dld.eval * (dc.eval + j)) 1 (by omega) value
      (fun i => ins (.copy p
        ⟨dst, dest + dr + IExp.var i + dld * (dc + IExp.var j)⟩
        ⟨src, so + sr + IExp.var i + sld * (sc + IExp.var j)⟩)) (by
          intro i hi τ hτ hτframe
          have hsep := hne (Nat.mul_pos (by omega) (by omega))
          have hsrc : τ.store.read p src
              (so.eval + sr.eval + i + sld.eval * (sc.eval + j)) = some (M ⟨i, hi⟩ ⟨j, hj⟩) := by
            rw [hτframe p src _ hsep, hframe p src _ (Or.inl hsep)]
            exact hread ⟨i, hi⟩ ⟨j, hj⟩
          obtain ⟨len, hlen, hlt⟩ := hcap i hi j hj
          obtain ⟨store, hw, hexec, _, _, _⟩ := exec_scalar_copy I p τ
            ⟨dst, dest + dr + IExp.var i + dld * (dc + IExp.var j)⟩
            ⟨src, so + sr + IExp.var i + sld * (sc + IExp.var j)⟩
            (M ⟨i, hi⟩ ⟨j, hj⟩) hsrc
            ⟨len, by rw [hτ, hshape]; exact hlen, hlt⟩
          refine ⟨_, hexec, ?_⟩
          simpa only [value, dif_pos hi, IExp.eval_add, IExp.eval_mul, IExp.eval_var,
            Nat.one_mul, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hw)
    refine ⟨next, ?_, hs.trans hshape, ?_, ?_⟩
    · change exec I (.seq (.loop m _) .skip) σ = some next
      rw [exec_seq_skip]
      exact hr
    · intro i l hl
      by_cases hlj : l.val = j
      · have he : l = ⟨j, hj⟩ := Fin.ext hlj
        subst l
        simpa only [value, dif_pos i.isLt, Nat.one_mul, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hrd i i.isLt
      · have hlt : l.val < j := by omega
        have hgap := Nat.mul_le_mul_left dld.eval
          (show dc.eval + l.val + 1 ≤ dc.eval + j by omega)
        rw [hfr p dst _ (Or.inr (by
          intro t ht
          have := i.isLt
          have := Nat.le_trans (Nat.succ_le_of_lt i.isLt) hld
          nlinarith)), hprefix i l hlt]
    · intro q b t ht
      rw [hfr q b t (ht.imp_right (fun h i hi => by
        have := h i hi j (Nat.lt_succ_self j)
        simpa only [Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this))]
      exact hframe q b t (ht.imp_right (fun h i hi l hl => h i hi l (by omega))))
  refine ⟨out, ?_, hshape, fun i j => hfinal i j j.isLt, hframe⟩
  change exec I (.seq (.loop n _) .skip) st = some out
  rw [exec_seq_skip]
  exact hrun

/-- Rectangular copying succeeds from initialized source cells and writable destination cells.
Destination columns do not overlap when the copied row count is at most its physical leading
dimension. All other cells, including gaps between copied columns, retain their original words.
The word carrier, scalar interpretation and charge monoid are arbitrary. Empty rectangles need
no valid handles or separation. -/
theorem exec_copyMatrixBlock (I : Interp P ι K C) (p : P) (st : St P K C)
    (m n : IExp ℕ) (src dst : ℕ) (so sld sr sc dest dld dr dc : IExp ℕ)
    (M : Matrix (Fin m.eval) (Fin n.eval) K) (hld : m.eval ≤ dld.eval)
    (hne : 0 < m.eval * n.eval → src ≠ dst)
    (hread : ∀ i j, st.store.read p src
      (so.eval + sr.eval + i.val + sld.eval * (sc.eval + j.val)) = some (M i j))
    (hcap : ∀ i < m.eval, ∀ j < n.eval, ∃ len, st.store.shape[dst]? = some (p, len) ∧
      dest.eval + dr.eval + i + dld.eval * (dc.eval + j) < len) :
    ∃ out, exec I (copyMatrixBlock p m n src dst so sld sr sc dest dld dr dc).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i j, out.store.read p dst
        (dest.eval + dr.eval + i.val + dld.eval * (dc.eval + j.val)) = some (M i j)) ∧
      ∀ q b t, (b ≠ dst ∨ ∀ i < m.eval, ∀ j < n.eval,
        t ≠ dest.eval + dr.eval + i + dld.eval * (dc.eval + j)) →
          out.store.read q b t = st.store.read q b t := by
  let body : ℕ → Stmt P ι ℕ ℕ := fun j => (forRange m fun i =>
    ins (.copy p ⟨dst, dest + dr + IExp.var i + dld * (dc + IExp.var j)⟩
      ⟨src, so + sr + IExp.var i + sld * (sc + IExp.var j)⟩)).run
  by_cases hm : m.eval = 0
  · obtain ⟨out, hr, hout⟩ := exists_exec_loop_eq_some_of_forall I
      (n := n) (body := body) (fun _ (σ : St P K C) => σ = st) rfl (by
        intro j hj σ hσ
        subst σ
        refine ⟨st, ?_, rfl⟩
        change exec I (.seq (.loop m _) .skip) st = some st
        simp only [exec_seq_skip, exec_loop, hm, List.range_zero, List.foldlM_nil,
          Option.pure_def])
    subst out
    refine ⟨st, ?_, rfl, ?_, fun _ _ _ _ => rfl⟩
    · change exec I (.seq (.loop n _) .skip) st = some st
      rw [exec_seq_skip]
      exact hr
    · intro i j
      have := i.isLt
      omega
  exact exec_copyMatrixBlock_of_pos I p st m n src dst so sld sr sc dest dld dr dc M
    (Nat.pos_of_ne_zero hm) hld hne hread hcap

/-- Gathering an initialized rectangular view into writable packed storage succeeds, writes
one full packed block and retains all other cells. Arbitrary carriers and empty dimensions
are supported; separation is required only for positive area. -/
theorem exec_gatherMatrixBlock (I : Interp P ι K C) (p : P) (st : St P K C)
    (m n ld : IExp ℕ) (src : ℕ) (so row col : IExp ℕ) (dst : ℕ) (doff : IExp ℕ)
    (M : Matrix (Fin m.eval) (Fin n.eval) K)
    (hne : 0 < m.eval * n.eval → src ≠ dst)
    (hread : ∀ i j, st.store.read p src
      (so.eval + row.eval + i.val + ld.eval * (col.eval + j.val)) = some (M i j))
    (hcap : Writable st.store p dst doff.eval (m.eval * n.eval)) :
    ∃ (out : St P K C) (W : Array K), W.size = m.eval * n.eval ∧
      exec I (gatherMatrixBlock p m n ld src so row col dst doff).run st = some out ∧
      st.store.writeBlock p dst doff.eval W = some out.store ∧
      Holds out.store p dst doff.eval M := by
  obtain ⟨out, hexec, hshape, hreads, hframe⟩ := exec_copyMatrixBlock I p st m n src dst
    so ld row col doff m 0 0 M le_rfl hne hread (by
      intro i hi j hj
      simpa only [IExp.eval_zero, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
        hcap (i + m.eval * j) (Nat.add_mul_lt_mul_of_lt_of_lt hi hj))
  have hM : Holds out.store p dst doff.eval M := fun i j => by
    simpa only [IExp.eval_zero, Nat.add_zero, Nat.zero_add] using hreads i j
  obtain ⟨W, hsize, hflat, _, _⟩ := hM.exists_array
  refine ⟨out, W, hsize, hexec, ?_, hM⟩
  apply Store.writeBlock_eq_some_of_read hshape
  · intro t ht
    exact hflat t (by simpa only [hsize] using ht)
  · intro q b t ht
    apply hframe q b t
    simp only [IExp.eval_zero, Nat.add_zero, Nat.zero_add]
    rcases ht with hb | hlo | hhi
    · exact Or.inl hb
    · exact Or.inr (fun i hi j hj => by omega)
    · refine Or.inr (fun i hi j hj => ?_)
      have := Nat.add_mul_lt_mul_of_lt_of_lt hi hj
      rw [hsize] at hhi
      omega

/-- Scattering a packed rectangle to a writable matrix view succeeds and keeps every gap
and outside cell unchanged. Copies perform no scalar arithmetic and impose no carrier
structure. Empty rectangles require no valid handles or separation. -/
theorem exec_scatterMatrixBlock (I : Interp P ι K C) (p : P) (st : St P K C)
    (m n ld : IExp ℕ) (src : ℕ) (so : IExp ℕ) (dst : ℕ) (doff row col : IExp ℕ)
    (M : Matrix (Fin m.eval) (Fin n.eval) K) (hld : m.eval ≤ ld.eval)
    (hne : 0 < m.eval * n.eval → src ≠ dst) (hread : Holds st.store p src so.eval M)
    (hcap : ∀ i < m.eval, ∀ j < n.eval, ∃ len, st.store.shape[dst]? = some (p, len) ∧
      doff.eval + row.eval + i + ld.eval * (col.eval + j) < len) :
    ∃ out, exec I (scatterMatrixBlock p m n ld src so dst doff row col).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i j, out.store.read p dst
        (doff.eval + row.eval + i.val + ld.eval * (col.eval + j.val)) = some (M i j)) ∧
      ∀ q b t, (b ≠ dst ∨ ∀ i < m.eval, ∀ j < n.eval,
        t ≠ doff.eval + row.eval + i + ld.eval * (col.eval + j)) →
          out.store.read q b t = st.store.read q b t := by
  exact exec_copyMatrixBlock I p st m n src dst so m 0 0 doff ld row col M hld hne
    (fun i j => by simpa only [IExp.eval_zero, Nat.add_zero, Nat.zero_add] using hread i j) hcap

end NLAlib.Computation
