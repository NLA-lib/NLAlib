/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Spec
public import NLAlib.Ops.Logic.Layout

/-!
# Decoded stored vectors and coefficients for Lanczos

Numerical state facts retain actual readable word witnesses. Their footprint lemmas transport
those witnesses through calls, and contiguous-column readback constructs the final basis
block without assuming that an execution succeeded.

## Main results

* `NLAlib.Krylov.Lanczos.StoresVec` and `NLAlib.Krylov.Lanczos.StoresCell` record decoded reads.
* `NLAlib.Krylov.Lanczos.exists_basis_readBlock` joins readable basis columns.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops

variable {K : Type} [Inhabited K]

/-- An actual readable block decodes to the stated finite vector. -/
def StoresVec (dec : K → ℝ) {n : ℕ} (q : ℕ × ℕ) (v : Fin n → ℝ) (s : Store K) : Prop :=
  ∃ xs, s.readBlock q.1 q.2 n = some xs ∧ decv dec n xs = v

/-- An actual readable cell decodes to the stated coefficient. -/
def StoresCell (dec : K → ℝ) (q : ℕ × ℕ) (v : ℝ) (s : Store K) : Prop :=
  ∃ a, s.get q.1 q.2 = some a ∧ dec a = v

/-- A decoded block fact reads only that block. -/
theorem readsOnly_storesVec (dec : K → ℝ) {n : ℕ} (q : ℕ × ℕ) (v : Fin n → ℝ) :
    Store.ReadsOnly (Store.inBlock q.1 q.2 n) (StoresVec dec q v) := by
  rintro s s' h ⟨xs, hx, he⟩
  exact ⟨xs, Store.readsOnly_readBlock q.1 q.2 n xs s s' h hx, he⟩

omit [Inhabited K] in
/-- A decoded coefficient fact reads only its cell. -/
theorem readsOnly_storesCell (dec : K → ℝ) (q : ℕ × ℕ) (v : ℝ) :
    Store.ReadsOnly (Store.inBlock q.1 q.2 1) (StoresCell dec q v) := by
  rintro s s' h ⟨a, ha, he⟩
  exact ⟨a, Store.readsOnly_get q.1 q.2 a s s' h ha, he⟩

/-- A decoded vector is preserved by writes disjoint from its block. -/
theorem StoresVec.keep {dec : K → ℝ} {n : ℕ} {q : ℕ × ℕ} {v : Fin n → ℝ}
    {s s' : Store K} {F : Fp} (h : StoresVec dec q v s) (hf : s.EqOff F s')
    (hd : Fp.Disj F (Store.inBlock q.1 q.2 n)) : StoresVec dec q v s' :=
  hf.keep (readsOnly_storesVec dec q v) hd h

omit [Inhabited K] in
/-- A decoded coefficient is preserved by writes disjoint from its cell. -/
theorem StoresCell.keep {dec : K → ℝ} {q : ℕ × ℕ} {v : ℝ}
    {s s' : Store K} {F : Fp} (h : StoresCell dec q v s) (hf : s.EqOff F s')
    (hd : Fp.Disj F (Store.inBlock q.1 q.2 1)) : StoresCell dec q v s' :=
  hf.keep (readsOnly_storesCell dec q v) hd h

/-- A literal-zero block decodes to the zero vector. -/
theorem StoresVec.of_zero_readBlock {dec : K → ℝ} {n : ℕ} {q : ℕ × ℕ} {s : Store K} {a : K}
    (hr : s.readBlock q.1 q.2 n = some (List.replicate n a)) (ha : dec a = 0) :
    StoresVec dec q (0 : Fin n → ℝ) s := by
  refine ⟨_, hr, ?_⟩
  funext i
  simp [decv, vec, List.getD_eq_getElem?_getD, i.isLt, ha]

/-- A cell read from a decoded vector retains its decoded entry. -/
theorem StoresVec.cell {dec : K → ℝ} {n : ℕ} {q : ℕ × ℕ} {s : Store K} {v : Fin n → ℝ}
    (h : StoresVec dec q v s) (i : Fin n) : StoresCell dec (q.1, q.2 + i) (v i) s := by
  obtain ⟨xs, hx, he⟩ := h
  exact ⟨vec xs i, by simpa [vec] using Store.get_of_readBlock hx i.isLt default,
    congrFun he i⟩

/-- Every subblock of an initialized decoded-zero block is initialized decoded zero. -/
theorem StoresVec.zero_sub {dec : K → ℝ} {N n o : ℕ} {q : ℕ × ℕ} {s : Store K}
    (h : StoresVec dec q (0 : Fin N → ℝ) s) (hb : o + n ≤ N) :
    StoresVec dec (q.1, q.2 + o) (0 : Fin n → ℝ) s := by
  obtain ⟨xs, hx, he⟩ := h
  refine ⟨(xs.drop o).take n, Store.readBlock_sub hx hb, ?_⟩
  funext i
  change dec (vec ((xs.drop o).take n) i) = 0
  rw [vec_drop_take i.isLt]
  exact congrFun he ⟨o + i, by omega⟩

/-- Readable contiguous columns give an actual read of the complete basis block. -/
theorem exists_basis_readBlock {dec : K → ℝ} {n k : ℕ} {V : ℕ × ℕ} {s : Store K}
    {v : ℕ → Fin n → ℝ}
    (h : ∀ j < k, StoresVec dec (V.1, V.2 + j * n) (v j) s) :
    ∃ vs, s.readBlock V.1 V.2 (k * n) = some vs := by
  induction k with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
    obtain ⟨xs, hx⟩ := ih fun j hj => h j (by omega)
    obtain ⟨ys, hy, _⟩ := h k (Nat.lt_succ_self k)
    exact ⟨xs ++ ys, by simpa only [Nat.succ_mul] using Store.readBlock_add hx hy⟩

/-- A complete basis read and a decoded column read agree on every column entry. -/
theorem StoresVec.entry_of_basis_readBlock {dec : K → ℝ} {n k j : ℕ} {V : ℕ × ℕ}
    {s : Store K} {vs : List K} {v : Fin n → ℝ}
    (h : StoresVec dec (V.1, V.2 + j * n) v s)
    (hr : s.readBlock V.1 V.2 (k * n) = some vs) (hj : j < k) (i : Fin n) :
    dec (vec vs (j * n + i)) = v i := by
  obtain ⟨xs, hx, he⟩ := h
  have hg := Store.get_of_readBlock hr (Idx.add_lt_mul hj i.isLt) default
  have hg' := Store.get_of_readBlock hx i.isLt default
  have hw : vec vs (j * n + i) = vec xs i :=
    Option.some.inj (hg.symm.trans (by simpa only [Nat.add_assoc] using hg'))
  exact (congrArg dec hw).trans (congrFun he i)

omit [Inhabited K] in
/-- Readable coefficient cells give an actual read of their complete contiguous block. -/
theorem exists_coeff_readBlock {dec : K → ℝ} {k : ℕ} {C : ℕ × ℕ} {s : Store K}
    {v : ℕ → ℝ} (h : ∀ i < k, StoresCell dec (C.1, C.2 + i) (v i) s) :
    ∃ cs, s.readBlock C.1 C.2 k = some cs := by
  induction k with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
    obtain ⟨xs, hx⟩ := ih fun i hi => h i (by omega)
    obtain ⟨a, ha, _⟩ := h k (Nat.lt_succ_self k)
    exact ⟨xs ++ [a], Store.readBlock_succ_of hx ha⟩

/-- A complete coefficient read and a decoded cell fact agree on that coefficient. -/
theorem StoresCell.value_of_readBlock {dec : K → ℝ} {k i : ℕ} {C : ℕ × ℕ}
    {s : Store K} {cs : List K} {v : ℝ}
    (h : StoresCell dec (C.1, C.2 + i) v s)
    (hr : s.readBlock C.1 C.2 k = some cs) (hi : i < k) : dec (vec cs i) = v := by
  obtain ⟨a, ha, he⟩ := h
  have hg := Store.get_of_readBlock hr hi default
  exact (congrArg dec (Option.some.inj (hg.symm.trans ha))).trans he

end NLAlib.Krylov.Lanczos
