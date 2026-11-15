/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveStorage

/-!
# Workspace geometry of the scalar Givens row solve

The triangular matrix, vector, coefficient arena, accumulator, arithmetic scratch and
singularity flag use separate buffers in this implementation. Scoped allocation supplies the
working buffers. Their separation is ordinary storage geometry, independent of numerical laws.

## Main results

* `NLAlib.ShiftedQR.RowSolveSeparate`: the six workspace buffers are separate.
* `NLAlib.ShiftedQR.rowSolve_live`: actual reads and capacities make the call arguments live.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

/-- Buffer separation chosen by this scalar row-solve implementation. -/
structure RowSolveSeparate (a v cf z t f : ℕ × ℕ) : Prop where
  /-- Matrix and coefficients use separate buffers. -/
  ac : a.1 ≠ cf.1
  /-- Vector and matrix use separate buffers. -/
  va : v.1 ≠ a.1
  /-- Coefficients and vector use separate buffers. -/
  cv : cf.1 ≠ v.1
  /-- Accumulator and matrix use separate buffers. -/
  za : z.1 ≠ a.1
  /-- Accumulator and vector use separate buffers. -/
  zv : z.1 ≠ v.1
  /-- Accumulator and coefficients use separate buffers. -/
  zc : z.1 ≠ cf.1
  /-- Scratch and matrix use separate buffers. -/
  ta : t.1 ≠ a.1
  /-- Scratch and vector use separate buffers. -/
  tv : t.1 ≠ v.1
  /-- Scratch and coefficients use separate buffers. -/
  tc : t.1 ≠ cf.1
  /-- Scratch and accumulator use separate buffers. -/
  tz : t.1 ≠ z.1
  /-- Flag and matrix use separate buffers. -/
  fa : f.1 ≠ a.1
  /-- Flag and vector use separate buffers. -/
  fv : f.1 ≠ v.1
  /-- Flag and coefficients use separate buffers. -/
  fc : f.1 ≠ cf.1
  /-- Flag and accumulator use separate buffers. -/
  fz : f.1 ≠ z.1
  /-- Flag and scratch use separate buffers. -/
  ft : f.1 ≠ t.1

/-- Four fresh workspace handles are separate from surviving vector and flag buffers. -/
theorem fresh_rowSolveSeparate {L : ℕ} {v f : ℕ × ℕ} (hv : v.1 < L) (hf : f.1 < L)
    (hfv : f.1 ≠ v.1) :
    RowSolveSeparate (L, 0) v (L + 1, 0) (L + 2, 0) (L + 3, 0) f := by
  constructor <;> dsimp <;> omega

/-- The full writable workspace of the concrete scalar row solver. -/
def rowSolveFp (n : ℕ) (a v cf z t f : ℕ × ℕ) : Fp :=
  Fp.blocks [a, cf, z, t, v, f] [2 * (n * n), 4 * n, 2, 10, 2 * n, 1]

/-- The complete row solve either certifies singularity or returns the exact inverse row. -/
def RowSolveResult {n : ℕ} (v f : ℕ × ℕ) (D : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin n → ℂ) (s : Store ℝ) : Prop :=
  (s.get f.1 f.2 = some 1 ∧ D.det = 0) ∨
    (s.get f.1 f.2 = some 0 ∧ HoldsVector v (w ᵥ* D⁻¹) s)

/-- A complete row-solve result survives removal of unrelated scoped workspace. -/
theorem RowSolveResult.of_below {n L : ℕ} {v f : ℕ × ℕ}
    {D : Matrix (Fin n) (Fin n) ℂ} {w : Fin n → ℂ} {s s' : Store ℝ}
    (h : RowSolveResult v f D w s) (hBelow : Store.Below L s s')
    (hv : v.1 < L) (hf : f.1 < L) : RowSolveResult v f D w s' := by
  rcases h with ⟨hflag, hdet⟩ | ⟨hflag, hV⟩
  · exact Or.inl ⟨((hBelow f.1 hf).2 _).trans hflag, hdet⟩
  · exact Or.inr ⟨((hBelow f.1 hf).2 _).trans hflag, hV.of_below hBelow hv⟩

/-- Source words and positive workspace capacities make every row-solve argument live. -/
theorem rowSolve_live {m : Mem ℝ} {n : ℕ} {a v cf z t f : ℕ × ℕ}
    {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {w : Fin (n + 1) → ℂ}
    (hR : HoldsMatrix a R m.store) (hV : HoldsVector v w m.store)
    (hc : cf.2 + 4 * (n + 1) ≤ m.store.len cf.1)
    (hz : z.2 + 2 ≤ m.store.len z.1) (ht : t.2 + 10 ≤ m.store.len t.1)
    (hf : f.2 + 1 ≤ m.store.len f.1) : m.Live [a, v, cf, z, t, f, v, f] := by
  have hal := Store.lt_length_of_get (hR.get_re (0 : Fin (n + 1)) 0)
  have hvl := Store.lt_length_of_get (HoldsVector.get_re hV (0 : Fin (n + 1)))
  have hcl : cf.1 < m.store.length := Store.lt_length_of_lt_len (by omega : cf.2 < _)
  have hzl : z.1 < m.store.length := Store.lt_length_of_lt_len (by omega : z.2 < _)
  have htl : t.1 < m.store.length := Store.lt_length_of_lt_len (by omega : t.2 < _)
  have hfl : f.1 < m.store.length := Store.lt_length_of_lt_len (by omega : f.2 < _)
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

end NLAlib.ShiftedQR
