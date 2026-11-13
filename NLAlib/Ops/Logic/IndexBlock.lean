/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.IndexLiteral
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Straight-line dimension literal blocks

A list of symbolic dimension literals and output operands expands to ordinary scalar writes.
The shared rule collects their actual machine words and their frame. Readback of every word
requires apart output cells; numerical exactness of their decoding is a separate hypothesis
of any later index query.

## Main results

* `NLAlib.Ops.Stmt.indexBlock`: ordinary right-associated dimension-literal calls.
* `NLAlib.Ops.writes_indexBlock`: their collected output blocks and unchanged tape position.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has IndexOp Op]

/-- A straight-line block of symbolic dimension literal writes, with no final skip when the
list is nonempty. This is definitionally the tree produced by the ordinary program builder. -/
def Stmt.indexBlock : List (IExp × Operand) → Stmt Op Tst
  | [] => .skip
  | [(n, z)] => .call (Has.inj IndexOp.lit) [n] [] [z]
  | (n, z) :: rest => .seq (.call (Has.inj IndexOp.lit) [n] [] [z]) (Stmt.indexBlock rest)

/-- A dimension literal block writes the actual machine literals of its evaluated natural
indices. Output cells are live through capacity and are pairwise apart for simultaneous
readback. No exactness or distinguishability of the literal decoding is assumed. -/
theorem writes_indexBlock {M : Machine K} {I : Interp Op Tst K} (hI : IsIndexLit M I)
    {τ : Tape K} {ρ : Env} {m : Mem K} (xs : List (IExp × Operand))
    {ns : List ℕ} {zs : List (ℕ × ℕ)}
    (hns : IExp.evalList ρ.idx (xs.map Prod.fst) = some ns)
    (hzs : Operand.evalList ρ (xs.map Prod.snd) = some zs)
    (hap : Fp.Apart zs (List.replicate xs.length 1))
    (hroom : m.Room zs (List.replicate xs.length 1)) :
    Writes .total I τ (Stmt.indexBlock xs) ρ (Fp.blocks zs (List.replicate xs.length 1))
      (fun m' => m'.pos = m.pos ∧ m'.readBlocks zs (List.replicate xs.length 1) =
        some (ns.map fun n => [M.lit (n : ℚ)])) m := by
  induction xs generalizing ns zs m with
  | nil =>
    simp only [List.map_nil, IExp.evalList_nil, Option.some.injEq] at hns
    simp only [List.map_nil, Operand.evalList_nil, Option.some.injEq] at hzs
    subst ns; subst zs
    exact Writes.skip ⟨rfl, rfl⟩
  | cons x xs ih =>
    simp only [List.map_cons, IExp.evalList_cons] at hns
    obtain ⟨n, hn, hns⟩ := Option.bind_eq_some_iff.mp hns
    obtain ⟨ns', hns', rfl⟩ := Option.map_eq_some_iff.mp hns
    simp only [List.map_cons, Operand.evalList_cons] at hzs
    obtain ⟨z, hz, hzs⟩ := Option.bind_eq_some_iff.mp hzs
    obtain ⟨zs', hzs', rfl⟩ := Option.map_eq_some_iff.mp hzs
    simp only [List.length_cons, List.replicate_succ, Fp.Apart] at hap
    simp only [List.length_cons, List.replicate_succ, Mem.room_cons] at hroom
    have hfirst := (writes_indexLit (τ := τ) (m := m) (ρ := ρ) hI hn hz
      (by have := hroom.1; omega)).readBlock_of_get
    cases xs with
    | nil =>
      simp only [List.map_nil, IExp.evalList_nil, Option.some.injEq] at hns'
      simp only [List.map_nil, Operand.evalList_nil, Option.some.injEq] at hzs'
      subst ns'; subst zs'
      exact hfirst.readBlocks_singleton
    | cons x' xs =>
      exact hfirst.seq_readBlock hap.1 fun m' hfr _ _ =>
        ih hns' hzs' hap.2 (hroom.2.congr hfr.len_eq)

end NLAlib.Ops
