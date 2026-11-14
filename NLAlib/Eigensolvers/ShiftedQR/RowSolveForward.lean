/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveChecked

/-!
# Total forward substitution with a singularity flag

Each column checks its actual pivot. The loop retains either a witnessed zero diagonal and
a set flag, or the exact solved prefix with all processed pivots nonzero. Thus singular
triangular matrices have a defined outcome and never reach a zero-denominator division.

## Main results

* `NLAlib.ShiftedQR.substitutionLoop`: checked increasing-column substitution.
* `NLAlib.ShiftedQR.SubstitutionState`: the mathematical and stored loop invariant.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Visit all columns, retaining the first singularity report and skipping later arithmetic. -/
def substitutionLoop : Impl Op Tst := opsImpl% [n] (R, V, Acc, T, Flag) → (V, Flag) {
  for j < n {
    run checkedSubstituteColumn.body [n, j] (R, V, Acc, T, Flag, V, Flag)
  }
}

/-- A set flag carries a previously observed zero diagonal. A clear flag carries the exact
solved prefix and a nonzero pivot for every completed column. -/
def SubstitutionState {n : ℕ} (v f : ℕ × ℕ) (R : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin n → ℂ) (k : ℕ) (s : Store ℝ) : Prop :=
  (s.get f.1 f.2 = some 1 ∧ ∃ i : Fin n, i < k ∧ R i i = 0) ∨
    (s.get f.1 f.2 = some 0 ∧ HoldsVector v (solvePrefix R w k) s ∧
      ∀ i : Fin n, i < k → R i i ≠ 0)

/-- The checked substitution loop either reports a genuine zero diagonal or returns the
exact triangular forward substitution with every diagonal entry nonzero. No hypothesis
excludes singular triangular inputs. [GolubVanLoan2013, §3.1.2]. -/
theorem substitutionLoop_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a v z t f : ℕ × ℕ}
    {R : Matrix (Fin n) (Fin n) ℂ} {w : Fin n → ℂ} (hn : 0 < n)
    (hR : HoldsMatrix a R m.store) (hV : HoldsVector v w m.store)
    (hva : v.1 ≠ a.1) (hza : z.1 ≠ a.1) (hzv : z.1 ≠ v.1)
    (hta : t.1 ≠ a.1) (htv : t.1 ≠ v.1) (htz : t.1 ≠ z.1)
    (hfa : f.1 ≠ a.1) (hfv : f.1 ≠ v.1) (hfz : f.1 ≠ z.1) (hft : f.1 ≠ t.1)
    (hf0 : m.store.get f.1 f.2 = some 0)
    (hz : z.2 + 2 ≤ m.store.len z.1) (ht : t.2 + 4 ≤ m.store.len t.1)
    (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ substitutionLoop.body (Env.frame [n] [a, v, z, t, f, v, f])
      (Store.inBlock f.1 f.2 1 ⊔ ((Store.inBlock t.1 t.2 4 ⊔ Store.inBlock z.1 z.2 2) ⊔
        Store.inBlock v.1 v.2 (2 * n)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a R m'.store ∧
        ((m'.store.get f.1 f.2 = some 1 ∧ ∃ i, R i i = 0) ∨
          (m'.store.get f.1 f.2 = some 0 ∧ HoldsVector v (rowForwardSubst R w) m'.store ∧
            ∀ i, R i i ≠ 0))) m := by
  have hal := Store.lt_length_of_get (hR.get_re (⟨0, hn⟩ : Fin n) ⟨0, hn⟩)
  have hvl := Store.lt_length_of_get (HoldsVector.get_re hV (⟨0, hn⟩ : Fin n))
  have hfl := Store.lt_length_of_get hf0
  have hzl : z.1 < m.store.length := Store.lt_length_of_lt_len (by omega : z.2 < _)
  have htl : t.1 < m.store.length := Store.lt_length_of_lt_len (by omega : t.2 < _)
  let F := Store.inBlock f.1 f.2 1 ⊔ ((Store.inBlock t.1 t.2 4 ⊔ Store.inBlock z.1 z.2 2) ⊔
    Store.inBlock v.1 v.2 (2 * n))
  change Writes .total I τ (.loop _ _) _ _ _ m
  refine (writes_loop (N := n) rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun k m' => m'.pos = m.pos ∧ HoldsMatrix a R m'.store ∧ SubstitutionState v f R w k m'.store)
    ⟨rfl, hR, Or.inr ⟨hf0, by simpa only [solvePrefix_zero] using hV, fun i hi => by omega⟩⟩
    ?_).mono le_rfl ?_
  · intro k hk m' hfr ⟨hp, hR', hstate⟩
    have hl : m'.Live [a, v, z, t, f, v, f] := by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [hfr.length_eq] <;> assumption
    rcases hstate with ⟨hone, i, hik, hzero⟩ | ⟨hzero, hV', hdiag⟩
    · have hw := checkedSubstituteColumn_singular hCmp (τ := τ) (n := n) (j := k)
        (a := a) (v := v) (z := z) (t := t) hone
      refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
        (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval]) hl).mono
          bot_le ?_
      rintro m'' _ rfl
      exact ⟨hp, hR', Or.inl ⟨hone, i, by omega, hzero⟩⟩
    · have hw := checkedSubstituteColumn_clear hS hE hCmp (τ := τ) ⟨k, hk⟩ hR' hV'
        hva hza hzv hta htv htz hfa hfv hfz hft hzero
        (by rw [hfr.len_eq]; exact hz) (by rw [hfr.len_eq]; exact ht)
        (by rw [hfr.len_eq]; exact hf)
      refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
        (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval]) hl).mono ?_ ?_
      · exact sup_le_sup le_rfl (sup_le_sup le_rfl
          (Fp.inBlock_le_inBlock (by omega) (by omega)))
      · intro m'' _ ⟨hp', hR'', hcase⟩
        refine ⟨hp'.trans hp, hR'', ?_⟩
        rcases hcase with ⟨hone, heq⟩ | ⟨hzero, hne, hV''⟩
        · exact Or.inl ⟨hone, ⟨k, hk⟩, by simp, heq⟩
        · refine Or.inr ⟨hzero, hV'', fun i hi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
          · exact hdiag i hi
          · have he : i = ⟨k, hk⟩ := Fin.ext hi
            simpa only [he] using hne
  · intro m' _ ⟨hp, hR', hstate⟩
    refine ⟨hp, hR', ?_⟩
    rcases hstate with ⟨hf, i, _, hi⟩ | ⟨hf, hV', hdiag⟩
    · exact Or.inl ⟨hf, i, hi⟩
    · exact Or.inr ⟨hf, by simpa only [solvePrefix_last] using hV', fun i => hdiag i i.isLt⟩

end NLAlib.ShiftedQR
