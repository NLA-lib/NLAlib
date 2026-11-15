/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Coefficients
public import NLAlib.Eigensolvers.ShiftedQR.RotationLoops
public import NLAlib.Eigensolvers.ShiftedQR.RowSolveMath

/-!
# Stored Givens factorization for an exact row solve

The working matrix is updated in place. Each adjacent-row rotation stores its two complex
coefficients in four consecutive words so the row solve can apply them in reverse order.
The coefficient computation and row rotations are the existing scalar programs.

## Main results

* `NLAlib.ShiftedQR.factorRows`: the scalar factorization sweep with saved coefficients.
* `NLAlib.ShiftedQR.HoldsCoefficients`: the actual stored coefficient prefix.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Compute the next factorization coefficients into their permanent pair views. -/
def factorCoefficients : Impl Op Tst := opsImpl% [n, k] (R, Cf) → (Cf) {
  run coefficients.body [] (R[2 * (k * n + k)], R[2 * (k * n + k + 1)],
    Cf[4 * k], Cf[4 * k + 2])
}

/-- Compute and retain one rotation, then apply it to the working matrix. -/
def factorRound : Impl Op Tst := opsImpl% [n, k] (R, Cf) → (R, Cf) {
  run factorCoefficients.body [n, k] (R, Cf, Cf);
  run rotateRows.body [n, k] (R, Cf[4 * k], Cf[4 * k + 2], R)
}

/-- All adjacent-row rotations of the Givens factorization, with saved coefficients. -/
def factorRows : Impl Op Tst := opsImpl% [n] (R, Cf) → (R, Cf) {
  for k < n - 1 {
    run factorRound.body [n, k] (R, Cf, R, Cf)
  }
}

/-- Saved rotation $j$ occupies the pairs at offsets $4j$ and $4j+2$. -/
def HoldsCoefficients {n : ℕ} (cf : ℕ × ℕ) (D : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (s : Store ℝ) : Prop :=
  ∀ j < k,
    s.readBlock cf.1 (cf.2 + 4 * j) 2 = some [(stepCoefs D j).1.re, (stepCoefs D j).1.im] ∧
    s.readBlock cf.1 (cf.2 + 4 * j + 2) 2 = some [(stepCoefs D j).2.re, (stepCoefs D j).2.im]

/-- The saved coefficient prefix reads only its first four words per completed round. -/
theorem readsOnly_holdsCoefficients {n : ℕ} (cf : ℕ × ℕ)
    (D : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    Store.ReadsOnly (Store.inBlock cf.1 cf.2 (4 * k)) (HoldsCoefficients cf D k) := by
  intro s s' hg h j hj
  have h₀ : Store.inBlock cf.1 (cf.2 + 4 * j) 2 ≤ Store.inBlock cf.1 cf.2 (4 * k) :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have h₁ : Store.inBlock cf.1 (cf.2 + 4 * j + 2) 2 ≤ Store.inBlock cf.1 cf.2 (4 * k) :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  exact ⟨Store.readsOnly_readBlock _ _ _ _ s s' (fun b i hi => hg b i (h₀ b i hi)) (h j hj).1,
    Store.readsOnly_readBlock _ _ _ _ s s' (fun b i hi => hg b i (h₁ b i hi)) (h j hj).2⟩

/-- A newly stored rotation extends the retained coefficient prefix. -/
theorem HoldsCoefficients.succ {n k : ℕ} {cf : ℕ × ℕ}
    {D : Matrix (Fin n) (Fin n) ℂ} {s : Store ℝ} (h : HoldsCoefficients cf D k s)
    (hc : s.readBlock cf.1 (cf.2 + 4 * k) 2 =
      some [(stepCoefs D k).1.re, (stepCoefs D k).1.im])
    (hs : s.readBlock cf.1 (cf.2 + 4 * k + 2) 2 =
      some [(stepCoefs D k).2.re, (stepCoefs D k).2.im]) : HoldsCoefficients cf D (k + 1) s := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact h j hj
  · exact ⟨hc, hs⟩

/-- The coefficient subprogram preserves the matrix and extends the saved prefix, including
for a zero input pair. [GolubVanLoan2013, Algorithm 5.2.4]. -/
theorem factorCoefficients_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {a cf : ℕ × ℕ}
    {D : Matrix (Fin n) (Fin n) ℂ} (hk : k + 1 < n) (hac : a.1 ≠ cf.1)
    (hH : HoldsMatrix a (givensHessenbergState D k).2 m.store)
    (hC : HoldsCoefficients cf D k m.store) (hcf : cf.2 + 4 * n ≤ m.store.len cf.1) :
    Writes .total I τ factorCoefficients.body (Env.frame [n, k] [a, cf, cf])
      (Store.inBlock cf.1 (cf.2 + 4 * k) 4)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (givensHessenbergState D k).2 m'.store ∧
        HoldsCoefficients cf D (k + 1) m'.store) m := by
  let r : Fin n := ⟨k, by omega⟩
  let r' : Fin n := ⟨k + 1, hk⟩
  let c : ℕ × ℕ := (cf.1, cf.2 + 4 * k)
  let s : ℕ × ℕ := (cf.1, cf.2 + 4 * k + 2)
  have hc : c.2 + 2 ≤ m.store.len c.1 := by dsimp [c]; omega
  have hs : s.2 + 2 ≤ m.store.len s.1 := by dsimp [s]; omega
  have hw := coefficients_writes hS hE hCmp (τ := τ) (c := c) (s := s)
    (a := rotationEntry a n (r, r)) (b := rotationEntry a n (r', r))
    (Fp.disj_inBlock_of_le (by dsimp [c, s]; omega))
    (hH.get_re r r) (hH.get_im r r) (hH.get_re r' r) (hH.get_im r' r) hc hs
  have hal := Store.lt_length_of_get (hH.get_re r r)
  have hcl : cf.1 < m.store.length := Store.lt_length_of_lt_len (by omega : cf.2 < _)
  have hl : m.Live [rotationEntry a n (r, r), rotationEntry a n (r', r), c, s] := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz | hz | hz <;> subst z <;> dsimp [rotationEntry, c, s] <;> assumption
  have hwrite : Fp.blocks [c, s] [2, 2] ≤ Store.inBlock cf.1 (cf.2 + 4 * k) 4 := by
    simpa only [Fp.blocks, sup_bot_eq, c, s, Nat.add_assoc] using
      (le_of_eq (Fp.inBlock_add cf.1 (cf.2 + 4 * k) 2 2))
  refine (writes_frame rfl (by simp [Operand.evalList, Operand.eval, Env.frame,
    IExp.eval, rotationEntry, r, r', c, s, Nat.add_assoc]) hl hw).mono hwrite ?_
  intro m' hfr hp
  have hfr' := hfr.mono hwrite
  have hH' := hH.of_eqOff hfr' (Fp.disj_inBlock_of_ne hac.symm)
  have hC' := hfr'.keep (readsOnly_holdsCoefficients cf D k)
    (Fp.disj_inBlock_of_le (by omega)).symm hC
  obtain ⟨xs, ys, hx, hy, he⟩ := Mem.readBlocks_cons_eq_some.mp hp.2
  obtain ⟨hxs, hys⟩ := List.cons.inj he
  cases hxs
  cases hys
  obtain ⟨zs, ws, hz, _, he⟩ := Mem.readBlocks_cons_eq_some.mp hy
  obtain ⟨hzs, _⟩ := List.cons.inj he
  cases hzs
  refine ⟨hp.1, hH', hC'.succ ?_ ?_⟩
  · simpa only [stepCoefs, dif_pos hk, c, r, r'] using hx
  · simpa only [stepCoefs, dif_pos hk, s, r, r'] using hz
/-- One retained Givens rotation advances the exact matrix state and its coefficient prefix.
[GolubVanLoan2013, Algorithm 5.2.4]. -/
theorem factorRound_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {a cf : ℕ × ℕ}
    {D : Matrix (Fin n) (Fin n) ℂ} (hk : k + 1 < n) (hac : a.1 ≠ cf.1)
    (hH : HoldsMatrix a (givensHessenbergState D k).2 m.store)
    (hC : HoldsCoefficients cf D k m.store) (hcf : cf.2 + 4 * n ≤ m.store.len cf.1) :
    Writes .total I τ factorRound.body (Env.frame [n, k] [a, cf, a, cf])
      (Store.inBlock a.1 a.2 (2 * (n * n)) ⊔ Store.inBlock cf.1 (cf.2 + 4 * k) 4)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (givensHessenbergState D (k + 1)).2 m'.store ∧
        HoldsCoefficients cf D (k + 1) m'.store) m := by
  have hal : a.1 < m.store.length := Store.lt_length_of_get
    (hH.get_re (⟨k, by omega⟩ : Fin n) ⟨k, by omega⟩)
  have hcl : cf.1 < m.store.length := Store.lt_length_of_lt_len (by omega : cf.2 < _)
  have hl : m.Live [a, cf, cf] := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have hw := factorCoefficients_writes hS hE hCmp (τ := τ) hk hac hH hC hcf
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hw.in_frame rfl rfl hl) le_sup_right
    fun m' hfr ⟨hp, hH', hC'⟩ => ?_
  obtain ⟨hc, hs⟩ := hC' k (by omega)
  let c : ℕ × ℕ := (cf.1, cf.2 + 4 * k)
  let s : ℕ × ℕ := (cf.1, cf.2 + 4 * k + 2)
  have hr := rotateRows_writes hS hE (τ := τ) (c := c) (s := s) hk hH' hc hs
    (Fp.disj_inBlock_of_ne hac) (Fp.disj_inBlock_of_ne hac)
  have hl' : m'.Live [a, c, s, a] := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz | hz | hz <;> subst z
    all_goals try dsimp only [c, s, Prod.fst]
    all_goals rw [hfr.length_eq]; assumption
  refine (hr.in_frame rfl (by simp [Operand.evalList, Operand.eval, Env.frame,
    IExp.eval, c, s, Nat.add_assoc]) hl').mono le_sup_left ?_
  intro m'' hfr' ⟨hp', hH''⟩
  refine ⟨hp'.trans hp, ?_, hfr'.keep (readsOnly_holdsCoefficients cf D (k + 1))
    (Fp.disj_inBlock_of_ne hac) hC'⟩
  simpa only [stepCoefs_mul_state D hk] using hH''

/-- The scalar factorization sweep returns the full Givens triangular factor and the saved
rotation sequence. Every pair, including zero pairs, follows the actual coefficient branch.
[GolubVanLoan2013, Algorithm 5.2.4]. -/
theorem factorRows_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a cf : ℕ × ℕ}
    {D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hac : a.1 ≠ cf.1)
    (hH : HoldsMatrix a D m.store) (hcf : cf.2 + 4 * (n + 1) ≤ m.store.len cf.1) :
    Writes .total I τ factorRows.body (Env.frame [n + 1] [a, cf, a, cf])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock cf.1 cf.2 (4 * (n + 1)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (givensHessenbergR D) m'.store ∧
        HoldsCoefficients cf D n m'.store) m := by
  have hal : a.1 < m.store.length := Store.lt_length_of_get
    (hH.get_re (0 : Fin (n + 1)) 0)
  have hcl : cf.1 < m.store.length := Store.lt_length_of_lt_len (by omega : cf.2 < _)
  let F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock cf.1 cf.2 (4 * (n + 1))
  change Writes .total I τ (.loop _ _) _ _ _ m
  refine (writes_loop (N := n) rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun k m' => m'.pos = m.pos ∧ HoldsMatrix a (givensHessenbergState D k).2 m'.store ∧
      HoldsCoefficients cf D k m'.store) ⟨rfl, hH, fun j hj => by omega⟩ ?_).mono
      le_rfl (fun _ _ h => ⟨h.1, by simpa only [factorState_last] using h.2.1, h.2.2⟩)
  intro k hk m' hfr ⟨hp, hH', hC⟩
  have hw := factorRound_writes hS hE hCmp (τ := τ) (by omega : k + 1 < n + 1) hac hH' hC
    (by rw [hfr.len_eq]; exact hcf)
  have hl : m'.Live [a, cf, a, cf] := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> rw [hfr.length_eq] <;> assumption
  refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval]) hl).mono ?_ ?_
  · exact sup_le le_sup_left ((Fp.inBlock_le_inBlock (by omega) (by omega)).trans le_sup_right)
  · intro m'' _ h
    exact ⟨h.1.trans hp, h.2⟩

end NLAlib.ShiftedQR
