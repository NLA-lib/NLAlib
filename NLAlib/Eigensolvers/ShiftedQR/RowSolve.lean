/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveCore
public import NLAlib.Eigensolvers.ShiftedQR.Shift

/-!
# A scoped exact scalar row solve

The input matrix is copied to fresh workspace. Givens factorization, checked forward
substitution and saved reverse rotations compute the row multiplied by its inverse. An actual
zero pivot instead produces a singularity report. Matrix, coefficients, accumulator and scalar
scratch are all scoped; only the vector and report survive.

## Main results

* `NLAlib.ShiftedQR.rowSolve`: the actual scalar implementation with scoped workspace.
* `NLAlib.ShiftedQR.rowSolve_writes`: total singularity-or-inverse correctness.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Solve an upper Hessenberg row system using scoped scalar workspace and a singularity flag.
Algorithm: shifted-qr (run model) -/
def rowSolve : Impl Op Tst := opsImpl% [n] (D, V) → (V, Flag) {
  let R ← alloc (2 * (n * n));
  let Cf ← alloc (4 * n);
  let Acc ← alloc 2;
  let T ← alloc 10;
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (n * n)] (D, R);
  run rowSolveCore.body [n] (R, V, Cf, Acc, T, Flag, V, Flag)
}

/-- The actual scalar solver is total on every upper Hessenberg matrix. Its report is one
only with a proof that the matrix is singular; otherwise the vector is the exact inverse row.
The vector and report use separate buffers, and the supplied report has one writable word.
[GolubVanLoan2013, §5.2.5]. -/
theorem rowSolve_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {d v f : ℕ × ℕ}
    {D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {w : Fin (n + 1) → ℂ}
    (hD : IsUpperHessenberg D) (hH : HoldsMatrix d D m.store) (hV : HoldsVector v w m.store)
    (hfv : f.1 ≠ v.1) (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ rowSolve.body (Env.frame [n + 1] [d, v, v, f])
      (Store.inBlock v.1 v.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧ RowSolveResult v f D w m'.store) m := by
  have hdl := Store.lt_length_of_get (hH.get_re (0 : Fin (n + 1)) 0)
  have hvl := Store.lt_length_of_get (HoldsVector.get_re hV (0 : Fin (n + 1)))
  have hfl : f.1 < m.store.length := Store.lt_length_of_lt_len (by omega : f.2 < _)
  apply writes_allocs_preserving_post
    (lens := [.const 2 * (.var 0 * .var 0), .const 4 * .var 0, .const 2, .const 10])
    (ns := [2 * ((n + 1) * (n + 1)), 4 * (n + 1), 2, 10]) rfl
    (fun hBelow hp => ⟨hp.1, hp.2.of_below hBelow hvl hfl⟩)
  intro store hlen hlens hBelow
  have hlen' : store.length = m.store.length + 4 := by simpa using hlen
  let a : ℕ × ℕ := (m.store.length, 0)
  let cf : ℕ × ℕ := (m.store.length + 1, 0)
  let z : ℕ × ℕ := (m.store.length + 2, 0)
  let t : ℕ × ℕ := (m.store.length + 3, 0)
  let m₁ : Mem ℝ := ⟨store, m.pos⟩
  have ha : a.2 + 2 * ((n + 1) * (n + 1)) ≤ store.len a.1 := by
    simpa [a] using (hlens 0 (by simp)).ge
  have hc : cf.2 + 4 * (n + 1) ≤ store.len cf.1 := by
    simpa [cf] using (hlens 1 (by simp)).ge
  have hz : z.2 + 2 ≤ store.len z.1 := by simpa [z] using (hlens 2 (by simp)).ge
  have ht : t.2 + 10 ≤ store.len t.1 := by simpa [t] using (hlens 3 (by simp)).ge
  have hf' : f.2 + 1 ≤ store.len f.1 := by rw [(hBelow f.1 hfl).1]; exact hf
  have hSep : RowSolveSeparate a v cf z t f := fresh_rowSolveSeparate hvl hfl hfv
  have hH' := hH.of_below hBelow hdl
  have hV' := hV.of_below hBelow hvl
  have hw := copyMatrix_writes hS (τ := τ) (m := m₁) (a := d) (b := a) hH' ha
    (Fp.disj_inBlock_of_ne (by dsimp [a]; omega))
  have hl : m₁.Live [d, a] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb <;> subst b
    · change d.1 < store.length
      omega
    · change m.store.length < store.length
      omega
  change Writes .total I τ (.seq _ _) _ _ _ m₁
  refine Writes.seq_le (hw.in_frame rfl rfl hl) (by fp_sub [a])
    fun m' hfr ⟨hp, hR⟩ => ?_
  have hV'' : HoldsVector v w m'.store := hfr.keep (readsOnly_holdsVector v w)
    (Fp.disj_inBlock_of_ne hSep.va.symm) hV'
  have hc' : cf.2 + 4 * (n + 1) ≤ m'.store.len cf.1 := by rw [hfr.len_eq]; exact hc
  have hz' : z.2 + 2 ≤ m'.store.len z.1 := by rw [hfr.len_eq]; exact hz
  have ht' : t.2 + 10 ≤ m'.store.len t.1 := by rw [hfr.len_eq]; exact ht
  have hf'' : f.2 + 1 ≤ m'.store.len f.1 := by rw [hfr.len_eq]; exact hf'
  have hs := rowSolveCore_writes hS hE hCmp (τ := τ) hD hR hV'' hSep hc' hz' ht' hf''
  exact (hs.in_frame rfl rfl (rowSolve_live hR hV'' hc' hz' ht' hf'')).mono
    (by fp_sub [rowSolveFp, a, cf, z, t]) (fun _ _ h => ⟨h.1.trans hp, h.2⟩)

end NLAlib.ShiftedQR
