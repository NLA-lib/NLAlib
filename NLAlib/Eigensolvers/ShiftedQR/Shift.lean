/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Storage
public import NLAlib.Ops.Blas.MapCorrect
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Logic.Builder

/-!
# Initial working matrix for a shifted QR step

The raw matrix is copied into the working block and the output block. A diagonal traversal
subtracts the supplied complex shift by two real scalar subtractions. All off-diagonal words
are retained by the spatial entry frame.

## Main results

* `NLAlib.ShiftedQR.shiftDiagonal`: the scalar diagonal-shift implementation.
* `NLAlib.ShiftedQR.initializeState`: initialization of the working and conjugated matrices.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Subtract both component words of the complex shift from each diagonal entry in place. -/
def shiftDiagonal : Impl Op Tst where
  nd := 1
  nin := 2
  nout := 1
  body := .loop (.var 0) (.frame [.const 2]
    [⟨0, .var 1 + .const 2 * (.var 4 * .var 0 + .var 4)⟩, ⟨1, .var 2⟩,
      ⟨2, .var 3 + .const 2 * (.var 4 * .var 0 + .var 4)⟩]
    (binaryMap (Has.inj ScalarOp.sub)).body)

/-- Copy the raw matrix into the two state matrices and shift only the working matrix.
The interface is `[n] (A,S) -> (W,Z)`, with all matrix blocks of size `2*n*n`. -/
def initializeState : Impl Op Tst := opsImpl% [n] (A, S) → (W, Z) {
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (n * n)] (A, W);
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (n * n)] (A, Z);
  run shiftDiagonal.body [n] (W, S, W)
}

/-- The mathematical matrix after shifting the first `k` diagonal entries. Entries outside
the finite diagonal are not visited, so any `k >= n` gives the complete diagonal shift. -/
def shiftedPrefix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if i = j ∧ i.val < k then A i j - s else A i j

/-- Before the diagonal traversal the matrix equals the supplied raw matrix. -/
@[simp] theorem shiftedPrefix_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    shiftedPrefix A s 0 = A := by
  ext i j
  simp [shiftedPrefix]

/-- Finishing the diagonal traversal subtracts the scalar multiple of the identity. -/
theorem shiftedPrefix_all {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    shiftedPrefix A s n = A - s • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases hij : i = j <;> simp [shiftedPrefix, hij]

/-- The next visit is the ordinary Mathlib update of the current diagonal entry. -/
theorem shiftedPrefix_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (k : Fin n) :
    shiftedPrefix A s (k + 1) =
      (shiftedPrefix A s k).updateRow k
        (Function.update (shiftedPrefix A s k k) k (A k k - s)) := by
  ext i j
  by_cases hik : i = k
  · subst i
    by_cases hjk : j = k
    · subst j
      simp [shiftedPrefix]
    · simp [shiftedPrefix, Matrix.updateRow_apply, hjk, Ne.symm hjk]
  · have hik' : i.val ≠ k.val := fun h => hik (Fin.ext h)
    have hlt : i.val < k.val + 1 ↔ i.val < k.val := by omega
    simp only [shiftedPrefix, Matrix.of_apply, Matrix.updateRow_apply, if_neg hik, hlt]

/-- Subtract a complex shift from one stored matrix entry, using exactly two scalar
subtractions and the generic binary-map frame. -/
private theorem shiftEntry_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {b a : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {s : ℂ}
    (hH : HoldsMatrix b H m.store) (hs : m.store.readBlock a.1 a.2 2 = some [s.re, s.im])
    (hd : Fp.Disj (Store.inBlock b.1 b.2 (2 * (n * n))) (Store.inBlock a.1 a.2 2))
    (i : Fin n) :
    Writes .total I τ (binaryMap (Has.inj ScalarOp.sub)).body
      (Env.frame [2] [(b.1, b.2 + 2 * (i * n + i)), a,
        (b.1, b.2 + 2 * (i * n + i))])
      (Store.inBlock b.1 (b.2 + 2 * (i * n + i)) 2)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix b
        (H.updateRow i (Function.update (H i) i (H i i - s))) m'.store) m := by
  have hr := hH.read_entry i i
  have hfp : Store.inBlock b.1 (b.2 + 2 * (i * n + i)) 2 ≤
      Store.inBlock b.1 b.2 (2 * (n * n)) := by
    have hi := Idx.add_lt_mul i.isLt i.isLt
    intro c j hj
    exact ⟨hj.1, by have := hj.2.1; omega, by have := hj.2.2; omega⟩
  have hdis : Fp.Disj (Store.inBlock a.1 a.2 2)
      (Store.inBlock b.1 (b.2 + 2 * (i * n + i)) 2) := by
    intro c j ha hb
    exact hd c j (hfp c j hb) ha
  have hw := writes_binaryMap (τ := τ)
    (x := (b.1, b.2 + 2 * (i * n + i)))
    (z := (b.1, b.2 + 2 * (i * n + i))) (hS .sub)
    (Store.holdsVec_of_readBlock hr) (Store.holdsVec_of_readBlock hs)
    (Store.le_len_of_readBlock hr (by omega)) (Or.inr rfl) (Or.inl hdis)
  have hsub (x y : ℝ) : M.sub x y = x - y := hE.sub x y
  exact hw.mono le_rfl fun m' hfr ⟨hv, hp⟩ => ⟨hp,
    hH.of_entry_write i i (H i i - s) hfr
      (by simpa [vec, hsub] using hv 0 (by omega))
      (by simpa [vec, hsub, Nat.add_assoc] using hv 1 (by omega))⟩

/-- The scalar diagonal traversal subtracts the shift from the actual stored matrix and
preserves every word outside that matrix. The supplied shift occupies a disjoint word block. -/
theorem shiftDiagonal_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {b a : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {s : ℂ}
    (hl : m.Live [b, a, b]) (hH : HoldsMatrix b H m.store)
    (hs : m.store.readBlock a.1 a.2 2 = some [s.re, s.im])
    (hd : Fp.Disj (Store.inBlock b.1 b.2 (2 * (n * n))) (Store.inBlock a.1 a.2 2)) :
    Writes .total I τ (shiftDiagonal (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [b, a, b]) (Store.inBlock b.1 b.2 (2 * (n * n)))
      (fun m' => m'.pos = m.pos ∧
        HoldsMatrix b (H - s • (1 : Matrix (Fin n) (Fin n) ℂ)) m'.store) m := by
  suffices hloop : Writes .total I τ (shiftDiagonal (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [b, a, b]) (Store.inBlock b.1 b.2 (2 * (n * n)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix b (shiftedPrefix H s n) m'.store) m by
    simpa only [shiftedPrefix_all] using hloop
  unfold shiftDiagonal
  refine writes_loop rfl
    (fun _ => Store.inBlock b.1 b.2 (2 * (n * n))) (fun _ _ => le_rfl)
    (fun k m' => m'.pos = m.pos ∧ HoldsMatrix b (shiftedPrefix H s k) m'.store)
    ⟨rfl, by simpa using hH⟩ ?_
  intro k hk m' hfr hp
  have hs' := hfr.keep (Store.readsOnly_readBlock _ _ _ _) hd hs
  have hl' : m'.Live [(b.1, b.2 + 2 * (k * n + k)), a,
      (b.1, b.2 + 2 * (k * n + k))] := by
    simpa [Mem.Live] using hl.congr hfr.length_eq
  have hw := shiftEntry_writes (τ := τ) hS hE hp.2 hs' hd (⟨k, hk⟩ : Fin n)
  have hf : Store.inBlock b.1 (b.2 + 2 * (k * n + k)) 2 ≤
      Store.inBlock b.1 b.2 (2 * (n * n)) := by
    have hi := Idx.add_lt_mul hk hk
    intro c j hj
    exact ⟨hj.1, by have := hj.2.1; omega, by have := hj.2.2; omega⟩
  refine (writes_frame (by rfl) (by simp [Operand.evalList, Operand.eval, Env.frame,
    Env.pushIdx, IExp.eval]) hl' hw).mono hf ?_
  intro m'' _ ⟨hpos, hmat⟩
  refine ⟨hpos.trans hp.1, ?_⟩
  have he : shiftedPrefix H s k ⟨k, hk⟩ ⟨k, hk⟩ = H ⟨k, hk⟩ ⟨k, hk⟩ := by
    simp [shiftedPrefix]
  have hsucc := shiftedPrefix_succ H s (⟨k, hk⟩ : Fin n)
  change shiftedPrefix H s (k + 1) = _ at hsucc
  rw [hsucc]
  simpa only [he] using hmat

/-- Copy the actual interleaved words of a matrix using the scalar copy map. -/
theorem copyMatrix_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a b : ℕ × ℕ}
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : HoldsMatrix a H m.store)
    (hB : b.2 + 2 * (n * n) ≤ m.store.len b.1)
    (hd : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n)))
      (Store.inBlock b.1 b.2 (2 * (n * n)))) :
    Writes .total I τ (unaryMap (Has.inj ScalarOp.copy)).body
      (Env.frame [2 * (n * n)] [a, b]) (Store.inBlock b.1 b.2 (2 * (n * n)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix b H m'.store) m := by
  simpa only [HoldsMatrix, List.map_id] using
    (writes_unaryMap_of_disj_or_eq (τ := τ) (f := id) (hS .copy) (Or.inl hd) hH hB)

/-- Initialization copies the actual raw matrix into both state matrices and subtracts the
supplied shift only from the working matrix. The raw matrix and shift occupy disjoint views
from the outputs, and the two output matrices are separate. No initialized output is needed. -/
theorem initializeState_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {a s w z : ℕ × ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {shift : ℂ}
    (hl : m.Live [a, s, w, z]) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hw : w.2 + 2 * (n * n) ≤ m.store.len w.1)
    (hz : z.2 + 2 * (n * n) ≤ m.store.len z.1)
    (haw : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n)))
      (Store.inBlock w.1 w.2 (2 * (n * n))))
    (haz : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n)))
      (Store.inBlock z.1 z.2 (2 * (n * n))))
    (hsw : Fp.Disj (Store.inBlock s.1 s.2 2) (Store.inBlock w.1 w.2 (2 * (n * n))))
    (hsz : Fp.Disj (Store.inBlock s.1 s.2 2) (Store.inBlock z.1 z.2 (2 * (n * n))))
    (hwz : Fp.Disj (Store.inBlock w.1 w.2 (2 * (n * n)))
      (Store.inBlock z.1 z.2 (2 * (n * n)))) :
    Writes .total I τ (initializeState (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [a, s, w, z])
      (Store.inBlock w.1 w.2 (2 * (n * n)) ⊔ Store.inBlock z.1 z.2 (2 * (n * n)))
      (fun m' => m'.pos = m.pos ∧
        HoldsMatrix w (H - shift • (1 : Matrix (Fin n) (Fin n) ℂ)) m'.store ∧
        HoldsMatrix z H m'.store) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length ∧
      w.1 < m.store.length ∧ z.1 < m.store.length := by simpa [Mem.Live] using hl
  unfold initializeState
  refine (copyMatrix_writes (τ := τ) hS hH hw haw).frame_seq_le rfl rfl
    (by simpa [Mem.Live] using And.intro hlive.1 hlive.2.2.1) le_sup_left ?_
  intro m₁ hfr₁ ⟨hp₁, hW₁⟩
  have hA₁ := hH.of_eqOff hfr₁ haw.symm
  have hS₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) hsw.symm hs
  refine (copyMatrix_writes (τ := τ) hS hA₁
    (by rw [hfr₁.len_eq]; exact hz) haz).frame_seq_le rfl rfl
    (by simpa [Mem.Live, ← hfr₁.length_eq] using And.intro hlive.1 hlive.2.2.2)
    le_sup_right ?_
  intro m₂ hfr₂ ⟨hp₂, hZ₂⟩
  have hW₂ := hW₁.of_eqOff hfr₂ hwz.symm
  have hS₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) hsz.symm hS₁
  have hshift := shiftDiagonal_writes (τ := τ) hS hE
    (by simpa [Mem.Live, ← hfr₂.length_eq, ← hfr₁.length_eq] using
      And.intro hlive.2.2.1 (And.intro hlive.2.1 hlive.2.2.1)) hW₂ hS₂ hsw.symm
  refine (hshift.in_frame rfl rfl
    (by simpa [Mem.Live, ← hfr₂.length_eq, ← hfr₁.length_eq] using
      And.intro hlive.2.2.1 (And.intro hlive.2.1 hlive.2.2.1))).mono le_sup_left ?_
  intro m₃ hfr₃ ⟨hp₃, hW₃⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hW₃, hZ₂.of_eqOff hfr₃ hwz⟩

end NLAlib.ShiftedQR
