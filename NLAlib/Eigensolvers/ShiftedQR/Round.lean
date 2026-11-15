/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Alg
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Exact scalar implementation of one QR state transition

The coefficients are computed from the actual working column. The same coefficients rotate
the working matrix and conjugate the output. Spatial frames retain the other matrix and
coefficient words between these calls. Every call is a scalar implementation.

## Main results

* `NLAlib.ShiftedQR.round_writes_word`: the transition on any machine.
* `NLAlib.ShiftedQR.round_writes`: the total simultaneous working/output transition.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- One round on any machine computes the coefficient words `(cv, sv)` of the actual working
column (`NLAlib.ShiftedQR.coefficientWords`), rotates the rows $k, k + 1$ of the working matrix
and conjugates the output by them (`NLAlib.ShiftedQR.machineRowRotation`,
`NLAlib.ShiftedQR.machineColRotation`). The two matrices and four coefficient words are
separated views; output aliases are exact. -/
theorem round_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {w z cf : ℕ × ℕ}
    {W Z : Matrix (Fin n) (Fin n) ℂ} {cv sv : ℂ} (hk : k + 1 < n)
    (hcs : coefficientWords M (W ⟨k, by omega⟩ ⟨k, by omega⟩) (W ⟨k + 1, hk⟩ ⟨k, by omega⟩) =
      (cv, sv))
    (hW : HoldsMatrix w W m.store) (hZ : HoldsMatrix z Z m.store)
    (hc : cf.2 + 4 ≤ m.store.len cf.1)
    (hwz : Fp.Disj (Store.inBlock w.1 w.2 (2 * (n * n)))
      (Store.inBlock z.1 z.2 (2 * (n * n))))
    (hwc : Fp.Disj (Store.inBlock w.1 w.2 (2 * (n * n)))
      (Store.inBlock cf.1 cf.2 4))
    (hzc : Fp.Disj (Store.inBlock z.1 z.2 (2 * (n * n)))
      (Store.inBlock cf.1 cf.2 4)) :
    Writes .total I τ round.body (Env.frame [n, k] [w, z, cf, w, z])
      (Store.inBlock w.1 w.2 (2 * (n * n)) ⊔
        Store.inBlock z.1 z.2 (2 * (n * n)) ⊔ Store.inBlock cf.1 cf.2 4)
      (fun m' => m'.pos = m.pos ∧
        HoldsMatrix w (machineRowRotation M ⟨k, by omega⟩ ⟨k + 1, hk⟩ cv sv W) m'.store ∧
        HoldsMatrix z (machineColRotation M ⟨k, by omega⟩ ⟨k + 1, hk⟩ cv sv
          (machineRowRotation M ⟨k, by omega⟩ ⟨k + 1, hk⟩ cv sv Z)) m'.store) m := by
  let c : ℕ × ℕ := cf
  let s : ℕ × ℕ := (cf.1, cf.2 + 2)
  let i : Fin n := ⟨k, by omega⟩
  let j : Fin n := ⟨k + 1, hk⟩
  have hcsub : Store.inBlock c.1 c.2 2 ≤ Store.inBlock cf.1 cf.2 4 :=
    Fp.inBlock_le_inBlock le_rfl (by dsimp [c]; omega)
  have hssub : Store.inBlock s.1 s.2 2 ≤ Store.inBlock cf.1 cf.2 4 :=
    Fp.inBlock_le_inBlock (by dsimp [s]; omega) (by dsimp [s]; omega)
  have hcs' : Fp.Disj (Store.inBlock c.1 c.2 2) (Store.inBlock s.1 s.2 2) := by
    apply Fp.disj_inBlock_of_le
    rfl
  have hcf : Fp.blocks [c, s] [2, 2] ≤ Store.inBlock cf.1 cf.2 4 := by
    simpa only [Fp.blocks, sup_bot_eq] using sup_le hcsub hssub
  have hcl : cf.1 < m.store.length := Store.lt_length_of_lt_len (by omega : cf.2 < _)
  have hwl : w.1 < m.store.length := Store.lt_length_of_get (hW.get_re i i)
  have hzl : z.1 < m.store.length := Store.lt_length_of_get (hZ.get_re i i)
  have hco := coefficients_writes_word (τ := τ) (m := m)
    (a := (w.1, w.2 + 2 * (k * n + k)))
    (b := (w.1, w.2 + 2 * (k * n + (k + 1))))
    (c := c) (s := s) (u := W i i) (v := W j i) hS hCmp hcs'
    (hW.get_re i i) (hW.get_im i i) (hW.get_re j i) (hW.get_im j i)
    (by dsimp [c]; omega) (by dsimp [s]; omega)
  unfold round
  refine hco.frame_seq_le rfl rfl
    (by simpa [Mem.Live, c, s] using And.intro hwl hcl)
    (hcf.trans le_sup_right) ?_
  intro m₁ hfr₁ ⟨hp₁, hcs₁⟩
  rw [show coefficientWords M (W i i) (W j i) = (cv, sv) from hcs] at hcs₁
  have hc₁ := (Mem.readBlocks_cons_iff.mp hcs₁).1
  have hs₁ := (Mem.readBlocks_cons_iff.mp (Mem.readBlocks_cons_iff.mp hcs₁).2).1
  have hW₁ := hW.of_eqOff hfr₁ (hwc.symm.mono hcf le_rfl)
  have hZ₁ := hZ.of_eqOff hfr₁ (hzc.symm.mono hcf le_rfl)
  have hrw := rotateRows_writes_word (τ := τ) hS hk hW₁ hc₁ hs₁
    (hwc.mono le_rfl hcsub) (hwc.mono le_rfl hssub)
  refine hrw.frame_seq_le rfl rfl
    (by simp [Mem.Live, c, s, hfr₁.length_eq, hwl, hcl])
    (le_sup_left.trans le_sup_left) ?_
  intro m₂ hfr₂ ⟨hp₂, hW₂⟩
  have hc₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _)
    (hwc.mono le_rfl hcsub) hc₁
  have hs₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _)
    (hwc.mono le_rfl hssub) hs₁
  have hZ₂ := hZ₁.of_eqOff hfr₂ hwz
  have hrz := rotateRows_writes_word (τ := τ) hS hk hZ₂ hc₂ hs₂
    (hzc.mono le_rfl hcsub) (hzc.mono le_rfl hssub)
  refine hrz.frame_seq_le rfl rfl
    (by simp [Mem.Live, c, s, hfr₂.length_eq, hfr₁.length_eq, hzl, hcl])
    (le_sup_right.trans le_sup_left) ?_
  intro m₃ hfr₃ ⟨hp₃, hZ₃⟩
  have hc₃ := hfr₃.keep (Store.readsOnly_readBlock _ _ _ _)
    (hzc.mono le_rfl hcsub) hc₂
  have hs₃ := hfr₃.keep (Store.readsOnly_readBlock _ _ _ _)
    (hzc.mono le_rfl hssub) hs₂
  have hW₃ := hW₂.of_eqOff hfr₃ hwz.symm
  have hcols := rotateColumns_writes_word (τ := τ) hS hk hZ₃ hc₃ hs₃
    (hzc.mono le_rfl hcsub) (hzc.mono le_rfl hssub)
  refine (hcols.in_frame rfl rfl
    (by simp [Mem.Live, c, s, hfr₃.length_eq, hfr₂.length_eq, hfr₁.length_eq,
      hzl, hcl])).mono (le_sup_right.trans le_sup_left) ?_
  intro m₄ hfr₄ ⟨hp₄, hZ₄⟩
  exact ⟨hp₄.trans (hp₃.trans (hp₂.trans hp₁)), hW₃.of_eqOff hfr₄ hwz.symm, hZ₄⟩

/-- One exact round computes the mathematical Givens step from the actual working matrix,
rotates that matrix on the left, and conjugates the output by the same rotation. The two
matrices and four coefficient words are separated views; output aliases are exact. -/
theorem round_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {w z cf : ℕ × ℕ}
    {W Z : Matrix (Fin n) (Fin n) ℂ} (hk : k + 1 < n)
    (hW : HoldsMatrix w W m.store) (hZ : HoldsMatrix z Z m.store)
    (hc : cf.2 + 4 ≤ m.store.len cf.1)
    (hwz : Fp.Disj (Store.inBlock w.1 w.2 (2 * (n * n)))
      (Store.inBlock z.1 z.2 (2 * (n * n))))
    (hwc : Fp.Disj (Store.inBlock w.1 w.2 (2 * (n * n)))
      (Store.inBlock cf.1 cf.2 4))
    (hzc : Fp.Disj (Store.inBlock z.1 z.2 (2 * (n * n)))
      (Store.inBlock cf.1 cf.2 4)) :
    Writes .total I τ round.body (Env.frame [n, k] [w, z, cf, w, z])
      (Store.inBlock w.1 w.2 (2 * (n * n)) ⊔
        Store.inBlock z.1 z.2 (2 * (n * n)) ⊔ Store.inBlock cf.1 cf.2 4)
      (fun m' => m'.pos = m.pos ∧
        HoldsMatrix w (givensHessenbergStep W k * W) m'.store ∧
        HoldsMatrix z (givensHessenbergStep W k * Z * (givensHessenbergStep W k)ᴴ)
          m'.store) m := by
  have hij : (⟨k, by omega⟩ : Fin n) ≠ ⟨k + 1, hk⟩ := Fin.ne_of_val_ne (Nat.succ_ne_self k).symm
  have he := givensHessenbergStep_of_lt W (by omega : k < n) hk (by omega : k < n)
  refine (round_writes_word (τ := τ) hS hCmp hk (coefficientWords_eq hE _ _) hW hZ hc hwz hwc
    hzc).mono le_rfl fun _ _ ⟨hp, hW', hZ'⟩ => ⟨hp, ?_, ?_⟩
  · rwa [he, ← machineRowRotation_eq hE hij]
  · rwa [he, ← machineRowRotation_eq hE hij, ← machineColRotation_eq hE hij]

end NLAlib.ShiftedQR
