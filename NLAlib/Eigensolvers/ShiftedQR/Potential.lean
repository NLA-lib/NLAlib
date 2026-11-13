/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Storage
public import NLAlib.Matrix.QRIteration.ShiftSearch
public import NLAlib.Ops.Blas.NormSq
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Logic.Allocation

/-!
# Scalar products of squared subdiagonal moduli

The shift-acceptance statistic is computed from the actual matrix entries by scalar squares,
addition and multiplication. One three-word scratch view is reused for every factor. The
empty product is one and needs no matrix entry read.

## Main results

* `NLAlib.ShiftedQR.subdiagProductWithScratch`: the visible scalar product loop.
* `NLAlib.ShiftedQR.subdiagProduct`: one scoped scratch allocation around the whole loop.
* `NLAlib.ShiftedQR.subdiagProductWithScratch_writes`: total exact product calculation.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- One product round in the enclosing loop's context: dimensions `n,k`, the three operand
offsets, then the current factor index. All three norm calls and the multiply remain visible. -/
def subdiagProductRound : Stmt Op Tst :=
  .seq (.frame []
    [⟨0, .var 2 + .const 2 *
      ((.var 0 - .const 1 - .var 1 + .var 5) * .var 0 +
        (.var 0 - .const 1 - .var 1 + .var 5 + .const 1))⟩, ⟨1, .var 3⟩]
    PairScalar.normSq.body)
    (.call (Has.inj ScalarOp.mul) [] [⟨2, .var 4⟩, ⟨1, .var 3 + .const 2⟩] [⟨2, .var 4⟩])

/-- Multiply the last `k` squared subdiagonal moduli of an order-`n` matrix. The three-word
scratch view is caller-owned; the single output word starts uninitialized. -/
def subdiagProductWithScratch : Impl Op Tst where
  nd := 2
  nin := 2
  nout := 1
  body := .seq (.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨2, .var 4⟩])
    (.loop (.var 1) subdiagProductRound)

/-- Scope the three scratch words once for the whole subdiagonal product calculation. -/
def subdiagProduct : Impl Op Tst := opsImpl% [n, k] (A) → (P) {
  let T ← alloc 3;
  run subdiagProductWithScratch.body [n, k] (A, T, P)
}

/-- The scalar product returns exactly the mathematical squared-potential statistic. Spatial
separation preserves the input matrix and permits disjoint views of one underlying buffer. -/
theorem subdiagProductWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n k : ℕ} {a t p : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hk : k ≤ n) (hH : HoldsMatrix a H m.store)
    (ht : t.2 + 3 ≤ m.store.len t.1) (hp : p.2 < m.store.len p.1)
    (hat : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock t.1 t.2 3))
    (hap : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock p.1 p.2 1))
    (htp : Fp.Disj (Store.inBlock t.1 t.2 3) (Store.inBlock p.1 p.2 1)) :
    Writes .total I τ subdiagProductWithScratch.body (Env.frame [n + 1, k] [a, t, p])
      (Store.inBlock p.1 p.2 1 ⊔ Store.inBlock t.1 t.2 3)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get p.1 p.2 = some (subdiagNormSqProd k H)) m := by
  let value := fun j => if hj : n - k + j < n then
    ‖H (⟨n - k + j, hj⟩ : Fin n).succ (⟨n - k + j, hj⟩ : Fin n).castSucc‖ ^ 2 else 1
  let F := Store.inBlock p.1 p.2 1 ⊔ Store.inBlock t.1 t.2 3
  have hpl := Store.lt_length_of_lt_len hp
  have htl := Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by omega)
  have hal := Store.lt_length_of_get (hH.get_re 0 0)
  unfold subdiagProductWithScratch
  refine (writes_call_const (hS (.lit 1)) rfl trivial hp).seq_le le_sup_left ?_
  intro m₁ hfr₁ ⟨hp₁, hOne⟩
  have hOne' : m₁.store.get p.1 p.2 = some (1 : ℝ) := by
    have hlit : M.lit 1 = (1 : ℝ) := by simpa using hE.lit 1
    simpa only [hlit] using hOne
  have hH₁ := hH.of_eqOff hfr₁ hap.symm
  have hloop : Writes .total I τ (.loop (.var 1) subdiagProductRound)
      (Env.frame [n + 1, k] [a, t, p]) F
      (fun m' => m'.pos = m₁.pos ∧
        m'.store.get p.1 p.2 = some (∏ j ∈ Finset.range k, value j)) m₁ := by
    refine writes_loop rfl (fun _ => F) (fun _ _ => le_rfl)
      (fun i m' => m'.pos = m₁.pos ∧
        m'.store.get p.1 p.2 = some (∏ j ∈ Finset.range i, value j))
      (by simpa using And.intro (rfl : m₁.pos = m₁.pos) hOne') ?_
    intro i hi m' hfr ⟨hpos, hProd⟩
    unfold subdiagProductRound
    let q : Fin n := ⟨n - k + i, by omega⟩
    have hH' := hH₁.of_eqOff hfr (Fp.disj_sup_left.mpr ⟨hap.symm, hat.symm⟩)
    have hentry : Store.inBlock a.1 (a.2 + 2 * (q * (n + 1) + (q + 1))) 2 ≤
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) := by
      apply Fp.inBlock_le_inBlock (by omega)
      have hq := Idx.add_lt_mul q.castSucc.isLt q.succ.isLt
      dsimp only [Fin.val_castSucc, Fin.val_succ] at hq
      omega
    have hnorm := PairScalar.normSq_writes (τ := τ) (m := m')
      (x := (a.1, a.2 + 2 * (q * (n + 1) + (q + 1)))) (t := t) hS hE
      (hH'.get_re q.succ q.castSucc) (hH'.get_im q.succ q.castSucc)
      (by rw [hfr.len_eq, hfr₁.len_eq]; exact ht) (hat.mono hentry le_rfl)
    refine hnorm.frame_seq_le rfl rfl
      (by simp [Mem.Live, hfr.length_eq, hfr₁.length_eq, hal, htl]) le_sup_right ?_
    intro m'' hfr' ⟨hp', hNorm⟩
    have hProd' := hfr'.keep (Store.readsOnly_get _ _ _) htp hProd
    refine (writes_call_bin (hS .mul) rfl rfl trivial hProd' hNorm rfl
      (fun _ => ⟨by room, by room⟩)).mono le_sup_left ?_
    intro m''' _ ⟨hp'', hMul⟩
    refine ⟨hp''.trans (hp'.trans hpos), ?_⟩
    rw [Finset.prod_range_succ]
    have hvalue : value i = (H q.succ q.castSucc).re ^ 2 +
        (H q.succ q.castSucc).im ^ 2 := by
      simp only [value, dif_pos (show n - k + i < n by omega)]
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [q, pow_two]
    have hmul (x y : ℝ) : M.mul x y = x * y := hE.mul x y
    simpa only [hmul, hvalue] using hMul
  exact hloop.mono le_rfl fun m' _ h =>
    ⟨h.1.trans hp₁, by simpa only [value, ← subdiagNormSqProd_eq_prod_range k hk H] using h.2⟩

/-- The scoped product routine returns the exact statistic and frees its three scratch words.
Only the matrix/output separation and one output word of capacity are supplied by the caller. -/
theorem subdiagProduct_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n k : ℕ} {a p : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hk : k ≤ n) (hH : HoldsMatrix a H m.store) (hp : p.2 < m.store.len p.1)
    (hap : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock p.1 p.2 1)) :
    Writes .total I τ subdiagProduct.body (Env.frame [n + 1, k] [a, p])
      (Store.inBlock p.1 p.2 1)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get p.1 p.2 = some (subdiagNormSqProd k H)) m := by
  have hpl := Store.lt_length_of_lt_len hp
  have hal := Store.lt_length_of_get (hH.get_re 0 0)
  change Writes .total I τ (Stmt.allocs [.const 3] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [3]) rfl
    (fun hBelow h => ⟨h.1, ((hBelow p.1 hpl).2 p.2).trans h.2⟩) ?_
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : store.len t.1 = 3 := by simpa [t] using hlens 0 (by simp)
  have hat : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock t.1 t.2 3) := Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have htp : Fp.Disj (Store.inBlock t.1 t.2 3) (Store.inBlock p.1 p.2 1) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have hbody := subdiagProductWithScratch_writes (τ := τ) (m := ⟨store, m.pos⟩)
    (t := t) hS hE hk (hH.of_below hBelow hal)
    (by dsimp [t]; simpa only [Nat.zero_add] using ht.ge)
    (by rw [(hBelow p.1 hpl).1]; exact hp) hat hap htp
  exact (hbody.in_frame rfl rfl (by simp [Mem.Live, t, hlen]; omega)).mono
    (sup_le le_sup_left (Fp.inBlock_le_sup_above le_rfl)) (fun _ _ h => h)

end NLAlib.ShiftedQR
