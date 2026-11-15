/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.IterationAlg
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Preparing an actual shift-strategy iteration

The concrete preparation program calls the local Ritz routine on the actual stored matrix,
then computes its subdiagonal product, contraction target, exceptional radius and zero flag
with the existing scalar implementations. Disjoint producer blocks retain every earlier
result, including the stored Ritz column used by the subsequent ordered search.

## Main results

* `NLAlib.ShiftedQR.prepareIteration_writes`: total stored Ritz values and strategy registers.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has CmpTst Q]

omit [Has EigenvalueKernelOp O] [Has CmpTst Q] in
private theorem radiusFlag_writes {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I)
    {tape : Tape ℝ} {μ : Mem ℝ} {ρ : Env} {m : ℕ}
    {ds : List IExp} {args : List Operand} {flag : Operand}
    {p b theta alpha rad f : ℕ × ℕ} {P B θ α : ℝ}
    (hd : IExp.evalList ρ.idx ds = some [m])
    (ha : Operand.evalList ρ args = some [p, b, theta, alpha, rad])
    (hf : flag.eval ρ = some f) (hl : μ.Live [p, b, theta, alpha, rad])
    (hP : μ.store.get p.1 p.2 = some P) (hB : μ.store.get b.1 b.2 = some B)
    (hθ : μ.store.get theta.1 theta.2 = some θ)
    (hα : μ.store.get alpha.1 alpha.2 = some α)
    (hP0 : 0 ≤ P) (hB0 : 0 ≤ B)
    (hr : rad.2 < μ.store.len rad.1) (hFlag : f.2 < μ.store.len f.1)
    (hsep : Fp.Disj (Store.inBlock rad.1 rad.2 1)
      (Store.inBlock b.1 b.2 1 ⊔ Store.inBlock theta.1 theta.2 1 ⊔
        Store.inBlock alpha.1 alpha.2 1))
    (hrf : Fp.Disj (Store.inBlock rad.1 rad.2 1) (Store.inBlock f.1 f.2 1)) :
    Writes .total I tape (.seq (.frame ds args radius.body)
      (.call (Has.inj IndexOp.lit) [.const 0] [] [flag])) ρ
      (Fp.blocks [rad, f] [1, 1])
      (fun μ' => μ'.pos = μ.pos ∧ μ'.readBlocks [rad, f] [1, 1] =
        some [[Real.sqrt^[m] (2 * B * Real.sqrt P) * θ * α], [0]]) μ := by
  have hrad := (radius_writes (k := m) (τ := tape) hS hE
    hP hB hθ hα hP0 hB0 hr hsep).readBlock_of_get
  refine (hrad.in_frame hd ha hl).seq_readBlock
    (by simpa only [Fp.blocks, sup_bot_eq] using hrf) ?_
  intro μ' hfr _ _
  have hzero := (writes_indexLit (τ := tape) (ρ := ρ) (m := μ') hL
    (e := .const 0) rfl hf (by rw [hfr.len_eq]; exact hFlag)).readBlock_of_get
  have he : M.lit 0 = 0 := by simpa using hE.lit 0
  simpa only [Nat.cast_zero, he] using hzero.readBlocks_singleton

private def registersCode : Stmt O Q :=
  .seq (.frame [.var 0, .var 2] [⟨0, .var 3⟩, ⟨4, .var 7⟩] subdiagProduct.body)
    (.seq (.call (Has.inj ScalarOp.mul) [] [⟨2, .var 5 + .const 1⟩, ⟨4, .var 7⟩]
      [⟨4, .var 7 + .const 1⟩])
      (.seq (.frame [.var 1] [⟨4, .var 7⟩, ⟨1, .var 4 + .const 1⟩,
        ⟨1, .var 4 + .const 2⟩, ⟨1, .var 4 + .const 3⟩, ⟨4, .var 7 + .const 2⟩] radius.body)
        (.call (Has.inj IndexOp.lit) [.const 0] [] [⟨4, .var 7 + .const 3⟩])))

omit [Has EigenvalueKernelOp O] [Has CmpTst Q] in
private theorem registers_writes {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m k : ℕ} {w p c ss r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {tol B θ α γ threshold rate : ℝ}
    (hkn : k ≤ n) (hB0 : 0 ≤ B) (hH : HoldsMatrix w H μ.store)
    (hP : μ.store.readBlock p.1 p.2 5 = some [tol, B, θ, α, γ])
    (hC : μ.store.readBlock c.1 c.2 2 = some [threshold, rate])
    (hr : r.2 + 4 ≤ μ.store.len r.1)
    (hRI : Fp.Disj (Store.inBlock r.1 r.2 4)
      (Fp.blocks [w, p, c] [2 * ((n + 1) * (n + 1)), 5, 2])) :
    Writes .total I tape registersCode (Env.frame [n + 1, m, k] [w, p, c, ss, r])
      (Fp.blocks [r, (r.1, r.2 + 1), (r.1, r.2 + 2), (r.1, r.2 + 3)] [1, 1, 1, 1])
      (fun μ' => μ'.pos = μ.pos ∧
        μ'.readBlocks [r, (r.1, r.2 + 1), (r.1, r.2 + 2), (r.1, r.2 + 3)] [1, 1, 1, 1] =
          some [[subdiagNormSqProd k H], [rate * subdiagNormSqProd k H],
            [Real.sqrt^[m] (2 * B * Real.sqrt (subdiagNormSqProd k H)) * θ * α], [0]]) μ := by
  have hd (i j : ℕ) (hij : i ≠ j) :
      Fp.Disj (Store.inBlock r.1 (r.2 + i) 1) (Store.inBlock r.1 (r.2 + j) 1) := by
    intro b q hi hj
    dsimp only [Store.inBlock] at hi hj
    omega
  have hwl := Store.lt_length_of_get (hH.get_re 0 0)
  have hrl := Store.lt_length_of_lt_len (show r.2 < μ.store.len r.1 by omega)
  have hinputs : μ.readBlocks [p, c] [5, 2] = some [[tol, B, θ, α, γ], [threshold, rate]] := by
    simp [Mem.readBlocks, hP, hC]
  have hzero := (subdiagProduct_writes (p := r) (a := w) (τ := tape) hS hE hkn hH (by omega)
    (hRI.symm.mono (by fp_sub) (by fp_sub))).readBlock_of_get
  refine (hzero.in_frame rfl rfl (by simp [Mem.Live]; omega)).seq_readBlock
    (zs := [(r.1, r.2 + 1), (r.1, r.2 + 2), (r.1, r.2 + 3)]) (ls := [1, 1, 1])
    (by simp only [Fp.blocks, Fp.disj_sup_right, Fp.disj_bot_right]
        exact ⟨hd 0 1 (by omega), hd 0 2 (by omega), hd 0 3 (by omega), trivial⟩) ?_
  intro μ₁ hfr₀ _ hProd
  have hi₁ := Mem.readBlocks_of_eqOff hfr₀ (hRI.mono (by fp_sub) (by fp_sub)) hinputs
  have hc₁ := Mem.readBlocks_getD hi₁ (i := 1) (by simp)
  have hRate : μ₁.store.get c.1 (c.2 + 1) = some rate := by
    simpa using Store.get_of_readBlock hc₁ (j := 1) (by simp) (0 : ℝ)
  have hProdGet : μ₁.store.get r.1 r.2 = some (subdiagNormSqProd k H) := by
    simpa using Store.get_of_readBlock hProd (j := 0) (by omega) (0 : ℝ)
  have hcLive := Store.lt_length_of_get hRate
  have hrLive := Store.lt_length_of_get hProdGet
  have hmul : Writes .total I tape
      (.call (Has.inj ScalarOp.mul) [] [⟨2, .var 5 + .const 1⟩, ⟨4, .var 7⟩]
        [⟨4, .var 7 + .const 1⟩]) (Env.frame [n + 1, m, k] [w, p, c, ss, r])
      (Store.inBlock r.1 (r.2 + 1) 1)
      (fun μ' => μ'.pos = μ₁.pos ∧ μ'.store.readBlock r.1 (r.2 + 1) 1 =
        some [rate * subdiagNormSqProd k H]) μ₁ := by
    refine (writes_call_bin (hS .mul) (x := (c.1, c.2 + 1))
      (y := r) (z := (r.1, r.2 + 1)) rfl rfl trivial hRate hProdGet ?_
      (fun _ => ⟨by simp [Mem.Live]; omega,
        by dsimp only; rw [hfr₀.len_eq]; omega⟩)).readBlock_of_get
    simpa only [id_eq] using congrArg some (hE.mul rate (subdiagNormSqProd k H))
  refine hmul.seq_readBlock (zs := [(r.1, r.2 + 2), (r.1, r.2 + 3)]) (ls := [1, 1])
    (by simp only [Fp.blocks, Fp.disj_sup_right, Fp.disj_bot_right]
        exact ⟨hd 1 2 (by omega), hd 1 3 (by omega), trivial⟩) ?_
  intro μ₂ hfr₁ _ _
  have hi₂ := Mem.readBlocks_of_eqOff hfr₁ (hRI.mono (by fp_sub) (by fp_sub)) hi₁
  have hp₂ := Mem.readBlocks_getD hi₂ (i := 0) (by simp)
  have hB : μ₂.store.get p.1 (p.2 + 1) = some B := by
    simpa using Store.get_of_readBlock hp₂ (j := 1) (by simp) (0 : ℝ)
  have hθ : μ₂.store.get p.1 (p.2 + 2) = some θ := by
    simpa using Store.get_of_readBlock hp₂ (j := 2) (by simp) (0 : ℝ)
  have hα : μ₂.store.get p.1 (p.2 + 3) = some α := by
    simpa using Store.get_of_readBlock hp₂ (j := 3) (by simp) (0 : ℝ)
  have hProd₂ := hfr₁.keep (Store.readsOnly_readBlock r.1 r.2 1 [subdiagNormSqProd k H])
    (by simpa only [Nat.add_zero] using hd 1 0 (by omega)) hProd
  have hProdGet₂ : μ₂.store.get r.1 r.2 = some (subdiagNormSqProd k H) := by
    simpa using Store.get_of_readBlock hProd₂ (j := 0) (by omega) (0 : ℝ)
  have hbl := Store.lt_length_of_get hB
  have hpl := Store.lt_length_of_get hProdGet₂
  have hcap : r.2 + 4 ≤ μ₂.store.len r.1 := by rw [hfr₁.len_eq, hfr₀.len_eq]; exact hr
  refine radiusFlag_writes hS hE hL rfl rfl rfl (by simp [Mem.Live]; omega)
    hProdGet₂ hB hθ hα ?_ hB0 (by dsimp; omega) (by dsimp; omega)
    (hRI.mono (by fp_sub) (by fp_sub)) (hd 2 3 (by omega))
  unfold subdiagNormSqProd
  exact Finset.prod_nonneg fun _ _ => sq_nonneg _


private theorem registers_readBlock {μ : Mem ℝ} {r : ℕ × ℕ} {a b c d : ℝ}
    (h : μ.readBlocks [r, (r.1, r.2 + 1), (r.1, r.2 + 2), (r.1, r.2 + 3)] [1, 1, 1, 1] =
      some [[a], [b], [c], [d]]) : μ.store.readBlock r.1 r.2 4 = some [a, b, c, d] := by
  refine Store.readBlock_eq_some_iff.mpr ⟨rfl, ?_⟩
  intro i hi
  interval_cases i
  · simpa using Store.get_of_readBlock (Mem.readBlocks_getD h (i := 0) (by simp))
      (j := 0) (by simp) (0 : ℝ)
  · simpa using Store.get_of_readBlock (Mem.readBlocks_getD h (i := 1) (by simp))
      (j := 0) (by simp) (0 : ℝ)
  · simpa using Store.get_of_readBlock (Mem.readBlocks_getD h (i := 2) (by simp))
      (j := 0) (by simp) (0 : ℝ)
  · simpa using Store.get_of_readBlock (Mem.readBlocks_getD h (i := 3) (by simp))
      (j := 0) (by simp) (0 : ℝ)

omit [Has CmpTst Q] in
/-- Concrete preparation returns the local routine's actual Ritz column and four scalar
registers: subdiagonal product, contraction target, exceptional radius and zero flag. All
inputs are protected from the disjoint output views. The degree is the positive power of two
within the trailing block, and the conditioning bound is nonnegative. -/
theorem prepareIteration_writes {M : Machine ℝ} {I : Interp O Q ℝ}
    {eta : ℝ} {K : KernelRoutines eta}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I)
    (hK : IsEigenvalueKernels K I) {tape : Tape ℝ} {μ : Mem ℝ}
    {n m k : ℕ} {w p c ss r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {tol B theta alpha gamma : ℝ}
    (hkm : k = 2 ^ m) (hkn : k ≤ n) (hB : 0 ≤ B)
    (hl : μ.Live [w, p, c, ss, r]) (hH : HoldsMatrix w H μ.store)
    (hP : μ.store.readBlock p.1 p.2 5 = some [tol, B, theta, alpha, gamma])
    (hC : μ.store.readBlock c.1 c.2 2 = some [tol ^ 2, (1 - gamma) ^ (2 * k)])
    (hSS : ss.2 + 2 * k ≤ μ.store.len ss.1) (hR : r.2 + 4 ≤ μ.store.len r.1)
    (hApart : Fp.Apart [ss, r] [2 * k, 4])
    (hsep : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * k) ⊔ Store.inBlock r.1 r.2 4)
      (Fp.blocks [w, p, c] [2 * ((n + 1) * (n + 1)), 5, 2])) :
    Writes .total I tape prepareIteration.body (Env.frame [n + 1, m, k] [w, p, c, ss, r])
      (Store.inBlock ss.1 ss.2 (2 * k) ⊔ Store.inBlock r.1 r.2 4)
      (fun μ' => μ'.pos = μ.pos ∧
        HoldsMatrix ss (shiftColumn (K.ritz (n + 1) k H)) μ'.store ∧
        μ'.store.readBlock r.1 r.2 4 = some [subdiagNormSqProd k H,
          (1 - gamma) ^ (2 * k) * subdiagNormSqProd k H,
          exceptionalRadius k B theta alpha (hessenbergPotential k H), 0]) μ := by
  subst k
  have hwl := hl w (by simp)
  have hssl := hl ss (by simp)
  have hRitz := writes_ritz (τ := tape) (μ := μ)
    (ρ := Env.frame [n + 1, m, 2 ^ m] [w, p, c, ss, r]) hK
    (ds := [.var 0, .var 2]) (ins := [⟨0, .var 3⟩]) (outs := [⟨3, .var 6⟩])
    rfl rfl rfl (by simp [Mem.Live]; omega) hH hSS
  have hRitzRead := hRitz.mono le_rfl (fun μ' _ hp =>
    show μ'.pos = μ.pos ∧ μ'.store.readBlock ss.1 ss.2 (2 * (2 ^ m)) =
      some (matrixWords (listColumn (K.ritz (n + 1) (2 ^ m) H) (2 ^ m))) from
      ⟨hp.1, by simpa only [HoldsMatrix, one_mul] using hp.2⟩)
  change Writes .total I tape (.seq _ registersCode) _ _ _ μ
  refine (hRitzRead.seq_readBlock (zs := [r, (r.1, r.2 + 1), (r.1, r.2 + 2), (r.1, r.2 + 3)])
    (ls := [1, 1, 1, 1])
    (yss := [[subdiagNormSqProd (2 ^ m) H],
      [(1 - gamma) ^ (2 * (2 ^ m)) * subdiagNormSqProd (2 ^ m) H],
      [Real.sqrt^[m] (2 * B * Real.sqrt (subdiagNormSqProd (2 ^ m) H)) * theta * alpha], [0]]) (by
      have hd : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * (2 ^ m))) (Store.inBlock r.1 r.2 4) := by
        simpa only [Fp.Apart, Fp.blocks, sup_bot_eq] using hApart.1
      exact hd.mono le_rfl (by fp_sub)) ?_).mono (by fp_sub) ?_
  · intro μ₁ hfr _ _
    have hH₁ := hH.of_eqOff hfr (hsep.mono le_sup_left (by fp_sub))
    have hP₁ := hfr.keep (Store.readsOnly_readBlock p.1 p.2 5 [tol, B, theta, alpha, gamma])
      (hsep.mono le_sup_left (by fp_sub)) hP
    have hC₁ := hfr.keep
      (Store.readsOnly_readBlock c.1 c.2 2 [tol ^ 2, (1 - gamma) ^ (2 * (2 ^ m))])
      (hsep.mono le_sup_left (by fp_sub)) hC
    exact registers_writes hS hE hL hkn hB hH₁ hP₁ hC₁
      (by rw [hfr.len_eq]; exact hR) (hsep.mono le_sup_right le_rfl)
  · intro μ' _ ⟨hp, hout⟩
    obtain ⟨hSS', hRegisters⟩ := Mem.readBlocks_cons_iff.mp hout
    have hcol : HoldsMatrix ss (listColumn (K.ritz (n + 1) (2 ^ m) H) (2 ^ m)) μ'.store := by
      simpa only [HoldsMatrix, one_mul] using hSS'
    refine ⟨hp, hcol.shiftColumn (K.length_ritz _ _ _), ?_⟩
    simpa only [exceptionalRadius_two_pow_eq hB theta alpha m H] using
      registers_readBlock hRegisters


end NLAlib.ShiftedQR
