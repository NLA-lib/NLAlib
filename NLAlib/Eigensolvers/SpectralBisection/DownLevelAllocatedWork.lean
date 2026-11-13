/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownLevelWork
public import NLAlib.Eigensolvers.SpectralBisection.DownLevelSolve
public import NLAlib.Eigensolvers.SpectralBisection.SlotWork
public import NLAlib.Ops.Logic.Allocation

/-!
# Kernel work of an allocated downward level

The actual allocated body uses the stored canonical node sizes. Disjoint occupied intervals
bound their combined kernel cost by one root-size cost. The shared allocation decomposition
retains arbitrary incoming counts and live scratch history.

## Main results

* `NLAlib.SpectralBisection.downLevel_kernelWeight_le_of_exec`: allocated level kernel bound.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section

variable {K : Type} [Inhabited K]
  (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  {I : Interp DenseOp (CmpTst ⊕ IdxTst) K} {τ : Tape K} {μ : Mem K}
  {n L fuel d base : ℕ} {par lv su sg ma ua qa ea sz kd kp c : ℕ × ℕ}
  (R0 eps0 beta : K) (A : Matrix (Fin n) (Fin n) (K × K))

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "root" => EighNode.mk n A R0 eps0 L
local notation "nodes" => (fun lo => nodeAtSlot F n fuel R0 beta root d lo)

/-- One actual allocated downward level adds at most `(2 * fuel + 9) * T n` to matrix-kernel
weight. Inputs are stored canonical level data and ordinary fresh-scratch geometry. The cost
function is monotone and superadditive; no accuracy or distribution premise is needed. -/
theorem downLevel_kernelWeight_le_of_exec (hS : IsScalar M I) (hL : IsIndexLit M I)
    (hC : IsCmp dec I) (hMM : IsMatrixMul (EntryCodec.pair K) mm I)
    (hQR : IsMatrixQR (EntryCodec.pair K) qr I) (hQ : IsToNat dec I) (hSample : IsSample I)
    (hexact : IsExactNatLit dec M (max n 4))
    (hl : μ.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c])
    (hLevel : StoresLevel M F n fuel R0 beta root d ma sz lv μ)
    (hpar : μ.store.readBlock par.1 par.2 3 = some [R0, eps0, beta])
    (hc : μ.store.readBlock c.1 c.2 5 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf])
    (hGeometry : ∀ s : Store K, s.length = μ.store.length + 1 →
      s.len μ.store.length = 5 → Store.Below μ.store.length μ.store s →
        DownLevelGeometry n d (fun lo => (nodes lo).k)
          par lv su sg ma ua qa ea sz kd kp c (μ.store.length, 0) s)
    (T : ℕ → ℕ) (hT : Monotone T) (hadd : ∀ i j, T i + T j ≤ T (i + j))
    (W : DenseOp → List ℕ → ℕ) {a b : St DenseOp (CmpTst ⊕ IdxTst) K}
    (hmem : a.mem = μ)
    (hr : evalCounted I W τ (downLevel (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)))
      (Env.frame [n, L, fuel, d] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c]) a = some b) :
    Dense.kernelWeight T b.cost ≤ Dense.kernelWeight T a.cost + (2 * fuel + 9) * T n := by
  subst μ
  let statement := downLevel (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
  obtain ⟨inner, final, hInner, hlength, hlens, hBelow, _, hcost, hfinal⟩ :=
    evalCounted_allocsAs_inv (allocations := statement.splitAllocations.1)
      (body := statement.splitAllocations.2) (ns := [5]) (by rfl)
      (by rw [Stmt.allocsAs_splitAllocations]; exact hr)
  have ht : inner.mem.store.len a.mem.store.length = 5 := by
    simpa using hlens 0 (by simp)
  have hGeo := hGeometry inner.mem.store (by simpa using hlength) ht hBelow
  have hLevel' : StoresLevel M F n fuel R0 beta root d ma sz lv inner.mem :=
    hLevel.of_below hBelow (hl ma (by simp)) (hl sz (by simp)) (hl lv (by simp))
  have hBody := evalCounted_frame_body (body := (downLevelImpl
      (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))).body)
    (d := [n, L, fuel, d])
    (as := [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, (a.mem.store.length, 0)])
    rfl rfl hInner
  have hslot (lo : ℕ) (hlo : lo < n) : lo + (nodes lo).k ≤ n := by
    have h := nodeAtSlot_k_le F n fuel R0 eps0 beta L A d lo
    change (nodes lo).k ≤ n - lo at h
    omega
  have hWork := downLevelImpl_kernelWeight_sum_le_of_exec M dec mm qr
    hS hL hC hMM hQR hQ hSample (fun lo => (nodes lo).k) (fun lo => (nodes lo).A)
    R0 eps0 beta (eighLevelParams F R0 eps0 L d).1 (eighLevelParams F R0 eps0 L d).2
    hslot hexact (fun lo hlo => hLevel'.nodeAtSlot_size hlo)
    (fun _ _ hp => hLevel'.nodeAtSlot_matrix hp)
    ((hBelow.readBlock (hl par (by simp)) _ _).trans hpar) hLevel'.2.2
    ((hBelow.readBlock (hl c (by simp)) _ _).trans hc) hGeo T W rfl hBody
  have hSum : (∑ lo ∈ Finset.range n, (2 * fuel + 9) * T ((nodes lo).k)) ≤
      (2 * fuel + 9) * T n := by
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left _ (sum_slotWork_le F n fuel R0 eps0 beta L A d hT hadd)
  have h := hWork.trans (Nat.add_le_add_left hSum _)
  simpa only [hcost, hfinal] using h

end

end NLAlib.SpectralBisection
