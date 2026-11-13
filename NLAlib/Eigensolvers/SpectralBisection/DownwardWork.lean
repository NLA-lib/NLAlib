/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownwardArena
public import NLAlib.Eigensolvers.SpectralBisection.DownLevelAllocatedWork
public import NLAlib.Ops.Logic.WeightedLoop

/-!
# Partition-sensitive work of the complete downward pass

The actual stored mathematical level supplies a disjoint node-size partition on every round.
The ordinary level theorem retains the next inputs and future zero size words. Summing the
actual counted kernel charges gives one root-size cost per depth, with arbitrary prior counts.

## Main results

* `NLAlib.SpectralBisection.downwardPass_kernelWeight_le_of_exec`: the complete actual pass.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section

variable {K : Type} [Inhabited K]
  (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  {I : Interp DenseOp (CmpTst ⊕ IdxTst) K} {τ : Tape K} {μ : Mem K} {n L fuel base : ℕ}
  {par lv su sg ma ua qa ea sz kd kp c : ℕ × ℕ}
  (R0 eps0 beta : K) (A : Matrix (Fin n) (Fin n) (K × K))

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "root" => EighNode.mk n A R0 eps0 L
local notation "nodes" => (fun d lo => nodeAtSlot F n fuel R0 beta root d lo)
local notation "region" => (fun d => downLevelOutputFp n d lv su sg ma ua qa ea sz kd kp)

/-- The actual downward pass adds at most one root-size matrix-kernel charge per level.
The model, stored inputs and finite arena capacities are ordinary semantic assumptions;
the counted execution starts from arbitrary prior history. -/
theorem downwardPass_kernelWeight_le_of_exec
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) (hSample : IsSample I)
    (hexact : IsExactNatLit dec M (max n 4))
    (hl : μ.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c])
    (hPos : μ.pos = base)
    (hLevel : StoresLevel M F n fuel R0 beta root 0 ma sz lv μ)
    (hpar : μ.store.readBlock par.1 par.2 3 = some [R0, eps0, beta])
    (hc : μ.store.readBlock c.1 c.2 5 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf])
    (hZero : ∀ e, 1 ≤ e → e ≤ L + 1 → ∀ lo < n,
      μ.store.get sz.1 (sz.2 + n * e + lo) = some (M.lit 0))
    (hRoom : μ.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hPar : Fp.Disj (Store.inBlock par.1 par.2 3)
      (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)))
    (T : ℕ → ℕ) (hT : Monotone T) (hadd : ∀ a b, T a + T b ≤ T (a + b))
    (W : DenseOp → List ℕ → ℕ) {a b : St DenseOp (CmpTst ⊕ IdxTst) K}
    (hmem : a.mem = μ)
    (hr : evalCounted I W τ (downwardPass (node (Op := DenseOp)
      (Tst := CmpTst ⊕ IdxTst))).body
      (Env.frame [n, L, fuel] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c]) a = some b) :
    Dense.kernelWeight T b.cost ≤ Dense.kernelWeight T a.cost +
      (L + 1) * ((2 * fuel + 9) * T n) := by
  subst μ
  let pre := Fp.loopPrefix region
  let P := fun i (ν : Mem K) => ν.pos = base + i * levelSampleSize n ∧
    ν.store.readBlock par.1 par.2 3 = some [R0, eps0, beta] ∧
    ν.store.readBlock c.1 c.2 5 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf] ∧
    StoresLevel M F n fuel R0 beta root i ma sz lv ν ∧
    ∀ e, i + 1 ≤ e → e ≤ L + 1 → ∀ lo < n,
      ν.store.get sz.1 (sz.2 + n * e + lo) = some (M.lit 0)
  have hGeom (i : ℕ) (hi : i ≤ L) (ν : Mem K) (hfr : a.mem.store.EqOff (pre i) ν.store)
      (s : Store K) (hSlength : s.length = ν.store.length + 1)
      (hTlen : s.len ν.store.length = 5) (hBelow : Store.Below ν.store.length ν.store s) :
      DownLevelGeometry n i (fun lo => (nodes i lo).k)
        par lv su sg ma ua qa ea sz kd kp c (ν.store.length, 0) s := by
    have hl' : ν.Live (par :: arenaOperands c ma ua qa ea sz kd kp lv su sg) := by
      intro z hz
      exact (hl.congr hfr.length_eq) z (by simp [arenaOperands] at hz ⊢; tauto)
    apply downLevelGeometry_of_arenas hi ?_ hl' (hRoom.congr hfr.len_eq) hAP hPar.symm
      hSlength hTlen hBelow
    intro lo hlo
    have hk := nodeAtSlot_k_le F n fuel R0 eps0 beta L A i lo
    change (nodes i lo).k ≤ n - lo at hk
    omega
  have h0 : P 0 a.mem := ⟨by simpa using hPos, hpar, hc, hLevel, hZero⟩
  have hb := evalCounted_loop_weight_of_writes (I := I) (W := W) (a := a) (b := b)
    (n := .var 1 + .const 1) (N := L + 1)
    (ρ := Env.frame [n, L, fuel] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c])
    rfl pre (fun i _ z j ⟨k, hk, hx⟩ => ⟨k, by omega, hx⟩) P h0 ?_
    (Dense.kernelWeight T) (fun _ => (2 * fuel + 9) * T n) ?_ hr
  · simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul] using hb.1
  · intro i hi ν hfr hp
    have hLive := hl.congr hfr.length_eq
    have hw := writes_downLevel M dec mm qr R0 eps0 beta A
      (τ := τ) (L := L) (fuel := fuel) (d := i) (base := base)
      hS hL hC hMM hQR hQ hSample hexact hLive hp.1 hp.2.2.2.1 hp.2.1 hp.2.2.1
      (hp.2.2.2.2 (i + 1) le_rfl (by omega)) (hGeom i (by omega) ν hfr)
    refine (hw.in_frame rfl rfl hLive).mono (fun z j hj => ⟨i, by omega, hj⟩) ?_
    intro ξ hstep hNew
    refine ⟨hNew.1, ?_, ?_, hNew.2.2, ?_⟩
    · exact hstep.keep (Store.readsOnly_readBlock par.1 par.2 3 _)
        (hPar.symm.mono (downLevelOutputFp_le_arenas (by omega)) le_rfl) hp.2.1
    · exact hstep.keep (Store.readsOnly_readBlock c.1 c.2 5 _)
        (disj_downLevelOutputFp_constants (by omega) hAP) hp.2.2.1
    · intro e he hbound lo hlo
      exact hstep.keep (Store.readsOnly_get sz.1 (sz.2 + n * e + lo) _)
        ((disj_downLevelOutputFp_futureSizes (by omega) hbound (by omega) hAP).mono le_rfl
          (Fp.inBlock_le_inBlock (by omega) (by omega)))
        (hp.2.2.2.2 e (by omega) hbound lo hlo)
  · intro i hi x y hfr hp hxy
    have hx := evalCounted_frame_body (d := [n, L, fuel, i])
      (as := [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c]) rfl rfl hxy
    exact downLevel_kernelWeight_le_of_exec M dec mm qr R0 eps0 beta A
      hS hL hC hMM hQR hQ hSample hexact (hl.congr hfr.length_eq)
      hp.2.2.2.1 hp.2.1 hp.2.2.1 (hGeom i (by omega) x.mem hfr) T hT hadd W rfl hx

end

end NLAlib.SpectralBisection
