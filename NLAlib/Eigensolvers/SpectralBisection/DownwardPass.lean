/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownLevelSolve
public import NLAlib.Eigensolvers.SpectralBisection.LevelInput

/-!
# The complete downward traversal

The counted level loop retains every completed mathematical level and node outcome. Future
size slots retain their initialized zeros until their parent level writes them. Each level
consumes the same two fixed sampling batches and advances the shared tape by their exact size.

## Main results

* `NLAlib.SpectralBisection.writes_downwardPass`: all downward records and input levels.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has SampleOp Op] [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
  (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  {I : Interp Op Tst K} {τ : Tape K} {μ : Mem K} {n L fuel base : ℕ}
  {par lv su sg ma ua qa ea sz kd kp c : ℕ × ℕ}
  (R0 eps0 beta : K) (A : Matrix (Fin n) (Fin n) (K × K))

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "root" => EighNode.mk n A R0 eps0 L
local notation "nodes" => (fun d lo => nodeAtSlot F n fuel R0 beta root d lo)
local notation "region" => (fun d => downLevelOutputFp n d lv su sg ma ua qa ea sz kd kp)

/-- The actual counted downward traversal produces all level inputs and all node records.
Its spatial premises protect earlier records, earlier input levels and future size zeros;
the fresh-scratch premise concerns only storage shape and capacities. -/
theorem writes_downwardPass (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
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
    (hGeometry : ∀ d ≤ L, ∀ ν : Mem K, ν.store.length = μ.store.length →
      (∀ b, ν.store.len b = μ.store.len b) → ∀ s : Store K,
      s.length = ν.store.length + 1 → s.len ν.store.length = 5 →
      Store.Below ν.store.length ν.store s →
        DownLevelGeometry n d (fun lo => (nodes d lo).k)
          par lv su sg ma ua qa ea sz kd kp c (ν.store.length, 0) s)
    (hRead : ∀ d ≤ L, Fp.Disj (region d)
      (Store.inBlock par.1 par.2 3 ⊔ Store.inBlock c.1 c.2 5))
    (hLevels : ∀ d ≤ L, ∀ e ≤ d, Fp.Disj (region d) (levelInputFp n e ma sz lv))
    (hFuture : ∀ d ≤ L, ∀ e, d + 2 ≤ e → e ≤ L + 1 →
      Fp.Disj (region d) (Store.inBlock sz.1 (sz.2 + n * e) n))
    (hRecords : ∀ d ≤ L, ∀ e < d, ∀ (a : List Bool) lo (x : EighNode K), a.length = e →
      eighLoc F n fuel R0 beta 0 0 root a = some (lo, x) → 0 < x.k →
      Fp.Disj (region d) (Fp.blocks
        (stepOutputs n e lo ma ua qa ea sz kd kp
          (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n e lo)))
        (stepOutputLengths
          (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n e lo))))) :
    Writes .total I τ (downwardPass (node (Op := Op) (Tst := Tst))).body
      (Env.frame [n, L, fuel] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c])
      (Fp.loopPrefix region (L + 1))
      (fun ν => ν.pos = base + (L + 1) * levelSampleSize n ∧
        ν.store.readBlock par.1 par.2 3 = some [R0, eps0, beta] ∧
        ν.store.readBlock c.1 c.2 5 =
          some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf] ∧
        (∀ e ≤ L + 1, StoresLevel M F n fuel R0 beta root e ma sz lv ν) ∧
        ∀ e ≤ L, StoresRecords M F n fuel R0 beta root e ma ua qa ea sz kd kp ν) μ := by
  let Inv := fun i (ν : Mem K) => ν.pos = base + i * levelSampleSize n ∧
    ν.store.readBlock par.1 par.2 3 = some [R0, eps0, beta] ∧
    ν.store.readBlock c.1 c.2 5 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf] ∧
    (∀ e ≤ i, StoresLevel M F n fuel R0 beta root e ma sz lv ν) ∧
    (∀ e < i, StoresRecords M F n fuel R0 beta root e ma ua qa ea sz kd kp ν) ∧
    ∀ e, i + 1 ≤ e → e ≤ L + 1 → ∀ lo < n,
      ν.store.get sz.1 (sz.2 + n * e + lo) = some (M.lit 0)
  have hInitial : Inv 0 μ := by
    refine ⟨by simpa using hPos, hpar, hc, ?_, ?_, hZero⟩
    · intro e he
      have : e = 0 := by omega
      subst e
      exact hLevel
    · intro e he; omega
  refine (writes_loop rfl (Fp.loopPrefix region) (fun i _ _ _ h => ?_)
    Inv hInitial ?_).mono le_rfl ?_
  · rcases h with ⟨j, hj, hx⟩; exact ⟨j, by omega, hx⟩
  · intro i hi ν hfr hInv
    rcases hInv with ⟨hp, hpar', hc', hLv, hRec, hZeros⟩
    have hLive : ν.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c] := by
      simpa only [Mem.Live, hfr.length_eq] using hl
    have hW := writes_downLevel M dec mm qr R0 eps0 beta A
      (τ := τ) (L := L) (fuel := fuel) (d := i) (base := base) hS hL hC hMM hQR hQ hSample
      hexact hLive hp (hLv i le_rfl) hpar' hc' (hZeros (i + 1) le_rfl (by omega))
      (hGeometry i (by omega) ν hfr.length_eq hfr.len_eq)
    refine (hW.in_frame rfl rfl hLive).mono (fun b j hj => ⟨i, by omega, hj⟩) ?_
    intro ξ hstep hNew
    refine ⟨hNew.1, ?_, ?_, ?_, ?_, ?_⟩
    · exact hstep.keep (Store.readsOnly_readBlock par.1 par.2 3 _)
        ((hRead i (by omega)).mono le_rfl le_sup_left) hpar'
    · exact hstep.keep (Store.readsOnly_readBlock c.1 c.2 5 _)
        ((hRead i (by omega)).mono le_rfl le_sup_right) hc'
    · intro e he
      by_cases hei : e ≤ i
      · exact (hLv e hei).of_eqOff_input hstep (hLevels i (by omega) e hei)
      · have heq : e = i + 1 := by omega
        subst e
        exact hNew.2.2
    · intro e he
      by_cases hei : e < i
      · exact (hRec e hei).of_eqOff hstep (hRecords i (by omega) e hei)
      · have heq : e = i := by omega
        subst e
        exact hNew.2.1
    · intro e he hbound lo hlo
      exact hstep.keep (Store.readsOnly_get sz.1 (sz.2 + n * e + lo) _)
        ((hFuture i (by omega) e (by omega) hbound).mono le_rfl
          (Fp.inBlock_le_inBlock (by omega) (by omega)))
        (hZeros e (by omega) hbound lo hlo)
  · intro ν _ h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun e he => h.2.2.2.2.1 e (by omega)⟩

end

end NLAlib.SpectralBisection
