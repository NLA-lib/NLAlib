/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpLevelReference
public import NLAlib.Eigensolvers.SpectralBisection.LevelRead

/-!
# The complete executable upward reconstruction

Reverse-depth iteration increases the ordinary mathematical recursion budget one step at a
time. Exact completed-level frames retain the still-needed metadata. The final represented
root result is the existing recursive matrix algorithm on the indexed sample tree.

## Main results

* `NLAlib.SpectralBisection.writes_upwardPass`: total root reconstruction by the actual loop.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section Reference

variable {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  [Has IdxTst Tst] (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K))
  (qr : QRMap (K × K)) (n base fuel L : ℕ) (R0 eps beta : K) (ell : ℕ)
  (A : Matrix (Fin n) (Fin n) (K × K)) (τ : Tape K)
  (ma lv ua qa ea sz kd kp c : ℕ × ℕ)

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "X" => (fun d => nodeAtSlot F n fuel R0 beta (EighNode.mk n A R0 eps ell) d)
local notation "KS" => (fun d lo => EighNode.k (X d lo))
local notation "ST" => (fun d lo => eighStep F n fuel R0 beta (EighNode.A (X d lo))
  (EighNode.R (X d lo)) (EighNode.ε (X d lo)) (EighNode.ℓ (X d lo)) (eighTapeSample n d lo))
local notation "REG" => (fun d => resultLevelFootprint n d (KS d) ua ea)
local notation "PRE" => (fun r => Fp.loopPrefix (fun j => REG (L - j)) r)

/-- The actual upward loop reconstructs the recursive root output. Read stability is stated
under the exact completed-level prefix; capacity and spatial arena conditions are explicit.
Every iteration uses the actual total upward-level theorem, with no successful-run premise. -/
theorem writes_upwardPass (unif : K → Su → K) (normal : Sg → K × K)
    {I : Interp Op Tst K} (hS : IsScalar M I) (hQ : IsToNat dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {m : Mem K}
    (hl : m.Live [lv, ua, qa, ea, sz, kd, kp, c, ma])
    (hBottom : StoresLevelResults F n fuel R0 beta ⟨n, A, R0, eps, ell⟩
      0 (L + 1) ua ea m.store)
    (hLit : IsExactNatLit dec M (max n 4))
    (G : ℕ → Fp)
    (hLevel : ∀ d ≤ L,
      StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d ma sz lv m)
    (hRecords : ∀ d ≤ L,
      StoresRecords M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩
        d ma ua qa ea sz kd kp m)
    (hTwo : m.store.get c.1 (c.2 + 1) = some (M.lit 2))
    (hLevelRead : ∀ d ≤ L, Store.ReadsOnly (G d) (fun s =>
      StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d ma sz lv ⟨s, m.pos⟩))
    (hRecordsRead : ∀ d ≤ L, Store.ReadsOnly (G d) (fun s =>
      StoresRecords M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩
        d ma ua qa ea sz kd kp ⟨s, m.pos⟩))
    (hConstant : ∀ d ≤ L, Store.inBlock c.1 (c.2 + 1) 1 ≤ G d)
    (hShallow : ∀ r < L + 1, Fp.Disj (PRE r) (G (L - r)))
    (hRoom : ∀ r < L + 1, ∀ m' : Mem K, m.store.EqOff (PRE r) m'.store → ∀ lo < n,
      m'.Room (resultOperands n (L - r) lo ua ea) (resultLengths (KS (L - r) lo)))
    (hApart : ∀ r < L + 1, ∀ m' : Mem K, m.store.EqOff (PRE r) m'.store → ∀ lo < n,
      Fp.Apart (upNodeRegions n (L - r) lo ua qa ea kd kp (m'.store.length, 0))
        (upNodeRegionLengths n (KS (L - r) lo)))
    (hDisj : ∀ d ≤ L, ∀ lo < n, ∀ j < n, lo ≠ j →
      Fp.Disj (Fp.blocks (resultOperands n d lo ua ea) (resultLengths (KS d lo)))
        (Fp.blocks (resultOperands n d j ua ea) (resultLengths (KS d j))))
    (hSizesProtect : ∀ d ≤ L, Fp.Disj (REG d) (Store.inBlock sz.1 (sz.2 + n * d) n))
    (hForward : ∀ d ≤ L, ∀ j lo, j < lo → lo < n → 0 < KS d lo →
      Fp.Disj (Fp.blocks (resultOperands n d j ua ea) (resultLengths (KS d j)))
        (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp (ST d lo))
          (stepOutputLengths (ST d lo))))
    (hChildProtect : ∀ d ≤ L, ∀ lo < n, ∀ side, (ST d lo).HasChild side →
      Fp.Disj (REG d)
        (Fp.blocks (resultOperands n (d + 1) ((ST d lo).childSlot lo side) ua ea)
          (resultLengths ((ST d lo).childSize side)))) :
    Writes .total I τ (upwardPass (Op := Op) (Tst := Tst)).body
      (Env.frame [n, L] [lv, ua, qa, ea, sz, kd, kp, c]) (PRE (L + 1))
      (fun m' => m'.pos = m.pos ∧ StoresResult n 0 0 ua ea
        (eighAux F n fuel R0 beta (L + 1) A R0 eps ell
          (eighSlotTree F n fuel R0 beta 0 0 ⟨n, A, R0, eps, ell⟩)) m'.store) m := by
  change Writes .total I τ (.loop (.var 1 + .const 1) _)
    (Env.frame [n, L] [lv, ua, qa, ea, sz, kd, kp, c]) (PRE (L + 1)) _ m
  refine (writes_loop rfl PRE (fun r _ b i ⟨j, hj, hc⟩ => ⟨j, by omega, hc⟩)
    (fun r m' => m'.pos = m.pos ∧ StoresLevelResults F n fuel R0 beta
      ⟨n, A, R0, eps, ell⟩ r (L + 1 - r) ua ea m'.store)
    ⟨rfl, by simpa using hBottom⟩ ?_).mono le_rfl ?_
  · intro r hr m' hfr ⟨hp, hResults⟩
    have hd : L + 1 - r = (L - r) + 1 := by omega
    have hd' : L + 1 - (r + 1) = L - r := by omega
    rw [hd] at hResults
    have hL := hfr.keep (hLevelRead (L - r) (by omega)) (hShallow r hr)
      (hLevel (L - r) (by omega))
    have hRec := hfr.keep (hRecordsRead (L - r) (by omega)) (hShallow r hr)
      (hRecords (L - r) (by omega))
    have hRec' : StoresRecords M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩
        (L - r) ma ua qa ea sz kd kp m' := by
      intro a lo x ha hx hxpos
      exact StoresStep.of_store_eq (μ := ⟨m'.store, m.pos⟩) (ν := m') rfl
        (hRec a lo x ha hx hxpos)
    have hC := hfr.keep ((Store.readsOnly_get _ _ _).mono (hConstant (L - r) (by omega)))
      (hShallow r hr) hTwo
    have hl' := hl.congr hfr.length_eq
    have hframeLive : m'.Live [lv, ua, qa, ea, sz, kd, kp, c] := by
      intro z hz
      exact hl' z (List.mem_append_left [ma] hz)
    have hw := writes_upLevel_eighAux (M := M) (dec := dec) (mm := mm) (qr := qr)
      (n := n) (base := base) (fuel := fuel) (R0 := R0) (eps := eps) (beta := beta)
      (ell := ell) (A := A) (d := L - r) (budget := r) (τ := τ) (m := m')
      unif normal hS hQ hMM
      hL hRec' hResults hl' hC hLit
      (hRoom r hr m' hfr) (hApart r hr m' hfr)
      (hDisj _ (by omega)) (hSizesProtect _ (by omega))
      (hForward _ (by omega)) (hChildProtect _ (by omega))
    let ρ := (Env.frame [n, L] [lv, ua, qa, ea, sz, kd, kp, c]).pushIdx r
    let ds : List IExp := [.var 0, .var 1 - .var 10]
    let args : List Operand := [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩,
      ⟨4, .var 6⟩, ⟨5, .var 7⟩, ⟨6, .var 8⟩, ⟨7, .var 9⟩]
    have hdims : IExp.evalList ρ.idx ds = some [n, L - r] := rfl
    have hargs : Operand.evalList ρ args = some [lv, ua, qa, ea, sz, kd, kp, c] := rfl
    refine (writes_frame (ρ := ρ) hdims hargs hframeLive hw).mono ?_ ?_
    · exact fun b i hc => (show PRE (r + 1) b i from ⟨r, by omega, hc⟩)
    · intro m'' _ ⟨hp', hs⟩
      exact ⟨hp'.trans hp, by simpa only [hd'] using hs⟩
  · intro m' _ ⟨hp, hs⟩
    exact ⟨hp, (by simpa using hs : StoresLevelResults F n fuel R0 beta
      ⟨n, A, R0, eps, ell⟩ (L + 1) 0 ua ea m'.store).root⟩

end Reference

end NLAlib.SpectralBisection
