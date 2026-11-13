/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpwardArena
public import NLAlib.Ops.Logic.WeightedLoop

/-!
# Weighted accounting through reverse-depth reconstruction

The mathematical invariant is the same stored `eighAux` result family as in the ordinary
upward proof. Existing read/frame geometry preserves shallower inputs. Per-level resource
proofs then accumulate on the existing counted evaluator with arbitrary prior history.

## Main results

* `NLAlib.SpectralBisection.upwardPass_weight_le_of_levels`: sum actual per-level charges.
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

/-- Actual reverse-depth reconstruction accumulates one supplied per-level charge. The
ordinary word invariant and geometry justify each step; this auxiliary composition theorem
keeps execution analysis separate from the final total algorithm certificate. -/
theorem upwardPass_weight_le_of_levels (unif : K → Su → K) (normal : Sg → K × K)
    {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} (hS : IsScalar M I) (hQ : IsToNat dec I)
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
          (resultLengths ((ST d lo).childSize side))))
    (weight : Count Op Tst →+ ℕ) (levelCost : ℕ)
    (hLevelWeight : ∀ r < L + 1, ∀ a b : St Op Tst K,
      m.store.EqOff (PRE r) a.mem.store →
      (a.mem.pos = m.pos ∧ StoresLevelResults F n fuel R0 beta
        ⟨n, A, R0, eps, ell⟩ r (L + 1 - r) ua ea a.mem.store) →
      evalCounted I W τ (upLevel (Op := Op) (Tst := Tst))
        (Env.frame [n, L - r] [lv, ua, qa, ea, sz, kd, kp, c]) a = some b →
      weight b.cost ≤ weight a.cost + levelCost)
    {a b : St Op Tst K} (ha : a.mem = m)
    (hrun : evalCounted I W τ (upwardPass (Op := Op) (Tst := Tst)).body
      (Env.frame [n, L] [lv, ua, qa, ea, sz, kd, kp, c]) a = some b) :
    weight b.cost ≤ weight a.cost + (L + 1) * levelCost := by
  let ρ := Env.frame [n, L] [lv, ua, qa, ea, sz, kd, kp, c]
  let P := fun r (m' : Mem K) => m'.pos = m.pos ∧ StoresLevelResults F n fuel R0 beta
    ⟨n, A, R0, eps, ell⟩ r (L + 1 - r) ua ea m'.store
  have h0 : P 0 a.mem := by
    rw [ha]
    exact ⟨rfl, by simpa only [Nat.sub_zero] using hBottom⟩
  have hdims (r : ℕ) : IExp.evalList (ρ.pushIdx r).idx [.var 0, .var 1 - .var 10] =
      some [n, L - r] := rfl
  have hargs (r : ℕ) : Operand.evalList (ρ.pushIdx r)
      [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩,
        ⟨4, .var 6⟩, ⟨5, .var 7⟩, ⟨6, .var 8⟩, ⟨7, .var 9⟩] =
      some [lv, ua, qa, ea, sz, kd, kp, c] := rfl
  change evalCounted I W τ (.loop (.var 1 + .const 1) _) ρ a = some b at hrun
  have hb := evalCounted_loop_weight_of_writes (ρ := ρ) (a := a) (b := b)
    (by rfl) PRE (fun r _ b i ⟨j, hj, hc⟩ => ⟨j, by omega, hc⟩)
    P h0 (fun r hr m' hfr hp => ?_) weight (fun _ => levelCost)
    (fun r hr x y hfr hp hxy => ?_) hrun
  · simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul] using hb.1
  · rw [ha] at hfr
    rcases hp with ⟨hp, hResults⟩
    have hd : L + 1 - r = (L - r) + 1 := by omega
    have hd' : L + 1 - (r + 1) = L - r := by omega
    rw [hd] at hResults
    have hL := hfr.keep (hLevelRead (L - r) (by omega)) (hShallow r hr)
      (hLevel (L - r) (by omega))
    have hRec := hfr.keep (hRecordsRead (L - r) (by omega)) (hShallow r hr)
      (hRecords (L - r) (by omega))
    have hRec' : StoresRecords M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩
        (L - r) ma ua qa ea sz kd kp m' := by
      intro path lo x hx hy hz
      exact StoresStep.of_store_eq (μ := ⟨m'.store, m.pos⟩) (ν := m') rfl
        (hRec path lo x hx hy hz)
    have hC := hfr.keep ((Store.readsOnly_get _ _ _).mono (hConstant (L - r) (by omega)))
      (hShallow r hr) hTwo
    have hl' := hl.congr hfr.length_eq
    have hLive : m'.Live [lv, ua, qa, ea, sz, kd, kp, c] := by
      intro z hz
      exact hl' z (List.mem_append_left [ma] hz)
    have hw := writes_upLevel_eighAux (M := M) (dec := dec) (mm := mm) (qr := qr)
      (n := n) (base := base) (fuel := fuel) (R0 := R0) (eps := eps) (beta := beta)
      (ell := ell) (A := A) (d := L - r) (budget := r) (τ := τ) (m := m')
      unif normal hS hQ hMM hL hRec' hResults hl' hC hLit
      (hRoom r hr m' hfr) (hApart r hr m' hfr)
      (hDisj _ (by omega)) (hSizesProtect _ (by omega))
      (hForward _ (by omega)) (hChildProtect _ (by omega))
    refine (writes_frame (hdims r) (hargs r) hLive hw).mono
      (fun b i hc => ⟨r, by omega, hc⟩) ?_
    intro m'' _ ⟨hp', hs⟩
    exact ⟨hp'.trans hp, by simpa only [P, hd'] using hs⟩
  · rw [ha] at hfr
    apply hLevelWeight r hr x y hfr hp
    simp only [evalCounted, hdims r, hargs r, Option.bind_some] at hxy
    split_ifs at hxy
    exact hxy

end Reference

end NLAlib.SpectralBisection
