/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.LevelParameters
public import NLAlib.Eigensolvers.SpectralBisection.TapeMachine
public import NLAlib.Ops.Blas.Sampling
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Parameter update and stored sampling batches

A downward level first computes its next parameter pair, then stores the uniform and Gaussian
batches. The position advances by the sum of their exact lengths.

## Main results

* `NLAlib.SpectralBisection.writes_downPrepare`: the actual next parameters and sampled words.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The level preparation writes the actual rounded parameters and both actual tape windows.
It draws exactly `levelSampleSize n` words, including for empty matrices. -/
theorem writes_downPrepare {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
    [Has SampleOp Op] {M : Machine K} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hIndex : IsIndexLit M I) (hSample : IsSample I)
    {τ : Tape K} {n L d : ℕ} {c lv su sg t : ℕ × ℕ} {m : Mem K}
    (one two half R eps : K) (hl : m.Live [c, lv, su, sg, t])
    (hAP : Fp.Apart [c, (lv.1, lv.2 + 2 * d), (lv.1, lv.2 + 2 * (d + 1)), su, sg, t]
      [3, 2, 2, n, 4 * (n * n), 4])
    (hc : m.store.readBlock c.1 c.2 3 = some [one, two, half])
    (hLv : m.store.readBlock lv.1 (lv.2 + 2 * d) 2 = some [R, eps])
    (hv : lv.2 + 2 * (d + 1) + 2 ≤ m.store.len lv.1)
    (hu : su.2 + n ≤ m.store.len su.1)
    (hg : sg.2 + 4 * (n * n) ≤ m.store.len sg.1)
    (ht : t.2 + 4 ≤ m.store.len t.1) :
    Writes .total I τ downPrepareImpl.body (Env.frame [n, L, d] [c, lv, su, sg, t])
      ((Store.inBlock lv.1 (lv.2 + 2 * (d + 1)) 2 ⊔ Store.inBlock t.1 t.2 4) ⊔
        (Store.inBlock su.1 su.2 n ⊔ Store.inBlock sg.1 sg.2 (4 * (n * n))))
      (fun μ => μ.pos = m.pos + levelSampleSize n ∧
        μ.store.readBlock lv.1 (lv.2 + 2 * (d + 1)) 2 =
          some [M.mul (M.add half (M.div two (M.lit (L + d : ℕ)))) R,
            M.mul (M.sub one (M.div one (M.lit (L + d : ℕ)))) eps] ∧
        μ.store.readBlock su.1 su.2 n = some (τ.window Stream.unif m.pos n) ∧
        μ.store.readBlock sg.1 sg.2 (4 * (n * n)) =
          some (τ.window Stream.gauss (m.pos + n) (4 * (n * n)))) m := by
  have hd (i j : Fin 6) (hij : i ≠ j) :=
    hAP.disj_getD i.isLt j.isLt (fun he => hij (Fin.ext he))
  have hp : Fp.Apart [c, (lv.1, lv.2 + 2 * d), (lv.1, lv.2 + 2 * (d + 1)), t]
      [3, 2, 2, 4] := by
    have h := hAP.subviews (fun i : Fin 4 => (![0, 1, 2, 5] : Fin 4 → Fin 6) i)
      (fun _ => 0) ![3, 2, 2, 4] (by intro i; fin_cases i <;> simp)
      (by intro i j hij he; fin_cases i <;> fin_cases j <;> simp at he hij ⊢)
    simpa using h
  have hP := writes_levelParameters (τ := τ) (L := L) hS hIndex one two half R eps hp hc hLv hv ht
  have hLive : c.1 < m.store.length ∧ lv.1 < m.store.length ∧ su.1 < m.store.length ∧
      sg.1 < m.store.length ∧ t.1 < m.store.length := by simpa [Mem.Live] using hl
  rcases hLive with ⟨hlc, hlv, hlu, hlg, hlt⟩
  refine (hP.in_frame rfl rfl (by room)).seq fun μ hfr0 hpar => ?_
  have hU := writes_sampleVector (τ := τ) (m := μ) hSample Stream.unif
    (y := su) (n := n) (by rw [hfr0.len_eq]; exact hu)
  refine (hU.in_frame rfl rfl (by room)).seq fun ν hfr1 hunif => ?_
  have hV := hfr1.keep (Store.readsOnly_readBlock lv.1 (lv.2 + 2 * (d + 1)) 2 _)
    (by simpa using hd 3 2 (by simp)) hpar.2
  have hfr01 := hfr0.trans' hfr1
  have hG := writes_sampleVector (τ := τ) (m := ν) hSample Stream.gauss
    (y := sg) (n := 4 * (n * n)) (by rw [hfr01.len_eq]; exact hg)
  refine (hG.in_frame rfl rfl (by room)).mono le_rfl ?_
  intro ξ hfr2 hgauss
  have hV' := hfr2.keep (Store.readsOnly_readBlock lv.1 (lv.2 + 2 * (d + 1)) 2 _)
    (by simpa using hd 4 2 (by simp)) hV
  have hU' := hfr2.keep (Store.readsOnly_readBlock su.1 su.2 n _)
    (by simpa using hd 4 3 (by simp)) hunif.1
  refine ⟨by simp only [hgauss.2, hunif.2, hpar.1, levelSampleSize, Nat.add_assoc], hV', ?_, ?_⟩
  · simpa only [hpar.1] using hU'
  · simpa only [hunif.2, hpar.1] using hgauss.1

end NLAlib.SpectralBisection
