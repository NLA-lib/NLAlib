/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Round
public import NLAlib.Ops.Logic.While

/-!
# Total capped Newton–Schulz execution

One mathematical matrix represents each reachable iterate. The actual flag query chooses the
same stopped transition as the existing mathematical recurrence. Shared capped-loop reasoning
handles early stopping and the cap; the proof never assumes successful execution or a passing
test at the cap.

## Main results

* `NLAlib.Sign.writes_loop`: the loop returns the actual capped mathematical iterate and cache.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K Op Tst Su Sg : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  [Has CmpTst Tst] {M : Ops.Machine K} {dec : K → ℝ}
  {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- From an actual initialized matrix/cache/flag representation, the capped loop terminates
with the existing mathematical capped Newton–Schulz result. It requires only functional
scalar/multiplication contracts, exact comparison queries, distinct zero/one decodings and
workspace capacities. No numerical convergence or successful-execution premise is assumed. -/
theorem writes_loop {I : Interp Op Tst K} (hS : IsScalar M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {τ : Tape K} {n cap : ℕ}
    (A : Matrix (Fin n) (Fin n) (K × K)) (η : K) {x w v t : ℕ × ℕ} {m : Mem K}
    (hState : LoopState (M.toFloatMachine dec mm qr unif normal) x w t η A m.store)
    (h01 : dec (M.lit 0) ≠ dec (M.lit 1)) (hl : m.Live [x, w, v, t])
    (hAP : Fp.Apart [x, w, v, t] [2 * (n * n), 2 * (n * n), 2 * (n * n), 5])
    (hx : x.2 + 2 * (n * n) ≤ m.store.len x.1)
    (hw : w.2 + 2 * (n * n) ≤ m.store.len w.1)
    (hv : v.2 + 2 * (n * n) ≤ m.store.len v.1) (ht : t.2 + 5 ≤ m.store.len t.1) :
    Writes .total I τ (loop (Has.inj MatrixOp.mul)).body
      (Env.frame [n, cap] [x, w, v, t, x, w, v, t]) (loopFootprint n x w v t)
      (fun μ => LoopState (M.toFloatMachine dec mm qr unif normal) x w t η
        (newtonSchulzLoop (M.toFloatMachine dec mm qr unif normal) η cap A) μ.store ∧
        μ.pos = m.pos) m := by
  let N := M.toFloatMachine dec mm qr unif normal
  let representation := fun (B : Matrix (Fin n) (Fin n) (K × K)) (μ : Mem K) =>
    LoopState N x w t η B μ.store ∧ μ.pos = m.pos
  let active := fun (B : Matrix (Fin n) (Fin n) (K × K)) => !(newtonSchulzTest N η B)
  let next := newtonSchulzRounded (n := n) N
  have hf : (fun B => if active B then next B else B) = eighSignIter N η := by
    funext B
    cases htest : newtonSchulzTest N η B <;> simp [active, next, eighSignIter, htest]
  refine (Ops.writes_whileFuel_iterate (I := I) (τ := τ)
    (ρ := Env.frame [n, cap] [x, w, v, t, x, w, v, t]) (F := loopFootprint n x w v t)
    representation active next (s := A) (N := cap) rfl ⟨hState, rfl⟩ ?_ ?_).mono le_rfl ?_
  · intro i hi μ hfr hStored
    change I.test (Has.inj CmpTst.eq) [] [(t.1, t.2 + 1), (t.1, t.2 + 3)] μ = some _
    exact hStored.1.test_eq hC h01 μ.pos
  · intro i hi μ hfr hStored _
    have hl' : μ.Live [x, w, v, t] := by simpa [Mem.Live, hfr.length_eq] using hl
    have hx' : x.2 + 2 * (n * n) ≤ μ.store.len x.1 := by rw [hfr.len_eq]; exact hx
    have hw' : w.2 + 2 * (n * n) ≤ μ.store.len w.1 := by rw [hfr.len_eq]; exact hw
    have hv' : v.2 + 2 * (n * n) ≤ μ.store.len v.1 := by rw [hfr.len_eq]; exact hv
    have ht' : t.2 + 5 ≤ μ.store.len t.1 := by rw [hfr.len_eq]; exact ht
    have hr := writes_round (dec := dec) (mm := mm) (qr := qr)
      (unif := unif) (normal := normal) (τ := τ) hS hC hMM _ η hStored.1 hl' hAP hx' hw' hv' ht'
    have hlFrame : μ.Live [x, w, v, t, x, w, v, t] :=
      (Mem.live_append μ _ _).mpr ⟨hl', hl'⟩
    exact (writes_frame rfl rfl hlFrame hr).mono le_rfl fun _ _ h => ⟨h.1, h.2.trans hStored.2⟩
  · intro μ _ h
    simpa only [representation, hf, ← newtonSchulzLoop_eq_iterate] using h

end NLAlib.Sign
