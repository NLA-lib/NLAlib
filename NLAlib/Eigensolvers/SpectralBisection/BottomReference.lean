/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpReference
public import NLAlib.Eigensolvers.SpectralBisection.Bottom

/-!
# The actual recursion boundary represents zero remaining budget

Literal identity entries and zero eigenvalues are exactly the existing pure recursion's
budget-zero output on the actual scalar machine. This supplies the initial ordinary result
family for reverse-depth reconstruction.

## Main results

* `NLAlib.SpectralBisection.storesLevelResults_zero_of_bottom`: actual bottom outputs suffice.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- A node's actual bottom identity and zeros represent the reference recursion at budget zero. -/
theorem BottomOutput.stores_eighNodeResult_zero {K : Type} (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (n base fuel : ℕ) (τ : Tape K)
    (R0 beta : K) (d lo : ℕ) (x : EighNode K) (u e : ℕ × ℕ) {s : Store K}
    (h : BottomOutput M x.k
      (u.1, u.2 + 2 * (n * n) * d + 2 * n * lo) (e.1, e.2 + n * d + lo) s) :
    StoresResult n d lo u e
      (eighNodeResult (tapeMachine M dec mm qr n base τ) n fuel R0 beta 0 d lo x) s := by
  have he : (Matrix.of fun (i j : Fin x.k) =>
      (if i = j then M.lit 1 else M.lit 0, M.lit 0)) =
      (tapeMachine M dec mm qr n base τ).identityMat x.k := by
    ext i j <;> by_cases hij : i = j <;>
      simp [FloatMachine.identityMat, tapeMachine, Machine.toFloatMachine, hij]
  have hr := h.readBlocks 0
  rw [he] at hr
  simpa [StoresResult, resultOperands, resultLengths, eighNodeResult, eighAux,
    tapeMachine, Machine.toFloatMachine] using hr

/-- Actual bottom results for every size-query slot give the complete zero-budget result
family. Empty reached nodes, including an empty root, require no initialized payload cells. -/
theorem storesLevelResults_zero_of_bottom {K : Type} (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (n base fuel d : ℕ) (τ : Tape K)
    (R0 eps beta : K) (ell : ℕ) (A : Matrix (Fin n) (Fin n) (K × K))
    (u e : ℕ × ℕ) (s : Store K)
    (hSlots : ∀ lo < n,
      BottomOutput M
        (nodeAtSlot (tapeMachine M dec mm qr n base τ) n fuel R0 beta
          ⟨n, A, R0, eps, ell⟩ d lo).k
        (u.1, u.2 + 2 * (n * n) * d + 2 * n * lo) (e.1, e.2 + n * d + lo) s) :
    StoresLevelResults (tapeMachine M dec mm qr n base τ) n fuel R0 beta
      ⟨n, A, R0, eps, ell⟩ 0 d u e s := by
  intro path lo x hlen hx
  by_cases hp : 0 < x.k
  · have hlo : lo < n := by have := (add_k_le_and_of_eighLoc hx).1; omega
    have hs := hSlots lo hlo
    rw [nodeAtSlot_eq_of_eighLoc hlen hx hp] at hs
    exact hs.stores_eighNodeResult_zero M dec mm qr n base fuel τ R0 beta d lo x u e
  · exact storesResult_of_eq_zero (by omega) n d lo u e _ s

end NLAlib.SpectralBisection
