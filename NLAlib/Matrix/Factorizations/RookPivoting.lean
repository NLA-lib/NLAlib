/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Column norms for rook pivoting

A strict increase from a column maximum to a selected row entry forces growth of the next
column maximum. This finite collection of column scores supplies the termination argument for
stored rook selection, independently of its scalar interpretation or execution model.

## Main definitions

* `NLAlib.rookColumnMagnitude`: largest active-column scalar norm.

## Main results

* `NLAlib.norm_le_rookColumnMagnitude`: every active entry is bounded by its column score.
* `NLAlib.rookColumnMagnitude_eq`: an active maximum realizes the column score.
* `NLAlib.rookColumnMagnitude_lt_of_lt`: strict row improvement grows the next column score.
-/

@[expose] public section

namespace NLAlib

/-- The largest active-column norm, used only in the mathematical termination argument.
The runtime obtains its magnitude by the stored stable argmax scan. -/
def rookColumnMagnitude {𝕜 : Type*} [Norm 𝕜] {N : ℕ} (M : Matrix (Fin N) (Fin N) 𝕜) (k : Fin N)
    (c : Fin N) : ℝ :=
  (Finset.univ.filter fun i : Fin N => k ≤ i).sup'
    ⟨k, by simp⟩ (fun i => ‖M i c‖)

/-- Every active entry lies below its column's largest magnitude. -/
theorem norm_le_rookColumnMagnitude {𝕜 : Type*} [Norm 𝕜] {N : ℕ} (M : Matrix (Fin N) (Fin N) 𝕜)
    (k c i : Fin N) (hi : k ≤ i) : ‖M i c‖ ≤ rookColumnMagnitude M k c :=
  Finset.le_sup' (fun i => ‖M i c‖) (by simpa using hi)

/-- An actual active column maximum realizes the mathematical column magnitude. -/
theorem rookColumnMagnitude_eq {𝕜 : Type*} [Norm 𝕜] {N : ℕ} (M : Matrix (Fin N) (Fin N) 𝕜)
    (k c r : Fin N) (hr : k ≤ r) (hm : ∀ i : Fin N, k ≤ i → ‖M i c‖ ≤ ‖M r c‖) :
    rookColumnMagnitude M k c = ‖M r c‖ := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i hi => hm i (by simpa using hi))
  · exact norm_le_rookColumnMagnitude M k c r hr

/-- Strict growth of the selected row magnitude forces strict growth of the next column's
maximum. This rules out tie cycles without requiring the row scan to return the same column. -/
theorem rookColumnMagnitude_lt_of_lt {𝕜 : Type*} [Norm 𝕜] {N : ℕ} (M : Matrix (Fin N) (Fin N) 𝕜)
    (k c r d : Fin N) (hr : k ≤ r)
    (hm : ∀ i : Fin N, k ≤ i → ‖M i c‖ ≤ ‖M r c‖)
    (hlt : ‖M r c‖ < ‖M r d‖) : rookColumnMagnitude M k c < rookColumnMagnitude M k d := by
  rw [rookColumnMagnitude_eq M k c r hr hm]
  exact hlt.trans_le (norm_le_rookColumnMagnitude M k d r hr)

end NLAlib
