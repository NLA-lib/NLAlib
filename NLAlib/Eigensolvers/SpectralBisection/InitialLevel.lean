/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Initialization
public import NLAlib.Eigensolvers.SpectralBisection.Storage

/-!
# The mathematical level represented by arena initialization

The initialization tuple gives the root matrix and parameters, its literal size and zero in
every other size slot. These ordinary reads represent level zero of the existing pure tree,
including an empty root matrix.

## Main results

* `NLAlib.SpectralBisection.storesLevel_zero_of_initialize_read`: initialization represents
  the mathematical root level.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- All strictly deeper size slots start at literal zero, including the reserved bottom level. -/
theorem futureSize_zero_of_initialize_read {K : Type} (M : Machine K) {n L : ℕ}
    {sz : ℕ × ℕ} {μ : Mem K}
    (hSizes : μ.store.readBlock sz.1 sz.2 (n * (L + 2) + 1) =
      some ((List.range (n * (L + 2) + 1)).map
        (fun i => if i = 0 then M.lit (n : ℚ) else M.lit 0)))
    (e : ℕ) (he : 1 ≤ e) (hdepth : e ≤ L + 1) (lo : ℕ) (hlo : lo < n) :
    μ.store.get sz.1 (sz.2 + n * e + lo) = some (M.lit 0) := by
  have hn : 0 < n := by omega
  have he' := Nat.mul_le_mul_left n hdepth
  have he0 := Nat.mul_le_mul_left n he
  have hj : n * e + lo < n * (L + 2) + 1 := by nlinarith
  simpa [hj, hn.ne', show e ≠ 0 by omega, Nat.add_assoc] using
    (Store.readBlock_eq_some_iff.mp hSizes).2 (n * e + lo) hj

/-- Interpret the initializer's ordinary tuple of actual reads as the root level. -/
theorem storesLevel_zero_of_initialize_read {K : Type} (M : Machine K)
    (F : FloatMachine K ℕ ℕ) (fuel : ℕ) {n L : ℕ} (R0 eps beta : K)
    (A : Matrix (Fin n) (Fin n) (K × K)) {c sz ma lv : ℕ × ℕ} {μ : Mem K}
    (hread : μ.readBlocks [c, sz, ma, lv] [5, n * (L + 2) + 1, 2 * (n * n), 2] =
      some [[M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf],
        (List.range (n * (L + 2) + 1)).map
          (fun i => if i = 0 then M.lit (n : ℚ) else M.lit 0),
        (EntryCodec.pair K).packFinMatrix A, [R0, eps]]) :
    StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, L⟩ 0 ma sz lv μ := by
  have hSizes := Mem.readBlocks_getD hread (i := 1) (by simp)
  have hA := Mem.readBlocks_getD hread (i := 2) (by simp)
  have hParams := Mem.readBlocks_getD hread (i := 3) (by simp)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hSizes hA hParams
  have hSize (j : ℕ) (hj : j < n * (L + 2) + 1) :
      μ.store.get sz.1 (sz.2 + j) =
        some (if j = 0 then M.lit (n : ℚ) else M.lit 0) := by
    simpa [hj] using (Store.readBlock_eq_some_iff.mp hSizes).2 j hj
  refine storesLevel_zero M F A hA (by simpa using hSize 0 (by omega)) ?_ hParams
  intro lo hlo hne
  have hn : n ≤ n * (L + 2) := Nat.le_mul_of_pos_right _ (by omega)
  simpa [hne] using hSize lo (by omega)

end NLAlib.SpectralBisection
