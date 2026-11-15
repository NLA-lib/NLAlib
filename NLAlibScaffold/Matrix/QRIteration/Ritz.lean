/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.ShiftedQR
public import NLAlib.Matrix.Spectral.EigenvalueListing

/-!
# Approximate Ritz values

The Ritz values of order $k$ of a Hessenberg matrix are the eigenvalues of its trailing
$k \times k$ block (`NLAlib.ritzValues`). An eigenvalue routine with forward error $\beta$ returns
them in its own order. The strategy lemmas take approximate Ritz values as a list matched entry by
entry with `NLAlib.ritzValues`; this file reorders a computed listing into that form.

## Main results

* `NLAlib.exists_perm_forall₂_ritzValues`: a forward-accurate listing of the eigenvalues of the
  trailing block, reordered, is entrywise within $\beta$ of the Ritz values.
-/

@[expose] public section

namespace NLAlib

variable {n : ℕ}

/-- **Forward-approximate Ritz values in the order of `NLAlib.ritzValues`**: if `ev` is within
$\beta$ of a listing `lam` of the eigenvalues (with multiplicity) of the trailing $k \times k$ block
of $\mathbf{H}$, some reordering of `ev` is entrywise within $\beta$ of the Ritz values of order
$k$. -/
theorem exists_perm_forall₂_ritzValues {k : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ev lam : Fin k → ℂ} {β : ℝ} (hlam : IsEigenvalueListing (trailingBlock k H) lam)
    (hev : ∀ i, ‖ev i - lam i‖ ≤ β) :
    ∃ ss : List ℂ, ss.Perm (List.ofFn ev) ∧
      List.Forall₂ (fun r ρ => ‖r - ρ‖ ≤ β) ss (ritzValues k H) := by
  have hroots : (trailingBlock k H).charpoly.roots = (List.ofFn lam : Multiset ℂ) := by
    rw [isEigenvalueListing_iff.mp hlam]
    simpa only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
      List.prod_ofFn, Function.comp_def] using
      Polynomial.roots_multiset_prod_X_sub_C (List.ofFn lam : Multiset ℂ)
  have hperm : (ritzValues k H).Perm (List.ofFn lam) := by
    rw [← Multiset.coe_eq_coe, ritzValues, Multiset.coe_toList, hroots]
  have hpair : List.Forall₂ (flip fun r ρ : ℂ => ‖r - ρ‖ ≤ β) (List.ofFn lam) (List.ofFn ev) :=
    List.forall₂_iff_get.mpr
      ⟨by simp, fun i h1 _ => by simpa [flip] using hev ⟨i, by simpa using h1⟩⟩
  obtain ⟨ss, hss, hssp⟩ := List.perm_comp_forall₂ hperm hpair
  exact ⟨ss, hssp, hss.flip⟩

end NLAlib
