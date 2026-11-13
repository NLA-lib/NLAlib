/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Splitting a polynomial along a partition of its roots

Upstream candidate for Mathlib.

## Main results

* `Polynomial.exists_monic_mul_eq_of_filter_roots` factors a monic polynomial into two coprime
  factors with prescribed root multisets.
-/

@[expose] public section

namespace Polynomial
variable {K : Type*} [Field K] [IsAlgClosed K]

/-- A decidable partition of the roots of a monic polynomial gives coprime
monic factors with the specified root multisets, including multiplicity. -/
theorem exists_monic_mul_eq_of_filter_roots (p : K[X]) (hp : p.Monic)
    (P : K → Prop) [DecidablePred P] :
    ∃ f g : K[X], f.Monic ∧ g.Monic ∧ f * g = p ∧ IsCoprime f g ∧
      f.roots = p.roots.filter P ∧ g.roots = p.roots.filter (fun z => ¬ P z) := by
  classical
  let f : K[X] := ((p.roots.filter P).map fun z => X - C z).prod
  let g : K[X] := ((p.roots.filter (fun z => ¬ P z)).map fun z => X - C z).prod
  have hf : f.Monic := monic_multisetProd_X_sub_C _
  have hg : g.Monic := monic_multisetProd_X_sub_C _
  have hfr : f.roots = p.roots.filter P := roots_multiset_prod_X_sub_C _
  have hgr : g.roots = p.roots.filter (fun z => ¬ P z) := roots_multiset_prod_X_sub_C _
  refine ⟨f, g, hf, hg, ?_, ?_, hfr, hgr⟩
  · change ((p.roots.filter P).map fun z => X - C z).prod *
      ((p.roots.filter (fun z => ¬ P z)).map fun z => X - C z).prod = p
    rw [← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not]
    exact ((IsAlgClosed.splits p).eq_prod_roots_of_monic hp).symm
  · rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K]
    intro z
    simp only [coe_aeval_eq_eval]
    by_cases hfz : f.eval z = 0
    · right
      intro hgz
      have hfi := (mem_roots hf.ne_zero).mpr hfz
      have hgi := (mem_roots hg.ne_zero).mpr hgz
      rw [hfr, Multiset.mem_filter] at hfi
      rw [hgr, Multiset.mem_filter] at hgi
      exact hgi.2 hfi.2
    · exact Or.inl hfz

end Polynomial
