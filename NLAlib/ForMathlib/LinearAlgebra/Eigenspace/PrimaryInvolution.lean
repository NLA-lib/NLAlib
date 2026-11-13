/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Primary subspaces of a commuting involution

Upstream candidate for Mathlib.

## Main results

* `Module.End.eigenspace_eq_iSup_maxGenEigenspace_of_stable_involution` identifies the
  eigenspaces of an involution commuting with a complex endomorphism.
-/

@[expose] public section

open Module

namespace Module.End
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A common eigenspace/primary-space intersection vanishes when its
product eigenvalue is excluded by positive stability. -/
private theorem eigenspace_inf_maxGenEigenspace_eq_bot_of_stable_product
    (f s : End ℂ V) (hfs : Commute f s)
    (hpos : ∀ z, (s * f).HasEigenvalue z → 0 < z.re)
    (a μ : ℂ) (hμ : ¬0 < (a * μ).re) :
    s.eigenspace a ⊓ f.maxGenEigenspace μ = ⊥ := by
  let W := s.eigenspace a ⊓ f.maxGenEigenspace μ
  have hpres : ∀ v ∈ W, f v ∈ W := by
    intro v hv
    refine ⟨mem_eigenspace_iff.mpr ?_, f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ hv.2⟩
    have hc : f (s v) = s (f v) := congrArg (fun T : End ℂ V => T v) hfs.eq
    rw [← hc, mem_eigenspace_iff.mp hv.1, map_smul]
  by_contra hW
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨ν, hν⟩ := Module.End.exists_eigenvalue (f.restrict hpres)
  obtain ⟨v, hv, hv0⟩ := hν.exists_hasEigenvector
  have hv0' : (v : V) ≠ 0 := by exact fun h => hv0 (Subtype.ext h)
  have hfν : f (v : V) = ν • (v : V) :=
    congrArg Subtype.val (mem_eigenspace_iff.mp hv)
  have hνμ : ν = μ := by
    by_contra hne
    have hboth : (v : V) ∈ f.maxGenEigenspace ν ⊓ f.maxGenEigenspace μ :=
      ⟨eigenspace_le_maxGenEigenspace (mem_eigenspace_iff.mpr hfν), v.property.2⟩
    rw [(f.disjoint_genEigenspace hne ⊤ ⊤).eq_bot] at hboth
    exact hv0' hboth
  subst ν
  have hp : (s * f).HasEigenvalue (a * μ) := by
    apply hasEigenvalue_of_hasEigenvector (x := (v : V))
    refine ⟨mem_eigenspace_iff.mpr ?_, hv0'⟩
    change s (f (v : V)) = (a * μ) • (v : V)
    rw [hfν, map_smul, mem_eigenspace_iff.mp v.property.1, smul_smul, mul_comm μ a]
  exact hμ (hpos _ hp)

/-- A commuting sign involution selects exactly the generalized
eigenspaces for which the signed eigenvalue lies in the right half-plane.
The scalar `a` may be `1` or `-1`; the equation `a²=1` includes both. -/
theorem eigenspace_eq_iSup_maxGenEigenspace_of_stable_involution
    (f s : End ℂ V) (hfs : Commute f s) (hss : s ^ 2 = 1)
    (hpos : ∀ z, (s * f).HasEigenvalue z → 0 < z.re)
    (a : ℂ) (haa : a ^ 2 = 1) :
    s.eigenspace a = ⨆ z : {z : ℂ // 0 < (a * z).re}, f.maxGenEigenspace z.val := by
  have hpres : ∀ v ∈ s.eigenspace a, f v ∈ s.eigenspace a := by
    intro v hv
    apply mem_eigenspace_iff.mpr
    have hc : f (s v) = s (f v) := congrArg (fun T : End ℂ V => T v) hfs.eq
    rw [← hc, mem_eigenspace_iff.mp hv, map_smul]
  apply le_antisymm
  · rw [Submodule.eq_iSup_inf_genEigenspace (f := f) ⊤ hpres
      (iSup_maxGenEigenspace_eq_top f)]
    apply iSup_le
    intro μ
    by_cases hμ : 0 < (a * μ).re
    · exact inf_le_right.trans (le_iSup
        (fun z : {z : ℂ // 0 < (a * z).re} => f.maxGenEigenspace z.val) ⟨μ, hμ⟩)
    · rw [eigenspace_inf_maxGenEigenspace_eq_bot_of_stable_product f s hfs hpos a μ hμ]
      exact bot_le
  · apply iSup_le
    intro μ v hv
    have hssv : s (s v) = v := by
      have h := congrArg (fun T : End ℂ V => T v) hss
      simpa only [pow_two, mul_apply, one_apply] using h
    have haa' : a * a = 1 := by simpa only [pow_two] using haa
    let q : V := (2 : ℂ)⁻¹ • (v - a • s v)
    have hqW : q ∈ f.maxGenEigenspace μ.val :=
      (f.maxGenEigenspace μ.val).smul_mem _
        ((f.maxGenEigenspace μ.val).sub_mem hv
          ((f.maxGenEigenspace μ.val).smul_mem a (f.mapsTo_maxGenEigenspace_of_comm hfs μ.val hv)))
    have hqS : q ∈ s.eigenspace (-a) := by
      apply mem_eigenspace_iff.mpr
      dsimp [q]
      rw [map_smul, map_sub, map_smul, hssv]
      rw [smul_comm (-a) ((2 : ℂ)⁻¹)]
      congr 1
      simp only [smul_sub, smul_smul, neg_mul, haa', neg_one_smul]
      module
    have hq0 : q = 0 := by
      have hh : q ∈ s.eigenspace (-a) ⊓ f.maxGenEigenspace μ.val := ⟨hqS, hqW⟩
      have hn : ¬ 0 < ((-a) * μ.val).re := by
        simpa only [neg_mul, Complex.neg_re] using not_lt_of_ge (neg_nonpos.mpr μ.property.le)
      rw [eigenspace_inf_maxGenEigenspace_eq_bot_of_stable_product f s hfs hpos (-a) μ.val hn] at hh
      exact hh
    have hzero : v - a • s v = 0 := (smul_eq_zero.mp hq0).resolve_left (by norm_num)
    have hv' : v = a • s v := sub_eq_zero.mp hzero
    apply mem_eigenspace_iff.mpr
    calc
      s v = (a * a) • s v := by rw [haa', one_smul]
      _ = a • v := by rw [mul_smul, ← hv']

end Module.End
