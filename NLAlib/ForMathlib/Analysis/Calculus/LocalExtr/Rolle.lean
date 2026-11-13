/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Data.Multiset.Sort

/-!
# Rolle's theorem for zeros counted with multiplicity

If $f$ has $q + 2$ zeros counted with multiplicity in $[a, b]$, a zero of multiplicity $r$ at $y$
meaning that $f, f', \dots, f^{(r-1)}$ vanish at $y$, then $f^{(q+1)}$ vanishes somewhere in
$(a, b)$. Repeated zeros must be interior; simple zeros may sit at the endpoints, where only
continuity is used. This is the step behind every Hermite interpolation remainder (Gauss nodes
doubled, Radau and Lobatto endpoints simple). Mathlib has the single-derivative case
`exists_deriv_eq_zero`. Upstream candidate for `Mathlib.Analysis.Calculus.LocalExtr.Rolle`.


## Main results

* `exists_iteratedDeriv_eq_zero_of_multiset`: iterated Rolle with multiplicities.
-/

@[expose] public section

open Set

/-- One Rolle step on a multiset of zeros: the zeros of `deriv f` obtained from the repeated
points of `m` and from Rolle between consecutive distinct points, with their multiplicities. -/
private lemma exists_multiset_deriv_zeros {f : ℝ → ℝ} {a b : ℝ} (n : ℕ) :
    ∀ m : Multiset ℝ, m.card = n + 1 → (∀ y ∈ m, y ∈ Icc a b) →
      (∀ y ∈ m, 1 < m.count y → y ∈ Ioo a b) →
      (∀ x ∈ m, ∀ y ∈ m, x < y → ContinuousOn f (Icc x y)) → (∀ y ∈ m, f y = 0) →
      ∃ m' : Multiset ℝ, m'.card = n ∧ (∀ y ∈ m', y ∈ Ioo a b) ∧ (∀ y ∈ m', ∃ z ∈ m, y ≤ z) ∧
        (∀ y ∈ m, m'.count y + 1 = m.count y) ∧
        (∀ y ∈ m', y ∉ m → m'.count y = 1 ∧ deriv f y = 0) := by
  induction n with
  | zero =>
    intro m hm _ _ _ _
    obtain ⟨x, rfl⟩ := Multiset.card_eq_one.1 hm
    refine ⟨0, rfl, by simp, by simp, fun y hy => ?_, by simp⟩
    rw [Multiset.mem_singleton] at hy
    simp [hy]
  | succ n ih =>
    intro m hm hmem hrep hcont hzero
    obtain ⟨M, hM, hMmax⟩ := Multiset.exists_max_image id (s := m) (by rintro rfl; simp at hm)
    obtain ⟨r, rfl⟩ := Multiset.exists_cons_of_mem hM
    have hr : r.card = n + 1 := by simpa using hm
    have hsub : ∀ y ∈ r, y ∈ M ::ₘ r := fun y hy => Multiset.mem_cons_of_mem hy
    have hcount : ∀ y, r.count y ≤ (M ::ₘ r).count y := fun y => by
      rw [Multiset.count_cons]; omega
    obtain ⟨r', hr'c, hr'Ioo, hr'le, hr'count, hr'new⟩ := ih r hr (fun y hy => hmem y (hsub y hy))
      (fun y hy h => hrep y (hsub y hy) (h.trans_le (hcount y)))
      (fun x hx y hy => hcont x (hsub x hx) y (hsub y hy)) (fun y hy => hzero y (hsub y hy))
    obtain ⟨M₂, hM₂, hM₂max⟩ := Multiset.exists_max_image id (s := r) (by rintro rfl; simp at hr)
    simp only [id] at hMmax hM₂max
    rcases (hMmax M₂ (hsub M₂ hM₂)).eq_or_lt with h | h
    · -- the maximum is repeated: keep it as a zero of `deriv f`
      subst h
      refine ⟨M₂ ::ₘ r', by simp [hr'c], fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
        fun y hy hny => ?_⟩
      · rcases Multiset.mem_cons.1 hy with rfl | hy
        · refine hrep y hM ?_
          rw [Multiset.count_cons_self]
          have := Multiset.count_pos.2 hM₂
          omega
        · exact hr'Ioo y hy
      · rcases Multiset.mem_cons.1 hy with rfl | hy
        · exact ⟨y, hM, le_rfl⟩
        · obtain ⟨z, hz, hyz⟩ := hr'le y hy
          exact ⟨z, hsub z hz, hyz⟩
      · by_cases hyM : y = M₂
        · subst hyM
          rw [Multiset.count_cons_self, Multiset.count_cons_self]
          have := hr'count y hM₂
          omega
        · rw [Multiset.count_cons_of_ne hyM, Multiset.count_cons_of_ne hyM]
          exact hr'count y ((Multiset.mem_cons.1 hy).resolve_left hyM)
      · have hyM : y ≠ M₂ := fun e => hny (e ▸ hM)
        rw [Multiset.count_cons_of_ne hyM]
        exact hr'new y ((Multiset.mem_cons.1 hy).resolve_left hyM) fun h' => hny (hsub y h')
    · -- the maximum is simple: Rolle between `M₂` and `M`
      obtain ⟨ξ, hξ, hdξ⟩ := exists_deriv_eq_zero h (hcont M₂ (hsub M₂ hM₂) M hM h)
        ((hzero M₂ (hsub M₂ hM₂)).trans (hzero M hM).symm)
      have hrlt : ∀ y ∈ r, y < ξ := fun y hy => by linarith [hM₂max y hy, hξ.1]
      have hlt : ∀ y ∈ r', y < ξ := fun y hy => by
        obtain ⟨z, hz, hyz⟩ := hr'le y hy
        linarith [hrlt z hz]
      have hξr' : ξ ∉ r' := fun h' => lt_irrefl ξ (hlt ξ h')
      refine ⟨ξ ::ₘ r', by simp [hr'c], fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
        fun y hy hny => ?_⟩
      · rcases Multiset.mem_cons.1 hy with rfl | hy
        · exact ⟨by linarith [(hmem M₂ (hsub M₂ hM₂)).1, hξ.1], by linarith [(hmem M hM).2, hξ.2]⟩
        · exact hr'Ioo y hy
      · rcases Multiset.mem_cons.1 hy with rfl | hy
        · exact ⟨M, hM, hξ.2.le⟩
        · obtain ⟨z, hz, hyz⟩ := hr'le y hy
          exact ⟨z, hsub z hz, hyz⟩
      · rcases Multiset.mem_cons.1 hy with rfl | hyr
        · have hMr : y ∉ r := fun h' => by linarith [hrlt y h', hξ.2]
          have hMm' : y ∉ ξ ::ₘ r' := fun h' => by
            rcases Multiset.mem_cons.1 h' with e | h'
            · linarith [hξ.2]
            · linarith [hlt y h', hξ.2]
          rw [Multiset.count_cons_self, Multiset.count_eq_zero.2 hMr, Multiset.count_eq_zero.2 hMm']
        · rw [Multiset.count_cons_of_ne (hrlt y hyr).ne,
            Multiset.count_cons_of_ne (by linarith [hM₂max y hyr] : y ≠ M)]
          exact hr'count y hyr
      · rcases Multiset.mem_cons.1 hy with rfl | hyr'
        · exact ⟨by rw [Multiset.count_cons_self, Multiset.count_eq_zero.2 hξr'], hdξ⟩
        · rw [Multiset.count_cons_of_ne (hlt y hyr').ne]
          exact hr'new y hyr' fun h' => hny (hsub y h')

/-- The Rolle step, stated for the jets of `deriv f`. -/
private lemma exists_multiset_iteratedDeriv_deriv {f : ℝ → ℝ} {a b : ℝ} {m : Multiset ℝ}
    {n : ℕ} (hm : m.card = n + 1) (hmem : ∀ y ∈ m, y ∈ Icc a b)
    (hrep : ∀ y ∈ m, 1 < m.count y → y ∈ Ioo a b)
    (hcont : ∀ x ∈ m, ∀ y ∈ m, x < y → ContinuousOn f (Icc x y))
    (hz : ∀ y ∈ m, ∀ j < m.count y, iteratedDeriv j f y = 0) :
    ∃ m' : Multiset ℝ, m'.card = n ∧ (∀ y ∈ m', y ∈ Ioo a b) ∧
      ∀ y ∈ m', ∀ j < m'.count y, iteratedDeriv j (deriv f) y = 0 := by
  obtain ⟨m', hm', hIoo, -, hcount, hnew⟩ := exists_multiset_deriv_zeros n m hm hmem hrep hcont
    (fun y hy => by simpa using hz y hy 0 (Multiset.count_pos.2 hy))
  refine ⟨m', hm', hIoo, fun y hy j hj => ?_⟩
  by_cases hym : y ∈ m
  · rw [← iteratedDeriv_succ']
    exact hz y hym (j + 1) (by have := hcount y hym; omega)
  · obtain ⟨h1, h2⟩ := hnew y hy hym
    obtain rfl : j = 0 := by omega
    simpa using h2

/-- Iterated Rolle for zeros inside the open interval. -/
private lemma exists_iteratedDeriv_eq_zero_of_multiset_Ioo {a b : ℝ} (q : ℕ) :
    ∀ (f : ℝ → ℝ) (m : Multiset ℝ), m.card = q + 1 → (∀ y ∈ m, y ∈ Ioo a b) →
      ContDiffOn ℝ q f (Ioo a b) → (∀ y ∈ m, ∀ j < m.count y, iteratedDeriv j f y = 0) →
      ∃ ξ ∈ Ioo a b, iteratedDeriv q f ξ = 0 := by
  induction q with
  | zero =>
    intro f m hm hIoo _ hz
    obtain ⟨y, rfl⟩ := Multiset.card_eq_one.1 hm
    exact ⟨y, hIoo y (Multiset.mem_singleton_self y),
      hz y (Multiset.mem_singleton_self y) 0 (by simp)⟩
  | succ q ih =>
    intro f m hm hIoo hf hz
    obtain ⟨m', hm', hIoo', hz'⟩ := exists_multiset_iteratedDeriv_deriv hm
      (fun y hy => Ioo_subset_Icc_self (hIoo y hy)) (fun y hy _ => hIoo y hy)
      (fun x hx y hy _ => hf.continuousOn.mono (Icc_subset_Ioo (hIoo x hx).1 (hIoo y hy).2)) hz
    rw [iteratedDeriv_succ']
    exact ih _ m' hm' hIoo' (hf.deriv_of_isOpen isOpen_Ioo (by norm_cast)) hz'

/-- **Rolle's theorem with multiplicities**: let $m$ be a multiset of $q + 2$ points of
$[a, b]$, every point of multiplicity at least $2$ in $(a, b)$, and let $f$ be continuous on
$[a, b]$ and $C^{q+1}$ on $(a, b)$ with $f^{(j)}(y) = 0$ for every $y \in m$ and every $j$ below
the multiplicity of $y$. Then $f^{(q+1)}(\xi) = 0$ for some $\xi \in (a, b)$.
[DeBoor2005, proof of Proposition 43], iterating the interlacing of the derivative zeros. -/
theorem exists_iteratedDeriv_eq_zero_of_multiset {f : ℝ → ℝ} {a b : ℝ} {m : Multiset ℝ} {q : ℕ}
    (hm : m.card = q + 2) (hmem : ∀ y ∈ m, y ∈ Icc a b)
    (hrep : ∀ y ∈ m, 1 < m.count y → y ∈ Ioo a b) (hf : ContinuousOn f (Icc a b))
    (hf' : ContDiffOn ℝ (q + 1 : ℕ) f (Ioo a b))
    (hz : ∀ y ∈ m, ∀ j < m.count y, iteratedDeriv j f y = 0) :
    ∃ ξ ∈ Ioo a b, iteratedDeriv (q + 1) f ξ = 0 := by
  obtain ⟨m', hm', hIoo, hz'⟩ := exists_multiset_iteratedDeriv_deriv hm hmem hrep
    (fun x hx y hy _ => hf.mono (Icc_subset_Icc (hmem x hx).1 (hmem y hy).2)) hz
  rw [iteratedDeriv_succ']
  exact exists_iteratedDeriv_eq_zero_of_multiset_Ioo q _ m' hm' hIoo
    (hf'.deriv_of_isOpen isOpen_Ioo (by norm_cast)) hz'
