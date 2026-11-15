/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Ops.Logic.Probabilistic

/-!
# Probabilistic block specifications for a family of preconditions

A contract of a randomized routine is often a family `∀ x, PWrites … (P x) (Q x) φ`: one good set
of tapes for each input `x` (a matrix stored in the memory, say). A caller that runs the routine
at a memory whose input is not known in advance needs **one** good set, measurable in the memory,
and a family of good sets chosen independently for each `x` need not be measurable jointly in
`x`. When the input is determined by the memory and the relation between the memory before and
after the run that the family guarantees is contained in a measurable set `T`, the largest good
set "the run ends in `T`" serves for every input at once (`NLAlib.Ops.PWrites.pstep_of_forall`).

Also here: consequence through the frame (`NLAlib.Ops.PWrites.mono_eqOff`), the branch on a size
(`NLAlib.Ops.PWrites.ifPos`), and the measurability of the frame relation and of a stored cell.

## Main results

* `NLAlib.Ops.PWrites.pstep_of_forall`: a family of probabilistic block specifications with a
  measurable relation is one probabilistic step specification.
* `NLAlib.Ops.PWrites.mono_eqOff`, `NLAlib.Ops.PWrites.ifPos`.
* `NLAlib.Ops.Mem.measurableSet_eqOff`, `NLAlib.Ops.Mem.measurableSet_get_eq`.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.Ops

variable {Op Tst K : Type}

section Measurable

variable [Inhabited K] [MeasurableSpace K] [MeasurableEq K]

/-- **The frame relation is measurable**: the pairs of memories whose stores have the same shape
and the same cells off `F` form a measurable set. -/
theorem Mem.measurableSet_eqOff (F : Fp) :
    MeasurableSet {x : Mem K × Mem K | x.1.store.EqOff F x.2.store} := by
  classical
  have hc : ∀ b i : ℕ, MeasurableSet {x : Mem K × Mem K |
      x.2.store.get b i = x.1.store.get b i} := by
    intro b i
    have e : {x : Mem K × Mem K | x.2.store.get b i = x.1.store.get b i} =
        {x | (x.2.store.get b i).isSome = (x.1.store.get b i).isSome} ∩
          {x | (x.2.store.get b i).getD default = (x.1.store.get b i).getD default} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · intro h
        rw [h]
        exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        revert h1 h2
        cases x.2.store.get b i <;> cases x.1.store.get b i <;> simp
    rw [e]
    have hm := Mem.measurable_cell (K := K) (b, i)
    exact (measurableSet_eq_fun (measurable_fst.comp (hm.comp measurable_snd))
      (measurable_fst.comp (hm.comp measurable_fst))).inter
      (measurableSet_eq_fun (measurable_snd.comp (hm.comp measurable_snd))
        (measurable_snd.comp (hm.comp measurable_fst)))
  have e : {x : Mem K × Mem K | x.1.store.EqOff F x.2.store} =
      {x | x.2.store.shape = x.1.store.shape} ∩
        ⋂ b : ℕ, ⋂ i : ℕ, {x | F b i ∨ x.2.store.get b i = x.1.store.get b i} := by
    ext x
    simp only [Store.EqOff, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    refine and_congr Iff.rfl ⟨fun h b i => ?_, fun h b i hF => (h b i).resolve_left hF⟩
    by_cases hF : F b i
    · exact Or.inl hF
    · exact Or.inr (h b i hF)
  rw [e]
  refine (Mem.measurableSet_shape_eq measurable_snd measurable_fst).inter
    (.iInter fun b => .iInter fun i => ?_)
  by_cases hF : F b i
  · simp [hF]
  · simpa [hF] using hc b i

/-- **A stored cell with a given value** is a measurable set of memories. -/
theorem Mem.measurableSet_get_eq (z : ℕ × ℕ) (v : K) :
    MeasurableSet {m : Mem K | m.store.get z.1 z.2 = some v} := by
  have e : {m : Mem K | m.store.get z.1 z.2 = some v} =
      (fun m : Mem K => ((m.store.get z.1 z.2).isSome, (m.store.get z.1 z.2).getD default)) ⁻¹'
        {(true, v)} := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    cases m.store.get z.1 z.2 <;> simp
  rw [e]
  exact Mem.measurable_cell z (measurableSet_singleton _)

end Measurable

namespace PWrites

variable [Inhabited K] [MeasurableSpace K] {law : ℕ → Measure K} {I : Interp Op Tst K}
  {c : Stmt Op Tst} {ρ : Env} {F : Fp} {Pre Post : Mem K → Prop} {φ : ℝ}

/-- **Consequence through the frame**: a stronger precondition, and a postcondition that may use
the initial memory and the frame of the run. -/
theorem mono_eqOff {Pre' Post' : Mem K → Prop} (h : PWrites law I c ρ F Pre Post φ)
    (hPre : ∀ m, Pre' m → Pre m)
    (hPost : ∀ m m', Pre' m → m.store.EqOff F m'.store → Post m' → Post' m') :
    PWrites law I c ρ F Pre' Post' φ :=
  PStep.mono h hPre (fun m m' hm ⟨e, hp⟩ => ⟨e, hPost m m' hm e hp⟩) le_rfl

/-- **The branch on a size**: `ifPos e body` runs the body once (at the index $0$) when $e > 0$
and does nothing otherwise. The failure bound is that of the body, and nonnegative. -/
theorem ifPos {e : IExp} {body : Stmt Op Tst} {n : ℕ} (he : e.eval ρ.idx = some n) (hφ : 0 ≤ φ)
    (h : 0 < n → PWrites law I body (ρ.pushIdx 0) F Pre Post φ)
    (h0 : n = 0 → ∀ m, Pre m → Post m) :
    PWrites law I (.ifPos e body) ρ F Pre Post φ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine of_writes hφ fun m τ hm => writes_ifPos he ?_
    rw [if_neg (lt_irrefl 0)]
    exact h0 rfl m hm
  · obtain ⟨G, hGm, hGd, hG⟩ := h hn
    refine ⟨G, hGm, hGd, fun m hm => ⟨fun τ hτ => writes_ifPos he ?_, (hG m hm).2⟩⟩
    rw [if_pos hn]
    exact (hG m hm).1 τ hτ

/-- **A family of probabilistic block specifications is one probabilistic step**: under a
measurable interpretation whose operations read the tape only in their windows, if for every
input `x` the run from the memories of `P x` writes only `F` and ends in `Q x` except with
probability at most $\varphi$, and every such outcome lies in a measurable set `T` of pairs of
memories (before, after), then from every memory of some `P x` the run ends in `T` except with
probability at most $\varphi$. The good set is the largest one, "the run ends in `T`"; it does
not depend on the input, so `T` carries whatever the caller needs to know about the input. -/
theorem pstep_of_forall [MeasurableEq K] (hI : I.IsMeasurable) {win : Op → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {ι : Type*} {P Q : ι → Mem K → Prop}
    (h : ∀ x, PWrites law I c ρ F (P x) (Q x) φ) {T : Set (Mem K × Mem K)}
    (hT : MeasurableSet T)
    (hPT : ∀ x m m', P x m → m.store.EqOff F m'.store → Q x m' → (m, m') ∈ T) :
    PStep law (fun τ m => eval I τ c ρ m) (fun m => ∃ x, P x m) (fun m m' => (m, m') ∈ T) φ := by
  have hev := hI.measurable_eval c ρ
  have hsw : Measurable fun x : Mem K × Tape K => (x.2, x.1) := measurable_snd.prodMk measurable_fst
  refine ⟨fun m => {τ | ∃ m', eval I τ c ρ m = some m' ∧ (m, m') ∈ T}, ?_, ?_, ?_⟩
  · have e : {x : Mem K × Tape K | x.2 ∈ {τ | ∃ m', eval I τ c ρ x.1 = some m' ∧ (x.1, m') ∈ T}} =
        {x | (eval I x.2 c ρ x.1).isSome = true} ∩
          {x | (x.1, (eval I x.2 c ρ x.1).getD x.1) ∈ T} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      cases eval I x.2 c ρ x.1 <;> simp
    rw [e]
    exact ((hev.1.comp hsw) (measurableSet_singleton true)).inter
      ((measurable_fst.prodMk (hev.2.comp hsw)) hT)
  · intro m τ τ' hττ'
    have := Follows.eq_of_agree (f := fun τ m => eval I τ c ρ m)
      (fun τ τ' => run_follows hloc τ τ' c ρ) (m := m) hττ'
    simp only [Set.mem_ofPred_eq, this]
  · rintro m ⟨x, hx⟩
    obtain ⟨G, -, -, hG⟩ := h x
    obtain ⟨hW, hP⟩ := hG m hx
    have hsub : ∀ τ ∈ G m, ∃ m', eval I τ c ρ m = some m' ∧ (m, m') ∈ T := fun τ hτ => by
      obtain ⟨m', he, hEq, hq⟩ := hW τ hτ
      exact ⟨m', he, hPT x m m' hx hEq hq⟩
    refine ⟨fun τ hτ => hτ, fun P ξ hξ => ?_⟩
    have := hξ.isProbabilityMeasure
    refine (measureReal_mono fun ω (hω : ω ∈ {ω | ξ ω ∉ {τ | ∃ m', eval I τ c ρ m = some m' ∧
      (m, m') ∈ T}}) (hmem : ξ ω ∈ G m) => hω (hsub _ hmem)).trans (hP P ξ hξ)

end PWrites

end NLAlib.Ops
