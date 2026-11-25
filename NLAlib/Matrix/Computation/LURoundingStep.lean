/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLURoundingState
public import NLAlib.Matrix.Computation.SchurTotalRoundingTrace

/-!
# Shared rounded LU elimination phase

The factor-column divisions and saved-pivot Schur trace advance the same numerical prefix
under either partial or complete pivoting. This phase does not choose a pivot.

## Main results

* `NLAlib.Computation.PLURounding.exec_totalPhase`: actual rounded materialization and update.
-/

@[expose] public section

namespace NLAlib.Computation.PLURounding

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Materialize the rounded factor column and upper row, then execute the zero-safe saved
pivot Schur update. The existing rounding prefix advances independently of pivot policy;
maximality of the active column handles a zero pivot. The supplied frame retains a log. -/
theorem exec_totalPhase {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (st : St P K C) (S L U H : ℕ) (lo uo ho : IExp ℕ)
    (B M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : HoldsDecoded st.store dec tag S 0 M)
    (hF : HoldsDecoded st.store dec tag L lo.eval F)
    (hG : HoldsDecoded st.store dec tag U uo.eval G)
    (hmax : ∀ i : Fin n.eval, ⟨k.eval, hk⟩ ≤ i →
      |M i ⟨k.eval, hk⟩| ≤ |M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩|)
    (hpref : u tag < 1 → IsLURoundingPrefix (u tag) k.eval B M F G)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSH : S ≠ H) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (base : Store P K) (hframe : PLU.Frame base n.eval S L U H lo.eval uo.eval ho.eval st.store) :
    let r : Fin n.eval := ⟨k.eval, hk⟩
    ∃ (out : St P K C) (M' : Matrix (Fin n.eval) (Fin n.eval) ℝ) (v : Fin n.eval → ℝ),
      exec I (do
        luColumnTotal tag n k S L U 0 lo uo
        schurStepTotal tag n S 0 k).run st = some out ∧
      PLU.Frame base n.eval S L U H lo.eval uo.eval ho.eval out.store ∧
      HoldsDecoded out.store dec tag S 0 M' ∧
      HoldsDecoded out.store dec tag L lo.eval (F.updateCol r v) ∧
      HoldsDecoded out.store dec tag U uo.eval
        (G.updateRow r (fun j => if j < r then 0 else M r j)) ∧
      (∀ i, i < r → v i = 0) ∧ v r = 1 ∧
      (∀ i, r < i → RelErr (u tag) (M i r / M r r) (v i)) ∧
      (u tag < 1 → IsLURoundingPrefix (u tag) (k.eval + 1) B M'
        (F.updateCol r v) (G.updateRow r (fun j => if j < r then 0 else M r j))) ∧
      ∀ q i, out.store.read q H i = st.store.read q H i := by
  dsimp only
  let r : Fin n.eval := ⟨k.eval, hk⟩
  have hu : 0 ≤ u tag := h.nonneg trivial
  obtain ⟨mid, WL, WU, v, hr₁, -, -, hw₁, hF', hG', hv0, hv1, hvrel⟩ :=
    h.exec_luColumnTotal I n k hi tag st S L U 0 lo uo M F G hk hM hF hG hSL hSU hLU
  have hM' : HoldsDecoded mid.store dec tag S 0 M := by
    intro i j
    obtain ⟨w, hw, hd⟩ := hM i j
    refine ⟨w, ?_, hd⟩
    rw [Store.read_of_writeBlocks_eq_some_of_forall hw₁ (fun block hblock => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
      rcases hblock with rfl | rfl
      · exact Or.inl hSL
      · exact Or.inl hSU)]
    exact hw
  obtain ⟨out, W, hr₂, hWs, hw₂, hM'', htrace⟩ :=
    h.exec_schurStepTotal_trace I tag mid n S 0 k M hk hM'
  refine ⟨out, _, v, ?_, (hframe.write_factors hw₁).write_residual hw₂ hWs, hM'',
    ?_, ?_, hv0, hv1, hvrel, ?_, ?_⟩
  · rw [exec_run_bind I (b := luColumnTotal tag n k S L U 0 lo uo) (fun _ => rfl),
      hr₁, Option.bind_some]
    exact hr₂
  · intro i j
    obtain ⟨w, hw, hd⟩ := hF' i j
    exact ⟨w, (Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hSL.symm)).trans hw, hd⟩
  · intro i j
    obtain ⟨w, hw, hd⟩ := hG' i j
    exact ⟨w, (Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hSU.symm)).trans hw, hd⟩
  · intro hu1
    rcases htrace with ⟨hp, he⟩ | ⟨hp, ell, c, t, q, hell, hc, ht, hq⟩
    · rw [he]
      apply (hpref hu1).step_of_eq_zero hu hk v hv0 hv1 hvrel hp
      intro i hri
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa only [hp, abs_zero] using hmax i hri) (abs_nonneg _)
    · exact (hpref hu1).step_of_ne_zero hu hu1 hk v _ ell c t q hv0 hv1 hvrel hp hell hc ht
        (fun i j => (hq i j).1) (fun i j => (hq i j).2)
  · intro q i
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hSH.symm),
      Store.read_of_writeBlocks_eq_some_of_forall hw₁ (fun block hblock => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
        rcases hblock with rfl | rfl
        · exact Or.inl hLH.symm
        · exact Or.inl hUH.symm)]


end NLAlib.Computation.PLURounding
