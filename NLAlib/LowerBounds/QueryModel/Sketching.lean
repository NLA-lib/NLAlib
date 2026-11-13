/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.QueryModel.Basic
public import NLAlib.Matrix.Factorizations.SketchedLowRank
public import NLAlib.Probability.Measurability.Matrix

/-!
# Sketching algorithms in the two-sided query model

The seed contains right and left test matrices. Querying their columns produces the two
sketches using only the matrix–vector oracle for the matrix and its adjoint. The right and
left widths may differ; all probes are fixed before any response, so one pass suffices.
Generalized Nyström postprocesses these sketches, without further access to the matrix.

This is an exact oracle representation, not an arithmetic or finite-precision cost theorem.
It does not turn a two-sided algorithm into a one-sided algorithm.

## Main results

* `NLAlib.run_twoSidedSketchQueryAlgorithm`: the output is the pair of matrix sketches.
* `NLAlib.rightCount_twoSidedSketchQueryAlgorithm_le`: the right sketch width bounds products.
* `NLAlib.leftCount_twoSidedSketchQueryAlgorithm_le`: the left sketch width bounds products.
* `NLAlib.run_generalizedNystromQueryAlgorithm`: the oracle output is generalized Nyström.
* `NLAlib.run_generalizedNystromQueryAlgorithm_eq_self_of_rank_eq`: low-rank exact recovery.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] {q p : ℕ}

/-- A seeded two-sided sketch takes q right probes and p left probes. The first q queries
have only a right component, and the last p only a left component. The output is the pair
of sampled matrices. The algorithm receives no matrix, and q+p is its round budget.
All probes are fixed by the seed, so their ordering does not require extra passes.
[TroppYurtseverUdellCevher2017, (4.1)–(4.2)].
Algorithm: two-sided-sketch (run model) -/
def twoSidedSketchQueryAlgorithm (Ω : Matrix n (Fin q) 𝕜) (Ψ : Matrix m (Fin p) 𝕜) :
    QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) ((m → 𝕜) × (n → 𝕜)) (q + p)
      (Matrix m (Fin q) 𝕜 × Matrix n (Fin p) 𝕜) where
  query i _ := if hi : i < q then (fun a => Ω a ⟨i, hi⟩, 0)
    else if hip : i < q + p then (0, fun a => Ψ a ⟨i - q, by omega⟩) else (0, 0)
  output τ := (Matrix.of fun a j => (τ (Fin.castAdd p j)).1 a,
    Matrix.of fun a j => (τ ⟨q + j, by omega⟩).2 a)

omit [Fintype m] [Fintype n] in
/-- The seeded two-sided sketch makes no response-dependent query. -/
theorem isNonAdaptive_twoSidedSketchQueryAlgorithm
    (Ω : Matrix n (Fin q) 𝕜) (Ψ : Matrix m (Fin p) 𝕜) :
    (twoSidedSketchQueryAlgorithm Ω Ψ).IsNonAdaptive := by
  intro i hi h h'
  rfl

omit [Fintype m] [Fintype n] in
/-- Every query of the two-sided sketch belongs to the same pass, labelled zero.
For a nonempty round budget this is one pass; an empty budget makes no query. -/
theorem isPassStructured_twoSidedSketchQueryAlgorithm
    (Ω : Matrix n (Fin q) 𝕜) (Ψ : Matrix m (Fin p) 𝕜) :
    (twoSidedSketchQueryAlgorithm Ω Ψ).IsPassStructured (fun _ => 0) :=
  (QueryAlgorithm.isPassStructured_zero_iff_isNonAdaptive _).mpr
    (isNonAdaptive_twoSidedSketchQueryAlgorithm Ω Ψ)

/-- Running the two-sided sampler gives exactly the right sketch and adjoint-left sketch,
including empty sketch widths. The output contains no unqueried entries of the matrix. -/
theorem run_twoSidedSketchQueryAlgorithm (A : Matrix m n 𝕜)
    (Ω : Matrix n (Fin q) 𝕜) (Ψ : Matrix m (Fin p) 𝕜) :
    (twoSidedSketchQueryAlgorithm Ω Ψ).run (twoSidedMulVec A) = (A * Ω, Aᴴ * Ψ) := by
  apply Prod.ext
  · ext a j
    change ((twoSidedSketchQueryAlgorithm Ω Ψ).history (twoSidedMulVec A)
      (q + p) (Fin.castAdd p j)).1 a = _
    rw [QueryAlgorithm.history_apply]
    simp only [QueryAlgorithm.queryAt, twoSidedSketchQueryAlgorithm, Fin.val_castAdd,
      dif_pos j.isLt, twoSidedMulVec, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext a j
    change ((twoSidedSketchQueryAlgorithm Ω Ψ).history (twoSidedMulVec A)
      (q + p) ⟨q + j, by omega⟩).2 a = _
    rw [QueryAlgorithm.history_apply]
    simp only [QueryAlgorithm.queryAt, twoSidedSketchQueryAlgorithm,
      dif_neg (show ¬ q + j.val < q by omega),
      dif_pos (show q + j.val < q + p by omega), Nat.add_sub_cancel_left,
      twoSidedMulVec, Matrix.mul_apply, Matrix.mulVec, dotProduct]

omit [Fintype m] [Fintype n] in
/-- The two-sided sampler uses at most q right products on every transcript. Zero probes
are free under the query model's nonzero-product convention. -/
theorem rightCount_twoSidedSketchQueryAlgorithm_le
    (Ω : Matrix n (Fin q) 𝕜) (Ψ : Matrix m (Fin p) 𝕜)
    (τ : Fin (q + p) → (m → 𝕜) × (n → 𝕜)) :
    (twoSidedSketchQueryAlgorithm Ω Ψ).rightCount τ ≤ q := by
  classical
  let S := {j : Fin (q + p) | ((twoSidedSketchQueryAlgorithm Ω Ψ).queries τ j).1 ≠ 0}
  change S.ncard ≤ q
  have hs (j : Fin (q + p)) (hj : j ∈ S) : j.val < q := by
    by_contra h
    simp only [S, Set.mem_ofPred_eq, QueryAlgorithm.queries, twoSidedSketchQueryAlgorithm,
      dif_neg h] at hj
    split_ifs at hj <;> exact hj rfl
  by_cases hq : q = 0
  · subst q
    have he : S = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun j hj => by
      have := hs j hj
      omega
    simp only [he, Set.ncard_empty, le_refl]
  · have h := Set.ncard_le_ncard_of_injOn (s := S) (t := (Set.univ : Set (Fin q)))
      (fun j => if hj : j ∈ S then ⟨j.val, hs j hj⟩ else ⟨0, Nat.pos_of_ne_zero hq⟩)
      (fun _ _ => Set.mem_univ _) ?_ (Set.toFinite _)
    · simpa using h
    · intro i hi j hj hij
      simp only [dif_pos hi, dif_pos hj, Fin.mk.injEq] at hij
      exact Fin.ext hij

omit [Fintype m] [Fintype n] in
/-- The two-sided sampler uses at most p left products on every transcript. Its left
queries require access to the adjoint oracle, separately from the q right products. -/
theorem leftCount_twoSidedSketchQueryAlgorithm_le
    (Ω : Matrix n (Fin q) 𝕜) (Ψ : Matrix m (Fin p) 𝕜)
    (τ : Fin (q + p) → (m → 𝕜) × (n → 𝕜)) :
    (twoSidedSketchQueryAlgorithm Ω Ψ).leftCount τ ≤ p := by
  classical
  let S := {j : Fin (q + p) | ((twoSidedSketchQueryAlgorithm Ω Ψ).queries τ j).2 ≠ 0}
  change S.ncard ≤ p
  have hs (j : Fin (q + p)) (hj : j ∈ S) : q ≤ j.val := by
    by_contra h
    have hjq : j.val < q := by omega
    simp only [S, Set.mem_ofPred_eq, QueryAlgorithm.queries, twoSidedSketchQueryAlgorithm,
      dif_pos hjq] at hj
    exact hj rfl
  by_cases hp : p = 0
  · subst p
    have he : S = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun j hj => by
      have := hs j hj
      have := j.isLt
      omega
    simp only [he, Set.ncard_empty, le_refl]
  · have h := Set.ncard_le_ncard_of_injOn (s := S) (t := (Set.univ : Set (Fin p)))
      (fun j => if hj : j ∈ S then ⟨j.val - q, by have := hs j hj; omega⟩
        else ⟨0, Nat.pos_of_ne_zero hp⟩)
      (fun _ _ => Set.mem_univ _) ?_ (Set.toFinite _)
    · simpa using h
    · intro i hi j hj hij
      simp only [dif_pos hi, dif_pos hj, Fin.mk.injEq] at hij
      apply Fin.ext
      have := hs i hi
      have := hs j hj
      omega

omit [Fintype m] [Fintype n] in
/-- Joint measurability of the two-sided sampler in both sketch seeds and responses.
No seed distribution or independence is needed. -/
theorem isMeasurableFamily_twoSidedSketchQueryAlgorithm :
    QueryAlgorithm.IsMeasurableFamily (fun s : Matrix n (Fin q) 𝕜 × Matrix m (Fin p) 𝕜 =>
      twoSidedSketchQueryAlgorithm s.1 s.2) := by
  constructor
  · intro i hi
    simp only [twoSidedSketchQueryAlgorithm]
    split_ifs <;> fun_prop
  · change Measurable fun s : (Matrix n (Fin q) 𝕜 × Matrix m (Fin p) 𝕜) ×
        (Fin (q + p) → (m → 𝕜) × (n → 𝕜)) =>
      ((fun a j => (s.2 (Fin.castAdd p j)).1 a),
        (fun a (j : Fin p) => (s.2 ⟨q + j, by omega⟩).2 a))
    fun_prop

/-- Generalized Nyström from a two-sided sketch seed: the output is obtained by multiplying
the sampled right matrix by the pseudoinverse of its left sketch and the adjoint of the
sampled adjoint-left matrix. There are q+p oracle rounds, with at most q right and p left
products, all in one pass. No matrix is supplied to this algorithm.
[EpperlyWebber2026, Definition 4.1].
Algorithm: generalized-nystrom (run model) -/
noncomputable def generalizedNystromQueryAlgorithm
    (Ω : Matrix n (Fin q) 𝕜) (Ψ : Matrix m (Fin p) 𝕜) :
    QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) ((m → 𝕜) × (n → 𝕜)) (q + p) (Matrix m n 𝕜) :=
  (twoSidedSketchQueryAlgorithm Ω Ψ).mapOutput fun YZ =>
    YZ.1 * pinv (Ψᴴ * YZ.1) * YZ.2ᴴ

omit [Fintype n] in
/-- Generalized Nyström is nonadaptive in the two-sided oracle: its pseudoinverse is computed
only after all right and left sketch responses have arrived. -/
theorem isNonAdaptive_generalizedNystromQueryAlgorithm
    (Ω : Matrix n (Fin q) 𝕜) (Ψ : Matrix m (Fin p) 𝕜) :
    (generalizedNystromQueryAlgorithm Ω Ψ).IsNonAdaptive :=
  isNonAdaptive_twoSidedSketchQueryAlgorithm Ω Ψ

omit [Fintype n] in
/-- Generalized Nyström uses one pass in the two-sided oracle model. Both the right and left
probe matrices are chosen before any response; postprocessing makes no oracle call. -/
theorem isPassStructured_generalizedNystromQueryAlgorithm
    (Ω : Matrix n (Fin q) 𝕜) (Ψ : Matrix m (Fin p) 𝕜) :
    (generalizedNystromQueryAlgorithm Ω Ψ).IsPassStructured (fun _ => 0) :=
  (isPassStructured_twoSidedSketchQueryAlgorithm Ω Ψ).mapOutput _

omit [Fintype n] in
/-- Generalized Nyström makes at most q right products, for every transcript. -/
theorem rightCount_generalizedNystromQueryAlgorithm_le
    (Ω : Matrix n (Fin q) 𝕜) (Ψ : Matrix m (Fin p) 𝕜)
    (τ : Fin (q + p) → (m → 𝕜) × (n → 𝕜)) :
    (generalizedNystromQueryAlgorithm Ω Ψ).rightCount τ ≤ q :=
  rightCount_twoSidedSketchQueryAlgorithm_le Ω Ψ τ

omit [Fintype n] in
/-- Generalized Nyström makes at most p adjoint-left products, for every transcript.
This budget is separate from the right-product budget. -/
theorem leftCount_generalizedNystromQueryAlgorithm_le
    (Ω : Matrix n (Fin q) 𝕜) (Ψ : Matrix m (Fin p) 𝕜)
    (τ : Fin (q + p) → (m → 𝕜) × (n → 𝕜)) :
    (generalizedNystromQueryAlgorithm Ω Ψ).leftCount τ ≤ p :=
  leftCount_twoSidedSketchQueryAlgorithm_le Ω Ψ τ

omit [Fintype n] in
/-- Generalized Nyström is jointly measurable in both sketch seeds and oracle responses,
including rank-deficient or empty sketches. No seed distribution is assumed. -/
theorem isMeasurableFamily_generalizedNystromQueryAlgorithm :
    QueryAlgorithm.IsMeasurableFamily (fun s : Matrix n (Fin q) 𝕜 × Matrix m (Fin p) 𝕜 =>
      generalizedNystromQueryAlgorithm s.1 s.2) := by
  constructor
  · exact isMeasurableFamily_twoSidedSketchQueryAlgorithm.measurable_query
  · have h := (isMeasurableFamily_twoSidedSketchQueryAlgorithm
      (𝕜 := 𝕜) (m := m) (n := n) (q := q) (p := p)).measurable_output
    have hΨ : Measurable fun z : (Matrix n (Fin q) 𝕜 × Matrix m (Fin p) 𝕜) ×
        (Fin (q + p) → (m → 𝕜) × (n → 𝕜)) => z.1.2ᴴ :=
      Measurable.matrix_conjTranspose continuous_star.measurable measurable_fst.snd
    exact (h.fst.matrix_mul (measurable_pinv.comp (hΨ.matrix_mul h.fst))).matrix_mul
      (Measurable.matrix_conjTranspose continuous_star.measurable h.snd)

/-- The two-sided oracle implementation returns
$\mathsf{gn}(\mathbf{A},\mathbf{\Omega},\mathbf{\Psi})$ for all sketch widths,
including zero, and for every rank of $\mathbf{A}$. -/
theorem run_generalizedNystromQueryAlgorithm (A : Matrix m n 𝕜)
    (Ω : Matrix n (Fin q) 𝕜) (Ψ : Matrix m (Fin p) 𝕜) :
    (generalizedNystromQueryAlgorithm Ω Ψ).run (twoSidedMulVec A) =
      generalizedNystrom A Ω Ψ := by
  rw [generalizedNystromQueryAlgorithm, QueryAlgorithm.run_mapOutput,
    run_twoSidedSketchQueryAlgorithm, generalizedNystrom_def]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- The existing low-rank exactness theorem certifies the oracle routine: when the right
sketch keeps the matrix rank and the left sketch keeps the sampled right rank, it recovers
the matrix exactly from its q+p two-sided query responses. -/
theorem run_generalizedNystromQueryAlgorithm_eq_self_of_rank_eq {A : Matrix m n 𝕜}
    {Ω : Matrix n (Fin q) 𝕜} {Ψ : Matrix m (Fin p) 𝕜}
    (hΩ : (A * Ω).rank = A.rank) (hΨ : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) :
    (generalizedNystromQueryAlgorithm Ω Ψ).run (twoSidedMulVec A) = A := by
  rw [run_generalizedNystromQueryAlgorithm]
  exact generalizedNystrom_eq_self_of_rank_eq hΩ hΨ

end NLAlib
