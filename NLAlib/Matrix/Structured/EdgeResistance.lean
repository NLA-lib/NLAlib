/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Pseudoinverse.Pinv
public import NLAlib.Matrix.Subspaces.Leverage

/-!
# Effective resistance and leverage in a weighted graph

An oriented edge record supplies a row of the incidence matrix. Distinct records can
have the same endpoints. The graph may have isolated vertices or no edges.

## Main results

* `NLAlib.GraphEdgeOrientation.mul_edgeResistance_eq_leverageScore`: the weighted effective
  resistance of an edge is its leverage score.
* `NLAlib.GraphEdgeOrientation.sum_mul_edgeResistance`: Foster's identity.
* `NLAlib.GraphEdgeOrientation.rank_weightedLaplacian_add`: the Laplacian rank counts
  vertices minus components when all weights are positive.
-/

@[expose] public section

open Matrix
open scoped Matrix

namespace NLAlib

/-- Endpoints of oriented edge records covering the adjacencies of an undirected graph.
Parallel records are permitted. [SpielmanSrivastava2011, §2]. -/
structure GraphEdgeOrientation {V : Type*} (G : SimpleGraph V) (E : Type*) where
  /-- Source vertex of an edge record. -/
  source : E → V
  /-- Target vertex of an edge record. -/
  target : E → V
  /-- Every record connects adjacent vertices. -/
  adjacent : ∀ e, G.Adj (source e) (target e)
  /-- Every adjacency has a record in one of its two orders. -/
  covers : ∀ {u v}, G.Adj u v → ∃ e,
    (source e = u ∧ target e = v) ∨ (source e = v ∧ target e = u)

namespace GraphEdgeOrientation

variable {V E : Type*} {G : SimpleGraph V} (o : GraphEdgeOrientation G E) [DecidableEq V]

/-- The signed incidence matrix, with one row per edge record. [SpielmanSrivastava2011, §2]. -/
def incidence : Matrix E V ℝ := fun e v =>
  (if o.source e = v then 1 else 0) - (if o.target e = v then 1 else 0)

/-- Incidence matrix with each row scaled by the square root of its edge weight.
[SpielmanSrivastava2011, §2]. -/
noncomputable def weightedIncidence (w : E → ℝ) : Matrix E V ℝ :=
  fun e v => √(w e) * o.incidence e v

variable [Fintype V]

/-- Applying the weighted incidence matrix computes weighted endpoint differences.
[SpielmanSrivastava2011, §2]. -/
theorem weightedIncidence_mulVec (w : E → ℝ) (x : V → ℝ) (e : E) :
    (o.weightedIncidence w *ᵥ x) e = √(w e) * (x (o.source e) - x (o.target e)) := by
  simp [weightedIncidence, incidence, Matrix.mulVec, dotProduct, mul_assoc, ← Finset.mul_sum,
    sub_mul, Finset.sum_sub_distrib]

/-- The kernel of a positively weighted incidence matrix consists of the signals constant
along each adjacency. [SpielmanSrivastava2011, §2]. -/
theorem weightedIncidence_mulVec_eq_zero_iff {w : E → ℝ} (hw : ∀ e, 0 < w e) (x : V → ℝ) :
    o.weightedIncidence w *ᵥ x = 0 ↔ ∀ u v, G.Adj u v → x u = x v := by
  constructor
  · intro hx u v huv
    obtain ⟨e, he | he⟩ := o.covers huv
    all_goals
      have hz := congrFun hx e
      rw [o.weightedIncidence_mulVec] at hz
      have hdiff := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (Real.sqrt_pos.mpr (hw e)).ne')
    · simpa only [he.1, he.2] using hdiff
    · simpa only [he.1, he.2] using hdiff.symm
  · intro h
    funext e
    rw [o.weightedIncidence_mulVec, h _ _ (o.adjacent e), sub_self, mul_zero]
    rfl

variable [Fintype E]

/-- The Gram matrix of the weighted incidence matrix on vertices.
[SpielmanSrivastava2011, §2]. -/
noncomputable def weightedLaplacian (w : E → ℝ) : Matrix V V ℝ :=
  (o.weightedIncidence w)ᴴ * o.weightedIncidence w

/-- Effective resistance between the endpoints of a given edge record, computed with the
Laplacian pseudoinverse and the signed incidence vector. [SpielmanSrivastava2011, §2]. -/
noncomputable def edgeResistance (w : E → ℝ) (e : E) : ℝ :=
  quadForm (pinv (o.weightedLaplacian w)) (o.incidence e)

/-- **Edge resistance and leverage.** For a nonnegatively weighted edge, its weight times
its effective resistance equals the leverage score of its row of the weighted incidence
matrix. [SpielmanSrivastava2011, Lemma 3], allowing disconnected graphs.
Result: laplacian-resistance-leverage -/
theorem mul_edgeResistance_eq_leverageScore (w : E → ℝ) (e : E) (he : 0 ≤ w e) :
    w e * o.edgeResistance w e = leverageScore (o.weightedIncidence w) e := by
  classical
  let C := o.weightedIncidence w
  change _ = rangeProjector C e e
  rw [← mul_pinv_conjTranspose_mul_self_mul_conjTranspose C]
  have hd : (C * pinv (Cᴴ * C) * Cᴴ) e e = quadForm (pinv (Cᴴ * C)) (C e) := by
    rw [quadForm, star_trivial, Matrix.dotProduct_mulVec]
    rfl
  rw [hd, show C e = √(w e) • o.incidence e from rfl, quadForm_smul_right,
    star_trivial, ← pow_two, Real.sq_sqrt he]
  rfl

/-- **Foster's identity.** For a finite graph with nonnegative weights the sum of the
weighted edge resistances equals the rank of the weighted Laplacian.
[SpielmanSrivastava2011, Lemma 3], allowing zero weights and disconnected graphs.
Result: foster-theorem -/
theorem sum_mul_edgeResistance {w : E → ℝ} (hw : ∀ e, 0 ≤ w e) :
    ∑ e, w e * o.edgeResistance w e = ((o.weightedLaplacian w).rank : ℝ) := by
  classical
  simp_rw [o.mul_edgeResistance_eq_leverageScore w _ (hw _)]
  rw [sum_leverageScore, weightedLaplacian, Matrix.rank_conjTranspose_mul_self]

/-- **Weighted Laplacian rank.** For positive weights the rank plus the number of connected
components equals the number of vertices, including isolated vertices.
[SpielmanSrivastava2011, §2], extended componentwise.
Result: weighted-laplacian-rank -/
theorem rank_weightedLaplacian_add {w : E → ℝ} (hw : ∀ e, 0 < w e) :
    (o.weightedLaplacian w).rank + Nat.card G.ConnectedComponent = Fintype.card V := by
  classical
  let C := o.weightedIncidence w
  have hker : C.mulVecLin.ker = (G.lapMatrix ℝ).toLin'.ker := by
    ext x
    change C *ᵥ x = 0 ↔ G.lapMatrix ℝ *ᵥ x = 0
    rw [o.weightedIncidence_mulVec_eq_zero_iff hw, G.lapMatrix_mulVec_eq_zero_iff_forall_adj]
  rw [weightedLaplacian, Matrix.rank_conjTranspose_mul_self, Nat.card_eq_fintype_card,
    G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix, ← hker]
  exact C.mulVecLin.finrank_range_add_finrank_ker.trans (Module.finrank_fintype_fun_eq_card ℝ)

end GraphEdgeOrientation
end NLAlib
