/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyRoundingState
public import NLAlib.Computation.MatrixStorage

/-!
# Recovering the actual rounded Cholesky output

The completed stored invariant supplies the actual output words, exact triangular zeros,
positive diagonal and entrywise error. Releasing residual scratch leaves precisely one full
factor-block write in the original store. Word carriers need no algebraic structure.

## Main results

* `NLAlib.Computation.CholeskyRounding.State.writeBlock_pop`: the completed output and its frame.
-/

@[expose] public section

namespace NLAlib.Computation.CholeskyRounding

variable {P K : Type} [DecidableEq P]

/-- Release the residual scratch of a completed rounded Cholesky run and recover the actual
packed output words. Triangular zeros, positive diagonal and the invariant's entrywise error
hold for their decoded matrix. Empty matrices require no valid output handle. -/
theorem State.writeBlock_pop {dec : P → K → ℝ} {u μ B e : ℝ}
    {initial final : Store P K} {p : P} {L lo N : ℕ} {scratch : Array (Option K)}
    {A : Matrix (Fin N) (Fin N) ℝ}
    (hs : State dec u μ B e (initial.push (p, scratch)) p initial.size L lo A N final)
    (hcap : Writable initial p L lo (N * N)) :
    ∃ W : Array K, W.size = N * N ∧
      initial.writeBlock p L lo W = some final.pop ∧
      (unflatten N N (W.map (dec p))).IsLowerTriangular ∧
      (∀ i, 0 < unflatten N N (W.map (dec p)) i i) ∧
      (∀ i j, |unflatten N N (W.map (dec p)) i j - choleskyLower A i j| ≤ e) ∧
      HoldsDecoded final.pop dec p L lo (unflatten N N (W.map (dec p))) := by
  classical
  let M : Matrix (Fin N) (Fin N) K := fun i j => (hs.factor i j j.isLt).choose
  have hM : Holds final p L lo M := fun i j => (hs.factor i j j.isLt).choose_spec.1
  have hprop : ∀ i j : Fin N,
      (i < j → dec p (M i j) = 0) ∧ (i = j → 0 < dec p (M i j)) ∧
      |dec p (M i j) - choleskyLower A i j| ≤ e :=
    fun i j => (hs.factor i j j.isLt).choose_spec.2
  obtain ⟨W, hsize, hread, hcoords, _⟩ := hM.exists_array
  have hcapW : Writable initial p L lo W.size := by rw [hsize]; exact hcap
  obtain ⟨store, hw⟩ := hcapW.exists_writeBlock (y := W)
  obtain ⟨g, hframe⟩ := hs.frame
  have hpop : final.pop = store := hframe.pop_eq hw hsize
    (fun t ht => (hframe.2.2 t ht).symm.trans (hread t ht))
  have hwrite : initial.writeBlock p L lo W = some final.pop := hpop ▸ hw
  have hdecoded : unflatten N N (W.map (dec p)) = fun i j => dec p (M i j) := by
    ext i j
    simp only [unflatten, Matrix.of_apply, Array.getD_eq_getD_getElem?,
      Array.getElem?_map, hcoords, Option.map_some, Option.getD_some]
  refine ⟨W, hsize, hwrite, ?_, ?_, ?_, ?_⟩
  · rw [hdecoded]
    exact fun i j hij => (hprop i j).1 hij
  · intro i
    rw [hdecoded]
    exact (hprop i i).2.1 rfl
  · intro i j
    rw [hdecoded]
    exact (hprop i j).2.2
  · intro i j
    refine ⟨M i j, ?_, ?_⟩
    · simpa only [Nat.add_assoc] using
        (Store.read_of_writeBlock_eq_some_of_lt hwrite
          (by rw [hsize]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)).trans
            (hcoords i j)
    · rw [hdecoded]

end NLAlib.Computation.CholeskyRounding
