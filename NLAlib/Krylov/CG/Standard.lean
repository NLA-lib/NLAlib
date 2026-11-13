/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.Standard

/-!
# Exact consequences of the standard CG operation model

The exact scheme's zero error bounds imply the existing exact scalar, BLAS and matvec
interfaces. These bridges concern local operations, independently of solver execution.

## Main results

* `NLAlib.Krylov.CG.exactModel_of_zero`: zero scalar error is exact arithmetic.
* `NLAlib.Krylov.CG.isExactMatvec_of_zero`: zero normwise error is exact matvec.
-/

@[expose] public section

namespace NLAlib.Krylov.CG

open Ops
open scoped Matrix

/-- Zero relative arithmetic errors identify every operation's exact decoded value. -/
theorem exactModel_of_zero {K : Type} {dec : K → ℝ} {M : Machine K}
    (h : StdModel 0 dec M) : ExactModel dec M where
  lit q := sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using h.lit q))
  add a b := sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using h.add a b))
  sub a b := sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using h.sub a b))
  mul a b := sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using h.mul a b))
  div a b hb := sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using h.div a b hb))
  neg := h.neg
  sqrt a ha := sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using h.sqrt a ha))

/-- The zero normwise matvec contract implies the existing exact relation on the same calls. -/
theorem isExactMatvec_of_zero {K Op Tst : Type} [Inhabited K] [Has OperatorOp Op]
    {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {I : Interp Op Tst K}
    (h : IsMatvec dec A 0 I) : IsExactMatvec dec A I := by
  refine Interp.Meets.mono h (fun _ _ _ _ _ hp => hp) ?_
  rintro d ins outs τ μ μ' _ ⟨xs, hr, hz, ys, hlen, hrel, rfl⟩
  refine ⟨xs, hr, hz, ys, hlen, ?_, rfl⟩
  cases xs with
  | nil => simp [matvecErrorRel] at hrel
  | cons x xs => cases xs with
    | cons _ _ => simp [matvecErrorRel] at hrel
    | nil => cases ys with
      | nil => simp [matvecErrorRel] at hrel
      | cons y ys => cases ys with
        | cons _ _ => simp [matvecErrorRel] at hrel
        | nil =>
          have he : WithLp.toLp 2 (A *ᵥ decv dec n x - decv dec m y) = 0 :=
            norm_eq_zero.mp (le_antisymm (by simpa [matvecErrorRel] using hrel) (norm_nonneg _))
          exact (sub_eq_zero.mp ((WithLp.toLp_eq_zero 2).mp he)).symm

/-- The exact standard scheme supplies the complete existing exact scalar, BLAS, operator
and comparison interfaces from its declared contracts, without listing primitives per solver. -/
theorem exact_laws {K : Type} [Inhabited K] {r b : ℕ} {P : Problem K r b}
    {n : (Fin r → ℕ) → ℕ} (model : Standard.Model P n) (hExact : model.scheme = .exact)
    {d : Fin r → ℕ} {x : P.Input d} {I : Interp Standard.Operation CmpTst K}
    (hI : model.access.contracts d x I) :
    IsScalar model.machine I ∧ ExactModel model.decode model.machine ∧
      IsExactBlas1 model.decode (fun _ => True) I ∧
      IsExactMatvec model.decode (model.matrix d x) I ∧ IsCmp model.decode I := by
  obtain ⟨hS, hB, hA, hC⟩ := model.laws hI
  have hs : Blas.seqSumErr 0 = fun _ => 0 := by
    funext j
    simp [Blas.seqSumErr]
  have hok : Standard.Scheme.exact.admits = fun _ => True := rfl
  refine ⟨hS, exactModel_of_zero (M := model.machine) (dec := model.decode) ?_,
    IsBlas1.toExact ?_, isExactMatvec_of_zero ?_, hC⟩
  · simpa [hExact, Standard.Scheme.roundoff] using model.scalar
  · simpa [hExact, Standard.Scheme.errors, Standard.Scheme.roundoff,
      Blas.seq.err, Blas.level1Err, hs, hok] using hB
  · simpa [hExact, Standard.Scheme.roundoff] using hA

end NLAlib.Krylov.CG
