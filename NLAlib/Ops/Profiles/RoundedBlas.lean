/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.ExactBlas

/-!
# Rounded scalar and sequential level-one operation model

The collection declares scalar machine functions and the standard sequential BLAS error
contracts. It contains no matrix-vector primitive or hidden matrix storage. A joint reference
is obtained by executing the proved scalar implementations of every vector operation.

## Main results

* `NLAlib.Ops.RoundedBlas.model`: the jointly realized rounded scalar/vector model.
* `NLAlib.Ops.RoundedBlas.laws`: all declared local numerical and comparison laws.
-/

@[expose] public section

namespace NLAlib.Ops.RoundedBlas

/-- Exhaustive scalar machine functions and reference vector functions. The vector functions
are replaced by the sequential scalar implementation when constructing the joint witness. -/
noncomputable def functions (M : Machine ℝ) : RCLikeBlas.Operation → BlockFn ℝ
  | .inl o => M.fn o
  | .inr o => RCLikeBlas.functions o

/-- Scalar functions and sequential rounded vector contracts, with their ordinary spatial
admission. The signature has no operation that can read an undeclared matrix operand. -/
def operation (M : Machine ℝ) (u : ℝ) : RCLikeBlas.Operation → Contract ℝ
  | .inl o => (M.fn o).rel.spec AnyOperands
  | .inr o => Standard.blasContract id (Blas.seq.err u) (fun _ => True) o

/-- A standard scalar law supplies a joint interpretation of every rounded local contract.
All resource units are abstract cells and declared work weights, independent of an encoding. -/
noncomputable def model {r b : ℕ} (P : Problem ℝ r b)
    (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
    (cost : Standard.Costing) : AccessModel RCLikeBlas.Operation CmpTst P where
  word := 0
  operation _ _ := operation M u
  query _ _ := Functional.query id
  resources := ExactBlas.resources cost
  realize _ _ _ := by
    let base := Functional.interp id (functions M)
    have hs : IsScalar M base := fun o =>
      Interp.ofFns_isFn (Tst := CmpTst) (functions M) .total (.inl o) AnyOperands
    obtain ⟨hS, hB⟩ := (Blas.seq_certifies hM hu (fun _ => True)).meets base hs
    refine ⟨base.link (Blas.seq (Op := RCLikeBlas.Operation) (Tst := CmpTst)).table, ?_, ?_⟩
    · intro o
      cases o with
      | inl a => exact hS a
      | inr a => cases a with
        | sum => exact hB.sum
        | dot => exact hB.dot
        | axpy => exact hB.axpy
        | nrm2 => exact hB.nrm2
        | scal => exact hB.scal
        | copy => exact hB.copy
    · intro q
      exact ⟨(Functional.interp_contracts id (functions M)).2 q, fun _ _ => rfl⟩

/-- Satisfying the declared rounded model supplies precisely the local scalar, sequential
vector and exact comparison contracts used by stored algorithms. -/
theorem laws {r b : ℕ} {P : Problem ℝ r b} {M : Machine ℝ} {u : ℝ}
    {hM : StdModel u id M} {hu : 0 ≤ u} {cost : Standard.Costing}
    {d : Fin r → ℕ} {x : P.Input d} {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (h : (model P M u hM hu cost).contracts d x I) :
    IsScalar M I ∧ IsBlas1 id (Blas.seq.err u) (fun _ => True) I ∧ IsCmp id I := by
  refine ⟨fun o => h.1 (.inl o), ?_, ?_⟩
  · exact ⟨h.1 (.inr .sum), h.1 (.inr .dot), h.1 (.inr .axpy), h.1 (.inr .nrm2),
      h.1 (.inr .scal), h.1 (.inr .copy)⟩
  · intro q d a mem xs hr
    exact (h.2 q).1 d a mem xs hr

end NLAlib.Ops.RoundedBlas
