/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Functional
public import NLAlib.Ops.Catalog.RCLikeBlas
public import NLAlib.Ops.Profiles.Standard

/-!
# Exact scalar and level-one operation model

The standardized collection contains only scalar and vector operations, with explicit
spatial admissions for the scalar implementations of BLAS. There is no operator primitive
or hidden matrix data in the signature. The complete local-function assignment generates
all contracts and a joint reference realization for any supplied raw-input problem.

## Main results

* `NLAlib.Ops.ExactBlas.model` generates the exact scalar/vector operation model.
* `NLAlib.Ops.ExactBlas.laws` extracts its local arithmetic and comparison laws.
-/

@[expose] public section

namespace NLAlib.Ops.ExactBlas

/-- Scalar calls permit alias; vector calls use the documented reduction and map admissions. -/
def admissible : RCLikeBlas.Operation → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop
  | .inl _ => AnyOperands
  | .inr o => RCLikeBlas.admissible o

/-- Unit scalar work and the chosen length-dependent vector work, including unit costs
for all canonical structural instructions and comparisons. Primitive scratch is zero. -/
def resources (cost : Standard.Costing) : ResourceModel RCLikeBlas.Operation CmpTst :=
  Functional.cellResources
    (fun o => Standard.signature (Sum.elim Standard.Operation.scalar Standard.Operation.blas o))
    (fun o d => Sum.elim (fun _ => 1) (fun b => cost.blasWork b d) o) (fun _ _ => 0)

/-- Generate exact local scalar/vector functions and their joint realization. An entry
occupies one abstract cell; this model asserts neither a finite encoding nor physical timing. -/
noncomputable def model {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜] {r b : ℕ}
    (P : Problem 𝕜 r b) (cost : Standard.Costing) :
    AccessModel RCLikeBlas.Operation CmpTst P :=
  Functional.modelWithAdm P RCLike.re (fun _ _ => RCLikeBlas.operationFunctions)
    admissible (resources cost)

/-- Every interpretation of the model satisfies all exact scalar/vector contracts and
real-part comparisons. These assumptions concern individual declared operands only. -/
theorem laws {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜] {r b : ℕ}
    {P : Problem 𝕜 r b} {cost : Standard.Costing} {d : Fin r → ℕ} {x : P.Input d}
    {I : Interp RCLikeBlas.Operation CmpTst 𝕜}
    (h : (model P cost).contracts d x I) :
    IsScalar RCLikeBlas.machine I ∧ RCLikeBlas.IsExact I ∧ IsCmp RCLike.re I :=
  ⟨fun o => Functional.isFnWithAdm h (.inl o),
    fun o => Functional.isFnWithAdm h (.inr o), Functional.isCmpWithAdm h⟩

end NLAlib.Ops.ExactBlas
