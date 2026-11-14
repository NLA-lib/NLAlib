/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Confined
public import NLAlib.Ops.Profiles.Dense
public import NLAlib.Ops.Profiles.ExactLinear
public import NLAlib.Ops.Profiles.ExactScalarLinear
public import NLAlib.Ops.Profiles.RoundedScalarBlas
public import NLAlib.Ops.Profiles.ScalarOnly

/-!
# The standard collections are confined; which are uniform and charged

Every standard collection is confined (`NLAlib.Ops.AccessModel.Confined`): its primitives are in
operand form and its comparisons read their operands. The collections without an operator
oracle are uniform (`NLAlib.Ops.AccessModel.Uniform`). The matrix-free standard model
(`NLAlib.Ops.Standard.Model.access`) is confined and not uniform: its matrix-vector contract is
the declared oracle for the operator of the input.

A collection is charged (`NLAlib.Ops.AccessModel.Charged`) when its weights are fixed and
positive. Collections whose primitive weights are parameters carry no instance: their work
claims depend on the weights a certificate supplies. The length-weighted vector costing has no
instance either, since it charges nothing for an update, scaling or copy of length zero.

## Main results

* `NLAlib.Ops.Functional.confined_modelWithAdm`: generated functional models are confined.
* `NLAlib.Ops.Standard.confined_access`: the matrix-free standard model is confined.
-/

@[expose] public section

namespace NLAlib.Ops

/-- A generated comparison reads exactly its operand blocks. -/
theorem Functional.confined_query {K : Type} (dec : K → ℝ) (c : CmpTst) :
    (Functional.query dec c).Confined :=
  ⟨fun _ => c.lens, fun _ _ blocks result => ∀ xs, blocks = some xs → result = some (c.fn dec xs),
    fun _ _ result => result = none, fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

/-- Generated functional models are confined, whatever functions they are given. -/
instance Functional.confined_modelWithAdm {K Op : Type} [Inhabited K] {r b : ℕ}
    (P : Problem K r b) (dec : K → ℝ)
    (functions : (d : Fin r → ℕ) → P.Input d → Op → BlockFn K)
    (admissible : Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop)
    (resources : ResourceModel Op CmpTst) :
    (Functional.modelWithAdm P dec functions admissible resources).Confined :=
  ⟨fun _ _ _ => BlockRel.confined_spec _ _, fun _ _ c => Functional.confined_query dec c⟩

/-- Generated functional models with unrestricted operands are confined. -/
instance Functional.confined_model {K Op : Type} [Inhabited K] {r b : ℕ}
    (P : Problem K r b) (dec : K → ℝ)
    (functions : (d : Fin r → ℕ) → P.Input d → Op → BlockFn K)
    (resources : ResourceModel Op CmpTst) :
    (Functional.model P dec functions resources).Confined :=
  Functional.confined_modelWithAdm P dec functions _ resources

/-- A generated functional model whose functions ignore the sizes and the input is uniform. -/
instance Functional.uniform_modelWithAdm {K Op : Type} [Inhabited K] {r b : ℕ}
    (P : Problem K r b) (dec : K → ℝ) (functions : Op → BlockFn K)
    (admissible : Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop)
    (resources : ResourceModel Op CmpTst) :
    (Functional.modelWithAdm P dec (fun _ _ => functions) admissible resources).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- The same, with unrestricted operands. -/
instance Functional.uniform_model {K Op : Type} [Inhabited K] {r b : ℕ}
    (P : Problem K r b) (dec : K → ℝ) (functions : Op → BlockFn K)
    (resources : ResourceModel Op CmpTst) :
    (Functional.model P dec (fun _ _ => functions) resources).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-! ### Exact scalar and vector collection -/

instance ExactBlas.confined_model {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜] {r b : ℕ}
    (P : Problem 𝕜 r b) (cost : Standard.Costing) : (ExactBlas.model P cost).Confined :=
  Functional.confined_modelWithAdm ..

instance ExactBlas.uniform_model {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜] {r b : ℕ}
    (P : Problem 𝕜 r b) (cost : Standard.Costing) : (ExactBlas.model P cost).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- Unit costing charges every scalar and vector call. -/
instance ExactBlas.charged_model_unit {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜] {r b : ℕ}
    (P : Problem 𝕜 r b) : (ExactBlas.model P .unit).Charged :=
  ⟨fun o _ => by cases o <;> exact Nat.one_pos, fun _ _ => Nat.one_pos, fun _ _ => Nat.one_pos⟩

/-! ### Exact collections with stored operators, and the scalar-only collection -/

instance ExactLinear.confined_model {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜] {r b : ℕ}
    (P : Problem 𝕜 r b) (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜)
    (work workspace : ExactLinear.Operation → List ℕ → ℕ) :
    (ExactLinear.model P dataLength matrix work workspace).Confined :=
  Functional.confined_modelWithAdm ..

instance ExactLinear.uniform_model {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜] {r b : ℕ}
    (P : Problem 𝕜 r b) (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜)
    (work workspace : ExactLinear.Operation → List ℕ → ℕ) :
    (ExactLinear.model P dataLength matrix work workspace).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

instance ExactScalarLinear.confined_model {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜] {r b : ℕ}
    (P : Problem 𝕜 r b) (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜)
    (work workspace : ExactScalarLinear.Operation → List ℕ → ℕ) :
    (ExactScalarLinear.model P dataLength matrix work workspace).Confined :=
  Functional.confined_modelWithAdm ..

instance ExactScalarLinear.uniform_model {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜] {r b : ℕ}
    (P : Problem 𝕜 r b) (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜)
    (work workspace : ExactScalarLinear.Operation → List ℕ → ℕ) :
    (ExactScalarLinear.model P dataLength matrix work workspace).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

instance ScalarOnly.confined_model {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜] {r b : ℕ}
    (P : Problem 𝕜 r b) (work workspace : ScalarOnly.Operation → List ℕ → ℕ) :
    (ScalarOnly.model P work workspace).Confined :=
  Functional.confined_modelWithAdm ..

instance ScalarOnly.uniform_model {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜] {r b : ℕ}
    (P : Problem 𝕜 r b) (work workspace : ScalarOnly.Operation → List ℕ → ℕ) :
    (ScalarOnly.model P work workspace).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-! ### Rounded collections -/

/-- The rounded sequential vector contracts are in operand form. -/
theorem Standard.confined_blasContract {K : Type} [Inhabited K] (dec : K → ℝ) (e : Blas1Err)
    (ok : ℕ → Prop) (o : Blas1Op) : (Standard.blasContract dec e ok o).Confined := by
  cases o <;> exact BlockRel.confined_spec _ _

instance RoundedBlas.confined_model {r b : ℕ} (P : Problem ℝ r b) (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (cost : Standard.Costing) :
    (RoundedBlas.model P M u hM hu cost).Confined :=
  ⟨fun _ _ o => by
    cases o with
    | inl a => exact BlockRel.confined_spec _ _
    | inr a => exact Standard.confined_blasContract ..,
    fun _ _ c => Functional.confined_query id c⟩

instance RoundedBlas.uniform_model {r b : ℕ} (P : Problem ℝ r b) (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (cost : Standard.Costing) :
    (RoundedBlas.model P M u hM hu cost).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

instance RoundedBlas.charged_model_unit {r b : ℕ} (P : Problem ℝ r b) (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) : (RoundedBlas.model P M u hM hu .unit).Charged :=
  ⟨fun o _ => by cases o <;> exact Nat.one_pos, fun _ _ => Nat.one_pos, fun _ _ => Nat.one_pos⟩

instance RoundedScalarBlas.confined_model {r b : ℕ} (P : Problem ℝ r b) (M : Machine ℝ) :
    (RoundedScalarBlas.model P M).Confined :=
  Functional.confined_modelWithAdm ..

instance RoundedScalarBlas.uniform_model {r b : ℕ} (P : Problem ℝ r b) (M : Machine ℝ) :
    (RoundedScalarBlas.model P M).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

instance RoundedScalarBlas.charged_model {r b : ℕ} (P : Problem ℝ r b) (M : Machine ℝ) :
    (RoundedScalarBlas.model P M).Charged :=
  ⟨fun _ _ => Nat.one_pos, fun _ _ => Nat.one_pos, fun _ _ => Nat.one_pos⟩

/-! ### The dense collection -/

/-- Dense comparisons and the floor query read exactly their operand blocks. -/
theorem Dense.confined_queryContract {K : Type} (dec : K → ℝ) (q : CmpTst ⊕ IdxTst) :
    (Dense.queryContract dec q).Confined := by
  rcases q with c | ⟨⟩
  · exact ⟨fun _ => c.lens,
      fun _ _ blocks result => ∀ xs, blocks = some xs → result = some (c.fn dec xs),
      fun _ _ result => result = none, fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩
  · exact ⟨fun _ => [], fun _ _ _ result => result = none,
      fun _ blocks result => ∀ xs, blocks = some xs → result = toNatFn dec xs.flatten,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

instance Dense.confined_functionalModel {K E : Type} [Inhabited K] {r b : ℕ}
    (P : Problem K r b) (M : Machine K) (dec : K → ℝ) (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E)
    (R : ResourceModel DenseOp (CmpTst ⊕ IdxTst)) :
    (Dense.functionalModel P M dec C mm qr R).Confined :=
  ⟨fun _ _ _ => BlockRel.confined_spec _ _, fun _ _ q => Dense.confined_queryContract dec q⟩

instance Dense.uniform_functionalModel {K E : Type} [Inhabited K] {r b : ℕ}
    (P : Problem K r b) (M : Machine K) (dec : K → ℝ) (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E)
    (R : ResourceModel DenseOp (CmpTst ⊕ IdxTst)) :
    (Dense.functionalModel P M dec C mm qr R).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-! ### The matrix-free standard model: confined, with a declared operator oracle -/

/-- **The matrix-free standard model is confined.** It is not uniform: the matrix-vector
contract names the operator of the input. -/
instance Standard.confined_access {K : Type} [Inhabited K] {r b : ℕ} {P : Problem K r b}
    {n : (Fin r → ℕ) → ℕ} (m : Standard.Model P n) : m.access.Confined :=
  ⟨fun d x o => by
    cases o with
    | scalar a => exact BlockRel.confined_spec _ _
    | blas a => exact Standard.confined_blasContract ..
    | matvec => exact BlockRel.confined_spec _ _,
    fun _ _ c => Functional.confined_query m.decode c⟩

end NLAlib.Ops
