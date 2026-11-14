/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.MGS.Certification
public import NLAlib.Ops.Confined

/-!
# The modified Gram–Schmidt model is confined and uniform

The exact scalar and vector model of the MGS certificate
(`NLAlib.MGS.Certification.model`) has no oracle: its contracts are in operand form and do not
depend on the input. With unit costing every instruction is charged.

## Main results

* `NLAlib.MGS.Certification.confined_model`, `NLAlib.MGS.Certification.uniform_model`: the
  model is confined and uniform.
-/

@[expose] public section

namespace NLAlib.MGS.Certification

open Ops

variable {𝕜 : Type} [RCLike 𝕜]

/-- **The MGS model is confined.** -/
instance confined_model (cost : Standard.Costing) : (model (𝕜 := 𝕜) cost).Confined :=
  ⟨fun _ _ _ => BlockRel.confined_spec _ _, fun _ _ c =>
    ⟨fun _ => c.lens,
      fun _ _ blocks result => ∀ xs, blocks = some xs → result = some (c.fn RCLike.re xs),
      fun _ _ result => result = none, fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩⟩

/-- **The MGS model is uniform.** -/
instance uniform_model (cost : Standard.Costing) : (model (𝕜 := 𝕜) cost).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- With unit costing every scalar call, vector call, comparison and structural instruction of
the MGS model is charged. -/
instance charged_model_unit : (model (𝕜 := 𝕜) .unit).Charged :=
  ⟨fun o _ => by cases o <;> exact Nat.one_pos, fun _ _ => Nat.one_pos, fun _ _ => Nat.one_pos⟩

end NLAlib.MGS.Certification
