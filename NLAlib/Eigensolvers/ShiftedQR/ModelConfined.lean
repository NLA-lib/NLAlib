/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Kernels
public import NLAlib.Ops.Profiles.Confined

/-!
# The shifted QR kernel model is confined and uniform

The model of the shifted QR deflation certificate (`NLAlib.ShiftedQR.model`) has exact scalar
arithmetic and two spectral kernels. Every contract is in operand form and none depends on the
input: a kernel reads the matrix block it is given. The kernel weights are parameters of the
resource model, so the model carries no instance of `NLAlib.Ops.AccessModel.Charged`.

## Main results

* `NLAlib.ShiftedQR.confined_model`, `NLAlib.ShiftedQR.uniform_model`: the model is confined
  and uniform.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- **The shifted QR kernel model is confined.** -/
instance confined_model {r b : ℕ} (P : Problem ℝ r b) {θ : ℝ} (K : KernelRoutines θ)
    (R : ResourceModel Op Tst) : (model P K R).Confined :=
  ⟨fun _ _ _ => BlockRel.confined_spec _ _, fun _ _ q => Dense.confined_queryContract id q⟩

/-- **The shifted QR kernel model is uniform.** -/
instance uniform_model {r b : ℕ} (P : Problem ℝ r b) {θ : ℝ} (K : KernelRoutines θ)
    (R : ResourceModel Op Tst) : (model P K R).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

end NLAlib.ShiftedQR
