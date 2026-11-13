/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.StoredWords

/-!
# Fixed stored dense Lanczos programs

Both programs declare four raw buffers: matrix entries, right-hand side, basis capacity and
coefficient capacity. Every matrix application is a scalar dense leaf. The program is fixed
before matrix dimension, iteration cap and raw input words; its remaining vector names are
those of the explicitly chosen exact BLAS operation model.

## Main results

* `NLAlib.Krylov.Lanczos.Stored.program`: the fixed ordinary stored-matrix tree.
* `NLAlib.Krylov.Lanczos.Stored.Reorth.program`: the fixed reorthogonalized tree.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Stored

open Ops

/-- The fixed ordinary tree declares the dense matrix as its first raw input buffer. -/
def program : Program RCLikeBlas.Operation CmpTst 2 4 :=
  ⟨(solve (Op := Standard.Operation) (Tst := CmpTst)).linkContext 1 2
    (ContextLinear.table 1 0)⟩

/-- The canonical four-buffer environment forwards matrix data to every procedure. -/
theorem environment_eq (d : Fin 2 → ℕ) :
    Program.environment (b := 4) d =
      (Env.frame [d 0, d 1] [(1, 0), (2, 0), (3, 0)]).withContext [(0, 0)] 2 := by
  rfl

namespace Reorth

/-- The fixed two-pass reorthogonalized tree uses the identical declared matrix layout. -/
def program : Program RCLikeBlas.Operation CmpTst 2 4 :=
  ⟨(Lanczos.Reorth.solve (Op := Standard.Operation) (Tst := CmpTst)).linkContext 1 2
    (ContextLinear.table 1 0)⟩

end Reorth
end NLAlib.Krylov.Lanczos.Stored
