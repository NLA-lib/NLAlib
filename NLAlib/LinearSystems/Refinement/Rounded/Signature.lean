/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Tagged

/-!
# The operations of iterative refinement in three precisions

Scalar arithmetic at three precision tags (the factorization, the working and the residual
precision) and the four casts that the program uses: working to factorization and back, working
to residual and back. The signature is closed: it has no other operation.

## Main definitions

* `NLAlib.LinearSystems.Refinement.Rounded.FTag`, `NLAlib.LinearSystems.Refinement.Rounded.WTag`,
  `NLAlib.LinearSystems.Refinement.Rounded.RTag`: the three precision tags.
* `NLAlib.LinearSystems.Refinement.Rounded.Signature`: the closed signature.

## Main results

* `NLAlib.LinearSystems.Refinement.Rounded.Signature.fn`: the block function of each operation.
-/

@[expose] public section

namespace NLAlib.LinearSystems.Refinement.Rounded

open Ops

/-- The tag of the factorization precision. -/
inductive FTag
/-- The tag of the working precision. -/
inductive WTag
/-- The tag of the residual precision. -/
inductive RTag

/-- **The closed signature of three-precision refinement**: scalar arithmetic at each of the
three tags, and the casts working to factorization, factorization to working, working to
residual and residual to working. -/
inductive Signature where
  /-- Scalar arithmetic at the factorization precision. -/
  | f (a : ScalarOp)
  /-- Scalar arithmetic at the working precision. -/
  | w (a : ScalarOp)
  /-- Scalar arithmetic at the residual precision. -/
  | r (a : ScalarOp)
  /-- The cast from the working to the factorization precision. -/
  | castWF
  /-- The cast from the factorization to the working precision. -/
  | castFW
  /-- The cast from the working to the residual precision. -/
  | castWR
  /-- The cast from the residual to the working precision. -/
  | castRW
  deriving DecidableEq

instance : Has (Tagged FTag ScalarOp) Signature where
  inj t := .f t.op
  proj
    | .f a => some ⟨a⟩
    | _ => none
  proj_inj _ := rfl
  inj_of_proj o g h := by cases o <;> first | cases h; rfl | cases h

instance : Has (Tagged WTag ScalarOp) Signature where
  inj t := .w t.op
  proj
    | .w a => some ⟨a⟩
    | _ => none
  proj_inj _ := rfl
  inj_of_proj o g h := by cases o <;> first | cases h; rfl | cases h

instance : Has (Tagged RTag ScalarOp) Signature where
  inj t := .r t.op
  proj
    | .r a => some ⟨a⟩
    | _ => none
  proj_inj _ := rfl
  inj_of_proj o g h := by cases o <;> first | cases h; rfl | cases h

instance : Has (CastOp WTag FTag) Signature where
  inj _ := .castWF
  proj
    | .castWF => some .cast
    | _ => none
  proj_inj c := by cases c; rfl
  inj_of_proj o g h := by cases o <;> first | (cases g; rfl) | cases h

instance : Has (CastOp FTag WTag) Signature where
  inj _ := .castFW
  proj
    | .castFW => some .cast
    | _ => none
  proj_inj c := by cases c; rfl
  inj_of_proj o g h := by cases o <;> first | (cases g; rfl) | cases h

instance : Has (CastOp WTag RTag) Signature where
  inj _ := .castWR
  proj
    | .castWR => some .cast
    | _ => none
  proj_inj c := by cases c; rfl
  inj_of_proj o g h := by cases o <;> first | (cases g; rfl) | cases h

instance : Has (CastOp RTag WTag) Signature where
  inj _ := .castRW
  proj
    | .castRW => some .cast
    | _ => none
  proj_inj c := by cases c; rfl
  inj_of_proj o g h := by cases o <;> first | (cases g; rfl) | cases h

instance : Apart (Tagged FTag ScalarOp) (Tagged WTag ScalarOp) Signature := ⟨fun _ => rfl⟩
instance : Apart (Tagged WTag ScalarOp) (Tagged FTag ScalarOp) Signature := ⟨fun _ => rfl⟩
instance : Apart (Tagged FTag ScalarOp) (Tagged RTag ScalarOp) Signature := ⟨fun _ => rfl⟩
instance : Apart (Tagged RTag ScalarOp) (Tagged FTag ScalarOp) Signature := ⟨fun _ => rfl⟩
instance : Apart (Tagged WTag ScalarOp) (Tagged RTag ScalarOp) Signature := ⟨fun _ => rfl⟩
instance : Apart (Tagged RTag ScalarOp) (Tagged WTag ScalarOp) Signature := ⟨fun _ => rfl⟩

/-- The block function of each operation, for the three machines and the four cast functions:
scalar arithmetic at a tag is the machine of the tag, and a cast is its function on one word. -/
noncomputable def Signature.fn {K : Type} (Mf Mw Mr : Machine K) (cWF cFW cWR cRW : K → K) :
    Signature → BlockFn K
  | .f a => Mf.fn a
  | .w a => Mw.fn a
  | .r a => Mr.fn a
  | .castWF => .un fun a => some (cWF a)
  | .castFW => .un fun a => some (cFW a)
  | .castWR => .un fun a => some (cWR a)
  | .castRW => .un fun a => some (cRW a)

end NLAlib.LinearSystems.Refinement.Rounded
