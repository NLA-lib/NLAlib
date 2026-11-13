/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.MGS.Certification
public import NLAlib.Ops.Profiles.RCLikeScalar
public import NLAlib.Ops.Catalog.Functional
public import NLAlib.Ops.LinkWorkspace

/-!
# Full scalar certification of rank-revealing MGS

The fixed implementation table expands every vector primitive into scalar field
operations and explicit scalar conjugation. The canonical certificate reuses the checked
MGS algorithm through generic linking; it proves no new factorization theorem. Three
stored scratch cells suffice independently of dimensions and rank.

## Main results

* `NLAlib.MGS.ScalarCertification.algorithm` certifies the actual fully scalar program.
-/

@[expose] public section

namespace NLAlib.MGS.ScalarCertification

open Ops

variable {𝕜 : Type} [RCLike 𝕜]

/-- Zero supplies the default word of the generated scalar model. -/
local instance instInhabitedScalarCertification : Inhabited 𝕜 := ⟨0⟩

/-- Keep scalar calls and implement all six vector names by the fixed scalar BLAS table. -/
def table : Table RCLikeBlas.Operation RCLikeStar.Operation CmpTst
  | .inl o => .inr (.inl o)
  | .inr o => RCLikeScalar.table o

/-- One linked first-order scalar tree, fixed before dimensions and input words. -/
def program : Program RCLikeStar.Operation CmpTst 2 1 :=
  (MGS.program (Op := RCLikeBlas.Operation) (Tst := CmpTst)).link table

/-- Scalar field operations retain their standard cell signatures; conjugation is unary. -/
def signature : RCLikeStar.Operation → OperandSignature
  | .inl o => Standard.signature (.scalar o)
  | .inr _ => ⟨[.cell], [.cell]⟩

/-- Every scalar, comparison and structural instruction is charged. Primitive workspace
is zero; the source program's scoped temporary allocations remain fully counted. -/
def resources (work : RCLikeStar.Operation → List ℕ → ℕ) :
    ResourceModel RCLikeStar.Operation CmpTst :=
  Functional.cellResources signature work (fun _ _ => 0)

/-- The complete exact scalar model is generated from exhaustive local word functions.
There are no BLAS operation names or vector-operation assumptions in its signature. -/
noncomputable def model (work : RCLikeStar.Operation → List ℕ → ℕ) :
    AccessModel RCLikeStar.Operation CmpTst (Certification.problem (𝕜 := 𝕜)) :=
  Functional.model Certification.problem RCLike.re (fun _ _ => RCLikeStar.operationFunctions)
    (resources work)

/-- The generated scalar model induces every local contract of the original MGS model. -/
theorem contracts_link {work : RCLikeStar.Operation → List ℕ → ℕ}
    {d : Fin 2 → ℕ} {x : (Certification.problem (𝕜 := 𝕜)).Input d}
    {I : Interp RCLikeStar.Operation CmpTst 𝕜} (hI : (model work).contracts d x I) :
    (Certification.model .unit).contracts d x (I.link table) := by
  have hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I :=
    fun o => Functional.isFn hI (.inl o)
  have hStar : RCLikeStar.IsExact I := Functional.isFn hI (.inr .conj)
  refine ⟨?_, ?_⟩
  · intro o
    cases o with
    | inl s => exact Interp.link_meets_kept rfl (hS s)
    | inr b =>
      cases b
      · exact Interp.link_meets rfl (RCLikeScalar.meets_sum hS)
      · exact Interp.link_meets rfl (RCLikeScalar.meets_dot hS hStar)
      · exact Interp.link_meets rfl (RCLikeScalar.meets_axpy hS)
      · exact Interp.link_meets rfl (RCLikeScalar.meets_nrm2 hS hStar)
      · exact Interp.link_meets rfl (RCLikeScalar.meets_scal hS)
      · exact Interp.link_meets rfl (RCLikeScalar.meets_copy hS)
  · intro q
    exact hI.2 q

/-- Three stored scalar cells bound the complete linked program: the two MGS cells and
one reused scalar-kernel temporary. This is independent of the instruction manifest. -/
theorem staticPeak_program (work : RCLikeStar.Operation → List ℕ → ℕ) (d : Fin 2 → ℕ) :
    staticPeak (resources work) program d ≤ 3 := by
  rw [staticPeak_eq, (resources work).queryReserve_of_zero (fun _ _ => rfl), Nat.add_zero]
  have hb : ∀ o r, table o = .inl r → ∀ idx,
      stmtPeak (fun _ _ => 0) r.body idx ≤ 1 := by
    intro o r hr idx
    cases o with
    | inl s => simp [table] at hr
    | inr b =>
      have h := RCLikeScalar.table_peak_zero (Op := RCLikeStar.Operation) (Tst := CmpTst) b idx
      change RCLikeScalar.table b = .inl r at hr
      simpa only [hr] using h
  have h := stmtPeak_link_le_zero_add table 1 hb
    (MGS.program (Op := RCLikeBlas.Operation) (Tst := CmpTst)).body
    (Program.environment (b := 1) d).idx
  have hz := Certification.staticPeak_program .unit d
  rw [staticPeak_eq, (Certification.resources .unit).queryReserve_of_zero (fun _ _ => rfl),
    Nat.add_zero] at hz
  change stmtPeak (fun (_ : RCLikeBlas.Operation) _ => 0)
    (MGS.program (Op := RCLikeBlas.Operation) (Tst := CmpTst)).body
    (Program.environment (b := 1) d).idx = 2 at hz
  change stmtPeak (fun (_ : RCLikeStar.Operation) _ => 0)
    ((MGS.program (Op := RCLikeBlas.Operation) (Tst := CmpTst)).body.link table)
    (Program.environment (b := 1) d).idx ≤ 3
  simpa only [hz] using h

/-- The full scalar instrumented tree determines the complete size-only instruction budget. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (RCLikeStar.Operation ⊕ Bookkeeping) CmpTst := staticCost program d

/-- Mathematical output is unchanged by lowering; work, span, counts and memory refer to the
same scalar run. The storage bound uses three cells above the supplied matrix. -/
noncomputable def specification (work : RCLikeStar.Operation → List ℕ → ℕ) :
    Specification RCLikeStar.Operation CmpTst (Certification.problem (𝕜 := 𝕜)) where
  budget := staticBudget
  scratch _ := 3
  work d := (resources work).work (staticBudget d)
  span d := (resources work).span (staticBudget d)
  memory d := d 1 * d 0 + 3
  good d x τ _ m := (Certification.specification .unit).good d x τ 0 m

/-- Every raw matrix has a total fully scalar MGS execution at every rank. The certificate
includes actual scalar/conjugation instructions, cleanup, full accounting and constant scratch. -/
noncomputable def algorithm (work : RCLikeStar.Operation → List ℕ → ℕ) :
    Algorithm (model (𝕜 := 𝕜) work) (specification work) := by
  refine (Certification.algorithm (𝕜 := 𝕜) .unit).link table (model work) (specification work)
    (by rfl) (fun _ _ _ _ h => contracts_link h) (fun _ _ _ _ _ _ _ hg _ _ => hg)
    (fun _ _ => le_rfl) (fun d _ => staticPeak_program work d)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  intro d _ x
  rw [Certification.initialBytes_problem]
  exact le_rfl

end NLAlib.MGS.ScalarCertification
