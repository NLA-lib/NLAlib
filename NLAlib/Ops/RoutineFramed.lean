/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.RoutineProblem

/-!
# Routine certificates retaining their spatial frame

The ordinary routine specification states its reported outputs. Dense factorizations also
promise retention of their source and all buffer extents. The framed specification keeps the
actual off-output frame in the certificate's postcondition, so both promises follow from the
same counted execution. The construction below uses the existing routine judgment and its
frame; it changes no operation, evaluator or reference execution rule.

The caller supplies a size-only scratch bound and a closed work bound. The scratch inequality
is proved against the fixed program's resource analysis, and the work inequality against its
kernel-computed instruction polynomial. Caller storage is added exactly once from the domain.

## Main results

* `NLAlib.Ops.Routine.framedSpecification`: reported outputs and full spatial retention.
* `NLAlib.Ops.Routine.Domain.certifyFramed`: derive this certificate from a routine judgment.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type} {r b : ℕ}

/-- The routine's ordinary output guarantee together with its actual off-output frame. Work
and span use `work`; additional scratch uses `scratch`, and memory includes `bytes` once. -/
noncomputable def Routine.framedSpecification (R : Routine Op Tst) {P : Problem K r b}
    (Sp : (d : Fin r → ℕ) → P.Input d → Routine.Spec K)
    (W : ResourceModel Op Tst) (input : (d : Fin r → ℕ) → P.Input d → List (List K))
    (bytes work scratch : (Fin r → ℕ) → ℕ) : Specification Op Tst P :=
  { R.specification Sp W input bytes work with
    scratch := scratch
    memory := fun d => bytes d + scratch d
    good := fun d X τ c m' =>
      (R.specification Sp W input bytes work).good d X τ c m' ∧
        (P.initial d X).store.EqOff
          (Fp.blocks (R.writeArgs (slots b)) (R.writeLens (List.ofFn d))) m'.store }

/-- A routine judgment proves its reported postcondition and spatial frame at every admitted
input. The work comes from the fixed tree's instruction polynomial, and `hspace` proves the
additional scratch allowance. No successful-run hypothesis is supplied by the caller. -/
noncomputable def Routine.Domain.certifyFramed {R : Routine Op Tst}
    (D : R.Domain K r b) {M : AccessModel Op Tst D.problem}
    (Sp : (d : Fin r → ℕ) → D.In d → Routine.Spec K)
    (work scratch : (Fin r → ℕ) → ℕ)
    (hmeets : ∀ d, D.valid d → ∀ (X : D.problem.Input d) (I : Interp Op Tst K),
      M.contracts d X I → R.Meets I (Sp d X.val.1))
    (hpre : ∀ d, D.valid d → ∀ x, D.accepts d x → ∀ τ : Tape K,
      (Sp d x).pre (List.ofFn d) τ (D.blocks d x))
    (hspace : ∀ d, D.valid d → staticPeak M.resources (R.close r b) d ≤ scratch d)
    (hop : ∀ o d, M.resources.operationWork o d ≤ 1)
    (hcore : ∀ k d, M.resources.coreWork k d ≤ 1)
    (hq : ∀ q d, M.resources.queryWork q d ≤ 1)
    (hwork : ∀ d, D.valid d → CountPoly.eval (List.ofFn d) (R.close r b).countPoly ≤ work d)
    (ht : (R.close r b).wellTyped M.resources D.problem.formats = true := by rfl)
    (hfit : R.bindsFit b = true := by rfl) (hflat : R.flat = true := by rfl)
    (hcontig : R.contiguous = true := by rfl) :
    Algorithm M (R.framedSpecification (P := D.problem) (fun d X => Sp d X.val.1)
      M.resources (fun d X => D.blocks d X.val.1) D.bytes work scratch) := by
  let manifest := R.manifest (P := D.problem) (fun d X => Sp d X.val.1)
    M.resources (fun d X => D.blocks d X.val.1) D.bytes
  let S : Specification Op Tst D.problem :=
    { manifest with
      scratch := scratch
      memory := fun d => D.bytes d + scratch d
      good := fun d X τ c m' => manifest.good d X τ c m' ∧
        (D.problem.initial d X).store.EqOff
          (Fp.blocks (R.writeArgs (slots b)) (R.writeLens (List.ofFn d))) m'.store }
  let A : Algorithm M S := D.algorithm Sp hmeets hpre
    (fun _ _ _ _ _ hfr hpos ys hys hpost _ _ => ⟨⟨hpos, ys, hys, hpost⟩, hfr⟩)
    (fun _ _ => le_rfl) hspace (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ X => by rw [D.initialBytes_eq X]; exact le_rfl) ht hfit hflat hcontig
  exact A.withCountPoly hop hcore hq work (by
    intro d hd
    change CountPoly.eval (List.ofFn d) (R.close r b).countPoly ≤ work d
    exact hwork d hd)

end NLAlib.Ops
