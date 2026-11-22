/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Rounded.StoredRoutine
public import NLAlib.Krylov.CG.HSPCG.Rounded.Alg
public import NLAlib.Krylov.CG.HSPCG.Rounded.Prefix
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.Profiles.RoundedScalarBlas

/-!
# Canonical rounded stored scalar PCG

The two actual matrix blocks precede the raw right-hand side and four uninitialized vector
capacities. Input admission states spectral windows for the decoded system and inverse
preconditioner. The fixed scalar program initializes zero, performs capped PCG with an actual
pairing stopping cache, and implements both matrix actions through dense scalar row loops.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Certification.problem`: the raw seven-buffer problem.
* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Certification.program`: the complete scalar-only tree.
* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Certification.specification`: physical prefix and complete
  resources.
* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Certification.algorithm`: total rounded scalar PCG
  certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Certification

open Ops
open scoped Matrix

/-- The inputs of the solver: the system matrix, the inverse preconditioner and the right-hand
side. -/
abbrev Inputs (d : Fin 2 → ℕ) : Type :=
  Matrix (Fin (d 0)) (Fin (d 0)) ℝ × Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)

/-- The admitted systems: both matrices are symmetric and have their declared spectral windows.
The right-hand side is unrestricted, including zero. -/
def accepts (lowerA upperA lowerP upperP : (Fin 2 → ℕ) → ℝ) (d : Fin 2 → ℕ)
    (x : Inputs d) : Prop :=
  x.1ᵀ = x.1 ∧ x.2.1ᵀ = x.2.1 ∧ spectrum ℝ x.1 ⊆ Set.Icc (lowerA d) (upperA d) ∧
    spectrum ℝ x.2.1 ⊆ Set.Icc (lowerP d) (upperP d)

variable (lowerA upperA lowerP upperP : (Fin 2 → ℕ) → ℝ)
  (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d → ∃ x : Inputs d, accepts lowerA upperA lowerP upperP d x)

/-- The admitted inputs: at the sizes of `domain`, the two matrices stored column by column and
the right-hand side, satisfying `accepts`; the four state vectors are blank. -/
noncomputable def inputs : zeroStartRoutine.Domain ℝ 2 7 where
  valid := domain
  In := Inputs
  accepts := accepts lowerA upperA lowerP upperP
  slot d := ![.stored (Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)) Prod.fst,
    .stored (Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)) fun x => x.2.1,
    .stored (Codec.vector (d 0)) fun x => x.2.2,
    .blank (d 0), .blank (d 0), .blank (d 0), .blank (d 0)]
  fits := by domain_fits
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Option.some.injEq] at h0 h1 h2
    exact Prod.ext ((Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)).encode_injective h0)
      (Prod.ext ((Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)).encode_injective h1)
        ((Codec.vector (d 0)).encode_injective h2))
  admitted := admitted
  inhabited := supply

/-- The two stored matrices, the right-hand side and four blank state vectors. -/
noncomputable abbrev problem : Problem ℝ 2 7 :=
  (inputs lowerA upperA lowerP upperP domain admitted supply).problem

variable {lowerA upperA lowerP upperP domain admitted supply}

/-- The reference system matrix of an input. -/
abbrev matrix {d : Fin 2 → ℕ}
    (x : (problem lowerA upperA lowerP upperP domain admitted supply).Input d) :
    Matrix (Fin (d 0)) (Fin (d 0)) ℝ := x.val.1.1

/-- The reference inverse preconditioner of an input, as decoded from its stored words. It is
the supplied matrix (`preconditioner_eq`); it is written through its words because the oracle of
the stored scalar action is indexed by them. -/
abbrev preconditioner {d : Fin 2 → ℕ}
    (x : (problem lowerA upperA lowerP upperP domain admitted supply).Input d) :
    Matrix (Fin (d 0)) (Fin (d 0)) ℝ :=
  StoredOperator.denseMatrix (d 0) (d 0) ((EntryCodec.scalar ℝ).packFinMatrix x.val.1.2.1)

/-- The decoded stored preconditioner is the supplied inverse preconditioner. -/
theorem preconditioner_eq {d : Fin 2 → ℕ}
    (x : (problem lowerA upperA lowerP upperP domain admitted supply).Input d) :
    preconditioner x = x.val.1.2.1 :=
  StoredOperator.denseMatrix_packFinMatrix _

/-- The vector-level program: the routine on stored data, which forwards both raw contexts and
initializes the supplied iterate. Every operator call already consists of dense scalar rows; BLAS
lowering follows separately. -/
def blasProgram : Program RCLikeBlas.Operation CmpTst 2 7 := solveRoutine.close 2 7

/-- The entire implementation has scalar operations as its target signature. This includes
all BLAS calls and both operator calls, with no remaining operator or vector primitive. -/
def program : Program ScalarOp CmpTst 2 7 := zeroStartRoutine.close 2 7

/-- The scalar program is the vector-level program with its vector operations linked. -/
theorem program_eq_link : program = blasProgram.link RoundedScalarBlas.table := rfl

/-- Both raw matrices and every supplied vector capacity contribute to resident payload. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem lowerA upperA lowerP upperP domain admitted supply).Input d) :
    (problem lowerA upperA lowerP upperP domain admitted supply).initialBytes d x =
      2 * d 0 * d 0 + 5 * d 0 := by
  refine ((inputs lowerA upperA lowerP upperP domain admitted supply).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.vector, Codec.matrix, List.ofFn_succ]
  ring

variable (lowerA upperA lowerP upperP domain admitted supply)

/-- The actual scalar program's complete canonical resources and physical rounded prefix.
The prefix length can be zero. An early stop has zero residual; reaching the cap makes no
convergence claim. The oracle is the actual stored scalar preconditioner action. -/
noncomputable def specification (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (E : (Fin 2 → ℕ) → ℝ) :
    Specification ScalarOp CmpTst
      (problem lowerA upperA lowerP upperP domain admitted supply) where
  budget := staticCost program
  scratch := staticPeak RoundedScalarBlas.resources program
  work d := RoundedScalarBlas.resources.work (staticCost program d)
  span d := RoundedScalarBlas.resources.span (staticCost program d)
  memory d := 2 * d 0 * d 0 + 5 * d 0 + staticPeak RoundedScalarBlas.resources program d
  good d x _ _ mem := mem.pos = 0 ∧ ∃ m ≤ d 1, ∃ s rho,
    StoresState id (d 0) (3, 0) (4, 0) (5, 0) (6, 0) s mem ∧
      RunPrefix (matrix x) (preconditioner x)
        (StoredContext.oracle hM hu (d 0) ((EntryCodec.scalar ℝ).packFinMatrix x.val.1.2.1))
        x.val.1.2.2
        (E d) m s rho ∧ (m < d 1 → s.r = 0)

/-- Raw spectral windows and explicit scalar/cap precision imply total rounded execution,
physical initialized-prefix output, and every resource bound of the actual scalar-only tree.
No local oracle-correctness or successful-execution callback is required. -/
noncomputable def algorithm (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (E : (Fin 2 → ℕ) → ℝ)
    (hAccuracy : ∀ d, domain d →
      Standard.Accuracy (StoredContext.relativeError u (d 0)) u (E d) (Blas.seq.err u) (d 0))
    (ha : ∀ d, domain d → 0 < lowerA d) (hp : ∀ d, domain d → 0 < lowerP d)
    (hAp : ∀ d, domain d → 6 * E d * upperA d ≤ lowerA d)
    (hPp : ∀ d, domain d → 6 * E d * upperP d ≤ lowerP d)
    (hwindow : ∀ d, domain d → E d *
      (1024 * (upperA d / lowerA d) * (upperP d / lowerP d)) ^ (d 1 + 1) ≤ 1 / 2) :
    Algorithm (RoundedScalarBlas.model
      (problem lowerA upperA lowerP upperP domain admitted supply) M)
      (specification lowerA upperA lowerP upperP domain admitted supply M u hM hu E) := by
  refine (inputs lowerA upperA lowerP upperP domain admitted supply).algorithm
    (fun d _ => zeroStartSpec hM hu (d 0) (E d) (lowerA d) (upperA d) (lowerP d) (upperP d))
    ?_ ?_ ?_ (hmemory := ?_)
  · intro d hd x I hI
    obtain ⟨hS, hCmp⟩ := RoundedScalarBlas.model_laws hI
    exact zeroStartRoutine_meets hS hCmp hM hu (hAccuracy d hd) (ha d hd) (hp d hd) (hAp d hd)
      (hPp d hd)
  · intro d hd x hx τ
    have hA := StoredOperator.denseMatrix_packFinMatrix x.1
    have hP := StoredOperator.denseMatrix_packFinMatrix x.2.1
    obtain ⟨h1, h2, h3, h4⟩ := hx
    exact ⟨rfl, hA.symm ▸ h1, hP.symm ▸ h2, hA.symm ▸ h3, hP.symm ▸ h4, hwindow d hd⟩
  · intro d _ x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs, rs, zs, ps)
    have hA := StoredOperator.denseMatrix_packFinMatrix x.val.1.1
    have hb := decv_ofFn (n := d 0) x.val.1.2.2
    have key : ∀ (A' : Matrix (Fin (d 0)) (Fin (d 0)) ℝ) (b' : Fin (d 0) → ℝ),
        A' = x.val.1.1 → b' = x.val.1.2.2 →
        (∃ m ≤ d 1, ∃ s rho, StoresState id (d 0) (3, 0) (4, 0) (5, 0) (6, 0) s m' ∧
          RunPrefix A' (preconditioner x)
            (StoredContext.oracle hM hu (d 0) ((EntryCodec.scalar ℝ).packFinMatrix x.val.1.2.1))
            b' (E d) m s rho ∧ (m < d 1 → s.r = 0)) →
        ∃ m ≤ d 1, ∃ s rho, StoresState id (d 0) (3, 0) (4, 0) (5, 0) (6, 0) s m' ∧
          RunPrefix x.val.1.1 (preconditioner x)
            (StoredContext.oracle hM hu (d 0) ((EntryCodec.scalar ℝ).packFinMatrix x.val.1.2.1))
            x.val.1.2.2 (E d) m s rho ∧ (m < d 1 → s.r = 0) := by
      rintro _ _ rfl rfl h
      exact h
    exact ⟨hpos, key _ _ hA hb (PrefixOutput.of_values hys hrel)⟩
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

/-- What the certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work, the span and the
memory of the
specification, and its final memory satisfies the output condition
(`NLAlib.Ops.Routine.Domain.Checked`). -/
theorem algorithm_checked (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (E : (Fin 2 → ℕ) → ℝ)
    (hAccuracy : ∀ d, domain d →
      Standard.Accuracy (StoredContext.relativeError u (d 0)) u (E d) (Blas.seq.err u) (d 0))
    (ha : ∀ d, domain d → 0 < lowerA d) (hp : ∀ d, domain d → 0 < lowerP d)
    (hAp : ∀ d, domain d → 6 * E d * upperA d ≤ lowerA d)
    (hPp : ∀ d, domain d → 6 * E d * upperP d ≤ lowerP d)
    (hwindow : ∀ d, domain d → E d *
      (1024 * (upperA d / lowerA d) * (upperP d / lowerP d)) ^ (d 1 + 1) ≤ 1 / 2) :
    (inputs lowerA upperA lowerP upperP domain admitted supply).Checked
      (algorithm lowerA upperA lowerP upperP domain admitted supply M u hM hu E hAccuracy ha hp
        hAp hPp hwindow) :=
  (inputs lowerA upperA lowerP upperP domain admitted supply).checked_all _

end NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Certification
