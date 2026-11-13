/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Specification
public import NLAlib.Ops.Probability

/-!
# Numerical probability transfer to the actual certified solver

A certificate of the word specification already supplies total execution, complete resource
bounds, actual output reads, the tape advance and scoped cleanup. A bound on the mathematical
reference's numerical failure therefore bounds complete counted solver failure. The numerical
bound is an independent premise, discharged by the tape-reference probability theorem.

## Main results

* `NLAlib.SpectralBisection.inputResult`: the word specification's mathematical reference.
* `NLAlib.SpectralBisection.measureReal_not_accepts_le_of_wordSpecification`: same-run probability
  bound retaining every resource and functional output condition.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops MeasureTheory

variable {K : Type} [Inhabited K]

/-- The exact mathematical word result of the supplied raw input and actual indexed tape.
This is specification data; it is not evaluated to initialize any program buffer. -/
noncomputable def inputResult (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {domain : (Fin 3 → ℕ) → Prop} {admitted : ∃ d, domain d}
    (d : Fin 3 → ℕ) (x : (problem (K := K) domain admitted).Input d) (tape : Tape K) :=
  let A := inputMatrix d x
  let R0 := vec x.val.1.2 0
  let eps := vec x.val.1.2 1
  let beta := vec x.val.1.2 2
  let F := tapeMachine M dec mm qr (d 0) 0 tape
  eigh F (d 2) (d 1) A R0 eps beta
    (eighSlotTree F (d 0) (d 2) R0 beta 0 0 ⟨d 0, A, R0, eps, d 1⟩)

/-- Actual stored output blocks are an approximate diagonalization of the decoded input. -/
def StoresApproxDiagonalization {n : ℕ} (dec : K → ℝ)
    (A : Matrix (Fin n) (Fin n) (K × K)) (eta kappa : ℝ) (u values : ℕ × ℕ) (m : Mem K) : Prop :=
  ∃ result : Matrix (Fin n) (Fin n) (K × K) × (Fin n → K),
    StoresResult n 0 0 u values result m.store ∧
      IsApproxDiagonalization (decodeMatrix dec A) (decodeMatrix dec result.1)
        (fun i => dec (result.2 i)) eta kappa

variable (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  {domain : (Fin 3 → ℕ) → Prop} {admitted : ∃ d, domain d}
  (budget : (Fin 3 → ℕ) → Count (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst))
  (scratch work span memory : (Fin 3 → ℕ) → ℕ)

/-- The functional word specification supplies exactly the reference pair at the actual
output handles. It performs no additional numerical computation. -/
theorem wordSpecification_stores_inputResult {d : Fin 3 → ℕ}
    {x : (problem (K := K) domain admitted).Input d} {tape : Tape K}
    {count : Count (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst)} {m : Mem K}
    (h : (wordSpecification M dec mm qr domain admitted budget scratch work span memory).good
      d x tape count m) :
    StoresResult (d 0) 0 0 (2, 0) (3, 0) (inputResult M dec mm qr d x tape) m.store := h.1

/-- Reference numerical failure bounds complete actual solver failure: `none`, any resource
bound violation, loss of the functional word specification, or incorrect numerical output.
All facts refer to the same canonical counted execution, with no success premise. -/
theorem measureReal_not_accepts_le_of_wordSpecification
    {model : AccessModel DenseOp (CmpTst ⊕ IdxTst) (problem (K := K) domain admitted)}
    (algorithm : Algorithm model
      (wordSpecification M dec mm qr domain admitted budget scratch work span memory))
    {d : Fin 3 → ℕ} (hd : domain d) (x : (problem (K := K) domain admitted).Input d)
    (I : Interp DenseOp (CmpTst ⊕ IdxTst) K) (hI : model.contracts d x I)
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsFiniteMeasure P]
    (tape : Omega → Tape K) {theta : ℝ}
    (hReference : P.real {omega | ¬ IsApproxDiagonalization (decodeMatrix dec (inputMatrix d x))
      (decodeMatrix dec (inputResult M dec mm qr d x (tape omega)).1)
      (fun i => dec ((inputResult M dec mm qr d x (tape omega)).2 i))
      (2 * dec (vec x.val.1.2 1) * dec (vec x.val.1.2 0)) (dec (vec x.val.1.2 1) / 3)} ≤ theta) :
    P.real {omega | ¬ (wordSpecification M dec mm qr domain admitted
      budget scratch work span memory).Accepts model.resources d x
        (exec algorithm.program I model.resources (problem (K := K) domain admitted).formats
          (tape omega) d ((problem (K := K) domain admitted).initial d x))
        (fun c m => (wordSpecification M dec mm qr domain admitted
            budget scratch work span memory).good d x (tape omega) c m ∧
          StoresApproxDiagonalization dec (inputMatrix d x)
            (2 * dec (vec x.val.1.2 1) * dec (vec x.val.1.2 0)) (dec (vec x.val.1.2 1) / 3)
            (2, 0) (3, 0) m)} ≤ theta := by
  refine algorithm.measureReal_failure_le hd x I hI tape _ _ ?_ P hReference
  intro omega count m hgood hreference
  refine ⟨hgood, inputResult M dec mm qr d x (tape omega), ?_, hreference⟩
  exact wordSpecification_stores_inputResult M dec mm qr budget scratch work span memory hgood

end NLAlib.SpectralBisection
