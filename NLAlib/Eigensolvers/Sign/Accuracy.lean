/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Certification
public import NLAlib.Matrix.FinitePrecision.NewtonSchulzSign.Accuracy
public import NLAlib.Ops.Probability

/-!
# Accuracy of the actual counted matrix sign execution

The numerical theorem for the capped mathematical iteration transfers directly to the
matrix returned by the canonical program. Its spectral gap, scale, precision and cap
conditions are explicit. Total execution and every resource bound come from the functional
certificate and remain attached to this same output.

## Main results

* `NLAlib.Sign.StoresApproximation` describes the actual returned sign approximation.
* `NLAlib.Sign.accepts_fixedProgram_of_isArithAccurate` guarantees that output and all
  declared resources under the numerical assumptions of the sign analysis.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K : Type} [Inhabited K]

/-- The actual returned matrix approximates the Hermitian matrix sign in spectral norm. -/
def StoresApproximation {n : ℕ} (dec : K → ℝ)
    (A : Matrix (Fin n) (Fin n) (K × K)) (eps : ℝ) (m : Mem K) : Prop :=
  ∃ X : Matrix (Fin n) (Fin n) (K × K),
    m.store.readBlock 2 0 (2 * (n * n)) = some ((EntryCodec.pair K).packFinMatrix X) ∧
      specNorm (cfc Real.sign (decodeMatrix dec A) - decodeMatrix dec X) ≤ eps

/-- Total counted matrix sign execution returns an approximation within its supplied
tolerance, under the Hermitian spectral-gap, scaling, arithmetic-error and cap assumptions
of the capped Newton–Schulz analysis. All resource bounds concern the same execution.
[Shah2024, Theorem 2.6]. -/
theorem accepts_fixedProgram_of_isArithAccurate
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → ℝ → K) (normal : ℂ → K × K)
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (h01 : dec (M.lit 0) ≠ dec (M.lit 1))
    {d : Fin 2 → ℕ} (hd : domain d) (x : (problem (K := K) domain admitted).Input d)
    (I : Interp DenseOp (CmpTst ⊕ IdxTst) K)
    (hI : (Dense.functionalModel (problem (K := K) domain admitted) M dec
      (EntryCodec.pair K) mm qr (Dense.resources matrixWork matrixWorkspace)).contracts d x I)
    (tape : Tape K) {u floor Omega : ℝ} {mu : ℕ → ℝ}
    (hM : (M.toFloatMachine dec mm qr unif normal).IsArithAccurate dec u floor Omega mu)
    (hmu : 0 ≤ mu (d 0)) (hu0 : 0 ≤ u) (hf0 : 0 ≤ floor)
    (hf : floor * (2 * d 0) ≤ 1) (hOmega : 9 * (d 0 + 1) ≤ Omega)
    (hA : (decodeMatrix dec (inputMatrix d x)).IsHermitian) {a : ℝ} (ha : 0 < a)
    (hspec : ∀ y ∈ spectrum ℝ (decodeMatrix dec (inputMatrix d x)), a ≤ |y|)
    (hb : specNorm (decodeMatrix dec (inputMatrix d x)) ≤ dec (vec x.val.1.2 1))
    (heps : 0 < dec (vec x.val.1.2 0)) (heps1 : dec (vec x.val.1.2 0) ≤ 1 / 2)
    (hu : 640 * d 0 * Real.sqrt (d 0 : ℝ) * (8 + mu (d 0)) *
      (newtonSchulzSteps (a / (2 * dec (vec x.val.1.2 1)))
        (dec (vec x.val.1.2 0) / (16 * d 0)) + 1) * u ≤
      a / dec (vec x.val.1.2 1) * dec (vec x.val.1.2 0))
    (hcap : newtonSchulzSteps (a / (2 * dec (vec x.val.1.2 1)))
      (dec (vec x.val.1.2 0) / (16 * d 0)) ≤ d 1) :
    (wordSpecification M dec mm qr unif normal domain admitted matrixWork matrixWorkspace).Accepts
      (Dense.resources matrixWork matrixWorkspace) d x
      (exec fixedProgram I (Dense.resources matrixWork matrixWorkspace)
        (problem (K := K) domain admitted).formats tape d
        ((problem (K := K) domain admitted).initial d x))
      (fun _ m => StoresApproximation dec (inputMatrix d x) (dec (vec x.val.1.2 0)) m) := by
  obtain ⟨st, hr, hp, hc, hw, hs, hm, hg⟩ :=
    (certifiedAlgorithm M dec mm qr unif normal domain admitted matrixWork matrixWorkspace
      h01).correct d hd x I hI tape
  refine ⟨st, hr, hp, hc, hw, hs, hm, ?_⟩
  refine ⟨_, hg.1, ?_⟩
  exact hM.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le hmu hu0 hf0 hf hOmega
    hA ha hspec hb heps heps1 hu hcap

end NLAlib.Sign
