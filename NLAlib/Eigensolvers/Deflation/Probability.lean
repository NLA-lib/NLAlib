/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Deflation.Certification
public import NLAlib.Eigensolvers.RandomizedDeflation
public import NLAlib.Ops.Probability

/-!
# Numerical probability for the actual sampled deflation program

The same stored sample words, matrix product, QR factors and selected columns appear in the
word certificate and the existing Gaussian deflation theorem. Their explicit coupling transfers
subspace accuracy to the actual output block and retains every resource claim on that run.

## Main results

* `NLAlib.Deflation.packedGaussianTape`: pack the normal sampler's actual word pairs.
* `NLAlib.Deflation.sampleMatrix_packedGaussianTape`: exact sample coupling.
* `NLAlib.Deflation.StoresApproxBasis`: a stored basis near the target up to a unitary factor.
* `NLAlib.Deflation.measureReal_not_accepts_le_of_reference`: generic same-run transfer.
* Concrete Gaussian subspace accuracy and complete same-run failure bounds.
-/

@[expose] public section

namespace NLAlib.Deflation

open Ops MeasureTheory ProbabilityTheory
open scoped Matrix

variable {K : Type} [Inhabited K]

/-- Store exactly the normal sampler's word pairs on the Gaussian stream. This finite tape
constructor makes no assertion about unused streams or positions, which contain default words. -/
def packedGaussianTape {n : ℕ} (normal : ℂ → K × K)
    (G : Matrix (Fin n) (Fin n) ℂ) : Tape K :=
  Tape.ofStream Stream.gauss ((EntryCodec.pair K).packFinMatrix (G.map normal))

/-- The program's complete consumed window is exactly the packed sampler output matrix. -/
theorem sampleMatrix_packedGaussianTape {n : ℕ} (normal : ℂ → K × K)
    (G : Matrix (Fin n) (Fin n) ℂ) :
    sampleMatrix n 0 (packedGaussianTape normal G) = G.map normal := by
  simp only [sampleMatrix, packedGaussianTape]
  have hlen : 2 * (n * n) = ((EntryCodec.pair K).packFinMatrix (G.map normal)).length := by
    simp [EntryCodec.pair, Nat.mul_comm]
  rw [hlen, Tape.window_ofStream, EntryCodec.matrix_packFinMatrix]

/-- The actual packed output basis is within `error` of the target basis after a square
unitary change of coordinates. This records a stored output, not a computed postprocessing. -/
def StoresApproxBasis {n rank : ℕ} (dec : K → ℝ) (U : Matrix (Fin n) (Fin rank) ℂ)
    (error : ℝ) (q : ℕ × ℕ) (m : Mem K) : Prop :=
  ∃ Q : Matrix (Fin n) (Fin rank) (K × K),
    m.store.readBlock q.1 q.2 (2 * (n * rank)) =
      some ((EntryCodec.pair K).packFinMatrix Q) ∧
      ∃ W : Matrix (Fin rank) (Fin rank) ℂ, HasOrthonormalCols W ∧
        specNorm (U * W - decodeMatrix dec Q) ≤ error

variable (F : FloatMachine K ℝ ℂ) (dec : K → ℝ)
  {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}
  (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)

/-- The total word specification identifies the mathematical deflation result on any ideal
sample whose normal-sampler words are exactly those read by the program. -/
theorem wordSpecification_stores_deflate {d : Fin 2 → ℕ}
    {x : (problem (K := K) domain admitted).Input d} {tape : Tape K}
    {G : Matrix (Fin (d 0)) (Fin (d 0)) ℂ}
    (hSample : sampleMatrix (d 0) 0 tape = G.map F.normal)
    {count : Count (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst)} {m : Mem K}
    (h : (wordSpecification F.mm F.qr domain admitted matrixWork matrixWorkspace).good
      d x tape count m) :
    m.store.readBlock 1 0 (2 * (d 0 * d 1)) =
      some ((EntryCodec.pair K).packFinMatrix (deflate F (d 1) (inputMatrix d x) G)) := by
  obtain ⟨hrank, hread, _, _⟩ := h
  rw [hSample] at hread
  rw [deflate_eq_submatrix F hrank]
  exact hread

/-- An independently bounded reference event controls full actual failure, including `none`,
resource violations, loss of the exact word output, sample advance or cleanup, and failure of
stored subspace accuracy. All conditions concern the same canonical counted execution. -/
theorem measureReal_not_accepts_le_of_reference
    {model : AccessModel DenseOp (CmpTst ⊕ IdxTst) (problem (K := K) domain admitted)}
    (algorithm : Algorithm model
      (wordSpecification F.mm F.qr domain admitted matrixWork matrixWorkspace))
    {d : Fin 2 → ℕ} (hd : domain d) (x : (problem (K := K) domain admitted).Input d)
    (I : Interp DenseOp (CmpTst ⊕ IdxTst) K) (hI : model.contracts d x I)
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsFiniteMeasure P]
    (tape : Omega → Tape K) (G : Omega → Matrix (Fin (d 0)) (Fin (d 0)) ℂ)
    (hSample : ∀ omega, sampleMatrix (d 0) 0 (tape omega) = (G omega).map F.normal)
    (U : Matrix (Fin (d 0)) (Fin (d 1)) ℂ) (error : ℝ) {theta : ℝ}
    (hReference : P.real {omega | ¬ ∃ W : Matrix (Fin (d 1)) (Fin (d 1)) ℂ,
      HasOrthonormalCols W ∧
        specNorm (U * W - decodeMatrix dec (deflate F (d 1) (inputMatrix d x) (G omega))) ≤
          error} ≤ theta) :
    P.real {omega | ¬ (wordSpecification F.mm F.qr domain admitted
      matrixWork matrixWorkspace).Accepts model.resources d x
        (exec algorithm.program I model.resources (problem (K := K) domain admitted).formats
          (tape omega) d ((problem (K := K) domain admitted).initial d x))
        (fun c m => (wordSpecification F.mm F.qr domain admitted
            matrixWork matrixWorkspace).good d x (tape omega) c m ∧
          StoresApproxBasis dec U error (1, 0) m)} ≤ theta := by
  refine algorithm.measureReal_failure_le hd x I hI tape _ _ ?_ P hReference
  intro omega count m hgood hreference
  refine ⟨hgood, deflate F (d 1) (inputMatrix d x) (G omega), ?_, hreference⟩
  exact wordSpecification_stores_deflate F matrixWork matrixWorkspace (hSample omega) hgood

/-- Gaussian deflation controls complete failure of the fixed canonical program. The raw
input decodes within `beta` of `U*S*Vᴴ`, the target factors have orthonormal columns and `S` is
invertible. The original conditioning, precision, underflow and range hypotheses are explicit.
The actual consumed tape is the packed output of the same numerical normal sampler on `G`.
The resulting probability bound retains every word and resource guarantee on the same run;
no execution-success assumption or unknown reference failure bound is supplied.
[Shah2024, Theorem 3.3]. -/
theorem measureReal_not_accepts_packedGaussianTape_le_of_hasLaw_complexGaussianMatrix
    (M : Machine K) (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (hRank : ∀ d, domain d → d 1 ≤ d 0)
    {d : Fin 2 → ℕ} (hd : domain d) (input : (problem (K := K) domain admitted).Input d)
    (I : Interp DenseOp (CmpTst ⊕ IdxTst) K)
    (hI : (Dense.functionalModel (problem (K := K) domain admitted) M dec
      (EntryCodec.pair K) F.mm F.qr
      (Dense.resources matrixWork matrixWorkspace)).contracts d input I)
    {u floor range cN beta t cut : ℝ} {muM muQ : ℕ → ℝ}
    (hArith : F.IsArithAccurate dec u floor range muM)
    (hQR : IsQRErr (decodeComplex dec) u floor range muQ F.qr)
    (hNormal : IsNormalSampler (decodeComplex dec) u cN floor range F.normal)
    {U V : Matrix (Fin (d 0)) (Fin (d 1)) ℂ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin (d 1)) (Fin (d 1)) ℂ} (hS : IsUnit S)
    {A : Matrix (Fin (d 0)) (Fin (d 0)) ℂ} (hA : A = U * S * Vᴴ)
    (hBeta : specNorm (A - decodeMatrix dec (inputMatrix d input)) ≤ beta) (hBetaMax : beta ≤ 1)
    (ht : 0 ≤ t) (hCut : 0 < cut)
    (hCondition : (specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(d 0 : ℝ) + t)) /
      cut * beta ≤ 1 / 5)
    (hPrecision : (4 * muQ (d 0) + 4 * √(d 0 : ℝ) * cN + 2 * muM (d 0)) * u ≤ beta)
    (hFloor : floor ≤ specNorm S * cut) (hFloorN : floor * √(d 0 : ℝ) ≤ cut)
    (hRange : 2 * (specNorm S + 1) * (√2 * (2 * √(d 0 : ℝ) + t)) ≤ range)
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (G : Omega → Matrix (Fin (d 0)) (Fin (d 0)) ℂ)
    (hG : HasLaw G (complexGaussianMatrix (Fin (d 0)) (Fin (d 0))) P) :
    P.real {omega | ¬ (wordSpecification F.mm F.qr domain admitted
      matrixWork matrixWorkspace).Accepts (Dense.resources matrixWork matrixWorkspace) d input
        (exec (certifiedAlgorithm M dec F.mm F.qr domain admitted
            matrixWork matrixWorkspace hRank).program I (Dense.resources matrixWork matrixWorkspace)
          (problem (K := K) domain admitted).formats (packedGaussianTape F.normal (G omega))
          d ((problem (K := K) domain admitted).initial d input))
        (fun c m => (wordSpecification F.mm F.qr domain admitted
            matrixWork matrixWorkspace).good d input (packedGaussianTape F.normal (G omega)) c m ∧
          StoresApproxBasis dec U
            (6 * ((specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(d 0 : ℝ) + t)) / cut) * beta)
            (1, 0) m)} ≤ 2 * Real.exp (-t ^ 2 / 2) + (d 1) ^ 2 * cut ^ 2 := by
  have : IsProbabilityMeasure P := hG.isProbabilityMeasure
  have hReference :=
    hArith.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_of_hasLaw_complexGaussianMatrix
      hQR hNormal (hRank d hd) hU hV hS hA hBeta hBetaMax ht hCut hCondition hPrecision
      hFloor hFloorN hRange hG
  exact measureReal_not_accepts_le_of_reference F dec matrixWork matrixWorkspace
    (certifiedAlgorithm M dec F.mm F.qr domain admitted matrixWork matrixWorkspace hRank)
    hd input I hI P (fun omega => packedGaussianTape F.normal (G omega)) G
    (fun omega => sampleMatrix_packedGaussianTape F.normal (G omega)) U _ hReference

end NLAlib.Deflation
