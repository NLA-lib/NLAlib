/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Samples
public import NLAlib.Eigensolvers.SpectralBisection.State
public import NLAlib.Matrix.FinitePrecision.OpsSampleCongr
public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Slots
public import NLAlib.Ops.Catalog.Random

/-!
# Mathematical bisection on the actual shared-position tape

The reference matrix machine uses the same Ops scalar functions and matrix routines. Natural
seeds name the existing stream-local sample coordinates, embedded into the shared tape by the
established coordinate maps. The explicit base is the program's starting tape position.
Actual level batches are ordinary tape windows, with Gaussian pairs decoded by the entry codec.

## Main results

* `NLAlib.SpectralBisection.tapeMachine`: the mathematical machine on actual word samples.
* `NLAlib.SpectralBisection.eighStep_tapeMachine`: equality to the actual stored-word step.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- A mathematical matrix machine whose natural seeds read the actual shared-position tape.
Gaussian words receive the same stored square-root-of-one-half multiplication as deflation. -/
noncomputable def tapeMachine {K : Type} (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (n base : ℕ) (τ : Tape K) :
    FloatMachine K ℕ ℕ :=
  M.toFloatMachine dec mm qr
    (fun scale i => M.mul scale (τ (base + uniformPosition n i) Stream.unif))
    (fun z => M.normalWords (τ (base + gaussianPosition n (2 * z)) Stream.gauss)
      (τ (base + gaussianPosition n (2 * z + 1)) Stream.gauss))

/-- The actual uniform words stored by one level's first sample batch. -/
def levelUniformWords {K : Type} (n base : ℕ) (τ : Tape K) (d : ℕ) : List K :=
  τ.window Stream.unif (base + d * levelSampleSize n) n

/-- The actual scalar Gaussian words stored by one level's second sample batch. -/
def levelGaussianWords {K : Type} (n base : ℕ) (τ : Tape K) (d : ℕ) : List K :=
  τ.window Stream.gauss (base + d * levelSampleSize n + n) (4 * (n * n))

/-- Decode the actual Gaussian word batch as the standard column-major pair matrix. Values
outside the stored rectangle are padding and are never used by a bounded node step. -/
def levelGaussianMatrix {K : Type} [Inhabited K] (n base : ℕ) (τ : Tape K) (d : ℕ) :
    ℕ → ℕ → K × K := fun i j => (EntryCodec.pair K).entry (levelGaussianWords n base τ d)
      (j * n + i)

/-- A node's uniform seed is exactly its word in the first level batch. -/
theorem tapeMachine_unif {K : Type} [Inhabited K] (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (n base : ℕ) (τ : Tape K)
    (d lo : ℕ) (hlo : lo < n) (scale : K) :
    (tapeMachine M dec mm qr n base τ).unif scale (n * d + lo) =
      M.mul scale (vec (levelUniformWords n base τ d) lo) := by
  simp only [tapeMachine, Machine.toFloatMachine, uniformPosition_mul_add n d lo hlo,
    levelUniformWords, vec_window τ Stream.unif _ hlo, Nat.add_assoc]

/-- A natural complex sample seed reads the exact two component addresses of its level. -/
theorem tapeMachine_normal {K : Type} (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (n base : ℕ) (τ : Tape K)
    (d lo j side i : ℕ) (hcol : lo + j < n) (hside : side < 2) (hrow : i < n) :
    (tapeMachine M dec mm qr n base τ).normal
      (2 * (n * n) * d + n * (2 * (lo + j) + side) + i) =
      M.normalWords
        (τ (base + d * levelSampleSize n + n + gaussianWord n lo j side i 0) Stream.gauss)
        (τ (base + d * levelSampleSize n + n + gaussianWord n lo j side i 1) Stream.gauss) := by
  have h0 := gaussianPosition_gaussianWord n d lo j side i 0 hcol hside hrow (by omega)
  have h1 := gaussianPosition_gaussianWord n d lo j side i 1 hcol hside hrow (by omega)
  simp only [Nat.add_zero] at h0
  simp only [tapeMachine, Machine.toFloatMachine]
  rw [h0, h1]
  simp only [Nat.add_assoc]

/-- Pair decoding of the stored Gaussian batch returns the actual addressed component words. -/
theorem levelGaussianMatrix_selected {K : Type} [Inhabited K] (n base : ℕ) (τ : Tape K)
    (d lo j side i : ℕ) (hcol : lo + j < n) (hside : side < 2) (hrow : i < n) :
    levelGaussianMatrix n base τ d i (2 * (lo + j) + side) =
      (τ (base + d * levelSampleSize n + n + gaussianWord n lo j side i 0) Stream.gauss,
        τ (base + d * levelSampleSize n + n + gaussianWord n lo j side i 1) Stream.gauss) := by
  have h0 := gaussianWord_lt n lo j side i 0 hcol hside hrow (by omega)
  have h1 := gaussianWord_lt n lo j side i 1 hcol hside hrow (by omega)
  unfold levelGaussianMatrix levelGaussianWords
  change (vec (τ.window Stream.gauss _ _) (((2 * (lo + j) + side) * n + i) * 2 + 0),
    vec (τ.window Stream.gauss _ _) (((2 * (lo + j) + side) * n + i) * 2 + 1)) = _
  have q0 : ((2 * (lo + j) + side) * n + i) * 2 + 0 = gaussianWord n lo j side i 0 := by
    unfold gaussianWord
    ring
  have q1 : ((2 * (lo + j) + side) * n + i) * 2 + 1 = gaussianWord n lo j side i 1 := by
    unfold gaussianWord
    ring
  rw [q0, q1, vec_window τ Stream.gauss _ h0, vec_window τ Stream.gauss _ h1]

/-- The leading normalized Gaussian blocks of the reference machine and actual stored words
agree at every requested entry. The node's slot bound justifies each component address. -/
theorem leadingBlock_tapeMachine_normal {K : Type} [Inhabited K] (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (n base : ℕ) (τ : Tape K)
    (d lo k : ℕ) (hslot : lo + k ≤ n) (side : Bool) :
    (leadingBlock k ((eighTapeSample n d lo).2 side)).map
      (tapeMachine M dec mm qr n base τ).normal =
    (leadingBlock k ((storedNodeSample n lo (vec (levelUniformWords n base τ d) lo)
      (levelGaussianMatrix n base τ d)).2 side)).map (fun z => M.normalWords z.1 z.2) := by
  apply Matrix.ext
  intro i j
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  have hcol : lo + j < n := by omega
  have hs : (if side then 0 else 1 : ℕ) < 2 := by cases side <;> simp
  have hij : (i : ℕ) < n ∧ (j : ℕ) < n := ⟨hi, hj⟩
  simp only [leadingBlock, Matrix.map_apply, Matrix.of_apply, dif_pos hij,
    eighTapeSample, storedNodeSample]
  rw [tapeMachine_normal M dec mm qr n base τ d lo j _ i hcol hs hi,
    levelGaussianMatrix_selected n base τ d lo j _ i hcol hs hi]

/-- The existing mathematical indexed-sample step is exactly the actual stored-word step.
A slot bound suffices, including empty or one-dimensional nodes whose step reads no samples. -/
theorem eighStep_tapeMachine {K : Type} [Inhabited K] (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (n base : ℕ) (τ : Tape K)
    (d lo fuel : ℕ) (R0 beta R eps : K) (ell : ℕ) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (K × K)) (hslot : lo + k ≤ n) :
    eighStep (tapeMachine M dec mm qr n base τ) n fuel R0 beta A R eps ell
      (eighTapeSample n d lo) =
    eighStep (M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2))
      n fuel R0 beta A R eps ell
      (storedNodeSample n lo (vec (levelUniformWords n base τ d) lo)
        (levelGaussianMatrix n base τ d)) := by
  by_cases hk : k ≤ 1
  · simp only [eighStep, if_pos hk]
    rfl
  have hlo : lo < n := by omega
  exact Machine.eighStep_toFloatMachine_samples M dec mm qr _ _ _ _ n fuel R0 beta A R eps ell
    _ _ (fun scale => tapeMachine_unif M dec mm qr n base τ d lo hlo scale)
    (leadingBlock_tapeMachine_normal M dec mm qr n base τ d lo k hslot)

end NLAlib.SpectralBisection
