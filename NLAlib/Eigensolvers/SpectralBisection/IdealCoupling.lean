/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.TapeMachine
public import NLAlib.Eigensolvers.SpectralBisection.TapeRounding
public import NLAlib.Matrix.FinitePrecision.OpsSampleMap

/-!
# Actual rounded tape words and the ideal sample tree

The indexed reference machine and the ideal-sample reference use exactly the same Ops scalar
functions, matrix multiplication and QR. Seed rounding and Gaussian normalization couple the
samplers pointwise. Agreement on every reached node then identifies their complete outputs.
The tape starts at an explicit fixed position; no execution or success hypothesis is used.

## Main results

* `NLAlib.SpectralBisection.eigh_tapeMachine_roundTape`: equality to the ideal-sample recursion.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops Computation

/-- Along reached paths, the indexed sample tree and the independent ideal tree agree on
every seed and every leading block actually used by the node. -/
theorem slotTree_map_agrees_idealTree {K : Type} (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → ℕ → K) (normal : ℕ → K × K)
    (unif' : K → ℝ → K) (normal' : ℂ → K × K) (ξ : Dist → ℕ → ℝ)
    (hu : ∀ scale i, unif scale i = unif' scale (ξ .uniform i))
    (hn : ∀ z, normal z = normal' (eighIdealComplex ξ z)) (n fuel D : ℕ) (R0 beta : K) :
    ∀ (a : List Bool) (d lo : ℕ) (x : EighNode K) (pre : List Bool) (y : EighNode K), x.k ≤ n →
      d + a.length < D →
      eighNodeAt (M.toFloatMachine dec mm qr unif' normal') n fuel R0 beta a x
        (fun path => (ξ .uniform
          (eighSlotTree (M.toFloatMachine dec mm qr unif normal) n fuel R0 beta d lo x path).1,
          fun side => ((eighSlotTree (M.toFloatMachine dec mm qr unif normal)
            n fuel R0 beta d lo x path).2 side).map (eighIdealComplex ξ))) = some y →
      ξ .uniform
          (eighSlotTree (M.toFloatMachine dec mm qr unif normal) n fuel R0 beta d lo x a).1 =
        (eighIdealTree (M.toFloatMachine dec mm qr unif' normal') n fuel D R0 beta ξ
          d lo (some x) pre a).1 ∧
      ∀ side, leadingBlock y.k (((eighSlotTree (M.toFloatMachine dec mm qr unif normal)
          n fuel R0 beta d lo x a).2 side).map (eighIdealComplex ξ)) =
        leadingBlock y.k ((eighIdealTree (M.toFloatMachine dec mm qr unif' normal')
          n fuel D R0 beta ξ d lo (some x) pre a).2 side) := by
  intro a
  induction a with
  | nil =>
    intro d lo x pre y _ hd h
    obtain rfl : x = y := Option.some.inj h
    exact eighIdealSample_eq_eighTapeSample ξ (by simpa using hd) lo x.k pre
  | cons side a ih =>
    intro d lo x pre y hx hd h
    have hs := M.eighStep_toFloatMachine_map_samples dec mm qr unif normal unif' normal'
      (ξ .uniform) (eighIdealComplex ξ) hu hn n fuel R0 beta hx x.A x.R x.ε x.ℓ
      (eighTapeSample n d lo)
    have h0 := eighIdealSample_eq_eighTapeSample ξ (N := n) (D := D) (d := d) (by
      simp only [List.length_cons] at hd; omega) lo x.k pre
    have hj := eighStep_congr_leadingBlock (M.toFloatMachine dec mm qr unif' normal') n fuel R0 beta
      x.A x.R x.ε x.ℓ
      (s := (ξ .uniform (eighTapeSample n d lo).1,
        fun side => ((eighTapeSample n d lo).2 side).map (eighIdealComplex ξ)))
      (s' := eighIdealSample ξ n D d lo (some x.k) pre) h0.1 h0.2
    have hd' : d + 1 + a.length < D := by simp only [List.length_cons] at hd; omega
    simp only [eighNodeAt, eighChild, eighSlotTree.eq_1, eighSlotTree.eq_2] at h
    rw [eighSlotTree.eq_2, eighIdealTree.eq_3, ← hj, ← hs]
    rw [← hs] at h
    generalize eighStep (M.toFloatMachine dec mm qr unif normal) n fuel R0 beta x.A
      x.R x.ε x.ℓ (eighTapeSample n d lo) = step at h ⊢
    cases step with
    | leaf U values => simp only [Option.bind_none, reduceCtorEq] at h
    | shift b A sigma =>
      by_cases hb : side = b
      · simp only [hb, if_true, Option.bind_some] at h ⊢
        exact ih (d + 1) lo _ (pre ++ [b]) y hx hd' h
      · simp only [hb, if_false, Option.bind_none, reduceCtorEq] at h
    | split r hr Qp Qm Ap Am sigma =>
      cases side
      · simp only [Bool.false_eq_true, if_false, Option.bind_some] at h ⊢
        exact ih (d + 1) (lo + r) _ (pre ++ [false]) y ((Nat.sub_le _ _).trans hx) hd' h
      · simp only [if_true, Option.bind_some] at h ⊢
        exact ih (d + 1) lo _ (pre ++ [true]) y (hr.trans hx) hd' h

/-- The actual rounded Ops tape reference returns exactly the ideal-sample recursion using
the same word arithmetic and matrix routines, at any fixed starting tape position. -/
theorem eigh_tapeMachine_roundTape {K : Type} (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (roundUnif roundGaussian : ℝ → K)
    (ideal : Tape ℝ) (n base fuel ell : ℕ) (A : Matrix (Fin n) (Fin n) (K × K))
    (R0 eps beta : K) :
    let T := tapeMachine M dec mm qr n base (roundTape roundUnif roundGaussian ideal)
    let F := M.toFloatMachine dec mm qr (M.uniformSample roundUnif)
      (M.normalSample roundGaussian)
    eigh T fuel ell A R0 eps beta (eighSlotTree T n fuel R0 beta 0 0 ⟨n, A, R0, eps, ell⟩) =
      eigh F fuel ell A R0 eps beta
        (fun a => eighIdealTree F n fuel (ell + 1) R0 beta (idealTape n (ideal.shift base))
          0 0 (some ⟨n, A, R0, eps, ell⟩) [] a) := by
  let word := roundTape roundUnif roundGaussian ideal
  let ξ := idealTape n (ideal.shift base)
  let unif := fun scale i => M.mul scale (word (base + uniformPosition n i) Stream.unif)
  let normal := fun z => M.normalWords (word (base + gaussianPosition n (2 * z)) Stream.gauss)
    (word (base + gaussianPosition n (2 * z + 1)) Stream.gauss)
  have hu : ∀ scale i, unif scale i = M.uniformSample roundUnif scale (ξ .uniform i) := by
    intro scale i
    rfl
  have hn : ∀ z, normal z = M.normalSample roundGaussian (eighIdealComplex ξ z) := by
    intro z
    rw [eighIdealComplex, Machine.normalSample_div_sqrt_two]
    rfl
  refine (M.eigh_toFloatMachine_map_samples dec mm qr unif normal
    (M.uniformSample roundUnif) (M.normalSample roundGaussian) (ξ .uniform)
    (eighIdealComplex ξ) hu hn fuel ell A R0 eps beta _).trans ?_
  refine eigh_congr_samples _ fuel ell A R0 eps beta fun a y ha hy => ?_
  exact slotTree_map_agrees_idealTree M dec mm qr unif normal
    (M.uniformSample roundUnif) (M.normalSample roundGaussian) ξ hu hn n fuel (ell + 1)
    R0 beta a 0 0 _ [] y le_rfl (by omega) hy

end NLAlib.SpectralBisection
