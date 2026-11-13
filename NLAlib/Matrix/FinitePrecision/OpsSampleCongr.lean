/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.OpsMachine
public import NLAlib.Matrix.FinitePrecision.SpectralBisection

/-!
# Mathematical sample coupling for one Ops scalar machine

Changing sample seed types changes neither the scalar operations nor the supplied matrix
routines. The sign iteration reads no random samples, and a bisection step depends only on
its sampled uniform shift and normalized leading Gaussian blocks.

## Main results

* `NLAlib.Ops.Machine.newtonSchulzSign_toFloatMachine_samplers`: sign is sampler independent.
* `NLAlib.Ops.Machine.eighStep_toFloatMachine_samples`: local word-level sample coupling.
-/

@[expose] public section

namespace NLAlib.Ops.Machine

/-- The sign routine is unchanged when only the two mathematical sampler fields change. -/
theorem newtonSchulzSign_toFloatMachine_samplers {K Su Sg Su' Sg' : Type}
    (M : Ops.Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (unif' : K → Su' → K) (normal' : Sg' → K × K) (eps scale : K) (cap : ℕ)
    {k : ℕ} (A : Matrix (Fin k) (Fin k) (K × K)) :
    newtonSchulzSign (M.toFloatMachine dec mm qr unif normal) eps scale cap A =
      newtonSchulzSign (M.toFloatMachine dec mm qr unif' normal') eps scale cap A := by
  suffices h : ∀ eta count (B : Matrix (Fin k) (Fin k) (K × K)),
      newtonSchulzLoop (M.toFloatMachine dec mm qr unif normal) eta count B =
        newtonSchulzLoop (M.toFloatMachine dec mm qr unif' normal') eta count B from h _ cap _
  intro eta count
  induction count with
  | zero => intro B; rfl
  | succ count ih => intro B; simp only [newtonSchulzLoop, ih]; rfl

/-- A deflation reads the sample matrix only after its actual normalization. -/
theorem deflate_toFloatMachine_samples {K Su Sg Su' Sg' : Type}
    (M : Ops.Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (unif' : K → Su' → K) (normal' : Sg' → K × K) {k : ℕ} (r : ℕ)
    (P : Matrix (Fin k) (Fin k) (K × K)) (G : Matrix (Fin k) (Fin k) Sg)
    (G' : Matrix (Fin k) (Fin k) Sg') (hG : G.map normal = G'.map normal') :
    NLAlib.deflate (M.toFloatMachine dec mm qr unif normal) r P G =
      NLAlib.deflate (M.toFloatMachine dec mm qr unif' normal') r P G' := by
  simp only [NLAlib.deflate, toFloatMachine, hG]

/-- A bisection step agrees on coupled sampled shifts and normalized leading Gaussian blocks.
All arithmetic and matrix routines are the actual same functions of the Ops scalar machine. -/
theorem eighStep_toFloatMachine_samples {K Su Sg Su' Sg' : Type} [Inhabited Sg]
    [Inhabited Sg'] (M : Ops.Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (unif' : K → Su' → K) (normal' : Sg' → K × K)
    (n fuel : ℕ) (R0 beta : K) {k : ℕ} (A : Matrix (Fin k) (Fin k) (K × K))
    (R eps : K) (ell : ℕ) (s : EighSample Su Sg n) (s' : EighSample Su' Sg' n)
    (hu : ∀ scale, unif scale s.1 = unif' scale s'.1)
    (hg : ∀ b, (leadingBlock k (s.2 b)).map normal =
      (leadingBlock k (s'.2 b)).map normal') :
    eighStep (M.toFloatMachine dec mm qr unif normal) n fuel R0 beta A R eps ell s =
      eighStep (M.toFloatMachine dec mm qr unif' normal') n fuel R0 beta A R eps ell s' := by
  have hShift : (M.toFloatMachine dec mm qr unif normal).hermShift A
      ((M.toFloatMachine dec mm qr unif normal).unif
        ((M.toFloatMachine dec mm qr unif normal).div R
          ((M.toFloatMachine dec mm qr unif normal).ofNat ell)) s.1) =
      (M.toFloatMachine dec mm qr unif' normal').hermShift A
        ((M.toFloatMachine dec mm qr unif' normal').unif
          ((M.toFloatMachine dec mm qr unif' normal').div R
            ((M.toFloatMachine dec mm qr unif' normal').ofNat ell)) s'.1) := by
    change (M.toFloatMachine dec mm qr unif normal).hermShift A
      (unif (M.div R (M.lit (ell : ℚ))) s.1) =
      (M.toFloatMachine dec mm qr unif' normal').hermShift A
        (unif' (M.div R (M.lit (ell : ℚ))) s'.1)
    rw [hu]
    rfl
  by_cases hk : k ≤ 1
  · simp only [eighStep, if_pos hk]; rfl
  simp only [eighStep, if_neg hk]
  generalize_proofs hp hm
  revert hp hm
  rw [hShift, newtonSchulzSign_toFloatMachine_samplers M dec mm qr unif normal unif' normal']
  intro hp hm
  simp only [deflate_toFloatMachine_samples M dec mm qr unif normal unif' normal' _ _ _ _
    (hg true), deflate_toFloatMachine_samples M dec mm qr unif normal unif' normal' _ _ _ _
      (hg false)]
  rfl

end NLAlib.Ops.Machine
