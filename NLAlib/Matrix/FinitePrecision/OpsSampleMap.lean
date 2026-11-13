/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.OpsSampleCongr

/-!
# Mapping sample representations for the same Ops word machine

The recursive matrix algorithm observes a seed only through its sampler. Mapping seed types
while retaining those sampled word values preserves every scalar and matrix result. These are
equalities of ordinary mathematical functions, with no program interpreter construction.

## Main results

* `NLAlib.Ops.Machine.eighStep_toFloatMachine_map_samples`: one mapped node step.
* `NLAlib.Ops.Machine.eigh_toFloatMachine_map_samples`: the complete recursive result.
-/

@[expose] public section

namespace NLAlib.Ops.Machine

/-- Mapping Gaussian seed representations preserves their normalized leading blocks. -/
theorem leadingBlock_map_samples {S T W : Type} [Inhabited S] [Inhabited T]
    (g : S → T) (normal : S → W) (normal' : T → W) (hn : ∀ z, normal z = normal' (g z))
    {n k : ℕ} (hk : k ≤ n) (G : Matrix (Fin n) (Fin n) S) :
    (leadingBlock k G).map normal = (leadingBlock k (G.map g)).map normal' := by
  apply Matrix.ext
  intro i j
  have hij : (i : ℕ) < n ∧ (j : ℕ) < n := ⟨i.isLt.trans_le hk, j.isLt.trans_le hk⟩
  simp only [leadingBlock, Matrix.map_apply, Matrix.of_apply, dif_pos hij, hn]

/-- A node step preserves all word operations when the seed maps preserve sampled values. -/
theorem eighStep_toFloatMachine_map_samples {K Su Sg Su' Sg' : Type}
    [Inhabited Sg] [Inhabited Sg'] (M : Ops.Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (unif' : K → Su' → K) (normal' : Sg' → K × K) (f : Su → Su') (g : Sg → Sg')
    (hu : ∀ scale v, unif scale v = unif' scale (f v))
    (hn : ∀ z, normal z = normal' (g z)) (n fuel : ℕ) (R0 beta : K) {k : ℕ}
    (hk : k ≤ n) (A : Matrix (Fin k) (Fin k) (K × K)) (R eps : K) (ell : ℕ)
    (s : EighSample Su Sg n) :
    eighStep (M.toFloatMachine dec mm qr unif normal) n fuel R0 beta A R eps ell s =
      eighStep (M.toFloatMachine dec mm qr unif' normal') n fuel R0 beta A R eps ell
        (f s.1, fun side => (s.2 side).map g) :=
  eighStep_toFloatMachine_samples M dec mm qr unif normal unif' normal'
    n fuel R0 beta A R eps ell s _ (fun scale => hu scale s.1)
      (fun side => leadingBlock_map_samples g normal normal' hn hk (s.2 side))

/-- Every finite recursive budget preserves the sampled word computation under seed maps. -/
theorem eighAux_toFloatMachine_map_samples {K Su Sg Su' Sg' : Type}
    [Inhabited Sg] [Inhabited Sg'] (M : Ops.Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (unif' : K → Su' → K) (normal' : Sg' → K × K) (f : Su → Su') (g : Sg → Sg')
    (hu : ∀ scale v, unif scale v = unif' scale (f v))
    (hn : ∀ z, normal z = normal' (g z)) (n fuel : ℕ) (R0 beta : K) (budget : ℕ) :
    ∀ {k : ℕ} (A : Matrix (Fin k) (Fin k) (K × K)) (R eps : K) (ell : ℕ)
      (s : List Bool → EighSample Su Sg n), k ≤ n →
      eighAux (M.toFloatMachine dec mm qr unif normal) n fuel R0 beta budget A R eps ell s =
        eighAux (M.toFloatMachine dec mm qr unif' normal') n fuel R0 beta budget A R eps ell
          (fun a => (f (s a).1, fun side => ((s a).2 side).map g)) := by
  induction budget with
  | zero => intros; rfl
  | succ budget ih =>
    intro k A R eps ell s hk
    simp only [eighAux]
    rw [eighStep_toFloatMachine_map_samples M dec mm qr unif normal unif' normal'
      f g hu hn n fuel R0 beta hk A R eps ell (s [])]
    generalize eighStep (M.toFloatMachine dec mm qr unif' normal') n fuel R0 beta A R eps ell
      (f (s []).1, fun side => ((s []).2 side).map g) = step
    cases step with
    | leaf U values => rfl
    | shift side A' sigma => dsimp only; rw [ih A' _ _ _ _ hk]; rfl
    | split r hr Qp Qm Ap Am sigma =>
      dsimp only
      rw [ih Ap _ _ _ _ (hr.trans hk), ih Am _ _ _ _ ((Nat.sub_le _ _).trans hk)]
      rfl

/-- The complete pure algorithm uses exactly the same words under coupled seed maps. -/
theorem eigh_toFloatMachine_map_samples {K Su Sg Su' Sg' : Type}
    [Inhabited Sg] [Inhabited Sg'] (M : Ops.Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (unif' : K → Su' → K) (normal' : Sg' → K × K) (f : Su → Su') (g : Sg → Sg')
    (hu : ∀ scale v, unif scale v = unif' scale (f v))
    (hn : ∀ z, normal z = normal' (g z)) (fuel ell : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (K × K)) (R0 eps beta : K)
    (s : List Bool → EighSample Su Sg n) :
    eigh (M.toFloatMachine dec mm qr unif normal) fuel ell A R0 eps beta s =
      eigh (M.toFloatMachine dec mm qr unif' normal') fuel ell A R0 eps beta
        (fun a => (f (s a).1, fun side => ((s a).2 side).map g)) :=
  eighAux_toFloatMachine_map_samples M dec mm qr unif normal unif' normal'
    f g hu hn n fuel R0 beta (ell + 1) A R0 eps ell s le_rfl

end NLAlib.Ops.Machine
