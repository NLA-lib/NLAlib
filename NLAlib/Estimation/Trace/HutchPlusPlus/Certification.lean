/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Specification
public import NLAlib.Estimation.Trace.HutchPlusPlus.Solve

/-!
# Total canonical Hutch++ certification

The fixed estimator reads the supplied operator representation, samples its actual two
adjacent tape windows, and writes the existing mathematical Hutch++ estimator. A jointly
realized standardized exact-linear model supplies local operations. No full-rank assumption,
observed execution, desired numerical output or whole-program callback is a premise.

## Main results

* `NLAlib.HutchPlusPlus.Certification.algorithm`: same-run output and full resources.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus.Certification

open Ops

variable {𝕜 : Type} [RCLike 𝕜]

/-- Zero supplies the default of the raw matrix codecs and operation-model witness. -/
local instance instInhabitedCertification : Inhabited 𝕜 := ⟨0⟩

/-- Every raw operator input with positive probe count has a total canonical execution.
Counts, work, span, resident payload and the independent scratch envelope concern the same
execution that writes the mathematical estimator and releases every temporary allocation. -/
noncomputable def algorithm (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜)
    (work workspace : ExactLinear.Operation → List ℕ → ℕ) (w : ℕ)
    (hW : ∀ o d, workspace o d ≤ w) (stream : ℕ) :
    Algorithm (ExactLinear.model (problem dataLength) dataLength matrix work workspace)
      (specification dataLength matrix work workspace w stream) := by
  refine Algorithm.ofWp (program stream) (by
    change (program stream).wellTyped (ExactLinear.resources work workspace)
      (fun _ => .cell) = true
    exact wellTyped_program work workspace stream) ?_
    (fun _ _ => le_rfl) (fun d _ => staticPeak_program_le work workspace w hW stream d)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d _ x I hI τ
    obtain ⟨hS, hB, hA, hSample, hLit, hC⟩ := ExactLinear.laws hI
    let μ := (problem (𝕜 := 𝕜) dataLength).initial d x
    have h0 : x.val.2 0 = x.val.1.map some := by rw [x.property.1]; rfl
    have h1 : x.val.2 1 = [none] := by rw [x.property.1]; rfl
    have hLength : x.val.1.length = dataLength (d 0) (d 0) := x.property.2
    have hRead := Problem.initial_readBlock d x (0 : Fin 2) h0
    rw [hLength] at hRead
    have hCap : μ.store.len 1 = 1 := by
      have hc := Problem.initial_len (P := problem (𝕜 := 𝕜) dataLength) d x (1 : Fin 2)
      rw [h1] at hc
      exact hc
    have hl : μ.Live [(0, 0), (1, 0)] := by simp [μ, Mem.Live, Problem.initial]
    have hRun := writes_estimate (m := μ) (τ := τ) (n := d 0) (k := d 1) (ell := d 2)
      (data := (0, 0)) (out := (1, 0)) hS hB hC hA hSample hLit stream x.val.1 hl hRead
      (by disjoint) (by simpa only [Nat.zero_add] using hCap.ge)
    change Wp .total I τ (.frame _ _ _) _ _ μ
    apply wp_frame rfl rfl hl
    exact hRun.wp fun out hfr hp c _ => by
      refine ⟨?_, ?_, ?_⟩
      · simpa [μ, Problem.initial] using hp.1
      · simpa [μ, Problem.initial] using hfr.length_eq
      · simpa [sampleMatrices, μ, Problem.initial] using hp.2
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.HutchPlusPlus.Certification
