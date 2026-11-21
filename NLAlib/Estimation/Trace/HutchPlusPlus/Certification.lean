/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Specification
public import NLAlib.Estimation.Trace.HutchPlusPlus.Routine
public import NLAlib.Ops.OperationCount
public import NLAlib.Ops.MonomialWork

/-!
# Total canonical Hutch++ certification

The fixed estimator reads the supplied operator representation, samples its actual two
adjacent tape windows, and writes the existing mathematical Hutch++ estimator. A jointly
realized standardized exact-linear model supplies local operations. No full-rank assumption,
observed execution, desired numerical output or whole-program callback is a premise.

With unit weights, the same certificate has explicit work: the number of instructions is a
polynomial in the sizes that the kernel computes from the tree, for every stream. The last
theorem states what that certificate means in terms of the evaluator alone, for every tape: the
output is a deterministic function of the stored operator and of the words the tape holds in the
declared window. No probability law is asserted.

## Main results

* `NLAlib.HutchPlusPlus.Certification.algorithm`: same-run output and full resources.
* `NLAlib.HutchPlusPlus.Certification.countedAlgorithm`: the same with explicit work.
* `NLAlib.HutchPlusPlus.Certification.estimate_checked`: what it states.
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
  refine Routine.algorithm (r := 3) (b := 2) (estimateRoutine stream dataLength)
    (fun _ _ => estimateSpec stream matrix) (fun _ x => [x.val.1])
    (ht := wellTyped_estimateProgram work workspace stream) ?_ ?_ ?_
    (hspace := fun d _ => staticPeak_estimateProgram_le work workspace w hW stream d) (hmemory :=
        ?_)
  · intro d _ x I hI
    obtain ⟨hS, hB, hA, hSample, hLit, hC⟩ := ExactLinear.laws hI
    exact estimateRoutine_meets hS hB hC hA hSample hLit stream
  · intro d _ x
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
    refine ⟨Mem.readBlocks_of_cons hRead rfl, fun _ => trivial, ?_⟩
    change μ.Room [(1, 0)] [1]
    simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add]
    exact hCap.ge
  · intro d _ x τ m' hfr hpos ys hys hrel c _
    read_outputs hys as (zs)
    obtain ⟨v, hv, rfl⟩ := Store.readBlock_one_eq_some.mp hzs
    refine ⟨hpos.eq_of_start rfl, by simpa [Problem.initial] using hfr.length_eq, ?_⟩
    have hval : v = hutchpp (matrix (d 0) (d 0) x.val.1)
        (sampleMatrices stream (d 0) (d 1) (d 2) τ).1
        (sampleMatrices stream (d 0) (d 1) (d 2) τ).2 := hrel
    exact hzs.trans (by rw [hval])
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

/-! ### Explicit work -/

/-- The number of instructions at order `d 0` with `d 1` sketch columns and `d 2` probes, at
most. -/
def operationCount (d : Fin 3 → ℕ) : ℕ :=
  230 + 155 * d 1 + 71 * d 2 + 38 * (d 1 * d 2) + 6 * (d 0 * d 1) + 6 * (d 0 * d 2) +
    38 * (d 1 * d 1)

/-- The instruction polynomial of the program, evaluated by the kernel. It is the same for every
stream. -/
theorem countPoly_estimateProgram (stream : ℕ) :
    (estimateProgram (Op := ExactLinear.Operation) (Tst := CmpTst) stream).countPoly =
      [(230, []), (155, [1]), (71, [2]), (38, [1, 2]), (6, [0, 1]), (6, [0, 2]),
        (38, [1, 1])] := by
  kernel_rfl

/-- The polynomial of the program at the sizes `d` is the operation count. -/
theorem eval_countPoly_estimateProgram (stream : ℕ) (d : Fin 3 → ℕ) :
    CountPoly.eval (List.ofFn d)
      (estimateProgram (Op := ExactLinear.Operation) (Tst := CmpTst) stream).countPoly =
      operationCount d := by
  rw [countPoly_estimateProgram]
  poly_eval [operationCount]

/-- The certificate with explicit work: when every operation counts one, the work and the span
of the run are at most `operationCount`. The program, the output and the memory are those of
`algorithm`. -/
noncomputable def countedAlgorithm (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜)
    (workspace : ExactLinear.Operation → List ℕ → ℕ) (w : ℕ)
    (hW : ∀ o d, workspace o d ≤ w) (stream : ℕ) :
    Algorithm (ExactLinear.model (problem dataLength) dataLength matrix (fun _ _ => 1) workspace)
      { specification dataLength matrix (fun _ _ => 1) workspace w stream with
        work := operationCount, span := operationCount } :=
  (algorithm dataLength matrix (fun _ _ => 1) workspace w hW stream).withCountPoly
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) operationCount
    (fun d _ => (eval_countPoly_estimateProgram stream d).le)

/-- What the certificate states, with no reference to routines or contracts. For every order
$n$, sketch width $k$ and positive probe count $\ell$, every stored operator supplied in the
first buffer, every interpretation of the exact operations of the model, and every tape, the
counted run of the fixed program succeeds, executes at most
$230 + 155 k + 71 \ell + 38 k \ell + 6 n k + 6 n \ell + 38 k^2$ instructions (each vector
operation, draw and product with the operator counting one), stops at tape position
$n (k + \ell)$, and leaves in the second buffer the Hutch++ value of the operator for the sketch
in the first $n k$ words of the stream and the probes in the next $n \ell$. -/
theorem estimate_checked (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜)
    (workspace : ExactLinear.Operation → List ℕ → ℕ) (w : ℕ)
    (hW : ∀ o d, workspace o d ≤ w) (stream : ℕ) (d : Fin 3 → ℕ) (hd : 0 < d 2)
    (x : (problem (𝕜 := 𝕜) dataLength).Input d) (I : Interp ExactLinear.Operation CmpTst 𝕜)
    (hI : (ExactLinear.model (problem dataLength) dataLength matrix (fun _ _ => 1)
      workspace).contracts d x I) (τ : Tape 𝕜) :
    ∃ st, exec (estimateProgram stream) I (ExactLinear.resources (fun _ _ => 1) workspace)
        (problem (𝕜 := 𝕜) dataLength).formats τ d
        ((problem (𝕜 := 𝕜) dataLength).initial d x) = some st ∧
      (ExactLinear.resources (fun _ _ => 1) workspace).work st.cost ≤ operationCount d ∧
      st.mem.pos = d 0 * (d 1 + d 2) ∧
      st.mem.store.get 1 0 = some (hutchpp (matrix (d 0) (d 0) x.val.1)
        ((EntryCodec.scalar 𝕜).matrix (d 0) (d 1) (τ.window stream 0 (d 0 * d 1)))
        ((EntryCodec.scalar 𝕜).matrix (d 0) (d 2)
          (τ.window stream (d 0 * d 1) (d 0 * d 2)))) := by
  obtain ⟨st, hr, -, -, hw, -, -, hpos, -, hread⟩ :=
    (countedAlgorithm dataLength matrix workspace w hW stream).correct d hd x I hI τ
  refine ⟨st, hr, hw, hpos, ?_⟩
  simpa [vec, sampleMatrices] using Store.get_of_readBlock hread (j := 0) (by omega) default

end NLAlib.HutchPlusPlus.Certification
