/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Specification
public import NLAlib.Eigensolvers.SpectralBisection.Solve

/-!
# Certification from actual supplied word buffers

The fixed dense program has total output and resource certification for every admitted raw
input and tape. Its problem supplies a packed matrix, three scalar words and empty output
capacity. Primitive contracts and independent dimension-only resource bounds are explicit.

## Main results

* `NLAlib.SpectralBisection.initial_parameter_words`: the three supplied scalar words.
* `NLAlib.SpectralBisection.initial_problem_geometry`: actual initial capacities and separation.
* `NLAlib.SpectralBisection.certifiedAlgorithm`: independent output and resource claims.
* `NLAlib.SpectralBisection.manifestAlgorithm`: full syntactic manifest certification.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {K : Type} [Inhabited K] {domain : (Fin 3 → ℕ) → Prop} {admitted : ∃ d, domain d}

private theorem vecList_three {xs : List K} (hlen : xs.length = 3) :
    xs = [vec xs 0, vec xs 1, vec xs 2] := by
  rcases xs with _ | ⟨a, xs⟩
  · simp at hlen
  rcases xs with _ | ⟨b, xs⟩
  · simp at hlen
  rcases xs with _ | ⟨c, xs⟩
  · simp at hlen
  have hz : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
  subst xs
  rfl

/-- The initial parameter buffer contains precisely its three supplied radius, tolerance and
accuracy words. The equality merely identifies the raw list using its declared length. -/
theorem initial_parameter_words (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    ((problem (K := K) domain admitted).initial d x).store.readBlock 1 0 3 =
      some [vec x.val.1.2 0, vec x.val.1.2 1, vec x.val.1.2 2] := by
  rw [initial_readBlock_parameters, ← vecList_three (length_input_parameters d x)]

/-- The four supplied buffers are live and separated, and both uninitialized output blocks
have their declared capacities. Every fact follows from the explicit raw-buffer interface. -/
theorem initial_problem_geometry (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    let μ := (problem (K := K) domain admitted).initial d x
    μ.Live [(0, 0), (1, 0), (2, 0), (3, 0)] ∧
      Fp.Apart [(0, 0), (1, 0), (2, 0), (3, 0)]
        [2 * (d 0 * d 0), 3, 2 * (d 0 * d 0), d 0] ∧
      μ.Room [(2, 0), (3, 0)] [2 * (d 0 * d 0), d 0] ∧
      μ.store.length = 4 ∧ μ.pos = 0 := by
  dsimp only
  have hs : ((problem (K := K) domain admitted).initial d x).store =
      [x.val.1.1.map some, x.val.1.2.map some,
        List.replicate (2 * (d 0 * d 0)) none, List.replicate (d 0) none] := by
    change List.ofFn x.val.2 = _
    rw [input_buffers]
    rfl
  refine ⟨?_, ?_, ?_, by simp, rfl⟩
  · simp [Mem.Live]
  · disjoint
  · simp [Mem.Room, hs, Store.len]

/-- Transparent full-tree count, scratch, work, span and resident-capacity declarations for
the fixed dense program. Matrix operation costs and workspace come from the supplied profile. -/
noncomputable def manifestSpecification (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) :
    Specification DenseOp (CmpTst ⊕ IdxTst) (problem (K := K) domain admitted) :=
  let R := Dense.resources matrixWork matrixWorkspace
  let p := program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
  wordSpecification M dec mm qr domain admitted staticBudget
    (staticPeak R p) (fun d => R.work (staticBudget d)) (fun d => R.span (staticBudget d))
    (fun d => 4 * (d 0 * d 0) + d 0 + 3 + staticPeak R p d)

/-- Canonical total certification for the fixed dense program. Bounded natural literals are
exact on every admitted dimension. The five independent resource claims refer to the same
fixed tree and supplied resource profile; no execution or whole-program hypothesis is assumed. -/
noncomputable def certifiedAlgorithm (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (budget : (Fin 3 → ℕ) → Count (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst))
    (scratch work span memory : (Fin 3 → ℕ) → ℕ)
    (hLit : ∀ d, domain d → IsExactNatLit dec M (max (d 0) 4))
    (hCost : ∀ d, domain d → staticBudget d ≤ budget d)
    (hScratch : ∀ d, domain d → staticPeak (Dense.resources matrixWork matrixWorkspace)
      (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) d ≤ scratch d)
    (hWork : ∀ d, domain d → (Dense.resources matrixWork matrixWorkspace).work (budget d) ≤ work d)
    (hSpan : ∀ d, domain d → (Dense.resources matrixWork matrixWorkspace).span (budget d) ≤ span d)
    (hMemory : ∀ d, domain d → 4 * (d 0 * d 0) + d 0 + 3 + scratch d ≤ memory d) :
    Algorithm
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (wordSpecification M dec mm qr domain admitted budget scratch work span memory) := by
  refine Algorithm.ofWp (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
    (wellTyped_program matrixWork matrixWorkspace) ?_ hCost hScratch hWork hSpan ?_
  · intro d hd x I hI τ
    rcases Dense.laws_functionalModel M dec (EntryCodec.pair K) mm qr
      (Dense.resources matrixWork matrixWorkspace) d x I hI with
      ⟨hS, hL, hMM, hQR, hSample, hC, hQ⟩
    rcases initial_problem_geometry d x with ⟨hl, _, hRoom, hLength, _⟩
    have hRun := writes_solve M dec mm qr (vec x.val.1.2 0) (vec x.val.1.2 1)
      (vec x.val.1.2 2) (inputMatrix d x)
      (μ := (problem (K := K) domain admitted).initial d x) (τ := τ) (L := d 1) (fuel := d 2)
      (a := (0, 0)) (par := (1, 0)) (u := (2, 0)) (dv := (3, 0))
      hS hL hC hMM hQR hQ hSample (hLit d hd) hl
      (initial_readBlock_inputMatrix d x) (initial_parameter_words d x) hRoom
      (by disjoint) (by disjoint)
    apply hRun.wp
    intro ν hfr h c _
    have hFinalLength : ν.store.length = 4 := hfr.length_eq.trans hLength
    simpa only [wordSpecification, Problem.initial, Nat.zero_add] using
      And.intro h.2 (And.intro h.1 hFinalLength)
  · intro d hd x
    change (problem (K := K) domain admitted).initialBytes d x + scratch d ≤ memory d
    rw [initialBytes_problem]
    exact hMemory d hd

/-- The transparent syntactic manifest, with work/span and memory evaluated on that same
manifest and profile, has a canonical certificate for every admitted raw input and tape. -/
noncomputable def manifestAlgorithm (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (hLit : ∀ d, domain d → IsExactNatLit dec M (max (d 0) 4)) :
    Algorithm
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (manifestSpecification M dec mm qr domain admitted matrixWork matrixWorkspace) := by
  apply certifiedAlgorithm M dec mm qr domain admitted matrixWork matrixWorkspace
    staticBudget _ _ _ _ hLit
  all_goals intros; exact le_rfl

/-- The fixed spectral-bisection program satisfies its actual word output specification and
all transparent manifest bounds under the generated dense functional model. -/
theorem certifies_manifest (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (hLit : ∀ d, domain d → IsExactNatLit dec M (max (d 0) 4)) :
    (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).Certifies
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (manifestSpecification M dec mm qr domain admitted matrixWork matrixWorkspace) :=
  (manifestAlgorithm M dec mm qr domain admitted matrixWork matrixWorkspace hLit).correct

end NLAlib.SpectralBisection
