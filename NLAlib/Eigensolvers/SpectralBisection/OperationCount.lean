/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.WorkCertification
public import NLAlib.Ops.OperationCount

/-!
# The operation count of spectral bisection

The work of the dense spectral bisection program (`NLAlib.SpectralBisection.bisectionProgram`) at
order
`n`, depth `L` and iteration cap `c` is at most

`(L + 1) c (362 n³ + 146 n² + 222 n) + L (1587 n³ + 760 n² + 2429 n + 305)
  + 1599 n³ + 818 n² + 2509 n + 680 + (L + 1) (2 c + 11) T(n)`,

where `T` dominates the declared cost of a matrix multiplication or QR factorization. The first
three terms bound every instruction that is not a matrix operation: scalar operations, draws,
literals, queries and structural instructions, each of weight one. They are the instruction
polynomial of the fixed instrumented tree (`NLAlib.Ops.Program.countPoly`), checked by the
kernel. The last term is the matrix work of `NLAlib.SpectralBisection.matrixWorkBisectionAlgorithm`.

The polynomial is an upper bound read off the syntax: a loop over the blocks of a level is
charged as if every block had the full order, so its cubic term overestimates the scalar
overhead, whose blocks have total order `n`. The matrix term uses the actual block sizes.

## Main results

* `NLAlib.SpectralBisection.countPoly_bisectionProgram`: the polynomial of the program.
* `NLAlib.SpectralBisection.countedBisectionAlgorithm`: the certificate with this explicit work and
  span.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The number of instructions other than matrix operations of spectral bisection at order
`d 0`, depth `d 1` and iteration cap `d 2`, at most. -/
def operationCount (d : Fin 3 → ℕ) : ℕ :=
  (d 1 + 1) * d 2 * (362 * d 0 ^ 3 + 146 * d 0 ^ 2 + 222 * d 0) +
    d 1 * (1587 * d 0 ^ 3 + 760 * d 0 ^ 2 + 2429 * d 0 + 305) +
    1599 * d 0 ^ 3 + 818 * d 0 ^ 2 + 2509 * d 0 + 680

/-- The instruction polynomial of the spectral bisection program, evaluated by the kernel. -/
theorem countPoly_bisectionProgram :
    (bisectionProgram (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).countPoly =
      [(680, []), (146, [0, 0, 1, 2]), (362, [0, 0, 0, 1, 2]), (222, [0, 1, 2]),
        (146, [0, 0, 2]), (362, [0, 0, 0, 2]), (222, [0, 2]), (818, [0, 0]), (2509, [0]),
        (1599, [0, 0, 0]), (305, [1]), (760, [0, 0, 1]), (2429, [0, 1]),
        (1587, [0, 0, 0, 1])] := by
  kernel_rfl

/-- The polynomial of the program at the sizes `d` is the operation count. -/
theorem eval_countPoly_bisectionProgram (d : Fin 3 → ℕ) :
    CountPoly.eval (List.ofFn d)
      (bisectionProgram (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).countPoly = operationCount d := by
  rw [countPoly_bisectionProgram]
  simp only [CountPoly.eval, CountPoly.monoEval, operationCount, List.ofFn_succ, List.ofFn_zero,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil,
    List.getD_cons_zero, List.getD_cons_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

variable {K : Type} [Inhabited K]

/-- The work specification of spectral bisection with the explicit operation count in place
of the static count of the program. -/
noncomputable def countedSpecification
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWorkspace : MatrixOp → List ℕ → ℕ) (T : ℕ → ℕ) :
    Specification DenseOp (CmpTst ⊕ IdxTst) (problem (K := K) domain admitted) :=
  { workSpecification M dec mm qr domain admitted matrixWorkspace T with
    work := fun d => operationCount d + (d 1 + 1) * (2 * d 2 + 11) * T (d 0)
    span := fun d => operationCount d + (d 1 + 1) * (2 * d 2 + 11) * T (d 0) }

/-- Dense spectral bisection at order `n`, depth `L` and cap `c` runs within
`operationCount` instructions other than matrix operations, plus `(L + 1) (2 c + 11) T(n)`
matrix work, with the output, storage and hypotheses of `matrixWorkBisectionAlgorithm`. -/
noncomputable def countedBisectionAlgorithm
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) (T : ℕ → ℕ)
    (hLit : ∀ d, domain d → IsExactNatLit dec M (max (d 0) 4))
    (hN : ∀ d, domain d → 2 ≤ d 0) (hT : Monotone T)
    (hadd : ∀ i j, T i + T j ≤ T (i + j))
    (hMatrix : ∀ o ds, matrixWork o ds ≤ T (ds.foldr max 0)) :
    Algorithm
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (countedSpecification M dec mm qr domain admitted matrixWorkspace T) := by
  refine ⟨bisectionProgram (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst), ?_⟩
  refine (Ops.Program.certifies_iff_exec _ _ _).mpr ?_
  intro d hd x I hI τ
  obtain ⟨st, hr, hp, hc, -, -, hm, hgood⟩ := (matrixWorkBisectionAlgorithm M dec mm qr domain
    admitted matrixWork matrixWorkspace T hLit hN hT hadd hMatrix).correct_exec d hd x I hI τ
  rcases Dense.laws_functionalModel M dec (EntryCodec.pair K) mm qr
    (Dense.resources matrixWork matrixWorkspace) d x I hI with
    ⟨hS, hL, hMM, hQR, hSample, hC, hQ⟩
  have hKernel := bisectionProgram_kernelWeight_le_of_exec M dec mm qr
    hS hL hC hMM hQR hQ hSample d x (hLit d hd) T hT hadd
    (Dense.resources matrixWork matrixWorkspace) hr
  have hSplit := Dense.work_le_of_kernelWeight_le matrixWork matrixWorkspace T hMatrix
    (le_refl st.cost) hKernel
  have hPoly := (bisectionProgram (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).exec_weight_le_countPoly
    (Dense.resources matrixWork matrixWorkspace) (Dense.resources (fun _ _ => 0) matrixWorkspace)
    (fun o _ => by cases o <;> simp [Dense.resources]) (fun _ _ => le_rfl) (fun _ _ => le_rfl) hr
  have hWork : (Dense.resources matrixWork matrixWorkspace).work st.cost ≤
      operationCount d + (d 1 + 1) * (2 * d 2 + 11) * T (d 0) :=
    hSplit.trans (Nat.add_le_add_right (hPoly.trans (eval_countPoly_bisectionProgram d).le) _)
  refine ⟨st, hr, hp, hc, hWork, ?_, hm, hgood⟩
  change (Dense.resources matrixWork matrixWorkspace).span st.cost ≤ _
  rw [Dense.span_eq_work]
  exact hWork

end NLAlib.SpectralBisection
