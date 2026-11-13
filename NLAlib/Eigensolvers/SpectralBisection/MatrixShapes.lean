/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Ops.CallSupport
public import NLAlib.Ops.Catalog.Dense
public import NLAlib.Ops.Catalog.MatrixWorkspace

/-!
# Root-bounded matrix-call shapes

The claims inspect the actual static call support, including every permitted bounded query
result. Operand offsets, recursion depth and iteration caps are unrestricted.

## Main results

* `NLAlib.SpectralBisection.MatrixShape`: exact matrix-operation arities and root bounds.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Matrix primitives have their declared arities, and every logical dimension is at most
the root size. Other primitive groups impose no matrix-shape requirement. -/
def MatrixShape (n : ℕ) : DenseOp → List ℕ → Prop
  | .matrix .mul, ds => ∃ l m k, ds = [l, m, k] ∧ l ≤ n ∧ m ≤ n ∧ k ≤ n
  | .matrix .qr, ds => ∃ m k, ds = [m, k] ∧ m ≤ n ∧ k ≤ n
  | _, _ => True

/-- A statement using only scalar, index and sample primitives has no matrix shape obligations. -/
theorem matrixShapes_of_allOps (n : ℕ) (s : Stmt DenseOp (CmpTst ⊕ IdxTst))
    (hs : s.allOps (fun o => match o with | .matrix _ => false | _ => true) = true)
    (idx : List ℕ) : (stmtCost s idx).CallsSatisfy (MatrixShape n) := by
  refine Stmt.allOps_callsSatisfy _ (MatrixShape n) ?_ s hs idx
  intro o ho ds
  cases o <;> simp only [MatrixShape, Bool.false_eq_true] at ho ⊢

private theorem signTest_shape (n k : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (Sign.test (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ?_
  constructor
  · change (Count.one (DenseOp.matrix .mul) [k, k, k] :
        Count DenseOp (CmpTst ⊕ IdxTst)).CallsSatisfy (MatrixShape n)
    exact (Count.callsSatisfy_one _ _ _).mpr ⟨k, k, k, rfl, hk, hk, hk⟩
  · exact matrixShapes_of_allOps n _ (by rfl) _

private theorem signStep_shape (n k : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (Sign.step (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ?_
  refine ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ?_
  refine ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ?_
  constructor
  · change (Count.one (DenseOp.matrix .mul) [k, k, k] :
        Count DenseOp (CmpTst ⊕ IdxTst)).CallsSatisfy (MatrixShape n)
    exact (Count.callsSatisfy_one _ _ _).mpr ⟨k, k, k, rfl, hk, hk, hk⟩
  · exact matrixShapes_of_allOps n _ (by rfl) _

private theorem signRound_shape (n k : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (Sign.round (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
  · refine callsSatisfy_stmtCost_frame (d := [k]) (P := MatrixShape n) ?_ ?_
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => signStep_shape n k os hk
  · refine callsSatisfy_stmtCost_frame (d := [k]) (P := MatrixShape n) ?_ ?_
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => signTest_shape n k os hk

private theorem signLoop_shape (n k cap : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (Sign.loop (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k, cap] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
  · refine (Count.callsSatisfy_sum _ _ (MatrixShape n)).mpr ?_
    intro i hi
    refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
    · exact callsSatisfy_testCost _ _ _ _
    · refine callsSatisfy_stmtCost_frame (d := [k]) (P := MatrixShape n) ?_ ?_
      · simp [IExp.evalList, IExp.eval]
      · exact fun os => signRound_shape n k os hk
  · refine (Count.callsSatisfy_finset_sup _ _ (MatrixShape n)).mpr ?_
    exact fun i _ => matrixShapes_of_allOps n _ (by rfl) _

private theorem signStart_shape (n k cap : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (Sign.start (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k, cap] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
  · refine callsSatisfy_stmtCost_frame (d := [k]) (P := MatrixShape n) ?_ ?_
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => signTest_shape n k os hk
  · refine callsSatisfy_stmtCost_frame (d := [k, cap]) (P := MatrixShape n) ?_ ?_
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => signLoop_shape n k cap os hk

private theorem signInitialized_shape (n k cap : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (Sign.initialized (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k, cap] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine callsSatisfy_stmtCost_frame (d := [k, cap]) (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval]
  · exact fun os => signStart_shape n k cap os hk

/-- Every multiplication inside the fixed capped sign program has the square input shape.
The cap and all operand offsets are independent of the matrix dimension bound. -/
theorem sign_matrixShapes (n k cap : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (Sign.program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k, cap] ++ offs)).CallsSatisfy (MatrixShape n) := by
  simp only [Sign.program]
  refine callsSatisfy_stmtCost_frame (d := [k, cap]) (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval]
  · exact fun os => signInitialized_shape n k cap os hk

/-- Deflation's QR operates on the full square sampled product, before selecting columns. -/
theorem deflate_matrixShapes (n k r lo side : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (deflate (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      ([n, k, r, lo, side] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
  · change (Count.one (DenseOp.matrix .mul) [k, k, k] :
        Count DenseOp (CmpTst ⊕ IdxTst)).CallsSatisfy (MatrixShape n)
    exact (Count.callsSatisfy_one _ _ _).mpr ⟨k, k, k, rfl, hk, hk, hk⟩
  · refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
      ⟨?_, matrixShapes_of_allOps n _ (by rfl) _⟩
    change (Count.one (DenseOp.matrix .qr) [k, k] :
      Count DenseOp (CmpTst ⊕ IdxTst)).CallsSatisfy (MatrixShape n)
    exact (Count.callsSatisfy_one _ _ _).mpr ⟨k, k, rfl, hk, hk⟩

/-- Compression uses its actual rectangular product dimensions, including empty children. -/
theorem compress_matrixShapes (n k r : ℕ) (offs : List ℕ) (hk : k ≤ n) (hr : r ≤ n) :
    (stmtCost (compress (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      ([k, r] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
  · change (Count.one (DenseOp.matrix .mul) [r, k, k] :
        Count DenseOp (CmpTst ⊕ IdxTst)).CallsSatisfy (MatrixShape n)
    exact (Count.callsSatisfy_one _ _ _).mpr ⟨r, k, k, rfl, hr, hk, hk⟩
  · refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
      ⟨?_, matrixShapes_of_allOps n _ (by rfl) _⟩
    change (Count.one (DenseOp.matrix .mul) [r, k, r] :
      Count DenseOp (CmpTst ⊕ IdxTst)).CallsSatisfy (MatrixShape n)
    exact (Count.callsSatisfy_one _ _ _).mpr ⟨r, k, r, rfl, hr, hk, hr⟩

/-- A supported matrix call fits the finite maximum over the root-bounded shape box. -/
theorem workspace_le_envelope_of_matrixShape (W : MatrixOp → List ℕ → ℕ)
    {n : ℕ} {o : DenseOp} {ds : List ℕ} (h : MatrixShape n o ds) :
    (match o with | .matrix m => W m ds | _ => 0) ≤ MatrixOp.workspaceEnvelope W n := by
  cases o with
  | scalar _ | index _ | sample _ => exact Nat.zero_le _
  | matrix m =>
    cases m with
    | mul =>
      obtain ⟨l, m, k, rfl, hl, hm, hk⟩ := h
      exact MatrixOp.workspace_mul_le_envelope W hl hm hk
    | qr =>
      obtain ⟨m, k, rfl, hm, hk⟩ := h
      exact MatrixOp.workspace_qr_le_envelope W hm hk

end NLAlib.SpectralBisection
