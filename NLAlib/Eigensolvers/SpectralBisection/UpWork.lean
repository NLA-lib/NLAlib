/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpNodeTotal
public import NLAlib.Ops.WeightedCost
public import NLAlib.Ops.Profiles.DenseWeight
public import NLAlib.Ops.Certification

/-!
# Matrix-kernel work of upward node reconstruction

The actual stored kind selects one reconstruction and a bounded split size. Its two
products are charged at their actual dimensions, rather than at every possible answer of
the split-size query. Scalar shifts remain explicit and separately counted.

## Main results

* `NLAlib.SpectralBisection.weightedCost_upSplit_le`: two root-size kernel charges.
* `NLAlib.SpectralBisection.runs_upNode_kernelWeight`: total assembly and actual kernel work.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

private def nonmatrix : DenseOp → Bool
  | .matrix _ => false
  | _ => true

private theorem matrixFree_weightedCost {Tst : Type} (T : ℕ → ℕ)
    (s : Stmt DenseOp Tst) (hs : s.allOps nonmatrix = true) (idx : List ℕ) :
    stmtWeightedCost (Dense.matrixWeight (MatrixOp.dimensionWeight T)) (fun _ _ => 0)
      s idx = 0 := stmtWeightedCost_matrix_zero_of_allOps _ s hs idx

/-- A bounded split reconstruction performs two matrix products. Each product's largest
dimension is the parent size, including a zero-width child. No monotonicity of `T` is needed. -/
theorem weightedCost_upSplit_le (T : ℕ → ℕ) (k kp : ℕ) (offs : List ℕ) (hp : kp ≤ k) :
    stmtWeightedCost (Dense.matrixWeight (MatrixOp.dimensionWeight T))
      (fun (_ : CmpTst ⊕ IdxTst) _ => 0)
      (upSplitResultImpl (Op := DenseOp)).body ([k, kp] ++ offs) ≤ 2 * T k := by
  change _ + (_ + _) ≤ _
  conv_lhs => arg 2; arg 2; rw [matrixFree_weightedCost T _ (by rfl)]
  have hmul : (Has.inj MatrixOp.mul : DenseOp) = DenseOp.matrix .mul := rfl
  simp [stmtWeightedCost, IExp.evalList, IExp.eval, Dense.matrixWeight,
    MatrixOp.dimensionWeight, hmul, max_eq_left hp]
  omega

/-- Every bounded stored kind selects at most the two products of a split reconstruction.
The scalar maxima range over possible answers before weighting, so the bound does not
charge all possible split dimensions. No input-dependent execution assumption is used. -/
theorem weightedCost_upNode_le (T : ℕ → ℕ) (n d lo k : ℕ) (offs : List ℕ)
    (hlen : offs.length = 6) :
    stmtWeightedCost (Dense.matrixWeight (MatrixOp.dimensionWeight T))
      (fun (_ : CmpTst ⊕ IdxTst) _ => 0)
      (upNodeImpl (Op := DenseOp)).body ([n, d, lo, k] ++ offs) ≤ 2 * T k := by
  change 0 + _ ≤ _
  simp only [Nat.zero_add]
  apply Finset.sup_le
  intro kind hkind
  change _ + (_ + _) ≤ _
  conv_lhs => arg 1; rw [matrixFree_weightedCost T _ (by rfl)]
  conv_lhs => arg 2; arg 1; rw [matrixFree_weightedCost T _ (by rfl)]
  simp only [Nat.zero_add]
  apply stmtWeightedCost_ifZero_le
  intro i
  change 0 + _ ≤ _
  simp only [Nat.zero_add]
  apply Finset.sup_le
  intro kp hkp
  have hp : kp ≤ k := by
    have hb := Nat.le_of_lt_succ (Finset.mem_range.mp hkp)
    simpa [IExp.eval] using hb
  apply stmtWeightedCost_frame_le (d := [k, kp])
  · simp [IExp.evalList, IExp.eval, hlen]
  · exact fun os => weightedCost_upSplit_le T k kp os hp

/-- Actual upward reconstruction terminates and returns the existing mathematical assembly
with matrix-kernel weight at most twice the parent-size cost. The hypotheses are the stored
outcome/children, scalar and multiplication contracts, exact bounded metadata and spatial
capacity conditions. No successful-execution or numerical-quality premise is assumed.
All structural instructions remain in the instrumented execution's full count. -/
theorem runs_upNode_kernelWeight {K Su Sg : Type} [Inhabited K]
    {M : Machine K} {dec : K → ℝ} (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    {I : Interp DenseOp (CmpTst ⊕ IdxTst) K} (hS : IsScalar M I) (hQ : IsToNat dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I)
    (T : ℕ → ℕ) (W : DenseOp → List ℕ → ℕ) {τ : Tape K} {m : Mem K}
    {n d lo k : ℕ} {R : K} {ma ua qa ea sz kd kp t : ℕ × ℕ} (step : EighStep K k)
    (children : (b : Bool) →
      Matrix (Fin (step.childSize b)) (Fin (step.childSize b)) (K × K) ×
        (Fin (step.childSize b) → K))
    (hStep : StoresStep M R n d lo ma ua qa ea sz kd kp step m)
    (hChildren : ∀ b, step.HasChild b →
      StoresResult n (d + 1) (step.childSlot lo b) ua ea (children b) m.store)
    (hLit : IsExactNatLit dec M (max n 4)) (hk : k ≤ n)
    (hl : m.Live [ua, qa, ea, kd, kp, t])
    (ht : m.store.get t.1 t.2 = some (M.div R (M.lit 2)) ∧
      m.store.get t.1 (t.2 + 1) = some (M.neg (M.div R (M.lit 2))))
    (hroom : m.Room (resultOperands n d lo ua ea) (resultLengths k))
    (hap : Fp.Apart (upNodeRegions n d lo ua qa ea kd kp t) (upNodeRegionLengths n k)) :
    ConditionalRunsW I.instrument (instrumentWorkspace W) τ
      (upNodeImpl (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body.instrument
      (Env.frame [n, d, lo, k] [ua, qa, ea, kd, kp, t]) m
      (stmtPeak W (upNodeImpl (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
        (Env.frame [n, d, lo, k] [ua, qa, ea, kd, kp, t]).idx)
      (fun c m' => Dense.kernelWeight T (Count.original c) ≤ 2 * T k ∧
        m'.pos = m.pos ∧ StoresResult n d lo ua ea
          (step.assemble (M.toFloatMachine dec mm qr unif normal) children) m'.store) := by
  have htotal := writes_upNode (τ := τ) mm qr unif normal hS hQ hMM step children hStep hChildren
    hLit hk hl ht hroom hap
  apply Wp.runs_original_weighted (htotal.wp fun _ _ hp => hp)
    (Dense.matrixWeight (MatrixOp.dimensionWeight T)) (fun _ _ => 0) W
  simpa only [Env.idx_frame, List.map_cons, List.map_nil] using
    weightedCost_upNode_le T n d lo k [ua.2, qa.2, ea.2, kd.2, kp.2, t.2] rfl

end NLAlib.SpectralBisection
