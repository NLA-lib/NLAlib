/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Alg
public import NLAlib.Krylov.Lanczos.Reorth.TwoPass

/-!
# Lanczos with two classical reorthogonalization passes

This follows the existing full-reorthogonalized Lanczos algorithm: Paige's raw residual,
its norm before orthogonalization, two classical passes against all current basis columns,
and guarded normalization. The coefficient prefix agrees with ordinary Lanczos; the suffix
stores each preorthogonalization norm. All output tails are zero initialized.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.solve`: complete reorthogonalized Lanczos program.
* `NLAlib.Krylov.Lanczos.Reorth.staticCost_solve`: explicit triangular sweep accounting.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
variable [Has CmpTst Tst]

/-- The preorthogonalization self-dot is rooted only on its positive branch. A zero vector
leaves its preinitialized norm entry zero. -/
def preNorm : Stmt Op Tst :=
  .seq (.call (Has.inj Blas1Op.dot) [.var 0]
    [⟨4, .const 0⟩, ⟨4, .const 0⟩] [⟨5, .const 0⟩])
    (.ite (Has.inj CmpTst.isPos) [] [⟨5, .const 0⟩]
      (.call (Has.inj ScalarOp.sqrt) [] [⟨5, .const 0⟩]
        [⟨2, .var 4 + .const 2 * .var 1 + .const 2 + .var 5⟩]) .skip)

/-- One round uses the current V prefix for both classical passes. The enclosing layout is
B,V,C,Prev,Work,t and index n,cap,Boff,Voff,Coff,j, as in ordinary Lanczos. -/
def advance : Stmt Op Tst :=
  .seq (.frame [.var 0]
    [⟨3, .const 0⟩, ⟨1, .var 3 + .var 5 * .var 0⟩, ⟨2, .var 4 + .var 1 + .var 5⟩,
      ⟨4, .const 0⟩, ⟨2, .var 4 + .var 5⟩, ⟨5, .const 0⟩,
      ⟨4, .const 0⟩, ⟨2, .var 4 + .var 5⟩] Lanczos.update)
    (.seq preNorm
      (.seq (.frame [.var 0, .var 5 + .const 1]
        [⟨1, .var 3⟩, ⟨4, .const 0⟩, ⟨4, .const 0⟩] cgs2)
        (.seq (.call (Has.inj Blas1Op.dot) [.var 0]
          [⟨4, .const 0⟩, ⟨4, .const 0⟩] [⟨5, .const 0⟩])
          (.seq (.call (Has.inj Blas1Op.copy) [.var 0]
            [⟨1, .var 3 + .var 5 * .var 0⟩] [⟨3, .const 0⟩])
            (.frame [.var 0]
              [⟨4, .const 0⟩, ⟨5, .const 0⟩,
                ⟨1, .var 3 + (.var 5 + .const 1) * .var 0⟩,
                ⟨2, .var 4 + .var 1 + .var 5 + .const 1⟩,
                ⟨1, .var 3 + (.var 5 + .const 1) * .var 0⟩,
                ⟨2, .var 4 + .var 1 + .var 5 + .const 1⟩] Lanczos.normalize)))))

/-- Stop before the next round when the latest self-dot is zero, or at the requested cap. -/
def rounds : Stmt Op Tst :=
  .whileFuel (.var 1) (Has.inj CmpTst.isPos) [] [⟨5, .const 0⟩] advance .skip

/-- Full-reorthogonalized Lanczos with output V of length (cap+1)*n and packed C of length
3*cap+2. C's ordinary prefix has length 2*cap+2, followed by cap preorthogonalization norms. -/
def solve : Stmt Op Tst :=
  .alloc (.var 0) (.alloc (.var 0) (.alloc (.const 2)
    (.seq (.frame [(.var 1 + .const 1) * .var 0] [⟨1, .var 3⟩] Lanczos.zero)
      (.seq (.frame [.const 3 * .var 1 + .const 2] [⟨2, .var 4⟩] Lanczos.zero)
        (.seq (.frame [.var 0] [⟨3, .const 0⟩] Lanczos.zero)
          (.seq (.call (Has.inj Blas1Op.dot) [.var 0]
            [⟨0, .var 2⟩, ⟨0, .var 2⟩] [⟨5, .const 0⟩])
            (.seq (.frame [.var 0]
              [⟨0, .var 2⟩, ⟨5, .const 0⟩, ⟨1, .var 3⟩,
                ⟨2, .var 4 + .const 2 * .var 1 + .const 1⟩,
                ⟨1, .var 3⟩, ⟨2, .var 4 + .const 2 * .var 1 + .const 1⟩] Lanczos.normalize)
              rounds)))))))

/-- Two dimensions, one input and two packed outputs. -/
def solveImpl : Impl Op Tst := ⟨2, 1, 2, solve⟩

/-- The extra preorthogonalization norm has a self-dot, a test and a possible square root. -/
noncomputable def preNormCount (n : ℕ) : Count Op Tst :=
  Count.one (Has.inj Blas1Op.dot) [n] + Count.test (Has.inj CmpTst.isPos) [] +
    Count.one (Has.inj ScalarOp.sqrt) []

/-- Every active round performs the ordinary calls, an extra norm and two classical passes. -/
noncomputable def advanceCount (n j : ℕ) : Count Op Tst :=
  Lanczos.advanceCount n + preNormCount n + cgs2Count n (j + 1)

/-- The two classical passes sum to cap*(cap+1) projections over all capped rounds. -/
noncomputable def solveCount (n cap : ℕ) : Count Op Tst :=
  Lanczos.zeroCount ((cap + 1) * n) + Lanczos.zeroCount (3 * cap + 2) + Lanczos.zeroCount n +
    Count.one (Has.inj Blas1Op.dot) [n] + Lanczos.normalizeCount n +
    cap • (Count.test (Has.inj CmpTst.isPos) [] + Lanczos.advanceCount n + preNormCount n) +
    (cap * (cap + 1)) • (Count.one (Has.inj Blas1Op.dot) [n] +
      Count.one (Has.inj ScalarOp.neg) [] + Count.one (Has.inj Blas1Op.axpy) [n])

/-- Static accounting of a single round retains its actual growing basis prefix. -/
theorem staticCost_advance (n cap b v c j : ℕ) :
    staticCost (advance (Op := Op) (Tst := Tst)) [n,cap,b,v,c,j] = advanceCount n j := by
  simp [advance, preNorm, staticCost, useCost, testCost, Lanczos.staticCost_update,
    Lanczos.staticCost_normalize, staticCost_cgs2, advanceCount, Lanczos.advanceCount,
    preNormCount]
  module

/-- Every capped projection is charged, including columns before the final breakdown test. -/
theorem staticCost_solve (n cap b v c : ℕ) :
    staticCost (solve (Op := Op) (Tst := Tst)) [n,cap,b,v,c] = solveCount n cap := by
  have hsum : ∑ j ∈ Finset.range cap, ((j + 1) * 2) = cap * (cap + 1) := by
    induction cap with
    | zero => simp
    | succ cap ih => rw [Finset.sum_range_succ, ih]; ring
  have hsup : (Finset.range (cap + 1)).sup (fun _ => (0 : Count Op Tst)) = 0 :=
    le_antisymm (Finset.sup_le fun _ _ => le_rfl) zero_le
  simp [solve, rounds, staticCost, useCost, testCost, Lanczos.staticCost_zero,
    Lanczos.staticCost_normalize, staticCost_advance, advanceCount, solveCount,
    cgs2Count, cgsPassCount, ← mul_nsmul, Finset.sum_add_distrib,
    Finset.sum_nsmul_assoc, hsum, hsup]
  module

/-- A uniform primitive-workspace envelope, including output initialization. -/
def primitivePeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  W (Has.inj OperatorOp.matvec) [n,n] + W (Has.inj ScalarOp.neg) [] +
    W (Has.inj Blas1Op.axpy) [n] + W (Has.inj Blas1Op.dot) [n] +
    W (Has.inj ScalarOp.sqrt) [] + W (Has.inj Blas1Op.copy) [n] +
    W (Has.inj Blas1Op.scal) [n] + W (Has.inj (ScalarOp.lit 0)) []

/-- At round j the reusable coefficient scratch has j+1 cells, plus one scalar cell. -/
theorem staticPeak_advance_le (W : Op → List ℕ → ℕ) (n cap b v c j : ℕ) :
    staticPeak W (advance (Op := Op) (Tst := Tst)) [n,cap,b,v,c,j] ≤
      j + 2 + primitivePeak W n := by
  have hcgs := staticPeak_cgs2_le (Op := Op) (Tst := Tst) W n (j+1) v 0 0
  simp only [cgs2Peak, cgsPassPeak] at hcgs
  unfold primitivePeak
  simp [advance, preNorm, Lanczos.update, Lanczos.normalize, staticPeak]
  omega

/-- Two n-vectors and two scalar cells are held throughout; at most cap coefficients and one
extra scalar are borrowed by a classical sweep. -/
def solvePeak (W : Op → List ℕ → ℕ) (n cap : ℕ) : ℕ :=
  2 * n + cap + 3 + primitivePeak W n

/-- All scratch is bounded independently of how early breakdown occurs. Output arrays are
caller-owned and therefore excluded from this additional-workspace bound. -/
theorem staticPeak_solve_le (W : Op → List ℕ → ℕ) (n cap b v c : ℕ) :
    staticPeak W (solve (Op := Op) (Tst := Tst)) [n,cap,b,v,c] ≤ solvePeak W n cap := by
  have hrounds : (Finset.range cap).sup (fun j =>
      staticPeak W (advance (Op := Op) (Tst := Tst)) [n,cap,b,v,c,j]) ≤
      cap + 1 + primitivePeak W n := by
    apply Finset.sup_le
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact (staticPeak_advance_le W n cap b v c j).trans (by omega)
  have hz₁ := Lanczos.staticPeak_zero_le (Op := Op) (Tst := Tst) W ((cap+1)*n) v
  have hz₂ := Lanczos.staticPeak_zero_le (Op := Op) (Tst := Tst) W (3*cap+2) c
  have hz₃ := Lanczos.staticPeak_zero_le (Op := Op) (Tst := Tst) W n 0
  simp only [solvePeak, primitivePeak] at hrounds ⊢
  simp [solve, rounds, Lanczos.normalize, staticPeak]
  omega

end NLAlib.Krylov.Lanczos.Reorth
