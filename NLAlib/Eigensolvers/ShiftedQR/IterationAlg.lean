/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.GridSearch
public import NLAlib.Eigensolvers.ShiftedQR.Radius
public import NLAlib.Eigensolvers.ShiftedQR.Kernels

/-!
# Scalar shift-strategy iteration

The actual local Ritz kernel produces stored candidate words. Scalar trials inspect them in
order, followed when needed by the implemented promising-Ritz search and a streaming grid.
The iteration copies its selected matrix back to the original matrix view. Square-root,
trial and promising-search workspace is scoped inside the implementation.

The promising search enters as a fixed implementation tree with a local total word theorem.
It is substituted by the concrete scalar implementation in the closed decoupling program;
it is never an operation of the access model.

## Main results

* `NLAlib.ShiftedQR.RitzSearchContract`: local implementation-substitution interface.
* `NLAlib.ShiftedQR.iterationWith`: the actual scalar three-phase strategy composition.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- A fixed promising-Ritz implementation consumes the actual matrix and shift words. Its
inverse-domain premises concern those mathematical shifts, and are derived by the caller from
failed candidate trials. The interface assumes no future execution or output property. -/
def RitzSearchContract {O Q : Type} (F : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n m : ℕ} {h ss r : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (shifts : List ℂ),
    IsUpperHessenberg H → shifts.length = 2 ^ m →
    (∀ s ∈ shifts, (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det ≠ 0) →
    HoldsMatrix h H μ.store → HoldsMatrix ss (shiftColumn shifts) μ.store →
    μ.Live [h, ss, r] → r.2 + 2 ≤ μ.store.len r.1 →
    Fp.Disj (Store.inBlock r.1 r.2 2)
      (Store.inBlock h.1 h.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock ss.1 ss.2 (2 * shifts.length)) →
    Writes .total I tape F.body (Env.frame [n + 1, m, 2 ^ m] [h, ss, r])
      (Store.inBlock r.1 r.2 2)
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock r.1 r.2 2 =
        some [(findRitz H m 1 shifts).re, (findRitz H m 1 shifts).im]) μ

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has CmpTst Q]

/-- Prepare stored Ritz values, product, contraction target, radius and zero acceptance flag.
The four initialized register words are followed by four words reserved for the later search. -/
def prepareIteration : Impl O Q := opsImpl% [n, m, k]
    (W, Params, Constants) → (SS, R) {
  call (Has.inj EigenvalueKernelOp.ritz) [n, k] (W) → (SS);
  run subdiagProduct.body [n, k] (W, R);
  call (Has.inj ScalarOp.mul) [] (Constants[1], R) → (R[1]);
  run radius.body [m] (R, Params[1], Params[2], Params[3], R[2]);
  call (Has.inj IndexOp.lit) [0] () → (R[3])
}

/-- After the stored Ritz trials, run the promising and exceptional-grid searches if needed.
The final guarded trial supplies a defined promising-shift fallback for a rejected full list. -/
def finishRitzSearchWith (ritzSearch : Impl O Q) : Impl O Q := opsImpl% [n, m, k, D]
    (W, SS, Constants, R, Z) → (Z, R) {
  if (Has.inj CmpTst.isZero) [] (R[3]) {
    run ritzSearch.body [n, m, k] (W, SS, R[4]);
    run tryCandidate.body [n, k] (W, R[4], Constants, R[1], R[3], Z, R[3]);
    run searchGridWithScratch.body [n, k, D]
      (W, R[4], R[2], Constants, R[1], R[3], R[6], Z, R[3]);
    run tryCandidate.body [n, k] (W, R[4], Constants, R[1], R[3], Z, R[3])
  } else { skip }
}

/-- Complete the ordered Ritz, promising and grid search from initialized registers. The
fallback repeats the promising shift if no candidate passed; convergence assumptions later
exclude that case. The original matrix remains available for every actual candidate trial. -/
def completeSearchWith (ritzSearch : Impl O Q) : Impl O Q := opsImpl% [n, m, k, D]
    (W, SS, Constants, R) → (Z, R) {
  run searchStoredWithScratch.body [n, k, k]
    (W, SS, Constants, R[1], R[6], R[3], Z, R[3]);
  run (finishRitzSearchWith ritzSearch).body [n, m, k, D] (W, SS, Constants, R, Z, Z, R)
}

/-- Run the prepared candidate search and copy its selected/default matrix back to W. The
register and trial views belong to the enclosing scoped iteration. -/
def searchAndCopyWith (ritzSearch : Impl O Q) : Impl O Q := opsImpl% [n, m, k, D]
    (W, SS, Constants, R, Z) → (W, Z, R) {
  run (completeSearchWith ritzSearch).body [n, m, k, D] (W, SS, Constants, R, Z, R);
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (n * n)] (Z, W)
}

/-- One strategy iteration over actual word buffers. Params contains `[τ,B,θ,α,γ]` and
Constants contains `[τ²,(1-γ)^(2*k)]`, initialized once by the enclosing decoupling program.
The eight local registers are product, target, radius, flag, center pair and current-shift pair.
The promising-Ritz implementation is a compile-time tree parameter, rather than a primitive. -/
def iterationWith (ritzSearch : Impl O Q) : Impl O Q := opsImpl% [n, m, k, D]
    (W, Params, Constants) → (W) {
  let SS ← alloc (2 * k);
  let R ← alloc 8;
  let Z ← alloc (2 * (n * n));
  run prepareIteration.body [n, m, k] (W, Params, Constants, SS, R);
  run (searchAndCopyWith ritzSearch).body [n, m, k, D]
    (W, SS, Constants, R, Z, W, Z, R)
}

end NLAlib.ShiftedQR
