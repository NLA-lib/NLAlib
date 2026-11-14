/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Scalar
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rounded roots of order a power of two

Shifted QR of degree $k = 2^m$ needs $k$-th roots of positive scalars (the potential
$\psi_k = (\psi_k^k)^{1/k}$, the exceptional radius). [BanksGarzaVargasSrivastava2022, Lemma 2.1]
assumes an unspecified Newton routine with constants $c_{\mathrm{root}}, C_{\mathrm{root}}$. For
$k = 2^m$ no such routine is needed: $m$ rounded square roots compute $a^{1/k}$ with relative
error at most $3\boldsymbol{u}$, because the square root halves the relative error of its input
and adds $\boldsymbol{u}$. The exact development computes the same iterated square roots
(`NLAlib.ShiftedQR.squareRoots`).

## Main definitions

* `NLAlib.sqrtIter`: $m$ square roots on the machine.
-/

@[expose] public section

namespace NLAlib

open Ops

/-- $m$ square roots of the word `a` on the machine `M`. -/
def sqrtIter {K : Type} (M : Machine K) : ℕ → K → K
  | 0, a => a
  | m + 1, a => sqrtIter M m (M.sqrt a)

/-- **Rounded roots of order $2^m$**: under the standard model with $0 \le \boldsymbol{u} \le
1/100$, $m$ rounded square roots of $a \ge 0$ are within $3\boldsymbol{u}\,a^{1/2^m}$ of
$a^{1/2^m}$. [BanksGarzaVargasSrivastava2022, Lemma 2.1], for $k = 2^m$. -/
theorem Ops.StdModel.abs_sqrtIter_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    |sqrtIter M m a - a ^ ((2 : ℝ) ^ m)⁻¹| ≤ 3 * u * a ^ ((2 : ℝ) ^ m)⁻¹ := by
  sorry

end NLAlib
