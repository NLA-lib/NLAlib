/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.SpectralBisection

/-!
# Mathematical slots of the spectral bisection tree

A node's mathematical size determines its interval of slots. Sample indices, path traversal,
subtree samples and level parameters depend only on the pure matrix algorithm. They are
independent of a program evaluator, memory representation or operation interpretation.

## Main definitions

* `NLAlib.eighTapeSample`: sample indices for a node's depth and slot.
* `NLAlib.eighLoc`: the slot and mathematical node reached along a path.
* `NLAlib.eighSlotTree`: sample indices throughout a subtree.
* `NLAlib.eighLevelParams`: the rounded radius and tolerance at each depth.
-/

@[expose] public section

namespace NLAlib

/-! ### Slots and samples -/

/-- **The sample positions of the node at slot $lo$ of depth $d$** (root size $N$): the seed at
uniform position $Nd + lo$, and entry $(i, j)$ of the test matrix of side $b$ at the complex
sample $2N^2 d + N(2(lo + j) + s) + i$, $s = 0$ for the positive side and $1$ for the negative
(its real draws at the Gaussian positions twice that and the next). -/
def eighTapeSample (N d lo : ℕ) : EighSample ℕ ℕ N :=
  (N * d + lo, fun b => Matrix.of fun i j =>
    2 * (N * N) * d + N * (2 * (lo + j) + if b then 0 else 1) + i)

variable {F Su Sg : Type*} [Inhabited Sg]

/-- **The slot and node at a path** of the shallow recursion from the node $x$ at slot $lo$ of
depth $d$, each node with the samples of its slot (`NLAlib.eighTapeSample`): $(lo, x)$ at the
empty path; along $b :: a$ none at a leaf and on the absent side of a one-child node, the same slot
for a one-child node, and the slots $lo$ (positive side) and $lo + k_+$ (negative side) of a
split, with the children of `NLAlib.eighStep`, the next window and tolerance
(`NLAlib.eighNextParams`) and the next depth counter. -/
def eighLoc (M : FloatMachine F ℕ ℕ) (N signFuel : ℕ) (R₀ β : F) :
    ℕ → ℕ → EighNode F → List Bool → Option (ℕ × EighNode F)
  | _, lo, x, [] => some (lo, x)
  | d, lo, x, b :: a =>
    let q := eighNextParams M x.R x.ε x.ℓ
    match eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
    | .leaf _ _ => none
    | .shift b' A' _ =>
      if b = b' then eighLoc M N signFuel R₀ β (d + 1) lo ⟨x.k, A', q.1, q.2, x.ℓ + 1⟩ a else none
    | .split kp _ _ _ Ap Am _ =>
      if b then eighLoc M N signFuel R₀ β (d + 1) lo ⟨kp, Ap, q.1, q.2, x.ℓ + 1⟩ a
      else eighLoc M N signFuel R₀ β (d + 1) (lo + kp) ⟨x.k - kp, Am, q.1, q.2, x.ℓ + 1⟩ a

/-- **The tree of samples at the slots** of the shallow recursion from the node $x$ at slot $lo$ of
depth $d$: at a path, the sample positions (`NLAlib.eighTapeSample`) of the slot that
`NLAlib.eighLoc` reaches, and below a leaf or on the absent side of a one-child node (unused by
`NLAlib.eigh`) those of the slot of the parent at the next depth. -/
def eighSlotTree (M : FloatMachine F ℕ ℕ) (N signFuel : ℕ) (R₀ β : F) :
    ℕ → ℕ → EighNode F → List Bool → EighSample ℕ ℕ N
  | d, lo, _, [] => eighTapeSample N d lo
  | d, lo, x, b :: a =>
    let q := eighNextParams M x.R x.ε x.ℓ
    match eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
    | .leaf _ _ => eighTapeSample N (d + 1) lo
    | .shift _ A' _ => eighSlotTree M N signFuel R₀ β (d + 1) lo ⟨x.k, A', q.1, q.2, x.ℓ + 1⟩ a
    | .split kp _ _ _ Ap Am _ =>
      if b then eighSlotTree M N signFuel R₀ β (d + 1) lo ⟨kp, Ap, q.1, q.2, x.ℓ + 1⟩ a
      else eighSlotTree M N signFuel R₀ β (d + 1) (lo + kp) ⟨x.k - kp, Am, q.1, q.2, x.ℓ + 1⟩ a

/-- **The window and tolerance of depth $d$**: $(R_0, \varepsilon)$ at depth $0$, and the next
window and tolerance (`NLAlib.eighNextParams`) with depth counter $\ell_0 + d$ below; every node at
depth $d$ has them. -/
def eighLevelParams (M : FloatMachine F Su Sg) (R₀ ε : F) (ℓ₀ : ℕ) : ℕ → F × F
  | 0 => (R₀, ε)
  | d + 1 =>
    eighNextParams M (eighLevelParams M R₀ ε ℓ₀ d).1 (eighLevelParams M R₀ ε ℓ₀ d).2 (ℓ₀ + d)

end NLAlib
