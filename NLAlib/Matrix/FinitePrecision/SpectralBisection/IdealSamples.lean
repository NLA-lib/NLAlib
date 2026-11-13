/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Slots
public import NLAlib.Matrix.FinitePrecision.Samples

/-!
# Ideal samples for spectral bisection

## Main results

* `NLAlib.eighIdealTree`: indexed ideal samples along the pure recursion.
-/

@[expose] public section

namespace NLAlib

open Computation

variable {F : Type*}

/-! ### Ideal samples -/

/-- **The ideal complex sample** $(\xi_{2z} + i\,\xi_{2z+1})/\sqrt2$ of the Gaussian draws of an
ideal tape at the complex sample $z$. -/
noncomputable def eighIdealComplex (ξ : Dist → ℕ → ℝ) (z : ℕ) : ℂ :=
  ⟨ξ .gaussian (2 * z) / √2, ξ .gaussian (2 * z + 1) / √2⟩

/-- **The ideal sample of a node** of root size $N$ and depth budget $D$, on the ideal tape $\xi$,
at the path `a`: for a node of size $k$ at slot $lo$ of depth $d < D$ (`ko = some k`), the seed at
uniform position $Nd + lo$ and the entries $(i, j)$, $i, j < k$, of the test matrices at the
static positions of `NLAlib.eighTapeSample`; every other seed and entry at a position beyond the
$N D$ uniform and $4N^2 D$ Gaussian draws of the program, indexed by the path, the side and the
entry (`Encodable.encode`). -/
noncomputable def eighIdealSample (ξ : Dist → ℕ → ℝ) (N D d lo : ℕ) (ko : Option ℕ)
    (a : List Bool) : EighSample ℝ ℂ N :=
  let fresh : Bool → Fin N → Fin N → ℂ := fun b i j =>
    eighIdealComplex ξ (2 * (N * N) * D + Encodable.encode (a, b, (i : ℕ), (j : ℕ)))
  match ko with
  | some k =>
    if d < D then
      (ξ .uniform (N * d + lo), fun b => Matrix.of fun i j =>
        if (i : ℕ) < k ∧ (j : ℕ) < k then
          eighIdealComplex ξ (2 * (N * N) * d + N * (2 * (lo + j) + if b then 0 else 1) + i)
        else fresh b i j)
    else (ξ .uniform (N * D + Encodable.encode a), fun b => Matrix.of (fresh b))
  | none => (ξ .uniform (N * D + Encodable.encode a), fun b => Matrix.of (fresh b))

/-- **The tree of ideal samples** that a run of `NLAlib.eighProg` on the ideal tape $\xi$ reads, for
the machine `M` over ideal samples: from the node $x$ (if any) at slot $lo$ of depth $d$, reached
by the path `pre`, the sample `NLAlib.eighIdealSample` at the empty path, and along $b :: a$ the
child that `NLAlib.eighStep` on that sample gives (none below a leaf and on the absent side of a
one-child node), at its slot. -/
noncomputable def eighIdealTree (M : FloatMachine F ℝ ℂ) (N signFuel D : ℕ) (R₀ β : F)
    (ξ : Dist → ℕ → ℝ) : ℕ → ℕ → Option (EighNode F) → List Bool → List Bool → EighSample ℝ ℂ N
  | d, lo, x, pre, [] => eighIdealSample ξ N D d lo (x.map EighNode.k) pre
  | d, lo, none, pre, b :: a => eighIdealTree M N signFuel D R₀ β ξ (d + 1) lo none (pre ++ [b]) a
  | d, lo, some x, pre, b :: a =>
    let q := eighNextParams M x.R x.ε x.ℓ
    match eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighIdealSample ξ N D d lo (some x.k) pre)
    with
    | .leaf _ _ => eighIdealTree M N signFuel D R₀ β ξ (d + 1) lo none (pre ++ [b]) a
    | .shift b' A' _ =>
      eighIdealTree M N signFuel D R₀ β ξ (d + 1) lo
        (if b = b' then some ⟨x.k, A', q.1, q.2, x.ℓ + 1⟩ else none) (pre ++ [b]) a
    | .split kp _ _ _ Ap Am _ =>
      if b then eighIdealTree M N signFuel D R₀ β ξ (d + 1) lo (some ⟨kp, Ap, q.1, q.2, x.ℓ + 1⟩)
        (pre ++ [b]) a
      else eighIdealTree M N signFuel D R₀ β ξ (d + 1) (lo + kp)
        (some ⟨x.k - kp, Am, q.1, q.2, x.ℓ + 1⟩) (pre ++ [b]) a


end NLAlib
