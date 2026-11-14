/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.BasisExtension
public import NLAlib.Ops.Catalog.Orth

/-!
# The contracts of a basis extension

The operation `NLAlib.Ops.OrthOp.extend` extends a stored basis by a block. Its contract
`NLAlib.Ops.extendRelOf` takes a predicate on the decoded matrices; this file states the two
instances, with the rounded predicate `NLAlib.IsBasisExtensionErr` and the exact predicate
`NLAlib.IsBasisExtension`. A driver assumes one of them of the operation, and an orthogonalization
scheme is proved against it and substituted by linking, so the file depends on no driver.
Design: `docs/design/LowRank-BlockLanczos.md` §3.1a.

## Main definitions

* `NLAlib.Ops.extendRel`: the rounded contract, with parameters $(\eta_0, \mu, \varepsilon)$.
* `NLAlib.Ops.exactExtendRel`: the exact contract.

## Main results

* `NLAlib.Ops.Interp.Meets.extendRel_mono`: the rounded contract is monotone in its parameters.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Ops

variable {K Op Tst : Type} [Inhabited K]

/-- **The rounded contract of a basis extension** with parameters
$(\eta_0, \mu, \varepsilon)$: the decoded basis $\mathbf{Q}$, input block $\mathbf{W}$, new block
$\mathbf{Q}'$ and coefficients $\mathbf{H}$, $\mathbf{R}$ satisfy the rounded extension
predicate `NLAlib.IsBasisExtensionErr`. Nothing is said of the words left over the input block.
The call succeeds at the dimensions `[n, k, b]` admitted by `ok`. -/
def extendRel (dec : K → ℝ) (η₀ μ ε : ℝ) (ok : ℕ → ℕ → ℕ → Prop) : BlockRel K :=
  extendRelOf dec ok fun _ _ _ Q W Q' H R => IsBasisExtensionErr η₀ μ ε Q W Q' H R

/-- **The exact contract of a basis extension**: the decoded basis $\mathbf{Q}$, input block
$\mathbf{W}$, new block $\mathbf{Q}'$ and coefficients $\mathbf{H}$, $\mathbf{R}$ satisfy the
exact extension predicate `NLAlib.IsBasisExtension`, at all dimensions. -/
def exactExtendRel {𝕜 : Type} [RCLike 𝕜] (dec : K → 𝕜) : BlockRel K :=
  extendRelOf dec (fun _ _ _ => True) fun _ _ _ Q W Q' H R => IsBasisExtension Q W Q' H R

/-- An operation that meets the rounded contract of a basis extension with parameters
$(\eta_0, \mu, \varepsilon)$, $\mu \ge 0$, meets it with a smaller window $\eta_0' \le \eta_0$,
larger parameters $\mu \le \mu'$, $\varepsilon \le \varepsilon'$ and fewer admitted
dimensions. -/
theorem Interp.Meets.extendRel_mono {dec : K → ℝ} {η₀ μ ε η₀' μ' ε' : ℝ}
    {ok ok' : ℕ → ℕ → ℕ → Prop} {I : Interp Op Tst K} {o : Op}
    (h : I.Meets .total o ((extendRel dec η₀ μ ε ok).spec ExtendOperands))
    (hok : ∀ n k b, ok' n k b → ok n k b) (hμ0 : 0 ≤ μ) (hη : η₀' ≤ η₀) (hμ : μ ≤ μ')
    (hε : ε ≤ ε') :
    I.Meets .total o ((extendRel dec η₀' μ' ε' ok').spec ExtendOperands) :=
  h.extendRelOf_mono hok fun _ _ _ _ _ _ _ _ hE => hE.mono hμ0 hη hμ hε

end NLAlib.Ops
