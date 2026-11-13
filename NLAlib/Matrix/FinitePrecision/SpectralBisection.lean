/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Deflation
public import NLAlib.Matrix.FinitePrecision.NewtonSchulzSign
public import NLAlib.Matrix.Spectral.SingularValues
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Real.Sign

/-!
# Hermitian diagonalization by randomized spectral bisection

`NLAlib.eigh M N ℓ A R₀ ε β s` computes an approximate diagonalization
$\mathbf{A} \approx \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$ of a stored
Hermitian $\mathbf{A}$ with $\|\mathbf{A}\|_2 \le R_0$ by randomized spectral bisection
([Shah2024, Algorithm 3]): at a node with window $R$, shift by a random $c$ of size at most
$R/\ell$, compute the sign of $\mathbf{A} - c\mathbf{I}$ by the Newton–Schulz iteration, the two
spectral projectors $\tfrac12(\mathbf{I} \pm \operatorname{sign})$, the rank of one by a rounded
trace, orthonormal bases $\mathbf{Q}_\pm$ of their ranges by randomized deflation, and recurse on
the compressions $\mathbf{Q}_\pm^{\mathsf{H}}\mathbf{A}\mathbf{Q}_\pm \mp (R/2)\mathbf{I}$ with
window $(1/2 + 2/\ell)R$, tolerance $(1 - 1/\ell)\varepsilon$ and $\ell + 1$; a node stops when
it has size at most $1$ or $R \le \varepsilon R_0$.

Everything is written over a `NLAlib.FloatMachine` `M`: stored numbers of an abstract type `F`,
ideal samples of abstract types `Su`, `Sg`, and only the machine's operations on them; every
scalar parameter ($R/\ell$, $R/2$, $2R$, the next window and tolerance, the test
$R \le \varepsilon R_0$, the sign threshold) is computed by the machine. The sizes $k$, $k_+$,
the depth counter $\ell$ and the step limits are natural numbers (exact integer bookkeeping, as
in [Shah2024]). Two inputs are precomputed thresholds rather than computed: $\ell$, at least
$\lceil\log_2(1/\varepsilon)\rceil + 5$, and the sign and deflation accuracy $\beta$, any stored
number below the bound of the analysis (a lower bound suffices, so no square root or logarithm is
needed). The node reached by the path `a` from the root uses the sample `s a`, a seed for its
shift and two Gaussian test matrices.

Deviations from [Shah2024, Algorithm 3]: the compressions and projectors are stored as Hermitian
matrices by the machine's entrywise operations (the source leaves their symmetry implicit);
$k_- = k - k_+$ (the source rounds both traces); one accuracy $\beta$ for all nodes (the source's
node-dependent $\delta$ is larger); explicit step limits.

## Main definitions

* `NLAlib.EighSample`, `NLAlib.leadingBlock`.
* `NLAlib.bisectionSignTol`, `NLAlib.bisectionDepth`: analysis-side bounds (reals).
* `NLAlib.EighStep`, `NLAlib.EighStep.IsSplit`, `NLAlib.eighStep`, `NLAlib.eighAux`,
  `NLAlib.eigh`.
* `NLAlib.EighNode`, `NLAlib.eighChild`, `NLAlib.eighNodeAt`: the recursion tree.
* `NLAlib.IsApproxDiagonalization`: the output guarantee.
* `NLAlib.IsEighGoodSample`: the good events of a node.

## Main results

The analysis is in `NLAlib/Matrix/Computation/SpectralBisection/`: `Projectors` (the computed
projectors and rank recovery at a node), `Split` (frames and compressions at a split), `Child`
(the children's parameters and invariant), `Node` ([Shah2024, Lemma 4.1]), `Tree` (depth, node
parameters and counts) and `Global` (the deterministic part of [Shah2024, Theorem 4.2]); the
probability is in `NLAlib/Eigensolvers/SpectralBisection.lean` and its `Global` file.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- The **ideal sample of a node**: a seed for the shift and two $N \times N$ Gaussian test
matrices, one for each spectral projector ($N$ the size of the root). -/
abbrev EighSample (Su Sg : Type*) (N : ℕ) : Type _ :=
  Su × (Bool → Matrix (Fin N) (Fin N) Sg)

/-- The **leading $k \times k$ block** of an $N \times N$ matrix, the default value outside it
when $k > N$. -/
def leadingBlock {Sg : Type*} [Inhabited Sg] {N : ℕ} (k : ℕ) (G : Matrix (Fin N) (Fin N) Sg) :
    Matrix (Fin k) (Fin k) Sg :=
  Matrix.of fun i j => if h : (i : ℕ) < N ∧ (j : ℕ) < N then G ⟨i, h.1⟩ ⟨j, h.2⟩ else default

/-- The **deflation accuracy bound of the analysis** at a node of size $k$ with tolerance
$\varepsilon$, failure parameter $\rho$ and depth parameter $\ell$:
$$\beta(k, \varepsilon, \rho, \ell) = \frac{\eta\sqrt\rho}{36k\bigl(2\sqrt k +
\sqrt{2\log(4/\rho)}\bigr)} \,, \qquad \eta = \frac{(1 - 1/\ell)\varepsilon}{5\ell} \,.$$
A real number used in hypotheses only: the algorithm takes a stored accuracy below it.
[Shah2024, Algorithm 3, line 5], with this library's Gaussian constants. -/
noncomputable def bisectionSignTol (k : ℕ) (ε ρ : ℝ) (ℓ : ℕ) : ℝ :=
  (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * √ρ /
    (36 * k * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ))))

/-- The **least depth parameter at the root** of the analysis,
$\lceil \log_2(1/\varepsilon) \rceil + 5$. [Shah2024, Section 4]. -/
noncomputable def bisectionDepth (ε : ℝ) : ℕ :=
  ⌈Real.logb 2 ε⁻¹⌉₊ + 5

/-- The **outcome of one node** of size $k$ with stored entries `F`: a leaf with its output, a
single child on the same size (the spectrum lies on one side of the shift) with the side, the
shifted matrix and the stored shift to add back, or a split into a positive part of size $k_+$
and a negative part of size $k - k_+$ with the two computed bases, the two compressions and the
stored shift. -/
inductive EighStep (F : Type*) (k : ℕ) where
  /-- A leaf, with its output. -/
  | leaf (U : Matrix (Fin k) (Fin k) (F × F)) (d : Fin k → F)
  /-- One child: the side, the shifted matrix and the shift added back to its output. -/
  | shift (b : Bool) (A' : Matrix (Fin k) (Fin k) (F × F)) (σ : F)
  /-- Two children: the bases, the compressions and the shift. -/
  | split (kp : ℕ) (h : kp ≤ k) (Qp : Matrix (Fin k) (Fin kp) (F × F))
      (Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)) (Ap : Matrix (Fin kp) (Fin kp) (F × F))
      (Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)) (σ : F)

/-- The step **splits into two children**: it is `NLAlib.EighStep.split`. -/
def EighStep.IsSplit {F : Type*} {k : ℕ} : EighStep F k → Prop
  | .split .. => True
  | _ => False

variable {F Su Sg : Type*} [Inhabited Sg]

/-- The **next window** $\mathrm{fl}(\mathrm{fl}(\mathrm{fl}(1/2) + \mathrm{fl}(2/\ell))R)$ and
**next tolerance** $\mathrm{fl}(\mathrm{fl}(1 - \mathrm{fl}(1/\ell))\varepsilon)$ of the children,
computed by the machine. -/
def eighNextParams (M : FloatMachine F Su Sg) (R ε : F) (ℓ : ℕ) : F × F :=
  let two := M.ofNat 2
  let l := M.ofNat ℓ
  (M.mul (M.add (M.div M.one two) (M.div two l)) R, M.mul (M.sub M.one (M.div M.one l)) ε)

/-- **One node of randomized spectral bisection** on the machine `M`, for a stored $\mathbf{A}$
of size $k$ with stored window $R$ and tolerance $\varepsilon$, depth counter $\ell$, ideal sample
$(v, \mathbf{G}_{\pm})$, stored root scale $R_0$ and accuracy $\beta$, and at most $N$ sign
steps: a leaf $(\mathbf{I}, \operatorname{Re}\operatorname{diag}\mathbf{A})$ for $k \le 1$, a
leaf $(\mathbf{I}, \mathbf{0})$ when the machine finds $R \le \mathrm{fl}(\varepsilon R_0)$;
otherwise the computed shift $c = \mathrm{unif}(\mathrm{fl}(R/\ell), v)$, $\mathbf{B}$ the
Newton–Schulz sign of $\mathbf{A} - c\mathbf{I}$ at accuracy $\beta$ and scale
$\mathrm{fl}(2R)$, the stored projectors $\mathbf{P}_+ = (\mathbf{B} + \mathbf{I})/2$ and
$\mathbf{P}_- = -(\mathbf{B} - \mathbf{I})/2$ (each a shift, then a rounded division by $2$:
one rounding per operation), $k_+ = \min(k, \lfloor\mathrm{fl}(t + \mathrm{fl}(1/2))\rfloor_+)$
for $t$ the rounded trace of $\mathbf{P}_+$ (the machine's floor, $0$ below zero; the program
`NLAlib.eighProg` clamps $\mathrm{fl}(t + \mathrm{fl}(1/2))$ to $[0, k]$ by two counted comparisons
before its index binder, which computes the same $k_+$ under exact comparisons and conversion);
one child on $\mathbf{A} \mp \mathrm{fl}(R/2)\mathbf{I}$ when $k_+ \in \{k, 0\}$, and otherwise the
deflated bases $\mathbf{Q}_{\pm}$ and the stored
$(\mathbf{C}_\pm + \mathbf{C}_\pm^{\mathsf{H}})/2 \mp \mathrm{fl}(R/2)\mathbf{I}$,
$\mathbf{C}_\pm = \mathrm{mm}(\mathrm{mm}(\mathbf{Q}_\pm^{\mathsf{H}}, \mathbf{A}),
\mathbf{Q}_\pm)$. [Shah2024, Algorithm 3].
Algorithm: spectral-bisection -/
def eighStep (M : FloatMachine F Su Sg) (N signFuel : ℕ) (R₀ β : F) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (R ε : F) (ℓ : ℕ) (s : EighSample Su Sg N) :
    EighStep F k :=
  if k ≤ 1 then .leaf (M.identityMat k) fun i => (A i i).1
  else if M.le R (M.mul ε R₀) then .leaf (M.identityMat k) fun _ => M.zero
  else
    let two := M.ofNat 2
    let half := M.div R two
    let c := M.unif (M.div R (M.ofNat ℓ)) s.1
    let B := newtonSchulzSign M β (M.mul two R) signFuel (M.hermShift A c)
    let Pp := M.hermScale (M.hermShift B (M.neg M.one)) two
    let Pm := M.hermScale (M.negMat (M.hermShift B M.one)) two
    let kp := min k (M.toNat (M.add (M.traceRe Pp) (M.div M.one two)))
    if kp = k then .shift true (M.hermShift A half) half
    else if kp = 0 then .shift false (M.hermShift A (M.neg half)) (M.neg half)
    else
      let Qp := deflate M kp Pp (leadingBlock k (s.2 true))
      let Qm := deflate M (k - kp) Pm (leadingBlock k (s.2 false))
      .split kp (min_le_left _ _) Qp Qm
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) two) half)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) two) (M.neg half))
        half

/-- **Randomized spectral bisection with recursion budget** $f$ on the machine `M`: unfold
`NLAlib.eighStep` at the root with the sample `s []`, recurse on the children with the
machine-computed next window and tolerance (`NLAlib.eighNextParams`), depth counter $\ell + 1$
and the samples of their subtrees, and assemble $[\mathrm{mm}(\mathbf{Q}_+, \mathbf{U}_+)\
\mathrm{mm}(\mathbf{Q}_-, \mathbf{U}_-)]$ with the rounded shifted eigenvalues. Junk value
(stored identity and zeros) when the budget is spent. [Shah2024, Algorithm 3].
Algorithm: spectral-bisection -/
def eighAux (M : FloatMachine F Su Sg) (N signFuel : ℕ) (R₀ β : F) :
    ℕ → {k : ℕ} → Matrix (Fin k) (Fin k) (F × F) → F → F → ℕ →
      (List Bool → EighSample Su Sg N) → Matrix (Fin k) (Fin k) (F × F) × (Fin k → F)
  | 0, k, _, _, _, _, _ => (M.identityMat k, fun _ => M.zero)
  | f + 1, k, A, R, ε, ℓ, s =>
    let p := eighNextParams M R ε ℓ
    match eighStep M N signFuel R₀ β A R ε ℓ (s []) with
    | .leaf U d => (U, d)
    | .shift b A' σ =>
      let r := eighAux M N signFuel R₀ β f A' p.1 p.2 (ℓ + 1) fun a => s (b :: a)
      (r.1, fun i => M.add (r.2 i) σ)
    | .split kp h Qp Qm Ap Am σ =>
      let rp := eighAux M N signFuel R₀ β f Ap p.1 p.2 (ℓ + 1) fun a => s (true :: a)
      let rm := eighAux M N signFuel R₀ β f Am p.1 p.2 (ℓ + 1) fun a => s (false :: a)
      let e : Fin k ≃ Fin kp ⊕ Fin (k - kp) :=
        (finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm
      ((Matrix.fromCols (M.mm Qp rp.1) (M.mm Qm rm.1)).submatrix id e,
        fun i => Sum.elim (fun j => M.add (rp.2 j) σ) (fun j => M.sub (rm.2 j) σ) (e i))

/-- **Randomized spectral bisection** $\mathsf{eigh}(\mathbf{A}, \varepsilon)$ on the machine `M`
for a stored $n \times n$ matrix with stored scale $R_0$, tolerance $\varepsilon$ and accuracy
$\beta$, depth counter $\ell$ (at least $\lceil\log_2(1/\varepsilon)\rceil + 5$ in the analysis),
at most $N$ steps per sign computation and the tree of ideal samples `s`: `NLAlib.eighAux` at
the root with window $R_0$ and recursion budget $\ell + 1$. In pseudo-code, with $N$ the sign
step limit `signFuel`, each node drawing its own sample $(v, \mathbf{G}_+, \mathbf{G}_-)$
($v \in [-1, 1]$, $\mathbf{G}_\pm$ the leading $k \times k$ blocks of its Gaussian matrices), every
scalar operation rounded by the machine and products, QR and the samplers its black boxes:

```text
eigh(A, R₀, ε, β, ℓ):              A Hermitian n×n, ‖A‖₂ ≤ R₀
  return node(A, R₀, ε, ℓ, budget = ℓ + 1)

node(A, R, ε, ℓ, budget):          A of size k
  if budget = 0:  return (I, 0)                  (not reached in the analysis)
  if k ≤ 1:       return (I, Re diag A)
  if R ≤ ε·R₀:    return (I, 0)
  c  ← (R/ℓ)·v                                   uniform shift in [−R/ℓ, R/ℓ]
  B  ← sign(A − c·I; accuracy β, scale 2R, at most N steps)
  P₊ ← (B + I)/2,   P₋ ← (I − B)/2
  k₊ ← min(k, ⌊tr P₊ + 1/2⌋)                     ⌊x⌋ = 0 for x < 0
  R′ ← (1/2 + 2/ℓ)·R,   ε′ ← (1 − 1/ℓ)·ε
  if k₊ = k:
    (U, d) ← node(A − (R/2)·I, R′, ε′, ℓ + 1, budget − 1);  return (U, d + R/2)
  if k₊ = 0:
    (U, d) ← node(A + (R/2)·I, R′, ε′, ℓ + 1, budget − 1);  return (U, d − R/2)
  Q₊ ← deflate(P₊, k₊; G₊),   Q₋ ← deflate(P₋, k − k₊; G₋)
  A₊ ← (C₊ + C₊ᴴ)/2 − (R/2)·I,   C₊ = Q₊ᴴ·A·Q₊
  A₋ ← (C₋ + C₋ᴴ)/2 + (R/2)·I,   C₋ = Q₋ᴴ·A·Q₋
  (U₊, d₊) ← node(A₊, R′, ε′, ℓ + 1, budget − 1)
  (U₋, d₋) ← node(A₋, R′, ε′, ℓ + 1, budget − 1)
  return ([Q₊·U₊  Q₋·U₋], [d₊ + R/2; d₋ − R/2])
```

[Shah2024, Section 4], the root call there with $R_0 = \|\mathbf{A}\|_2$ and node-dependent
accuracies; the nodes are [Shah2024, Algorithm 3].
Algorithm: spectral-bisection -/
def eigh (M : FloatMachine F Su Sg) (signFuel ℓ : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (F × F)) (R₀ ε β : F) (s : List Bool → EighSample Su Sg n) :
    Matrix (Fin n) (Fin n) (F × F) × (Fin n → F) :=
  eighAux M n signFuel R₀ β (ℓ + 1) A R₀ ε ℓ s

/-- A **node of the recursion tree** with stored entries `F`: its size $k$, matrix, window $R$,
tolerance $\varepsilon$ and depth counter $\ell$. -/
structure EighNode (F : Type*) where
  /-- The size. -/
  k : ℕ
  /-- The matrix. -/
  A : Matrix (Fin k) (Fin k) (F × F)
  /-- The window. -/
  R : F
  /-- The tolerance. -/
  ε : F
  /-- The depth counter. -/
  ℓ : ℕ

/-- **The child of a node on side $b$** under the sample `s`: none at a leaf and on the absent
side of a one-child node, and otherwise the child node of `NLAlib.eighStep` with the next window
and tolerance (`NLAlib.eighNextParams`) and depth counter. -/
def eighChild (M : FloatMachine F Su Sg) (N signFuel : ℕ) (R₀ β : F) (x : EighNode F)
    (s : EighSample Su Sg N) (b : Bool) : Option (EighNode F) :=
  let p := eighNextParams M x.R x.ε x.ℓ
  match eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ s with
  | .leaf _ _ => none
  | .shift b' A' _ => if b = b' then some ⟨x.k, A', p.1, p.2, x.ℓ + 1⟩ else none
  | .split kp _ _ _ Ap Am _ =>
    if b then some ⟨kp, Ap, p.1, p.2, x.ℓ + 1⟩ else some ⟨x.k - kp, Am, p.1, p.2, x.ℓ + 1⟩

/-- **The node at the path $a$** below the node $x$ with the tree of samples `s`: $x$ at the empty
path, and the node at the rest of the path below the child on side $b$ for a path $b :: a$, with
the samples of that subtree; none when the path leaves the tree. -/
def eighNodeAt (M : FloatMachine F Su Sg) (N signFuel : ℕ) (R₀ β : F) :
    List Bool → EighNode F → (List Bool → EighSample Su Sg N) → Option (EighNode F)
  | [], x, _ => some x
  | b :: a, x, s => (eighChild M N signFuel R₀ β x (s []) b).bind fun y =>
    eighNodeAt M N signFuel R₀ β a y fun a' => s (b :: a')

/-- `IsApproxDiagonalization A U d η κ`: **$\mathbf{U}\operatorname{diag}(\mathbf{d})
\mathbf{U}^{\mathsf{H}}$ is an approximate diagonalization of $\mathbf{A}$** with residual $\eta$
and a nearly unitary $\mathbf{U}$:
$\|\mathbf{A} - \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}\|_2 \le \eta$ and
every singular value of $\mathbf{U}$ lies in $[1 - \kappa, 1 + \kappa]$, in Loewner form
$(1 - \kappa)^2\mathbf{I} \preceq \mathbf{U}^{\mathsf{H}}\mathbf{U} \preceq
(1 + \kappa)^2\mathbf{I}$. The output guarantee of [Shah2024, Theorem 4.2]. -/
structure IsApproxDiagonalization {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℂ) (d : n → ℝ) (η κ : ℝ) : Prop where
  /-- The residual bound. -/
  specNorm_sub_le : specNorm (A - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) ≤ η
  /-- The lower singular value bound. -/
  smul_one_le : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ Uᴴ * U
  /-- The upper singular value bound. -/
  le_smul_one : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ)

/-- `IsEighGoodSample dec w x t y s`: **the good events of the node $y$ for its ideal sample**
$s = (v, \mathbf{G}_\pm)$, read through the decoding `dec`, with $\bar{\mathbf{A}}$ the decoded
matrix and the ideal shift $c' = (\bar R/\ell)v$: (I) the seed lies in $[-1, 1]$ (true almost
surely) and every eigenvalue of $\bar{\mathbf{A}}$ is at distance at least $w$ from $c'$; (II)
for each side $\pm$ whose spectral projector $\tfrac12(\mathbf{I} \pm
\operatorname{sign}(\bar{\mathbf{A}} - c'\mathbf{I}))$ has rank $r$ with $0 < r < k$, and every
orthonormal basis $\mathbf{V}$ of its range, the leading $k \times k$ block $\mathbf{G}$ of
$\mathbf{G}_\pm$ has $\|\mathbf{G}\|_2 < t$ and $\sigma_{r-1}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)
> x$, with $\mathbf{G}_1$ its first $r$ columns. [Shah2024, Lemma 4.1], Events I and II there. -/
def IsEighGoodSample {N : ℕ} (dec : F → ℝ) (w x t : ℝ) (y : EighNode F)
    (s : EighSample ℝ ℂ N) : Prop :=
  (s.1 ∈ Set.Icc (-1 : ℝ) 1 ∧
      ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * s.1|) ∧
    ∀ (b : Bool) (r : ℕ) (V : Matrix (Fin y.k) (Fin r) ℂ), 0 < r → r < y.k →
      HasOrthonormalCols V →
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + (if b then (1 : ℝ) else -1) • cfc Real.sign
        (decodeMatrix dec y.A - (dec y.R / y.ℓ * s.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))) →
      specNorm (leadingBlock y.k (s.2 b)) < t ∧
        ∀ h : r ≤ y.k,
          x < singularValues (Vᴴ * (leadingBlock y.k (s.2 b)).submatrix id (Fin.castLE h)) (r - 1)

end NLAlib
