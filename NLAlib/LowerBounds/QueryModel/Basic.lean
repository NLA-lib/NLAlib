/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import NLAlib.ForMathlib.MeasureTheory.Matrix
public import NLAlib.ForMathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Adaptive query algorithms

A deterministic algorithm that makes `q` adaptive queries to an oracle `f : Q → R` and then
outputs a value of type `β`: the `i`-th query is a function of the first `i` responses, and the
output is a function of all `q` of them. Randomness is not part of the object: a randomized
algorithm is a family `S → QueryAlgorithm Q R q β` indexed by a seed, and a random input is a
random variable on the probability space, so a lower bound is a statement about one product
probability space and needs no Markov kernels.

The matrix–vector query model is the oracle `A.mulVec` of a matrix `A : Matrix m n 𝕜`: a query is
a vector $\mathbf{x}$, its response $\mathbf{A}\mathbf{x}$. Access to both $\mathbf{A}$ and
$\mathbf{A}^{\mathsf{H}}$ is the oracle `twoSidedMulVec A`: a query is a pair
$(\mathbf{x}, \mathbf{y})$ and its response
$(\mathbf{A}\mathbf{x}, \mathbf{A}^{\mathsf{H}}\mathbf{y})$. Either side may be zero, and a zero
side costs nothing: `rightCount τ` and `leftCount τ` count the rounds whose right part
$\mathbf{x}$, respectively left part $\mathbf{y}$, is nonzero, so separate budgets for products
with $\mathbf{A}$ and with $\mathbf{A}^{\mathsf{H}}$ are hypotheses `rightCount τ ≤ q_R`,
`leftCount τ ≤ q_L`. The number `q` of rounds bounds both.

The definitions are total. `query i` is defined for every `i : ℕ`; only `i < q` is ever used.

The responses of an algorithm are the oracle's values at its queries; two oracles that agree at
the queries made on one of them give the same transcript (indistinguishability); non-adaptive
queries do not depend on the transcript; measurable algorithms have measurable transcripts and
outputs; the rank of the right (left) query matrix of pair queries is at most the number of right
(left) products; the Gram simulation runs an algorithm for $\mathbf{X}\mathbf{X}^{\mathsf{H}}$
on two-sided queries to $\mathbf{X}$, with `q` products on each side.

## Main definitions

* `NLAlib.QueryAlgorithm Q R q β`: the algorithm.
* `NLAlib.QueryAlgorithm.history`, `NLAlib.QueryAlgorithm.queryAt`,
  `NLAlib.QueryAlgorithm.transcript`, `NLAlib.QueryAlgorithm.run`: running it against an oracle.
* `NLAlib.QueryAlgorithm.truncate`: the first `i` queries as an algorithm of its own.
* `NLAlib.QueryAlgorithm.queries`, `NLAlib.QueryAlgorithm.queryMatrix`: the queries recomputed
  from a transcript, and for vector queries the matrix with the queries as columns.
* `NLAlib.twoSidedMulVec`: the two-sided matrix–vector oracle.
* `NLAlib.QueryAlgorithm.rightQueryMatrix`, `NLAlib.QueryAlgorithm.leftQueryMatrix`,
  `NLAlib.QueryAlgorithm.rightCount`, `NLAlib.QueryAlgorithm.leftCount`,
  `NLAlib.QueryAlgorithm.IsOneSided`: the two sides of pair queries and their costs.
* `NLAlib.QueryAlgorithm.IsNonAdaptive`: the queries do not depend on the responses.
* `NLAlib.QueryAlgorithm.IsPassStructured`: the queries come in passes, each a block chosen
  from the responses of the earlier passes.
* `NLAlib.QueryAlgorithm.comapResponse`, `NLAlib.QueryAlgorithm.mapOutput`: reading the responses
  through a map (a weaker oracle) and post-processing the output.
* `NLAlib.QueryAlgorithm.IsMeasurable`, `NLAlib.QueryAlgorithm.IsMeasurableFamily`: measurability
  of an algorithm and joint measurability of a seeded family.
* `NLAlib.QueryAlgorithm.gramSimulation`: a `2q`-round algorithm against the two-sided oracle of
  $\mathbf{X}$ that runs a `q`-query algorithm against $\mathbf{X}\mathbf{X}^{\mathsf{H}}$;
  `NLAlib.QueryAlgorithm.gramDecode` reads the simulated responses off its history.

## Main results

* `NLAlib.Measurable.twoSidedMulVec`: the two-sided oracle is measurable.
* `NLAlib.QueryAlgorithm.history_apply`, `NLAlib.QueryAlgorithm.queryAt_eq_queries_transcript`.
* `NLAlib.QueryAlgorithm.transcript_eq_of_forall_apply_queries_eq`,
  `NLAlib.QueryAlgorithm.run_eq_of_forall_apply_queries_eq`: indistinguishability.
* `NLAlib.QueryAlgorithm.IsNonAdaptive.queries_eq`.
* `NLAlib.QueryAlgorithm.IsMeasurable.measurable_history`,
  `NLAlib.QueryAlgorithm.IsMeasurable.measurable_transcript`,
  `NLAlib.QueryAlgorithm.IsMeasurable.measurable_run`,
  `NLAlib.QueryAlgorithm.IsMeasurable.measurable_queryMatrix`,
  `NLAlib.QueryAlgorithm.IsMeasurable.measurable_rightQueryMatrix`,
  `NLAlib.QueryAlgorithm.IsMeasurable.measurable_leftQueryMatrix`,
  `NLAlib.QueryAlgorithm.IsMeasurableFamily.measurable_run`,
  `NLAlib.QueryAlgorithm.IsMeasurableFamily.isMeasurable`.
* `NLAlib.QueryAlgorithm.rank_rightQueryMatrix_le_rightCount`,
  `NLAlib.QueryAlgorithm.rank_leftQueryMatrix_le_leftCount`: query spans and costs.
* `NLAlib.QueryAlgorithm.gramDecode_history_gramSimulation`,
  `NLAlib.QueryAlgorithm.run_gramSimulation`,
  `NLAlib.QueryAlgorithm.queryAt_gramSimulation_two_mul`,
  `NLAlib.QueryAlgorithm.queryAt_gramSimulation_two_mul_add_one`,
  `NLAlib.QueryAlgorithm.IsMeasurable.gramSimulation`,
  `NLAlib.QueryAlgorithm.rightCount_gramSimulation_le`,
  `NLAlib.QueryAlgorithm.leftCount_gramSimulation_le`,
  `NLAlib.QueryAlgorithm.rank_rightQueryMatrix_gramSimulation_le`.
* `NLAlib.QueryAlgorithm.history_comapResponse`, `NLAlib.QueryAlgorithm.run_comapResponse`.
* `NLAlib.QueryAlgorithm.history_mapOutput`, `NLAlib.QueryAlgorithm.run_mapOutput`.
* `NLAlib.QueryAlgorithm.IsMeasurable.comapResponse`,
  `NLAlib.QueryAlgorithm.IsMeasurable.mapOutput`,
  `NLAlib.QueryAlgorithm.IsMeasurableFamily.comapResponse`,
  `NLAlib.QueryAlgorithm.IsMeasurableFamily.mapOutput`.
* `NLAlib.QueryAlgorithm.IsPassStructured.comapResponse`,
  `NLAlib.QueryAlgorithm.IsPassStructured.mapOutput`,
  `NLAlib.QueryAlgorithm.isPassStructured_id`,
  `NLAlib.QueryAlgorithm.isPassStructured_zero_iff_isNonAdaptive`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- A deterministic **adaptive query algorithm** with `q` queries to an oracle `Q → R` and output
in `β`. The `i`-th query is `query i` applied to the first `i` responses; the output is `output`
applied to all `q` responses. Queries with index $i \ge q$ are never made. A randomized algorithm is
a family `S → QueryAlgorithm Q R q β` indexed by a seed (`QueryAlgorithm.IsMeasurableFamily`). -/
structure QueryAlgorithm (Q R : Type*) (q : ℕ) (β : Type*) where
  /-- The `i`-th query as a function of the first `i` responses. -/
  query : (i : ℕ) → (Fin i → R) → Q
  /-- The output as a function of the `q` responses. -/
  output : (Fin q → R) → β

/-- The **two-sided matrix–vector oracle** of $\mathbf{A} \in \Bbbk^{m \times n}$: the query
$(\mathbf{x}, \mathbf{y})$ returns $(\mathbf{A}\mathbf{x}, \mathbf{A}^{\mathsf{H}}\mathbf{y})$,
one product with $\mathbf{A}$ (the right part) and one with $\mathbf{A}^{\mathsf{H}}$ (the left
part). A zero part returns zero and costs nothing (`QueryAlgorithm.rightCount`,
`QueryAlgorithm.leftCount`). -/
def twoSidedMulVec {𝕜 m n : Type*} [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring 𝕜] [Star 𝕜]
    (A : Matrix m n 𝕜) (v : (n → 𝕜) × (m → 𝕜)) : (m → 𝕜) × (n → 𝕜) :=
  (A *ᵥ v.1, Aᴴ *ᵥ v.2)

namespace QueryAlgorithm

variable {Q R β : Type*} {q : ℕ}

/-- The first `i` responses of the algorithm run against the oracle `f`, by recursion on `i`:
the next query is computed from the responses so far and its response appended. -/
def history (alg : QueryAlgorithm Q R q β) (f : Q → R) : (i : ℕ) → Fin i → R
  | 0 => Fin.elim0
  | i + 1 => Fin.snoc (α := fun _ => R) (history alg f i) (f (alg.query i (history alg f i)))

/-- The `i`-th query the algorithm makes when run against the oracle `f`. -/
def queryAt (alg : QueryAlgorithm Q R q β) (f : Q → R) (i : ℕ) : Q :=
  alg.query i (alg.history f i)

/-- The **transcript**: the `q` responses of the algorithm run against the oracle `f`. -/
def transcript (alg : QueryAlgorithm Q R q β) (f : Q → R) : Fin q → R :=
  alg.history f q

/-- The output of the algorithm run against the oracle `f`. -/
def run (alg : QueryAlgorithm Q R q β) (f : Q → R) : β :=
  alg.output (alg.transcript f)

/-- The queries recomputed from a list `τ` of `q` responses: the `j`-th is `query j` applied to
the first `j` entries of `τ`. On the transcript they are the queries made
(`QueryAlgorithm.queryAt_eq_queries_transcript`). -/
def queries (alg : QueryAlgorithm Q R q β) (τ : Fin q → R) (j : Fin q) : Q :=
  alg.query j fun l => τ (Fin.castLE j.isLt.le l)

/-- For vector queries, the **query matrix** of a transcript `τ`: its column `j` is the `j`-th
query `alg.queries τ j`. -/
def queryMatrix {𝕜 n : Type*} (alg : QueryAlgorithm (n → 𝕜) R q β) (τ : Fin q → R) :
    Matrix n (Fin q) 𝕜 :=
  Matrix.of fun r j => alg.queries τ j r

section TwoSided

variable {𝕜 m n : Type*}

/-- For pair queries $(\mathbf{x}, \mathbf{y})$ (`twoSidedMulVec`), the **right query matrix**
of a transcript `τ`: its column `j` is the right part $\mathbf{x}_j$ of the `j`-th query. -/
def rightQueryMatrix (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) (τ : Fin q → R) :
    Matrix n (Fin q) 𝕜 :=
  Matrix.of fun r j => (alg.queries τ j).1 r

/-- For pair queries $(\mathbf{x}, \mathbf{y})$ (`twoSidedMulVec`), the **left query matrix** of
a transcript `τ`: its column `j` is the left part $\mathbf{y}_j$ of the `j`-th query. -/
def leftQueryMatrix (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) (τ : Fin q → R) :
    Matrix m (Fin q) 𝕜 :=
  Matrix.of fun r j => (alg.queries τ j).2 r

variable [Zero 𝕜]

/-- The **number of right products** of a transcript `τ`: the rounds whose right part
$\mathbf{x}_j$ is nonzero, each one product $\mathbf{A}\mathbf{x}_j$. A budget of $q_R$ products
with $\mathbf{A}$ is the hypothesis `∀ τ, alg.rightCount τ ≤ q_R`. -/
noncomputable def rightCount (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) (τ : Fin q → R) :
    ℕ :=
  {j : Fin q | (alg.queries τ j).1 ≠ 0}.ncard

/-- The **number of left products** of a transcript `τ`: the rounds whose left part
$\mathbf{y}_j$ is nonzero, each one product $\mathbf{A}^{\mathsf{H}}\mathbf{y}_j$. A budget of
$q_L$ products with $\mathbf{A}^{\mathsf{H}}$ is the hypothesis `∀ τ, alg.leftCount τ ≤ q_L`. -/
noncomputable def leftCount (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) (τ : Fin q → R) :
    ℕ :=
  {j : Fin q | (alg.queries τ j).2 ≠ 0}.ncard

/-- A pair-query algorithm is **one-sided** when it makes no product with
$\mathbf{A}^{\mathsf{H}}$: every left part is zero, for every transcript. -/
def IsOneSided (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) : Prop :=
  ∀ τ, alg.leftCount τ = 0

end TwoSided

/-- The algorithm **truncated** to its first `i` queries, with no output: its transcript is the
history of length `i` (`QueryAlgorithm.transcript_truncate`). Inductions over the number of
queries (deferred decision) run through it. -/
def truncate (alg : QueryAlgorithm Q R q β) (i : ℕ) : QueryAlgorithm Q R i Unit where
  query := alg.query
  output _ := ()

/-- The truncated algorithm has the same histories. -/
@[simp]
theorem history_truncate (alg : QueryAlgorithm Q R q β) (f : Q → R) (i j : ℕ) :
    (alg.truncate i).history f j = alg.history f j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [history, history, ih]; rfl

/-- The transcript of the truncated algorithm is the history of length `i`. -/
@[simp]
theorem transcript_truncate (alg : QueryAlgorithm Q R q β) (f : Q → R) (i : ℕ) :
    (alg.truncate i).transcript f = alg.history f i :=
  history_truncate alg f i i

/-- A query algorithm is **non-adaptive** when each of its `q` queries is the same for every
history: the queries are fixed in advance (the sketching model). For pair queries both parts are
fixed in advance: a one-pass algorithm with $\ell$ products with $\mathbf{A}$ and $p$ with
$\mathbf{A}^{\mathsf{H}}$ is `IsNonAdaptive` with `rightCount ≤ ℓ` and `leftCount ≤ p`. -/
def IsNonAdaptive (alg : QueryAlgorithm Q R q β) : Prop :=
  ∀ i < q, ∀ h h' : Fin i → R, alg.query i h = alg.query i h'

/-- A query algorithm is **pass-structured** with pass map `pass : ℕ → ℕ` when its rounds are
grouped into passes, round `i` in pass `pass i`, the passes in order (`pass` is monotone), and
each query depends only on the responses of earlier passes: two histories that agree on every
round of a pass before `pass i` give the same query `i`. The queries of one pass form a block
chosen before any of its responses is seen. A `p`-pass algorithm is one with the further
hypothesis `∀ i < q, pass i < p`. Every algorithm is pass-structured with `pass = id`, one query
per pass (`QueryAlgorithm.isPassStructured_id`); with `pass = 0` it is non-adaptive
(`QueryAlgorithm.isPassStructured_zero_iff_isNonAdaptive`). -/
structure IsPassStructured (alg : QueryAlgorithm Q R q β) (pass : ℕ → ℕ) : Prop where
  /-- The passes come in order. -/
  monotone : Monotone pass
  /-- Query `i` depends only on the responses of the passes before `pass i`. -/
  query_eq : ∀ i < q, ∀ h h' : Fin i → R,
    (∀ j : Fin i, pass j < pass i → h j = h' j) → alg.query i h = alg.query i h'

/-- The algorithm reading its responses through `f : R' → R`: it makes the queries `alg` makes
on the responses `f r`, so against an oracle `O'` it runs `alg` against `f ∘ O'`
(`QueryAlgorithm.run_comapResponse`). A stronger oracle simulates a weaker one this way: the
matrix–vector oracle $\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ is the first component of
`hiddenRotationOracle`. -/
def comapResponse {R' : Type*} (f : R' → R) (alg : QueryAlgorithm Q R q β) :
    QueryAlgorithm Q R' q β where
  query i h := alg.query i (f ∘ h)
  output h := alg.output (f ∘ h)

/-- The algorithm with its output post-processed by `g : β → β'`; the queries are those of
`alg` (`QueryAlgorithm.run_mapOutput`). -/
def mapOutput {β' : Type*} (g : β → β') (alg : QueryAlgorithm Q R q β) :
    QueryAlgorithm Q R q β' where
  query := alg.query
  output h := g (alg.output h)

/-- Send each query through a map, keeping the response history and output unchanged.
Against an oracle $O'$, this simulates the original algorithm against $O' \circ f$.
Together with `QueryAlgorithm.comapResponse`, this transports a query model along a
reindexing or an embedding without giving the algorithm access to the input matrix. -/
def mapQuery {Q' : Type*} (f : Q → Q') (alg : QueryAlgorithm Q R q β) :
    QueryAlgorithm Q' R q β where
  query i h := f (alg.query i h)
  output := alg.output

/-- A query algorithm is **measurable** when each of its `q` query maps and the output map are
measurable (for the product σ-algebras on histories); the unused maps `query i`, $i \ge q$, are
unconstrained. Lower bounds quantify over these. -/
structure IsMeasurable [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β]
    (alg : QueryAlgorithm Q R q β) : Prop where
  /-- Each of the `q` query maps is measurable. -/
  measurable_query : ∀ i < q, Measurable (alg.query i)
  /-- The output map is measurable. -/
  measurable_output : Measurable alg.output

/-- A seeded family of query algorithms, a **randomized algorithm** with seed space `S`, is
measurable when its query and output maps are jointly measurable in the seed and the history. -/
structure IsMeasurableFamily {S : Type*} [MeasurableSpace S] [MeasurableSpace Q]
    [MeasurableSpace R] [MeasurableSpace β] (alg : S → QueryAlgorithm Q R q β) : Prop where
  /-- Each of the `q` query maps is jointly measurable in the seed and the history. -/
  measurable_query : ∀ i < q, Measurable fun p : S × (Fin i → R) => (alg p.1).query i p.2
  /-- The output map is jointly measurable in the seed and the transcript. -/
  measurable_output : Measurable fun p : S × (Fin q → R) => (alg p.1).output p.2

/-- The decoding of the Gram simulation: from a history of `2 * i` two-sided rounds, the first
components of the odd responses, the `i` responses of the simulated algorithm
(`QueryAlgorithm.gramDecode_history_gramSimulation`). -/
def gramDecode {𝕜 d k : Type*} {i : ℕ} (h : Fin (2 * i) → (d → 𝕜) × (k → 𝕜)) : Fin i → d → 𝕜 :=
  fun l => (h ⟨2 * l + 1, by have := l.isLt; omega⟩).1

/-- The **Gram simulation**: from an algorithm with `q` queries to
$\mathbf{A} = \mathbf{X}\mathbf{X}^{\mathsf{H}}$ (`X : Matrix d k 𝕜`), an algorithm with `2q`
rounds against `twoSidedMulVec X` with the same output. Round `2i` is the left query
$(\mathbf{0}, \mathbf{x}_i)$, which returns $\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$ in the second
component; round `2i + 1` is the right query $(\mathbf{X}^{\mathsf{H}}\mathbf{x}_i, \mathbf{0})$,
which returns $\mathbf{X}\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$ in the first. So it makes at most
`q` products with each of $\mathbf{X}$ and $\mathbf{X}^{\mathsf{H}}$. The original responses are the
first components of the odd responses (`QueryAlgorithm.gramDecode`,
`QueryAlgorithm.run_gramSimulation`). It makes explicit
what [ZhangEtAl2026, Section 4.1] uses implicitly: the analysis works with the factor
$\mathbf{X}$ while the queries are to $\mathbf{X}\mathbf{X}^{\mathsf{T}}$. -/
def gramSimulation {𝕜 d : Type*} [Zero 𝕜] (k : Type*) (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β) :
    QueryAlgorithm ((k → 𝕜) × (d → 𝕜)) ((d → 𝕜) × (k → 𝕜)) (2 * q) β where
  query j h :=
    if hj : j % 2 = 0 then
      (0, alg.query (j / 2) (gramDecode (h ∘ Fin.castLE (by omega))))
    else
      ((h ⟨j - 1, by omega⟩).2, 0)
  output h := alg.output (gramDecode h)

end QueryAlgorithm

end NLAlib

open MeasureTheory
open scoped Matrix

namespace NLAlib

/-- The two-sided oracle is jointly measurable in the matrix and the query. -/
@[fun_prop]
theorem Measurable.twoSidedMulVec {α m n : Type*} [MeasurableSpace α] [Fintype m]
    [Fintype n] {f : α → Matrix m n ℝ} {v : α → (n → ℝ) × (m → ℝ)} (hf : Measurable f)
    (hv : Measurable v) : Measurable fun a => twoSidedMulVec (f a) (v a) :=
  (hf.matrix_mulVec hv.fst).prodMk
    ((Measurable.matrix_conjTranspose continuous_star.measurable hf).matrix_mulVec hv.snd)

namespace QueryAlgorithm

variable {Q R β : Type*} {q : ℕ}

/-! ### Running an algorithm -/

/-- Responses are oracle values: the `j`-th of the first `i` responses of an algorithm run
against the oracle $f$ is $f$ at the `j`-th query, $h_j = f(x_j)$. -/
theorem history_apply (alg : QueryAlgorithm Q R q β) (f : Q → R) (i : ℕ) (j : Fin i) :
    alg.history f i j = f (alg.queryAt f j) := by
  induction i with
  | zero => exact j.elim0
  | succ i ih =>
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [history, Fin.snoc_last]
      rfl
    · rw [history, Fin.snoc_castSucc, ih]
      rfl

/-- Entries of a history do not depend on the length of the history. -/
private theorem history_eq_history (alg : QueryAlgorithm Q R q β) (f : Q → R) {n m j : ℕ}
    (hn : j < n) (hm : j < m) : alg.history f n ⟨j, hn⟩ = alg.history f m ⟨j, hm⟩ := by
  rw [history_apply, history_apply]

/-- The queries made are the queries of the transcript: the `j`-th query of an algorithm run
against $f$ is `queries` evaluated at its transcript. -/
theorem queryAt_eq_queries_transcript (alg : QueryAlgorithm Q R q β) (f : Q → R) (j : Fin q) :
    alg.queryAt f j = alg.queries (alg.transcript f) j := by
  unfold queryAt queries transcript
  congr 1
  funext l
  exact history_eq_history alg f l.isLt (l.isLt.trans j.isLt)

/-- Indistinguishability: if a second oracle $g$ agrees with $f$ at every query the algorithm
makes against $f$, then the algorithm makes the same queries against $g$ and gets the same
transcript. This is the deterministic half of every adversary and deferred-decision argument. -/
theorem transcript_eq_of_forall_apply_queries_eq (alg : QueryAlgorithm Q R q β) {f g : Q → R}
    (h : ∀ j, g (alg.queries (alg.transcript f) j) = f (alg.queries (alg.transcript f) j)) :
    alg.transcript g = alg.transcript f := by
  have key : ∀ i, i ≤ q → alg.history g i = alg.history f i := by
    intro i
    induction i with
    | zero => intro _; funext j; exact j.elim0
    | succ i ih =>
      intro hi
      have hq : i < q := hi
      have hgf := h ⟨i, hq⟩
      rw [← queryAt_eq_queries_transcript alg f ⟨i, hq⟩] at hgf
      unfold history
      rw [ih (by omega)]
      congr 1
  exact key q le_rfl

/-- Indistinguishability of outputs: if $g$ agrees with $f$ at every query the algorithm makes
against $f$, the algorithm outputs the same value against both. -/
theorem run_eq_of_forall_apply_queries_eq (alg : QueryAlgorithm Q R q β) {f g : Q → R}
    (h : ∀ j, g (alg.queries (alg.transcript f) j) = f (alg.queries (alg.transcript f) j)) :
    alg.run g = alg.run f :=
  congrArg alg.output (transcript_eq_of_forall_apply_queries_eq alg h)

/-- Non-adaptive queries are fixed: a non-adaptive algorithm makes the same queries whatever
the responses, so `queries` does not depend on the transcript. -/
theorem IsNonAdaptive.queries_eq {alg : QueryAlgorithm Q R q β} (h : alg.IsNonAdaptive)
    (τ τ' : Fin q → R) : alg.queries τ = alg.queries τ' := by
  funext j
  exact h j j.isLt _ _

/-! ### Measurability -/

section Measurable

variable [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β] {M : Type*}
  [MeasurableSpace M]

/-- The history of length $i \le q$ is measurable in the input: for a measurable algorithm and an
oracle $O_x$ depending jointly measurably on an input $x$ and the query, $x \mapsto$ history is
measurable. -/
theorem IsMeasurable.measurable_history {alg : QueryAlgorithm Q R q β}
    (halg : alg.IsMeasurable) {O : M → Q → R} (hO : Measurable (Function.uncurry O)) {i : ℕ}
    (hi : i ≤ q) : Measurable fun x => alg.history (O x) i := by
  induction i with
  | zero => exact measurable_pi_iff.2 fun j => j.elim0
  | succ i ih =>
    refine measurable_pi_iff.2 fun j => ?_
    induction j using Fin.lastCases with
    | last =>
      simp only [QueryAlgorithm.history, Fin.snoc_last]
      exact hO.comp (measurable_id.prodMk
        ((halg.measurable_query i (by omega)).comp (ih (by omega))))
    | cast j =>
      simp only [QueryAlgorithm.history, Fin.snoc_castSucc]
      exact (measurable_pi_apply j).comp (ih (by omega))

/-- The transcript is measurable in the input: for a measurable algorithm and an oracle
$O_x$ depending jointly measurably on an input $x$ and the query, $x \mapsto$ transcript is
measurable. -/
theorem IsMeasurable.measurable_transcript {alg : QueryAlgorithm Q R q β}
    (halg : alg.IsMeasurable) {O : M → Q → R} (hO : Measurable (Function.uncurry O)) :
    Measurable fun x => alg.transcript (O x) :=
  halg.measurable_history hO le_rfl

/-- The output is measurable in the input, for a measurable algorithm and a jointly
measurable oracle. -/
theorem IsMeasurable.measurable_run {alg : QueryAlgorithm Q R q β} (halg : alg.IsMeasurable)
    {O : M → Q → R} (hO : Measurable (Function.uncurry O)) :
    Measurable fun x => alg.run (O x) :=
  halg.measurable_output.comp (halg.measurable_transcript hO)

/-- The query matrix is measurable in the transcript, for a measurable algorithm with vector
queries. This is what makes the projectors onto the query spans random matrices. -/
theorem IsMeasurable.measurable_queryMatrix {𝕜 n : Type*} [MeasurableSpace 𝕜]
    {alg : QueryAlgorithm (n → 𝕜) R q β} (halg : alg.IsMeasurable) :
    Measurable (alg.queryMatrix : (Fin q → R) → Matrix n (Fin q) 𝕜) := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_
  exact (measurable_pi_apply r).comp ((halg.measurable_query j j.isLt).comp
    (measurable_pi_iff.2 fun l => measurable_pi_apply _))

/-- The right query matrix is measurable in the transcript, for a measurable algorithm with
pair queries $(\mathbf{x}, \mathbf{y})$. -/
theorem IsMeasurable.measurable_rightQueryMatrix {𝕜 m n : Type*} [MeasurableSpace 𝕜]
    {alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β} (halg : alg.IsMeasurable) :
    Measurable (alg.rightQueryMatrix : (Fin q → R) → Matrix n (Fin q) 𝕜) := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_
  exact (measurable_pi_apply r).comp (measurable_fst.comp
    ((halg.measurable_query j j.isLt).comp (measurable_pi_iff.2 fun l => measurable_pi_apply _)))

/-- The left query matrix is measurable in the transcript, for a measurable algorithm with
pair queries $(\mathbf{x}, \mathbf{y})$. -/
theorem IsMeasurable.measurable_leftQueryMatrix {𝕜 m n : Type*} [MeasurableSpace 𝕜]
    {alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β} (halg : alg.IsMeasurable) :
    Measurable (alg.leftQueryMatrix : (Fin q → R) → Matrix m (Fin q) 𝕜) := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_
  exact (measurable_pi_apply r).comp
    (measurable_snd.comp ((halg.measurable_query j j.isLt).comp
      (measurable_pi_iff.2 fun l => measurable_pi_apply _)))

/-- The histories of a measurable seeded family, jointly measurable in the seed and the input. -/
theorem IsMeasurableFamily.measurable_history {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {O : M → Q → R}
    (hO : Measurable (Function.uncurry O)) :
    ∀ i ≤ q, Measurable fun p : S × M => (alg p.1).history (O p.2) i := by
  intro i
  induction i with
  | zero => intro _; exact measurable_const
  | succ i ih =>
    intro hi
    refine measurable_pi_iff.2 fun j => ?_
    induction j using Fin.lastCases with
    | last =>
      simp only [QueryAlgorithm.history, Fin.snoc_last]
      exact hO.comp (measurable_snd.prodMk ((halg.measurable_query i (by omega)).comp
        (measurable_fst.prodMk (ih (by omega)))))
    | cast j =>
      simp only [QueryAlgorithm.history, Fin.snoc_castSucc]
      exact (measurable_pi_apply j).comp (ih (by omega))

/-- A randomized algorithm has a jointly measurable output: for a measurable seeded family
and a jointly measurable oracle, (seed, input) $\mapsto$ output is measurable. -/
theorem IsMeasurableFamily.measurable_run {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {O : M → Q → R}
    (hO : Measurable (Function.uncurry O)) :
    Measurable fun p : S × M => (alg p.1).run (O p.2) :=
  halg.measurable_output.comp
    (measurable_fst.prodMk (halg.measurable_history hO q le_rfl))

/-- Each member of a measurable family is measurable: fixing the seed of a measurable
randomized algorithm gives a measurable deterministic one. -/
theorem IsMeasurableFamily.isMeasurable {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) (s : S) :
    (alg s).IsMeasurable :=
  ⟨fun i hi => (halg.measurable_query i hi).comp measurable_prodMk_left,
    halg.measurable_output.comp measurable_prodMk_left⟩

/-- Truncating a measurable algorithm keeps it measurable, for $i \le q$. -/
theorem IsMeasurable.truncate {alg : QueryAlgorithm Q R q β} (halg : alg.IsMeasurable) {i : ℕ}
    (hi : i ≤ q) : (alg.truncate i).IsMeasurable :=
  ⟨fun j hj => halg.measurable_query j (by omega), measurable_const⟩

end Measurable

/-! ### Costs of pair queries -/

section Count

variable {𝕜 m n : Type*} [Field 𝕜]

/-- A matrix whose columns vanish outside `S` has rank at most `S.ncard`. -/
private lemma rank_le_ncard_of_col_eq_zero {m : Type*} (M : Matrix m (Fin q) 𝕜)
    (S : Set (Fin q)) (h : ∀ j ∉ S, ∀ r, M r j = 0) : M.rank ≤ S.ncard := by
  classical
  have hS : S.Finite := Set.toFinite S
  have : Fintype S := hS.fintype
  let N : Matrix m S 𝕜 := fun r j => M r j
  let P : Matrix S (Fin q) 𝕜 := fun j k => if (j : Fin q) = k then 1 else 0
  have hMNP : M = N * P := by
    ext r k
    rw [Matrix.mul_apply]
    by_cases hk : k ∈ S
    · rw [Finset.sum_eq_single (⟨k, hk⟩ : S)]
      · simp [N, P]
      · intro b _ hb
        have : (b : Fin q) ≠ k := fun e => hb (Subtype.ext e)
        simp [N, P, this]
      · simp
    · rw [h k hk r]
      refine Eq.symm (Finset.sum_eq_zero fun b _ => ?_)
      have : (b : Fin q) ≠ k := fun e => hk (e ▸ b.2)
      simp [P, this]
  calc M.rank = (N * P).rank := by rw [← hMNP]
    _ ≤ N.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card S := Matrix.rank_le_card_width N
    _ = S.ncard := by rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- The right query span is bounded by the number of right products: the rank of the right
query matrix is at most the number of rounds with a nonzero right part. -/
theorem rank_rightQueryMatrix_le_rightCount (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β)
    (τ : Fin q → R) : (alg.rightQueryMatrix τ).rank ≤ alg.rightCount τ :=
  rank_le_ncard_of_col_eq_zero _ _ fun j hj r => by
    simp only [Set.mem_ofPred_eq, not_not] at hj
    simp [QueryAlgorithm.rightQueryMatrix, hj]

/-- The left query span is bounded by the number of left products: the rank of the left query
matrix is at most the number of rounds with a nonzero left part. -/
theorem rank_leftQueryMatrix_le_leftCount (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β)
    (τ : Fin q → R) : (alg.leftQueryMatrix τ).rank ≤ alg.leftCount τ :=
  rank_le_ncard_of_col_eq_zero _ _ fun j hj r => by
    simp only [Set.mem_ofPred_eq, not_not] at hj
    simp [QueryAlgorithm.leftQueryMatrix, hj]

end Count

/-! ### The Gram simulation -/

section Gram

variable {𝕜 d k : Type*} [RCLike 𝕜]

/-- Queries of an algorithm at equal indices, with the responses reindexed along the equality. -/
private theorem query_eq_of_index {Q R β : Type*} {q : ℕ} (alg : QueryAlgorithm Q R q β)
    {a b : ℕ} (hab : a = b) (F : Fin a → R) (G : Fin b → R)
    (hFG : ∀ m : Fin b, F (Fin.cast hab.symm m) = G m) : alg.query a F = alg.query b G := by
  subst hab
  congr 1
  funext m
  exact hFG m

/-- Even rounds of the Gram simulation are `(0, x)`. -/
private theorem gramSimulation_query_even {𝕜 d k : Type*} [Zero 𝕜]
    (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β) (l : ℕ)
    (h : Fin (2 * l) → (d → 𝕜) × (k → 𝕜)) :
    (alg.gramSimulation k).query (2 * l) h = (0, alg.query l fun m =>
      (h ⟨2 * m + 1, by have := m.isLt; omega⟩).1) := by
  simp only [QueryAlgorithm.gramSimulation]
  rw [dif_pos (Nat.mul_mod_right 2 l)]
  congr 1
  exact query_eq_of_index alg (Nat.mul_div_cancel_left l two_pos) _ _ fun m => rfl

/-- Odd rounds of the Gram simulation are `(x, 0)`, with `x` the left response of the round before.
-/
private theorem gramSimulation_query_odd {𝕜 d k : Type*} [Zero 𝕜]
    (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β) (l : ℕ)
    (h : Fin (2 * l + 1) → (d → 𝕜) × (k → 𝕜)) :
    (alg.gramSimulation k).query (2 * l + 1) h = ((h ⟨2 * l, by omega⟩).2, 0) := by
  simp only [QueryAlgorithm.gramSimulation]
  rw [dif_neg (by omega)]
  rfl

/-- The Gram simulation reproduces the history: after `2 * i` rounds of `alg.gramSimulation k`
against `twoSidedMulVec X`, the first components of the odd responses are the first `i`
responses of `alg` against $\mathbf{X}\mathbf{X}^{\mathsf{H}}$. Holds for every `i`. -/
theorem gramDecode_history_gramSimulation [Fintype d] [Fintype k]
    (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β) (X : Matrix d k 𝕜) (i : ℕ) :
    gramDecode ((alg.gramSimulation k).history (twoSidedMulVec X) (2 * i)) =
      alg.history (X * Xᴴ).mulVec i := by
  -- Odd round `2l + 1` returns `X * (Xᴴ * x_l)`, where `x_l` is the query `l` of the history.
  have key : ∀ l : ℕ, ((alg.gramSimulation k).history (twoSidedMulVec X) (2 * l + 2)
      ⟨2 * l + 1, by omega⟩).1 = (X * Xᴴ).mulVec (alg.queryAt (X * Xᴴ).mulVec l) := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
    have e1 : ((alg.gramSimulation k).history (twoSidedMulVec X) (2 * l + 2)
        ⟨2 * l + 1, by omega⟩).1
        = X *ᵥ ((alg.gramSimulation k).history (twoSidedMulVec X) (2 * l + 1)
          ⟨2 * l, by omega⟩).2 := by
      rw [history_apply]
      simp only [queryAt, gramSimulation_query_odd, twoSidedMulVec, Matrix.mulVec_zero]
    have e2 : ((alg.gramSimulation k).history (twoSidedMulVec X) (2 * l + 1)
        ⟨2 * l, by omega⟩).2
        = Xᴴ *ᵥ alg.query l (fun m => ((alg.gramSimulation k).history (twoSidedMulVec X)
          (2 * l) ⟨2 * m + 1, by have := m.isLt; omega⟩).1) := by
      rw [history_apply]
      simp only [queryAt, gramSimulation_query_even, twoSidedMulVec, Matrix.mulVec_zero]
    have e3 : (fun m : Fin l => ((alg.gramSimulation k).history (twoSidedMulVec X)
        (2 * l) ⟨2 * m + 1, by have := m.isLt; omega⟩).1) = alg.history (X * Xᴴ).mulVec l := by
      funext m
      rw [history_eq_history _ _ (n := 2 * l) (m := 2 * m + 2) (j := 2 * m + 1) (by omega)
        (by omega)]
      rw [ih m m.isLt, history_apply]
    rw [e1, e2, e3, Matrix.mulVec_mulVec]
    rfl
  funext l
  rw [gramDecode, history_eq_history _ _ (n := 2 * i) (m := 2 * l + 2)
    (by have := l.isLt; omega) (by omega), key l, history_apply]

/-- Round `2l` of the Gram simulation is the left query $(\mathbf{0}, \mathbf{x}_l)$. -/
theorem queryAt_gramSimulation_two_mul [Fintype d] [Fintype k]
    (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β) (Y : Matrix d k 𝕜) (l : ℕ) :
    (alg.gramSimulation k).queryAt (twoSidedMulVec Y) (2 * l) =
      (0, alg.queryAt (Y * Yᴴ).mulVec l) := by
  have h := gramDecode_history_gramSimulation alg Y l
  rw [queryAt]
  generalize (alg.gramSimulation k).history (twoSidedMulVec Y) (2 * l) = H at h ⊢
  dsimp only [gramSimulation]
  rw [dif_pos (by omega)]
  have key : ∀ (n : ℕ) (hn : n = l) (f : Fin n → d → 𝕜),
      alg.query n f = alg.query l fun m => f (Fin.cast hn.symm m) := by
    rintro n rfl f; rfl
  refine Prod.ext rfl ((key _ (by omega) _).trans ?_)
  exact congrArg (alg.query l) h

/-- Round `2l + 1` of the Gram simulation is the right query
$(\mathbf{Y}^{\mathsf{H}}\mathbf{x}_l, \mathbf{0})$. -/
theorem queryAt_gramSimulation_two_mul_add_one [Fintype d] [Fintype k]
    (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β) (Y : Matrix d k 𝕜) (l : ℕ) :
    (alg.gramSimulation k).queryAt (twoSidedMulVec Y) (2 * l + 1) =
      (Yᴴ *ᵥ alg.queryAt (Y * Yᴴ).mulVec l, 0) := by
  have h := history_apply (alg.gramSimulation k) (twoSidedMulVec Y) (2 * l + 1) ⟨2 * l, by omega⟩
  rw [queryAt_gramSimulation_two_mul] at h
  rw [queryAt]
  generalize (alg.gramSimulation k).history (twoSidedMulVec Y) (2 * l + 1) = H at h ⊢
  dsimp only [gramSimulation]
  rw [dif_neg (by omega)]
  refine Prod.ext ?_ rfl
  change (H ⟨2 * l, by omega⟩).2 = _
  rw [h]
  rfl

/-- **The Gram simulation runs the original algorithm**: the `2q`-round algorithm
`alg.gramSimulation k` against `twoSidedMulVec X`, $\mathbf{X} \in \Bbbk^{d \times k}$, outputs
what `alg` outputs against $\mathbf{X}\mathbf{X}^{\mathsf{H}}$. Two-sided queries to the factor
$\mathbf{X}$ therefore simulate products with $\mathbf{X}\mathbf{X}^{\mathsf{H}}$, at `q` products
with each of $\mathbf{X}$ and $\mathbf{X}^{\mathsf{H}}$
(`QueryAlgorithm.rightCount_gramSimulation_le`, `QueryAlgorithm.leftCount_gramSimulation_le`).
[ZhangEtAl2026, Section 4.1]; there implicit: the analysis works with the factor $\mathbf{X}$
while the queries are to $\mathbf{X}\mathbf{X}^{\mathsf{T}}$. -/
theorem run_gramSimulation [Fintype d] [Fintype k] (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β)
    (X : Matrix d k 𝕜) :
    (alg.gramSimulation k).run (twoSidedMulVec X) = alg.run (X * Xᴴ).mulVec := by
  unfold QueryAlgorithm.run QueryAlgorithm.transcript
  exact congrArg alg.output (gramDecode_history_gramSimulation alg X q)

/-- The Gram simulation of a measurable algorithm is measurable. -/
theorem IsMeasurable.gramSimulation [MeasurableSpace 𝕜] [MeasurableSpace β]
    {alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β} (halg : alg.IsMeasurable) :
    (alg.gramSimulation k).IsMeasurable := by
  refine ⟨fun j hj => ?_, ?_⟩
  · unfold QueryAlgorithm.gramSimulation
    by_cases hjm : j % 2 = 0
    · simp only [hjm, dite_true]
      refine measurable_const.prodMk ((halg.measurable_query (j / 2) (by omega)).comp ?_)
      exact measurable_pi_iff.2 fun l => measurable_fst.comp (measurable_pi_apply _)
    · simp only [hjm, dite_false]
      exact (measurable_snd.comp (measurable_pi_apply _)).prodMk measurable_const
  · refine halg.measurable_output.comp ?_
    exact measurable_pi_iff.2 fun l => measurable_fst.comp (measurable_pi_apply _)

/-- A set of rounds of one parity among `2 * q` rounds has at most `q` elements. -/
private theorem ncard_le_of_forall_mod_two_eq {J : Set (Fin (2 * q))} (r : ℕ)
    (h : ∀ j ∈ J, (j : ℕ) % 2 = r) : J.ncard ≤ q := by
  have key := Set.ncard_le_ncard_of_injOn (s := J) (t := (Set.univ : Set (Fin q)))
    (fun j : Fin (2 * q) => ⟨j / 2, by omega⟩) (fun _ _ => Set.mem_univ _) ?_ (Set.toFinite _)
  · simpa using key
  intro a ha b hb hab
  have := h a ha
  have := h b hb
  simp only [Fin.mk.injEq] at hab
  ext
  omega

/-- The Gram simulation makes at most `q` products with $\mathbf{X}$: for every transcript,
only odd-numbered rounds have a nonzero right part. -/
theorem rightCount_gramSimulation_le (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β)
    (τ : Fin (2 * q) → (d → 𝕜) × (k → 𝕜)) : (alg.gramSimulation k).rightCount τ ≤ q :=
  ncard_le_of_forall_mod_two_eq 1 fun j hj => by
    by_contra hodd
    apply hj
    simp only [QueryAlgorithm.queries, QueryAlgorithm.gramSimulation]
    rw [dif_pos (by omega)]

/-- The Gram simulation makes at most `q` products with $\mathbf{X}^{\mathsf{H}}$: for every
transcript, only even-numbered rounds have a nonzero left part. -/
theorem leftCount_gramSimulation_le (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β)
    (τ : Fin (2 * q) → (d → 𝕜) × (k → 𝕜)) : (alg.gramSimulation k).leftCount τ ≤ q :=
  ncard_le_of_forall_mod_two_eq 0 fun j hj => by
    by_contra h
    apply hj
    simp [QueryAlgorithm.queries, QueryAlgorithm.gramSimulation, h]

/-- The right queries of the Gram simulation span at most `q` dimensions: for every
transcript, the right query matrix has rank at most `q`. -/
theorem rank_rightQueryMatrix_gramSimulation_le
    (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β) (τ : Fin (2 * q) → (d → 𝕜) × (k → 𝕜)) :
    ((alg.gramSimulation k).rightQueryMatrix τ).rank ≤ q :=
  (QueryAlgorithm.rank_rightQueryMatrix_le_rightCount _ τ).trans
    (QueryAlgorithm.rightCount_gramSimulation_le alg τ)

end Gram

end QueryAlgorithm

end NLAlib

namespace NLAlib

namespace QueryAlgorithm

variable {Q R R' β β' : Type*} {q : ℕ}

/-- Mapping queries simulates precomposition of the oracle, at every history length. -/
theorem history_mapQuery {Q' : Type*} (f : Q → Q') (alg : QueryAlgorithm Q R q β)
    (O : Q' → R) (i : ℕ) :
    (alg.mapQuery f).history O i = alg.history (O ∘ f) i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [history, history, ih]; rfl

/-- Mapping queries does not change the number of rounds: the new run against $O$ is the
original run against $O \circ f$. This is an exact simulation, without probabilistic hypotheses. -/
theorem run_mapQuery {Q' : Type*} (f : Q → Q') (alg : QueryAlgorithm Q R q β) (O : Q' → R) :
    (alg.mapQuery f).run O = alg.run (O ∘ f) := by
  simp only [run, transcript, history_mapQuery]
  rfl

/-- Mapping queries preserves pass labels and their dependence on previous-pass responses. -/
theorem IsPassStructured.mapQuery {Q' : Type*} {alg : QueryAlgorithm Q R q β}
    {pass : ℕ → ℕ} (h : alg.IsPassStructured pass) (f : Q → Q') :
    (alg.mapQuery f).IsPassStructured pass :=
  ⟨h.monotone, fun i hi u v huv => congrArg f (h.query_eq i hi u v huv)⟩

/-- A measurable query map transports a measurable algorithm to the new query space. -/
theorem IsMeasurable.mapQuery {Q' : Type*} [MeasurableSpace Q] [MeasurableSpace Q']
    [MeasurableSpace R] [MeasurableSpace β] {alg : QueryAlgorithm Q R q β}
    (h : alg.IsMeasurable) {f : Q → Q'} (hf : Measurable f) :
    (alg.mapQuery f).IsMeasurable :=
  ⟨fun i hi => hf.comp (h.measurable_query i hi), h.measurable_output⟩

/-- A measurable query map transports a jointly measurable seeded family, with unchanged
seed law, query count and output type. -/
theorem IsMeasurableFamily.mapQuery {Q' S : Type*} [MeasurableSpace Q] [MeasurableSpace Q']
    [MeasurableSpace R] [MeasurableSpace β] [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (h : IsMeasurableFamily alg) {f : Q → Q'}
    (hf : Measurable f) : IsMeasurableFamily fun s => (alg s).mapQuery f :=
  ⟨fun i hi => hf.comp (h.measurable_query i hi), h.measurable_output⟩

/-- Reading the responses through $f$ reproduces the history: the history of
`alg.comapResponse f` against an oracle $O'$, read through $f$, is the history of `alg` against
$f \circ O'$, at every length $i$. -/
theorem history_comapResponse (f : R' → R) (alg : QueryAlgorithm Q R q β) (O : Q → R')
    (i : ℕ) : f ∘ (alg.comapResponse f).history O i = alg.history (f ∘ O) i := by
  induction i with
  | zero => funext x; exact x.elim0
  | succ i ih =>
    rw [history, history, Fin.comp_snoc, ← ih]
    rfl

/-- An algorithm reading its responses through $f$ against the oracle $O'$ outputs what `alg`
outputs against $f \circ O'$. So a lower bound for an oracle $O$ holds for every weaker oracle
$f \circ O$: the matrix–vector oracle is the first component of `hiddenRotationOracle`. -/
theorem run_comapResponse (f : R' → R) (alg : QueryAlgorithm Q R q β) (O : Q → R') :
    (alg.comapResponse f).run O = alg.run (f ∘ O) := by
  unfold QueryAlgorithm.run QueryAlgorithm.transcript
  rw [← history_comapResponse f alg O]
  rfl

/-- Post-processing the output does not change the history. -/
theorem history_mapOutput (g : β → β') (alg : QueryAlgorithm Q R q β) (O : Q → R) (i : ℕ) :
    (alg.mapOutput g).history O i = alg.history O i := by
  induction i with
  | zero => rfl
  | succ n ih => rw [history, history, ih]; rfl

/-- The output of `alg.mapOutput g` is $g$ of the output of `alg`. -/
theorem run_mapOutput (g : β → β') (alg : QueryAlgorithm Q R q β) (O : Q → R) :
    (alg.mapOutput g).run O = g (alg.run O) := by
  simp only [QueryAlgorithm.run, QueryAlgorithm.transcript, history_mapOutput]; rfl

section Measurable

variable [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace R'] [MeasurableSpace β]
  [MeasurableSpace β']

private theorem measurable_comp_left {n : ℕ} {f : R' → R} (hf : Measurable f) :
    Measurable fun h : Fin n → R' => f ∘ h :=
  measurable_pi_iff.2 fun j => hf.comp (measurable_pi_apply j)

/-- Reading the responses through a measurable map keeps an algorithm measurable. -/
theorem IsMeasurable.comapResponse {alg : QueryAlgorithm Q R q β} (halg : alg.IsMeasurable)
    {f : R' → R} (hf : Measurable f) : (alg.comapResponse f).IsMeasurable :=
  { measurable_query := fun i hi => (halg.measurable_query i hi).comp (measurable_comp_left hf)
    measurable_output := halg.measurable_output.comp (measurable_comp_left hf) }

/-- Post-processing the output by a measurable map keeps an algorithm measurable. -/
theorem IsMeasurable.mapOutput {alg : QueryAlgorithm Q R q β} (halg : alg.IsMeasurable)
    {g : β → β'} (hg : Measurable g) : (alg.mapOutput g).IsMeasurable := by
  exact ⟨halg.measurable_query, hg.comp halg.measurable_output⟩

/-- A measurable seeded family reading its responses through a measurable map is measurable. -/
theorem IsMeasurableFamily.comapResponse {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {f : R' → R}
    (hf : Measurable f) : IsMeasurableFamily fun s => (alg s).comapResponse f := by
  refine ⟨fun i hi => ?_, ?_⟩
  · exact (halg.measurable_query i hi).comp (measurable_fst.prodMk
      (measurable_pi_iff.2 fun j => hf.comp ((measurable_pi_apply j).comp measurable_snd)))
  · exact (halg.measurable_output).comp (measurable_fst.prodMk
      (measurable_pi_iff.2 fun j => hf.comp ((measurable_pi_apply j).comp measurable_snd)))

/-- A measurable seeded family with its output post-processed by a measurable map is measurable. -/
theorem IsMeasurableFamily.mapOutput {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {g : β → β'}
    (hg : Measurable g) : IsMeasurableFamily fun s => (alg s).mapOutput g :=
  ⟨halg.measurable_query, hg.comp halg.measurable_output⟩

end Measurable

/-- Reading the responses through a map keeps the pass structure. -/
theorem IsPassStructured.comapResponse {alg : QueryAlgorithm Q R q β} {pass : ℕ → ℕ}
    (h : alg.IsPassStructured pass) (f : R' → R) :
    (alg.comapResponse f).IsPassStructured pass :=
  ⟨h.monotone, fun i hi u u' huu' =>
    h.query_eq i hi _ _ fun j hj => by simp only [Function.comp_apply]; rw [huu' j hj]⟩

/-- Post-processing the output keeps the pass structure. -/
theorem IsPassStructured.mapOutput {alg : QueryAlgorithm Q R q β} {pass : ℕ → ℕ}
    (h : alg.IsPassStructured pass) (g : β → β') :
    (alg.mapOutput g).IsPassStructured pass := by
  exact ⟨h.monotone, h.query_eq⟩

/-- Every algorithm is pass-structured with one query per pass: with `pass = id` the
condition is that query $i$ depends only on the $i$ responses before it, which is the definition
of an adaptive algorithm. The fully adaptive model is the $q$-pass case. -/
theorem isPassStructured_id (alg : QueryAlgorithm Q R q β) : alg.IsPassStructured id :=
  ⟨monotone_id, fun i _ _ _ hh => congrArg (alg.query i) (funext fun j => hh j j.isLt)⟩

/-- One pass is non-adaptivity: an algorithm is pass-structured with every round in pass
$0$ if and only if it is non-adaptive. -/
theorem isPassStructured_zero_iff_isNonAdaptive (alg : QueryAlgorithm Q R q β) :
    alg.IsPassStructured (fun _ => 0) ↔ alg.IsNonAdaptive := by
  refine ⟨fun h i hi u u' => h.query_eq i hi u u' fun j hj => absurd hj (lt_irrefl _),
    fun h => ⟨monotone_const, fun i hi u u' _ => h i hi u u'⟩⟩

end QueryAlgorithm

end NLAlib
