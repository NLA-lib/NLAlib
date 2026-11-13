/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Basic
public import NLAlib.Probability.Law
public import NLAlib.Probability.SubGaussian.Square
public import NLAlib.RandomMatrix.SubGaussian.ExtremeSingularValues
public import NLAlib.Sketching.Properties.Isotropic
public import NLAlib.Sketching.Properties.JohnsonLindenstrauss

/-!
# Sub-Gaussian sketches

The sub-Gaussian sketch is $\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$ for a random
`X : Matrix k n ℝ` ($\lvert k \rvert$ rows) whose rows $\mathbf{X}_i$ are independent, isotropic
and sub-Gaussian with proxy $c$ (the three hypotheses of
`NLAlib/RandomMatrix/SubGaussian/ExtremeSingularValues.lean`, suffix `_of_isSubgaussianVector`,
always in the order `hind`, `hsub`, `hiso`). It is written out in each statement,
`fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω`; there is no named sketch law. Its isotropy is
`NLAlib.isIsotropicSketch_smul_of_isIsotropic` (no independence needed), so it gets no isotropy
statement here.

It has the distributional Johnson–Lindenstrauss property with Vershynin's two-regime
tail <!-- value subgaussianJLConstant -->
$2 e^{-(1/36) \lvert k \rvert \min(\varepsilon^2/c^2, \varepsilon/c)}$, the constant being
`subgaussianJLConstant` (Bernstein's inequality on the centred squares
$\langle \mathbf{X}_i, \mathbf{x} \rangle^2 - 1$), and, for rows with proxy $1$ and fourth
directional moments at most $3$, the tail
$2 e^{-\lvert k \rvert (\varepsilon^2/4 - \varepsilon^3/6)}$ of Dasgupta and Gupta (Achlioptas's
argument; incomparable, docs/contributing/statements.md §2 rule 4). It has the
JL moment property at $p = 2$ and, from the sub-exponential tail, at every $p > 0$, so
$O(c^2\log(1/\delta)/\varepsilon^2)$ rows give it at $p = \max(2, \log(1/\delta))$; sign
sketches are the case $c = 1$ (`NLAlib.isSubgaussianVector_of_hasLaw_rademacherVector`,
`NLAlib.isIsotropic_of_hasLaw_rademacherVector`, `ProbabilityTheory.HasLaw.iIndepFun_eval`),
with no separate statement. It is an oblivious subspace embedding and injection through JL
plus a net (`NLAlib.HasJLProperty.isObliviousSubspaceEmbedding` at $4\varepsilon/5$); that route
dominates the rows theorem's Gram sandwich in every regime.
Matrices with independent sub-Gaussian entries of unit variance reach the rows hypotheses through
`NLAlib.iIndepFun_row_of_iIndepFun_entry`; only their JL tail is stated. The sample sizes are
named quantities with nonnegativity, monotonicity and an explicit comparison.

Degenerate cases: for empty $k$, $\mathbf{S} = \mathbf{0}$, the JL bounds are $2$ and the OSE
bounds $2 \cdot 21^d$, all true, but $\mathbf{S}$ is not isotropic, hence `[Nonempty k]` on the OSI
and the moment. With rows and columns present the hypotheses force $c \ge 1$; for $c = 0$,
$\varepsilon/0 = 0$ and the bound is $2$. No $\varepsilon \ge 0$ on the Bernstein tails: for
$\varepsilon < 0$ the bound exceeds $2$. For $\varepsilon = 1$ the lower JL event is
$\{\mathbf{S}\mathbf{x} = \mathbf{0}\}$, which need not be null (for signs, probability
$2^{-\lvert k \rvert}$ at $\mathbf{x} = (\mathbf{e}_1 + \mathbf{e}_2)/\sqrt{2}$); for
$\varepsilon > 1$ it is empty, and the lower OSE constant $1 - \varepsilon \le 0$ is vacuous
(`NLAlib.isSubspaceInjection_of_nonpos`).

## Main definitions

* `NLAlib.subgaussianJLConstant`: the constant of the sub-Gaussian JL
  tail, <!-- value subgaussianJLConstant -->$C = 1/36$.
* `NLAlib.subgaussianJLDim`, `NLAlib.subgaussianEmbeddingDim`, `NLAlib.subgaussianJLMomentDim`:
  the sample sizes for
  JL <!-- value subgaussianJLDim c \varepsilon \delta -->$c^2 \log(2/\delta)/(C \varepsilon^2)$,
  for the OSE <!-- value subgaussianEmbeddingDim c d \varepsilon \delta -->
  $25 c^2 (d \log 21 + \log(2/\delta))/(16 C \varepsilon^2)$
  and for the JL moment <!-- value subgaussianJLMomentDim c \varepsilon \delta -->
  $16c^2\max(2, \log(1/\delta))/(C\varepsilon^2)$.

## Main results

* `NLAlib.hasJLProperty_of_isSubgaussianVector`: sub-Gaussian distributional JL.
* `NLAlib.hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le`: the Dasgupta–Gupta
  tail for proxy $1$ and Gaussian fourth moments.
* `NLAlib.hasJLMoment_of_isSubgaussianVector`: the JL moment property at $p = 2$.
* `NLAlib.hasJLMoment_subexponentialMomentBound_of_isSubgaussianVector`: at every $p > 0$, and
  its size form `NLAlib.hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`.
* `NLAlib.isObliviousSubspaceEmbedding_of_isSubgaussianVector`,
  `NLAlib.isObliviousSubspaceInjection_of_isSubgaussianVector`.
* `NLAlib.hasJLProperty_of_iIndepFun_entry`: JL for independent sub-Gaussian entries.
* `NLAlib.exists_forall_hasJLProperty_of_isSubgaussianVector`,
  `NLAlib.exists_forall_isObliviousSubspaceEmbedding_of_isSubgaussianVector`,
  `NLAlib.exists_forall_hasJLMoment_of_isSubgaussianVector`: the asymptotic
  forms, $O(c^2 \log(1/\delta)/\varepsilon^2)$ and $O(c^2 (d + \log(1/\delta))/\varepsilon^2)$
  rows. The projection-cost-preserving forms are in `NLAlib.Sketching.Gaussian.ProjectionCost`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal

namespace NLAlib

/-! ### Proof-local arithmetic -/

/-- $2 \cdot 21^d e^{-L} \le \delta$ once $d \log 21 + \log(2/\delta) \le L$, for $\delta > 0$. -/
private theorem two_mul_twentyOne_pow_mul_exp_le {d : ℕ} {L δ : ℝ} (hδ : 0 < δ)
    (h : d * Real.log 21 + Real.log (2 / δ) ≤ L) : 2 * 21 ^ d * Real.exp (-L) ≤ δ := by
  calc 2 * 21 ^ d * Real.exp (-L) ≤
        2 * 21 ^ d * Real.exp (-(d * Real.log 21 + Real.log (2 / δ))) := by
        gcongr
    _ = δ := by
      rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_nat_mul,
        Real.exp_log (by norm_num), Real.exp_log (by positivity)]
      field_simp

/-! ### The constant and the sample sizes -/

/-- The constant $C$ of the sub-Gaussian JL tail
$2 e^{-C \lvert k \rvert \min(\varepsilon^2/c^2, \varepsilon/c)}$, proved
with <!-- value subgaussianJLConstant -->$C = 1/36$. Unspecified in
[Vershynin2018, Exercise 5.3.3, Theorem 2.8.1]. The
proof gives the centred square the parameters $(18 c^2, 18 c)$
(`ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral_of_le`), which
Bernstein's inequality turns into $\min(\varepsilon^2/(36 c^2), \varepsilon/(36 c))$: the window
$18c$ is the one at which the two regimes have the same constant. Honorio and Jaakkola's
$(32 c^2, 4 c)$ give $\min(\varepsilon^2/(64 c^2), \varepsilon/(8 c))$, so $1/64$ in this shape.
Larger is better; consumers use only `subgaussianJLConstant_pos` and
`le_subgaussianJLConstant`. -/
noncomputable irreducible_def subgaussianJLConstant : ℝ := 1 / 36

/-- The sub-Gaussian JL constant is positive. -/
theorem subgaussianJLConstant_pos : 0 < subgaussianJLConstant := by
  rw [subgaussianJLConstant_def]
  norm_num

/-- The explicit lower bound $1/36$ on `subgaussianJLConstant`, whose value
is <!-- value subgaussianJLConstant -->$1/36$. -/
theorem le_subgaussianJLConstant : 1 / 36 ≤ subgaussianJLConstant := by
  rw [subgaussianJLConstant_def]

/-- The **sub-Gaussian JL dimension** <!-- value subgaussianJLDim c \varepsilon \delta -->
$c^2 \log(2/\delta)/(C \varepsilon^2)$, with <!-- value subgaussianJLConstant -->$C = 1/36$
(`subgaussianJLConstant`): for $0 < \varepsilon \le c$ and $\delta > 0$, at least this many rows
give the JL property with distortion $\varepsilon$ and failure probability $\delta$
(`NLAlib.hasJLProperty_of_isSubgaussianVector_of_subgaussianJLDim_le`). Junk: for $\delta > 2$
the logarithm is negative, and the value is $0$ at $\varepsilon = 0$. -/
noncomputable irreducible_def subgaussianJLDim (c ε δ : ℝ) : ℝ :=
  c ^ 2 * Real.log (2 / δ) / (subgaussianJLConstant * ε ^ 2)

/-- The **sub-Gaussian embedding
dimension** <!-- value subgaussianEmbeddingDim c d \varepsilon \delta -->
$25 c^2 (d \log 21 + \log(2/\delta))/(16 C \varepsilon^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$ (`subgaussianJLConstant`): for
$0 < \varepsilon \le 5c/4$ and $\delta > 0$, at least this many rows
give an oblivious subspace embedding for dimension $d$ with constants $1 \mp \varepsilon$ and
failure probability $\delta$
(`NLAlib.isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le`): the
JL size at distortion $4\varepsilon/5$ for the $21^d$ points of a $1/10$-net.
Junk: the value is $0$ at $\varepsilon = 0$, and negative for $\delta > 2 \cdot 21^d$. -/
noncomputable irreducible_def subgaussianEmbeddingDim (c : ℝ) (d : ℕ) (ε δ : ℝ) : ℝ :=
  25 * c ^ 2 * (d * Real.log 21 + Real.log (2 / δ)) / (16 * subgaussianJLConstant * ε ^ 2)

/-- The **sub-Gaussian JL moment
dimension** <!-- value subgaussianJLMomentDim c \varepsilon \delta -->
$16c^2\max(2, \log(1/\delta))/(C\varepsilon^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$ (`subgaussianJLConstant`): for
$0 < \varepsilon \le c$ and $\delta > 0$, at least this many rows give the JL moment property
with distortion $\varepsilon$, failure probability $\delta$ and exponent $\max(2, \log(1/\delta))$
(`NLAlib.hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`). The value the proof
reaches, inverting the readable form of the sub-exponential moment bound
(`NLAlib.subexponentialMomentBound_le`) at $v = c^2/(2C\lvert k\rvert)$,
$b = c/(2C\lvert k\rvert)$; a Stirling-sharp inversion would lower the $16$ without a statement
change. Junk: $0$ at $\varepsilon = 0$. -/
noncomputable irreducible_def subgaussianJLMomentDim (c ε δ : ℝ) : ℝ :=
  16 * c ^ 2 * max 2 (Real.log (1 / δ)) / (subgaussianJLConstant * ε ^ 2)

section Sizes

variable {c c' ε ε' δ δ' : ℝ} {d d' : ℕ}

/-- The sub-Gaussian JL dimension is nonnegative for $0 < \delta \le 2$. -/
theorem subgaussianJLDim_nonneg (c ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    0 ≤ subgaussianJLDim c ε δ := by
  rw [subgaussianJLDim_def]
  exact div_nonneg (mul_nonneg (sq_nonneg c) (Real.log_nonneg ((one_le_div₀ hδ).2 hδ2)))
    (mul_nonneg subgaussianJLConstant_pos.le (sq_nonneg ε))

/-- The sub-Gaussian JL dimension is monotone in $c \ge 0$ and antitone in $\varepsilon > 0$ and
$\delta > 0$ (for $\delta \le 2$). -/
theorem subgaussianJLDim_mono (hc : 0 ≤ c) (hcc' : c ≤ c') (hε : 0 < ε) (hεε' : ε ≤ ε')
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') (hδ2 : δ ≤ 2) :
    subgaussianJLDim c ε' δ' ≤ subgaussianJLDim c' ε δ := by
  have hL := Real.log_nonneg ((one_le_div₀ hδ).2 hδ2)
  have hC := subgaussianJLConstant_pos
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  rw [subgaussianJLDim_def, subgaussianJLDim_def]
  rcases le_or_gt 0 (Real.log (2 / δ')) with hL' | hL'
  · have hLL : Real.log (2 / δ') ≤ Real.log (2 / δ) := by gcongr
    have hcc : c ^ 2 ≤ c' ^ 2 := pow_le_pow_left₀ hc hcc' 2
    refine div_le_div₀ (mul_nonneg (sq_nonneg _) hL) (mul_le_mul hcc hLL hL' (sq_nonneg _))
      (by positivity) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hεε' 2) hC.le)
  · refine (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) hL'.le) (by positivity)).trans ?_
    exact div_nonneg (mul_nonneg (sq_nonneg _) hL) (by positivity)

/-- An explicit upper bound on the sub-Gaussian JL dimension: it is at most
$36 c^2 \log(2/\delta) / \varepsilon^2$ for $0 < \delta \le 2$. -/
theorem subgaussianJLDim_le (c ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    subgaussianJLDim c ε δ ≤ 36 * c ^ 2 * Real.log (2 / δ) / ε ^ 2 := by
  rw [subgaussianJLDim_def]
  rcases eq_or_ne ε 0 with rfl | hε
  · simp
  calc c ^ 2 * Real.log (2 / δ) / (subgaussianJLConstant * ε ^ 2)
      ≤ c ^ 2 * Real.log (2 / δ) / (1 / 36 * ε ^ 2) :=
        div_le_div_of_nonneg_left
          (mul_nonneg (sq_nonneg c) (Real.log_nonneg ((one_le_div₀ hδ).2 hδ2))) (by positivity)
          (mul_le_mul_of_nonneg_right le_subgaussianJLConstant (sq_nonneg ε))
    _ = 36 * c ^ 2 * Real.log (2 / δ) / ε ^ 2 := by field_simp

/-- The sub-Gaussian embedding dimension is nonnegative for $0 < \delta \le 2$. -/
theorem subgaussianEmbeddingDim_nonneg (c : ℝ) (d : ℕ) (ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    0 ≤ subgaussianEmbeddingDim c d ε δ := by
  rw [subgaussianEmbeddingDim_def]
  have h21 : 0 ≤ Real.log 21 := Real.log_nonneg (by norm_num)
  exact div_nonneg (mul_nonneg (by positivity)
      (add_nonneg (mul_nonneg (Nat.cast_nonneg d) h21) (Real.log_nonneg ((one_le_div₀ hδ).2 hδ2))))
    (mul_nonneg (mul_nonneg (by norm_num) subgaussianJLConstant_pos.le) (sq_nonneg ε))

/-- The sub-Gaussian embedding dimension is monotone in $c \ge 0$ and in $d$, and antitone in
$\varepsilon > 0$ and $\delta > 0$ (for $\delta \le 2$). -/
theorem subgaussianEmbeddingDim_mono (hc : 0 ≤ c) (hcc' : c ≤ c') (hd : d ≤ d') (hε : 0 < ε)
    (hεε' : ε ≤ ε') (hδ : 0 < δ) (hδδ' : δ ≤ δ') (hδ2 : δ ≤ 2) :
    subgaussianEmbeddingDim c d ε' δ' ≤ subgaussianEmbeddingDim c' d' ε δ := by
  have hL := Real.log_nonneg ((one_le_div₀ hδ).2 hδ2)
  have hC := subgaussianJLConstant_pos
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  have h21 : 0 ≤ Real.log 21 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ (d' : ℝ) * Real.log 21 + Real.log (2 / δ) :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) h21) hL
  rw [subgaussianEmbeddingDim_def, subgaussianEmbeddingDim_def]
  rcases le_or_gt 0 ((d : ℝ) * Real.log 21 + Real.log (2 / δ')) with hL' | hL'
  · have hLL : (d : ℝ) * Real.log 21 + Real.log (2 / δ') ≤
        d' * Real.log 21 + Real.log (2 / δ) := by
      have hdd : (d : ℝ) ≤ d' := by exact_mod_cast hd
      have : Real.log (2 / δ') ≤ Real.log (2 / δ) := by gcongr
      nlinarith
    have hcc : 25 * c ^ 2 ≤ 25 * c' ^ 2 := by
      have := pow_le_pow_left₀ hc hcc' 2
      linarith
    refine div_le_div₀ (mul_nonneg (by positivity) hA) (mul_le_mul hcc hLL hL' (by positivity))
      (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hεε' 2) (by positivity))
  · refine (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hL'.le) (by positivity)).trans ?_
    exact div_nonneg (mul_nonneg (by positivity) hA) (by positivity)

/-- An explicit upper bound on the sub-Gaussian embedding dimension,
$172 c^2 (d + \log(2/\delta)) / \varepsilon^2$ for $0 < \delta \le 2$ ($(225/4) \log 21 \le 172$):
[Woodruff2014, Theorem 6]'s $\Theta((d + \log(1/\delta))/\varepsilon^2)$ with an explicit
constant. -/
theorem subgaussianEmbeddingDim_le (c : ℝ) (d : ℕ) (ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    subgaussianEmbeddingDim c d ε δ ≤ 172 * c ^ 2 * (d + Real.log (2 / δ)) / ε ^ 2 := by
  rw [subgaussianEmbeddingDim_def, subgaussianJLConstant_def]
  have hL := Real.log_nonneg ((one_le_div₀ hδ).2 hδ2)
  have h21 : (d : ℝ) * Real.log 21 ≤ d * (61 / 20) :=
    mul_le_mul_of_nonneg_left Real.log_twentyOne_le_sixtyOne_div_twenty (Nat.cast_nonneg d)
  have e : 25 * c ^ 2 * (d * Real.log 21 + Real.log (2 / δ)) / (16 * (1 / 36) * ε ^ 2) =
      225 / 4 * c ^ 2 * (d * Real.log 21 + Real.log (2 / δ)) / ε ^ 2 := by
    rcases eq_or_ne ε 0 with rfl | hε
    · simp
    field_simp
    ring
  rw [e]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
  have hc := sq_nonneg c
  nlinarith [mul_le_mul_of_nonneg_left h21 hc, mul_nonneg hc hL]

/-- The sub-Gaussian JL moment dimension is nonnegative. -/
theorem subgaussianJLMomentDim_nonneg (c ε δ : ℝ) : 0 ≤ subgaussianJLMomentDim c ε δ := by
  rw [subgaussianJLMomentDim_def]
  have : (0 : ℝ) ≤ max 2 (Real.log (1 / δ)) := le_max_of_le_left zero_le_two
  have := subgaussianJLConstant_pos
  positivity

/-- The sub-Gaussian JL moment dimension is monotone in $c \ge 0$ and antitone in
$\varepsilon > 0$ and $\delta > 0$. -/
theorem subgaussianJLMomentDim_mono (hc : 0 ≤ c) (hcc' : c ≤ c') (hε : 0 < ε) (hεε' : ε ≤ ε')
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') :
    subgaussianJLMomentDim c ε' δ' ≤ subgaussianJLMomentDim c' ε δ := by
  rw [subgaussianJLMomentDim_def, subgaussianJLMomentDim_def]
  have hC := subgaussianJLConstant_pos
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  have hM : (0 : ℝ) ≤ max 2 (Real.log (1 / δ')) := le_max_of_le_left zero_le_two
  have hL : Real.log (1 / δ') ≤ Real.log (1 / δ) := by gcongr
  calc 16 * c ^ 2 * max 2 (Real.log (1 / δ')) / (subgaussianJLConstant * ε' ^ 2)
      ≤ 16 * c ^ 2 * max 2 (Real.log (1 / δ')) / (subgaussianJLConstant * ε ^ 2) := by gcongr
    _ ≤ 16 * c' ^ 2 * max 2 (Real.log (1 / δ)) / (subgaussianJLConstant * ε ^ 2) := by gcongr

/-- An explicit upper bound on the sub-Gaussian JL moment dimension: it is at most
$1728 c^2 \log(1/\delta)/\varepsilon^2$ for $0 < \delta \le 1/2$, where
$\max(2, \log(1/\delta)) \le 3\log(1/\delta)$. -/
theorem subgaussianJLMomentDim_le (c ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    subgaussianJLMomentDim c ε δ ≤ 1728 * c ^ 2 * Real.log (1 / δ) / ε ^ 2 := by
  rw [subgaussianJLMomentDim_def]
  rcases eq_or_ne ε 0 with rfl | hε
  · simp
  have h2 := Real.log_two_le_log_one_div hδ hδ2
  have hl2 := Real.log_two_gt_d9
  have hmax : max 2 (Real.log (1 / δ)) ≤ 3 * Real.log (1 / δ) :=
    max_le (by linarith) (by linarith)
  have hL : 0 ≤ Real.log (1 / δ) := by linarith
  calc 16 * c ^ 2 * max 2 (Real.log (1 / δ)) / (subgaussianJLConstant * ε ^ 2)
      ≤ 16 * c ^ 2 * (3 * Real.log (1 / δ)) / (1 / 36 * ε ^ 2) := by
        gcongr
        exact le_subgaussianJLConstant
    _ = 1728 * c ^ 2 * Real.log (1 / δ) / ε ^ 2 := by field_simp; ring

end Sizes

/-! ### Independent isotropic sub-Gaussian rows -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n : Type*} [Fintype k]
  [Fintype n] {X : Ω → Matrix k n ℝ} {c : ℝ≥0} {ε δ : ℝ} {d : ℕ}

/-- The fourth moment of a sub-Gaussian variable $Y$ with proxy $c$: $\mathbb{E}[Y^4] \le 16 c^2$
(`HasSubgaussianMGF.integral_abs_rpow_le` at $p = 4$). -/
private theorem integral_pow_four_le {Y : Ω → ℝ} (h : HasSubgaussianMGF Y c μ) :
    ∫ ω, Y ω ^ 4 ∂μ ≤ 16 * (c : ℝ) ^ 2 := by
  have h4 := h.integral_abs_rpow_le (p := 4) (by norm_num)
  have hpt (ω : Ω) : |Y ω| ^ (4 : ℝ) = Y ω ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_abs,
      abs_of_nonneg (by positivity)]
  simp only [hpt] at h4
  have hΓ : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial, Nat.factorial_one,
      Nat.cast_one]
  rw [show (4 : ℝ) / 2 = 2 by norm_num, Real.rpow_two, hΓ] at h4
  linarith

/-- The centred sum of squares of independent $Y_i$, $i \in \iota$, sub-Gaussian with proxy $c$,
with $\mathbb{E}[Y_i^2] = 1$: it is square integrable and
$\mathbb{E}\bigl(\sum_i (Y_i^2 - 1)\bigr)^2 \le \lvert \iota \rvert (16 c^2 - 1)$. -/
private theorem integral_sum_sq_sub_one_sq_le {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ}
    (hind : iIndepFun Y μ) (hsub : ∀ i, HasSubgaussianMGF (Y i) c μ)
    (h2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = 1) :
    MemLp (fun ω => ∑ i, (Y i ω ^ 2 - 1)) 2 μ ∧
      ∫ ω, (∑ i, (Y i ω ^ 2 - 1)) ^ 2 ∂μ ≤ Fintype.card ι * (16 * (c : ℝ) ^ 2 - 1) := by
  have := hind.isProbabilityMeasure
  set Z : ι → Ω → ℝ := fun i ω => Y i ω ^ 2 - 1 with hZ
  have hpow (i : ι) (m : ℕ) : Integrable (fun ω => Y i ω ^ m) μ :=
    integrable_pow_of_integrable_exp_mul one_ne_zero ((hsub i).integrable_exp_mul 1)
      ((hsub i).integrable_exp_mul (-1)) m
  have hZm (i : ι) : AEStronglyMeasurable (Z i) μ :=
    ((hsub i).aemeasurable.pow_const 2 |>.sub_const 1).aestronglyMeasurable
  have hsq (i : ι) (ω : Ω) : Z i ω ^ 2 = Y i ω ^ 4 - 2 * Y i ω ^ 2 + 1 := by
    simp only [hZ]
    ring
  have hZ2 (i : ι) : Integrable (fun ω => Z i ω ^ 2) μ := by
    simp only [hsq]
    exact (((hpow i 4).sub ((hpow i 2).const_mul 2)).add (integrable_const 1))
  have hZL (i : ι) : MemLp (Z i) 2 μ := (memLp_two_iff_integrable_sq (hZm i)).2 (hZ2 i)
  have hZ0 (i : ι) : ∫ ω, Z i ω ∂μ = 0 := by
    simp only [hZ]
    rw [integral_sub (hpow i 2) (integrable_const 1), h2, integral_const, probReal_univ,
      one_smul, sub_self]
  have hZsq (i : ι) : ∫ ω, Z i ω ^ 2 ∂μ ≤ 16 * (c : ℝ) ^ 2 - 1 := by
    simp only [hsq]
    have hA : Integrable (fun ω => Y i ω ^ 4 - 2 * Y i ω ^ 2) μ :=
      (hpow i 4).sub ((hpow i 2).const_mul 2)
    rw [integral_add hA (integrable_const 1),
      integral_sub (hpow i 4) ((hpow i 2).const_mul 2), integral_const_mul, h2,
      integral_const, probReal_univ, one_smul]
    linarith [integral_pow_four_le (hsub i)]
  have hfun : (fun ω => ∑ i, Z i ω) = ∑ i, Z i := by
    ext ω
    simp only [Finset.sum_apply]
  have hSL : MemLp (∑ i, Z i) 2 μ := memLp_finsetSum' _ fun i _ => hZL i
  have hZind : iIndepFun Z μ :=
    hind.comp (fun _ y => y ^ 2 - 1) (fun _ => by fun_prop)
  have hvar : variance (∑ i, Z i) μ = ∑ i, variance (Z i) μ :=
    IndepFun.variance_sum (fun i _ => hZL i) fun i _ j _ hij => hZind.indepFun hij
  have hS0 : μ[∑ i, Z i] = 0 := by
    rw [← hfun, integral_finsetSum _ fun i _ => (hZL i).integrable one_le_two]
    simp only [hZ0, Finset.sum_const_zero]
  refine ⟨by rw [show (fun ω => ∑ i, (Y i ω ^ 2 - 1)) = ∑ i, Z i from hfun]; exact hSL, ?_⟩
  have hvar' : ∫ ω, (∑ i, (Y i ω ^ 2 - 1)) ^ 2 ∂μ = ∑ i, ∫ ω, Z i ω ^ 2 ∂μ := by
    have e1 := variance_eq_integral hSL.aemeasurable (μ := μ)
    rw [hS0] at e1
    rw [hvar] at e1
    simp only [sub_zero, Finset.sum_apply] at e1
    rw [← e1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [variance_eq_integral (hZL i).aemeasurable, hZ0]
    simp only [sub_zero]
  rw [hvar']
  calc ∑ i, ∫ ω, Z i ω ^ 2 ∂μ ≤ ∑ _i : ι, (16 * (c : ℝ) ^ 2 - 1) :=
        Finset.sum_le_sum fun i _ => hZsq i
    _ = Fintype.card ι * (16 * (c : ℝ) ^ 2 - 1) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

section Rows

variable [DecidableEq n]

/-- **Sub-Gaussian distributional JL**: for a random $\mathbf{X}$ with independent, isotropic,
sub-Gaussian rows with proxy $c$, the sketch $\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$
has the JL property at every $\varepsilon$: for every
unit $\mathbf{x}$, <!-- value subgaussianJLConstant -->
$$\mathbb{P}\bigl[\varepsilon \le \lvert \|\mathbf{S}\mathbf{x}\|^2 - 1 \rvert\bigr]
\le 2 e^{-\frac{1}{36} \lvert k \rvert \min(\varepsilon^2/c^2, \, \varepsilon/c)} \,,$$
the constant being `subgaussianJLConstant`. [Vershynin2018, Exercise 5.3.3], there
with an unspecified constant. For proxy $1$ and fourth directional moments at most $3$,
`NLAlib.hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le` is better for
$\varepsilon \lesssim 1.43$ and this one beyond.
Result: jl-subgaussian -/
theorem hasJLProperty_of_isSubgaussianVector (hind : iIndepFun (fun i ω => X ω i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      (2 * Real.exp (-(subgaussianJLConstant * Fintype.card k *
        min (ε ^ 2 / (c : ℝ) ^ 2) (ε / c)))) μ := by
  have := hind.isProbabilityMeasure
  intro x hx
  have hC := subgaussianJLConstant_pos
  rcases le_or_gt (subgaussianJLConstant * Fintype.card k *
    min (ε ^ 2 / (c : ℝ) ^ 2) (ε / c)) 0 with h0 | h0
  · refine measureReal_le_one.trans ?_
    have : 1 ≤ Real.exp (-(subgaussianJLConstant * Fintype.card k *
        min (ε ^ 2 / (c : ℝ) ^ 2) (ε / c))) := Real.one_le_exp (by linarith)
    linarith
  rw [mul_assoc] at h0
  have hKm := pos_of_mul_pos_right h0 hC.le
  have hK0 : (0 : ℝ) < Fintype.card k := by
    refine lt_of_le_of_ne (Nat.cast_nonneg _) fun h => ?_
    rw [← h, zero_mul] at hKm
    exact lt_irrefl _ hKm
  have hm := pos_of_mul_pos_right hKm hK0.le
  have hεc : 0 < ε / c := hm.trans_le (min_le_right _ _)
  have hc : (0 : ℝ) < c := by
    refine lt_of_le_of_ne c.2 fun h => ?_
    rw [← h, div_zero] at hεc
    exact lt_irrefl _ hεc
  have hε : 0 < ε := by
    have := mul_pos hεc hc
    rwa [div_mul_cancel₀ _ hc.ne'] at this
  have hZ := hasSubexponentialMGF_norm_mulVec_sq_sub_of_isSubgaussianVector hind hsub hiso hx
    (v := 18 * c ^ 2) (b := 18 * c) (mul_le_mul_of_nonneg_right (by norm_num) c.2)
    (by push_cast; nlinarith [pow_nonneg c.coe_nonneg 3])
  have hev : {ω | ε ≤ |‖WithLp.toLp 2 (((√(Fintype.card k : ℝ))⁻¹ • X ω) *ᵥ x)‖ ^ 2 - 1|} =
      {ω | ε * Fintype.card k ≤ |‖WithLp.toLp 2 (X ω *ᵥ x)‖ ^ 2 - Fintype.card k|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Matrix.smul_mulVec,
      EuclideanSpace.norm_toLp_inv_sqrt_card_smul_sq]
    rw [div_sub_one hK0.ne', abs_div, abs_of_pos hK0, le_div_iff₀ hK0]
  rw [hev]
  refine (hZ.measureReal_abs_ge_le (by positivity)).trans ?_
  gcongr
  push_cast
  rw [subgaussianJLConstant_def]
  refine le_min ?_ ?_
  · have e : (ε * Fintype.card k) ^ 2 / (2 * (18 * (c : ℝ) ^ 2 * Fintype.card k)) =
        1 / 36 * Fintype.card k * (ε ^ 2 / (c : ℝ) ^ 2) := by
      field_simp
      ring
    rw [e]
    gcongr
    exact min_le_left _ _
  · have e : ε * Fintype.card k / (2 * (18 * (c : ℝ))) = 1 / 36 * Fintype.card k * (ε / c) := by
      field_simp
      ring
    rw [e]
    gcongr
    exact min_le_right _ _

/-- **Dasgupta–Gupta tail for rows with Gaussian fourth moments**: for a random $\mathbf{X}$ with
independent, isotropic rows $\mathbf{X}_i$, sub-Gaussian with proxy $1$, with
$\mathbb{E} \langle \mathbf{x}, \mathbf{X}_i \rangle^4 \le 3 \|\mathbf{x}\|^4$ for every
$\mathbf{x}$, and $\varepsilon \ge 0$, the sketch
$\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$ has the JL property with failure probability
$$2 e^{-\lvert k \rvert (\varepsilon^2/4 - \varepsilon^3/6)} \,,$$
the Gaussian sketch's
(`NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix`). From
`NLAlib.measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun` at
$Y_i = \langle \mathbf{X}_i, \mathbf{x} \rangle$.
[Woodruff2014, §2.1, after Theorem 6] attributes this to Achlioptas for signs. Incomparable
with `NLAlib.hasJLProperty_of_isSubgaussianVector` at $c = 1$
(docs/contributing/statements.md §2 rule 4): this
one is better for $\varepsilon \lesssim 1.43$ (sixteen times the exponent at small
$\varepsilon$), that one beyond, and needs no fourth-moment hypothesis.
Result: jl-subgaussian -/
theorem hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) 1 μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ)
    (h4 : ∀ i (x : n → ℝ), ∫ ω, (x ⬝ᵥ X ω i) ^ 4 ∂μ ≤ 3 * ‖WithLp.toLp 2 x‖ ^ 4) (hε : 0 ≤ ε) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      (2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6)))) μ := by
  have := hind.isProbabilityMeasure
  intro x hx
  have hxn : ‖WithLp.toLp 2 x‖₊ = 1 := by rw [← NNReal.coe_eq_one, coe_nnnorm, hx]
  have hY : iIndepFun (fun i ω => x ⬝ᵥ X ω i) μ :=
    hind.comp (fun _ v => x ⬝ᵥ v) (fun _ => by simp only [dotProduct]; fun_prop)
  have hsubY (i : k) : HasSubgaussianMGF (fun ω => x ⬝ᵥ X ω i) 1 μ := by
    have h := (hsub i).hasSubgaussianMGF x
    rw [hxn, one_pow, mul_one] at h
    simpa only [RCLike.re_to_real] using h
  have h2 (i : k) : ∫ ω, (x ⬝ᵥ X ω i) ^ 2 ∂μ = 1 := by
    have h2 := (hiso i).integral_norm_dotProduct_sq x
    simpa only [Real.norm_eq_abs, sq_abs, hx, one_pow] using h2
  have h4' (i : k) : ∫ ω, (x ⬝ᵥ X ω i) ^ 4 ∂μ ≤ 3 := by
    have h := h4 i x
    rwa [hx, one_pow, mul_one] at h
  have h := measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun hY hsubY h2 h4' hε
  simp only [norm_inv_sqrt_card_smul_mulVec_sq, Real.norm_eq_abs, sq_abs]
  exact h

/-- **Sub-Gaussian JL moment** at $p = 2$: for a random $\mathbf{X}$ with $k$ independent,
isotropic, sub-Gaussian rows $\mathbf{X}_i$ with proxy $c$, $k$ nonempty, the sketch
$\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$ and unit $\mathbf{x}$,
$\mathbb{E}(\|\mathbf{S}\mathbf{x}\|^2 - 1)^2$ is
$(\mathbb{E} \langle \mathbf{X}_i, \mathbf{x} \rangle^4 - 1)/\lvert k \rvert$ on average over the
rows, and $\mathbb{E} \langle \mathbf{X}_i, \mathbf{x} \rangle^4 \le 16 c^2$
(`HasSubgaussianMGF.integral_abs_rpow_le` at $p = 4$), so the JL moment property holds for
$\varepsilon > 0$ with $\delta = (16 c^2 - 1)/(\lvert k \rvert \varepsilon^2)$. [Woodruff2014,
Definition 12] for the property; the constant is the closed form of the sub-Gaussian fourth
moment bound. -/
theorem hasJLMoment_of_isSubgaussianVector [Nonempty k] (hind : iIndepFun (fun i ω => X ω i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (hε : 0 < ε) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      ((16 * (c : ℝ) ^ 2 - 1) / (Fintype.card k * ε ^ 2)) 2 μ := by
  have := hind.isProbabilityMeasure
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have key (x : n → ℝ) (hx : ‖WithLp.toLp 2 x‖ = 1) :
      MemLp (fun ω => ∑ i, ((x ⬝ᵥ X ω i) ^ 2 - 1)) 2 μ ∧
        ∫ ω, (∑ i, ((x ⬝ᵥ X ω i) ^ 2 - 1)) ^ 2 ∂μ ≤
          Fintype.card k * (16 * (c : ℝ) ^ 2 - 1) := by
    have hxn : ‖WithLp.toLp 2 x‖₊ = 1 := by rw [← NNReal.coe_eq_one, coe_nnnorm, hx]
    have hY : iIndepFun (fun i ω => x ⬝ᵥ X ω i) μ :=
      hind.comp (fun _ v => x ⬝ᵥ v) (fun _ => by simp only [dotProduct]; fun_prop)
    refine integral_sum_sq_sub_one_sq_le hY (fun i => ?_) fun i => ?_
    · have h := (hsub i).hasSubgaussianMGF x
      rw [hxn, one_pow, mul_one] at h
      simpa only [RCLike.re_to_real] using h
    · have h2 := (hiso i).integral_norm_dotProduct_sq x
      simpa only [Real.norm_eq_abs, sq_abs, hx, one_pow] using h2
  have e (x : n → ℝ) (ω : Ω) :
      |‖WithLp.toLp 2 (((√(Fintype.card k : ℝ))⁻¹ • X ω) *ᵥ x)‖ ^ 2 - 1| ^ (2 : ℝ) =
        (∑ i, ((x ⬝ᵥ X ω i) ^ 2 - 1)) ^ 2 / (Fintype.card k : ℝ) ^ 2 := by
    rw [Real.rpow_two, sq_abs, norm_inv_sqrt_card_smul_mulVec_sq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      div_sub_one hK.ne', div_pow]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp only [e]
    exact (key x hx).1.integrable_sq.div_const _
  · simp only [e]
    rw [integral_div, Real.rpow_two]
    calc (∫ ω, (∑ i, ((x ⬝ᵥ X ω i) ^ 2 - 1)) ^ 2 ∂μ) / (Fintype.card k : ℝ) ^ 2
        ≤ Fintype.card k * (16 * (c : ℝ) ^ 2 - 1) / (Fintype.card k : ℝ) ^ 2 := by
          gcongr
          exact (key x hx).2
      _ = ε ^ 2 * ((16 * (c : ℝ) ^ 2 - 1) / (Fintype.card k * ε ^ 2)) := by
          field_simp

/-- **Sub-Gaussian OSE**: for a random $\mathbf{X}$ with independent, isotropic, sub-Gaussian rows
with proxy $c$, $\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$ is an oblivious subspace
embedding for dimension $d$ with constants $1 \mp \varepsilon$ and failure
probability <!-- value subgaussianJLConstant -->
$$2 \cdot 21^d \, e^{-\frac{1}{36} \lvert k \rvert
\min(16\varepsilon^2/(25c^2), \, 4\varepsilon/(5c))} \,,$$
the constant being `subgaussianJLConstant`: JL plus a net of radius $1/10$ at $4\varepsilon/5$
(`NLAlib.HasJLProperty.isObliviousSubspaceEmbedding`). [Vershynin2018, Theorem 4.6.1, (4.22)],
there for the singular values, $K^2 \max(\delta, \delta^2)$ with an unspecified
constant; it dominates the rows theorem's Gram sandwich in every regime.

Result: subgaussian-ose -/
theorem isObliviousSubspaceEmbedding_of_isSubgaussianVector (hind : iIndepFun (fun i ω => X ω i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (d : ℕ) :
    IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) (1 + ε)
      (2 * 21 ^ d * Real.exp (-(subgaussianJLConstant * Fintype.card k *
        min (16 * ε ^ 2 / (25 * (c : ℝ) ^ 2)) (4 * ε / (5 * c))))) μ := by
  have := hind.isProbabilityMeasure
  have h := (hasJLProperty_of_isSubgaussianVector (ε := 4 * ε / 5) hind hsub
    hiso).isObliviousSubspaceEmbedding (by positivity) d
  rw [Module.finrank_self, mul_one,
    show 1 - 5 / 4 * (4 * ε / 5) = 1 - ε by ring, show 1 + 5 / 4 * (4 * ε / 5) = 1 + ε by ring,
    show (4 * ε / 5) ^ 2 / (c : ℝ) ^ 2 = 16 * ε ^ 2 / (25 * (c : ℝ) ^ 2) by ring,
    show 4 * ε / 5 / (c : ℝ) = 4 * ε / (5 * c) by ring] at h
  exact h.mono le_rfl le_rfl le_rfl (le_of_eq (by ring))

/-- **Sub-Gaussian OSI**: for a random $\mathbf{X}$ with $k$ independent, isotropic,
sub-Gaussian rows with proxy $c$, $k$ nonempty, the sketch
$\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$ is an oblivious subspace injection for
dimension $d$ with constant $1 - \varepsilon$ and failure
probability <!-- value subgaussianJLConstant -->
$$2 \cdot 21^d \, e^{-(1/36) \lvert k \rvert
\min(16\varepsilon^2/(25c^2), \, 4\varepsilon/(5c))}\,:$$
the lower half of `NLAlib.isObliviousSubspaceEmbedding_of_isSubgaussianVector`, with the sketch's
isotropy (`NLAlib.isIsotropicSketch_smul_of_isIsotropic`). [Vershynin2018, Theorem 4.6.1];
[CamanoEpperlyMeyerTropp2025, Definition 1.2] for the notion. -/
theorem isObliviousSubspaceInjection_of_isSubgaussianVector [Nonempty k]
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (d : ℕ) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε)
      (2 * 21 ^ d * Real.exp (-(subgaussianJLConstant * Fintype.card k *
        min (16 * ε ^ 2 / (25 * (c : ℝ) ^ 2)) (4 * ε / (5 * c))))) μ := by
  have := hind.isProbabilityMeasure
  exact (isObliviousSubspaceEmbedding_of_isSubgaussianVector hind hsub hiso
    d).isObliviousSubspaceInjection (isIsotropicSketch_smul_of_isIsotropic hiso)

/-- **Sub-Gaussian JL, sample-size form**: for a random $\mathbf{X}$ with independent,
isotropic, sub-Gaussian rows with proxy $c$, $0 < \varepsilon \le c$, $\delta > 0$ and at
least <!-- value subgaussianJLDim c \varepsilon \delta -->$c^2 \log(2/\delta)/(C \varepsilon^2)$
rows (`subgaussianJLDim c ε δ`, with <!-- value subgaussianJLConstant -->$C = 1/36$ the
constant `subgaussianJLConstant`), the sketch $\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$
has the JL property with distortion $\varepsilon$ and failure
probability $\delta$ (for $\varepsilon \le c$ the $\min$ of the tail is its quadratic part).
[Vershynin2018, Exercise 5.3.3]. Asymptotic form:
`NLAlib.exists_forall_hasJLProperty_of_isSubgaussianVector`.
Result: jl-subgaussian -/
theorem hasJLProperty_of_isSubgaussianVector_of_subgaussianJLDim_le
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (hε : 0 < ε) (hεc : ε ≤ c) (hδ : 0 < δ)
    (hk : subgaussianJLDim c ε δ ≤ Fintype.card k) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε δ μ := by
  have := hind.isProbabilityMeasure
  have hc : (0 : ℝ) < c := hε.trans_le hεc
  have hC := subgaussianJLConstant_pos
  have hmin : min (ε ^ 2 / (c : ℝ) ^ 2) (ε / c) = ε ^ 2 / (c : ℝ) ^ 2 := by
    refine min_eq_left ?_
    rw [div_le_div_iff₀ (by positivity) hc]
    have : ε ^ 2 * c ≤ ε * c ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hεc (mul_nonneg hε.le hc.le)]
    linarith
  refine (hasJLProperty_of_isSubgaussianVector hind hsub hiso).mono le_rfl ?_
  rw [hmin]
  rw [subgaussianJLDim_def, div_le_iff₀ (by positivity)] at hk
  have hL : ((0 : ℕ) : ℝ) * Real.log 21 + Real.log (2 / δ) ≤
      subgaussianJLConstant * Fintype.card k * (ε ^ 2 / (c : ℝ) ^ 2) := by
    rw [Nat.cast_zero, zero_mul, zero_add, mul_div_assoc', le_div_iff₀ (by positivity)]
    linarith
  simpa only [pow_zero, mul_one, Nat.cast_zero] using
    two_mul_twentyOne_pow_mul_exp_le (d := 0) hδ hL

/-- Sub-Gaussian JL, asymptotic form: $O(c^2 \log(1/\delta)/\varepsilon^2)$ rows suffice for
the sketch with independent isotropic rows, sub-Gaussian with proxy $c$, to have the JL property
with distortion $\varepsilon$ and failure probability $\delta$, for $\varepsilon$ and $\delta$ below
absolute constants; the constants come before every dimension and the proxy. Proved from
`NLAlib.hasJLProperty_of_isSubgaussianVector_of_subgaussianJLDim_le` with $C = 72$,
$\varepsilon_0 = 1$ and $\delta \le 1/2$; isotropy forces $c \ge 1$ once there is a column.
Asymptotic: NLAlib.hasJLProperty_of_isSubgaussianVector_of_subgaussianJLDim_le -/
theorem exists_forall_hasJLProperty_of_isSubgaussianVector :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      [DecidableEq n] [Nonempty k] (μ : Measure Ω) (X : Ω → Matrix k n ℝ) (c : ℝ≥0) (ε δ : ℝ),
      iIndepFun (fun i ω => X ω i) μ → (∀ i, IsSubgaussianVector (fun ω => X ω i) c μ) →
      (∀ i, IsIsotropic (fun ω => X ω i) μ) → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((c : ℝ) ^ 2 * Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card k →
      HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε δ μ := by
  refine ⟨72, 1, by norm_num, one_pos, ?_⟩
  intro Ω k n _ _ _ _ _ μ X c ε δ hind hsub hiso hε hε1 hδ hδ2 hk
  have := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty n with hn | hn
  · intro x hx
    rw [Subsingleton.elim x 0] at hx
    simp at hx
  have hc : 1 ≤ (c : ℝ) :=
    (hsub (Classical.arbitrary k)).one_le_of_isIsotropic (hiso (Classical.arbitrary k))
  have hl1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hl2 := Real.log_two_div_le_two_mul_log_one_div hδ hδ2
  refine hasJLProperty_of_isSubgaussianVector_of_subgaussianJLDim_le hind hsub hiso hε
    (by linarith) hδ ((subgaussianJLDim_le c ε hδ (by linarith)).trans (le_trans ?_ hk))
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right
    (by nlinarith [mul_le_mul_of_nonneg_left hl2 (sq_nonneg (c : ℝ))]) (sq_nonneg ε)

/-- **Sub-Gaussian JL moments at every order**: for a random $\mathbf{X}$ with $k$ independent,
isotropic, sub-Gaussian rows with proxy $c$, $k$ nonempty, the sketch
$\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$, $\varepsilon > 0$ and $p > 0$, the JL moment
property holds with exponent $p$ and failure probability $\delta = \beta/\varepsilon^p$,
with <!-- value subexponentialMomentBound (c^2/(2C\lvert{k}\rvert)) (c/(2C\lvert{k}\rvert)) p -->
$$\beta = p(2(c^2/(2C\lvert{k}\rvert)))^{p/2}\Gamma(p/2) +
2p(2(c/(2C\lvert{k}\rvert)))^{p}\Gamma(p)\,,$$
with <!-- value subgaussianJLConstant -->$C = 1/36$ (`subgaussianJLConstant`), $\beta$ being
`NLAlib.subexponentialMomentBound` at the parameters of the sub-Gaussian JL tail
$2e^{-C\lvert k\rvert\min(t^2/c^2, t/c)}$ (`NLAlib.hasJLProperty_of_isSubgaussianVector`), which
`NLAlib.hasJLMoment_of_forall_hasJLProperty` integrates. Incomparable with
`NLAlib.hasJLMoment_of_isSubgaussianVector` (the fourth moment, better at $p = 2$). Sign sketches
are the case $c = 1$. [Woodruff2014, Definition 12] for the property; that dense sketches have it
at $p = \log(1/\delta)$ follows from [KaneNelson2014, Remark 22]. -/
theorem hasJLMoment_subexponentialMomentBound_of_isSubgaussianVector [Nonempty k]
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (hε : 0 < ε) {p : ℝ} (hp : 0 < p) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      (subexponentialMomentBound ((c : ℝ) ^ 2 / (2 * subgaussianJLConstant * Fintype.card k))
        ((c : ℝ) / (2 * subgaussianJLConstant * Fintype.card k)) p / ε ^ p) p μ := by
  have := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty n with hn | hn
  · refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    · rw [Subsingleton.elim x 0] at hx
      simp at hx
  have hc : 1 ≤ (c : ℝ) :=
    (hsub (Classical.arbitrary k)).one_le_of_isIsotropic (hiso (Classical.arbitrary k))
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have hC := subgaussianJLConstant_pos
  have hX : AEMeasurable X μ := aemeasurable_pi_lambda X fun i => (hsub i).aemeasurable
  refine hasJLMoment_of_forall_hasJLProperty (S := fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω)
    (hX.const_smul ((√(Fintype.card k : ℝ))⁻¹)) (by positivity) (by positivity)
    (fun t ht => ?_) hε hp
  refine (hasJLProperty_of_isSubgaussianVector (ε := t) hind hsub hiso).mono le_rfl
    (le_of_eq ?_)
  have hc0 : (0 : ℝ) < c := by linarith
  have e1 : t ^ 2 / (2 * ((c : ℝ) ^ 2 / (2 * subgaussianJLConstant * Fintype.card k))) =
      subgaussianJLConstant * Fintype.card k * (t ^ 2 / (c : ℝ) ^ 2) := by
    field_simp
  have e2 : t / (2 * ((c : ℝ) / (2 * subgaussianJLConstant * Fintype.card k))) =
      subgaussianJLConstant * Fintype.card k * (t / c) := by
    field_simp
  rw [e1, e2, ← mul_min_of_nonneg _ _ (by positivity)]

/-- **Sub-Gaussian JL moments, sample-size form**: for a random $\mathbf{X}$ with independent,
isotropic, sub-Gaussian rows with proxy $c$, $0 < \varepsilon \le c$, $\delta > 0$ and at
least <!-- value subgaussianJLMomentDim c \varepsilon \delta -->
$16c^2\max(2, \log(1/\delta))/(C\varepsilon^2)$ rows (`subgaussianJLMomentDim c ε δ`,
with <!-- value subgaussianJLConstant -->$C = 1/36$ the constant `subgaussianJLConstant`), the
sketch $\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$ has the JL moment property with
distortion $\varepsilon$, failure probability $\delta$ and exponent
$$\max(2, \log(1/\delta)) \,;$$
approximate matrix multiplication with failure probability $\delta$ follows
(`NLAlib.HasJLMoment.measureReal_frobNorm_conjTranspose_mul_sub_ge_le`). Sign sketches are the
case $c = 1$. [Woodruff2014, Definition 12 and Theorem 13], the property and AMM from it; the
size $O(\log(1/\delta)/\varepsilon^2)$ follows from [KaneNelson2014, Remark 22], the
constants are this proof's. Asymptotic form:
`NLAlib.exists_forall_hasJLMoment_of_isSubgaussianVector`.
Result: jl-moment-subgaussian -/
theorem hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (hε : 0 < ε) (hεc : ε ≤ c) (hδ : 0 < δ)
    (hk : subgaussianJLMomentDim c ε δ ≤ Fintype.card k) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε δ (max 2 (Real.log (1 / δ))) μ := by
  set p := max 2 (Real.log (1 / δ)) with hpdef
  have hp2 : 2 ≤ p := le_max_left _ _
  have hp0 : 0 < p := by linarith
  have hc0 : (0 : ℝ) < c := hε.trans_le hεc
  have hC := subgaussianJLConstant_pos
  have hD : 0 < subgaussianJLConstant * ε ^ 2 := by positivity
  have hK : 16 * (c : ℝ) ^ 2 * p ≤ subgaussianJLConstant * ε ^ 2 * Fintype.card k := by
    rw [subgaussianJLMomentDim_def, div_le_iff₀ hD] at hk
    linarith
  have hK0 : (0 : ℝ) < Fintype.card k := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hD.le h, mul_pos (pow_pos hc0 2) hp0]
  have : Nonempty k := Fintype.card_pos_iff.1 (by exact_mod_cast hK0)
  have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
  have hCK : 0 < 2 * subgaussianJLConstant * Fintype.card k := by positivity
  have hb := subexponentialMomentBound_le_mul_exp_neg
    (v := (c : ℝ) ^ 2 / (2 * subgaussianJLConstant * Fintype.card k))
    (b := (c : ℝ) / (2 * subgaussianJLConstant * Fintype.card k)) (by positivity) (by positivity)
    hp2 hε (by rw [div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ hCK]; nlinarith)
    (by
      rw [div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ hCK]
      nlinarith [mul_le_mul_of_nonneg_left hεc (mul_nonneg hε.le (mul_nonneg hC.le hK0.le))])
  refine (hasJLMoment_subexponentialMomentBound_of_isSubgaussianVector hind hsub hiso hε
    hp0).mono le_rfl ?_ hε.le hp0.le (div_nonneg (subexponentialMomentBound_nonneg (by positivity)
      (by positivity) hp0.le) hεp.le)
  rw [div_le_iff₀ hεp, mul_comm δ]
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ hεp.le)
  calc Real.exp (-p) ≤ Real.exp (-Real.log (1 / δ)) :=
        Real.exp_le_exp.2 (neg_le_neg (le_max_right _ _))
    _ = δ := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]

/-- **Sub-Gaussian JL moments, asymptotic form**: $O(c^2\log(1/\delta)/\varepsilon^2)$ rows
suffice for the sketch with independent isotropic rows, sub-Gaussian with proxy $c$, to have the
JL moment property with distortion $\varepsilon$, failure probability $\delta$ and exponent
$$\max(2, \log(1/\delta)) \,,$$
for $\varepsilon$ and $\delta$ below absolute constants; the constants
come before every dimension and the proxy. Proved from
`NLAlib.hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le` with $C = 1728$,
$\varepsilon_0 = 1$ and $\delta \le 1/2$; isotropy forces $c \ge 1$ once there is a column.
[Woodruff2014, Definition 12 and Theorem 13].
Asymptotic: NLAlib.hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le
Result: jl-moment-subgaussian -/
theorem exists_forall_hasJLMoment_of_isSubgaussianVector :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      [DecidableEq n] [Nonempty k] (μ : Measure Ω) (X : Ω → Matrix k n ℝ) (c : ℝ≥0) (ε δ : ℝ),
      iIndepFun (fun i ω => X ω i) μ → (∀ i, IsSubgaussianVector (fun ω => X ω i) c μ) →
      (∀ i, IsIsotropic (fun ω => X ω i) μ) → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((c : ℝ) ^ 2 * Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card k →
      HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε δ (max 2 (Real.log (1 / δ))) μ := by
  refine ⟨1728, 1, by norm_num, one_pos, ?_⟩
  intro Ω k n _ _ _ _ _ μ X c ε δ hind hsub hiso hε hε1 hδ hδ2 hk
  have := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty n with hn | hn
  · refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    · rw [Subsingleton.elim x 0] at hx
      simp at hx
  have hc : 1 ≤ (c : ℝ) :=
    (hsub (Classical.arbitrary k)).one_le_of_isIsotropic (hiso (Classical.arbitrary k))
  refine hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le hind hsub hiso hε
    (by linarith) hδ ((subgaussianJLMomentDim_le c ε hδ hδ2).trans (le_of_eq_of_le ?_ hk))
  ring

omit [DecidableEq n] in
/-- The failure probability of the sub-Gaussian OSE is at most $\delta$ for
$0 < \varepsilon \le 5c/4$, $\delta > 0$ and at
least <!-- value subgaussianEmbeddingDim c d \varepsilon \delta -->
$25 c^2 (d \log 21 + \log(2/\delta))/(16 C \varepsilon^2)$ rows
(`subgaussianEmbeddingDim c d ε δ`, with <!-- value subgaussianJLConstant -->$C = 1/36$ the
constant `subgaussianJLConstant`). -/
private theorem failure_le_of_subgaussianEmbeddingDim_le (hε : 0 < ε) (hεc : ε ≤ 5 / 4 * c)
    (hδ : 0 < δ) (hk : subgaussianEmbeddingDim c d ε δ ≤ Fintype.card k) :
    2 * 21 ^ d * Real.exp (-(subgaussianJLConstant * Fintype.card k *
      min (16 * ε ^ 2 / (25 * (c : ℝ) ^ 2)) (4 * ε / (5 * c)))) ≤ δ := by
  have hc : (0 : ℝ) < c := by
    have : (0 : ℝ) < 5 / 4 * c := hε.trans_le hεc
    linarith
  have hC := subgaussianJLConstant_pos
  have hmin : min (16 * ε ^ 2 / (25 * (c : ℝ) ^ 2)) (4 * ε / (5 * c)) =
      16 * ε ^ 2 / (25 * (c : ℝ) ^ 2) := by
    refine min_eq_left ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hεc (mul_nonneg hε.le hc.le)]
  rw [hmin]
  rw [subgaussianEmbeddingDim_def, div_le_iff₀ (by positivity)] at hk
  refine two_mul_twentyOne_pow_mul_exp_le hδ ?_
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  linarith

/-- **Sub-Gaussian OSE, sample-size form**: for a random $\mathbf{X}$ with $k$ independent,
isotropic, sub-Gaussian rows with proxy $c$, $0 < \varepsilon \le 5c/4$, $\delta > 0$ and at
least <!-- value subgaussianEmbeddingDim c d \varepsilon \delta -->
$25 c^2 (d \log 21 + \log(2/\delta))/(16 C \varepsilon^2)$ rows
(`subgaussianEmbeddingDim c d ε δ`, with <!-- value subgaussianJLConstant -->$C = 1/36$ the
constant `subgaussianJLConstant`),
$\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$
is an oblivious subspace embedding for dimension $d$ with constants $1 \mp \varepsilon$ and
failure probability $\delta$. [Vershynin2018, Theorem 4.6.1]; [Woodruff2014,
Theorem 6]. Asymptotic form:
`NLAlib.exists_forall_isObliviousSubspaceEmbedding_of_isSubgaussianVector`.
Result: subgaussian-ose -/
theorem isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (hε : 0 < ε) (hεc : ε ≤ 5 / 4 * c) (hδ : 0 < δ)
    (hk : subgaussianEmbeddingDim c d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) (1 + ε) δ
      μ := by
  have := hind.isProbabilityMeasure
  exact (isObliviousSubspaceEmbedding_of_isSubgaussianVector hind hsub hiso d).mono le_rfl le_rfl
    le_rfl (failure_le_of_subgaussianEmbeddingDim_le hε hεc hδ hk)

/-- **Sub-Gaussian OSE, asymptotic form**: $O(c^2 (d + \log(1/\delta))/\varepsilon^2)$ rows
suffice for the sketch with independent isotropic rows, sub-Gaussian with proxy $c$, to be an
oblivious subspace embedding for dimension $d$ with constants $1 \mp \varepsilon$ and failure
probability $\delta$, for $\varepsilon$ and $\delta$ below absolute constants; the constants come
before every dimension and the proxy. Proved from
`NLAlib.isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le` with
$C = 344$, $\varepsilon_0 = 1$ and $\delta \le 1/2$; isotropy forces $c \ge 1$ once there is a
column. [Woodruff2014, Theorem 6].
Asymptotic: NLAlib.isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
-/
theorem exists_forall_isObliviousSubspaceEmbedding_of_isSubgaussianVector :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      [DecidableEq n] [Nonempty k] (μ : Measure Ω) (X : Ω → Matrix k n ℝ) (c : ℝ≥0) (d : ℕ)
      (ε δ : ℝ),
      iIndepFun (fun i ω => X ω i) μ → (∀ i, IsSubgaussianVector (fun ω => X ω i) c μ) →
      (∀ i, IsIsotropic (fun ω => X ω i) μ) → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((c : ℝ) ^ 2 * (d + Real.log (1 / δ)) / ε ^ 2) ≤ Fintype.card k →
      IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) (1 + ε) δ
        μ := by
  refine ⟨344, 1, by norm_num, one_pos, ?_⟩
  intro Ω k n _ _ _ _ _ μ X c d ε δ hind hsub hiso hε hε1 hδ hδ2 hk
  have := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty n with hn | hn
  · intro U _
    rw [show U = 0 from Matrix.ext fun i => isEmptyElim i]
    exact hasSubspaceEmbedding_of_rank_eq_zero Matrix.rank_zero hδ.le
  have hc : 1 ≤ (c : ℝ) :=
    (hsub (Classical.arbitrary k)).one_le_of_isIsotropic (hiso (Classical.arbitrary k))
  have hl1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hl2 := Real.log_two_div_le_two_mul_log_one_div hδ hδ2
  refine isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le hind
    hsub hiso hε (by linarith) hδ
    ((subgaussianEmbeddingDim_le c d ε hδ (by linarith)).trans (le_trans ?_ hk))
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right
    (by nlinarith [mul_le_mul_of_nonneg_left hl2 (sq_nonneg (c : ℝ)),
      mul_nonneg (sq_nonneg (c : ℝ)) (Nat.cast_nonneg (α := ℝ) d),
      mul_nonneg (sq_nonneg (c : ℝ)) hl1]) (sq_nonneg ε)

/-- Sub-Gaussian OSI, sample-size form: for a random $\mathbf{X}$ with $k$ independent,
isotropic, sub-Gaussian rows with proxy $c$, $0 < \varepsilon \le 5c/4$, $\delta > 0$, $k$
nonempty and at least <!-- value subgaussianEmbeddingDim c d \varepsilon \delta -->
$25 c^2 (d \log 21 + \log(2/\delta))/(16 C \varepsilon^2)$ rows
(`subgaussianEmbeddingDim c d ε δ`, with <!-- value subgaussianJLConstant -->$C = 1/36$ the
constant `subgaussianJLConstant`),
$\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$ is an oblivious
subspace injection for dimension $d$ with constant $1 - \varepsilon$ and failure probability
$\delta$; the injection twin of
`NLAlib.isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le`. -/
theorem isObliviousSubspaceInjection_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
    [Nonempty k] (hind : iIndepFun (fun i ω => X ω i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (hε : 0 < ε) (hεc : ε ≤ 5 / 4 * c) (hδ : 0 < δ)
    (hk : subgaussianEmbeddingDim c d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) δ μ := by
  have := hind.isProbabilityMeasure
  exact (isObliviousSubspaceInjection_of_isSubgaussianVector hind hsub hiso d).mono le_rfl le_rfl
    (failure_le_of_subgaussianEmbeddingDim_le hε hεc hδ hk)

end Rows

/-! ### Independent sub-Gaussian entries -/

/-- **Sub-Gaussian JL for independent entries**: for a random $\mathbf{X}$ with independent
entries $\mathbf{X}_{i,j}$, each sub-Gaussian with proxy $c$ and with
$\mathbb{E}[\mathbf{X}_{i,j}^2] = 1$,
$$\mathbf{S} = \lvert k \rvert^{-1/2} \, \mathbf{X}$$
has the JL property with failure probability <!-- value subgaussianJLConstant -->
$2 e^{-(1/36) \lvert k \rvert \min(\varepsilon^2/c^2, \varepsilon/c)}$, the constant being
`subgaussianJLConstant`. The mean is $0$ by `HasSubgaussianMGF.integral_eq_zero`, so the second
moment is the variance. The rows hypotheses
follow by `NLAlib.iIndepFun_row_of_iIndepFun_entry`, `IsSubgaussianVector.of_iIndepFun` and
`IsIsotropic.of_iIndepFun`; the other rows theorems apply to entries through the same three
steps. [Vershynin2018, Exercise 5.3.3].
Result: jl-subgaussian -/
theorem hasJLProperty_of_iIndepFun_entry
    (hind : iIndepFun (fun p : k × n => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      (2 * Real.exp (-(subgaussianJLConstant * Fintype.card k *
        min (ε ^ 2 / (c : ℝ) ^ 2) (ε / c)))) μ := by
  classical
  have := hind.isProbabilityMeasure
  have hrow : iIndepFun (fun i ω => X ω i) μ :=
    iIndepFun_row_of_iIndepFun_entry hind fun i j => (hsub i j).aemeasurable
  have hcol (i : k) : iIndepFun (fun j ω => X ω i j) μ :=
    hind.precomp (g := fun j : n => (i, j)) (Prod.mk_right_injective i)
  refine hasJLProperty_of_isSubgaussianVector hrow
    (fun i => IsSubgaussianVector.of_iIndepFun (x := fun ω => X ω i) (hcol i) (hsub i))
    fun i => IsIsotropic.of_iIndepFun (x := fun ω => X ω i) (hcol i) (fun j => ?_)
      (fun j => (hsub i j).integral_eq_zero) fun j => ?_
  · simpa using (hsub i j).memLp 2
  · simpa only [Real.norm_eq_abs, sq_abs] using hvar i j

end NLAlib
