/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.EntrywiseRounding
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# A floating-point machine that rounds every result to a binary format

`NLAlib.binaryFloatMachine fmt r` is a `NLAlib.FloatMachine` on stored reals whose arithmetic
**rounds its exact result to the grid of the binary format** `fmt` with gradual underflow
(`NLAlib.Computation.binaryFloatRound`, nearest selector `r`): conversion, addition,
subtraction, multiplication and division, the normal sampler, and the two black boxes, which are
correctly rounded (they compute the exact product, or an exact QR factorization, and round each
entry, real and imaginary parts separately). Zero, one, negation, comparison and the floor
conversion are exact, and the uniform sampler rounds $sv$ and then clamps it to $[-s, s]$.
Stored values are arbitrary reals, so exact negation of an off-grid input and the clamp at an
off-grid scale return values off the grid: in binary128 ($p = 113$), the scale
$s = 1 - 2^{-115}$ and every seed $v \le 1$ with $sv \ge 1 - 2^{-114}$ give
$\mathrm{unif}(s, v) = s$. Results are on the grid when the inputs and the scale are.
Overflow is not modelled: the quantizer rounds a value above the largest finite number to the
$p$-bit grid at an exponent the format does not have, so a rounded result is a number of the
format only when it is at most the largest finite number in magnitude. The contract's error
bounds for the scalar operations, the matrix product, the QR factorization and the normal
sampler apply only up to that range. Its exactness clauses, the uniform sampler's support and
error bounds (at every scale $s \ge 0$) and the exact Hermitian symmetry of a product with its
conjugate transpose have no range guard, and the machine meets them at every scale. It meets
the contract
`NLAlib.FloatMachine.IsAccurate` with $u = 2^{-p}$, floor $\tau = 2^{e_{\min} + p - 1}$, range
the largest finite number, $\mu_{\mathrm{MM}}(d) = \mu_{\mathrm{QR}}(d) = 2d$ and
$c_{\mathrm N} = \sqrt2$; with an odd selector the rounded product of a matrix with its conjugate
transpose is exactly Hermitian. Unlike `NLAlib.exists_floatMachine_isAccurate_binaryFloatRound`,
whose black boxes are exact, every rounded operation and black box of this machine returns a
value of the rounding, and its samplers have countable ranges and measurable fibres, the
hypotheses under which
the sampling analysis of `NLAlib.eigh` applies.

## Main definitions

* `NLAlib.binaryFloatMachine`: the machine.

## Main results

* `NLAlib.isAccurate_binaryFloatMachine`: the contract.
* `NLAlib.countable_range_binaryFloatRound`, `NLAlib.measurable_binaryFloatRound`.
* `NLAlib.measurable_intLog_abs`, `NLAlib.specNorm_sub_map_le`: shared with the grid machine
  (`NLAlib/Matrix/Computation/GridMachine.lean`).
* `NLAlib.countable_range_unif_binaryFloatMachine`,
  `NLAlib.measurableSet_preimage_unif_binaryFloatMachine`,
  `NLAlib.countable_range_normal_binaryFloatMachine`,
  `NLAlib.measurableSet_preimage_normal_binaryFloatMachine`: the samplers.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib

/-- The **floating-point machine of a binary format** `fmt` with nearest selector `r`, on
stored reals with real seeds and complex samples: $0$ and $1$, negation, comparison and the floor
conversion are exact; conversion, addition, subtraction, multiplication and division round the
exact result with `NLAlib.Computation.binaryFloatRound`; the matrix product and the QR
factorization compute the exact product (an exact factorization, chosen) and round each entry,
real and imaginary parts separately; the uniform sampler clamps the rounded $sv$ to $[-s, s]$
and the normal sampler rounds both parts. -/
noncomputable def binaryFloatMachine (fmt : Float.Model.Format) (r : ℝ → ℤ) :
    FloatMachine ℝ ℝ ℂ where
  zero := 0
  one := 1
  ofNat k := Computation.binaryFloatRound fmt r k
  add x y := Computation.binaryFloatRound fmt r (x + y)
  sub x y := Computation.binaryFloatRound fmt r (x - y)
  mul x y := Computation.binaryFloatRound fmt r (x * y)
  div x y := Computation.binaryFloatRound fmt r (x / y)
  neg x := -x
  le x y := if x ≤ y then true else false
  toNat x := ⌊x⌋₊
  mm := fun {_ _ _} A B => ((A.map (decodeComplex id)) * (B.map (decodeComplex id))).map
    fun z => (Computation.binaryFloatRound fmt r z.re, Computation.binaryFloatRound fmt r z.im)
  qr := fun {_ _} A =>
    ((Classical.choose (exists_hasOrthonormalCols_mul_isUpperTrapezoidal
        (A.map (decodeComplex id)))).map
      fun z => (Computation.binaryFloatRound fmt r z.re, Computation.binaryFloatRound fmt r z.im),
    (Classical.choose (Classical.choose_spec (exists_hasOrthonormalCols_mul_isUpperTrapezoidal
        (A.map (decodeComplex id))))).map
      fun z => (Computation.binaryFloatRound fmt r z.re, Computation.binaryFloatRound fmt r z.im))
  unif s v := max (-s) (min s (Computation.binaryFloatRound fmt r (s * v)))
  normal z := (Computation.binaryFloatRound fmt r z.re, Computation.binaryFloatRound fmt r z.im)

section Rounding

variable (fmt : Float.Model.Format) {r : ℝ → ℤ}

/-- With an odd selector, binary rounding is odd. -/
private theorem binaryFloatRound_neg (hodd : ∀ x, r (-x) = -r x) (x : ℝ) :
    Computation.binaryFloatRound fmt r (-x) = -Computation.binaryFloatRound fmt r x := by
  simp only [Computation.binaryFloatRound, abs_neg, neg_div, hodd, Int.cast_neg, neg_mul]

/-- Binary rounding has countable range: every value of
`NLAlib.Computation.binaryFloatRound` is an integer times a power of two. No printed source. -/
theorem countable_range_binaryFloatRound (r : ℝ → ℤ) :
    (Set.range (Computation.binaryFloatRound fmt r)).Countable := by
  refine (Set.countable_range fun p : ℤ × ℤ => (p.1 : ℝ) * (2 : ℝ) ^ p.2).mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(_, _), rfl⟩

/-- `Int.log 2 |x|` is a measurable function of $x$. No printed source. -/
theorem measurable_intLog_abs : Measurable fun x : ℝ => Int.log 2 |x| := by
  have h : (fun x : ℝ => Int.log 2 |x|) = fun x =>
      if 1 ≤ |x| then ((Nat.log 2 ⌊|x|⌋₊ : ℕ) : ℤ) else -((Nat.clog 2 ⌈|x|⁻¹⌉₊ : ℕ) : ℤ) := by
    funext x; rfl
  rw [h]
  have habs : Measurable fun x : ℝ => |x| := continuous_abs.measurable
  refine Measurable.ite (measurableSet_le measurable_const habs) ?_ ?_
  · exact (Measurable.of_discrete (f := fun k : ℕ => ((Nat.log 2 k : ℕ) : ℤ))).comp
      (Nat.measurable_floor.comp habs)
  · exact (Measurable.of_discrete (f := fun k : ℕ => -((Nat.clog 2 k : ℕ) : ℤ))).comp
      (Nat.measurable_ceil.comp habs.inv)

/-- Binary rounding with a measurable selector is measurable. No printed source. -/
theorem measurable_binaryFloatRound (hr : Measurable r) :
    Measurable (Computation.binaryFloatRound fmt r) := by
  have hg : Measurable fun p : ℝ × ℤ => ((r (p.1 / (2 : ℝ) ^ p.2) : ℤ) : ℝ) * (2 : ℝ) ^ p.2 :=
    measurable_from_prod_countable_left fun k =>
      ((Measurable.of_discrete (f := fun k : ℤ => (k : ℝ))).comp
        (hr.comp (measurable_id.div_const ((2 : ℝ) ^ k)))).mul_const ((2 : ℝ) ^ k)
  have he : Measurable fun x : ℝ => fmt.targetExponent (Int.log 2 |x| + 1) :=
    (Measurable.of_discrete (f := fun k : ℤ => fmt.targetExponent (k + 1))).comp
      measurable_intLog_abs
  exact hg.comp (measurable_id.prodMk he)

end Rounding

section Contract

variable {fmt : Float.Model.Format} {r : ℝ → ℤ}

/-- Entrywise rounding of a complex matrix, part by part, with a rounding of relative error $u$
above the floor $\tau$ at every scale, errs by at most $2du\max(\|\mathbf{X}\|_2, \tau)$ in the
spectral norm, $d$ at least both dimensions. No printed source. -/
theorem specNorm_sub_map_le {m n d : ℕ} {u τ : ℝ} {R : ℝ → ℝ} (hu : 0 ≤ u)
    (hτ : 0 ≤ τ) (hR : ∀ x, |x - R x| ≤ u * max |x| τ) (hm : m ≤ d) (hn : n ≤ d)
    (X : Matrix (Fin m) (Fin n) ℂ) :
    specNorm (X - X.map fun z => (⟨R z.re, R z.im⟩ : ℂ)) ≤
      2 * d * u * max (specNorm X) τ := by
  set K := u * max (specNorm X) τ with hK_def
  have hK : 0 ≤ K := mul_nonneg hu (le_max_of_le_right hτ)
  have hentry : ∀ i j, ‖(X - X.map fun z => (⟨R z.re, R z.im⟩ : ℂ)) i j‖ ^ 2 ≤ 2 * K ^ 2 := by
    intro i j
    have h1 : |(X i j).re| ≤ specNorm X :=
      (Complex.abs_re_le_norm _).trans (norm_apply_le_specNorm X i j)
    have h2 : |(X i j).im| ≤ specNorm X :=
      (Complex.abs_im_le_norm _).trans (norm_apply_le_specNorm X i j)
    have e1 := (hR (X i j).re).trans (mul_le_mul_of_nonneg_left (max_le_max h1 le_rfl) hu)
    have e2 := (hR (X i j).im).trans (mul_le_mul_of_nonneg_left (max_le_max h2 le_rfl) hu)
    rw [Matrix.sub_apply, Matrix.map_apply, Complex.sq_norm, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im]
    nlinarith [sq_le_sq' (abs_le.mp e1).1 (abs_le.mp e1).2,
      sq_le_sq' (abs_le.mp e2).1 (abs_le.mp e2).2]
  have hmn : (m : ℝ) * n ≤ d * d :=
    mul_le_mul (by exact_mod_cast hm) (by exact_mod_cast hn) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _)
  have hF : frobNorm (X - X.map fun z => (⟨R z.re, R z.im⟩ : ℂ)) ^ 2 ≤ (2 * d * K) ^ 2 := by
    rw [frobNorm_sq_eq_sum]
    calc _ ≤ ∑ _i : Fin m, ∑ _j : Fin n, 2 * K ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
      _ = m * n * (2 * K ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ (2 * d * K) ^ 2 := by nlinarith [sq_nonneg K]
  calc _ ≤ frobNorm (X - X.map fun z => (⟨R z.re, R z.im⟩ : ℂ)) := specNorm_le_frobNorm _
    _ ≤ 2 * d * K := (pow_le_pow_iff_left₀ (frobNorm_nonneg _) (by positivity) two_ne_zero).1 hF
    _ = _ := by rw [hK_def]; ring

/-- The decoded output of the product: the entrywise rounding of the exact product. -/
private theorem decode_mm_binaryFloatMachine {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (ℝ × ℝ))
    (B : Matrix (Fin m) (Fin n) (ℝ × ℝ)) :
    ((binaryFloatMachine fmt r).mm A B).map (decodeComplex id) =
      (A.map (decodeComplex id) * B.map (decodeComplex id)).map fun z =>
        (⟨Computation.binaryFloatRound fmt r z.re, Computation.binaryFloatRound fmt r z.im⟩ : ℂ) :=
  by ext i j; rfl

/-- The matrix-multiplication contract of the binary-format machine. -/
private theorem isMatMulErr_binaryFloatMachine
    (hr : ∀ x, Computation.AbsRelErr 0 (1 / 2) x (r x : ℝ)) (hodd : ∀ x, r (-x) = -r x)
    (Ω : ℝ) :
    IsMatMulErr (decodeComplex id) ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) Ω (fun d => 2 * d)
      (binaryFloatMachine fmt r).mm where
  specNorm_mul_sub_le {l m n} A B _ := by
    rw [decode_mm_binaryFloatMachine]
    refine (specNorm_sub_map_le (by positivity) (by positivity)
      (Computation.abs_sub_binaryFloatRound_le fmt hr) (le_max_left l (max m n))
      ((le_max_right m n).trans (le_max_right _ _)) _).trans ?_
    gcongr
    exact specNorm_mul_le _ _
  isHermitian_of_map_eq_conjTranspose {m n} A B hB := by
    rw [decode_mm_binaryFloatMachine, hB]
    set P := A.map (decodeComplex id) * (A.map (decodeComplex id))ᴴ
    have hP : P.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self _
    refine Matrix.IsHermitian.ext fun i j => ?_
    have h := hP.apply j i
    have hre : (P j i).re = (P i j).re := by rw [← h, Complex.star_def, Complex.conj_re]
    have him : (P j i).im = -(P i j).im := by rw [← h, Complex.star_def, Complex.conj_im]
    apply Complex.ext
    · simp only [Matrix.map_apply, Complex.star_def, Complex.conj_re, hre]
    · simp only [Matrix.map_apply, Complex.star_def, Complex.conj_im, him,
        binaryFloatRound_neg fmt hodd, neg_neg]

/-- The QR contract of the binary-format machine, for a floor $\tau \le 1$. -/
private theorem isQRErr_binaryFloatMachine
    (hr : ∀ x, Computation.AbsRelErr 0 (1 / 2) x (r x : ℝ))
    (hτ₁ : (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) ≤ 1) (Ω : ℝ) :
    IsQRErr (decodeComplex id) ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) Ω (fun d => 2 * d)
      (binaryFloatMachine fmt r).qr := by
  intro m n A _
  set R := Computation.binaryFloatRound fmt r
  have hround := Computation.abs_sub_binaryFloatRound_le fmt hr
  obtain ⟨hQ, hRt, hA⟩ := Classical.choose_spec (Classical.choose_spec
    (exists_hasOrthonormalCols_mul_isUpperTrapezoidal (A.map (decodeComplex id))))
  set Q := Classical.choose (exists_hasOrthonormalCols_mul_isUpperTrapezoidal
    (A.map (decodeComplex id)))
  set Rm := Classical.choose (Classical.choose_spec
    (exists_hasOrthonormalCols_mul_isUpperTrapezoidal (A.map (decodeComplex id))))
  have h1 : ((binaryFloatMachine fmt r).qr A).1.map (decodeComplex id) =
      Q.map fun z => (⟨R z.re, R z.im⟩ : ℂ) := by ext i j; rfl
  have h2 : ((binaryFloatMachine fmt r).qr A).2.map (decodeComplex id) =
      Rm.map fun z => (⟨R z.re, R z.im⟩ : ℂ) := by ext i j; rfl
  have hu : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ fmt.mantissaBits := by positivity
  have hτ : (0 : ℝ) ≤ (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) := by positivity
  have hmn := le_max_left m n
  rw [h1, h2]
  refine ⟨fun i j hij => ?_, Q, hQ, ?_, ?_⟩
  · have h0 : R 0 = 0 := Computation.binaryFloatRound_zero fmt hr
    rw [Matrix.map_apply, hRt i j hij, Complex.zero_re, Complex.zero_im, h0]
    rfl
  · refine (specNorm_sub_map_le hu hτ hround hmn hmn Q).trans ?_
    have : max (specNorm Q) ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) ≤ 1 :=
      max_le hQ.specNorm_le_one hτ₁
    calc _ ≤ 2 * ((max m n : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ fmt.mantissaBits * 1 := by gcongr
      _ = _ := mul_one _
  · have hR : specNorm Rm = specNorm (A.map (decodeComplex id)) := by
      rw [hA, hQ.specNorm_mul_left]
    have hsub : A.map (decodeComplex id) - Q * Rm.map (fun z => (⟨R z.re, R z.im⟩ : ℂ)) =
        Q * (Rm - Rm.map fun z => (⟨R z.re, R z.im⟩ : ℂ)) := by
      conv_lhs => rw [hA]
      rw [Matrix.mul_sub]
    rw [hsub, hQ.specNorm_mul_left, ← hR]
    exact specNorm_sub_map_le hu hτ hround hmn (le_max_right m n) Rm

/-- The binary-format machine meets the contract (`NLAlib.FloatMachine.IsAccurate`): for a
binary format `fmt` with precision $p$, smallest exponent $e_{\min}$ and smallest normal number
$\tau = 2^{e_{\min} + p - 1} \le 1$, and an odd nearest selector `r` (half-unit error,
$r(-x) = -r(x)$), the machine `NLAlib.binaryFloatMachine` meets the contract with the identity
decoding, unit roundoff $u = 2^{-p}$, floor $\tau$, range the largest finite number,
$\mu_{\mathrm{MM}}(d) = \mu_{\mathrm{QR}}(d) = 2d$ and $c_{\mathrm N} = \sqrt2$. Entrywise
rounding errs by $\sqrt2\,u\max(\|\mathbf{X}\|_2, \tau)$ per entry, hence by $2du\max(\cdot)$ in
the spectral norm via the Frobenius norm; the oddness keeps the rounded
$\mathbf{A}\mathbf{A}^{\mathsf{H}}$ Hermitian. No printed source. -/
theorem isAccurate_binaryFloatMachine
    (hr : ∀ x, Computation.AbsRelErr 0 (1 / 2) x (r x : ℝ)) (hodd : ∀ x, r (-x) = -r x)
    (hτ₁ : (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) ≤ 1) :
    (binaryFloatMachine fmt r).IsAccurate id ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) fmt.maxFinite (fun d => 2 * d)
      (fun d => 2 * d) √2 := by
  have hround := Computation.abs_sub_binaryFloatRound_le fmt hr
  set u : ℝ := (2 : ℝ)⁻¹ ^ fmt.mantissaBits
  set τ : ℝ := (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)
  set R := Computation.binaryFloatRound fmt r
  refine ⟨⟨rfl, rfl, fun k _ => hround _, fun x y _ => hround _, fun x y _ => hround _,
    fun x y _ => hround _, fun x y _ _ => hround _, fun x => rfl, fun x y => by
      change (if x ≤ y then true else false) = true ↔ x ≤ y
      split_ifs with h <;> simp [h],
    fun x => rfl, isMatMulErr_binaryFloatMachine hr hodd _⟩, isQRErr_binaryFloatMachine hr hτ₁ _,
    ?_, ?_⟩
  · intro s v hs hv
    simp only [id] at hs ⊢
    have hsv : |s * v| ≤ s := by
      rw [abs_mul, abs_of_nonneg hs]
      exact mul_le_of_le_one_right hs (abs_le.mpr ⟨hv.1, hv.2⟩)
    obtain ⟨hl, hh⟩ := abs_le.mp hsv
    have hw := hround (s * v)
    change |max (-s) (min s (R (s * v)))| ≤ s ∧ |s * v - max (-s) (min s (R (s * v)))| ≤ u * max s τ
    refine ⟨abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩, ?_⟩
    refine le_trans ?_ (hw.trans (by gcongr))
    rcases le_total s (R (s * v)) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith), abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      linarith
    · rw [min_eq_right h]
      rcases le_total (-s) (R (s * v)) with h' | h'
      · rw [max_eq_right h']
      · rw [max_eq_left h', abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
  · intro z _
    have hre := hround z.re
    have him := hround z.im
    have hRe : max |z.re| τ ≤ max ‖z‖ τ := by gcongr; exact Complex.abs_re_le_norm z
    have hIm : max |z.im| τ ≤ max ‖z‖ τ := by gcongr; exact Complex.abs_im_le_norm z
    apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
    rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, mul_pow, Real.sq_sqrt zero_le_two]
    have e1 : (z - decodeComplex id (R z.re, R z.im)).re = z.re - R z.re := rfl
    have e2 : (z - decodeComplex id (R z.re, R z.im)).im = z.im - R z.im := rfl
    change ((z - decodeComplex id (R z.re, R z.im)).re * (z - decodeComplex id (R z.re, R z.im)).re
      + (z - decodeComplex id (R z.re, R z.im)).im * (z - decodeComplex id (R z.re, R z.im)).im)
      ≤ _
    rw [e1, e2, ← sq, ← sq]
    have a1 := sq_le_sq' (abs_le.mp hre).1 (abs_le.mp hre).2
    have a2 := sq_le_sq' (abs_le.mp him).1 (abs_le.mp him).2
    have b1 : (u * max |z.re| τ) ^ 2 ≤ (u * max ‖z‖ τ) ^ 2 := by gcongr
    have b2 : (u * max |z.im| τ) ^ 2 ≤ (u * max ‖z‖ τ) ^ 2 := by gcongr
    nlinarith

end Contract

section Samplers

variable (fmt : Float.Model.Format) {r : ℝ → ℤ}

/-- The uniform sampler of the binary-format machine has countable range, at every scale
$c$: its values are clampings of binary roundings. No printed source. -/
theorem countable_range_unif_binaryFloatMachine (r : ℝ → ℤ) (c : ℝ) :
    (Set.range ((binaryFloatMachine fmt r).unif c)).Countable := by
  refine ((countable_range_binaryFloatRound fmt r).image fun y => max (-c) (min c y)).mono ?_
  rintro _ ⟨v, rfl⟩
  exact ⟨_, ⟨c * v, rfl⟩, rfl⟩

/-- The uniform sampler of the binary-format machine has measurable fibres, for a measurable
selector, at every scale $c$ and value $z$. No printed source. -/
theorem measurableSet_preimage_unif_binaryFloatMachine (hr : Measurable r) (c z : ℝ) :
    MeasurableSet ((binaryFloatMachine fmt r).unif c ⁻¹' {z}) :=
  (measurable_const.max (measurable_const.min
    ((measurable_binaryFloatRound fmt hr).comp (measurable_const.mul measurable_id))))
    (measurableSet_singleton z)

/-- The normal sampler of the binary-format machine has countable range: both parts are
binary roundings. No printed source. -/
theorem countable_range_normal_binaryFloatMachine (r : ℝ → ℤ) :
    (Set.range (binaryFloatMachine fmt r).normal).Countable := by
  refine ((countable_range_binaryFloatRound fmt r).prod
    (countable_range_binaryFloatRound fmt r)).mono ?_
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨z.re, rfl⟩, ⟨z.im, rfl⟩⟩

/-- The normal sampler of the binary-format machine has measurable fibres, for a measurable
selector. No printed source. -/
theorem measurableSet_preimage_normal_binaryFloatMachine (hr : Measurable r) (z : ℝ × ℝ) :
    MeasurableSet ((binaryFloatMachine fmt r).normal ⁻¹' {z}) :=
  (((measurable_binaryFloatRound fmt hr).comp Complex.measurable_re).prodMk
    ((measurable_binaryFloatRound fmt hr).comp Complex.measurable_im)) (measurableSet_singleton z)

end Samplers

end NLAlib
