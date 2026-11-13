/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Machine
public import NLAlib.ForMathlib.Algebra.Order.Round
public import NLAlib.Matrix.FinitePrecision.BinaryFloat
public import NLAlib.Matrix.Norms.Compare

/-!
# Entrywise operations on stored Hermitian matrices

The cheap steps of a dense eigensolver (a diagonal shift, a scaling, the Hermitian part of a
computed product, a trace) touch every entry once. Here they are **built from the scalar
operations of a `NLAlib.FloatMachine`**, real and imaginary parts separately, as IEEE complex
arithmetic does, so their error bounds follow from the machine's contract rather than being
assumed. Hermitian structure is kept by construction: `NLAlib.FloatMachine.hermFrom` computes
the strict upper triangle and the real diagonal and mirrors the rest with the machine's exact
negation, so its decoding is exactly Hermitian whatever the rounding does with signs.

## Main definitions

* `NLAlib.FloatMachine.hermFrom`: a stored Hermitian matrix from its upper triangle and diagonal.
* `NLAlib.FloatMachine.hermShift`, `NLAlib.FloatMachine.hermScale`,
  `NLAlib.FloatMachine.hermAvg`: $\mathbf{X} - c\mathbf{I}$, $\mathbf{X}/c$,
  $(\mathbf{X} + \mathbf{X}^{\mathsf{H}})/c$, stored Hermitian.
* `NLAlib.FloatMachine.negMat`, `NLAlib.FloatMachine.conjTransposeMat`,
  `NLAlib.FloatMachine.identityMat`, `NLAlib.FloatMachine.zeroMat`: exact operations.
* `NLAlib.FloatMachine.traceRe`: the rounded sum of the real parts of the diagonal.

## Main results

* `NLAlib.isRoundingOf_roundNearest`, `NLAlib.isRoundingOf_binaryFloatRound`.
* `NLAlib.FloatMachine.IsArithAccurate.isHermitian_decodeMatrix_hermFrom`,
  `NLAlib.FloatMachine.IsArithAccurate.decodeMatrix_negMat`,
  `NLAlib.FloatMachine.IsArithAccurate.decodeMatrix_conjTransposeMat`,
  `NLAlib.FloatMachine.IsArithAccurate.decodeMatrix_identityMat`.
* `NLAlib.FloatMachine.IsArithAccurate.specNorm_sub_decodeMatrix_hermShift_le`,
  `NLAlib.FloatMachine.IsArithAccurate.specNorm_sub_decodeMatrix_hermScale_le`,
  `NLAlib.FloatMachine.IsArithAccurate.specNorm_sub_decodeMatrix_hermAvg_le`,
  `NLAlib.FloatMachine.IsArithAccurate.abs_sum_sub_traceRe_le`.
-/

@[expose] public section

namespace NLAlib

namespace FloatMachine

variable {F Su Sg : Type*} (M : FloatMachine F Su Sg)

/-- **A stored Hermitian matrix from its upper triangle and diagonal**: the entry $(i, j)$ is
`up i j` for $i < j$, the conjugate (exact negation of the imaginary part) of `up j i` for
$i > j$, and $(\mathrm{dg}(i), 0)$ on the diagonal. -/
def hermFrom {k : ℕ} (up : Fin k → Fin k → F × F) (dg : Fin k → F) :
    Matrix (Fin k) (Fin k) (F × F) :=
  Matrix.of fun i j =>
    if i < j then up i j else if j < i then ((up j i).1, M.neg (up j i).2) else (dg i, M.zero)

/-- **Shift by a stored scalar**, $\mathbf{X} - c\mathbf{I}$ stored Hermitian: the diagonal real
parts are $\mathrm{fl}(\operatorname{Re}\mathbf{X}_{i,i} - c)$, the upper triangle is copied. -/
def hermShift {k : ℕ} (X : Matrix (Fin k) (Fin k) (F × F)) (c : F) :
    Matrix (Fin k) (Fin k) (F × F) :=
  M.hermFrom (fun i j => X i j) fun i => M.sub (X i i).1 c

/-- **Division by a stored scalar**, $\mathbf{X}/c$ stored Hermitian: every part of the upper
triangle and every diagonal real part divided by $c$ and rounded. -/
def hermScale {k : ℕ} (X : Matrix (Fin k) (Fin k) (F × F)) (c : F) :
    Matrix (Fin k) (Fin k) (F × F) :=
  M.hermFrom (fun i j => (M.div (X i j).1 c, M.div (X i j).2 c)) fun i => M.div (X i i).1 c

/-- **The scaled Hermitian part**, $(\mathbf{X} + \mathbf{X}^{\mathsf{H}})/c$ stored Hermitian:
on the upper triangle the parts of $\mathbf{X}_{i,j} + \overline{\mathbf{X}_{j,i}}$ are computed,
rounded, then divided by $c$ and rounded; on the diagonal $2\operatorname{Re}\mathbf{X}_{i,i}/c$
likewise. -/
def hermAvg {k : ℕ} (X : Matrix (Fin k) (Fin k) (F × F)) (c : F) :
    Matrix (Fin k) (Fin k) (F × F) :=
  M.hermFrom
    (fun i j => (M.div (M.add (X i j).1 (X j i).1) c, M.div (M.sub (X i j).2 (X j i).2) c))
    fun i => M.div (M.add (X i i).1 (X i i).1) c

/-- **Entrywise negation** of a stored matrix (exact). -/
def negMat {m n : Type*} (X : Matrix m n (F × F)) : Matrix m n (F × F) :=
  X.map fun z => (M.neg z.1, M.neg z.2)

/-- **The conjugate transpose** of a stored matrix (exact: a transpose and a negation). -/
def conjTransposeMat {m n : Type*} (X : Matrix m n (F × F)) : Matrix n m (F × F) :=
  Matrix.of fun i j => ((X j i).1, M.neg (X j i).2)

/-- **The stored identity matrix.** -/
def identityMat (k : ℕ) : Matrix (Fin k) (Fin k) (F × F) :=
  Matrix.of fun i j => if i = j then (M.one, M.zero) else (M.zero, M.zero)

/-- **The stored zero matrix.** -/
def zeroMat (m n : Type*) : Matrix m n (F × F) :=
  Matrix.of fun _ _ => (M.zero, M.zero)

/-- **The rounded trace of the real parts**: $s_0 = 0$, $s_{i+1} =
\mathrm{fl}(s_i + \operatorname{Re}\mathbf{X}_{i,i})$, from the left. -/
def traceRe {k : ℕ} (X : Matrix (Fin k) (Fin k) (F × F)) : F :=
  (List.finRange k).foldl (fun s i => M.add s (X i i).1) M.zero

end FloatMachine

section Accuracy

open scoped Matrix

/-- **Rounding to nearest is a rounding**: rounding to nearest on the grid of $t$-bit binary
numbers with unbounded exponent (`Real.roundNearest`) returns a rounding of every real $a$ in the
sense of `NLAlib.IsRoundingOf`, with unit roundoff $2^{-t}$, floor $0$ and every range $\Omega$.
The standard-model rounding is applied to real and imaginary parts as complex arithmetic
does. [Higham2002, Theorem 2.2]. -/
theorem isRoundingOf_roundNearest (t : ℕ) (Ω a : ℝ) :
    IsRoundingOf (2⁻¹ ^ t) 0 Ω a (Real.roundNearest t a) := by
  intro _
  rw [max_eq_left (abs_nonneg a)]
  exact Real.abs_sub_roundNearest_le t a

/-- The local error of binary rounding: at most half the spacing $2^{e}$ of the target exponent
(private helper; the proof of `NLAlib.Computation.local_error`). -/
private theorem local_error_binaryFloatRound (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, Computation.AbsRelErr 0 (1 / 2) x (r x : ℝ)) (x : ℝ) :
    |x - Computation.binaryFloatRound fmt r x| ≤
      (1 / 2 : ℝ) * 2 ^ fmt.targetExponent (Int.log 2 |x| + 1) := by
  set e := fmt.targetExponent (Int.log 2 |x| + 1)
  have he : (0 : ℝ) < 2 ^ e := zpow_pos two_pos _
  have hq : |x / (2 : ℝ) ^ e - (r (x / (2 : ℝ) ^ e) : ℝ)| ≤ 1 / 2 := by
    simpa only [Computation.AbsRelErr, zero_mul, zero_add] using hr (x / (2 : ℝ) ^ e)
  have heq : x - Computation.binaryFloatRound fmt r x =
      (x / (2 : ℝ) ^ e - (r (x / (2 : ℝ) ^ e) : ℝ)) * 2 ^ e := by
    dsimp only [Computation.binaryFloatRound, e]
    field_simp
  rw [heq, abs_mul, abs_of_pos he]
  exact mul_le_mul_of_nonneg_right hq he.le

/-- **Bounded-format rounding is a rounding with floor**: rounding to the binary format `fmt`
with gradual underflow (`NLAlib.Computation.binaryFloatRound`, any nearest tie rule) returns a
rounding of every real $a$ in the sense of `NLAlib.IsRoundingOf` with unit roundoff $2^{-p}$,
floor $\tau = 2^{e_{\min} + p - 1}$ (the smallest normal number) and range the largest finite
number, $p$ the precision and $e_{\min}$ the smallest exponent. In the normal range the error is
relative; below it, half the subnormal spacing, $2^{e_{\min}}/2 = 2^{-p}\tau$, so no factor is
lost against the mixed form `NLAlib.Computation.AbsRelErr`. [Higham2002, §2.2], with gradual
underflow. -/
theorem isRoundingOf_binaryFloatRound (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, Computation.AbsRelErr 0 (1 / 2) x (r x : ℝ)) (a : ℝ) :
    IsRoundingOf ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) fmt.maxFinite a
      (Computation.binaryFloatRound fmt r a) := by
  intro _
  have hut : (2 : ℝ)⁻¹ ^ fmt.mantissaBits * (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) =
      1 / 2 * (2 : ℝ) ^ fmt.minExponent := by
    rw [zpow_sub₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_natCast, zpow_one, inv_pow]
    field_simp
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Computation.binaryFloatRound_zero fmt hr]
    simp
  rcases le_total ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) |a| with h | h
  · obtain ⟨δ, hδ, hz⟩ := Computation.relErr_binaryFloatRound_of_minExponent_le fmt hr a
      (by
        have := (Int.zpow_le_iff_le_log one_lt_two (abs_pos.2 ha)).1 h
        omega)
    rw [max_eq_left h, hz, show a - a * (1 + δ) = -(a * δ) by ring, abs_neg, abs_mul,
      mul_comm]
    exact mul_le_mul_of_nonneg_right hδ (abs_nonneg a)
  · rw [max_eq_right h]
    have hlog : (2 : ℝ) ^ Int.log 2 |a| ≤ |a| := by
      exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two (abs_pos.mpr ha)
    have hL : Int.log 2 |a| ≤ fmt.minExponent + fmt.mantissaBits - 1 :=
      (zpow_le_zpow_iff_right₀ one_lt_two).1 (hlog.trans h)
    have he : fmt.targetExponent (Int.log 2 |a| + 1) = fmt.minExponent := by
      apply max_eq_right
      omega
    have herr := local_error_binaryFloatRound fmt hr a
    rw [he] at herr
    rw [← hut] at herr
    rw [mul_comm] at hut
    linarith

namespace FloatMachine.IsArithAccurate

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω : ℝ} {μM : ℕ → ℝ}

/-- A matrix built by `NLAlib.FloatMachine.hermFrom` decodes to a Hermitian matrix, under the
contract `NLAlib.FloatMachine.IsArithAccurate` (zero and negation exact). -/
theorem isHermitian_decodeMatrix_hermFrom (hM : M.IsArithAccurate dec u τ Ω μM) {k : ℕ}
    (up : Fin k → Fin k → F × F) (dg : Fin k → F) :
    (decodeMatrix dec (M.hermFrom up dg)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  rcases lt_trichotomy i j with h | rfl | h
  · apply Complex.ext <;>
      simp [FloatMachine.hermFrom, decodeMatrix, decodeComplex, h, lt_asymm h, hM.dec_neg]
  · apply Complex.ext <;> simp [FloatMachine.hermFrom, decodeMatrix, decodeComplex, hM.dec_zero]
  · apply Complex.ext <;>
      simp [FloatMachine.hermFrom, decodeMatrix, decodeComplex, h, lt_asymm h, hM.dec_neg]

/-- Entrywise negation is exact: the decoding of `NLAlib.FloatMachine.negMat` $\mathbf{X}$ is
$-\bar{\mathbf{X}}$. -/
theorem decodeMatrix_negMat (hM : M.IsArithAccurate dec u τ Ω μM) {m n : Type*}
    (X : Matrix m n (F × F)) : decodeMatrix dec (M.negMat X) = -decodeMatrix dec X := by
  ext i j
  apply Complex.ext <;>
    simp [decodeMatrix, FloatMachine.negMat, decodeComplex, hM.dec_neg]

/-- The stored conjugate transpose is exact: the decoding of
`NLAlib.FloatMachine.conjTransposeMat` $\mathbf{X}$ is $\bar{\mathbf{X}}^{\mathsf{H}}$. -/
theorem decodeMatrix_conjTransposeMat (hM : M.IsArithAccurate dec u τ Ω μM) {m n : Type*}
    (X : Matrix m n (F × F)) :
    decodeMatrix dec (M.conjTransposeMat X) = (decodeMatrix dec X)ᴴ := by
  ext i j : 2
  apply Complex.ext <;>
    simp [decodeMatrix, FloatMachine.conjTransposeMat, decodeComplex, hM.dec_neg]

/-- The stored identity decodes to the identity. -/
theorem decodeMatrix_identityMat (hM : M.IsArithAccurate dec u τ Ω μM) (k : ℕ) :
    decodeMatrix dec (M.identityMat k) = 1 := by
  ext i j : 2
  by_cases h : i = j
  · subst h
    apply Complex.ext <;>
      simp [decodeMatrix, FloatMachine.identityMat, decodeComplex, hM.dec_one, hM.dec_zero]
  · apply Complex.ext <;>
      simp [decodeMatrix, FloatMachine.identityMat, decodeComplex, hM.dec_zero, h]

/-- **Error of the stored shift**: under `NLAlib.FloatMachine.IsArithAccurate` with $u \ge 0$, for a
stored $\mathbf{X}$ with Hermitian decoding $\bar{\mathbf{X}}$ and a stored $c$ with
$\|\bar{\mathbf{X}} - \bar c\mathbf{I}\|_2 \le \Omega$,
$$\|(\bar{\mathbf{X}} - \bar c\mathbf{I}) - \overline{\mathrm{hermShift}(\mathbf{X}, c)}\|_2 \le
u\max(\|\bar{\mathbf{X}} - \bar c\mathbf{I}\|_2, \tau) \,.$$
The error is diagonal, so its norm is its largest entry, as [Shah2024, proof of Lemma 2.1]
notes; the mirrored entries are exact because $\bar{\mathbf{X}}$ is Hermitian. -/
theorem specNorm_sub_decodeMatrix_hermShift_le (hM : M.IsArithAccurate dec u τ Ω μM)
    (hu : 0 ≤ u) {k : ℕ} {X : Matrix (Fin k) (Fin k) (F × F)}
    (hX : (decodeMatrix dec X).IsHermitian) (c : F)
    (hΩ : specNorm (decodeMatrix dec X - dec c • (1 : Matrix (Fin k) (Fin k) ℂ)) ≤ Ω) :
    specNorm ((decodeMatrix dec X - dec c • (1 : Matrix (Fin k) (Fin k) ℂ)) -
      decodeMatrix dec (M.hermShift X c)) ≤
        u * max (specNorm (decodeMatrix dec X - dec c • (1 : Matrix (Fin k) (Fin k) ℂ))) τ := by
  set D := decodeMatrix dec X - dec c • (1 : Matrix (Fin k) (Fin k) ℂ) with hD
  have hS := specNorm_nonneg D
  have hre : ∀ i, (D i i).re = dec (X i i).1 - dec c := by
    intro i
    simp [hD, decodeMatrix, decodeComplex, Complex.real_smul]
  have hE : D - decodeMatrix dec (M.hermShift X c) =
      Matrix.diagonal fun i => (((dec (X i i).1 - dec c) - dec (M.sub (X i i).1 c) : ℝ) : ℂ) := by
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [hD, decodeMatrix, FloatMachine.hermShift, FloatMachine.hermFrom, decodeComplex, h.ne,
        h]
    · have hi : dec (X i i).2 = 0 := by
        have h := congrArg Complex.im (hX.apply i i)
        simp [decodeMatrix, decodeComplex] at h
        linarith
      apply Complex.ext <;> simp [hD, decodeMatrix, FloatMachine.hermShift,
        FloatMachine.hermFrom, decodeComplex, hM.dec_zero, hi]
    · have h2 := congrArg Complex.re (hX.apply i j)
      have h3 := congrArg Complex.im (hX.apply i j)
      simp [decodeMatrix, decodeComplex] at h2 h3
      apply Complex.ext <;> simp [hD, decodeMatrix, FloatMachine.hermShift, FloatMachine.hermFrom,
        decodeComplex, h.ne', lt_asymm h, h, hM.dec_neg] <;> linarith
  rw [hE]
  refine specNorm_diagonal_le (mul_nonneg hu (le_max_of_le_left hS)) fun i => ?_
  have ha : |dec (X i i).1 - dec c| ≤ specNorm D := by
    rw [← hre i]
    exact (Complex.abs_re_le_norm _).trans (norm_apply_le_specNorm D i i)
  have h2 := hM.sub (X i i).1 c (ha.trans hΩ)
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine h2.trans (mul_le_mul_of_nonneg_left (max_le_max ha le_rfl) hu)

/-- Entrywise moduli are dominated in Frobenius norm -/
private theorem frobNorm_le_of_norm_apply_le {m n : Type*} [Fintype m] [Fintype n]
    {A B : Matrix m n ℂ} (h : ∀ i j, ‖A i j‖ ≤ ‖B i j‖) : frobNorm A ≤ frobNorm B := by
  unfold frobNorm
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    pow_le_pow_left₀ (norm_nonneg _) (h i j) 2)

/-- $\max(\lvert x\rvert, \tau) \le \lvert x\rvert + \tau$ for $\tau \ge 0$. -/
private theorem max_abs_le_abs_add {x τ : ℝ} (hτ : 0 ≤ τ) : max |x| τ ≤ |x| + τ :=
  max_le (le_add_of_nonneg_right hτ) (le_add_of_nonneg_left (abs_nonneg x))

/-- The modulus of a complex entry whose real and imaginary errors are at most
$U(\lvert p\rvert+\tau)$, $U(\lvert q\rvert+\tau)$. -/
private theorem sqrt_sq_add_sq_le_of_abs_le (U τ p q e₁ e₂ : ℝ) (hU : 0 ≤ U) (hτ : 0 ≤ τ)
    (h₁ : |e₁| ≤ U * (|p| + τ)) (h₂ : |e₂| ≤ U * (|q| + τ)) :
    √(e₁ ^ 2 + e₂ ^ 2) ≤ U * (√(p ^ 2 + q ^ 2) + 2 * τ) := by
  have hr := Real.sq_sqrt (add_nonneg (sq_nonneg p) (sq_nonneg q))
  have hr0 := Real.sqrt_nonneg (p ^ 2 + q ^ 2)
  have hp : |p| ≤ √(p ^ 2 + q ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg q])
  have hq : |q| ≤ √(p ^ 2 + q ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg p])
  have a1 := sq_le_sq' (abs_le.mp h₁).1 (abs_le.mp h₁).2
  have a2 := sq_le_sq' (abs_le.mp h₂).1 (abs_le.mp h₂).2
  have hcr : (|p| + τ) ^ 2 + (|q| + τ) ^ 2 ≤ (√(p ^ 2 + q ^ 2) + 2 * τ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hp hq) hτ, sq_abs p, sq_abs q]
  have hcr' := mul_le_mul_of_nonneg_left hcr (sq_nonneg U)
  refine Real.sqrt_le_iff.mpr ⟨mul_nonneg hU (by positivity), ?_⟩
  nlinarith

/-- Complex entry errors bounded by $U(\lvert p\rvert+\tau)$ in parts. -/
private theorem norm_sub_le_of_abs_re_im_le (z w : ℂ) {U τ : ℝ} (hU : 0 ≤ U) (hτ : 0 ≤ τ)
    (h₁ : |(z - w).re| ≤ U * (|z.re| + τ)) (h₂ : |(z - w).im| ≤ U * (|z.im| + τ)) :
    ‖z - w‖ ≤ U * (‖z‖ + 2 * τ) := by
  have := sqrt_sq_add_sq_le_of_abs_le U τ z.re z.im (z - w).re (z - w).im hU hτ h₁ h₂
  simpa [Complex.norm_def, Complex.normSq_apply, sq] using this

/-- A square-matrix bound from entrywise moduli: the spectral norm is at most
$u(\sqrt k\,\|\mathbf{Z}\|_2 + 2k\tau)$, via the Frobenius norm. -/
private theorem specNorm_le_of_norm_apply_le {k : ℕ} (Z E : Matrix (Fin k) (Fin k) ℂ) {u τ : ℝ}
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (h : ∀ i j, ‖E i j‖ ≤ u * (‖Z i j‖ + 2 * τ)) :
    specNorm E ≤ u * (√(k : ℝ) * specNorm Z + 2 * k * τ) := by
  have hW : frobNorm (Matrix.of fun i j => ((‖Z i j‖ : ℝ) : ℂ)) = frobNorm Z := by
    unfold frobNorm; simp
  have hJ : frobNorm (Matrix.of fun (_ _ : Fin k) => (1 : ℂ)) = k := by
    have h2 : frobNorm (Matrix.of fun (_ _ : Fin k) => (1 : ℂ)) ^ 2 = (k : ℝ) ^ 2 := by
      rw [frobNorm_sq_eq_sum]; simp; ring
    exact (pow_left_inj₀ (frobNorm_nonneg _) (Nat.cast_nonneg _) two_ne_zero).1 h2
  have hE : frobNorm E ≤ u * frobNorm Z + 2 * u * τ * k := by
    calc frobNorm E ≤ frobNorm (u • (Matrix.of fun i j => ((‖Z i j‖ : ℝ) : ℂ)) +
          (2 * u * τ) • (Matrix.of fun (_ _ : Fin k) => (1 : ℂ))) := by
          refine frobNorm_le_of_norm_apply_le fun i j => ?_
          have hc : (u • (Matrix.of fun i j => ((‖Z i j‖ : ℝ) : ℂ)) +
              (2 * u * τ) • (Matrix.of fun (_ _ : Fin k) => (1 : ℂ))) i j =
              (((u * ‖Z i j‖ + 2 * u * τ : ℝ)) : ℂ) := by
            simp
          rw [hc, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          nlinarith [h i j]
      _ ≤ frobNorm (u • (Matrix.of fun i j => ((‖Z i j‖ : ℝ) : ℂ))) +
          frobNorm ((2 * u * τ) • (Matrix.of fun (_ _ : Fin k) => (1 : ℂ))) :=
          frobNorm_add_le _ _
      _ = u * frobNorm Z + 2 * u * τ * k := by
          rw [frobNorm_real_smul, frobNorm_real_smul, hW, hJ, abs_of_nonneg hu,
            abs_of_nonneg (by positivity)]
  have hZ := frobNorm_le_sqrt_card_mul_specNorm Z
  rw [Fintype.card_fin] at hZ
  calc specNorm E ≤ frobNorm E := specNorm_le_frobNorm E
    _ ≤ u * frobNorm Z + 2 * u * τ * k := hE
    _ ≤ u * (√(k : ℝ) * specNorm Z + 2 * k * τ) := by
        nlinarith [mul_le_mul_of_nonneg_left hZ hu]

/-- Error of the stored division by a scalar: under `NLAlib.FloatMachine.IsArithAccurate` with
$u, \tau \ge 0$, for a stored $\mathbf{X}$ with Hermitian decoding and a stored $c$ with
$\bar c \ne 0$ and $\|\bar{\mathbf{X}}\|_2/\lvert\bar c\rvert \le \Omega$, with
$\mathbf{Z} = \bar{\mathbf{X}}/\bar c$,
$$\|\mathbf{Z} - \overline{\mathrm{hermScale}(\mathbf{X}, c)}\|_2 \le
u\bigl(\sqrt k\,\|\mathbf{Z}\|_2 + 2k\tau\bigr) \,.$$ -/
theorem specNorm_sub_decodeMatrix_hermScale_le (hM : M.IsArithAccurate dec u τ Ω μM)
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) {k : ℕ} {X : Matrix (Fin k) (Fin k) (F × F)}
    (hX : (decodeMatrix dec X).IsHermitian) {c : F} (hc : dec c ≠ 0)
    (hΩ : specNorm (decodeMatrix dec X) / |dec c| ≤ Ω) :
    specNorm ((dec c)⁻¹ • decodeMatrix dec X - decodeMatrix dec (M.hermScale X c)) ≤
      u * (√(k : ℝ) * specNorm ((dec c)⁻¹ • decodeMatrix dec X) + 2 * k * τ) := by
  have hdiag : ∀ i, dec (X i i).2 = 0 := fun i => by
    have h := congrArg Complex.im (hX.apply i i)
    simp [decodeMatrix, decodeComplex] at h
    linarith
  have hbound : ∀ i j, |dec (X i j).1 / dec c| ≤ Ω ∧ |dec (X i j).2 / dec c| ≤ Ω := by
    intro i j
    have hS' : specNorm (decodeMatrix dec X) ≤ Ω * |dec c| := (div_le_iff₀ (abs_pos.2 hc)).1 hΩ
    have h1 : |dec (X i j).1| ≤ specNorm (decodeMatrix dec X) :=
      (Complex.abs_re_le_norm (decodeMatrix dec X i j)).trans
        (norm_apply_le_specNorm (decodeMatrix dec X) i j)
    have h2 : |dec (X i j).2| ≤ specNorm (decodeMatrix dec X) :=
      (Complex.abs_im_le_norm (decodeMatrix dec X i j)).trans
        (norm_apply_le_specNorm (decodeMatrix dec X) i j)
    constructor <;> rw [abs_div, div_le_iff₀ (abs_pos.2 hc)] <;> linarith
  set Z : Matrix (Fin k) (Fin k) ℂ := (dec c)⁻¹ • decodeMatrix dec X with hZdef
  set E : Matrix (Fin k) (Fin k) ℂ := Z - decodeMatrix dec (M.hermScale X c) with hEdef
  have hZre : ∀ i j, (Z i j).re = dec (X i j).1 / dec c := fun i j => by
    rw [hZdef, Matrix.smul_apply, Complex.smul_re, smul_eq_mul, div_eq_inv_mul]; rfl
  have hZim : ∀ i j, (Z i j).im = dec (X i j).2 / dec c := fun i j => by
    rw [hZdef, Matrix.smul_apply, Complex.smul_im, smul_eq_mul, div_eq_inv_mul]; rfl
  have hWre : ∀ i j, i ≤ j →
      (decodeMatrix dec (M.hermScale X c) i j).re = dec (M.div (X i j).1 c) := by
    intro i j h
    rcases eq_or_lt_of_le h with rfl | hlt
    · simp [FloatMachine.hermScale, FloatMachine.hermFrom, decodeMatrix, decodeComplex]
    · simp [FloatMachine.hermScale, FloatMachine.hermFrom, decodeMatrix, decodeComplex, hlt]
  have hWim : ∀ i j, i < j →
      (decodeMatrix dec (M.hermScale X c) i j).im = dec (M.div (X i j).2 c) := by
    intro i j hlt
    simp [FloatMachine.hermScale, FloatMachine.hermFrom, decodeMatrix, decodeComplex, hlt]
  have hWim_diag : ∀ i, (decodeMatrix dec (M.hermScale X c) i i).im = 0 := fun i => by
    simp [FloatMachine.hermScale, FloatMachine.hermFrom, decodeMatrix, decodeComplex, hM.dec_zero]
  have hE_le : ∀ i j, i ≤ j → ‖E i j‖ ≤ u * (‖Z i j‖ + 2 * τ) := by
    intro i j hij
    refine norm_sub_le_of_abs_re_im_le (Z i j) (decodeMatrix dec (M.hermScale X c) i j) hu hτ
      ?_ ?_
    · rw [Complex.sub_re, hZre, hWre i j hij]
      exact ((hM.div (X i j).1 c hc) (hbound i j).1).trans
        (mul_le_mul_of_nonneg_left (max_abs_le_abs_add hτ) hu)
    · rcases eq_or_lt_of_le hij with rfl | hlt
      · rw [Complex.sub_im, hWim_diag, sub_zero, hZim, hdiag i, zero_div, abs_zero]
        positivity
      · rw [Complex.sub_im, hZim, hWim i j hlt]
        exact ((hM.div (X i j).2 c hc) (hbound i j).2).trans
          (mul_le_mul_of_nonneg_left (max_abs_le_abs_add hτ) hu)
  have hEH : (decodeMatrix dec (M.hermScale X c)).IsHermitian :=
    isHermitian_decodeMatrix_hermFrom hM (fun i j => (M.div (X i j).1 c, M.div (X i j).2 c))
      (fun i => M.div (X i i).1 c)
  have hZH : Z.IsHermitian := by
    rw [hZdef]
    exact hX.smul (star_trivial _)
  have hE_all : ∀ i j, ‖E i j‖ ≤ u * (‖Z i j‖ + 2 * τ) := by
    intro i j
    rcases le_total i j with h | h
    · exact hE_le i j h
    · have hEH' : E.IsHermitian := hZH.sub hEH
      rw [← hEH'.apply i j, ← hZH.apply i j, norm_star, norm_star]
      exact hE_le j i h
  exact specNorm_le_of_norm_apply_le Z E hu hτ hE_all

/-- One part of the scaled Hermitian part: a rounded sum then a rounded division by $c$ errs by
$\tfrac52u(\lvert a/c\rvert+\tau)$. -/
private theorem abs_div_sub_le_of_isRoundingOf (a c s s' S u τ Ω : ℝ) (hc : 1 ≤ |c|) (hu : 0 ≤ u)
    (hu1 : u ≤ 1 / 2) (hτ : 0 ≤ τ) (ha : |a| ≤ 2 * S) (hΩ : 3 * S + τ ≤ Ω)
    (hadd : |a| ≤ Ω → |a - s| ≤ u * max |a| τ)
    (hdiv : |s / c| ≤ Ω → |s / c - s'| ≤ u * max |s / c| τ) :
    |a / c - s'| ≤ 5 / 2 * u * (|a / c| + τ) := by
  have hc0 : 0 < |c| := by linarith
  have hc0' : c ≠ 0 := fun h => by simp [h] at hc; linarith
  have hS : 0 ≤ S := by linarith [abs_nonneg a]
  have hA := hadd (ha.trans (by linarith))
  have hmax : max |a| τ ≤ |a| + τ := max_abs_le_abs_add hτ
  have hs : |s| ≤ 3 * S + τ := by
    have h2 : |s| ≤ |a| + |a - s| := by simpa using abs_sub a (a - s)
    have h3 : u * max |a| τ ≤ 1 / 2 * (2 * S + τ) := by
      nlinarith [mul_le_mul_of_nonneg_right hu1 (by positivity : (0 : ℝ) ≤ |a| + τ)]
    linarith
  have hB := hdiv (by rw [abs_div]; exact (div_le_self (abs_nonneg _) hc).trans (by linarith))
  have hτc : τ ≤ τ * |c| := le_mul_of_one_le_right hτ hc
  have e1 : |(a - s) / c| ≤ u * (|a / c| + τ) := by
    rw [abs_div, div_le_iff₀ hc0]
    have hq : |a / c| * |c| = |a| := by rw [abs_div, div_mul_cancel₀ _ hc0.ne']
    nlinarith [mul_le_mul_of_nonneg_left hmax hu, mul_le_mul_of_nonneg_left hτc hu]
  have ht : |s / c| ≤ |a / c| + u * (|a / c| + τ) := by
    have h := abs_sub (a / c) ((a - s) / c)
    have hh : a / c - (a - s) / c = s / c := by ring
    rw [hh] at h
    linarith
  have e2 : |s / c - s'| ≤ u * (|s / c| + τ) :=
    hB.trans (mul_le_mul_of_nonneg_left (max_abs_le_abs_add hτ) hu)
  calc |a / c - s'| = |(a - s) / c + (s / c - s')| := by ring_nf
    _ ≤ |(a - s) / c| + |s / c - s'| := abs_add_le _ _
    _ ≤ u * (|a / c| + τ) + u * (|s / c| + τ) := add_le_add e1 e2
    _ ≤ 5 / 2 * u * (|a / c| + τ) := by
        nlinarith [mul_nonneg (mul_nonneg hu (add_nonneg (abs_nonneg (a / c)) hτ))
          (sub_nonneg.2 hu1)]

/-- Error of the stored scaled Hermitian part: under `NLAlib.FloatMachine.IsArithAccurate` with
$0 \le u \le 1/2$, $\tau \ge 0$, for a stored $\mathbf{X}$ and a stored $c$ with
$\lvert \bar c \rvert \ge 1$ and $3\|\bar{\mathbf{X}}\|_2 + \tau \le \Omega$, with
$\mathbf{Z} = (\bar{\mathbf{X}} + \bar{\mathbf{X}}^{\mathsf{H}})/\bar c$,
$$\|\mathbf{Z} - \overline{\mathrm{hermAvg}(\mathbf{X}, c)}\|_2 \le
3u\bigl(\sqrt k\,\|\mathbf{Z}\|_2 + 2k\tau\bigr) \,.$$ -/
theorem specNorm_sub_decodeMatrix_hermAvg_le (hM : M.IsArithAccurate dec u τ Ω μM)
    (hu : 0 ≤ u) (hu₁ : u ≤ 1 / 2) (hτ : 0 ≤ τ) {k : ℕ} (X : Matrix (Fin k) (Fin k) (F × F))
    {c : F} (hc : 1 ≤ |dec c|) (hΩ : 3 * specNorm (decodeMatrix dec X) + τ ≤ Ω) :
    specNorm ((dec c)⁻¹ • (decodeMatrix dec X + (decodeMatrix dec X)ᴴ) -
      decodeMatrix dec (M.hermAvg X c)) ≤
        3 * u * (√(k : ℝ) * specNorm ((dec c)⁻¹ • (decodeMatrix dec X + (decodeMatrix dec X)ᴴ)) +
          2 * k * τ) := by
  have hc0 : dec c ≠ 0 := fun h => by simp [h] at hc; linarith
  have hxS : ∀ i j, |dec (X i j).1| ≤ specNorm (decodeMatrix dec X) ∧
      |dec (X i j).2| ≤ specNorm (decodeMatrix dec X) := fun i j =>
    ⟨(Complex.abs_re_le_norm (decodeMatrix dec X i j)).trans
        (norm_apply_le_specNorm (decodeMatrix dec X) i j),
     (Complex.abs_im_le_norm (decodeMatrix dec X i j)).trans
        (norm_apply_le_specNorm (decodeMatrix dec X) i j)⟩
  set Z : Matrix (Fin k) (Fin k) ℂ :=
    (dec c)⁻¹ • (decodeMatrix dec X + (decodeMatrix dec X)ᴴ) with hZdef
  set E : Matrix (Fin k) (Fin k) ℂ := Z - decodeMatrix dec (M.hermAvg X c) with hEdef
  have hZre : ∀ i j, (Z i j).re = (dec (X i j).1 + dec (X j i).1) / dec c := fun i j => by
    rw [hZdef, Matrix.smul_apply, Complex.smul_re, smul_eq_mul, div_eq_inv_mul]
    simp [Matrix.add_apply, Matrix.conjTranspose_apply, decodeMatrix, decodeComplex]
  have hZim : ∀ i j, (Z i j).im = (dec (X i j).2 - dec (X j i).2) / dec c := fun i j => by
    rw [hZdef, Matrix.smul_apply, Complex.smul_im, smul_eq_mul, div_eq_inv_mul]
    simp [Matrix.add_apply, Matrix.conjTranspose_apply, decodeMatrix, decodeComplex, sub_eq_add_neg]
  have hWre : ∀ i j, i ≤ j →
      (decodeMatrix dec (M.hermAvg X c) i j).re = dec (M.div (M.add (X i j).1 (X j i).1) c) := by
    intro i j h
    rcases eq_or_lt_of_le h with rfl | hlt
    · simp [FloatMachine.hermAvg, FloatMachine.hermFrom, decodeMatrix, decodeComplex]
    · simp [FloatMachine.hermAvg, FloatMachine.hermFrom, decodeMatrix, decodeComplex, hlt]
  have hWim : ∀ i j, i < j →
      (decodeMatrix dec (M.hermAvg X c) i j).im = dec (M.div (M.sub (X i j).2 (X j i).2) c) := by
    intro i j hlt
    simp [FloatMachine.hermAvg, FloatMachine.hermFrom, decodeMatrix, decodeComplex, hlt]
  have hWim_diag : ∀ i, (decodeMatrix dec (M.hermAvg X c) i i).im = 0 := fun i => by
    simp [FloatMachine.hermAvg, FloatMachine.hermFrom, decodeMatrix, decodeComplex, hM.dec_zero]
  have hU0 : 0 ≤ 5 / 2 * u := by linarith
  have hE_le : ∀ i j, i ≤ j → ‖E i j‖ ≤ 5 / 2 * u * (‖Z i j‖ + 2 * τ) := by
    intro i j hij
    refine norm_sub_le_of_abs_re_im_le (Z i j) (decodeMatrix dec (M.hermAvg X c) i j) hU0 hτ ?_ ?_
    · rw [Complex.sub_re, hZre, hWre i j hij]
      have ha : |dec (X i j).1 + dec (X j i).1| ≤ 2 * specNorm (decodeMatrix dec X) :=
        (abs_add_le _ _).trans (by linarith [(hxS i j).1, (hxS j i).1])
      exact abs_div_sub_le_of_isRoundingOf (dec (X i j).1 + dec (X j i).1) (dec c)
        (dec (M.add (X i j).1 (X j i).1)) (dec (M.div (M.add (X i j).1 (X j i).1) c))
        (specNorm (decodeMatrix dec X)) u τ Ω hc hu hu₁ hτ ha hΩ (hM.add _ _) (hM.div _ _ hc0)
    · rcases eq_or_lt_of_le hij with rfl | hlt
      · rw [Complex.sub_im, hWim_diag, sub_zero, hZim]
        simp only [sub_self, zero_div, abs_zero, zero_add]
        exact mul_nonneg hU0 hτ
      · rw [Complex.sub_im, hZim, hWim i j hlt]
        have ha : |dec (X i j).2 - dec (X j i).2| ≤ 2 * specNorm (decodeMatrix dec X) :=
          (abs_sub _ _).trans (by linarith [(hxS i j).2, (hxS j i).2])
        exact abs_div_sub_le_of_isRoundingOf (dec (X i j).2 - dec (X j i).2) (dec c)
          (dec (M.sub (X i j).2 (X j i).2)) (dec (M.div (M.sub (X i j).2 (X j i).2) c))
          (specNorm (decodeMatrix dec X)) u τ Ω hc hu hu₁ hτ ha hΩ (hM.sub _ _) (hM.div _ _ hc0)
  have hH : (decodeMatrix dec X + (decodeMatrix dec X)ᴴ).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  have hZH : Z.IsHermitian := by
    rw [hZdef]
    exact hH.smul (star_trivial _)
  have hEH : (decodeMatrix dec (M.hermAvg X c)).IsHermitian :=
    isHermitian_decodeMatrix_hermFrom hM
      (fun i j => (M.div (M.add (X i j).1 (X j i).1) c, M.div (M.sub (X i j).2 (X j i).2) c))
      (fun i => M.div (M.add (X i i).1 (X i i).1) c)
  have hEH' : E.IsHermitian := hZH.sub hEH
  have hE_all : ∀ i j, ‖E i j‖ ≤ 3 * u * (‖Z i j‖ + 2 * τ) := by
    intro i j
    rcases le_total i j with h | h
    · nlinarith [hE_le i j h, mul_nonneg hu (add_nonneg (norm_nonneg (Z i j))
        (mul_nonneg zero_le_two hτ))]
    · rw [← hEH'.apply i j, ← hZH.apply i j, norm_star, norm_star]
      nlinarith [hE_le j i h, mul_nonneg hu (add_nonneg (norm_nonneg (Z j i))
        (mul_nonneg zero_le_two hτ))]
  exact specNorm_le_of_norm_apply_le Z E (by linarith) hτ hE_all

private lemma abs_sum_range_sub_foldl_add_le (hM : M.IsArithAccurate dec u τ Ω μM)
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) {k : ℕ} (hku : k * u ≤ 1 / 2) (x : ℕ → F) {S : ℝ}
    (hS : ∑ i ∈ Finset.range k, |dec (x i)| ≤ S) (hΩ : 2 * (S + k * τ) ≤ Ω) :
    ∀ n ≤ k, |∑ i ∈ Finset.range n, dec (x i) -
      dec ((List.range n).foldl (fun s i => M.add s (x i)) M.zero)| ≤ 2 * n * u * (S + τ) := by
  have hS0 : 0 ≤ S := le_trans (Finset.sum_nonneg fun i _ => abs_nonneg _) hS
  intro n
  induction n with
  | zero => intro _; simp [hM.dec_zero]
  | succ n ih =>
    intro hn
    have ih := ih (by omega)
    set t := dec ((List.range n).foldl (fun s i => M.add s (x i)) M.zero)
    have hfold : (List.range (n + 1)).foldl (fun s i => M.add s (x i)) M.zero =
        M.add ((List.range n).foldl (fun s i => M.add s (x i)) M.zero) (x n) := by
      rw [List.range_succ, List.foldl_append]; rfl
    rw [hfold, Finset.sum_range_succ]
    have hsum : |∑ i ∈ Finset.range (n + 1), dec (x i)| ≤ S :=
      (Finset.abs_sum_le_sum_abs _ _).trans <| le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr hn) fun i _ _ => abs_nonneg _) hS
    rw [Finset.sum_range_succ] at hsum
    have hnu : 2 * n * u ≤ 1 := by
      have : (n : ℝ) + 1 ≤ k := by exact_mod_cast hn
      nlinarith
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have ha : |t + dec (x n)| ≤ S + 2 * n * u * (S + τ) := by
      have := abs_sub (∑ i ∈ Finset.range n, dec (x i) + dec (x n))
        (∑ i ∈ Finset.range n, dec (x i) - t)
      rw [show ∑ i ∈ Finset.range n, dec (x i) + dec (x n) - (∑ i ∈ Finset.range n, dec (x i) - t)
        = t + dec (x n) by ring] at this
      linarith
    have hr := hM.add _ (x n) (by nlinarith)
    have hr' : |t + dec (x n) - dec (M.add _ (x n))| ≤ u * (|t + dec (x n)| + τ) :=
      hr.trans (mul_le_mul_of_nonneg_left (max_abs_le_abs_add hτ) hu)
    calc |∑ i ∈ Finset.range n, dec (x i) + dec (x n) - dec (M.add _ (x n))|
        ≤ |∑ i ∈ Finset.range n, dec (x i) - t| + |t + dec (x n) - dec (M.add _ (x n))| := by
          rw [show ∑ i ∈ Finset.range n, dec (x i) + dec (x n) - dec (M.add _ (x n)) =
            (∑ i ∈ Finset.range n, dec (x i) - t) + (t + dec (x n) - dec (M.add _ (x n))) by
              ring]
          exact abs_add_le _ _
      _ ≤ 2 * n * u * (S + τ) + u * (S + 2 * n * u * (S + τ) + τ) := by
          gcongr
          exact hr'.trans (by gcongr)
      _ ≤ 2 * (n + 1 : ℕ) * u * (S + τ) := by
          push_cast
          nlinarith [mul_nonneg hu (add_nonneg hS0 hτ), mul_nonneg (mul_nonneg hu hu)
            (add_nonneg hS0 hτ)]

/-- **Error of the rounded trace**: under `NLAlib.FloatMachine.IsArithAccurate` with $u, \tau \ge 0$
and $ku \le 1/2$, for a stored $k \times k$ $\mathbf{X}$ with real parts of the diagonal
$x_i$ and $2(\sum_i \lvert x_i \rvert + k\tau) \le \Omega$,
$$\Bigl\lvert \sum_i x_i - \overline{\mathrm{traceRe}(\mathbf{X})} \Bigr\rvert \le
2ku\Bigl(\sum_i \lvert x_i \rvert + k\tau\Bigr) \,.$$
[Higham2002, (4.4)], there with $\gamma_{k-1}$ and $\tau = 0$. -/
theorem abs_sum_sub_traceRe_le (hM : M.IsArithAccurate dec u τ Ω μM) (hu : 0 ≤ u)
    (hτ : 0 ≤ τ) {k : ℕ} (hku : k * u ≤ 1 / 2) (X : Matrix (Fin k) (Fin k) (F × F))
    (hΩ : 2 * (∑ i, |dec (X i i).1| + k * τ) ≤ Ω) :
    |∑ i, dec (X i i).1 - dec (M.traceRe X)| ≤ 2 * k * u * (∑ i, |dec (X i i).1| + k * τ) := by
  set x : ℕ → F := fun i => if h : i < k then (X ⟨i, h⟩ ⟨i, h⟩).1 else M.zero
  have hx : ∀ a : Fin k, x a = (X a a).1 := fun a => by simp [x, a.isLt]
  have hsum : ∀ f : F → ℝ, ∑ i, f (X i i).1 = ∑ i ∈ Finset.range k, f (x i) := fun f => by
    rw [← Fin.sum_univ_eq_sum_range (fun i => f (x i))]
    simp only [hx]
  have htr : M.traceRe X = (List.range k).foldl (fun s i => M.add s (x i)) M.zero := by
    rw [← List.map_coe_finRange_eq_range, List.foldl_map]
    simp only [hx]
    rfl
  rw [hsum (fun y => dec y), hsum (fun y => |dec y|), htr] at *
  refine (abs_sum_range_sub_foldl_add_le hM hu hτ hku x le_rfl hΩ k le_rfl).trans ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    gcongr
    nlinarith

end FloatMachine.IsArithAccurate

end Accuracy


section RoundingBounds

/-- A rounding $z$ of $a$ (`NLAlib.IsRoundingOf` with $u, \tau \ge 0$ and $\lvert a\rvert \le
\Omega$) has $\lvert a - z\rvert \le u(\lvert a\rvert + \tau)$. -/
theorem abs_sub_le_of_isRoundingOf {u τ Ω a z : ℝ} (h : IsRoundingOf u τ Ω a z)
    (ha : |a| ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) : |a - z| ≤ u * (|a| + τ) :=
  (h ha).trans (mul_le_mul_of_nonneg_left (max_le_add_of_nonneg (abs_nonneg a) hτ) hu)

/-- A rounding $z$ of $0 \le a \le \Omega$ (`NLAlib.IsRoundingOf` with $u, \tau \ge 0$) has
$a - u(a + \tau) \le z \le a + u(a + \tau)$. -/
theorem le_and_le_of_isRoundingOf {u τ Ω a z : ℝ} (h : IsRoundingOf u τ Ω a z) (ha0 : 0 ≤ a)
    (ha : a ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) : a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) := by
  have h1 := abs_sub_le_of_isRoundingOf h (by rwa [abs_of_nonneg ha0]) hu hτ
  rw [abs_of_nonneg ha0] at h1
  constructor <;> linarith [(abs_le.mp h1).1, (abs_le.mp h1).2]

end RoundingBounds

end NLAlib
