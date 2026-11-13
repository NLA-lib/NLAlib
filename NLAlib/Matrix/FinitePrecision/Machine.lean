/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Orthonormal
public import NLAlib.Matrix.Factorizations.Triangular
public import NLAlib.Matrix.Norms.Spectral
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.FinitePrecision.BinaryFloat

/-!
# A floating-point machine with black-box matrix multiplication and QR

Fast dense algorithms are analysed against black-box primitives with normwise guarantees, not
against an implementation ([DemmelDumitriuHoltzKleinberg2007]; [DemmelDumitriuHoltz2007];
[Shah2024, Section 1.3]). This file fixes **what an algorithm may do with data**:
`NLAlib.FloatMachine F Su Sg` bundles every operation on stored numbers of an abstract type `F`
(rounded $+, -, \times, /$, exact negation, exact comparison, rounded conversion of a natural
number, exact conversion to a natural number by the floor, the constants $0$ and $1$), the
matrix-multiplication and QR black boxes on matrices of stored complex numbers `F × F` (real and
imaginary parts, as IEEE arithmetic stores them), and the two samplers, from ideal samples of
abstract types `Su`, `Sg` to stored numbers. An algorithm written generically over `F`, `Su` and
`Sg` touches data only through the machine: `F` has no arithmetic instance, so exact arithmetic on
computed values does not typecheck (design note
`docs/design/Eigensolvers-HermitianDiagonalization.md`, §2.0).

The analysis decodes stored numbers by `dec : F → ℝ` and states the machine's contract
`NLAlib.FloatMachine.IsAccurate`: each scalar operation returns a rounding of its exact result on
the decoded operands, one rounding per operation (`NLAlib.IsRoundingOf`: relative error $u$
above the floor $\tau$, in the range $\Omega$), negation, comparisons, the floor conversion,
$0$ and $1$ are exact, and the black boxes and samplers
meet the normwise contracts `NLAlib.IsMatMulErr`, `NLAlib.IsQRErr`, `NLAlib.IsUnifSampler`,
`NLAlib.IsNormalSampler` through the decoding. The floor $\tau$ and range $\Omega$ are $0$ and
arbitrary with an unbounded exponent; a bounded-exponent machine meets the contract with
$\tau > 0$ (§12 of the note).

## Main definitions

* `NLAlib.MatMulMap`, `NLAlib.QRMap`: the types of the routines on a type of stored entries.
* `NLAlib.IsRoundingOf`: $z$ is a rounding of $a$.
* `NLAlib.IsMatMulErr`, `NLAlib.IsQRErr`, `NLAlib.IsUnifSampler`, `NLAlib.IsNormalSampler`.
* `NLAlib.FloatMachine`, `NLAlib.decodeComplex`, `NLAlib.decodeMatrix`,
  `NLAlib.FloatMachine.IsArithAccurate`, `NLAlib.FloatMachine.IsAccurate`.

## Main results

* `NLAlib.exists_floatMachine_isAccurate`: the exact machine.
* `NLAlib.exists_floatMachine_isAccurate_binaryFloatRound`: a bounded-format machine.
* `NLAlib.IsMatMulErr.of_specNorm_mul_sub_le_add`: from a mixed bound to the floor form.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- A **matrix-multiplication routine** on matrices with entries in `K`, indexed by `Fin`, of
compatible shapes. -/
abbrev MatMulMap (K : Type*) : Type _ :=
  ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) K → Matrix (Fin m) (Fin n) K → Matrix (Fin l) (Fin n) K

/-- A **QR routine** on matrices with entries in `K`: an $m \times n$ matrix to a square
$m \times m$ factor and an $m \times n$ factor. -/
abbrev QRMap (K : Type*) : Type _ :=
  ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) K → Matrix (Fin m) (Fin m) K × Matrix (Fin m) (Fin n) K

/-- `IsRoundingOf u τ Ω a z`: **$z$ is a rounding of $a$** with unit roundoff $u$, floor $\tau$
and range $\Omega$: if $\lvert a \rvert \le \Omega$ then $\lvert a - z \rvert \le
u\max(\lvert a \rvert, \tau)$. At $\tau = 0$ this is the standard model [Higham2002, (2.4)]; a
floor $\tau > 0$ is the absolute error of gradual underflow, $\Omega$ the overflow threshold. -/
def IsRoundingOf (u τ Ω a z : ℝ) : Prop :=
  |a| ≤ Ω → |a - z| ≤ u * max |a| τ

variable {K 𝕜 : Type*} [RCLike 𝕜]

/-- `IsMatMulErr dec u τ Ω μ mm`: **the routine `mm` multiplies with normwise error
$\mu(d)\,u$**, read through the decoding `dec` of stored entries: for stored $\mathbf{A}$,
$\mathbf{B}$ with decodings $\bar{\mathbf{A}}$, $\bar{\mathbf{B}}$,
$\|\bar{\mathbf{A}}\|_2\|\bar{\mathbf{B}}\|_2 \le \Omega$ and $d$ the largest dimension,
$$\|\bar{\mathbf{A}}\bar{\mathbf{B}} - \overline{\mathrm{mm}(\mathbf{A}, \mathbf{B})}\|_2 \le
\mu(d)\,u\max(\|\bar{\mathbf{A}}\|_2\|\bar{\mathbf{B}}\|_2, \tau) \,,$$
and when $\bar{\mathbf{B}} = \bar{\mathbf{A}}^{\mathsf{H}}$ the decoded product is exactly
Hermitian. [Shah2024, Definition 1.1], with the identity decoding, $\tau = 0$ and no range
there. -/
structure IsMatMulErr (dec : K → 𝕜) (u τ Ω : ℝ) (μ : ℕ → ℝ) (mm : MatMulMap K) : Prop where
  /-- The normwise error bound in range. -/
  specNorm_mul_sub_le : ∀ {l m n : ℕ} (A : Matrix (Fin l) (Fin m) K)
    (B : Matrix (Fin m) (Fin n) K), specNorm (A.map dec) * specNorm (B.map dec) ≤ Ω →
      specNorm (A.map dec * B.map dec - (mm A B).map dec) ≤
        μ (max l (max m n)) * u * max (specNorm (A.map dec) * specNorm (B.map dec)) τ
  /-- A product with its own conjugate transpose is computed exactly Hermitian. -/
  isHermitian_of_map_eq_conjTranspose : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (B : Matrix (Fin n) (Fin m) K), B.map dec = (A.map dec)ᴴ → ((mm A B).map dec).IsHermitian

/-- `IsQRErr dec u τ Ω μ qr`: **the routine `qr` computes a backward-stable QR factorization**,
read through the decoding `dec`: for stored $\mathbf{A}$ with decoding $\bar{\mathbf{A}}$,
$\|\bar{\mathbf{A}}\|_2 \le \Omega$, $(\mathbf{Q}, \mathbf{R}) = \mathrm{qr}(\mathbf{A})$ and
$d = \max(m, n)$, the decoded $\bar{\mathbf{R}}$ is upper trapezoidal and there is a unitary
$\mathbf{Q}'$ with
$$\|\mathbf{Q}' - \bar{\mathbf{Q}}\|_2 \le \mu(d)\,u \,, \qquad
\|\bar{\mathbf{A}} - \mathbf{Q}'\bar{\mathbf{R}}\|_2 \le \mu(d)\,u\max(\|\bar{\mathbf{A}}\|_2,
\tau) \,.$$
[Shah2024, Definition 1.2], with the identity decoding, $\tau = 0$ and no range there. -/
def IsQRErr (dec : K → 𝕜) (u τ Ω : ℝ) (μ : ℕ → ℝ) (qr : QRMap K) : Prop :=
  ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) K), specNorm (A.map dec) ≤ Ω →
    IsUpperTrapezoidal ((qr A).2.map dec) ∧
      ∃ Q' : Matrix (Fin m) (Fin m) 𝕜, HasOrthonormalCols Q' ∧
        specNorm (Q' - (qr A).1.map dec) ≤ μ (max m n) * u ∧
        specNorm (A.map dec - Q' * (qr A).2.map dec) ≤
          μ (max m n) * u * max (specNorm (A.map dec)) τ

/-- `IsUnifSampler dec u τ unif`: **`unif` turns an ideal uniform seed into a computed shift**:
for a stored scale $s$ with $\bar s \ge 0$ and a seed $v \in [-1, 1]$, the computed
$c = \mathrm{unif}(s, v)$ has $\lvert \bar c \rvert \le \bar s$ and
$\lvert \bar s v - \bar c \rvert \le u\max(\bar s, \tau)$ (floor $\tau$ for gradual underflow,
$0$ with an unbounded exponent). With $v$ uniform on $[-1, 1]$ this is the coupling
of [Shah2024, Definition 1.3]. -/
def IsUnifSampler {F : Type*} (dec : F → ℝ) (u τ : ℝ) (unif : F → ℝ → F) : Prop :=
  ∀ (s : F) (v : ℝ), 0 ≤ dec s → v ∈ Set.Icc (-1 : ℝ) 1 →
    |dec (unif s v)| ≤ dec s ∧ |dec s * v - dec (unif s v)| ≤ u * max (dec s) τ

/-- `IsNormalSampler dec u c τ Ω normal`: **`normal` turns an ideal complex Gaussian sample into
a stored one** with relative error $c\,u$ above the floor $\tau$: $\lvert z -
\overline{\mathrm{normal}(z)} \rvert \le c\,u\max(\lvert z \rvert, \tau)$ for every
$z \in \mathbb{C}$ with $\lvert z \rvert \le \Omega$. With $z$ standard complex Gaussian this is the
coupling of [Shah2024, Definition 1.4]. -/
def IsNormalSampler {K : Type*} (dec : K → ℂ) (u c τ Ω : ℝ) (normal : ℂ → K) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ Ω → ‖z - dec (normal z)‖ ≤ c * u * max ‖z‖ τ

/-- A **floating-point machine** with stored numbers `F`, ideal seeds `Su` and ideal Gaussian
samples `Sg`: the only operations an algorithm written over it may apply to data. Stored complex
numbers are pairs `F × F` (real and imaginary parts).
[Shah2024, Sections 1.2, 1.3]. -/
structure FloatMachine (F Su Sg : Type*) where
  /-- The stored zero. -/
  zero : F
  /-- The stored one. -/
  one : F
  /-- Rounded conversion of a natural number. -/
  ofNat : ℕ → F
  /-- Rounded addition. -/
  add : F → F → F
  /-- Rounded subtraction. -/
  sub : F → F → F
  /-- Rounded multiplication. -/
  mul : F → F → F
  /-- Rounded division. -/
  div : F → F → F
  /-- Negation. -/
  neg : F → F
  /-- Comparison of stored numbers. -/
  le : F → F → Bool
  /-- Conversion to a natural number: the floor of a nonnegative stored number. -/
  toNat : F → ℕ
  /-- Matrix multiplication of stored complex matrices. -/
  mm : MatMulMap (F × F)
  /-- QR factorization of stored complex matrices. -/
  qr : QRMap (F × F)
  /-- The uniform sampler: a stored scale and an ideal seed to a stored shift. -/
  unif : F → Su → F
  /-- The normal sampler: an ideal Gaussian sample to a stored complex number. -/
  normal : Sg → F × F

/-- The **decoding of a stored complex number** $(x, y)$: $\bar x + i\bar y$. -/
def decodeComplex {F : Type*} (dec : F → ℝ) (z : F × F) : ℂ :=
  ⟨dec z.1, dec z.2⟩

/-- The **decoding of a stored complex matrix**, entrywise by `NLAlib.decodeComplex`. -/
def decodeMatrix {F : Type*} {m n : Type*} (dec : F → ℝ) (A : Matrix m n (F × F)) :
    Matrix m n ℂ :=
  A.map (decodeComplex dec)

/-- `M.IsArithAccurate dec u τ Ω μM`: **the arithmetic contract of a floating-point machine** at
decoding `dec`, unit roundoff $u$, floor $\tau$, range $\Omega$ and product constant
$\mu_{\mathrm{MM}}$: zero and one are exact; rounded conversion, addition, subtraction,
multiplication and division (by a nonzero) return a rounding (`NLAlib.IsRoundingOf`) of the exact
result on the decoded operands; negation and comparisons are exact; conversion to a natural number
is the exact floor $\lfloor\bar x\rfloor_+$; the matrix-multiplication black box meets
`NLAlib.IsMatMulErr` through the decoding. The part of `NLAlib.FloatMachine.IsAccurate` that says
nothing about the QR black box and the samplers. [Shah2024, Section 1.2 and Definitions 1.1–1.2],
with componentwise complex storage. -/
structure FloatMachine.IsArithAccurate {F : Type*} (M : FloatMachine F ℝ ℂ) (dec : F → ℝ)
    (u τ Ω : ℝ) (μM : ℕ → ℝ) : Prop where
  /-- Zero is exact. -/
  dec_zero : dec M.zero = 0
  /-- One is exact. -/
  dec_one : dec M.one = 1
  /-- Conversion rounds. -/
  ofNat : ∀ k : ℕ, IsRoundingOf u τ Ω k (dec (M.ofNat k))
  /-- Addition rounds. -/
  add : ∀ x y, IsRoundingOf u τ Ω (dec x + dec y) (dec (M.add x y))
  /-- Subtraction rounds. -/
  sub : ∀ x y, IsRoundingOf u τ Ω (dec x - dec y) (dec (M.sub x y))
  /-- Multiplication rounds. -/
  mul : ∀ x y, IsRoundingOf u τ Ω (dec x * dec y) (dec (M.mul x y))
  /-- Division by a nonzero rounds. -/
  div : ∀ x y, dec y ≠ 0 → IsRoundingOf u τ Ω (dec x / dec y) (dec (M.div x y))
  /-- Negation is exact. -/
  dec_neg : ∀ x, dec (M.neg x) = -dec x
  /-- Comparisons are exact. -/
  le_iff : ∀ x y, M.le x y = true ↔ dec x ≤ dec y
  /-- Conversion to a natural number is the exact floor (`0` below zero), as IEEE truncation. -/
  toNat_eq : ∀ x, M.toNat x = ⌊dec x⌋₊
  /-- The matrix-multiplication contract. -/
  isMatMulErr : IsMatMulErr (decodeComplex dec) u τ Ω μM M.mm

/-- `M.IsAccurate dec u τ Ω μM μQ cN`: **the contract of a floating-point machine** at decoding
`dec`, unit roundoff $u$, floor $\tau$, range $\Omega$, black-box constants $\mu_{\mathrm{MM}}$,
$\mu_{\mathrm{QR}}$ and normal-sampler constant $c_{\mathrm N}$: the arithmetic contract
`NLAlib.FloatMachine.IsArithAccurate` (rounded scalar operations, exact negation, comparisons,
floor conversion, $0$ and $1$, and `NLAlib.IsMatMulErr` for the products), and the QR black box
and the samplers meet `NLAlib.IsQRErr`, `NLAlib.IsUnifSampler` and `NLAlib.IsNormalSampler`
through the decoding. [Shah2024, Section 1.2 and Definitions 1.1–1.4], with componentwise complex
storage. -/
structure FloatMachine.IsAccurate {F : Type*} (M : FloatMachine F ℝ ℂ) (dec : F → ℝ)
    (u τ Ω : ℝ) (μM μQ : ℕ → ℝ) (cN : ℝ) : Prop extends M.IsArithAccurate dec u τ Ω μM where
  /-- The QR contract. -/
  isQRErr : IsQRErr (decodeComplex dec) u τ Ω μQ M.qr
  /-- The uniform-sampler contract. -/
  isUnifSampler : IsUnifSampler dec u τ M.unif
  /-- The normal-sampler contract. -/
  isNormalSampler : IsNormalSampler (decodeComplex dec) u cN τ Ω M.normal

section Witnesses

open scoped Matrix

/-- A stored pair of reals as a complex number. -/
private def toCplx (z : ℝ × ℝ) : ℂ := ⟨z.1, z.2⟩

/-- A complex number as a stored pair of reals. -/
private def ofCplx (w : ℂ) : ℝ × ℝ := (w.re, w.im)

private lemma map_ofCplx_toCplx {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) :
    (X.map ofCplx).map toCplx = X := by
  ext i j; rfl

private lemma exists_qrFactors {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin n) ℂ,
      HasOrthonormalCols p.1 ∧ IsUpperTrapezoidal p.2 ∧ A = p.1 * p.2 := by
  obtain ⟨Q, R, hQ, hR, hA⟩ := exists_hasOrthonormalCols_mul_isUpperTrapezoidal A
  exact ⟨(Q, R), hQ, hR, hA⟩

/-- The exact QR factors of a complex matrix (a choice). -/
private noncomputable def qrFactors {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin n) ℂ :=
  Classical.choose (exists_qrFactors A)

/-- The exact machine on stored reals and complex pairs: every operation is exact. -/
private noncomputable def exactMachine : FloatMachine ℝ ℝ ℂ where
  zero := 0
  one := 1
  ofNat k := (k : ℝ)
  add x y := x + y
  sub x y := x - y
  mul x y := x * y
  div x y := x / y
  neg x := -x
  le x y := if x ≤ y then true else false
  toNat x := ⌊x⌋₊
  mm := fun {_ _ _} A B => ((A.map toCplx) * (B.map toCplx)).map ofCplx
  qr := fun {_ _} A =>
    (((qrFactors (A.map toCplx)).1).map ofCplx, ((qrFactors (A.map toCplx)).2).map ofCplx)
  unif s v := s * v
  normal z := ofCplx z

private lemma exactMachine_mm_decode {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (ℝ × ℝ))
    (B : Matrix (Fin m) (Fin n) (ℝ × ℝ)) :
    (exactMachine.mm A B).map (decodeComplex id) =
      A.map (decodeComplex id) * B.map (decodeComplex id) :=
  map_ofCplx_toCplx _

private lemma isRounding_exact {u τ Ω a z : ℝ} (h : a = z) (hu : u = 0) :
    IsRoundingOf u τ Ω a z :=
  fun _ => by simp [h, hu]

private lemma exactMachine_isMatMulErr (u τ Ω : ℝ) (μ : ℕ → ℝ) (hu : 0 ≤ u)
    (hμ : ∀ d, 0 ≤ μ d) : IsMatMulErr (decodeComplex id) u τ Ω μ exactMachine.mm where
  specNorm_mul_sub_le A B _ := by
    rw [exactMachine_mm_decode, sub_self, specNorm_zero]
    exact mul_nonneg (mul_nonneg (hμ _) hu) (le_max_of_le_left (by positivity))
  isHermitian_of_map_eq_conjTranspose A B hB := by
    rw [exactMachine_mm_decode, hB]
    exact Matrix.isHermitian_mul_conjTranspose_self _

private lemma exactMachine_isQRErr (u τ Ω : ℝ) (μ : ℕ → ℝ) (hu : 0 ≤ u)
    (hμ : ∀ d, 0 ≤ μ d) : IsQRErr (decodeComplex id) u τ Ω μ exactMachine.qr := by
  intro m n A _
  have hp := Classical.choose_spec (exists_qrFactors (A.map toCplx))
  have hA : A.map toCplx = (qrFactors (A.map toCplx)).1 * (qrFactors (A.map toCplx)).2 :=
    hp.2.2
  refine ⟨?_, (qrFactors (A.map toCplx)).1, hp.1, ?_, ?_⟩
  · change IsUpperTrapezoidal ((((qrFactors (A.map toCplx)).2).map ofCplx).map toCplx)
    rw [map_ofCplx_toCplx]
    exact hp.2.1
  · change specNorm ((qrFactors (A.map toCplx)).1 -
      ((((qrFactors (A.map toCplx)).1).map ofCplx).map toCplx)) ≤ _
    rw [map_ofCplx_toCplx, sub_self, specNorm_zero]
    exact mul_nonneg (hμ _) hu
  · change specNorm (A.map toCplx -
      (qrFactors (A.map toCplx)).1 * ((((qrFactors (A.map toCplx)).2).map ofCplx).map toCplx)) ≤ _
    rw [map_ofCplx_toCplx, ← hA, sub_self, specNorm_zero]
    exact mul_nonneg (mul_nonneg (hμ _) hu) (le_max_of_le_left (by positivity))

/-- The machine contract is satisfiable: for every floor $\tau$, range $\Omega$, nonnegative
constants $\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$ and every $c_{\mathrm N}$, there is a
`NLAlib.FloatMachine` on stored reals, with real seeds and complex samples, meeting
`NLAlib.FloatMachine.IsAccurate` with the identity decoding and $u = 0$: exact arithmetic,
`Nat.floor` for the conversion, $s v$ for the uniform sampler, the parts of $z$ for the normal
sampler, exact products and an exact QR factorization. No printed source. -/
theorem exists_floatMachine_isAccurate (τ Ω : ℝ) {μM μQ : ℕ → ℝ} (hμM : ∀ d, 0 ≤ μM d)
    (hμQ : ∀ d, 0 ≤ μQ d) (cN : ℝ) :
    ∃ M : FloatMachine ℝ ℝ ℂ, M.IsAccurate id 0 τ Ω μM μQ cN := by
  refine ⟨exactMachine, ?_⟩
  refine
    { dec_zero := rfl
      dec_one := rfl
      ofNat := fun k => isRounding_exact rfl rfl
      add := fun x y => isRounding_exact rfl rfl
      sub := fun x y => isRounding_exact rfl rfl
      mul := fun x y => isRounding_exact rfl rfl
      div := fun x y _ => isRounding_exact rfl rfl
      dec_neg := fun x => rfl
      le_iff := fun x y => by
        change (if x ≤ y then true else false) = true ↔ x ≤ y
        split_ifs with h <;> simp [h]
      toNat_eq := fun x => rfl
      isMatMulErr := exactMachine_isMatMulErr 0 τ Ω μM le_rfl hμM
      isQRErr := exactMachine_isQRErr 0 τ Ω μQ le_rfl hμQ
      isUnifSampler := fun s v hs hv => by
        have hs' : 0 ≤ s := hs
        refine ⟨?_, by change |s * v - s * v| ≤ 0 * max s τ; simp⟩
        change |s * v| ≤ s
        rw [abs_mul, abs_of_nonneg hs']
        exact mul_le_of_le_one_right hs' (abs_le.mpr ⟨hv.1, hv.2⟩)
      isNormalSampler := fun z _ => by
        change ‖z - z‖ ≤ _
        simp }

/-- A bounded-format machine meets the contract: for a binary format `fmt` with precision
$p$, smallest exponent $e_{\min}$ and largest finite number $\Omega$, and nonnegative constants,
there is a `NLAlib.FloatMachine` on stored reals whose addition, subtraction, multiplication,
division by a nonzero and conversion round the exact result to `fmt`
(`NLAlib.Computation.binaryFloatRound`, gradual underflow), meeting
`NLAlib.FloatMachine.IsAccurate` with the identity decoding, $u = 2^{-p}$, floor
$\tau = 2^{e_{\min} + p - 1}$, range $\Omega$ and $c_{\mathrm N} = \sqrt2$: the uniform sampler
clamps the rounded $sv$ to $[-s, s]$, the normal sampler rounds both parts, and the black boxes
are exact. The bounded model is therefore an instance of the contract, not a separate one. No
printed source. -/
theorem exists_floatMachine_isAccurate_binaryFloatRound (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, Computation.AbsRelErr 0 (1 / 2) x (r x : ℝ)) {μM μQ : ℕ → ℝ}
    (hμM : ∀ d, 0 ≤ μM d) (hμQ : ∀ d, 0 ≤ μQ d) :
    ∃ M : FloatMachine ℝ ℝ ℂ,
      M.IsAccurate id ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
        ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) fmt.maxFinite μM μQ √2 ∧
      (∀ x y, M.add x y = Computation.binaryFloatRound fmt r (x + y)) ∧
      (∀ x y, M.sub x y = Computation.binaryFloatRound fmt r (x - y)) ∧
      (∀ x y, M.mul x y = Computation.binaryFloatRound fmt r (x * y)) ∧
      (∀ x y, y ≠ 0 → M.div x y = Computation.binaryFloatRound fmt r (x / y)) := by
  have hround := Computation.abs_sub_binaryFloatRound_le fmt hr
  set u : ℝ := (2 : ℝ)⁻¹ ^ fmt.mantissaBits
  set τ : ℝ := (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)
  have hu : 0 ≤ u := by positivity
  have hτ : 0 < τ := by positivity
  set R := Computation.binaryFloatRound fmt r
  obtain ⟨M₀, hM₀⟩ := exists_floatMachine_isAccurate τ fmt.maxFinite hμM hμQ (Real.sqrt 2)
  have hmax : ∀ a, 0 ≤ max a τ := fun a => le_max_of_le_right hτ.le
  refine ⟨{ M₀ with
      ofNat := (fun k => R k), add := (fun x y => R (x + y)), sub := (fun x y => R (x - y))
      mul := (fun x y => R (x * y)), div := (fun x y => R (x / y))
      unif := (fun s v => max (-s) (min s (R (s * v))))
      normal := (fun z => (R z.re, R z.im)) }, ⟨⟨hM₀.dec_zero, hM₀.dec_one,
    fun k _ => hround _, fun x y _ => hround _, fun x y _ => hround _, fun x y _ => hround _,
    fun x y _ _ => hround _, hM₀.dec_neg, hM₀.le_iff, hM₀.toNat_eq, ⟨?_, ?_⟩⟩, ?_, ?_, ?_⟩,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
  · intro l m n A B hAB
    refine (hM₀.isMatMulErr.specNorm_mul_sub_le A B hAB).trans ?_
    rw [mul_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (hμM _) hu) (hmax _)
  · exact hM₀.isMatMulErr.isHermitian_of_map_eq_conjTranspose
  · intro m n A hA
    obtain ⟨h1, Q', hQ', h2, h3⟩ := hM₀.isQRErr A hA
    refine ⟨h1, Q', hQ', h2.trans ?_, h3.trans ?_⟩
    · rw [mul_zero]; exact mul_nonneg (hμQ _) hu
    · rw [mul_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (hμQ _) hu) (hmax _)
  · intro s v hs hv
    simp only [id] at hs ⊢
    have hsv : |s * v| ≤ s := by
      rw [abs_mul, abs_of_nonneg hs]
      exact mul_le_of_le_one_right hs (abs_le.mpr ⟨hv.1, hv.2⟩)
    obtain ⟨hl, hh⟩ := abs_le.mp hsv
    have hw := hround (s * v)
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
    rw [e1, e2, ← sq, ← sq]
    have a1 := sq_le_sq' (abs_le.mp hre).1 (abs_le.mp hre).2
    have a2 := sq_le_sq' (abs_le.mp him).1 (abs_le.mp him).2
    have b1 : (u * max |z.re| τ) ^ 2 ≤ (u * max ‖z‖ τ) ^ 2 := by gcongr
    have b2 : (u * max |z.im| τ) ^ 2 ≤ (u * max ‖z‖ τ) ^ 2 := by gcongr
    nlinarith

/-- From a mixed absolute–relative product bound to the contract with a floor: if a routine
on stored entries with decoding `dec` satisfies $\|\bar{\mathbf{A}}\bar{\mathbf{B}} -
\overline{\mathrm{mm}(\mathbf{A}, \mathbf{B})}\|_2 \le \mu(d)\,u\,\|\bar{\mathbf{A}}\|_2
\|\bar{\mathbf{B}}\|_2 + \eta$ whenever $\|\bar{\mathbf{A}}\|_2\|\bar{\mathbf{B}}\|_2 \le \Omega$,
computes products with a conjugate transpose exactly Hermitian, and $\eta \le \mu(d)\,u\,\tau$ for
every $d$, then it satisfies `NLAlib.IsMatMulErr` with $2\mu$. A bounded-exponent product bound
(underflow as an absolute $\eta$) therefore gives the contract with floor $\tau = \eta/(\mu u)$.
No printed source. -/
theorem IsMatMulErr.of_specNorm_mul_sub_le_add {K 𝕜 : Type*} [RCLike 𝕜] {dec : K → 𝕜}
    {u τ Ω η : ℝ} {μ : ℕ → ℝ} {mm : MatMulMap K}
    (hmix : ∀ {l m n : ℕ} (A : Matrix (Fin l) (Fin m) K) (B : Matrix (Fin m) (Fin n) K),
      specNorm (A.map dec) * specNorm (B.map dec) ≤ Ω →
        specNorm (A.map dec * B.map dec - (mm A B).map dec) ≤
          μ (max l (max m n)) * u * (specNorm (A.map dec) * specNorm (B.map dec)) + η)
    (hherm : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin m) K),
      B.map dec = (A.map dec)ᴴ → ((mm A B).map dec).IsHermitian)
    (hμu : ∀ d, 0 ≤ μ d * u) (hη : ∀ d, η ≤ μ d * u * τ) :
    IsMatMulErr dec u τ Ω (fun d => 2 * μ d) mm := by
  refine ⟨fun {l m n} A B hΩ => ?_, fun {m n} A B hB => hherm A B hB⟩
  have h1 := hmix A B hΩ
  have hx := mul_le_mul_of_nonneg_left
    (le_max_left (specNorm (A.map dec) * specNorm (B.map dec)) τ) (hμu (max l (max m n)))
  have hτ := mul_le_mul_of_nonneg_left
    (le_max_right (specNorm (A.map dec) * specNorm (B.map dec)) τ) (hμu (max l (max m n)))
  have hη' := hη (max l (max m n))
  linarith

end Witnesses

end NLAlib
