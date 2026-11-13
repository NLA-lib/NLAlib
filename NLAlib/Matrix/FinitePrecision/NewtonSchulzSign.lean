/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.EntrywiseRounding
public import NLAlib.Matrix.Functions.Sign
public import NLAlib.Polynomial.Approximation.NewtonSchulz

/-!
# The matrix sign function by the Newton–Schulz iteration on a floating-point machine

`NLAlib.newtonSchulzSign M ε b N A` approximates the sign $\operatorname{sign}(\mathbf{A})$ of a
stored nonsingular Hermitian $\mathbf{A}$ with $\|\mathbf{A}\|_2 \le b$ by the inverse-free
iteration $\mathbf{A}_{k+1} = \tfrac12\mathbf{A}_k(3\mathbf{I} - \mathbf{A}_k^2)$ from
$\mathbf{A}_0 = \mathbf{A}/b$ ([Shah2024, Algorithm 1]), written over a `NLAlib.FloatMachine`:
two black-box products per step and the entrywise operations of
`NLAlib/Matrix/Computation/EntrywiseRounding.lean`. Each step stores the rounded Hermitian part
of the computed product, which [Shah2024] leaves implicit; the threshold $\varepsilon/(4n)$ of
the stopping test is computed by the machine; the iteration stops when every part of every entry
of the computed $\mathrm{mm}(\mathbf{A}_k, \mathbf{A}_k) - \mathbf{I}$ is at most the threshold
in absolute value, or after $N$ steps. The definitions are computable: they use the machine and
`ℕ` only.

## Main definitions

* `NLAlib.newtonSchulzRounded`: one step.
* `NLAlib.newtonSchulzTest`: the stopping test.
* `NLAlib.newtonSchulzLoop`, `NLAlib.newtonSchulzSign`: the iteration and the algorithm.

## Main results

* `NLAlib.FloatMachine.IsArithAccurate.isHermitian_decodeMatrix_newtonSchulzRounded`,
  `NLAlib.FloatMachine.IsArithAccurate.isHermitian_decodeMatrix_newtonSchulzSign`.
* `NLAlib.FloatMachine.IsArithAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le`,
  `NLAlib.FloatMachine.IsArithAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add`:
  one step (Lemma 2.1), with the factor $\sqrt n$ on the whole error or on the rounding only.
* `FloatMachine.IsArithAccurate.forall_isNewtonSchulzChain_and_specNorm_cfc_sign_sub_cfc_sign_le`:
  the eigenvalues of the rounded iterates lie on perturbed scalar chains
  (`NLAlib.IsNewtonSchulzChain`).

The accuracy of the algorithm (Theorem 2.6) and its stopping test are in
`NLAlib/Matrix/Computation/NewtonSchulzSign/Accuracy.lean`.
-/

@[expose] public section

namespace NLAlib

variable {F Su Sg : Type*} {n : ℕ}

/-- **One rounded Newton–Schulz step** on the machine `M`: with $\mathbf{X} =
\mathrm{mm}(\mathbf{A}, \mathbf{A})$ and $\mathbf{B} = -(\mathbf{X} - 3\mathbf{I})$ (rounded
shift, exact negation), the result is the stored Hermitian
$(\mathbf{Y} + \mathbf{Y}^{\mathsf{H}})/4$ for $\mathbf{Y} = \mathrm{mm}(\mathbf{A}, \mathbf{B})$
(`NLAlib.FloatMachine.hermAvg`), which in exact arithmetic is
$g(\mathbf{A}) = \tfrac12\mathbf{A}(3\mathbf{I} - \mathbf{A}^2)$. [Shah2024, (2.4)], there
without the Hermitian part.
Algorithm: newton-schulz-sign -/
def newtonSchulzRounded (M : FloatMachine F Su Sg) (A : Matrix (Fin n) (Fin n) (F × F)) :
    Matrix (Fin n) (Fin n) (F × F) :=
  M.hermAvg (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))) (M.ofNat 4)

/-- **The Newton–Schulz stopping test** at the stored threshold $\eta$: every real and imaginary
part of every entry of $\mathbf{T} = \mathrm{mm}(\mathbf{A}, \mathbf{A}) - \mathbf{I}$ (rounded
shift) lies in $[-\eta, \eta]$, by the machine's comparisons. [Shah2024, Algorithm 1], there
$\|\mathbf{I} - \mathbf{T}\|_{\max} \le \eta$. -/
def newtonSchulzTest (M : FloatMachine F Su Sg) (η : F) (A : Matrix (Fin n) (Fin n) (F × F)) :
    Bool :=
  let T := M.hermShift (M.mm A A) M.one
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    M.le (M.neg η) (T i j).1 && M.le (T i j).1 η && M.le (M.neg η) (T i j).2 && M.le (T i j).2 η

/-- **The Newton–Schulz loop** with at most $N$ steps: return $\mathbf{A}$ if it passes the test
at threshold $\eta$ (`NLAlib.newtonSchulzTest`) or $N = 0$, and otherwise continue from the
rounded step `NLAlib.newtonSchulzRounded`.
Algorithm: newton-schulz-sign -/
def newtonSchulzLoop (M : FloatMachine F Su Sg) (η : F) :
    ℕ → Matrix (Fin n) (Fin n) (F × F) → Matrix (Fin n) (Fin n) (F × F)
  | 0, A => A
  | N + 1, A =>
    if newtonSchulzTest M η A then A else newtonSchulzLoop M η N (newtonSchulzRounded M A)

/-- **The Newton–Schulz sign algorithm** $\mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)$
with at most $N$ steps, for stored $\varepsilon$ and $b$: the loop `NLAlib.newtonSchulzLoop` at
the computed threshold $\mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$ from the stored Hermitian
$\mathbf{A}/b$ (`NLAlib.FloatMachine.hermScale`). In pseudo-code, every scalar operation rounded
by the machine and the products its black box:

```text
sign(A; ε, b, N):                  A Hermitian n×n, ‖A‖₂ ≤ b
  η ← ε/(4n)
  X ← A/b
  repeat at most N times:
    if every real and imaginary part of every entry of X·X − I lies in [−η, η]:
      return X
    Y ← X·(3I − X·X)
    X ← (Y + Yᴴ)/4                               X(3I − X²)/2 in exact arithmetic
  return X
```

[Shah2024, Algorithm 1], there with no step limit.
Algorithm: newton-schulz-sign -/
def newtonSchulzSign (M : FloatMachine F Su Sg) (ε b : F) (N : ℕ)
    (A : Matrix (Fin n) (Fin n) (F × F)) : Matrix (Fin n) (Fin n) (F × F) :=
  newtonSchulzLoop M (M.div ε (M.ofNat (4 * n))) N (M.hermScale A b)

section Accuracy

open scoped Matrix

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω : ℝ} {μ : ℕ → ℝ}
  {n : ℕ}

/-- The rounded Newton–Schulz step decodes to a Hermitian matrix, under
`NLAlib.FloatMachine.IsArithAccurate`. -/
theorem FloatMachine.IsArithAccurate.isHermitian_decodeMatrix_newtonSchulzRounded
    (hM : M.IsArithAccurate dec u τ Ω μ) (A : Matrix (Fin n) (Fin n) (F × F)) :
    (decodeMatrix dec (newtonSchulzRounded M A)).IsHermitian := by
  unfold newtonSchulzRounded FloatMachine.hermAvg
  exact hM.isHermitian_decodeMatrix_hermFrom _ _

/-- The Newton–Schulz sign algorithm returns a matrix with Hermitian decoding, for every input and
step limit, under `NLAlib.FloatMachine.IsArithAccurate`. -/
theorem FloatMachine.IsArithAccurate.isHermitian_decodeMatrix_newtonSchulzSign
    (hM : M.IsArithAccurate dec u τ Ω μ) (ε b : F) (N : ℕ)
    (A : Matrix (Fin n) (Fin n) (F × F)) :
    (decodeMatrix dec (newtonSchulzSign M ε b N A)).IsHermitian := by
  have key : ∀ (η : F) (N : ℕ) (B : Matrix (Fin n) (Fin n) (F × F)),
      (decodeMatrix dec B).IsHermitian →
        (decodeMatrix dec (newtonSchulzLoop M η N B)).IsHermitian := by
    intro η N
    induction N with
    | zero => intro B hB; exact hB
    | succ N ih =>
      intro B hB
      unfold newtonSchulzLoop
      split
      · exact hB
      · exact ih _ (hM.isHermitian_decodeMatrix_newtonSchulzRounded B)
  unfold newtonSchulzSign FloatMachine.hermScale
  exact key _ N _ (hM.isHermitian_decodeMatrix_hermFrom _ _)

/-- The stored conversion of a natural number $k$ with $\tau \le k \le \Omega$ errs by at most
$ku$. -/
private theorem abs_sub_dec_ofNat_le (hM : M.IsArithAccurate dec u τ Ω μ) {k : ℕ}
    (hkΩ : (k : ℝ) ≤ Ω) (hkτ : τ ≤ k) : |(k : ℝ) - dec (M.ofNat k)| ≤ k * u := by
  have h := hM.ofNat k (by rwa [Nat.abs_cast])
  rwa [Nat.abs_cast, max_eq_left hkτ, mul_comm] at h

/-- The stored $3\mathbf{I} - \mathrm{mm}(\mathbf{A}, \mathbf{A})$ of a rounded Newton–Schulz
step is within $1.21\mu u + 7.5u$ of $3\mathbf{I} - \mathbf{A}^2$. -/
private theorem specNorm_sub_decodeMatrix_negMat_hermShift_le
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ : τ ≤ 1 / 2) (hΩ : 9 ≤ Ω)
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    (hA₁ : specNorm (decodeMatrix dec A) ≤ 11 / 10) :
    specNorm (((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      decodeMatrix dec A * decodeMatrix dec A) -
        decodeMatrix dec (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))) ≤
      121 / 100 * μ n * u + 15 / 2 * u := by
  set a := decodeMatrix dec A
  set x := decodeMatrix dec (M.mm A A)
  set t := dec (M.ofNat 3)
  have ht : |3 - t| ≤ 3 * u := by
    have h := abs_sub_dec_ofNat_le (k := 3) hM (by norm_num; linarith) (by norm_num; linarith)
    simpa only [Nat.cast_ofNat] using h
  have hx : x.IsHermitian := hM.isMatMulErr.isHermitian_of_map_eq_conjTranspose A A hA.eq.symm
  have ha0 := specNorm_nonneg a
  have hsq : specNorm a * specNorm a ≤ 121 / 100 := by nlinarith
  have hw : μ n * u ≤ 1 / 10 := by nlinarith
  have e1 : specNorm (a * a - x) ≤ μ n * u * (121 / 100) := by
    have h := hM.isMatMulErr.specNorm_mul_sub_le A A (hsq.trans (by linarith))
    simp only [max_self] at h
    exact h.trans (mul_le_mul_of_nonneg_left (max_le hsq (by linarith)) (mul_nonneg hμ hu₀))
  have h1 := specNorm_one_le (n := Fin n) (𝕜 := ℂ)
  have hK : specNorm (x - t • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ 9 / 2 := by
    have hxa := specNorm_sub_le (a * a) (a * a - x)
    rw [sub_sub_cancel] at hxa
    have hat := specNorm_mul_le a a
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_real_smul]
    have htt : |t| ≤ 3 + 3 * u := abs_le.mpr ⟨by linarith [(abs_le.mp ht).2],
      by linarith [(abs_le.mp ht).1]⟩
    nlinarith [abs_nonneg t, specNorm_nonneg (1 : Matrix (Fin n) (Fin n) ℂ)]
  have e2 := hM.specNorm_sub_decodeMatrix_hermShift_le hu₀ hx (M.ofNat 3) (hK.trans (by linarith))
  rw [hM.decodeMatrix_negMat]
  have heq : ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - a * a) -
      -decodeMatrix dec (M.hermShift (M.mm A A) (M.ofNat 3)) =
      -((a * a - x) + (t - 3) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        ((x - t • 1) - decodeMatrix dec (M.hermShift (M.mm A A) (M.ofNat 3)))) := by
    module
  rw [heq, specNorm_neg]
  have h3 : specNorm ((t - 3) • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ 3 * u := by
    rw [specNorm_real_smul, abs_sub_comm]; nlinarith [abs_nonneg (3 - t)]
  have h4 : u * max (specNorm (x - t • (1 : Matrix (Fin n) (Fin n) ℂ))) τ ≤ u * (9 / 2) :=
    mul_le_mul_of_nonneg_left (max_le hK (by linarith)) hu₀
  linarith [specNorm_add_le (a * a - x) ((t - 3) • (1 : Matrix (Fin n) (Fin n) ℂ)),
    specNorm_add_le (a * a - x + (t - 3) • (1 : Matrix (Fin n) (Fin n) ℂ))
      ((x - t • 1) - decodeMatrix dec (M.hermShift (M.mm A A) (M.ofNat 3)))]

/-- The stored $\mathrm{mm}(\mathbf{A}, 3\mathbf{I} - \mathbf{A}^2)$ of a rounded Newton–Schulz
step is within $6.3\mu u + 8.25u$ of $\mathbf{A}(3\mathbf{I} - \mathbf{A}^2)$. -/
private theorem specNorm_decodeMatrix_mm_negMat_hermShift_sub_le
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ : τ ≤ 1 / 2) (hΩ : 9 ≤ Ω)
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    (hA₁ : specNorm (decodeMatrix dec A) ≤ 11 / 10) :
    specNorm (decodeMatrix dec (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))) -
      decodeMatrix dec A * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        decodeMatrix dec A * decodeMatrix dec A)) ≤ 63 / 10 * μ n * u + 33 / 4 * u := by
  have eB := specNorm_sub_decodeMatrix_negMat_hermShift_le hM hμ hu₀ hu hτ hΩ hA hA₁
  set a := decodeMatrix dec A
  set b := decodeMatrix dec (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))
  set z := (3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - a * a
  have ha0 := specNorm_nonneg a
  have hw : μ n * u ≤ 1 / 10 := by nlinarith
  have hz : specNorm z ≤ 3 + 121 / 100 := by
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_real_smul]
    nlinarith [specNorm_one_le (n := Fin n) (𝕜 := ℂ), specNorm_mul_le a a]
  have hb : specNorm b ≤ 9 / 2 := by
    have h := specNorm_sub_le z (z - b)
    rw [sub_sub_cancel] at h
    nlinarith
  have hab : specNorm a * specNorm b ≤ 99 / 20 :=
    (mul_le_mul hA₁ hb (specNorm_nonneg b) (by norm_num)).trans (by norm_num)
  have e3 := hM.isMatMulErr.specNorm_mul_sub_le A
    (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3))) (hab.trans (by linarith))
  simp only [max_self] at e3
  have e3' : specNorm (a * b - decodeMatrix dec
      (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3))))) ≤ μ n * u * (99 / 20) :=
    e3.trans (mul_le_mul_of_nonneg_left (max_le hab (by linarith)) (mul_nonneg hμ hu₀))
  have heq : decodeMatrix dec (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))) - a * z =
      -(a * b - decodeMatrix dec (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3))))) +
        a * (b - z) := by
    rw [Matrix.mul_sub a b z]; abel
  rw [heq]
  refine (specNorm_add_le _ _).trans ?_
  rw [specNorm_neg]
  have h5 := (specNorm_mul_le a (b - z)).trans
    (mul_le_mul hA₁ ((specNorm_sub_comm b z).trans_le eB) (specNorm_nonneg _) (by norm_num))
  nlinarith

/-- The Hermitian part divided by $t$ is near $\mathbf{G}$ when $\mathbf{Y}$ is near
$2\mathbf{G}$, for Hermitian $\mathbf{G}$ and $t > 0$. -/
private theorem specNorm_sub_smul_add_conjTranspose_le {g y : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᴴ = g) {t e : ℝ} (ht : 0 < t) (hE : specNorm (y - (2 : ℝ) • g) ≤ e) :
    specNorm (g - t⁻¹ • (y + yᴴ)) ≤ |1 - 4 * t⁻¹| * specNorm g + 2 * t⁻¹ * e := by
  set E := y - (2 : ℝ) • g with hE_def
  have hy : y = E + (2 : ℝ) • g := by rw [hE_def, sub_add_cancel]
  have heq : g - t⁻¹ • (y + yᴴ) = (1 - 4 * t⁻¹) • g - t⁻¹ • (E + Eᴴ) := by
    rw [hy, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hg, star_trivial]
    module
  rw [heq]
  refine (specNorm_sub_le _ _).trans ?_
  rw [specNorm_real_smul, specNorm_real_smul, abs_of_pos (inv_pos.mpr ht)]
  have h := (specNorm_add_le E Eᴴ).trans_eq (by rw [specNorm_conjTranspose])
  have h2 : specNorm (E + Eᴴ) ≤ 2 * e := by linarith
  nlinarith [inv_pos.mpr ht]

/-- The two error terms of one rounded Newton–Schulz step: the Hermitian part of the computed
product, at most $(3.23\mu(n) + 6.23)u$, and the rounding of the stored Hermitian average, at most
$3u(2\sqrt n + 1)$. -/
private theorem specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add_mul
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 ≤ Ω) (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    (hA₁ : specNorm (decodeMatrix dec A) ≤ 11 / 10) :
    specNorm ((2⁻¹ : ℝ) • (decodeMatrix dec A * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      decodeMatrix dec A * decodeMatrix dec A)) - decodeMatrix dec (newtonSchulzRounded M A)) ≤
        2 * u + 2 * (10 / 39) * (63 / 10 * μ n * u + 33 / 4 * u) +
          3 * u * (√(n : ℝ) * 2 + 1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hτ' : τ ≤ 1 / 2 := by nlinarith
  have hs : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hw : 8 * u + μ n * u ≤ 1 / 10 := by linarith [mul_add u 8 (μ n)]
  have hw0 := mul_nonneg hμ hu₀
  have hu' : u ≤ 1 / 80 := by linarith
  have eY := specNorm_decodeMatrix_mm_negMat_hermShift_sub_le hM hμ hu₀ hu hτ' hΩ hA hA₁
  set a := decodeMatrix dec A
  set Y := M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))
  set g := (2⁻¹ : ℝ) • (a * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - a * a))
  have hgc : cfc newtonSchulz a = g := hA.cfc_newtonSchulz
  have hgH : gᴴ = g := by
    have h : (cfc newtonSchulz a).IsHermitian := cfc_predicate newtonSchulz a
    rw [hgc] at h; exact h.eq
  have hg1 : specNorm g ≤ 1 := by
    rw [← hgc]
    refine hA.specNorm_cfc_le zero_le_one fun x hx => abs_newtonSchulz_le_one ?_
    rw [hA.spectrum_eq_image_eigenvalue] at hx
    obtain ⟨k, -, rfl⟩ := hx
    linarith [hA.abs_eigenvalue_le_specNorm k]
  have h2g : a * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - a * a) = (2 : ℝ) • g := by
    rw [smul_smul]; norm_num
  rw [h2g] at eY
  set t := dec (M.ofNat 4)
  have ht : |4 - t| ≤ 4 * u := by
    have h := abs_sub_dec_ofNat_le (k := 4) hM (by norm_num; linarith) (by norm_num; linarith)
    simpa only [Nat.cast_ofNat] using h
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  have ht0 : 0 < t := by linarith
  have htinv : t⁻¹ ≤ 10 / 39 :=
    (inv_anti₀ (by norm_num) (by linarith : (39 / 10 : ℝ) ≤ t)).trans_eq (by norm_num)
  have htinv0 : 0 < t⁻¹ := inv_pos.mpr (by linarith)
  have h4 : |1 - 4 * t⁻¹| ≤ 2 * u := by
    rw [show 1 - 4 * t⁻¹ = (t - 4) * t⁻¹ by field_simp, abs_mul, abs_of_pos htinv0,
      abs_sub_comm]
    nlinarith [abs_nonneg (4 - t)]
  set D := specNorm (g - t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ))
  have hD : D ≤ 2 * u + 2 * (10 / 39) * (63 / 10 * μ n * u + 33 / 4 * u) :=
    (specNorm_sub_smul_add_conjTranspose_le hgH (by linarith) eY).trans
      (add_le_add (by nlinarith [specNorm_nonneg g])
        (by gcongr))
  have hy : specNorm (decodeMatrix dec Y) ≤ 263 / 100 := by
    have h := specNorm_add_le ((2 : ℝ) • g) (decodeMatrix dec Y - (2 : ℝ) • g)
    rw [add_sub_cancel, specNorm_real_smul, abs_two] at h
    nlinarith
  have e5 := hM.specNorm_sub_decodeMatrix_hermAvg_le hu₀ (by linarith) hτ₀ Y (c := M.ofNat 4)
    (by rw [abs_of_pos (by linarith)]; linarith) (by linarith)
  have hN1 : specNorm (t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ)) ≤ 2 := by
    have h := specNorm_sub_le g (g - t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ))
    rw [sub_sub_cancel] at h
    nlinarith [mul_nonneg hμ hu₀]
  have hfin : g - decodeMatrix dec (newtonSchulzRounded M A) =
      (g - t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ)) +
        (t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ) -
          decodeMatrix dec (M.hermAvg Y (M.ofNat 4))) := by
    rw [sub_add_sub_cancel]; rfl
  rw [hfin]
  refine (specNorm_add_le _ _).trans ?_
  have k1 := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hN1 (Real.sqrt_nonneg (n : ℝ)))
    (by linarith : 2 * (n : ℝ) * τ ≤ 1)) (by positivity : (0 : ℝ) ≤ 3 * u)
  linarith [e5.trans k1]

/-- **One rounded Newton–Schulz step** (Lemma 2.1): under the arithmetic contract
`NLAlib.FloatMachine.IsArithAccurate` $u$ $\tau$ $\Omega$ with product constant $\mu$,
$\mu(n) \ge 0$, $u \ge 0$, $u(8 + \mu(n)) \le 1/10$, $0 \le \tau$, $2n\tau \le 1$ and
$\Omega \ge 9$, every stored $\mathbf{A}$ whose decoding (still written $\mathbf{A}$) is
Hermitian with $\|\mathbf{A}\|_2 \le 11/10$ satisfies
$$\Bigl\|\tfrac12\mathbf{A}(3\mathbf{I} - \mathbf{A}^2) - \tilde g(\mathbf{A})\Bigr\|_2 \le
4\sqrt n\,(8 + \mu(n))\,u \,,$$
$\tilde g$ the decoded rounded step `NLAlib.newtonSchulzRounded` (constants $3$ and $4$ computed by
the machine's conversion). [Shah2024, Lemma 2.1], there
$\tfrac12(7 + (6 + \mu)a^2)a\,u$ for $\|\mathbf{A}\|_2 \le a$ without the Hermitian part; the
factor $\sqrt n$ is the cost of storing the result exactly Hermitian, and the statement is for
the regime $a \le 11/10$ of the iteration.
Result: newton-schulz-sign-rounded-step -/
theorem FloatMachine.IsArithAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 ≤ Ω)
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    (hA₁ : specNorm (decodeMatrix dec A) ≤ 11 / 10) :
    specNorm ((2⁻¹ : ℝ) • (decodeMatrix dec A * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      decodeMatrix dec A * decodeMatrix dec A)) - decodeMatrix dec (newtonSchulzRounded M A)) ≤
        4 * √(n : ℝ) * (8 + μ n) * u := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim (_ - _) 0, specNorm_zero]; simp
  have h := specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add_mul hM hμ hu₀ hu hτ₀ hτ hΩ hn hA
    hA₁
  have hs : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hμ hu₀), mul_le_mul_of_nonneg_left hs hu₀]

/-- **One rounded Newton–Schulz step, with the dimension factor on the rounding only**: under
the arithmetic contract `NLAlib.FloatMachine.IsArithAccurate` $u$ $\tau$ $\Omega$ with product
constant $\mu$, $\mu(n) \ge 0$, $u \ge 0$, $u(8 + \mu(n)) \le 1/10$, $0 \le \tau$, $2n\tau \le 1$
and $\Omega \ge 9$, every stored $\mathbf{A}$ with Hermitian decoding and $\|\mathbf{A}\|_2 \le
11/10$ satisfies
$$\Bigl\|\tfrac12\mathbf{A}(3\mathbf{I} - \mathbf{A}^2) - \tilde g(\mathbf{A})\Bigr\|_2 \le
\bigl(4\mu(n) + 10 + 10\sqrt n\bigr)u \,.$$
$\tilde g$ the decoded rounded step `NLAlib.newtonSchulzRounded`. The $\sqrt n$ comes only from the
entrywise rounding of the stored Hermitian part, the product errors are normwise; compare
`NLAlib.FloatMachine.IsArithAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le`
($4\sqrt n(8 + \mu(n))u$). [Shah2024, Lemma 2.1]. -/
theorem FloatMachine.IsArithAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 ≤ Ω)
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    (hA₁ : specNorm (decodeMatrix dec A) ≤ 11 / 10) :
    specNorm ((2⁻¹ : ℝ) • (decodeMatrix dec A * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      decodeMatrix dec A * decodeMatrix dec A)) - decodeMatrix dec (newtonSchulzRounded M A)) ≤
        (4 * μ n + 10 + 10 * √(n : ℝ)) * u := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim (_ - _) 0, specNorm_zero]
    exact mul_nonneg (by simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, add_zero]; linarith)
      hu₀
  have h := specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add_mul hM hμ hu₀ hu hτ₀ hτ hΩ hn hA
    hA₁
  nlinarith [mul_nonneg hμ hu₀, mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hu₀]

/-! ### Spectral helpers for the accuracy proof -/

/-- An eigenvalue $x$ of a Hermitian $\mathbf{X}$ has $\lvert x \rvert \le \|\mathbf{X}\|_2$. -/
theorem _root_.Matrix.IsHermitian.abs_le_specNorm_of_mem_spectrum {k : ℕ}
    {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) {x : ℝ} (hx : x ∈ spectrum ℝ X) : |x| ≤ specNorm X := by
  rw [hX.spectrum_eq_image_eigenvalue] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact hX.abs_eigenvalue_le_specNorm j

/-- For Hermitian $\mathbf{X}$, $\mathbf{Y}$, every eigenvalue $y$ of $\mathbf{Y}$ is within
$\|\mathbf{X} - \mathbf{Y}\|_2$ of some eigenvalue of $\mathbf{X}$. -/
theorem _root_.Matrix.IsHermitian.exists_mem_spectrum_abs_sub_le {k : ℕ}
    {X Y : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) {y : ℝ} (hy : y ∈ spectrum ℝ Y) :
    ∃ x ∈ spectrum ℝ X, |x - y| ≤ specNorm (X - Y) := by
  rw [hY.spectrum_eq_image_eigenvalue] at hy
  obtain ⟨j, hj, rfl⟩ := hy
  exact ⟨_, hX.eigenvalue_mem_spectrum hj, hX.abs_eigenvalue_sub_le hY j⟩

/-- For Hermitian $\mathbf{X}$ and real $c$, every eigenvalue of $c\mathbf{X}$ is $c x$ for an
eigenvalue $x$ of $\mathbf{X}$. -/
theorem _root_.Matrix.IsHermitian.exists_mem_spectrum_eq_mul {k : ℕ}
    {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) (c : ℝ) {y : ℝ} (hy : y ∈ spectrum ℝ (c • X)) :
    ∃ x ∈ spectrum ℝ X, y = c * x := by
  rw [← cfc_const_mul_id c X hX.isSelfAdjoint, cfc_map_spectrum _ _ hX.isSelfAdjoint] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, hx, rfl⟩

/-! ### Scalar chains of the perturbed iteration -/

/-- **A perturbed Newton–Schulz chain**: $y$ is reached at step $k$ by a sequence
$x_0, x_1, \dots$ with $s \le \lvert x_0 \rvert \le 11/10$ and
$\lvert x_{j+1} - g(x_j) \rvert \le \delta$ for every $j$, $g(x) = \tfrac12 x(3 - x^2)$ the
Newton–Schulz map (`NLAlib.newtonSchulz`). The eigenvalues of the rounded iterates of
`NLAlib.newtonSchulzSign` lie on such chains. -/
def IsNewtonSchulzChain (s δ y : ℝ) (k : ℕ) : Prop :=
  ∃ x : ℕ → ℝ, x k = y ∧ s ≤ |x 0| ∧ |x 0| ≤ 11 / 10 ∧
    ∀ j, |x (j + 1) - newtonSchulz (x j)| ≤ δ

/-- A start $y$ with $s \le \lvert y \rvert \le 11/10$ is reached at step $0$ by a perturbed
Newton–Schulz chain with errors at most $\delta \ge 0$ (`NLAlib.IsNewtonSchulzChain`). -/
theorem isNewtonSchulzChain_zero {s δ y : ℝ} (hδ : 0 ≤ δ) (h₁ : s ≤ |y|)
    (h₂ : |y| ≤ 11 / 10) : IsNewtonSchulzChain s δ y 0 :=
  ⟨fun j => newtonSchulz^[j] y, rfl, h₁, h₂, fun j => by
    simp only [Function.iterate_succ_apply', sub_self, abs_zero]; exact hδ⟩

/-- A perturbed Newton–Schulz chain (`NLAlib.IsNewtonSchulzChain`) reaching $y$ at step $k$
extends to any $z$ with $\lvert z - g(y) \rvert \le \delta$ at step $k + 1$, for
$\delta \ge 0$. -/
theorem IsNewtonSchulzChain.succ {s δ y z : ℝ} {k : ℕ}
    (h : IsNewtonSchulzChain s δ y k) (hδ : 0 ≤ δ) (hz : |z - newtonSchulz y| ≤ δ) :
    IsNewtonSchulzChain s δ z (k + 1) := by
  obtain ⟨x, hxk, h₁, h₂, hstep⟩ := h
  refine ⟨fun j => if j ≤ k then x j else newtonSchulz^[j - (k + 1)] z, ?_, ?_, ?_, ?_⟩
  · simp
  · simpa using h₁
  · simpa using h₂
  · intro j
    rcases lt_trichotomy j k with hj | rfl | hj
    · simp only [show j + 1 ≤ k by omega, hj.le, if_true]
      exact hstep j
    · simp only [le_refl, if_true, show ¬ j + 1 ≤ j by omega, if_false, Nat.sub_self,
        Function.iterate_zero, id, hxk]
      exact hz
    · simp only [show ¬ j + 1 ≤ k by omega, show ¬ j ≤ k by omega, if_false,
        show j + 1 - (k + 1) = (j - (k + 1)) + 1 by omega, Function.iterate_succ_apply',
        sub_self, abs_zero]
      exact hδ

/-- A point of a perturbed Newton–Schulz chain (`NLAlib.IsNewtonSchulzChain`) from a start of
modulus at least $s \le 1/2$, with errors $\delta$, $20\delta \le s$, has modulus at least $s$. -/
theorem IsNewtonSchulzChain.le_abs {s δ y : ℝ} {k : ℕ}
    (h : IsNewtonSchulzChain s δ y k) (hs : s ≤ 1 / 2) (hδ : 20 * δ ≤ s) : s ≤ |y| := by
  obtain ⟨x, rfl, h₁, h₂, hstep⟩ := h
  have := min_abs_le_abs_of_abs_sub_newtonSchulz_le (by linarith) (by linarith) (by linarith)
    hstep k
  exact le_trans (le_min h₁ hs) this

/-- A point of a perturbed Newton–Schulz chain (`NLAlib.IsNewtonSchulzChain`) with errors
$\delta \le 1/10$ has modulus at most $11/10$. -/
theorem IsNewtonSchulzChain.abs_le {s δ y : ℝ} {k : ℕ}
    (h : IsNewtonSchulzChain s δ y k) (hδ : δ ≤ 1 / 10) : |y| ≤ 11 / 10 := by
  obtain ⟨x, rfl, h₁, h₂, hstep⟩ := h
  rcases k with _ | k
  · exact h₂
  · have := abs_le_one_add_of_abs_sub_newtonSchulz_le (by linarith) (by linarith) hstep k
    linarith

/-- A point $y$ reached at step $k$ by a perturbed Newton–Schulz chain
(`NLAlib.IsNewtonSchulzChain`) from a start of modulus at least $s > 0$, with errors $\delta$,
$20\delta \le s$, $10\delta \le \varepsilon \le 3/80$, $\varepsilon > 0$ and
$N(s, \varepsilon) \le k$ (`NLAlib.newtonSchulzSteps`), has
$\lvert 1 - y^2 \rvert \le \varepsilon$. -/
theorem IsNewtonSchulzChain.abs_one_sub_sq_le {s δ y ε : ℝ} {k : ℕ}
    (h : IsNewtonSchulzChain s δ y k) (hs : 0 < s) (hδ : 20 * δ ≤ s) (hε : 0 < ε)
    (hε₁ : 10 * δ ≤ ε) (hε₂ : ε ≤ 3 / 80) (hk : newtonSchulzSteps s ε ≤ k) :
    |1 - y ^ 2| ≤ ε := by
  obtain ⟨x, rfl, h₁, h₂, hstep⟩ := h
  exact abs_one_sub_sq_le_of_newtonSchulzSteps_le hε hε₁ hε₂ (by linarith) (by linarith)
    (by linarith) hstep ((newtonSchulzSteps_le_of_le_abs hs h₁).trans hk)

/-! ### One step of the matrix iteration -/

/-- A Hermitian $\mathbf{X}$ whose eigenvalues all have modulus at most $c \ge 0$ has
$\|\mathbf{X}\|_2 \le c$. -/
theorem _root_.Matrix.IsHermitian.specNorm_le_of_forall_mem_spectrum_abs_le {k : ℕ}
    {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ spectrum ℝ X, |x| ≤ c) : specNorm X ≤ c := by
  have := hX.specNorm_cfc_le (f := id) hc h
  rwa [cfc_id ℝ X hX.isSelfAdjoint] at this

/-- One rounded Newton–Schulz step keeps the eigenvalues on perturbed chains: under
`NLAlib.FloatMachine.IsArithAccurate` $u$ $\tau$ $\Omega$ with product constant $\mu$,
$\mu(n) \ge 0$, $u \ge 0$, $u(8 + \mu(n)) \le 1/10$, $0 \le \tau$, $2n\tau \le 1$ and
$9 \le \Omega$, let $\delta = 4\sqrt n\,(8 + \mu(n))\,u$ and $0 < s \le 1/2$ with
$20\delta \le s$. If every eigenvalue of the stored $\mathbf{X}$ with Hermitian decoding is
reached at step $k$ by a perturbed Newton–Schulz chain from a start of modulus at least $s$ with
errors $\delta$ (`NLAlib.IsNewtonSchulzChain`), then every eigenvalue of the rounded step
`NLAlib.newtonSchulzRounded` is reached at step $k + 1$, and the step moves the sign by at most
$2\delta/s$ in the spectral norm. -/
theorem
    FloatMachine.IsArithAccurate.forall_isNewtonSchulzChain_and_specNorm_cfc_sign_sub_cfc_sign_le
    (hM : M.IsArithAccurate dec u τ Ω μ) (hμ : 0 ≤ μ n)
    (hu₀ : 0 ≤ u) (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1)
    (hΩ : 9 ≤ Ω) {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1 / 2)
    (hδ : 20 * (4 * √(n : ℝ) * (8 + μ n) * u) ≤ s) {k : ℕ}
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hch : ∀ y ∈ spectrum ℝ (decodeMatrix dec X),
      IsNewtonSchulzChain s (4 * √(n : ℝ) * (8 + μ n) * u) y k) :
    (∀ z ∈ spectrum ℝ (decodeMatrix dec (newtonSchulzRounded M X)),
      IsNewtonSchulzChain s (4 * √(n : ℝ) * (8 + μ n) * u) z (k + 1)) ∧
    specNorm (cfc Real.sign (decodeMatrix dec X) -
      cfc Real.sign (decodeMatrix dec (newtonSchulzRounded M X))) ≤
        2 * (4 * √(n : ℝ) * (8 + μ n) * u) / s := by
  set δ := 4 * √(n : ℝ) * (8 + μ n) * u
  have hδ₀ : 0 ≤ δ := by positivity
  have hY := hM.isHermitian_decodeMatrix_newtonSchulzRounded X
  have hgX : (cfc newtonSchulz (decodeMatrix dec X)).IsHermitian := cfc_predicate _ _
  have hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10 :=
    hX.specNorm_le_of_forall_mem_spectrum_abs_le (by norm_num) fun y hy =>
      (hch y hy).abs_le (by linarith)
  have herr : specNorm (cfc newtonSchulz (decodeMatrix dec X) -
      decodeMatrix dec (newtonSchulzRounded M X)) ≤ δ := by
    rw [hX.cfc_newtonSchulz]
    exact hM.specNorm_sub_decodeMatrix_newtonSchulzRounded_le hμ hu₀ hu hτ₀ hτ hΩ hX hXn
  have hchY : ∀ z ∈ spectrum ℝ (decodeMatrix dec (newtonSchulzRounded M X)),
      IsNewtonSchulzChain s δ z (k + 1) := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hgX.exists_mem_spectrum_abs_sub_le hY hz
    rw [cfc_map_spectrum newtonSchulz (decodeMatrix dec X) hX.isSelfAdjoint
      ((decodeMatrix dec X).finite_real_spectrum.continuousOn _)] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    exact (hch y hy).succ hδ₀ (by rw [abs_sub_comm]; exact hwz.trans herr)
  refine ⟨hchY, ?_⟩
  have h3 : (11 / 10 : ℝ) < √3 := Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [← hX.cfc_sign_cfc_newtonSchulz fun y hy =>
    ⟨hs.trans_le ((hch y hy).le_abs hs₁ hδ), ((hch y hy).abs_le (by linarith)).trans_lt h3⟩,
    specNorm_sub_comm]
  refine (hY.specNorm_cfc_sign_sub_cfc_sign_le hgX hs fun z hz =>
    (hchY z hz).le_abs hs₁ hδ).trans ?_
  rw [specNorm_sub_comm]
  gcongr

end Accuracy

end NLAlib
