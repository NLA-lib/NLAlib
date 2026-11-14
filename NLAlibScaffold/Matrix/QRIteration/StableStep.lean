/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.ShiftedQR
public import NLAlib.Matrix.Perturbation.UnitarySimilarity
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Perturbation.Inverse
public import NLAlibScaffold.Matrix.Perturbation.QRFactorization

/-!
# Backward-stable implicit QR steps

A **backward-stable single-shift QR step** with error $\varepsilon$ from $(\mathbf{H}, s)$ outputs
an upper Hessenberg $\widehat{\mathbf{H}}'$ and an upper triangular $\widehat{\mathbf{R}}$ with one
unitary $\widehat{\mathbf{Q}}$ for which $\|\widehat{\mathbf{H}}' - \widehat{\mathbf{Q}}^{\mathsf H}
\mathbf{H}\widehat{\mathbf{Q}}\|_2 \le \varepsilon$ and $\|\mathbf{H} - s - \widehat{\mathbf{Q}}
\widehat{\mathbf{R}}\|_2 \le \varepsilon$ [BanksGarzaVargasSrivastava2022, Definition 3.4]. A
rounded Givens sweep is one with $\varepsilon = \nu\boldsymbol{u}(\|\mathbf{H}\|_2 + \lvert s
\rvert)$. The paper's base $\|\mathbf{H} - s\|_2$ is not met in floating point (adding back the
shift rounds the diagonal with error $\boldsymbol{u}\lvert s\rvert$, and an implementation that
conjugates $\mathbf{H}$ itself rounds relative to $\|\mathbf{H}\|_2$); every use of the definition
bounds the base by $(1 + C)\|\mathbf{H}\|_2$ for shifts in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$, so
the base $\|\mathbf{H}\|_2 + \lvert s\rvert$ loses nothing.

A degree $m$ step is a chain of $m$ single steps (`NLAlib.IsStableQRChain`). This file states
what the chain gives: the backward error of the composed similarity (Lemma 3.6, first part, in
the corrected form: the norms of the intermediate matrices grow), the backward error of the
factorization of the shift polynomial (Lemma 3.6, second part, under $m\nu\boldsymbol{u} \le
1/4$, which the paper omits), the forward error against the exact multishift step (Lemma 3.8, with
the precision hypothesis corrected and the phase of the last diagonal entry), the last diagonal
entry of the product of the triangular factors (Lemma 3.9, by a direct argument that needs only
$\kappa_V$, not $\kappa_V^2$), and the potential after a rounded step (Lemma 5.2, over the last
$k$ subdiagonals).

## Main definitions

* `NLAlib.IsStableQRStep`: Definition 3.4 with an absolute error.
* `NLAlib.IsStableQRChain`: a degree $m$ step as a chain of single steps.

## Main results

* `NLAlib.isStableQRStep_upperHessenbergPart`: a stable step from a Hessenberg factorization and
  a nearby similarity.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {n : ℕ}

/-- A **backward-stable single-shift QR step** with error $\varepsilon$: `H'` is upper Hessenberg,
`R` upper triangular, and one unitary $\widehat{\mathbf{Q}}$ has
$\|\mathbf{H}' - \widehat{\mathbf{Q}}^{\mathsf H}\mathbf{H}\widehat{\mathbf{Q}}\|_2 \le \varepsilon$
and $\|\mathbf{H} - s\mathbf{I} - \widehat{\mathbf{Q}}\mathbf{R}\|_2 \le \varepsilon$.
[BanksGarzaVargasSrivastava2022, Definition 3.4], with an absolute error. -/
def IsStableQRStep (ε : ℝ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ)
    (H' R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  IsUpperHessenberg H' ∧ R.IsUpperTriangular ∧
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols Q ∧
      specNorm (H' - Qᴴ * H * Q) ≤ ε ∧ specNorm (H - s • (1 : Matrix _ _ ℂ) - Q * R) ≤ ε

/-- A **degree $m$ backward-stable QR step** with the relative error $\nu\boldsymbol{u}$ (`x`):
single steps with the shifts of the list in order, each with error
$x(\|\mathbf{H}_\ell\|_2 + \lvert s_\ell\rvert)$ at its own input $\mathbf{H}_\ell$; the list of
triangular factors is in the order of the steps. -/
inductive IsStableQRChain (x : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →
      List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) → Prop
  /-- No shift: no step. -/
  | nil (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : IsStableQRChain x H [] H []
  /-- One stable step, then the rest of the chain. -/
  | cons {H H₁ H' R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s : ℂ} {ss : List ℂ}
      {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
      (h : IsStableQRStep (x * (specNorm H + ‖s‖)) H s H₁ R)
      (t : IsStableQRChain x H₁ ss H' Rs) : IsStableQRChain x H (s :: ss) H' (R :: Rs)

/-- **A stable step from a Hessenberg factorization and a nearby similarity**: if $\mathbf{Q}$
is unitary and upper Hessenberg, $\mathbf{R}$ upper triangular,
$\|\mathbf{H} - s\mathbf{I} - \mathbf{Q}\mathbf{R}\|_2 \le d$ and
$\|\mathbf{Q}\mathbf{Z}\mathbf{Q}^{\mathsf H} - \mathbf{H}\|_2 \le e$, then $\mathbf{Z}$ with its
entries below the subdiagonal deleted is a backward-stable step with error
$d + \sqrt{n+1}\,(d + e)$ (and at least $d$): $\mathbf{R}\mathbf{Q} + s\mathbf{I}$ is upper
Hessenberg and within $d$ of $\mathbf{Q}^{\mathsf H}\mathbf{H}\mathbf{Q}$, and the deletion costs
at most a Frobenius norm. No printed source; the paper's step is computed Hessenberg. -/
theorem isStableQRStep_upperHessenbergPart {H Z Q R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {s : ℂ} {d e ε : ℝ} (hQ : HasOrthonormalCols Q) (hQH : IsUpperHessenberg Q)
    (hR : R.IsUpperTriangular) (hd : specNorm (H - s • (1 : Matrix _ _ ℂ) - Q * R) ≤ d)
    (he : specNorm (Q * Z * Qᴴ - H) ≤ e) (hdε : d ≤ ε)
    (hε : d + √(n + 1 : ℝ) * (d + e) ≤ ε) :
    IsStableQRStep ε H s (upperHessenbergPart Z) R := by
  set D := H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - Q * R with hD
  set K := R * Q + s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  have hQQ : Qᴴ * Q = 1 := hQ.conjTranspose_mul_self
  have hQQ' : Q * Qᴴ = 1 := hQ.mul_conjTranspose_self
  have hnorm : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, specNorm (Qᴴ * X * Q) = specNorm X := by
    intro X
    rw [Matrix.mul_assoc, hQ.conjTranspose.specNorm_mul_left,
      ← Matrix.conjTranspose_conjTranspose Q, hQ.conjTranspose.specNorm_mul_conjTranspose_right]
  have hK : IsUpperHessenberg K := by
    intro i j hij
    rw [show K i j = (R * Q + s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) i j from rfl,
      Matrix.add_apply, IsUpperHessenberg.isUpperTriangular_mul hR hQH i j hij, Matrix.smul_apply,
      Matrix.one_apply_ne (fun h => by subst h; omega), smul_zero, add_zero]
  have hHQ : Qᴴ * H * Q = K + Qᴴ * D * Q := by
    have hH : H = Q * R + s • (1 : Matrix _ _ ℂ) + D := by rw [hD]; abel
    rw [hH]
    simp only [K, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      ← Matrix.mul_assoc Qᴴ Q, hQQ, Matrix.one_mul]
  clear_value K D
  have hZK : K - Z = -(Qᴴ * D * Q + Qᴴ * (Q * Z * Qᴴ - H) * Q) := by
    have hZ : Qᴴ * (Q * Z * Qᴴ) * Q = Z := by
      simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
      rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, hZ, hHQ]
    abel
  have hKZ : specNorm (K - Z) ≤ d + e := by
    rw [hZK, specNorm_neg]
    refine (specNorm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [hnorm]
    · exact hd
    · exact he
  have hF : specNorm (K - upperHessenbergPart Z) ≤ √(n + 1 : ℝ) * (d + e) := by
    refine (specNorm_le_frobNorm _).trans ((hK.frobNorm_sub_upperHessenbergPart_le).trans ?_)
    refine (frobNorm_le_sqrt_card_mul_specNorm _).trans ?_
    rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_left hKZ (Real.sqrt_nonneg _)
  refine ⟨isUpperHessenberg_upperHessenbergPart Z, hR, Q, hQ, ?_, by rw [← hD]; exact hd.trans hdε⟩
  have e1 : upperHessenbergPart Z - Qᴴ * H * Q = -(K - upperHessenbergPart Z) - Qᴴ * D * Q := by
    rw [hHQ]; abel
  rw [e1]
  refine (specNorm_sub_le _ _).trans ?_
  rw [specNorm_neg, hnorm]
  linarith

/-- A backward-stable single step is a perturbed unitary similarity with the same error. -/
theorem IsStableQRStep.isPerturbedUnitarySimilar {ε : ℝ} {H H' R : Matrix (Fin (n + 1))
    (Fin (n + 1)) ℂ} {s : ℂ} (h : IsStableQRStep ε H s H' R) :
    IsPerturbedUnitarySimilar H H' ε := by
  obtain ⟨-, -, Q, hQ, hH', -⟩ := h
  exact IsPerturbedUnitarySimilar.of_specNorm_sub_le hQ hH'

/-- **Backward error of a degree $m$ step, similarity part** (corrected
[BanksGarzaVargasSrivastava2022, Lemma 3.6]): for shifts in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$, the
output is a perturbed unitary similarity of the input with error
$(1 + C)\|\mathbf{H}\|_2((1 + x)^m - 1)$. The paper's $1.4m(1 + C)\|\mathbf{H}\|_2 x$ follows when
$m x \le 1/4$; without such a bound it is false, because the norms of the intermediate matrices
grow. -/
theorem IsStableQRChain.isPerturbedUnitarySimilar {x C : ℝ} {H H' : Matrix (Fin (n + 1))
    (Fin (n + 1)) ℂ} {ss : List ℂ} {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x H ss H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) :
    IsPerturbedUnitarySimilar H H' ((1 + C) * specNorm H * ((1 + x) ^ ss.length - 1)) := by
  -- The invariant: a chain from `K` with shifts bounded by `C * specNorm H` and budget
  -- `c ≥ specNorm K + C * specNorm H` has backward error `c * ((1 + x) ^ length - 1)`.
  have key : ∀ (c : ℝ) (K K' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ts : List ℂ)
      (Ss : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
      specNorm K + C * specNorm H ≤ c → (∀ s ∈ ts, ‖s‖ ≤ C * specNorm H) →
      IsStableQRChain x K ts K' Ss →
        IsPerturbedUnitarySimilar K K' (c * ((1 + x) ^ ts.length - 1)) := by
    intro c K K' ts Ss hK hs g
    induction g generalizing c with
    | nil K => simpa using IsPerturbedUnitarySimilar.refl K
    | @cons K₀ K₁ K₂ R s ss Rs h t ih =>
      have hsK : ‖s‖ ≤ C * specNorm H := hs s (List.mem_cons_self ..)
      have hs' : ∀ s' ∈ ss, ‖s'‖ ≤ C * specNorm H :=
        fun s' hm => hs s' (List.mem_cons_of_mem _ hm)
      have hxc : x * (specNorm K₀ + ‖s‖) ≤ x * c :=
        mul_le_mul_of_nonneg_left (by linarith) hx
      have h1 := h.isPerturbedUnitarySimilar
      have hH₁ := h1.specNorm_le
      have h2 := ih ((1 + x) * c) (by nlinarith) hs'
      refine (h1.trans h2).mono ?_
      rw [List.length_cons, pow_succ]
      nlinarith [hxc]
  exact key ((1 + C) * specNorm H) H H' ss Rs (le_of_eq (by ring)) hs h

/-- The shift polynomial intertwines: $\mathbf{A}\mathbf{X} = \mathbf{X}\mathbf{B}$ gives
$p(\mathbf{A})\mathbf{X} = \mathbf{X}p(\mathbf{B})$. -/
private theorem aeval_shiftPoly_mul_eq_mul_aeval {A B X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hX : A * X = X * B) (ss : List ℂ) :
    Polynomial.aeval A (shiftPoly ss) * X = X * Polynomial.aeval B (shiftPoly ss) := by
  induction ss with
  | nil => simp [shiftPoly]
  | cons s ss ih =>
    have hs : (A - s • (1 : Matrix _ _ ℂ)) * X = X * (B - s • (1 : Matrix _ _ ℂ)) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, hX, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one]
    have e : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Polynomial.aeval M (shiftPoly (s :: ss)) =
        (M - s • (1 : Matrix _ _ ℂ)) * Polynomial.aeval M (shiftPoly ss) := fun M => by
      rw [shiftPoly, List.map_cons, List.prod_cons, map_mul, ← shiftPoly]
      simp [Algebra.algebraMap_eq_smul_one]
    rw [e, e, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hs, Matrix.mul_assoc]

/-- A shift polynomial is bounded by the product of its factors: $\|p(\mathbf{B})\|_2 \le D^m$
when $\|\mathbf{B} - s\mathbf{I}\|_2 \le D$ for every shift. -/
private theorem specNorm_aeval_shiftPoly_le {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {D : ℝ}
    {ss : List ℂ} (hB : ∀ s ∈ ss, specNorm (B - s • (1 : Matrix _ _ ℂ)) ≤ D) :
    specNorm (Polynomial.aeval B (shiftPoly ss)) ≤ D ^ ss.length := by
  induction ss with
  | nil => simp [shiftPoly]
  | cons s ss ih =>
    have hD : 0 ≤ D := (specNorm_nonneg _).trans (hB s (by simp))
    rw [shiftPoly, List.map_cons, List.prod_cons, map_mul, ← shiftPoly, List.length_cons,
      pow_succ']
    refine (specNorm_mul_le _ _).trans (mul_le_mul ?_ (ih fun r hr => hB r (by simp [hr]))
      (specNorm_nonneg _) hD)
    simpa [Algebra.algebraMap_eq_smul_one] using hB s (by simp)

/-- Telescoping the factors of a shift polynomial:
$D\|p(\mathbf{A}) - p(\mathbf{B})\|_2 \le mD^m\|\mathbf{A} - \mathbf{B}\|_2$. -/
private theorem mul_specNorm_aeval_shiftPoly_sub_le {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {D : ℝ} (hD : 0 ≤ D) {ss : List ℂ}
    (hA : ∀ s ∈ ss, specNorm (A - s • (1 : Matrix _ _ ℂ)) ≤ D)
    (hB : ∀ s ∈ ss, specNorm (B - s • (1 : Matrix _ _ ℂ)) ≤ D) :
    D * specNorm (Polynomial.aeval A (shiftPoly ss) - Polynomial.aeval B (shiftPoly ss)) ≤
      ss.length * D ^ ss.length * specNorm (A - B) := by
  induction ss with
  | nil => simp [shiftPoly]
  | cons s ss ih =>
    have e : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Polynomial.aeval M (shiftPoly (s :: ss)) =
        (M - s • (1 : Matrix _ _ ℂ)) * Polynomial.aeval M (shiftPoly ss) := fun M => by
      rw [shiftPoly, List.map_cons, List.prod_cons, map_mul, ← shiftPoly]
      simp [Algebra.algebraMap_eq_smul_one]
    set pA := Polynomial.aeval A (shiftPoly ss)
    set pB := Polynomial.aeval B (shiftPoly ss)
    have hpB : specNorm pB ≤ D ^ ss.length :=
      specNorm_aeval_shiftPoly_le fun r hr => hB r (by simp [hr])
    have hih := ih (fun r hr => hA r (by simp [hr])) (fun r hr => hB r (by simp [hr]))
    have hsplit : (A - s • (1 : Matrix _ _ ℂ)) * pA - (B - s • (1 : Matrix _ _ ℂ)) * pB =
        (A - s • (1 : Matrix _ _ ℂ)) * (pA - pB) + (A - B) * pB := by noncomm_ring
    rw [e, e, hsplit, List.length_cons]
    push_cast
    calc D * specNorm ((A - s • (1 : Matrix _ _ ℂ)) * (pA - pB) + (A - B) * pB)
        ≤ D * (specNorm (A - s • (1 : Matrix _ _ ℂ)) * specNorm (pA - pB) +
            specNorm (A - B) * specNorm pB) := by
          gcongr
          exact (specNorm_add_le _ _).trans (add_le_add (specNorm_mul_le _ _) (specNorm_mul_le _ _))
      _ ≤ D * (D * specNorm (pA - pB) + specNorm (A - B) * D ^ ss.length) := by
          gcongr
          exact hA s (by simp)
      _ = D * (D * specNorm (pA - pB)) + D ^ (ss.length + 1) * specNorm (A - B) := by ring
      _ ≤ D * (ss.length * D ^ ss.length * specNorm (A - B)) +
            D ^ (ss.length + 1) * specNorm (A - B) := by gcongr
      _ = _ := by ring

/-- $(1 + x)^k(1 - kx) \le 1$ for $x \ge 0$. -/
private theorem one_add_pow_mul_one_sub_le {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k * (1 - k * x) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 ≤ (1 + x) ^ k := pow_nonneg (by linarith) k
    have e : (1 + x) ^ (k + 1) * (1 - ((k + 1 : ℕ) : ℝ) * x) =
        (1 + x) ^ k * (1 - k * x) - (1 + x) ^ k * ((k + 1) * x ^ 2) := by push_cast; ring
    rw [e]
    nlinarith [mul_nonneg hp (by positivity : (0 : ℝ) ≤ (k + 1) * x ^ 2)]

/-- The scalar recursion of the factorization bound: under $(m + 1)x \le 1/4$, the three error
terms of one step stay below $4 \cdot 2^{m+1}c^{m+1}x$. -/
private theorem chain_step_bound_le {x c : ℝ} {m : ℕ} (hx : 0 ≤ x) (hc0 : 0 ≤ c)
    (hm : ((m : ℝ) + 1) * x ≤ 1 / 4) :
    c ^ m * (x * c) + m * ((1 + x) ^ m * c ^ m) * (x * c) +
        4 * 2 ^ m * ((1 + x) ^ m * c ^ m) * x * ((1 + x) * c) ≤
      4 * 2 ^ (m + 1) * c ^ (m + 1) * x := by
  have hpow : (1 + x) ^ (m + 1) ≤ 4 / 3 := by
    have := one_add_pow_mul_one_sub_le hx (m + 1)
    push_cast at this
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + x) (m + 1)]
  have hpow' : (1 + x) ^ m ≤ 4 / 3 :=
    (pow_le_pow_right₀ (by linarith) (Nat.le_succ m)).trans hpow
  have hm2 : (m : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
  have hP : 0 ≤ c ^ m * (x * c) := by positivity
  calc _ = c ^ m * (x * c) * (1 + m * (1 + x) ^ m + 4 * 2 ^ m * (1 + x) ^ (m + 1)) := by ring
    _ ≤ c ^ m * (x * c) * (1 + m * (4 / 3) + 4 * 2 ^ m * (4 / 3)) := by gcongr
    _ ≤ c ^ m * (x * c) * (8 * 2 ^ m) := by gcongr; nlinarith
    _ = _ := by ring

/-- The similarity errors of two unitary steps add up:
$\|\mathbf{G}' - (\mathbf{Q}_0\mathbf{Q}')^{\mathsf H}\mathbf{G}\mathbf{Q}_0\mathbf{Q}'\|_2 \le
\|\mathbf{G}' - \mathbf{Q}'^{\mathsf H}\mathbf{H}_1\mathbf{Q}'\|_2 +
\|\mathbf{H}_1 - \mathbf{Q}_0^{\mathsf H}\mathbf{G}\mathbf{Q}_0\|_2$. -/
private theorem specNorm_sub_conj_mul_le {Q₀ Q' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hQ' : HasOrthonormalCols Q') (G H₁ G' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    specNorm (G' - (Q₀ * Q')ᴴ * G * (Q₀ * Q')) ≤
      specNorm (G' - Q'ᴴ * H₁ * Q') + specNorm (H₁ - Q₀ᴴ * G * Q₀) := by
  rw [show G' - (Q₀ * Q')ᴴ * G * (Q₀ * Q') =
      (G' - Q'ᴴ * H₁ * Q') + Q'ᴴ * (H₁ - Q₀ᴴ * G * Q₀) * Q' by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]; noncomm_ring]
  exact (specNorm_add_le _ _).trans (by rw [hQ'.specNorm_conjTranspose_mul_mul])

/-- Both parts of a degree $m$ step with one unitary, at a free scale
$c \ge \|\mathbf{G}\|_2 + K$, for shifts bounded by $K$: the induction behind
`NLAlib.IsStableQRChain.exists_specNorm_aeval_sub_le`. -/
private theorem IsStableQRChain.exists_specNorm_aeval_sub_le_scale {x K : ℝ}
    {G G' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x G ss G' Rs) (hx : 0 ≤ x) (hK : 0 ≤ K)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ K) (hm : (ss.length : ℝ) * x ≤ 1 / 4) (c : ℝ)
    (hc : specNorm G + K ≤ c) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols Q ∧
      specNorm (Polynomial.aeval G (shiftPoly ss) - Q * Rs.reverse.prod) ≤
        4 * 2 ^ ss.length * c ^ ss.length * x ∧
      specNorm (G' - Qᴴ * G * Q) ≤ c * ((1 + x) ^ ss.length - 1) := by
  induction h generalizing c with
  | nil G =>
    refine ⟨1, hasOrthonormalCols_one, ?_, by simp⟩
    simp only [shiftPoly, List.map_nil, List.prod_nil, map_one, List.reverse_nil, mul_one,
      sub_self, specNorm_zero, List.length_nil, pow_zero]
    positivity
  | @cons G H₁ G' R s ss Rs hstep t ih =>
    obtain ⟨-, -, Q₀, hQ₀, hH₁, hGR⟩ := hstep
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hm ⊢
    set m := ss.length
    set ε := x * (specNorm G + ‖s‖)
    have hsK : ‖s‖ ≤ K := hs s (by simp)
    have hε : ε ≤ x * c := mul_le_mul_of_nonneg_left (by linarith) hx
    have hc0 : 0 ≤ c := by linarith [specNorm_nonneg G]
    have hxc : 0 ≤ x * c := mul_nonneg hx hc0
    have hsub : ∀ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r : ℂ), ‖r‖ ≤ K →
        specNorm (M - r • (1 : Matrix _ _ ℂ)) ≤ specNorm M + K := fun M r hr =>
      (specNorm_sub_le _ _).trans (by rw [specNorm_smul, specNorm_one, mul_one]; linarith)
    set A := Q₀ᴴ * G * Q₀
    have hA : specNorm A = specNorm G := hQ₀.specNorm_conjTranspose_mul_mul G
    have hH₁n : specNorm H₁ ≤ specNorm G + ε := by
      have := specNorm_add_le (H₁ - A) A
      rw [sub_add_cancel] at this
      linarith
    obtain ⟨Q', hQ', hIH, hsim⟩ := ih (fun r hr => hs r (by simp [hr])) (by nlinarith)
      ((1 + x) * c) (by nlinarith)
    refine ⟨Q₀ * Q', hQ₀.mul hQ', ?_, ?_⟩
    swap
    · have e : (1 + x) * c * ((1 + x) ^ m - 1) + x * c = c * ((1 + x) ^ (m + 1) - 1) := by ring
      linarith [specNorm_sub_conj_mul_le hQ' G H₁ G' (Q₀ := Q₀), hH₁.trans hε]
    have hGQ : G * Q₀ = Q₀ * A := by
      simp only [A, ← Matrix.mul_assoc, hQ₀.mul_conjTranspose_self, Matrix.one_mul]
    set F := G - s • (1 : Matrix _ _ ℂ) - Q₀ * R
    have hdecomp : Polynomial.aeval G (shiftPoly (s :: ss)) - Q₀ * Q' * (R :: Rs).reverse.prod =
        Polynomial.aeval G (shiftPoly ss) * F +
          Q₀ * ((Polynomial.aeval A (shiftPoly ss) - Polynomial.aeval H₁ (shiftPoly ss)) * R) +
          Q₀ * ((Polynomial.aeval H₁ (shiftPoly ss) - Q' * Rs.reverse.prod) * R) := by
      have hp : Polynomial.aeval G (shiftPoly (s :: ss)) =
          Polynomial.aeval G (shiftPoly ss) * (F + Q₀ * R) := by
        rw [show F + Q₀ * R = G - s • (1 : Matrix _ _ ℂ) by simp [F], shiftPoly,
          List.map_cons, List.prod_cons, mul_comm, map_mul, ← shiftPoly]
        simp [Algebra.algebraMap_eq_smul_one]
      rw [hp, List.reverse_cons, List.prod_append, List.prod_singleton, Matrix.mul_add,
        ← Matrix.mul_assoc _ Q₀ R, aeval_shiftPoly_mul_eq_mul_aeval hGQ ss]
      noncomm_ring
    set pA := Polynomial.aeval A (shiftPoly ss)
    set pB := Polynomial.aeval H₁ (shiftPoly ss)
    set D := (1 + x) * c
    have hcD : c ≤ D := by nlinarith
    have hR : specNorm R ≤ D := by
      rw [← hQ₀.specNorm_mul_left R, show Q₀ * R = G - s • (1 : Matrix _ _ ℂ) - F by simp [F]]
      linarith [specNorm_sub_le (G - s • (1 : Matrix _ _ ℂ)) F, hsub G s hsK]
    have hpG : specNorm (Polynomial.aeval G (shiftPoly ss)) ≤ c ^ m :=
      specNorm_aeval_shiftPoly_le fun r hr => (hsub G r (hs r (by simp [hr]))).trans hc
    have hdiff := mul_specNorm_aeval_shiftPoly_sub_le (D := D) (by positivity) (A := A) (B := H₁)
      (ss := ss) (fun r hr => (hsub A r (hs r (by simp [hr]))).trans (by linarith))
      (fun r hr => (hsub H₁ r (hs r (by simp [hr]))).trans (by linarith))
    rw [specNorm_sub_comm A H₁] at hdiff
    have hQM : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        specNorm (Q₀ * (M * R)) ≤ specNorm M * D := fun M => by
      rw [hQ₀.specNorm_mul_left]
      exact (specNorm_mul_le _ _).trans (by gcongr)
    have hDm : D ^ m = (1 + x) ^ m * c ^ m := mul_pow _ _ _
    rw [hdecomp]
    calc _ ≤ specNorm (Polynomial.aeval G (shiftPoly ss) * F) + specNorm (pA - pB) * D +
          specNorm (pB - Q' * Rs.reverse.prod) * D := by
          refine (specNorm_add_le _ _).trans (add_le_add ((specNorm_add_le _ _).trans
            (add_le_add le_rfl (hQM _))) (hQM _))
      _ ≤ c ^ m * (x * c) + m * ((1 + x) ^ m * c ^ m) * (x * c) +
          4 * 2 ^ m * ((1 + x) ^ m * c ^ m) * x * ((1 + x) * c) := by
          gcongr ?_ + ?_ + ?_
          · exact (specNorm_mul_le _ _).trans (mul_le_mul hpG (hGR.trans hε) (specNorm_nonneg _)
              (by positivity))
          · rw [mul_comm, ← hDm]
            exact hdiff.trans (by gcongr; exact hH₁.trans hε)
          · rw [← hDm]
            exact mul_le_mul_of_nonneg_right hIH (by positivity)
      _ ≤ _ := chain_step_bound_le hx hc0 hm

/-- **Backward error of a degree $m$ step, factorization part** (corrected
[BanksGarzaVargasSrivastava2022, Lemma 3.6]): for shifts in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$ and
$m x \le 1/4$, one unitary $\widehat{\mathbf{Q}}$ has $\|p(\mathbf{H}) - \widehat{\mathbf{Q}}
\widehat{\mathbf{R}}_m \cdots \widehat{\mathbf{R}}_1\|_2 \le 4(2(1 + C)\|\mathbf{H}\|_2)^m x$, with
$p(z) = \prod_\ell (z - s_\ell)$. The paper assumes only $x \le 1/4$, under which the statement is
false (its induction confuses per-step and cumulative errors); $m x \le 1/4$ suffices. -/
theorem IsStableQRChain.exists_specNorm_aeval_sub_le {x C : ℝ} {H H' : Matrix (Fin (n + 1))
    (Fin (n + 1)) ℂ} {ss : List ℂ} {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x H ss H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hm : (ss.length : ℝ) * x ≤ 1 / 4) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols Q ∧
      specNorm (Polynomial.aeval H (shiftPoly ss) - Q * Rs.reverse.prod) ≤
        4 * (2 * (1 + C) * specNorm H) ^ ss.length * x := by
  obtain ⟨Q, hQ, hle, -⟩ := h.exists_specNorm_aeval_sub_le_scale hx
    (mul_nonneg hC (specNorm_nonneg H)) hs hm ((1 + C) * specNorm H) (by linarith)
  exact ⟨Q, hQ, hle.trans_eq (by
    rw [show 2 * (1 + C) * specNorm H = 2 * ((1 + C) * specNorm H) by ring,
      mul_pow (2 : ℝ)]; ring)⟩

/-- The triangular factors of a chain are upper triangular. -/
private theorem IsStableQRChain.forall_isUpperTriangular {x : ℝ}
    {H H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)} (h : IsStableQRChain x H ss H' Rs) :
    ∀ R ∈ Rs, R.IsUpperTriangular := by
  induction h with
  | nil => simp
  | cons hstep _ ih =>
    intro R hR
    rcases List.mem_cons.mp hR with rfl | hR
    exacts [hstep.2.1, ih R hR]

/-- A product of upper triangular matrices is upper triangular, with the products of the
diagonal entries on its diagonal. -/
private theorem list_prod_isUpperTriangular_apply_self
    {L : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)} (hL : ∀ R ∈ L, R.IsUpperTriangular)
    (i : Fin (n + 1)) :
    L.prod.IsUpperTriangular ∧ L.prod i i = (L.map fun R => R i i).prod := by
  induction L with
  | nil => exact ⟨Matrix.blockTriangular_one, by simp⟩
  | cons R L ih =>
    obtain ⟨hU, hd⟩ := ih fun R' hR' => hL R' (by simp [hR'])
    have hR := hL R (by simp)
    refine ⟨by simpa using hR.mul hU, ?_⟩
    rw [List.prod_cons, hR.mul_apply_self hU, hd, List.map_cons, List.prod_cons]

/-- A row has Euclidean norm at most the spectral norm. -/
private theorem norm_toLp_row_le_specNorm' (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) : ‖WithLp.toLp 2 (A i)‖ ≤ specNorm A := by
  have := norm_toLp_col_le_specNorm Aᵀ i
  rwa [specNorm_transpose] at this

/-- A row of a square matrix with orthonormal columns, conjugate transposed, has norm one. -/
private theorem norm_toLp_conjTranspose_row_eq_one {Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hQ : HasOrthonormalCols Q) (i : Fin (n + 1)) : ‖WithLp.toLp 2 (Qᴴ i)‖ = 1 := by
  have h := congrFun (congrFun hQ.conjTranspose_mul_self i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h' : ∑ j, ((‖Q j i‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_one] at h'
  rw [EuclideanSpace.norm_eq]
  simp only [Matrix.conjTranspose_apply, norm_star]
  rw [h', Real.sqrt_one]

/-- An eigenvalue is at most the spectral norm. -/
private theorem norm_le_specNorm_of_mul_eq_mul_diagonal'
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (i : Fin (n + 1)) : ‖e i‖ ≤ specNorm H := by
  set v := V *ᵥ Pi.single i 1
  have hv : H *ᵥ v = e i • v := by
    rw [Matrix.mulVec_mulVec, hHV, ← Matrix.mulVec_mulVec, Matrix.mulVec_single,
      Matrix.mulVec_smul]
    simp [v]
  have hv0 : WithLp.toLp 2 v ≠ 0 := fun h0 => by
    have := congrFun (Matrix.mulVec_injective_iff_isUnit.mpr hV
      (show v = V *ᵥ 0 by rw [Matrix.mulVec_zero]; exact congrArg WithLp.ofLp h0)) i
    simp at this
  have h := norm_toLp_mulVec_le H v
  rw [hv, WithLp.toLp_smul, norm_smul] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hv0)

/-- A shift polynomial at distance at least $d$ from every shift is at least $d^m$. -/
private theorem pow_le_norm_eval_shiftPoly {d : ℝ} (hd : 0 ≤ d) {z : ℂ} {ss : List ℂ}
    (h : ∀ s ∈ ss, d ≤ ‖z - s‖) : d ^ ss.length ≤ ‖(shiftPoly ss).eval z‖ := by
  induction ss with
  | nil => simp [shiftPoly]
  | cons s ss ih =>
    rw [shiftPoly, List.map_cons, List.prod_cons, ← shiftPoly, Polynomial.eval_mul,
      norm_mul, List.length_cons, pow_succ']
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_le_mul (h s (by simp)) (ih fun r hr => h r (by simp [hr])) (by positivity)
      (norm_nonneg _)

/-- A shift polynomial of a diagonalised matrix acts on the eigenvectors diagonally:
$p(\mathbf{H})\mathbf{V} = \mathbf{V}\operatorname{diag}(p(\mathbf{e}))$. -/
private theorem aeval_shiftPoly_mul_eq_mul_diagonal {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} (hHV : H * V = V * Matrix.diagonal e) (ss : List ℂ) :
    Polynomial.aeval H (shiftPoly ss) * V =
      V * Matrix.diagonal fun i => (shiftPoly ss).eval (e i) := by
  induction ss with
  | nil => simp [shiftPoly]
  | cons s ss ih =>
    have hs : (H - s • (1 : Matrix _ _ ℂ)) * V = V * Matrix.diagonal fun i => e i - s := by
      rw [Matrix.sub_mul, hHV, Matrix.smul_mul, Matrix.one_mul, show
        (Matrix.diagonal fun i => e i - s) = Matrix.diagonal e - s • (1 : Matrix _ _ ℂ) by
          ext i j; by_cases hij : i = j <;> simp [hij],
        Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
    have e' : Polynomial.aeval H (shiftPoly (s :: ss)) =
        (H - s • (1 : Matrix _ _ ℂ)) * Polynomial.aeval H (shiftPoly ss) := by
      rw [shiftPoly, List.map_cons, List.prod_cons, map_mul, ← shiftPoly]
      simp [Algebra.algebraMap_eq_smul_one]
    rw [e', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hs, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    congr 2
    ext i
    simp [shiftPoly]

/-- The inverse of the shift polynomial of a diagonalisable matrix, with every shift at distance
at least $d > 0$ from every eigenvalue, has norm at most $\kappa(\mathbf{V})/d^m$. -/
private theorem specNorm_inv_aeval_shiftPoly_le {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} {d : ℝ} (hd : 0 < d) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖) :
    Polynomial.aeval H (shiftPoly ss) * (Polynomial.aeval H (shiftPoly ss))⁻¹ = 1 ∧
      specNorm (Polynomial.aeval H (shiftPoly ss))⁻¹ ≤
        pseudoConditionNumber V / d ^ ss.length := by
  have hle : ∀ i, d ^ ss.length ≤ ‖(shiftPoly ss).eval (e i)‖ := fun i =>
    pow_le_norm_eval_shiftPoly hd.le fun s hs => hdist s hs i
  have hne : ∀ i, (shiftPoly ss).eval (e i) ≠ 0 := fun i h0 => by
    have := hle i
    rw [h0, norm_zero] at this
    exact absurd this (not_le.mpr (by positivity))
  have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hMW : Polynomial.aeval H (shiftPoly ss) *
      (V * (Matrix.diagonal fun i => ((shiftPoly ss).eval (e i))⁻¹) * V⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, aeval_shiftPoly_mul_eq_mul_diagonal hHV,
      Matrix.mul_assoc V, Matrix.diagonal_mul_diagonal,
      show (fun i => (shiftPoly ss).eval (e i) * ((shiftPoly ss).eval (e i))⁻¹) = 1 from
        funext fun i => mul_inv_cancel₀ (hne i),
      Pi.one_def, Matrix.diagonal_one, Matrix.mul_one, Matrix.mul_nonsing_inv V hdet]
  have hdetM : IsUnit (Polynomial.aeval H (shiftPoly ss)).det :=
    IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hMW, Matrix.det_one])
  refine ⟨Matrix.mul_nonsing_inv _ hdetM, ?_⟩
  rw [Matrix.inv_eq_right_inv hMW, pseudoConditionNumber, pinv_of_isUnit hV]
  have hdiag : specNorm (Matrix.diagonal fun i => ((shiftPoly ss).eval (e i))⁻¹) ≤
      1 / d ^ ss.length := specNorm_diagonal_le (by positivity) fun i => by
    rw [norm_inv, one_div]
    exact inv_anti₀ (by positivity) (hle i)
  calc _ ≤ specNorm (V * Matrix.diagonal fun i => ((shiftPoly ss).eval (e i))⁻¹) *
        specNorm V⁻¹ := specNorm_mul_le _ _
    _ ≤ specNorm V * (1 / d ^ ss.length) * specNorm V⁻¹ := by
        gcongr
        exact (specNorm_mul_le _ _).trans (by gcongr)
    _ = _ := by ring

/-- The last diagonal entry of a perturbed QR factorization: if $\mathbf{M}$ is invertible and
$\mathbf{M} = \mathbf{Q}\widehat{\mathbf{R}} + \mathbf{E}$ with $\mathbf{Q}$ unitary,
$\widehat{\mathbf{R}}$ upper triangular and $\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_2 \le 4/8004$,
then $\lvert\widehat{\mathbf{R}}_{nn}\rvert$ is within $0.0006$, relatively, of
$\|\mathbf{e}_n^{\mathsf T}\mathbf{M}^{-1}\|^{-1}$. -/
private theorem abs_norm_last_sub_inv_le_of_mul {M Q Rh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hQ : HasOrthonormalCols Q) (hU : Rh.IsUpperTriangular) (hMM : M * M⁻¹ = 1)
    (hη : specNorm M⁻¹ * specNorm (M - Q * Rh) ≤ 4 / 8004) :
    |‖Rh (Fin.last n) (Fin.last n)‖ - ‖WithLp.toLp 2 (M⁻¹ (Fin.last n))‖⁻¹| ≤
      0.0006 * ‖WithLp.toLp 2 (M⁻¹ (Fin.last n))‖⁻¹ := by
  set E := M - Q * Rh
  set r := Rh (Fin.last n) (Fin.last n)
  -- the last row of `Qᴴ = R̂M⁻¹ + QᴴEM⁻¹`
  have hkey : Qᴴ = Rh * M⁻¹ + Qᴴ * E * M⁻¹ := by
    calc Qᴴ = Qᴴ * (M * M⁻¹) := by rw [hMM, Matrix.mul_one]
      _ = Qᴴ * Q * Rh * M⁻¹ + Qᴴ * E * M⁻¹ := by simp only [E]; noncomm_ring
      _ = _ := by rw [hQ.conjTranspose_mul_self, Matrix.one_mul]
  have hrowR : (Rh * M⁻¹) (Fin.last n) = r • M⁻¹ (Fin.last n) := by
    funext j
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
    · rfl
    · intro k _ hk
      rw [show Rh (Fin.last n) k = 0 from hU (Fin.lt_last_iff_ne_last.mpr hk), zero_mul]
    · simp
  have hrow : WithLp.toLp 2 (Qᴴ (Fin.last n)) = r • WithLp.toLp 2 (M⁻¹ (Fin.last n)) +
      WithLp.toLp 2 ((Qᴴ * E * M⁻¹) (Fin.last n)) := by
    rw [← WithLp.toLp_smul, ← hrowR, ← WithLp.toLp_add]
    exact congrArg (WithLp.toLp 2) (congrFun hkey (Fin.last n))
  have hw : ‖WithLp.toLp 2 ((Qᴴ * E * M⁻¹) (Fin.last n))‖ ≤ specNorm M⁻¹ * specNorm E := by
    refine (norm_toLp_row_le_specNorm' _ _).trans ?_
    refine (specNorm_mul_le _ _).trans ?_
    rw [mul_comm]
    gcongr
    refine (specNorm_mul_le _ _).trans ?_
    rw [specNorm_conjTranspose]
    nlinarith [hQ.specNorm_le_one, specNorm_nonneg E, specNorm_nonneg Q]
  have h1 := norm_toLp_conjTranspose_row_eq_one hQ (Fin.last n)
  set N := ‖WithLp.toLp 2 (M⁻¹ (Fin.last n))‖
  have hup : ‖r‖ * N ≤ 1 + specNorm M⁻¹ * specNorm E := by
    have := norm_sub_le (WithLp.toLp 2 (Qᴴ (Fin.last n)))
      (WithLp.toLp 2 ((Qᴴ * E * M⁻¹) (Fin.last n)))
    rw [hrow, add_sub_cancel_right, norm_smul, ← hrow, h1] at this
    linarith
  have hlo : 1 - specNorm M⁻¹ * specNorm E ≤ ‖r‖ * N := by
    have := norm_add_le (r • WithLp.toLp 2 (M⁻¹ (Fin.last n)))
      (WithLp.toLp 2 ((Qᴴ * E * M⁻¹) (Fin.last n)))
    rw [← hrow, h1, norm_smul] at this
    linarith
  have hN : 0 < N := by
    by_contra hc
    rw [le_antisymm (not_lt.mp hc) (norm_nonneg _), mul_zero] at hlo
    linarith
  rw [show ‖r‖ - N⁻¹ = (‖r‖ * N - 1) * N⁻¹ by field_simp, abs_mul,
    abs_of_pos (inv_pos.mpr hN)]
  exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩)
    (inv_nonneg.mpr hN.le)

/-- **The last diagonal entries of the triangular factors** (corrected
[BanksGarzaVargasSrivastava2022, Lemma 3.9]): let $\mathbf{H}\mathbf{V} = \mathbf{V}\mathbf{D}$
with $\kappa(\mathbf{V}) \le \kappa$, $\mathbf{H} \ne 0$, every shift in
$\mathbb{D}(0, C\|\mathbf{H}\|_2)$ and at distance at least $d > 0$ from every eigenvalue, and
$x \le (8004\kappa)^{-1}(d / ((2 + 2C)\|\mathbf{H}\|_2))^m$, the product of the moduli of the last
diagonal entries is within $0.0006$, relatively, of
$\|\mathbf{e}_n^{\mathsf T}p(\mathbf{H})^{-1}\|_2^{-1} = \tau_p(\mathbf{H})^m$. The paper's route
through the perturbation of the whole factor needs $\kappa^2$ and $24000$; the direct route uses
$\mathbf{R}_{nn} = \|\mathbf{e}_n^{\mathsf T}\mathbf{M}^{-1}\|_2^{-1}$
(`NLAlib.IsQR.last_le_of_add`). The computed product of $m$ moduli adds a relative error
$O(m\boldsymbol{u})$, a separate scalar estimate. -/
theorem IsStableQRChain.abs_prod_last_sub_le {x C κ d : ℝ} {H H' V : Matrix (Fin (n + 1))
    (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x H ss H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C) (hd : 0 < d) (hH0 : H ≠ 0)
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ κ)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖)
    (hu : x ≤ (8004 * κ)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ ss.length) :
    |(Rs.map fun R => ‖R (Fin.last n) (Fin.last n)‖).prod -
        ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss))⁻¹ (Fin.last n))‖⁻¹| ≤
      0.0006 * ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss))⁻¹ (Fin.last n))‖⁻¹ := by
  set m := ss.length
  set M := Polynomial.aeval H (shiftPoly ss)
  have hκ1 : 1 ≤ κ := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hH : 0 < specNorm H :=
    (specNorm_nonneg H).lt_of_ne fun h0 => hH0 (specNorm_eq_zero_iff.mp h0.symm)
  have hL : 0 < (2 + 2 * C) * specNorm H := by positivity
  set ρ := d / ((2 + 2 * C) * specNorm H)
  have hρ : ρ ^ m ≤ (1 / 2) ^ m := by
    rcases eq_or_ne ss [] with hss | hss
    · simp [m, hss]
    · obtain ⟨s, hs'⟩ := List.exists_mem_of_ne_nil ss hss
      have h1 := hdist s hs' 0
      have h2 := norm_le_specNorm_of_mul_eq_mul_diagonal' hV hHV 0
      have h3 := norm_sub_le (e 0) s
      have h4 := hs s hs'
      refine pow_le_pow_left₀ (by positivity) ?_ m
      rw [div_le_iff₀ hL]
      nlinarith
  have hx' : x ≤ 8004⁻¹ * (1 / 2) ^ m := by
    refine hu.trans ?_
    rw [mul_inv]
    calc 8004⁻¹ * κ⁻¹ * ρ ^ m ≤ 8004⁻¹ * 1 * (1 / 2) ^ m := by
          gcongr
          exact inv_le_one_of_one_le₀ hκ1
      _ = _ := by ring
  have h2m : (m : ℝ) * (1 / 2) ^ m ≤ 1 := by
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact_mod_cast Nat.lt_two_pow_self.le
  have hmx : (m : ℝ) * x ≤ 1 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hx' (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  obtain ⟨Q, hQ, hE⟩ := h.exists_specNorm_aeval_sub_le hx hC hs hmx
  set Rh := Rs.reverse.prod
  set E := M - Q * Rh
  obtain ⟨hMM, hMi⟩ := specNorm_inv_aeval_shiftPoly_le hd hV hHV hdist
  have hη : specNorm M⁻¹ * specNorm E ≤ 4 / 8004 := by
    have hEb : specNorm E ≤ 4 * d ^ m / (8004 * κ) := by
      calc specNorm E ≤ 4 * ((2 + 2 * C) * specNorm H) ^ m * x := by
            rw [show (2 + 2 * C) * specNorm H = 2 * (1 + C) * specNorm H by ring]; exact hE
        _ ≤ 4 * ((2 + 2 * C) * specNorm H) ^ m * ((8004 * κ)⁻¹ * ρ ^ m) := by gcongr
        _ = 4 * d ^ m / (8004 * κ) := by
            rw [div_pow]
            field_simp
    calc _ ≤ κ / d ^ m * (4 * d ^ m / (8004 * κ)) :=
          mul_le_mul (hMi.trans (by gcongr)) hEb (specNorm_nonneg _) (by positivity)
      _ = 4 / 8004 := by field_simp
  obtain ⟨hU, hdiag⟩ := list_prod_isUpperTriangular_apply_self (L := Rs.reverse)
    (fun R hR => h.forall_isUpperTriangular R (List.mem_reverse.mp hR)) (Fin.last n)
  set r := Rh (Fin.last n) (Fin.last n)
  have hprod : (Rs.map fun R => ‖R (Fin.last n) (Fin.last n)‖).prod = ‖r‖ := by
    rw [show r = _ from hdiag, List.norm_prod, List.map_map, List.map_reverse, List.prod_reverse]
    rfl
  rw [hprod]
  exact abs_norm_last_sub_inv_le_of_mul hQ hU hMM hη

/-- A unimodular phase: $\lvert p\rvert = 1$ gives $\bar p p = 1$. -/
private theorem star_mul_self_of_norm_eq_one {p : ℂ} (hp : ‖p‖ = 1) : star p * p = 1 := by
  rw [Complex.star_def, Complex.conj_mul', hp]
  norm_num

/-- A diagonal of unimodular entries is unitary. -/
private theorem hasOrthonormalCols_diagonal_of_norm_eq_one {p : Fin (n + 1) → ℂ}
    (hp : ∀ i, ‖p i‖ = 1) : HasOrthonormalCols (Matrix.diagonal p) := by
  rw [HasOrthonormalCols, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  exact congrArg _ (funext fun i => star_mul_self_of_norm_eq_one (hp i))

/-- The phases of the diagonal of a QR factorization of an invertible matrix: $p_i =
\mathbf{R}_{ii}/\lvert\mathbf{R}_{ii}\rvert$ has modulus one and $\bar p_i\mathbf{R}_{ii} > 0$. -/
private theorem IsQR.exists_phase_pos {A Q R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h : IsQR A Q R) (hA : IsUnit A) :
    ∃ p : Fin (n + 1) → ℂ, (∀ i, ‖p i‖ = 1) ∧
      ∀ i, 0 < (Matrix.diagonal (star p) * R) i i := by
  have hQ := h.hasOrthonormalCols
  have hQu : IsUnit Qᴴ :=
    ⟨⟨Qᴴ, Q, hQ.conjTranspose_mul_self, hQ.mul_conjTranspose_self⟩, rfl⟩
  have hR : ∀ i, R i i ≠ 0 := h.isUnit_iff.mp (by
    have := hQu.mul hA
    rwa [h.conjTranspose_mul_eq] at this)
  have hn : ∀ i, (‖R i i‖ : ℂ) ≠ 0 := fun i => by exact_mod_cast norm_ne_zero_iff.mpr (hR i)
  refine ⟨fun i => R i i / (‖R i i‖ : ℂ), fun i => ?_, fun i => ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr
      (hR i))]
  · rw [Matrix.diagonal_mul, Pi.star_apply, star_div₀, Complex.star_def, Complex.conj_ofReal,
      div_mul_eq_mul_div, ← Complex.star_def, Complex.star_def, Complex.conj_mul',
      show ((‖R i i‖ : ℂ) ^ 2) / (‖R i i‖ : ℂ) = (‖R i i‖ : ℂ) by field_simp]
    exact Complex.zero_lt_real.mpr (norm_pos_iff.mpr (hR i))

/-- Two unitary conjugations of $\mathbf{H}$ differ by at most
$2\|\mathbf{H}\|_2\|\mathbf{Q}_2 - \mathbf{Q}_1\|_{\mathsf F}$ in the Frobenius norm. -/
private theorem frobNorm_conj_sub_conj_le {Q₁ Q₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h₁ : HasOrthonormalCols Q₁) (h₂ : HasOrthonormalCols Q₂)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    frobNorm (Q₂ᴴ * H * Q₂ - Q₁ᴴ * H * Q₁) ≤ 2 * specNorm H * frobNorm (Q₂ - Q₁) := by
  have e : Q₂ᴴ * H * Q₂ - Q₁ᴴ * H * Q₁ = (Q₂ - Q₁)ᴴ * (H * Q₂) + Q₁ᴴ * H * (Q₂ - Q₁) := by
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  have a : frobNorm ((Q₂ - Q₁)ᴴ * (H * Q₂)) ≤ specNorm H * frobNorm (Q₂ - Q₁) := by
    refine (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans_eq ?_
    rw [frobNorm_conjTranspose, h₂.specNorm_mul_right, mul_comm]
  have b : frobNorm (Q₁ᴴ * H * (Q₂ - Q₁)) ≤ specNorm H * frobNorm (Q₂ - Q₁) :=
    (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans
      (by gcongr; exact h₁.specNorm_conjTranspose_mul_le H)
  rw [e]
  linarith [frobNorm_add_le ((Q₂ - Q₁)ᴴ * (H * Q₂)) (Q₁ᴴ * H * (Q₂ - Q₁))]

/-- The scalar bound on the accumulated similarity error of Lemma 3.8: under $m x \le 1/4$,
$(1 + x)^m - 1 \le 2\kappa T x$ for $\kappa \ge 1$ and $T \ge 2^m$. -/
private theorem one_add_pow_sub_one_le {x κ T : ℝ} {m : ℕ} (hx : 0 ≤ x) (hκ : 1 ≤ κ)
    (hmx : (m : ℝ) * x ≤ 1 / 4) (hT : 2 ^ m ≤ T) :
    (1 + x) ^ m - 1 ≤ 2 * κ * T * x := by
  have h1 := one_add_pow_mul_one_sub_le hx m
  have hm2 : (m : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
  have hp0 : 0 ≤ (1 + x) ^ m := pow_nonneg (by linarith) m
  have hmx0 : 0 ≤ (m : ℝ) * x := by positivity
  have hp : (1 + x) ^ m ≤ 4 / 3 := by nlinarith
  have hκT : 2 ^ m ≤ κ * T := by nlinarith [pow_pos (two_pos (α := ℝ)) m]
  calc (1 + x) ^ m - 1 ≤ (1 + x) ^ m * (m * x) := by nlinarith
    _ ≤ 4 / 3 * (m * x) := by gcongr
    _ ≤ 2 * 2 ^ m * x := by nlinarith
    _ ≤ 2 * κ * T * x := by nlinarith

/-- The scalar hypotheses of Lemma 3.8 give $2^m \le ((2 + 2C)\|\mathbf{H}\|_2/d)^m$ (a shift in
$\mathbb{D}(0, C\|\mathbf{H}\|_2)$ is within $(1 + C)\|\mathbf{H}\|_2$ of every eigenvalue) and
$m x \le 1/4$. -/
private theorem forward_scalar_bounds {x C κ d : ℝ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} (hd : 0 < d) (hH : 0 < specNorm H) (hC : 0 ≤ C)
    (hκ1 : 1 ≤ κ) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖)
    (hu : x ≤ (16 * κ)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ ss.length) :
    (2 : ℝ) ^ ss.length ≤ ((2 + 2 * C) * specNorm H / d) ^ ss.length ∧
      (ss.length : ℝ) * x ≤ 1 / 4 := by
  set m := ss.length
  set Λ := (2 + 2 * C) * specNorm H
  have hL : 0 < Λ := by positivity
  have hT : (2 : ℝ) ^ m ≤ (Λ / d) ^ m := by
    rcases eq_or_ne ss [] with hss | hss
    · simp [m, hss]
    · obtain ⟨s, hs'⟩ := List.exists_mem_of_ne_nil ss hss
      have h1 := hdist s hs' 0
      have h2 := norm_le_specNorm_of_mul_eq_mul_diagonal' hV hHV 0
      have h3 := norm_sub_le (e 0) s
      have h4 := hs s hs'
      refine pow_le_pow_left₀ (by norm_num) ?_ m
      rw [le_div_iff₀ hd]
      nlinarith
  refine ⟨hT, ?_⟩
  have hρ : (d / Λ) ^ m ≤ (1 / 2) ^ m := by
    rw [div_pow, one_div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    rw [div_pow, le_div_iff₀ (by positivity)] at hT
    linarith
  have hx' : x ≤ 16⁻¹ * (1 / 2) ^ m := by
    refine hu.trans ?_
    rw [mul_inv]
    calc 16⁻¹ * κ⁻¹ * (d / Λ) ^ m ≤ 16⁻¹ * 1 * (1 / 2) ^ m := by
          gcongr
          exact inv_le_one_of_one_le₀ hκ1
      _ = _ := by ring
  have h2m : (m : ℝ) * (1 / 2) ^ m ≤ 1 := by
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact_mod_cast Nat.lt_two_pow_self.le
  nlinarith [mul_le_mul_of_nonneg_left hx' (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- **Forward error from a perturbed factorization**: if $\mathbf{M} = \mathbf{Q}\mathbf{R}$ and
$\mathbf{M} - \mathbf{E} = \widehat{\mathbf{Q}}\widehat{\mathbf{R}}$ are QR factorizations with
$\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_2 \le 1/4$, a diagonal unitary $\mathbf{D}$ has
$\|\mathbf{D}^{\mathsf H}\mathbf{H}'\mathbf{D} - \mathbf{Q}^{\mathsf H}\mathbf{H}\mathbf{Q}
\|_{\mathsf F} \le \sqrt{n + 1}\,\|\mathbf{H}' - \widehat{\mathbf{Q}}^{\mathsf H}\mathbf{H}
\widehat{\mathbf{Q}}\|_2 + 16\sqrt{n + 1}\,\|\mathbf{H}\|_2\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_2$:
the phases rescale both factorizations to positive diagonals, then
`NLAlib.IsQR.frobNorm_sub_le_of_add`. -/
private theorem exists_frobNorm_conj_sub_le_of_isQR
    {M E Q R Qh Rh H H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hMu : IsUnit M)
    (hQR : IsQR M Q R) (hQR' : IsQR (M + -E) Qh Rh) (hη : specNorm M⁻¹ * specNorm E ≤ 1 / 4) :
    ∃ D : Fin (n + 1) → ℂ, (∀ i, ‖D i‖ = 1) ∧
      frobNorm ((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D - Qᴴ * H * Q) ≤
        Real.sqrt (n + 1) * specNorm (H' - Qhᴴ * H * Qh) +
          2 * specNorm H * (8 * specNorm M⁻¹ * (Real.sqrt (n + 1) * specNorm E)) := by
  have hMEu : IsUnit (M + -E) := isUnit_add_of_specNorm_inv_mul_specNorm_lt_one hMu
    (by rw [specNorm_neg]; linarith)
  obtain ⟨p, hp, hpR⟩ := hQR.exists_phase_pos hMu
  obtain ⟨p', hp', hpR'⟩ := hQR'.exists_phase_pos hMEu
  have hs1 : ∀ i, star (p i) * p i = 1 := fun i => star_mul_self_of_norm_eq_one (hp i)
  have hs2 : ∀ i, star (p' i) * p' i = 1 := fun i => star_mul_self_of_norm_eq_one (hp' i)
  have hQd := (hQR.mul_diagonal hs1).frobNorm_sub_le_of_add hMu (hQR'.mul_diagonal hs2) hpR hpR'
    (by rw [specNorm_neg]; exact hη)
  -- the phase `D = p' p̄` matches the two unitary factors
  set D : Fin (n + 1) → ℂ := fun i => p' i * star (p i)
  have hDn : ∀ i, ‖D i‖ = 1 := fun i => by simp only [D, norm_mul, norm_star, hp, hp', mul_one]
  have hDo := hasOrthonormalCols_diagonal_of_norm_eq_one hDn
  have hPo := hasOrthonormalCols_diagonal_of_norm_eq_one (p := star p) fun i => by
    rw [Pi.star_apply, norm_star, hp]
  have eQ : Q = Q * Matrix.diagonal p * Matrix.diagonal (star p) := by
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, show (fun i => p i * star p i) = 1 from
      funext fun i => by rw [mul_comm]; exact hs1 i, Pi.one_def, Matrix.diagonal_one,
      Matrix.mul_one]
  have eQh : Qh * Matrix.diagonal D = Qh * Matrix.diagonal p' * Matrix.diagonal (star p) := by
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    rfl
  set X := H' - Qhᴴ * H * Qh
  have hsplit : (Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D - Qᴴ * H * Q =
      (Matrix.diagonal D)ᴴ * X * Matrix.diagonal D +
        ((Qh * Matrix.diagonal D)ᴴ * H * (Qh * Matrix.diagonal D) - Qᴴ * H * Q) := by
    rw [Matrix.conjTranspose_mul]
    simp only [X]
    noncomm_ring
  have hN : Real.sqrt (Fintype.card (Fin (n + 1)) : ℝ) = Real.sqrt (n + 1) := by
    rw [Fintype.card_fin]; push_cast; rfl
  refine ⟨D, hDn, hsplit ▸ (frobNorm_add_le _ _).trans (add_le_add ?_ ?_)⟩
  · rw [hDo.frobNorm_mul_right, ← hN]
    refine (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans ?_
    rw [specNorm_conjTranspose]
    calc _ ≤ 1 * frobNorm X := by
          gcongr
          exact hDo.specNorm_le_one
      _ ≤ _ := by rw [one_mul]; exact frobNorm_le_sqrt_card_mul_specNorm X
  · rw [eQh, eQ]
    refine (frobNorm_conj_sub_conj_le ((hQR.mul_diagonal hs1).hasOrthonormalCols.mul hPo)
      ((hQR'.mul_diagonal hs2).hasOrthonormalCols.mul hPo) H).trans ?_
    rw [← Matrix.sub_mul, hPo.frobNorm_mul_right]
    gcongr
    refine hQd.trans ?_
    gcongr
    rw [← hN, ← specNorm_neg E]
    exact frobNorm_le_sqrt_card_mul_specNorm _

/-- **Forward error of a degree $m$ step** (corrected [BanksGarzaVargasSrivastava2022,
Lemma 3.8]): let $\mathbf{H}$ be upper Hessenberg, $\mathbf{H}\mathbf{V} = \mathbf{V}\mathbf{D}$
with $\kappa(\mathbf{V}) \le \kappa$, every shift at distance at least $d > 0$ from every
eigenvalue and in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$, $\mathbf{H} \ne 0$, and
$x \le (16\kappa)^{-1}(d / ((2 + 2C)\|\mathbf{H}\|_2))^m$ (the paper's hypothesis lacks the factor
$(2 + 2C)^{-m}$). Then for a diagonal unitary $\mathbf{D}$ (the phase of the last diagonal entry
of the computed triangular factor; the paper compares with the positive-diagonal QR factor
directly), $\|\mathbf{D}^{\mathsf H}\widehat{\mathbf{H}}'\mathbf{D} - \mathbf{H}'\|_{\mathsf F} \le
(66 + 2C)\kappa\|\mathbf{H}\|_2((2 + 2C)\|\mathbf{H}\|_2 / d)^m\sqrt{n + 1}\,x$, where
$\mathbf{H}'$ is the exact multishift step. $64$ is the QR perturbation term with the loose
constant $8$ (`NLAlib.IsQR.frobNorm_sub_le_of_add`); $2 + 2C$ absorbs the accumulated similarity
error, which the paper's $33$ covers only when $d \le \|\mathbf{H}\|_2$ (false for large $C$:
$\mathbf{H} = -\mathbf{I}_2$, $s = 200$). The Hessenberg hypothesis is needed: Givens QR of a
matrix that is not Hessenberg is not a QR factorization, and a $3 \times 3$ counterexample
breaks the bound by a factor $1670$ without it. -/
theorem IsStableQRChain.exists_frobNorm_conj_sub_le {x C κ d : ℝ} {H H' V : Matrix (Fin (n + 1))
    (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x H ss H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C) (hd : 0 < d) (hH0 : H ≠ 0)
    (hHess : IsUpperHessenberg H)
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ κ)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖)
    (hu : x ≤ (16 * κ)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ ss.length) :
    ∃ D : Fin (n + 1) → ℂ, (∀ i, ‖D i‖ = 1) ∧
      frobNorm ((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D - multiShiftedQRStep H ss) ≤
        (66 + 2 * C) * κ * specNorm H * ((2 + 2 * C) * specNorm H / d) ^ ss.length *
          Real.sqrt (n + 1) * x := by
  set m := ss.length
  set M := Polynomial.aeval H (shiftPoly ss)
  have hκ1 : 1 ≤ κ := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hH : 0 < specNorm H :=
    (specNorm_nonneg H).lt_of_ne fun h0 => hH0 (specNorm_eq_zero_iff.mp h0.symm)
  obtain ⟨hT, hmx⟩ := forward_scalar_bounds hd hH hC hκ1 hV hHV hs hdist hu
  set Λ := (2 + 2 * C) * specNorm H
  have hL : 0 < Λ := by positivity
  -- one unitary for both parts of the backward error
  obtain ⟨Qh, hQh, hE, hsim⟩ := h.exists_specNorm_aeval_sub_le_scale hx
    (mul_nonneg hC hH.le) hs hmx ((1 + C) * specNorm H) (by linarith)
  set Rh := Rs.reverse.prod
  set E := M - Qh * Rh
  obtain ⟨hMM, hMi⟩ := specNorm_inv_aeval_shiftPoly_le hd hV hHV hdist
  have hMu : IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).mpr (Matrix.isUnit_det_of_right_inverse hMM)
  have hEb : specNorm E ≤ 4 * Λ ^ m * x := by
    refine hE.trans_eq ?_
    have e2 : Λ ^ ss.length = 2 ^ ss.length * ((1 + C) * specNorm H) ^ ss.length := by
      rw [← mul_pow]
      congr 1
      simp only [Λ]
      ring
    change _ = 4 * Λ ^ ss.length * x
    rw [e2]
    ring
  -- `‖M⁻¹‖ ‖E‖ ≤ 4 κ (Λ / d)^m x ≤ 1 / 4`
  have hηx : specNorm M⁻¹ * specNorm E ≤ 4 * κ * (Λ / d) ^ m * x := by
    calc _ ≤ κ / d ^ m * (4 * Λ ^ m * x) :=
          mul_le_mul (hMi.trans (by gcongr)) hEb (specNorm_nonneg _) (by positivity)
      _ = _ := by rw [div_pow]; ring
  have hη : specNorm M⁻¹ * specNorm E ≤ 1 / 4 := by
    refine hηx.trans ?_
    have hdm : (Λ / d) ^ m * (d / Λ) ^ m = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm Λ d, div_self (by positivity), one_pow]
    calc 4 * κ * (Λ / d) ^ m * x ≤ 4 * κ * (Λ / d) ^ m * ((16 * κ)⁻¹ * (d / Λ) ^ m) := by
          gcongr
      _ = 1 / 4 := by
          rw [mul_inv]
          field_simp
          nlinarith [hdm]
  -- compare with the exact step through the QR perturbation bound
  obtain ⟨Q, R, hQR, hstep⟩ := hHess.exists_isQR_aeval_shiftPoly ss
  have hU : Rh.IsUpperTriangular := (list_prod_isUpperTriangular_apply_self (L := Rs.reverse)
    (fun R hR => h.forall_isUpperTriangular R (List.mem_reverse.mp hR)) 0).1
  obtain ⟨D, hDn, hD⟩ := exists_frobNorm_conj_sub_le_of_isQR (H := H) (H' := H') hMu hQR
    (⟨by simp [E], hQh, hU⟩ : IsQR (M + -E) Qh Rh) hη
  refine ⟨D, hDn, hstep ▸ hD.trans ?_⟩
  have hX : specNorm (H' - Qhᴴ * H * Qh) ≤ (1 + C) * specNorm H * (2 * κ * (Λ / d) ^ m * x) :=
    hsim.trans (by gcongr; exact one_add_pow_sub_one_le hx hκ1 hmx hT)
  have hs0 : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
  have hHs := hH.le
  calc _ ≤ Real.sqrt (n + 1) * ((1 + C) * specNorm H * (2 * κ * (Λ / d) ^ m * x)) +
        2 * specNorm H * (8 * Real.sqrt (n + 1) * (4 * κ * (Λ / d) ^ m * x)) := by
        rw [show 2 * specNorm H * (8 * specNorm M⁻¹ * (Real.sqrt (n + 1) * specNorm E)) =
          2 * specNorm H * (8 * Real.sqrt (n + 1) * (specNorm M⁻¹ * specNorm E)) by ring]
        gcongr
    _ = _ := by ring

/-- **The potential after a rounded step** (corrected [BanksGarzaVargasSrivastava2022,
Lemma 5.2]): if the computed $\widehat{\mathbf{H}}'$ is within $0.001\omega$ of the exact step
$\mathbf{H}'$ entrywise on the last $k$ subdiagonals, then either one of those last $k$
subdiagonals of $\widehat{\mathbf{H}}'$ is below $\omega$, or
$\psi_k(\widehat{\mathbf{H}}') \le 1.0011\,\psi_k(\mathbf{H}')$. The paper takes the product and
the case split over all $n - 1$ subdiagonals; then the first alternative is not a decoupling of
the bottom block, and the factor is $1.001^{(n-1)/k}$. -/
theorem potential_le_or_exists_lt_of_sub_le {k : ℕ} (hk : 0 < k) {ω : ℝ} (hω : 0 < ω)
    {H₁ H₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hclose : ∀ i : Fin n, n ≤ (i : ℕ) + k →
      ‖H₁ i.succ i.castSucc - H₂ i.succ i.castSucc‖ ≤ 0.001 * ω) :
    (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H₁ i.succ i.castSucc‖ < ω) ∨
      hessenbergPotential k H₁ ≤ 1.0011 * hessenbergPotential k H₂ := by
  by_cases hex : ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H₁ i.succ i.castSucc‖ < ω
  · exact Or.inl hex
  right
  simp only [not_exists, not_and, not_lt] at hex
  set S := Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k) with hS
  have hent : ∀ i ∈ S, ‖H₁ i.succ i.castSucc‖ ≤ 1.0011 * ‖H₂ i.succ i.castSucc‖ := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    have h1 := hex i hi.2
    have h2 := hclose i hi.2
    have h3 := norm_sub_norm_le (H₁ i.succ i.castSucc) (H₂ i.succ i.castSucc)
    linarith
  have hcard : S.card ≤ k := by
    have := Finset.card_le_card_of_injOn (fun i : Fin n => (i : ℕ) + k - n) (s := S)
      (t := Finset.range k)
      (by
        intro i hi
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
          Finset.mem_coe, Finset.mem_range] at hi ⊢
        have := i.isLt
        omega)
      (by
        intro i hi j hj hij
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
          Finset.mem_coe] at hi hj
        simp only at hij
        have := i.isLt
        have := j.isLt
        apply Fin.ext
        omega)
    simpa using this
  have hprod : ∏ i ∈ S, ‖H₁ i.succ i.castSucc‖ ≤ 1.0011 ^ k * ∏ i ∈ S, ‖H₂ i.succ i.castSucc‖ := by
    calc ∏ i ∈ S, ‖H₁ i.succ i.castSucc‖ ≤ ∏ i ∈ S, (1.0011 * ‖H₂ i.succ i.castSucc‖) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) hent
      _ = 1.0011 ^ S.card * ∏ i ∈ S, ‖H₂ i.succ i.castSucc‖ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ 1.0011 ^ k * ∏ i ∈ S, ‖H₂ i.succ i.castSucc‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard)
            (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold hessenbergPotential
  rw [← hS]
  calc (∏ i ∈ S, ‖H₁ i.succ i.castSucc‖) ^ ((k : ℝ)⁻¹)
      ≤ (1.0011 ^ k * ∏ i ∈ S, ‖H₂ i.succ i.castSucc‖) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => norm_nonneg _) hprod (by positivity)
    _ = 1.0011 * (∏ i ∈ S, ‖H₂ i.succ i.castSucc‖) ^ ((k : ℝ)⁻¹) := by
        rw [Real.mul_rpow (by positivity) (Finset.prod_nonneg fun i _ => norm_nonneg _),
          Real.pow_rpow_inv_natCast (by norm_num) hk.ne']

end NLAlib
