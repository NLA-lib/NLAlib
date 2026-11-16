/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Matrix.QRIteration.ShiftedQR

/-!
# Rounded rows of a product of matrices

A row vector multiplied by $k$ matrices $\mathbf{A}_0, \dots, \mathbf{A}_{k-1}$ in turn, with a
relative error $\eta$ in each product, ends within $((1 + \eta)^k - 1)\prod_j a_j
\|\mathbf{x}_0\|$ of the exact $\mathbf{x}_0^{\mathsf T}\mathbf{A}_0 \cdots \mathbf{A}_{k-1}$,
for bounds $\|\mathbf{A}_j\|_2 \le a_j$ (`NLAlib.norm_toLp_sub_vecMul_prod_le`). The errors
committed at each step are propagated by the later factors, which do not amplify them by more
than their norms.

The case of a shift polynomial: the last row $\mathbf{e}_n^{\mathsf T}p(\mathbf{H})$,
$p(z) = \prod_j (z - s_j)$, computed by the recurrence $\widehat{\mathbf{r}}_{j+1} =
\mathrm{fl}(\widehat{\mathbf{r}}_j^{\mathsf T}(\mathbf{H} - s_j))$ from
$\widehat{\mathbf{r}}_0 = \mathbf{e}_n$, with shifts $\lvert s_j\rvert \le C\|\mathbf{H}\|_2$ and
a relative error $\eta \le 1$ per step, is within
$\tfrac12 k\eta\,((2 + 2C)\|\mathbf{H}\|_2)^k$ of the exact row
(`NLAlib.norm_toLp_sub_aeval_shiftPoly_row_le`). [BanksGarzaVargasSrivastava2022, Lemma 4.5]
computes the same quantity with the conjugate recurrence
$\widehat{\mathbf{v}}_{j+1} = \mathrm{fl}((\mathbf{H} - s_{j+1})^{\mathsf H}\widehat{\mathbf{v}}_j)$
and $\eta = n^{3/2}\boldsymbol{u}$.

## Main results

* `NLAlib.norm_toLp_sub_vecMul_prod_le`: a row through $k$ rounded products.
* `NLAlib.norm_toLp_sub_aeval_shiftPoly_row_le`: the rounded last row of a shift polynomial.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- The norm of the computed rows grows by at most $(1 + \eta)a_j$ per step. -/
private theorem norm_toLp_le_of_forall_norm_sub_vecMul_le {x : ℕ → m → 𝕜}
    {A : ℕ → Matrix m m 𝕜} {a : ℕ → ℝ} {η : ℝ} (hη : 0 ≤ η) {k : ℕ}
    (hA : ∀ j < k, specNorm (A j) ≤ a j)
    (hstep : ∀ j < k, ‖WithLp.toLp 2 (x (j + 1) - x j ᵥ* A j)‖ ≤ η * a j * ‖WithLp.toLp 2 (x j)‖) :
    ‖WithLp.toLp 2 (x k)‖ ≤ (1 + η) ^ k * (∏ j ∈ Finset.range k, a j) * ‖WithLp.toLp 2 (x 0)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (fun j hj => hA j (by omega)) (fun j hj => hstep j (by omega))
    have ha : 0 ≤ a k := (specNorm_nonneg _).trans (hA k (by omega))
    have h1 : ‖WithLp.toLp 2 (x (k + 1))‖ ≤
        ‖WithLp.toLp 2 (x (k + 1) - x k ᵥ* A k)‖ + ‖WithLp.toLp 2 (x k ᵥ* A k)‖ := by
      have := norm_add_le (WithLp.toLp 2 (x (k + 1) - x k ᵥ* A k)) (WithLp.toLp 2 (x k ᵥ* A k))
      rwa [← WithLp.toLp_add, sub_add_cancel] at this
    have h2 : ‖WithLp.toLp 2 (x k ᵥ* A k)‖ ≤ a k * ‖WithLp.toLp 2 (x k)‖ :=
      (norm_toLp_vecMul_le _ _).trans
        (mul_le_mul_of_nonneg_right (hA k (by omega)) (norm_nonneg _))
    have h3 := hstep k (by omega)
    rw [Finset.prod_range_succ, pow_succ]
    calc ‖WithLp.toLp 2 (x (k + 1))‖ ≤ (1 + η) * a k * ‖WithLp.toLp 2 (x k)‖ := by nlinarith
      _ ≤ (1 + η) * a k * ((1 + η) ^ k * (∏ j ∈ Finset.range k, a j) *
          ‖WithLp.toLp 2 (x 0)‖) := mul_le_mul_of_nonneg_left ih' (by positivity)
      _ = _ := by ring

/-- **A row through $k$ rounded products**: let $\mathbf{x}_{j+1}$ be the product
$\mathbf{x}_j^{\mathsf T}\mathbf{A}_j$ computed with the error
$\|\mathbf{x}_{j+1} - \mathbf{x}_j^{\mathsf T}\mathbf{A}_j\| \le \eta\,a_j\|\mathbf{x}_j\|$,
$\eta \ge 0$, for $\|\mathbf{A}_j\|_2 \le a_j$ and $j < k$. Then
$$\|\mathbf{x}_k - \mathbf{x}_0^{\mathsf T}\mathbf{A}_0 \cdots \mathbf{A}_{k-1}\| \le
((1 + \eta)^k - 1)\,a_0 \cdots a_{k-1}\,\|\mathbf{x}_0\|.$$
[Higham2002, Chapter 3], for products of perturbed matrices. -/
theorem norm_toLp_sub_vecMul_prod_le {x : ℕ → m → 𝕜} {A : ℕ → Matrix m m 𝕜} {a : ℕ → ℝ}
    {η : ℝ} (hη : 0 ≤ η) {k : ℕ} (hA : ∀ j < k, specNorm (A j) ≤ a j)
    (hstep : ∀ j < k, ‖WithLp.toLp 2 (x (j + 1) - x j ᵥ* A j)‖ ≤ η * a j * ‖WithLp.toLp 2 (x j)‖) :
    ‖WithLp.toLp 2 (x k - x 0 ᵥ* (List.ofFn fun j : Fin k => A j).prod)‖ ≤
      ((1 + η) ^ k - 1) * (∏ j ∈ Finset.range k, a j) * ‖WithLp.toLp 2 (x 0)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (fun j hj => hA j (by omega)) (fun j hj => hstep j (by omega))
    have hn := norm_toLp_le_of_forall_norm_sub_vecMul_le (k := k) hη (fun j hj => hA j (by omega))
      (fun j hj => hstep j (by omega))
    have ha : 0 ≤ a k := (specNorm_nonneg _).trans (hA k (by omega))
    set P := (List.ofFn fun j : Fin k => A j).prod
    have hprod : (List.ofFn fun j : Fin (k + 1) => A j).prod = P * A k := by
      rw [List.ofFn_succ', List.prod_concat]
      rfl
    have hsplit : x (k + 1) - x 0 ᵥ* (P * A k) =
        (x (k + 1) - x k ᵥ* A k) + (x k - x 0 ᵥ* P) ᵥ* A k := by
      rw [← Matrix.vecMul_vecMul, Matrix.sub_vecMul]
      abel
    rw [hprod, hsplit, WithLp.toLp_add]
    have h2 : ‖WithLp.toLp 2 ((x k - x 0 ᵥ* P) ᵥ* A k)‖ ≤
        a k * ‖WithLp.toLp 2 (x k - x 0 ᵥ* P)‖ :=
      (norm_toLp_vecMul_le _ _).trans
        (mul_le_mul_of_nonneg_right (hA k (by omega)) (norm_nonneg _))
    have h3 := hstep k (by omega)
    have h4 : η * a k * ‖WithLp.toLp 2 (x k)‖ ≤ η * a k * ((1 + η) ^ k *
        (∏ j ∈ Finset.range k, a j) * ‖WithLp.toLp 2 (x 0)‖) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    have h5 : a k * ‖WithLp.toLp 2 (x k - x 0 ᵥ* P)‖ ≤ a k * (((1 + η) ^ k - 1) *
        (∏ j ∈ Finset.range k, a j) * ‖WithLp.toLp 2 (x 0)‖) :=
      mul_le_mul_of_nonneg_left ih' ha
    calc _ ≤ ‖WithLp.toLp 2 (x (k + 1) - x k ᵥ* A k)‖ +
          ‖WithLp.toLp 2 ((x k - x 0 ᵥ* P) ᵥ* A k)‖ := norm_add_le _ _
      _ ≤ η * a k * ((1 + η) ^ k * (∏ j ∈ Finset.range k, a j) * ‖WithLp.toLp 2 (x 0)‖) +
          a k * (((1 + η) ^ k - 1) * (∏ j ∈ Finset.range k, a j) *
            ‖WithLp.toLp 2 (x 0)‖) := by linarith
      _ = _ := by rw [Finset.prod_range_succ, pow_succ]; ring

/-- $(1 + \eta)^k - 1 \le k\eta\,2^{k-1}$ for $0 \le \eta \le 1$, written as
$\tfrac12 k\eta\,2^k$. -/
private theorem one_add_pow_sub_one_le_mul_two_pow {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (k : ℕ) :
    (1 + η) ^ k - 1 ≤ k * η / 2 * 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : (1 + η) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    have hp : (0 : ℝ) ≤ 2 ^ k := by positivity
    push_cast
    rw [pow_succ, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left h2 hη, mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hη) hp]

/-- **The rounded last row of a shift polynomial**: let $\mathbf{H}$ be of order $n + 1$, the
shifts $s_0, \dots, s_{k-1}$ (the list `ss`) satisfy $\lvert s_j\rvert \le C\|\mathbf{H}\|_2$,
and let the rows $\widehat{\mathbf{r}}_j$ start at $\widehat{\mathbf{r}}_0 = \mathbf{e}_n$ and be
computed with the relative error $\eta$, $0 \le \eta \le 1$:
$\|\widehat{\mathbf{r}}_{j+1} - \widehat{\mathbf{r}}_j^{\mathsf T}(\mathbf{H} - s_j)\| \le
\eta(1 + C)\|\mathbf{H}\|_2\|\widehat{\mathbf{r}}_j\|$. Then, with $p(z) = \prod_j (z - s_j)$
(`NLAlib.shiftPoly`),
$$\|\widehat{\mathbf{r}}_k - \mathbf{e}_n^{\mathsf T}p(\mathbf{H})\| \le
\tfrac12 k\eta\,\bigl((2 + 2C)\|\mathbf{H}\|_2\bigr)^k.$$
[BanksGarzaVargasSrivastava2022, Lemma 4.5], whose proof, with $\eta = n^{3/2}\boldsymbol{u}$
and $k \le n$, gives $\tfrac12 n^{5/2}$ in place of the stated $2n^2$. -/
theorem norm_toLp_sub_aeval_shiftPoly_row_le {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ} {C η : ℝ} (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    {r : ℕ → Fin (n + 1) → ℂ} (h0 : r 0 = Pi.single (Fin.last n) 1)
    (hstep : ∀ j (hj : j < ss.length),
      ‖WithLp.toLp 2 (r (j + 1) - r j ᵥ* (H - ss[j] • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)))‖
        ≤ η * ((1 + C) * specNorm H) * ‖WithLp.toLp 2 (r j)‖) :
    ‖WithLp.toLp 2 (r ss.length - (Polynomial.aeval H (shiftPoly ss)) (Fin.last n))‖ ≤
      ss.length * η / 2 * ((2 + 2 * C) * specNorm H) ^ ss.length := by
  set A : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    fun j => H - ss.getD j 0 • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  have hAj : ∀ j (hj : j < ss.length), A j = H - ss[j] • 1 := fun j hj => by
    simp [A, List.getD_eq_getElem?_getD, hj]
  have hA : ∀ j < ss.length, specNorm (A j) ≤ (1 + C) * specNorm H := fun j hj => by
    rw [hAj j hj]
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_smul, specNorm_one]
    have := hs _ (List.getElem_mem hj)
    linarith
  have hprod : (Polynomial.aeval H (shiftPoly ss)) =
      (List.ofFn fun j : Fin ss.length => A j).prod := by
    rw [shiftPoly, map_list_prod, List.map_map]
    conv_lhs => rw [← List.ofFn_getElem (xs := ss), List.map_ofFn]
    congr 1
    refine List.ofFn_inj.mpr (funext fun j => ?_)
    simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, hAj j j.2]
  have hrow : (Polynomial.aeval H (shiftPoly ss)) (Fin.last n) =
      r 0 ᵥ* (List.ofFn fun j : Fin ss.length => A j).prod := by
    rw [h0, Matrix.single_one_vecMul, hprod]
    rfl
  have h := norm_toLp_sub_vecMul_prod_le hη hA (fun j hj => by
    rw [hAj j hj]; exact hstep j hj)
  rw [hrow]
  refine h.trans ?_
  have hr0 : ‖WithLp.toLp 2 (r 0)‖ = 1 := by
    rw [h0, PiLp.toLp_single, PiLp.norm_single, norm_one]
  rw [hr0, mul_one, Finset.prod_const, Finset.card_range]
  rcases Nat.eq_zero_or_pos ss.length with hk | hk
  · rw [hk]; simp
  have ha : 0 ≤ (1 + C) * specNorm H := (specNorm_nonneg _).trans (hA 0 hk)
  calc ((1 + η) ^ ss.length - 1) * ((1 + C) * specNorm H) ^ ss.length
      ≤ (ss.length * η / 2 * 2 ^ ss.length) * ((1 + C) * specNorm H) ^ ss.length :=
        mul_le_mul_of_nonneg_right (one_add_pow_sub_one_le_mul_two_pow hη hη1 _) (by positivity)
    _ = _ := by
        have e : ((2 + 2 * C) * specNorm H) ^ ss.length =
            2 ^ ss.length * ((1 + C) * specNorm H) ^ ss.length := by
          rw [← mul_pow]; ring_nf
        rw [e]; ring

end NLAlib
