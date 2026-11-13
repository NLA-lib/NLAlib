/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Traces
public import NLAlib.Matrix.FinitePrecision.ClassicalGramSchmidt
public import NLAlib.Matrix.Norms.Compare

/-!
# The rounding error of one classical Gram–Schmidt pass

The norm analysis of one rounded classical Gram–Schmidt pass. A recursive accumulation trace
(`NLAlib.Computation.IsDotTrace`) of a row of $\mathbf{A}\mathbf{x}$ is bounded entrywise against
the partial products, which gives a Euclidean bound $(1 + u)^n u\,(\|\mathbf{A}\|_{\mathsf F} +
n\|\mathbf{A}\|_2)\|\mathbf{x}\|$ for the dots and for the `gemv` of a pass. For
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0$ and $(N + j + 2)u \le 1/100$,
the dots, the product, the rounded literal $-1$ and the update together stay within
`NLAlib.cgsPassBound`,
that is <!-- value cgsPassBound N j u \eta_0 -->$2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$.
Design: `docs/design/Krylov-LanczosReorth.md` §2.2.

## Main results

* `NLAlib.Computation.IsDotTrace.abs_sub_mulVec_le`: a trace of one row of a matrix-vector
  product, against its partial products.
* `NLAlib.norm_sub_le_cgsPassBound_mul_norm_of_abs_sub_le`: the three error bounds of one rounded
  pass from the entrywise errors of its phases.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace Computation

/-- The forward error of a trace of recursive accumulation against its partial sums:
$\lvert s_n - S_n\rvert \le (1+u)^n u \sum_{k<n} (\lvert x_k\rvert\lvert y_k\rvert +
\lvert S_{k+1}\rvert)$, $S_k = \sum_{t<k} x_t y_t$. -/
private theorem IsDotTrace.abs_sub_sum_le_partial {u : ℝ} {x y s : ℕ → ℝ} {n : ℕ}
    (h : IsDotTrace (fun _ => RelErr u) x y n s) (hu : 0 ≤ u) :
    |s n - ∑ t ∈ Finset.range n, x t * y t| ≤ (1 + u) ^ n * u *
      ∑ k ∈ Finset.range n, (|x k| * |y k| + |∑ t ∈ Finset.range (k + 1), x t * y t|) := by
  have key : ∀ k ≤ n, |s k - ∑ t ∈ Finset.range k, x t * y t| ≤ (1 + u) ^ k * u *
      ∑ i ∈ Finset.range k, (|x i| * |y i| + |∑ t ∈ Finset.range (i + 1), x t * y t|) := by
    intro k
    induction k with
    | zero => intro _; simp [h.1]
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      obtain ⟨q, ⟨δ, hδ, rfl⟩, ⟨ε, hε, hs⟩, -⟩ := h.2 k (by omega)
      set S := ∑ t ∈ Finset.range (k + 1), x t * y t with hSdef
      set T := ∑ i ∈ Finset.range k, (|x i| * |y i| + |∑ t ∈ Finset.range (i + 1), x t * y t|)
      set e := s k - ∑ t ∈ Finset.range k, x t * y t
      have hS : S = ∑ t ∈ Finset.range k, x t * y t + x k * y k := Finset.sum_range_succ _ _
      have he : s (k + 1) - S = (e + x k * y k * δ) * (1 + ε) + ε * S := by
        rw [hs, hS]; ring
      rw [he, Finset.sum_range_succ]
      have h1u : 1 ≤ 1 + u := by linarith
      have hp : (1 + u) ≤ (1 + u) ^ (k + 1) := le_self_pow₀ h1u (by omega)
      have hp1 : 1 ≤ (1 + u) ^ (k + 1) := one_le_pow₀ h1u
      have hε' : |1 + ε| ≤ 1 + u := (abs_add_le _ _).trans (by rw [abs_one]; linarith)
      have hxy : |x k * y k * δ| ≤ |x k| * |y k| * u := by
        rw [abs_mul, abs_mul]; exact mul_le_mul_of_nonneg_left hδ (by positivity)
      have hεS : |ε * S| ≤ u * |S| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hε (abs_nonneg _)
      have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ => by positivity
      have hA : |(e + x k * y k * δ) * (1 + ε)| ≤ (|e| + |x k| * |y k| * u) * (1 + u) := by
        rw [abs_mul]
        exact mul_le_mul ((abs_add_le _ _).trans (add_le_add le_rfl hxy)) hε' (abs_nonneg _)
          (by positivity)
      have hB : (|e| + |x k| * |y k| * u) * (1 + u) ≤
          (1 + u) ^ (k + 1) * u * T + (1 + u) ^ (k + 1) * u * (|x k| * |y k|) := by
        have h2 : |e| * (1 + u) ≤ (1 + u) ^ k * u * T * (1 + u) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
        have h3 : (1 + u) ^ k * u * T * (1 + u) = (1 + u) ^ (k + 1) * u * T := by ring
        have h4 : |x k| * |y k| * u * (1 + u) ≤ (1 + u) ^ (k + 1) * u * (|x k| * |y k|) := by
          have := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ |x k| * |y k| * u)
          linarith
        nlinarith
      have hC : u * |S| ≤ (1 + u) ^ (k + 1) * u * |S| := by
        have := mul_le_mul_of_nonneg_left hp1 (by positivity : 0 ≤ u * |S|)
        linarith
      calc |(e + x k * y k * δ) * (1 + ε) + ε * S|
          ≤ |(e + x k * y k * δ) * (1 + ε)| + |ε * S| := abs_add_le _ _
        _ ≤ _ := by nlinarith
  exact key n le_rfl

/-- The forward error of a trace of one row of a matrix-vector product, against its partial
products: if $s$ is a trace (`NLAlib.Computation.IsDotTrace`, relative error $u \ge 0$) of
$\sum_r a_{ir} x_r$ for row $i$ of the $m \times n$ matrix $\mathbf{A}$, then
$$\lvert s_n - (\mathbf{A}\mathbf{x})_i\rvert \le (1 + u)^n u \Bigl((\lvert\mathbf{A}\rvert
\lvert\mathbf{x}\rvert)_i + \sum_{r < n} \lvert(\mathbf{A}\mathbf{x}_{\le r})_i\rvert\Bigr),$$
$\mathbf{x}_{\le r}$ the vector $\mathbf{x}$ with the entries after $r$ set to zero. This is the
bound behind the rounded dots and `gemv` of one classical Gram–Schmidt pass. -/
theorem IsDotTrace.abs_sub_mulVec_le {u : ℝ} {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin m) {xs ys s : ℕ → ℝ}
    (hxs : ∀ r (hr : r < n), xs r = A i ⟨r, hr⟩) (hys : ∀ r (hr : r < n), ys r = x ⟨r, hr⟩)
    (h : IsDotTrace (fun _ => RelErr u) xs ys n s) (hu : 0 ≤ u) :
    |s n - (A *ᵥ x) i| ≤ (1 + u) ^ n * u * ((A.map abs *ᵥ fun r => |x r|) i +
      ∑ r ∈ Finset.range n,
        |(A *ᵥ fun t : Fin n => if (t : ℕ) < r + 1 then x t else 0) i|) := by
  have hfull : ∑ t ∈ Finset.range n, xs t * ys t = (A *ᵥ x) i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [← Fin.sum_univ_eq_sum_range (fun t => xs t * ys t)]
    exact Finset.sum_congr rfl fun t _ => by rw [hxs t t.2, hys t t.2]
  have habs : ∑ k ∈ Finset.range n, |xs k| * |ys k| = (A.map abs *ᵥ fun r => |x r|) i := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [← Fin.sum_univ_eq_sum_range (fun t => |xs t| * |ys t|)]
    exact Finset.sum_congr rfl fun t _ => by rw [hxs t t.2, hys t t.2]
  have hpart : ∀ r < n, ∑ t ∈ Finset.range (r + 1), xs t * ys t =
      (A *ᵥ fun t : Fin n => if (t : ℕ) < r + 1 then x t else 0) i := by
    intro r hr
    have hsplit : ∑ t ∈ Finset.range n, (if t < r + 1 then xs t * ys t else 0) =
        ∑ t ∈ Finset.range (r + 1), xs t * ys t := by
      rw [← Finset.sum_range_add_sum_Ico _ (show r + 1 ≤ n by omega)]
      rw [Finset.sum_congr rfl fun t ht => if_pos (Finset.mem_range.mp ht),
        Finset.sum_congr rfl fun t ht => if_neg (by
          have := (Finset.mem_Ico.mp ht).1; omega), Finset.sum_const_zero, add_zero]
    rw [← hsplit]
    simp only [Matrix.mulVec, dotProduct]
    rw [← Fin.sum_univ_eq_sum_range (fun t => if t < r + 1 then xs t * ys t else 0)]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp [hxs t t.2, hys t t.2]
  have key := h.abs_sub_sum_le_partial hu
  rw [hfull, Finset.sum_add_distrib, habs,
    Finset.sum_congr rfl fun r hr => by rw [hpart r (Finset.mem_range.mp hr)]] at key
  exact key

end Computation

open Computation

/-- $(1 + u)^n \le 100/99$ for $nu \le 1/100$. -/
private theorem one_add_pow_le_of_mul_le {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hn : (n : ℝ) * u ≤ 1 / 100) : (1 + u) ^ n ≤ 100 / 99 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · norm_num
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hu1 : u < 1 := by nlinarith
  have e1 := one_add_pow_sub_one_le_roundingFactor (n := n) hu hu1
  have e2 := roundingFactor_le (n := n) hu (by linarith)
  have e3 : (n : ℝ) * u / (1 - n * u) ≤ 1 / 99 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith

/-- An entrywise bound by a scaled sum of absolute values bounds the Euclidean norm. -/
private theorem norm_toLp_le_of_abs_le_add_sum {m n : ℕ} {e A : Fin m → ℝ}
    {B : ℕ → Fin m → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ k, |e k| ≤ c * (|A k| + ∑ r ∈ Finset.range n, |B r k|)) :
    ‖WithLp.toLp 2 e‖ ≤
      c * (‖WithLp.toLp 2 A‖ + ∑ r ∈ Finset.range n, ‖WithLp.toLp 2 (B r)‖) := by
  have habs : ∀ x : Fin m → ℝ, ‖WithLp.toLp 2 (fun i => |x i|)‖ = ‖WithLp.toLp 2 x‖ :=
    fun x => by simp [EuclideanSpace.norm_eq]
  have hdom := EuclideanSpace.norm_toLp_le_norm_toLp (x := e)
    (y := c • ((fun i => |A i|) + ∑ r ∈ Finset.range n, fun i => |B r i|)) fun k => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
      rw [abs_of_nonneg (a := c * (|A k| + ∑ r ∈ Finset.range n, |B r k|)) (by positivity)]
      exact h k
  refine hdom.trans ?_
  rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [WithLp.toLp_add, WithLp.toLp_sum]
  refine (norm_add_le _ _).trans (add_le_add (habs A).le ?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => (habs (B r)).le)

/-- Truncating a vector does not increase its Euclidean norm. -/
private theorem norm_toLp_mask_le {m : ℕ} (x : Fin m → ℝ) (r : ℕ) :
    ‖WithLp.toLp 2 (fun t : Fin m => if (t : ℕ) < r then x t else 0)‖ ≤ ‖WithLp.toLp 2 x‖ :=
  EuclideanSpace.norm_toLp_le_norm_toLp fun t => by split_ifs <;> simp

/-- The entrywise trace bounds of a product bound its Euclidean error by
$c(\|\mathbf{A}\|_{\mathsf F} + n\|\mathbf{A}\|_2)\|\mathbf{x}\|$. -/
private theorem norm_toLp_sub_mulVec_le_of_partial {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (e : Fin m → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |e i - (A *ᵥ x) i| ≤ c * ((A.map abs *ᵥ fun r => |x r|) i +
      ∑ r ∈ Finset.range n, |(A *ᵥ fun t : Fin n => if (t : ℕ) < r + 1 then x t else 0) i|)) :
    ‖WithLp.toLp 2 (e - A *ᵥ x)‖ ≤ c * (frobNorm A + n * specNorm A) * ‖WithLp.toLp 2 x‖ := by
  have h1 := norm_toLp_le_of_abs_le_add_sum (e := e - A *ᵥ x)
    (A := A.map abs *ᵥ fun r => |x r|)
    (B := fun r => A *ᵥ fun t : Fin n => if (t : ℕ) < r + 1 then x t else 0) hc fun i =>
      (h i).trans (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) le_rfl) hc)
  have hx : ‖WithLp.toLp 2 (fun j => |x j|)‖ = ‖WithLp.toLp 2 x‖ := by
    simp [EuclideanSpace.norm_eq]
  have hF : frobNorm (A.map abs) = frobNorm A := by simp [frobNorm]
  have h2 : ‖WithLp.toLp 2 (A.map abs *ᵥ fun r => |x r|)‖ ≤ frobNorm A * ‖WithLp.toLp 2 x‖ := by
    have := norm_toLp_mulVec_le_frobNorm_mul (A.map abs) fun r => |x r|
    rwa [hF, hx] at this
  have h3 : ∑ r ∈ Finset.range n,
      ‖WithLp.toLp 2 (A *ᵥ fun t : Fin n => if (t : ℕ) < r + 1 then x t else 0)‖ ≤
      n * (specNorm A * ‖WithLp.toLp 2 x‖) := by
    have := Finset.sum_le_sum (s := Finset.range n) fun r _ =>
      (norm_toLp_mulVec_le A fun t : Fin n => if (t : ℕ) < r + 1 then x t else 0).trans
        (mul_le_mul_of_nonneg_left (norm_toLp_mask_le x (r + 1)) (specNorm_nonneg A))
    simpa using this
  calc _ ≤ _ := h1
    _ ≤ c * (frobNorm A * ‖WithLp.toLp 2 x‖ + n * (specNorm A * ‖WithLp.toLp 2 x‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add h2 h3) hc
    _ = _ := by ring

/-- The constant inequality behind `NLAlib.cgsPassBound`,
that is <!-- value cgsPassBound N j u \eta_0 -->$2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$. -/
private theorem cgsPass_const_le {t s J Nr : ℝ} (hN : 1 ≤ Nr) (hJ : J = 0 ∨ 1 ≤ J)
    (ht0 : 0 ≤ t) (hs0 : 0 ≤ s) (ht : t ^ 2 = J) (hs : s ^ 2 = J + 1) :
    10000 / 9801 * (t + J) + 4181 / 1000 + 100 / 99 * (t + Nr) ≤ 2 * s * (Nr + J + 2) := by
  rcases hJ with rfl | hJ
  · have : t = 0 := by nlinarith
    have : s = 1 := by nlinarith
    subst_vars; nlinarith
  · have hst : t ≤ s := by nlinarith
    have hs14 : 14 / 10 ≤ s := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hs14 (by linarith : (0 : ℝ) ≤ Nr),
      mul_le_mul_of_nonneg_right hs14 (by linarith : (0 : ℝ) ≤ J)]

/-- The arithmetic of one rounded pass: the norm bounds of its phases collected against
$2a^2\sqrt{j+1}(N+j+2)u$. -/
private theorem cgsPass_arith {a u t s Nr J nw Eh Eg yn R2 R3 : ℝ} (hu : 0 ≤ u) (ha1 : 1 ≤ a)
    (ht0 : 0 ≤ t) (hs0 : 0 ≤ s) (ht : t ^ 2 = J) (hs : s ^ 2 = J + 1) (hJ : J = 0 ∨ 1 ≤ J)
    (hN : 1 ≤ Nr ∨ nw = 0) (hN0 : 0 ≤ Nr) (hnw : 0 ≤ nw)
    (hEh : Eh ≤ 100 / 99 * u * a * (t + Nr) * nw)
    (hEg : Eg ≤ 10000 / 9801 * a ^ 2 * u * (t + J) * nw) (hyn : yn ≤ 1026 / 1000 * a ^ 2 * nw)
    (hR2 : R2 ≤ Eg + 31 / 10 * u * yn + u * nw) (hR3 : R3 ≤ R2 + a * Eh) :
    Eh ≤ 2 * a ^ 2 * s * (Nr + J + 2) * u * nw ∧ R2 ≤ 2 * a ^ 2 * s * (Nr + J + 2) * u * nw ∧
      R3 ≤ 2 * a ^ 2 * s * (Nr + J + 2) * u * nw := by
  have hJ0 : 0 ≤ J := by rw [← ht]; positivity
  set P := a ^ 2 * u * nw with hPdef
  have hP : 0 ≤ P := by positivity
  set K := 10000 / 9801 * (t + J) + 4181 / 1000 + 100 / 99 * (t + Nr) with hKdef
  have hX : P * K ≤ 2 * a ^ 2 * s * (Nr + J + 2) * u * nw := by
    rcases hN with hN | hN
    · have := mul_le_mul_of_nonneg_left (cgsPass_const_le hN hJ ht0 hs0 ht hs) hP
      calc P * K ≤ P * (2 * s * (Nr + J + 2)) := this
        _ = _ := by rw [hPdef]; ring
    · simp [hPdef, hN]
  have ha2 : a ≤ a ^ 2 := by nlinarith
  have h1 : 100 / 99 * u * a * (t + Nr) * nw ≤ P * (100 / 99 * (t + Nr)) := by
    have := mul_le_mul_of_nonneg_right ha2 (by positivity : 0 ≤ 100 / 99 * u * (t + Nr) * nw)
    calc _ = a * (100 / 99 * u * (t + Nr) * nw) := by ring
      _ ≤ a ^ 2 * (100 / 99 * u * (t + Nr) * nw) := this
      _ = _ := by rw [hPdef]; ring
  have h2 : Eg ≤ P * (10000 / 9801 * (t + J)) := hEg.trans (le_of_eq (by rw [hPdef]; ring))
  have h3 : 31 / 10 * u * yn ≤ P * (31 / 10 * (1026 / 1000)) := by
    have := mul_le_mul_of_nonneg_left hyn (by positivity : (0 : ℝ) ≤ 31 / 10 * u)
    exact this.trans (le_of_eq (by rw [hPdef]; ring))
  have h4 : u * nw ≤ P := by
    have := mul_le_mul_of_nonneg_right (by nlinarith : (1 : ℝ) ≤ a ^ 2) (mul_nonneg hu hnw)
    calc u * nw = 1 * (u * nw) := by ring
      _ ≤ a ^ 2 * (u * nw) := this
      _ = P := by rw [hPdef]; ring
  have h5 : a * Eh ≤ P * (100 / 99 * (t + Nr)) := by
    have := mul_le_mul_of_nonneg_left hEh (by linarith : 0 ≤ a)
    exact this.trans (le_of_eq (by rw [hPdef]; ring))
  have hPt : 0 ≤ P * t := mul_nonneg hP ht0
  have hPJ : 0 ≤ P * J := mul_nonneg hP hJ0
  have hPN : 0 ≤ P * Nr := mul_nonneg hP hN0
  have hR2' : R2 ≤ P * K := by
    have : R2 ≤ P * (10000 / 9801 * (t + J)) + P * (31 / 10 * (1026 / 1000)) + P := by linarith
    refine this.trans ?_
    rw [hKdef]
    nlinarith
  have hR3' : R3 ≤ P * K := by
    have : R3 ≤ P * (10000 / 9801 * (t + J)) + P * (31 / 10 * (1026 / 1000)) + P +
        P * (100 / 99 * (t + Nr)) := by linarith
    refine this.trans ?_
    rw [hKdef]
    nlinarith
  have hEh' : Eh ≤ P * K := by
    refine hEh.trans (h1.trans ?_)
    rw [hKdef]
    nlinarith
  exact ⟨hEh'.trans hX, hR2'.trans hX, hR3'.trans hX⟩

/-- The norm bounds of the dots of one rounded pass. -/
private theorem cgsPass_dot_norms {N j : ℕ} {V : Matrix (Fin N) (Fin j) ℝ} {w : Fin N → ℝ}
    {hh : Fin j → ℝ} {u a t : ℝ} (hu : 0 ≤ u) (ha0 : 0 ≤ a) (hsVT : specNorm Vᵀ ≤ a)
    (hFT : frobNorm Vᵀ ≤ t * a) (hCN : (1 + u) ^ N ≤ 100 / 99) (hut : u * (t + N) ≤ 1 / 100)
    (hh_err : ∀ k, |hh k - (Vᵀ *ᵥ w) k| ≤ (1 + u) ^ N * u * ((Vᵀ.map abs *ᵥ fun r => |w r|) k +
      ∑ r ∈ Finset.range N, |(Vᵀ *ᵥ fun t : Fin N => if (t : ℕ) < r + 1 then w t else 0) k|)) :
    ‖WithLp.toLp 2 (hh - Vᵀ *ᵥ w)‖ ≤ 100 / 99 * u * a * (t + N) * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 hh‖ ≤ 100 / 99 * a * ‖WithLp.toLp 2 w‖ := by
  have hnw : 0 ≤ ‖WithLp.toLp 2 w‖ := norm_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hEh : ‖WithLp.toLp 2 (hh - Vᵀ *ᵥ w)‖ ≤ 100 / 99 * u * a * (t + N) * ‖WithLp.toLp 2 w‖ := by
    refine (norm_toLp_sub_mulVec_le_of_partial Vᵀ w hh (by positivity) hh_err).trans ?_
    have h1 : frobNorm Vᵀ + N * specNorm Vᵀ ≤ a * (t + N) := by
      linarith [mul_le_mul_of_nonneg_left hsVT hN0]
    have h2 : (1 + u) ^ N * u ≤ 100 / 99 * u := mul_le_mul_of_nonneg_right hCN hu
    have h3 : 0 ≤ frobNorm Vᵀ + N * specNorm Vᵀ := by
      have := frobNorm_nonneg Vᵀ; have := specNorm_nonneg Vᵀ; positivity
    calc (1 + u) ^ N * u * (frobNorm Vᵀ + N * specNorm Vᵀ) * ‖WithLp.toLp 2 w‖
        ≤ 100 / 99 * u * (a * (t + N)) * ‖WithLp.toLp 2 w‖ := by gcongr
      _ = _ := by ring
  refine ⟨hEh, ?_⟩
  have e1 : ‖WithLp.toLp 2 hh‖ ≤ ‖WithLp.toLp 2 (hh - Vᵀ *ᵥ w)‖ + ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ := by
    calc ‖WithLp.toLp 2 hh‖ = ‖WithLp.toLp 2 (hh - Vᵀ *ᵥ w) + WithLp.toLp 2 (Vᵀ *ᵥ w)‖ := by
          rw [← WithLp.toLp_add, sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have e2 : ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ ≤ a * ‖WithLp.toLp 2 w‖ :=
    (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hsVT hnw)
  have e3 : 100 / 99 * u * a * (t + N) * ‖WithLp.toLp 2 w‖ ≤ a * ‖WithLp.toLp 2 w‖ / 99 := by
    have := mul_le_mul_of_nonneg_left hut (by positivity : 0 ≤ 100 / 99 * a * ‖WithLp.toLp 2 w‖)
    calc _ = 100 / 99 * a * ‖WithLp.toLp 2 w‖ * (u * (t + N)) := by ring
      _ ≤ 100 / 99 * a * ‖WithLp.toLp 2 w‖ * (1 / 100) := this
      _ = _ := by ring
  linarith

/-- The norm bounds of the product of one rounded pass. -/
private theorem cgsPass_gemv_norms {N j : ℕ} {V : Matrix (Fin N) (Fin j) ℝ} {w y : Fin N → ℝ}
    {hh : Fin j → ℝ} {u a t : ℝ} (hu : 0 ≤ u) (ha0 : 0 ≤ a) (ht0 : 0 ≤ t) (hsV : specNorm V ≤ a)
    (hF : frobNorm V ≤ t * a) (hCj : (1 + u) ^ j ≤ 100 / 99) (hutj : u * (t + j) ≤ 3 / 200)
    (hhn : ‖WithLp.toLp 2 hh‖ ≤ 100 / 99 * a * ‖WithLp.toLp 2 w‖)
    (hy_err : ∀ i, |y i - (V *ᵥ hh) i| ≤ (1 + u) ^ j * u * ((V.map abs *ᵥ fun r => |hh r|) i +
      ∑ r ∈ Finset.range j, |(V *ᵥ fun t : Fin j => if (t : ℕ) < r + 1 then hh t else 0) i|)) :
    ‖WithLp.toLp 2 (y - V *ᵥ hh)‖ ≤ 10000 / 9801 * a ^ 2 * u * (t + j) * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 y‖ ≤ 1026 / 1000 * a ^ 2 * ‖WithLp.toLp 2 w‖ := by
  have hnw : 0 ≤ ‖WithLp.toLp 2 w‖ := norm_nonneg _
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hEg : ‖WithLp.toLp 2 (y - V *ᵥ hh)‖ ≤
      10000 / 9801 * a ^ 2 * u * (t + j) * ‖WithLp.toLp 2 w‖ := by
    refine (norm_toLp_sub_mulVec_le_of_partial V hh y (by positivity) hy_err).trans ?_
    have h1 : frobNorm V + j * specNorm V ≤ a * (t + j) := by
      linarith [mul_le_mul_of_nonneg_left hsV hj0]
    have h2 : (1 + u) ^ j * u ≤ 100 / 99 * u := mul_le_mul_of_nonneg_right hCj hu
    have h3 : 0 ≤ frobNorm V + j * specNorm V := by
      have := frobNorm_nonneg V; have := specNorm_nonneg V; positivity
    calc (1 + u) ^ j * u * (frobNorm V + j * specNorm V) * ‖WithLp.toLp 2 hh‖
        ≤ 100 / 99 * u * (a * (t + j)) * (100 / 99 * a * ‖WithLp.toLp 2 w‖) := by gcongr
      _ = _ := by ring
  refine ⟨hEg, ?_⟩
  have e1 : ‖WithLp.toLp 2 y‖ ≤ ‖WithLp.toLp 2 (y - V *ᵥ hh)‖ + ‖WithLp.toLp 2 (V *ᵥ hh)‖ := by
    calc ‖WithLp.toLp 2 y‖ = ‖WithLp.toLp 2 (y - V *ᵥ hh) + WithLp.toLp 2 (V *ᵥ hh)‖ := by
          rw [← WithLp.toLp_add, sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have e2 : ‖WithLp.toLp 2 (V *ᵥ hh)‖ ≤ a * (100 / 99 * a * ‖WithLp.toLp 2 w‖) :=
    (norm_toLp_mulVec_le _ _).trans (mul_le_mul hsV hhn (norm_nonneg _) ha0)
  have e3 : 10000 / 9801 * a ^ 2 * u * (t + j) * ‖WithLp.toLp 2 w‖ ≤
      10000 / 9801 * a ^ 2 * ‖WithLp.toLp 2 w‖ * (3 / 200) := by
    have := mul_le_mul_of_nonneg_left hutj
      (by positivity : 0 ≤ 10000 / 9801 * a ^ 2 * ‖WithLp.toLp 2 w‖)
    calc _ = 10000 / 9801 * a ^ 2 * ‖WithLp.toLp 2 w‖ * (u * (t + j)) := by ring
      _ ≤ _ := this
  have e4 : a * (100 / 99 * a * ‖WithLp.toLp 2 w‖) = 100 / 99 * (a ^ 2 * ‖WithLp.toLp 2 w‖) := by
    ring
  have e5 : 0 ≤ a ^ 2 * ‖WithLp.toLp 2 w‖ := by positivity
  linarith

/-- The norm bounds of the update of one rounded pass. -/
private theorem cgsPass_update_norms {N j : ℕ} {V : Matrix (Fin N) (Fin j) ℝ}
    {w y Wd : Fin N → ℝ} {hh : Fin j → ℝ} {u δ₀ : ℝ} {θ δ : Fin N → ℝ} (hu : 0 ≤ u)
    (hu2 : 2 * u ≤ 1 / 100) (hδ₀ : |δ₀| ≤ u) (hθ : ∀ i, |θ i| ≤ roundingFactor 2 u)
    (hδ : ∀ i, |δ i| ≤ u) (hW : ∀ i, Wd i = -(1 + δ₀) * y i * (1 + θ i) + w i * (1 + δ i)) :
    ‖WithLp.toLp 2 (w - V *ᵥ hh - Wd)‖ ≤ ‖WithLp.toLp 2 (y - V *ᵥ hh)‖ +
        31 / 10 * u * ‖WithLp.toLp 2 y‖ + u * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 (Wd - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤ ‖WithLp.toLp 2 (w - V *ᵥ hh - Wd)‖ +
        specNorm V * ‖WithLp.toLp 2 (hh - Vᵀ *ᵥ w)‖ := by
  have hγ2 : roundingFactor 2 u ≤ 200 / 99 * u := by
    have := roundingFactor_le (n := 2) hu (by push_cast; linarith)
    refine this.trans ?_
    push_cast
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hg : ∀ i, |(1 + δ₀) * (1 + θ i) - 1| ≤ 31 / 10 * u := fun i => by
    have e : (1 + δ₀) * (1 + θ i) - 1 = δ₀ + θ i + δ₀ * θ i := by ring
    rw [e]
    have h1 : |δ₀ * θ i| ≤ u * (200 / 99 * u) := by
      rw [abs_mul]; exact mul_le_mul hδ₀ ((hθ i).trans hγ2) (abs_nonneg _) hu
    have h2 := abs_add_le (δ₀ + θ i) (δ₀ * θ i)
    have h3 := abs_add_le δ₀ (θ i)
    have h4 := (hθ i).trans hγ2
    have h5 : u * (200 / 99 * u) ≤ 1 / 50 * u := by nlinarith
    linarith
  have hR2id : w - V *ᵥ hh - Wd = (y - V *ᵥ hh) + (fun i => y i * ((1 + δ₀) * (1 + θ i) - 1)) -
      fun i => w i * δ i := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, hW]
    ring
  have hA : ‖WithLp.toLp 2 (fun i => y i * ((1 + δ₀) * (1 + θ i) - 1))‖ ≤
      31 / 10 * u * ‖WithLp.toLp 2 y‖ := by
    have := EuclideanSpace.norm_toLp_le_norm_toLp
      (x := fun i => y i * ((1 + δ₀) * (1 + θ i) - 1)) (y := (31 / 10 * u) • y) fun i => by
        simp only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 31 / 10 * u)]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hg i) (abs_nonneg _)
    rwa [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (by positivity)] at this
  have hB : ‖WithLp.toLp 2 (fun i => w i * δ i)‖ ≤ u * ‖WithLp.toLp 2 w‖ := by
    have := EuclideanSpace.norm_toLp_le_norm_toLp
      (x := fun i => w i * δ i) (y := u • w) fun i => by
        simp only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hu]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hδ i) (abs_nonneg _)
    rwa [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hu] at this
  refine ⟨?_, ?_⟩
  · rw [hR2id, WithLp.toLp_sub, WithLp.toLp_add]
    exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl hA)) hB)
  · have hR3id : Wd - (w - V *ᵥ (Vᵀ *ᵥ w)) = -(w - V *ᵥ hh - Wd) - V *ᵥ (hh - Vᵀ *ᵥ w) := by
      rw [Matrix.mulVec_sub]; abel
    rw [hR3id, WithLp.toLp_sub, WithLp.toLp_neg]
    refine (norm_sub_le _ _).trans (add_le_add (by rw [norm_neg]) ?_)
    exact norm_toLp_mulVec_le _ _

/-- The three error bounds of one rounded classical Gram–Schmidt pass from the entrywise errors
of its phases: if $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0$, $(N + j +
2)u \le 1/100$, $u \ge 0$, the coefficients $\mathbf{h}$ and the product $\mathbf{y}$ satisfy the
partial-product bounds of `NLAlib.Computation.IsDotTrace.abs_sub_mulVec_le` against
$\mathbf{V}^{\mathsf{T}}\mathbf{w}$ and $\mathbf{V}\mathbf{h}$, and the update is $w'_i = -(1 +
\delta_0)y_i(1 + \theta_i) + w_i(1 + \delta_i)$ with $\lvert\delta_0\rvert \le u$ (the rounded
literal $-1$), $\lvert\theta_i\rvert \le \gamma_2$ and $\lvert\delta_i\rvert \le u$, then
$\|\mathbf{h} - \mathbf{V}^{\mathsf{T}}\mathbf{w}\|$, $\|\mathbf{w} - \mathbf{V}\mathbf{h} -
\mathbf{w}'\|$ and $\|\mathbf{w}' - (\mathbf{w} - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w})\|$
are at most $c_1\|\mathbf{w}\|$, $c_1$ = `NLAlib.cgsPassBound`, that
is <!-- value cgsPassBound N j u \eta_0 -->$2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$. -/
theorem norm_sub_le_cgsPassBound_mul_norm_of_abs_sub_le {N j : ℕ} {V : Matrix (Fin N) (Fin j) ℝ}
    {w y Wd : Fin N → ℝ} {hh : Fin j → ℝ} {u η₀ δ₀ : ℝ} {θ δ : Fin N → ℝ} (hu : 0 ≤ u)
    (hV : specNorm (Vᵀ * V - 1) ≤ η₀) (hM : ((N + j + 2 : ℕ) : ℝ) * u ≤ 1 / 100)
    (hh_err : ∀ k, |hh k - (Vᵀ *ᵥ w) k| ≤ (1 + u) ^ N * u * ((Vᵀ.map abs *ᵥ fun r => |w r|) k +
      ∑ r ∈ Finset.range N, |(Vᵀ *ᵥ fun t : Fin N => if (t : ℕ) < r + 1 then w t else 0) k|))
    (hy_err : ∀ i, |y i - (V *ᵥ hh) i| ≤ (1 + u) ^ j * u * ((V.map abs *ᵥ fun r => |hh r|) i +
      ∑ r ∈ Finset.range j, |(V *ᵥ fun t : Fin j => if (t : ℕ) < r + 1 then hh t else 0) i|))
    (hδ₀ : |δ₀| ≤ u) (hθ : ∀ i, |θ i| ≤ roundingFactor 2 u) (hδ : ∀ i, |δ i| ≤ u)
    (hW : ∀ i, Wd i = -(1 + δ₀) * y i * (1 + θ i) + w i * (1 + δ i)) :
    ‖WithLp.toLp 2 (hh - Vᵀ *ᵥ w)‖ ≤ cgsPassBound N j u η₀ * ‖WithLp.toLp 2 w‖ ∧
    ‖WithLp.toLp 2 (w - V *ᵥ hh - Wd)‖ ≤ cgsPassBound N j u η₀ * ‖WithLp.toLp 2 w‖ ∧
    ‖WithLp.toLp 2 (Wd - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤ cgsPassBound N j u η₀ * ‖WithLp.toLp 2 w‖ := by
  have hη0 : 0 ≤ η₀ := (specNorm_nonneg _).trans hV
  have ha2 : Real.sqrt (1 + η₀) ^ 2 = 1 + η₀ := Real.sq_sqrt (by linarith)
  have ha0 : 0 ≤ Real.sqrt (1 + η₀) := Real.sqrt_nonneg _
  have ha1 : 1 ≤ Real.sqrt (1 + η₀) := Real.one_le_sqrt.mpr (by linarith)
  have hsV : specNorm V ≤ Real.sqrt (1 + η₀) :=
    specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le hV
  have hsVT : specNorm Vᵀ ≤ Real.sqrt (1 + η₀) := by rw [specNorm_transpose]; exact hsV
  have ht0 : 0 ≤ Real.sqrt (j : ℝ) := Real.sqrt_nonneg _
  have hs0 : 0 ≤ Real.sqrt ((j : ℝ) + 1) := Real.sqrt_nonneg _
  have ht2 : Real.sqrt (j : ℝ) ^ 2 = j := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs2 : Real.sqrt ((j : ℝ) + 1) ^ 2 = j + 1 := Real.sq_sqrt (by positivity)
  have htJ : 2 * Real.sqrt (j : ℝ) ≤ (j : ℝ) + 1 := by
    nlinarith [sq_nonneg (Real.sqrt (j : ℝ) - 1)]
  have hF : frobNorm V ≤ Real.sqrt (j : ℝ) * Real.sqrt (1 + η₀) := by
    have := frobNorm_le_sqrt_card_mul_specNorm V
    rw [Fintype.card_fin] at this
    exact this.trans (mul_le_mul_of_nonneg_left hsV ht0)
  have hFT : frobNorm Vᵀ ≤ Real.sqrt (j : ℝ) * Real.sqrt (1 + η₀) := by
    rw [frobNorm_transpose]; exact hF
  have hM' : ((N : ℝ) + j + 2) * u ≤ 1 / 100 := by exact_mod_cast hM
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hNu : (N : ℝ) * u ≤ 1 / 100 := by nlinarith
  have hju : (j : ℝ) * u ≤ 1 / 100 := by nlinarith
  have hut : u * (Real.sqrt (j : ℝ) + N) ≤ 1 / 100 := by nlinarith
  have hutj : u * (Real.sqrt (j : ℝ) + j) ≤ 3 / 200 := by nlinarith
  have hu2 : 2 * u ≤ 1 / 100 := by nlinarith
  obtain ⟨hEh, hhn⟩ := cgsPass_dot_norms hu ha0 hsVT hFT (one_add_pow_le_of_mul_le hu hNu) hut
    hh_err
  obtain ⟨hEg, hyn⟩ := cgsPass_gemv_norms hu ha0 ht0 hsV hF (one_add_pow_le_of_mul_le hu hju) hutj
    hhn hy_err
  obtain ⟨hR2, hR3⟩ := cgsPass_update_norms (V := V) (hh := hh) hu hu2 hδ₀ hθ hδ hW
  have hR3' := hR3.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right hsV (norm_nonneg _)))
  have hN : (1 : ℝ) ≤ N ∨ ‖WithLp.toLp 2 w‖ = 0 := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · right; subst hN; simp [EuclideanSpace.norm_eq]
    · left; exact_mod_cast hN
  have hJ : (j : ℝ) = 0 ∨ 1 ≤ (j : ℝ) := by
    rcases Nat.eq_zero_or_pos j with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hc : cgsPassBound N j u η₀ * ‖WithLp.toLp 2 w‖ = 2 * Real.sqrt (1 + η₀) ^ 2 *
      Real.sqrt ((j : ℝ) + 1) * ((N : ℝ) + j + 2) * u * ‖WithLp.toLp 2 w‖ := by
    rw [cgsPassBound_def, ha2]; push_cast; ring
  rw [hc]
  exact cgsPass_arith hu ha1 ht0 hs0 ht2 hs2 hJ hN hN0 (norm_nonneg _) hEh hEg hyn hR2 hR3'

end NLAlib
