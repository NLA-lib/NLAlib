/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Math.NormGuard
public import NLAlib.Krylov.Orthogonalization.CGS2.ExtendDecode
public import NLAlib.Krylov.Orthogonalization.CGS2.ExtendLoop
public import NLAlib.Krylov.Orthogonalization.CGS2.PassSupport
public import NLAlib.Matrix.Factorizations.BasisExtensionContract
public import NLAlib.Matrix.Factorizations.CGS2.BasisExtensionErr
public import NLAlib.Ops.Catalog.Operator

/-!
# The rounded contract of the column-wise two-pass Gram–Schmidt extension

Under the standard model of rounded arithmetic and the level-1 contracts, the implementation
`NLAlib.CGS2.cgs2ExtendImpl` with a threshold $\tau > 0$ meets the rounded contract
`NLAlib.Ops.extendRel` of a basis extension with the parameters
`NLAlib.cgs2ExtendMu` and `NLAlib.cgs2ExtendEps` at the constants of two classical passes. The
stored basis has zero columns where earlier columns were dropped: a rounded dot product with a
stored zero column decodes to zero, and the update with a zero coefficient is one more link of
the chain of rounded updates, so the two passes meet the single-vector guarantee on the support
with the pass coefficient of the full number of stored columns. Design:
`docs/design/LowRank-BlockLanczos.md` §3.5, statement E3 of §5.

## Main results

* `NLAlib.CGS2.decv_eq_zero_of_passOut`: a classical pass maps a zero vector to a zero vector.
* `NLAlib.CGS2.isOrthErrOnSupport_of_passOut`: two rounded passes against a stored basis with
  zero columns meet the single-vector guarantee on the support.
* `NLAlib.CGS2.passBudget_mono`, `NLAlib.CGS2.threshold_bounds`,
  `NLAlib.CGS2.norm_smul_sub_le_of_isScalErr`: the budget, the rounded threshold and the rounded
  scaling.
* `NLAlib.CGS2.colOut_rounded`, `NLAlib.CGS2.isBasisExtensionErr_of_colsDone`: the words of the
  rounds, decoded, give a rounded extension.
* `NLAlib.CGS2.meets_nrm2RelOf`, `NLAlib.CGS2.meets_scalRelOf`: the contracts of the norm and of
  the scaling in the form used by a round.
* `NLAlib.CGS2.cgs2Extend_spec`: the implementation meets the rounded contract of a basis
  extension.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.CGS2

open Ops Krylov.Lanczos Krylov.Lanczos.Reorth

variable {K Op Tst : Type} [Inhabited K]

/-- A rounded classical pass maps a vector that decodes to zero to a vector that decodes to
zero, for any error parameters of the dot products and of the updates: every coefficient is a
rounded dot product with the zero vector, and every update adds a zero multiple to zero. -/
theorem decv_eq_zero_of_passOut {dec : K → ℝ} {ed ea : ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec ed ea n k qs ws ws' hs) (hw : decv dec n ws = 0) :
    decv dec n ws' = 0 := by
  have hw' : ∀ i < n, dec (vec ws i) = 0 := fun i hi => congrFun hw ⟨i, hi⟩
  have hdot : ∀ j < k, dec (vec hs j) = 0 := by
    intro j hj
    have hd := h.dot j hj
    unfold IsDotErr at hd
    have h1 : ∑ i ∈ Finset.range n, dec (vec qs (j * n + i)) * dec (vec ws i) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hw' i (Finset.mem_range.mp hi), mul_zero]
    have h2 : ∑ i ∈ Finset.range n, |dec (vec qs (j * n + i)) * dec (vec ws i)| = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [hw' i (Finset.mem_range.mp hi), mul_zero, abs_zero]
    rw [h1, h2, mul_zero, sub_zero] at hd
    exact abs_eq_zero.mp (le_antisymm hd (abs_nonneg _))
  have key : ∀ (m : ℕ) (w : ℕ → K),
      Ops.Examples.AxpyChain dec ea n (fun j i => vec qs (j * n + i)) (vec hs) (vec ws) m w →
      m ≤ k →
      ∀ i < n, dec (w i) = 0 := by
    intro m w hch
    induction hch with
    | zero => exact fun _ => hw'
    | @step j w₀ w₁ t hprev ht hax ih =>
      intro hm i hi
      have h0 := ih (by omega) i hi
      have hax' := hax i hi
      simp only [h0, ht, hdot j (by omega), neg_zero, zero_mul, add_zero, sub_zero, abs_zero,
        mul_zero] at hax'
      exact abs_eq_zero.mp (le_antisymm hax' (abs_nonneg _))
  funext i
  exact key k _ h.update le_rfl i i.isLt

/-- Two rounded classical passes against a stored basis with zero columns. Let two passes
against the $k$ stored columns $\mathbf{V}$ of length $n$ have dot errors $e_d \ge 0$ and update
errors $e_a \ge 0$, the first from $\mathbf{w}$ to $\mathbf{w}_1$ with coefficients
$\mathbf{h}_1$ and the second from $\mathbf{w}_1$ to $\mathbf{w}_2$ with coefficients
$\mathbf{h}_2$, and let $\mathbf{h}$ be their sum computed with relative error $u$,
$\lvert h_j - (h_{1,j} + h_{2,j})\rvert \le u\lvert h_{1,j} + h_{2,j}\rvert$. If
$0 \le \eta \le 1/100$, $c \le 1/100$, $u \ge 0$, $4u \le c$ and
$(k+1)e_d(1+\eta)^2 + ((1+e_a)^k - 1)(1 + k(1+e_d)(1+\eta)^2) \le c$, then
$(\mathbf{h}, \mathbf{w}_2)$ meets the single-vector guarantee on the support for $\mathbf{w}$
and $\mathbf{V}$ with parameters $(\eta, 2c, 3c, 2(\eta + c)^2)$. The stored columns may be
zero: the budget counts all $k$ columns. -/
theorem isOrthErrOnSupport_of_passOut {dec : K → ℝ} {ed ea η c u : ℝ} {n k : ℕ}
    {qs ws mid ws' h₁ h₂ : List K} {h : Fin k → ℝ}
    (hp₁ : PassOut dec ed ea n k qs ws mid h₁) (hp₂ : PassOut dec ed ea n k qs mid ws' h₂)
    (hd : 0 ≤ ed) (ha : 0 ≤ ea) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 100) (hc : c ≤ 1 / 100)
    (hu : 0 ≤ u) (hu₁ : 4 * u ≤ c)
    (hbudget : (k + 1) * ed * (1 + η) ^ 2 +
      ((1 + ea) ^ k - 1) * (1 + k * (1 + ed) * (1 + η) ^ 2) ≤ c)
    (hsum : ∀ j : Fin k, |h j - (dec (vec h₁ j) + dec (vec h₂ j))| ≤
      u * |dec (vec h₁ j) + dec (vec h₂ j)|) :
    IsOrthErrOnSupport η (2 * c) (3 * c) (2 * (η + c) ^ 2) (decodeMatrix dec n k qs)
      (decv dec n ws) h (decv dec n ws') := by
  have hVb : decodeMatrix dec n k qs = basisMatrix dec n qs k := by
    ext i j
    rw [decodeMatrix_apply]
    rfl
  rw [hVb]
  exact isOrthErrOnSupport_of_two_passes hη hc hu hu₁
    (fun hV => passOut_norm_bounds hp₁ hd ha hη₀ hbudget
      (specNorm_le_one_add_of_specNorm_gramDefect_le hη₀ hV))
    (fun hV => passOut_norm_bounds hp₂ hd ha hη₀ hbudget
      (specNorm_le_one_add_of_specNorm_gramDefect_le hη₀ hV)) hsum

/-- The budget of one classical pass is monotone in the number of stored columns: for
$e_d, e_a \ge 0$ and $j \le m$,
$(j+1)e_d(1+\eta)^2 + ((1+e_a)^j - 1)(1 + j(1+e_d)(1+\eta)^2) \le
(m+1)e_d(1+\eta)^2 + ((1+e_a)^m - 1)(1 + m(1+e_d)(1+\eta)^2)$. -/
theorem passBudget_mono {ed ea η : ℝ} (hd : 0 ≤ ed) (ha : 0 ≤ ea) {j m : ℕ} (hjm : j ≤ m) :
    ((j : ℝ) + 1) * ed * (1 + η) ^ 2 +
        ((1 + ea) ^ j - 1) * (1 + j * (1 + ed) * (1 + η) ^ 2) ≤
      ((m : ℝ) + 1) * ed * (1 + η) ^ 2 +
        ((1 + ea) ^ m - 1) * (1 + m * (1 + ed) * (1 + η) ^ 2) := by
  have hjm' : (j : ℝ) ≤ m := by exact_mod_cast hjm
  have hp : (1 + ea) ^ j ≤ (1 + ea) ^ m := pow_le_pow_right₀ (by linarith) hjm
  have hp1 : 1 ≤ (1 + ea) ^ j := one_le_pow₀ (by linarith)
  have hsq : 0 ≤ (1 + η) ^ 2 := sq_nonneg _
  have hA : 0 ≤ (1 + ed) * (1 + η) ^ 2 := mul_nonneg (by linarith) hsq
  have hB : 0 ≤ ed * (1 + η) ^ 2 := mul_nonneg hd hsq
  have h1 : ((j : ℝ) + 1) * ed * (1 + η) ^ 2 ≤ ((m : ℝ) + 1) * ed * (1 + η) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hjm' hB
    nlinarith
  have hjA : (j : ℝ) * (1 + ed) * (1 + η) ^ 2 ≤ m * (1 + ed) * (1 + η) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hjm' hA
    nlinarith
  have hj0 : 0 ≤ (j : ℝ) * (1 + ed) * (1 + η) ^ 2 := by
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hA
    nlinarith
  have h2 : ((1 + ea) ^ j - 1) * (1 + j * (1 + ed) * (1 + η) ^ 2) ≤
      ((1 + ea) ^ m - 1) * (1 + m * (1 + ed) * (1 + η) ^ 2) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

omit [Inhabited K] in
/-- The rounded deflation threshold: under the standard model at $0 \le u \le 1/400$, for a
rational $\theta > 0$ and a word $\nu$ with nonnegative value, the machine product $t$ of the
literal $\theta$ and $\nu$ satisfies $\theta\nu/2 \le t \le 3\theta\nu/2$. -/
theorem threshold_bounds {M : Machine K} {dec : K → ℝ} {u : ℝ} (hM : StdModel u dec M)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 400) {θ : ℚ} (hθ : 0 < θ) {ν₀ : K} (hν : 0 ≤ dec ν₀) :
    (θ : ℝ) / 2 * dec ν₀ ≤ dec (M.mul (M.lit θ) ν₀) ∧
      dec (M.mul (M.lit θ) ν₀) ≤ 3 / 2 * θ * dec ν₀ := by
  have hθ' : (0 : ℝ) < θ := by exact_mod_cast hθ
  have h1 := abs_le.mp (hM.lit θ)
  rw [abs_of_pos hθ'] at h1
  have hLlo : (1 - u) * θ ≤ dec (M.lit θ) := by linarith
  have hLhi : dec (M.lit θ) ≤ (1 + u) * θ := by linarith
  have hl : 0 ≤ dec (M.lit θ) := le_trans (mul_nonneg (by linarith) hθ'.le) hLlo
  have h2 := abs_le.mp (hM.mul (M.lit θ) ν₀)
  rw [abs_of_nonneg (mul_nonneg hl hν)] at h2
  have hP : 0 ≤ (θ : ℝ) * dec ν₀ := mul_nonneg hθ'.le hν
  have hlo := mul_le_mul_of_nonneg_right hLlo hν
  have hhi := mul_le_mul_of_nonneg_right hLhi hν
  have hlo' := mul_le_mul_of_nonneg_left hlo (by linarith : (0 : ℝ) ≤ 1 - u)
  have hhi' := mul_le_mul_of_nonneg_left hhi (by linarith : (0 : ℝ) ≤ 1 + u)
  have hc1 : 0 ≤ ((1 - u) * (1 - u) - 1 / 2) * ((θ : ℝ) * dec ν₀) :=
    mul_nonneg (by nlinarith) hP
  have hc2 : 0 ≤ (3 / 2 - (1 + u) * (1 + u)) * ((θ : ℝ) * dec ν₀) :=
    mul_nonneg (by nlinarith) hP
  constructor <;> nlinarith

/-- A rounded scaling by a positive divisor: if $\mathbf{z}$ is $\mathbf{x}/\beta$ up to the
componentwise relative error $e \le E$ and $\beta > 0$, then
$\lVert\beta\mathbf{z} - \mathbf{x}\rVert \le E\lVert\mathbf{x}\rVert$. -/
theorem norm_smul_sub_le_of_isScalErr {dec : K → ℝ} {e E : ℝ} {n : ℕ} {β : K}
    {xs zs : List K} (he : e ≤ E) (hE : 0 ≤ E) (hβ : 0 < dec β)
    (h : IsScalErr dec e n β (vec xs) (vec zs)) :
    ‖WithLp.toLp 2 (dec β • decv dec n zs - decv dec n xs)‖ ≤
      E * ‖WithLp.toLp 2 (decv dec n xs)‖ := by
  have hcomp : ∀ i : Fin n, ‖(dec β • decv dec n zs - decv dec n xs) i‖ ≤
      ‖(E • decv dec n xs) i‖ := by
    intro i
    have hi := h hβ.ne' i i.isLt
    rw [abs_div, abs_of_pos hβ] at hi
    have e1 : (dec β • decv dec n zs - decv dec n xs) i =
        dec β * (dec (vec zs i) - dec (vec xs i) / dec β) := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, decv]
      field_simp
    rw [e1, Real.norm_eq_abs, abs_mul, abs_of_pos hβ, Pi.smul_apply, smul_eq_mul,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hE]
    calc dec β * |dec (vec zs i) - dec (vec xs i) / dec β|
        ≤ dec β * (e * (|dec (vec xs i)| / dec β)) := mul_le_mul_of_nonneg_left hi hβ.le
      _ = e * |dec (vec xs i)| := by field_simp
      _ ≤ E * |decv dec n xs i| := mul_le_mul_of_nonneg_right he (abs_nonneg _)
  have hle := EuclideanSpace.norm_toLp_le_norm_toLp hcomp
  rwa [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hE] at hle

/-- One rounded round, decoded. Under the standard model at $u \ge 0$, $4u \le c$,
$0 \le \eta_0 \le 1/100$, $c \le 1/100$, $0 \le E \le 1/100$, a rational threshold
$\theta > 0$, dot, update and square-root errors $e_d, e_a, e_s \ge 0$, scaling error at most
$E$, the pass budget of the $j$ stored columns at most $c$ and $e_d + e_s(1 + e_d) \le E$, the
words of a round `NLAlib.CGS2.ColOut` decode to: computed norms $\nu$, $\beta$ of the input
and of the reduced column accurate to $E$; the single-vector guarantee on the support with
parameters $(\eta_0, 2c, 3c, 2(\eta_0 + c)^2)$ for the coefficients of the first $j$ rows; a
zero reduced column for a zero input column; zero coefficients after row $j$; and either
$\beta \le \tfrac32\theta\nu$ with a zero new column and a zero diagonal coefficient, or
$\tfrac12\theta\nu < \beta$ with the diagonal coefficient $\beta$ and the new column
$\mathbf{q}$ with $\lVert\beta\mathbf{q} - \mathbf{w}'\rVert \le E\lVert\mathbf{w}'\rVert$. -/
theorem colOut_rounded {M : Machine K} {dec : K → ℝ} {u η₀ c E ed ea es ec : ℝ} {θ : ℚ}
    {n j r : ℕ} {vs wc w₂ cc qc : List K} (hM : StdModel u dec M) (hu : 0 ≤ u)
    (hu₁ : 4 * u ≤ c) (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100) (hc : c ≤ 1 / 100) (hE : 0 ≤ E)
    (hE' : E ≤ 1 / 100) (hθ : 0 < θ) (hd : 0 ≤ ed) (ha : 0 ≤ ea) (hs : 0 ≤ es)
    (hscal : ec ≤ E)
    (hbudget : ((j : ℝ) + 1) * ed * (1 + η₀) ^ 2 +
      ((1 + ea) ^ j - 1) * (1 + j * (1 + ed) * (1 + η₀) ^ 2) ≤ c)
    (hnorm : ed + es * (1 + ed) ≤ E)
    (h : ColOut M dec ed ea (IsNrm2Err dec ed es n) (IsScalErr dec ec n) θ n j r vs wc w₂ cc
      qc) :
    ∃ ν β : ℝ,
      IsOrthErrOnSupport η₀ (2 * c) (3 * c) (2 * (η₀ + c) ^ 2) (decodeMatrix dec n j vs)
        (decv dec n wc) (fun i : Fin j => dec (vec cc i)) (decv dec n w₂) ∧
      (decv dec n wc = 0 → decv dec n w₂ = 0) ∧
      |ν - ‖WithLp.toLp 2 (decv dec n wc)‖| ≤ E * ‖WithLp.toLp 2 (decv dec n wc)‖ ∧
      |β - ‖WithLp.toLp 2 (decv dec n w₂)‖| ≤ E * ‖WithLp.toLp 2 (decv dec n w₂)‖ ∧
      (∀ i, j < i → i < r → dec (vec cc i) = 0) ∧
      ((β ≤ 3 / 2 * θ * ν ∧ decv dec n qc = 0 ∧ dec (vec cc j) = 0) ∨
        (θ / 2 * ν < β ∧ dec (vec cc j) = β ∧
          ‖WithLp.toLp 2 (β • decv dec n qc - decv dec n w₂)‖ ≤
            E * ‖WithLp.toLp 2 (decv dec n w₂)‖)) := by
  obtain ⟨ν₀, β, mid, h₁, h₂, hn₀, hp₁, hp₂, hnβ, hadd, hzero, hbr⟩ := h
  have hes0 : 0 ≤ es * (1 + ed) := mul_nonneg hs (by linarith)
  have hesd : 0 ≤ es * ed := mul_nonneg hs hd
  have hed1 : ed < 1 := by linarith
  have hes1 : es < 1 := by nlinarith
  obtain ⟨hν0, hν⟩ := hn₀.norm_error_bounds hed1 hs hes1
  obtain ⟨hβ0, hβ⟩ := hnβ.norm_error_bounds hed1 hs hes1
  have hθ' : (0 : ℝ) < θ := by exact_mod_cast hθ
  obtain ⟨hlo, hhi⟩ := threshold_bounds hM hu (by linarith) hθ hν0
  refine ⟨dec ν₀, dec β, ?_, ?_, hν.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)),
    hβ.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)), ?_, ?_⟩
  · exact isOrthErrOnSupport_of_passOut hp₁ hp₂ hd ha hη₀ hη hc hu hu₁ hbudget fun i => by
      rw [hadd i i.isLt]
      exact hM.add _ _
  · exact fun hw => decv_eq_zero_of_passOut hp₂ (decv_eq_zero_of_passOut hp₁ hw)
  · intro i h1 h2
    rw [hzero i h1 h2]
    exact hM.zero
  · rcases hbr with ⟨hle, hcc, hq⟩ | ⟨hgt, hcc, hsc⟩
    · refine Or.inl ⟨hle.trans hhi, ?_, by rw [hcc]; exact hM.zero⟩
      funext i
      change dec (vec qc i) = 0
      rw [hq i i.isLt]
      exact hM.zero
    · have hlt : (θ : ℝ) / 2 * dec ν₀ < dec β := lt_of_le_of_lt hlo (not_le.mp hgt)
      have hβpos : 0 < dec β := lt_of_le_of_lt (mul_nonneg (by linarith) hν0) hlt
      exact Or.inr ⟨hlt, by rw [hcc], norm_smul_sub_le_of_isScalErr hscal hE hβpos hsc⟩

/-- The rounded columns give a rounded extension. Assume the standard model at $u \ge 0$,
$4u \le c$, $0 \le \eta_0 \le 1/100$, $c \le 1/100$, $0 \le E \le 1/100$, a rational threshold
$\theta > 0$, dot, update and square-root errors $e_d, e_a, e_s \ge 0$, a scaling error at most
$E$, the pass budget of $k + b$ columns
$(k+b+1)e_d(1+\eta_0)^2 + ((1+e_a)^{k+b} - 1)(1 + (k+b)(1+e_d)(1+\eta_0)^2) \le c$ and
$e_d + e_s(1 + e_d) \le E$. Then the relations `NLAlib.CGS2.ColsDone` of the $b$ columns, for
basis words of $k$ columns of length $n$, imply that the decoded basis, block, new block and
coefficients satisfy `NLAlib.IsBasisExtensionErr` with the window $\eta_0$ and the parameters
$\mu = 4c + 8(\eta_0 + c)^2/\theta + 5E$ and $\varepsilon = 3c + 2E + 2\theta$. -/
theorem isBasisExtensionErr_of_colsDone {M : Machine K} {dec : K → ℝ} {u η₀ c E ed ea es ec : ℝ}
    {θ : ℚ} {n k b : ℕ} {qs ws qn wd cs : List K} (hM : StdModel u dec M) (hu : 0 ≤ u)
    (hu₁ : 4 * u ≤ c) (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100) (hc : c ≤ 1 / 100) (hE : 0 ≤ E)
    (hE' : E ≤ 1 / 100) (hθ : 0 < θ) (hd : 0 ≤ ed) (ha : 0 ≤ ea) (hs : 0 ≤ es)
    (hscal : ec ≤ E)
    (hbudget : ((k + b : ℕ) + 1) * ed * (1 + η₀) ^ 2 +
      ((1 + ea) ^ (k + b) - 1) * (1 + (k + b : ℕ) * (1 + ed) * (1 + η₀) ^ 2) ≤ c)
    (hnorm : ed + es * (1 + ed) ≤ E) (hqs : qs.length = k * n)
    (hdone : ColsDone M dec ed ea (IsNrm2Err dec ed es n) (IsScalErr dec ec n) θ n k b qs ws b
      qn wd cs) :
    IsBasisExtensionErr η₀ (cgs2ExtendMu (2 * c) (2 * (η₀ + c) ^ 2) E θ)
      (cgs2ExtendEps (3 * c) E θ) (decodeMatrix dec n k qs) (decodeMatrix dec n b ws)
      (decodeMatrix dec n b qn) (coefTop (decodeMatrix dec (k + b) b cs))
      (coefBot (decodeMatrix dec (k + b) b cs)) := by
  have hcol : ∀ c' : Fin b, _ := fun c' =>
    colOut_rounded hM hu hu₁ hη₀ hη hc hE hE' hθ hd ha hs hscal
      ((passBudget_mono hd ha (show k + (c' : ℕ) ≤ k + b by have := c'.isLt; omega)).trans
        hbudget) hnorm (hdone c' c'.isLt)
  choose ν β hO hz hν hβ hzero hstep using hcol
  have hc0 : 0 ≤ c := by linarith
  have h50 : η₀ + c ≤ 1 / 50 := by linarith
  have h500 : 0 ≤ η₀ + c := by linarith
  refine isBasisExtensionErr_of_columns (W' := decodeMatrix dec n b wd) (ν := ν) (β := β) hη
    (by linarith) (by linarith) (by linarith) (by linarith) (by positivity) (by nlinarith) hE hE'
    (by exact_mod_cast hθ) ?_ (fun c' => ?_) (fun c' => ?_) (fun c' => ?_) (fun c' => ?_)
    (fun c' => ?_)
  · intro i j' hij
    have hij' : (j' : ℕ) < i := hij
    exact (dec_vec_coef cs j' (i := k + i) (by have := i.isLt; omega)).symm.trans
      (hzero j' (k + i) (by omega) (by have := i.isLt; omega))
  · refine IsOrthErrOnSupport.of_submatrix (storedCol_injective k b c' c'.isLt.le)
      (fun i hi => col_fromCols_colsBefore_eq_zero _ _ c' hi) ?_
    have hh : Sum.elim ((coefTop (decodeMatrix dec (k + b) b cs)).col c')
        ((strictUpper (coefBot (decodeMatrix dec (k + b) b cs))).col c') ∘
          storedCol k b c' c'.isLt.le =
        fun i : Fin (k + c') =>
          dec (vec ((cs.drop (c' * (k + b))).take (k + b)) i) := by
      funext i
      have hi := i.isLt
      have hcb := c'.isLt
      rw [dec_vec_coef (dec := dec) (k := k) cs c' (i := i) (by omega)]
      unfold storedCol
      by_cases hik : (i : ℕ) < k
      · simp only [Function.comp_apply, dif_pos hik, Sum.elim_inl]
        rfl
      · have hlt : (⟨(i : ℕ) - k, by omega⟩ : Fin b) < c' :=
          Fin.lt_def.mpr (show (i : ℕ) - k < c' by omega)
        simp only [Function.comp_apply, dif_neg hik, Sum.elim_inr, Matrix.col_apply, strictUpper,
          Matrix.of_apply, if_pos hlt, coefBot, Matrix.submatrix_apply, id_eq]
        congr 1
        exact Fin.ext (by simp only [Fin.natAdd_mk]; omega)
    rw [submatrix_fromCols_colsBefore hqs c', hh, ← decv_take_drop ws c',
      ← decv_take_drop wd c']
    exact hO c'
  · rw [← decv_take_drop ws c', ← decv_take_drop wd c']
    exact hz c'
  · rw [← decv_take_drop ws c']
    exact hν c'
  · rw [← decv_take_drop wd c']
    exact hβ c'
  · have hR : coefBot (decodeMatrix dec (k + b) b cs) c' c' =
        dec (vec ((cs.drop (c' * (k + b))).take (k + b)) (k + c')) :=
      (dec_vec_coef cs c' (i := k + c') (by have := c'.isLt; omega)).symm
    rw [← decv_take_drop qn c', ← decv_take_drop wd c', hR]
    exact hstep c'

variable [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

omit [Has ScalarOp Op] [Has CmpTst Tst] in
/-- The norm contract of the level-1 operations, in the form used by a round. -/
theorem meets_nrm2RelOf {dec : K → ℝ} {ed : ℕ → ℝ} {es : ℝ} {ok : ℕ → Prop}
    {I : Interp Op Tst K}
    (h : I.Meets .total (Has.inj Blas1Op.nrm2) ((nrm2Rel dec ed es).spec (OutApart ok))) :
    I.Meets .total (Has.inj Blas1Op.nrm2)
      ((nrm2RelOf fun n => IsNrm2Err dec (ed n) es n).spec (OutApart ok)) := by
  refine h.mono (fun _ _ _ _ _ hp => hp) ?_
  intro d ins outs τ m m' _ hpost
  obtain ⟨X, hread, hroom, Y, hlen, hrel, hm⟩ := hpost
  refine ⟨X, hread, hroom, Y, hlen, ?_, hm⟩
  simp only [nrm2Rel_rel] at hrel
  split at hrel
  · exact hrel
  · contradiction

omit [Has ScalarOp Op] [Has CmpTst Tst] in
/-- The scaling contract of the level-1 operations, in the form used by a round. -/
theorem meets_scalRelOf {dec : K → ℝ} {e : ℝ} {ok : ℕ → Prop} {I : Interp Op Tst K}
    (h : I.Meets .total (Has.inj Blas1Op.scal) ((scalRel dec e).spec (InPlace ok))) :
    I.Meets .total (Has.inj Blas1Op.scal)
      ((scalRelOf fun n => IsScalErr dec e n).spec (InPlace ok)) := by
  refine h.mono (fun _ _ _ _ _ hp => hp) ?_
  intro d ins outs τ m m' _ hpost
  obtain ⟨X, hread, hroom, Y, hlen, hrel, hm⟩ := hpost
  refine ⟨X, hread, hroom, Y, hlen, ?_, hm⟩
  simp only [scalRel_rel] at hrel
  split at hrel
  · exact hrel
  · contradiction

/-- **Column-wise two-pass classical Gram–Schmidt with threshold deflation meets the rounded
contract of a basis extension.** Assume the standard model of rounded arithmetic at the unit
roundoff $u$, the level-1 contracts with dot error $e_d(n)$, update error $e_a$, square-root
error $e_s$ and scaling error $e_c$, and exact comparisons. Let $0 \le \eta_0 \le 1/100$,
$c \le 1/100$, $u \ge 0$, $4u \le c$, $0 \le E \le 1/100$, and let $\tau > 0$ be the rational
threshold of the implementation. At every admitted dimension $(n, k, b)$ assume that the level-1
operations admit the length $n$, that $e_d(n) \ge 0$, that the pass budget of $k + b$ columns
holds,
$(k+b+1)e_d(n)(1+\eta_0)^2 + ((1+e_a)^{k+b} - 1)(1 + (k+b)(1+e_d(n))(1+\eta_0)^2) \le c$,
and that the computed norms are accurate to $E$, $e_d(n) + e_s(1 + e_d(n)) \le E$; assume also
$e_c \le E$. Then the implementation runs on all admitted operands and its decoded output is a
rounded extension with the window $\eta_0$ and the parameters
$\mu = 4c + 8(\eta_0 + c)^2/\tau + 5E$ and $\varepsilon = 3c + 2E + 2\tau$. -/
theorem cgs2Extend_spec {M : Machine K} {dec : K → ℝ} {u η₀ c E : ℝ} {τ : ℚ} {ε : Blas1Err}
    {okB : ℕ → Prop} {ok : ℕ → ℕ → ℕ → Prop} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec ε okB I) (hCmp : IsCmp dec I)
    (hu : 0 ≤ u) (hu₁ : 4 * u ≤ c) (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100) (hc : c ≤ 1 / 100)
    (hE : 0 ≤ E) (hE' : E ≤ 1 / 100) (hτ : 0 < τ)
    (ha : 0 ≤ ε.axpy) (hs : 0 ≤ ε.sqrt) (hsc : 0 ≤ ε.scal) (hscal : ε.scal ≤ E)
    (hokB : ∀ n k b, ok n k b → okB n) (hdot : ∀ n k b, ok n k b → 0 ≤ ε.dot n)
    (hbudget : ∀ n k b, ok n k b → ((k + b : ℕ) + 1) * ε.dot n * (1 + η₀) ^ 2 +
      ((1 + ε.axpy) ^ (k + b) - 1) * (1 + (k + b : ℕ) * (1 + ε.dot n) * (1 + η₀) ^ 2) ≤ c)
    (hnorm : ∀ n k b, ok n k b → ε.dot n + ε.sqrt * (1 + ε.dot n) ≤ E) :
    (cgs2ExtendImpl (Op := Op) (Tst := Tst) τ).Triple I .total
      ((extendRel dec η₀ (cgs2ExtendMu (2 * c) (2 * (η₀ + c) ^ 2) E τ)
        (cgs2ExtendEps (3 * c) E τ) ok).spec ExtendOperands) := by
  have _ := hsc
  have ops : ColOps M dec ε.dot ε.axpy (fun n => IsNrm2Err dec (ε.dot n) ε.sqrt n)
      (fun n => IsScalErr dec ε.scal n) okB I :=
    ⟨hS, hB.dot, hB.axpy, hM.neg, meets_nrm2RelOf hB.nrm2, meets_scalRelOf hB.scal, hB.copy,
      hCmp⟩
  exact cgs2Extend_triple_of ops hokB fun n k b qs ws qn wd cs hok hqs _ _ _ _ hdone =>
    isBasisExtensionErr_of_colsDone hM hu hu₁ hη₀ hη hc hE hE' hτ (hdot n k b hok) ha hs hscal
      (hbudget n k b hok) (hnorm n k b hok) hqs hdone

end NLAlib.CGS2
