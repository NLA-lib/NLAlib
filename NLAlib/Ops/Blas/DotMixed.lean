/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.ArithmeticError
public import NLAlib.Ops.Blas.Dot
public import NLAlib.Ops.Blas.Sum

/-!
# Sequential dot products with mixed rounding and finite range

A mathematical accumulation trace tracks each rounded product and addition. Its error and
input-only range bounds apply to the actual sequential scalar implementation, including
absolute rounding allowances. Adding zero need not be exact for these bounds.

## Main results

* `NLAlib.Ops.IsDotTrace` records local product and accumulation errors.
* `NLAlib.Ops.IsDotTrace.abs_sum_mul_sub_le_of_absRelErr` bounds its forward error.
* `NLAlib.Ops.IsDotTrace.abs_add_le_of_absRelErr` bounds every next exact accumulation
  using input entries, dimension and precision.
-/

@[expose] public section

namespace NLAlib.Ops

open NLAlib.Computation

/-- A sequential inner-product trace starts at zero and relates every product and sum
by the specified local error predicate. This relation asserts no execution or memory fact. -/
def IsDotTrace (err : ℝ → ℝ → Prop) (x y : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ) : Prop :=
  s 0 = 0 ∧ ∀ k < n, ∃ q : ℝ, err (x k * y k) q ∧ err (s k + q) (s (k + 1))

private theorem abs_add_sub_le_of_absRelErr {u η S s a q z B E : ℝ}
    (hu : 0 ≤ u) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hm : AbsRelErr u η a q) (ha : AbsRelErr u η (s + q) z)
    (hS : |S - s| ≤ E) (hb : |S| ≤ B) :
    |S + a - z| ≤ (1 + u) ^ 2 * E + ((1 + u) ^ 2 - 1) * (B + |a|) +
      (2 + u) * η := by
  have hs : |s| ≤ B + E := by
    calc
      |s| = |S - (S - s)| := by congr 1; ring
      _ ≤ |S| + |S - s| := abs_sub _ _
      _ ≤ B + E := add_le_add hb hS
  have hsq : |s + q| ≤ B + E + ((1 + u) * |a| + η) :=
    (abs_add_le _ _).trans (add_le_add hs hm.abs_le)
  have hz : |S + a - z| ≤ E + (u * |a| + η) +
      (u * (B + E + ((1 + u) * |a| + η)) + η) := by
    calc
      |S + a - z| = |(S - s) + (a - q) + (s + q - z)| := by congr 1; ring
      _ ≤ |S - s| + |a - q| + |s + q - z| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add hS hm.abs_sub_le)
        (ha.abs_sub_le.trans (by gcongr))
  have h₁ : 0 ≤ (u + u ^ 2) * E := mul_nonneg (by positivity) hE
  have h₂ : 0 ≤ (u + u ^ 2) * B := mul_nonneg (by positivity) hB
  nlinarith

/-- A dot trace with relative allowance $u \ge 0$ and absolute allowance $\eta \ge 0$ on
each product and addition has error at most
$$\bigl((1+u)^{2n}-1\bigr)\sum_{i<n}\lvert x_i y_i\rvert
  \quad + n(1+u)^{2n}(2+u)\eta\,.$$
No smallness assumption on $nu$ is needed. This supports underflow-aware consumers of the
actual kernel; it is not a no-overflow assertion. [Higham2002, §2.2 and §3.1]. -/
theorem IsDotTrace.abs_sum_mul_sub_le_of_absRelErr {u η : ℝ}
    (hu : 0 ≤ u) (hη : 0 ≤ η) {x y s : ℕ → ℝ} {n : ℕ}
    (h : IsDotTrace (AbsRelErr u η) x y n s) :
    |∑ k ∈ Finset.range n, x k * y k - s n| ≤
      ((1 + u) ^ (2 * n) - 1) * (∑ k ∈ Finset.range n, |x k * y k|) +
      n * (1 + u) ^ (2 * n) * (2 + u) * η := by
  have hb : 1 ≤ 1 + u := by linarith
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, h.1, sub_self,
      abs_zero, mul_zero, Nat.cast_zero, zero_mul, add_zero, le_refl]
  | succ n ih =>
    have ht : IsDotTrace (AbsRelErr u η) x y n s :=
      ⟨h.1, fun k hk => h.2 k (by omega)⟩
    have hp : 1 ≤ (1 + u) ^ (2 * n) := one_le_pow₀ hb
    have hpow : (1 + u) ^ (2 * (n + 1)) = (1 + u) ^ (2 * n) * (1 + u) ^ 2 := by
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    have hp₂ : 1 ≤ (1 + u) ^ 2 := one_le_pow₀ hb
    let B : ℝ := ∑ k ∈ Finset.range n, |x k * y k|
    let E : ℝ := ((1 + u) ^ (2 * n) - 1) * B + n * (1 + u) ^ (2 * n) * (2 + u) * η
    have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hs : |∑ k ∈ Finset.range n, x k * y k - s n| ≤ E := ih ht
    obtain ⟨q, hm, ha⟩ := h.2 n (by omega)
    have hstep := abs_add_sub_le_of_absRelErr hu hB hE hm ha hs
      (Finset.abs_sum_le_sum_abs _ _)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hpow, Nat.cast_add, Nat.cast_one]
    have hp₀ : 0 ≤ (1 + u) ^ (2 * n) := by positivity
    have hc₀ : 0 ≤ (2 + u) * η := mul_nonneg (by linarith) hη
    have htail : 0 ≤ ((1 + u) ^ (2 * n) * (1 + u) ^ 2 - 1) * ((2 + u) * η) :=
      mul_nonneg (by nlinarith) hc₀
    have hprod : 0 ≤ ((1 + u) ^ (2 * n) - 1) * (1 + u) ^ 2 * |x n * y n| :=
      mul_nonneg (mul_nonneg (by linarith) (by positivity)) (abs_nonneg _)
    dsimp [E, B] at hstep
    nlinarith [sq_nonneg (1 + u)]

/-- Every next exact accumulation in a mixed-error dot prefix of length $k<N$ has magnitude
at most
$$ (1+u)^{2N}\sum_{i<N}\lvert x_i y_i\rvert + N(1+u)^{2N}(2+u)\eta\,.$$
The allowances $u$ and $\eta$ must be nonnegative. This input-only bound can discharge a
finite-format backend's range condition without observing intermediate states, and does not
require a dimension-precision smallness assumption. -/
theorem IsDotTrace.abs_add_le_of_absRelErr {u η : ℝ} {x y s : ℕ → ℝ}
    {k N : ℕ} {q : ℝ} (h : IsDotTrace (AbsRelErr u η) x y k s)
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hkn : k < N) (hq : AbsRelErr u η (x k * y k) q) :
    |s k + q| ≤ (1 + u) ^ (2 * N) * (∑ i ∈ Finset.range N, |x i * y i|) +
      N * (1 + u) ^ (2 * N) * (2 + u) * η := by
  have hb : 1 ≤ 1 + u := by linarith
  have hPN : 1 ≤ (1 + u) ^ (2 * N) := one_le_pow₀ hb
  have hPk : (1 + u) ^ (2 * k) ≤ (1 + u) ^ (2 * N) :=
    pow_le_pow_right₀ hb (by omega)
  have hbN : 1 + u ≤ (1 + u) ^ (2 * N) := by
    calc
      1 + u = (1 + u) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hb (by omega)
  have herr := h.abs_sum_mul_sub_le_of_absRelErr hu hη
  have hs : |s k| ≤ (1 + u) ^ (2 * k) * (∑ i ∈ Finset.range k, |x i * y i|) +
      k * (1 + u) ^ (2 * k) * (2 + u) * η := by
    calc
      |s k| = |(∑ i ∈ Finset.range k, x i * y i) -
          ((∑ i ∈ Finset.range k, x i * y i) - s k)| := by congr 1; ring
      _ ≤ |∑ i ∈ Finset.range k, x i * y i| +
          |(∑ i ∈ Finset.range k, x i * y i) - s k| := abs_sub _ _
      _ ≤ _ := (add_le_add (Finset.abs_sum_le_sum_abs _ _) herr).trans_eq (by ring)
  have hsum : (∑ i ∈ Finset.range k, |x i * y i|) + |x k * y k| ≤
      ∑ i ∈ Finset.range N, |x i * y i| := by
    rw [← Finset.sum_range_succ]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkn)
      (fun _ _ _ => abs_nonneg _)
  have hsN : |s k| ≤ (1 + u) ^ (2 * N) * (∑ i ∈ Finset.range k, |x i * y i|) +
      k * (1 + u) ^ (2 * N) * (2 + u) * η := hs.trans (by gcongr)
  have hqN : |q| ≤ (1 + u) ^ (2 * N) * |x k * y k| + η :=
    hq.abs_le.trans (by gcongr)
  have hpadding : η ≤ (1 + u) ^ (2 * N) * (2 + u) * η := by
    have : 1 ≤ (1 + u) ^ (2 * N) * (2 + u) := by nlinarith
    exact le_mul_of_one_le_left hη this
  have hsumN := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ (1 + u) ^ (2 * N) by positivity)
  have hcount : (k : ℝ) + 1 ≤ N := by exact_mod_cast hkn
  have htail := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ (1 + u) ^ (2 * N) * (2 + u) * η by positivity)
  have hbound := (abs_add_le (s k) q).trans (add_le_add hsN hqN)
  nlinarith

/-- With absolute allowance $\eta\ge0$ and zero relative allowance, every next exact
accumulation in a dot trace of length $k<N$ has magnitude at most
$\sum_{i<N}\lvert x_i y_i\rvert+2N\eta$. This bound uses only input entries, dimension and
precision; it can discharge a backend's safe-range condition without observing intermediate
states. -/
theorem IsDotTrace.abs_add_le_of_absRelErr_zero {η : ℝ} {x y s : ℕ → ℝ}
    {k N : ℕ} {q : ℝ} (h : IsDotTrace (AbsRelErr 0 η) x y k s)
    (hη : 0 ≤ η) (hkn : k < N) (hq : AbsRelErr 0 η (x k * y k) q) :
    |s k + q| ≤ (∑ i ∈ Finset.range N, |x i * y i|) + 2 * N * η := by
  have hbound := h.abs_add_le_of_absRelErr (by norm_num) hη hkn hq
  simpa only [add_zero, one_pow, one_mul, mul_one, mul_comm (N : ℝ) 2] using hbound

/-- An input-only range condition for every intermediate exact product and accumulation
of sequential dot. It uses the vector entries, dimension and two rounding allowances. -/
def DotRange {K : Type} (u eta : ℝ) (dec : K → ℝ) (safe : ℝ → Prop)
    (n : ℕ) (x y : ℕ → K) : Prop :=
  ∀ z : ℝ, |z| ≤ (1 + u) ^ (2 * n) *
    (∑ i ∈ Finset.range n, |dec (x i) * dec (y i)|) +
      n * (1 + u) ^ (2 * n) * (2 + u) * eta → safe z

/-- A numerical upper bound on the input-only envelope supplies the dot range condition. -/
theorem DotRange.of_le {K : Type} {u eta B : ℝ} {dec : K → ℝ} {safe : ℝ → Prop}
    {n : ℕ} {x y : ℕ → K}
    (hB : (1 + u) ^ (2 * n) * (∑ i ∈ Finset.range n, |dec (x i) * dec (y i)|) +
      n * (1 + u) ^ (2 * n) * (2 + u) * eta ≤ B)
    (hsafe : ∀ z : ℝ, |z| ≤ B → safe z) : DotRange u eta dec safe n x y :=
  fun z hz => hsafe z (hz.trans hB)

/-- The word returned after a prefix of sequential products and summation. The empty
prefix returns literal zero; nonempty prefixes copy the first product and add the rest. -/
def dotPrefix {K : Type} (M : Machine K) (x y : ℕ → K) : ℕ → K
  | 0 => M.lit 0
  | k + 1 => seqF M (fun i => M.mul (x i) (y i)) k

/-- The prefix word is precisely the mathematical function of sequential summation. -/
theorem dotPrefix_eq_sumSeqF {K : Type} (M : Machine K) (x y : ℕ → K) (n : ℕ) :
    dotPrefix M x y n = sumSeqF M (fun i => M.mul (x i) (y i)) n := by
  cases n with
  | zero => rfl
  | succ n => simp [dotPrefix, sumSeqF]

/-- Every noninitial accumulation performs the machine's actual addition. -/
theorem dotPrefix_succ_of_pos {K : Type} (M : Machine K) (x y : ℕ → K) {k : ℕ}
    (hk : 0 < k) :
    dotPrefix M x y (k + 1) = M.add (dotPrefix M x y k) (M.mul (x k) (y k)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rfl

/-- The mixed arithmetic model and an input-only range envelope certify every local
product and addition in the actual sequential dot word function. Zero literal decoding
is explicit. No bound on an observed trajectory or successful execution is assumed. -/
theorem MixedModel.isDotTrace_dotPrefix {K : Type} {M : Machine K} {dec : K → ℝ}
    {u eta : ℝ} {safe : ℝ → Prop} (hM : MixedModel u eta dec M safe)
    (hzero : dec (M.lit 0) = 0) {n : ℕ} {x y : ℕ → K}
    (hsafe : DotRange u eta dec safe n x y) :
    IsDotTrace (AbsRelErr u eta) (fun i => dec (x i)) (fun i => dec (y i)) n
      (fun k => dec (dotPrefix M x y k)) := by
  have hu := hM.roundoff_nonneg
  have heta := hM.absolute_nonneg
  have hpow : 1 ≤ (1 + u) ^ (2 * n) := one_le_pow₀ (by linarith)
  have hsum : 0 ≤ ∑ i ∈ Finset.range n, |dec (x i) * dec (y i)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsumBound : (∑ i ∈ Finset.range n, |dec (x i) * dec (y i)|) ≤
      (1 + u) ^ (2 * n) * (∑ i ∈ Finset.range n, |dec (x i) * dec (y i)|) +
        n * (1 + u) ^ (2 * n) * (2 + u) * eta := by
    exact (le_mul_of_one_le_left hsum hpow).trans (le_add_of_nonneg_right (by positivity))
  have htrace : ∀ k, k ≤ n →
      IsDotTrace (AbsRelErr u eta) (fun i => dec (x i)) (fun i => dec (y i)) k
        (fun i => dec (dotPrefix M x y i)) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨hzero, fun i hi => by omega⟩
    | succ k ih =>
      intro hk
      have ht := ih (by omega)
      have hkn : k < n := by omega
      have hprodBound : |dec (x k) * dec (y k)| ≤
          ∑ i ∈ Finset.range n, |dec (x i) * dec (y i)| :=
        Finset.single_le_sum (f := fun i => |dec (x i) * dec (y i)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hkn)
      have hprod : AbsRelErr u eta (dec (x k) * dec (y k)) (dec (M.mul (x k) (y k))) := by
        simpa only [AbsRelErr, abs_sub_comm] using
          hM.mul (x k) (y k) (hsafe _ (hprodBound.trans hsumBound))
      refine ⟨hzero, fun i hi => ?_⟩
      by_cases hik : i < k
      · exact ht.2 i hik
      have heq : i = k := by omega
      subst i
      refine ⟨dec (M.mul (x k) (y k)), hprod, ?_⟩
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp only [dotPrefix, seqF, AbsRelErr, hzero, zero_add, sub_self, abs_zero]
        positivity
      · have hadd := hM.add (dotPrefix M x y k) (M.mul (x k) (y k))
          (hsafe _ (ht.abs_add_le_of_absRelErr hu heta hkn hprod))
        simpa only [AbsRelErr, dotPrefix_succ_of_pos M x y hpos, abs_sub_comm] using hadd
  exact htrace n le_rfl

/-- Mixed-error bound for the actual word function of the scalar sequential dot product.
Its input-only range condition controls products and every exact addition before rounding.
[Higham2002, §2.2 and §3.1]. -/
theorem MixedModel.abs_sum_mul_sub_sumSeqF_le {K : Type} {M : Machine K} {dec : K → ℝ}
    {u eta : ℝ} {safe : ℝ → Prop} (hM : MixedModel u eta dec M safe)
    (hzero : dec (M.lit 0) = 0) {n : ℕ} {x y : ℕ → K}
    (hsafe : DotRange u eta dec safe n x y) :
    |∑ i ∈ Finset.range n, dec (x i) * dec (y i) -
      dec (sumSeqF M (fun i => M.mul (x i) (y i)) n)| ≤
        ((1 + u) ^ (2 * n) - 1) * (∑ i ∈ Finset.range n, |dec (x i) * dec (y i)|) +
          n * (1 + u) ^ (2 * n) * (2 + u) * eta := by
  simpa only [dotPrefix_eq_sumSeqF] using
    (hM.isDotTrace_dotPrefix hzero hsafe).abs_sum_mul_sub_le_of_absRelErr
      hM.roundoff_nonneg hM.absolute_nonneg

end NLAlib.Ops
