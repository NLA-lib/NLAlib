/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Blas1

/-!
# Classical Gram–Schmidt in finite precision: the mathematics

No program here. One column of classical Gram–Schmidt is described by local errors
(`NLAlib.Ops.Examples.CgsCol`): the coefficients `r_i ≈ q_iᵀ a`, the chain of updates
`w ← w - r_i q_i` (`NLAlib.Ops.Examples.AxpyChain`), the norm `ρ ≈ ‖w‖` and the scaled column
`q ≈ w / ρ`.

## Main results

* `NLAlib.Ops.Examples.AxpyChain.abs_sub_le`: after `i` updates of componentwise error `e`, the
  vector is `a - Σ_{k<i} r_k q_k` up to `((1 + e) ^ i - 1) (|a| + Σ_{k<i} |r_k| |q_k|)`.
* `NLAlib.Ops.Examples.CgsCol.backward`: **the componentwise backward error of a column**,
  `|a - Σ_{k<j} r_k q_k - ρ q| ≤ ((1 + ε_scal) (1 + ε_axpy) ^ j - 1) (|a| + Σ_{k<j} |r_k| |q_k|)`
  when `ρ ≠ 0`. It holds whatever the accuracy of the coefficients and of the norm: the computed
  factors reproduce `A` even when they are far from orthogonal. Bounds on `|Q̂| |R̂|` in terms of
  `‖a‖`, and the loss of orthogonality in terms of `κ(A) u`, need the accuracy of `dot` and
  `nrm2`, which `CgsCol` records; they are not proved here.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K : Type}

/-- **The chain of updates of one column**: from `a`, the `i`-th update replaces `w` by
`w + t q_i` up to the componentwise error `e`, with `t = -r_i` exactly. -/
inductive AxpyChain (dec : K → ℝ) (e : ℝ) (n : ℕ) (q : ℕ → ℕ → K) (r : ℕ → K) (a : ℕ → K) :
    ℕ → (ℕ → K) → Prop
  /-- No update. -/
  | zero : AxpyChain dec e n q r a 0 a
  /-- One more update. -/
  | step {i : ℕ} {w w' : ℕ → K} {t : K} : AxpyChain dec e n q r a i w → dec t = -dec (r i) →
      IsAxpyErr dec e n t (q i) w w' → AxpyChain dec e n q r a (i + 1) w'

/-- **The accumulated error of the chain of updates.** -/
theorem AxpyChain.abs_sub_le {dec : K → ℝ} {e : ℝ} {n : ℕ} {q : ℕ → ℕ → K} {r a : ℕ → K}
    {i : ℕ} {w : ℕ → K} (he : 0 ≤ e) (h : AxpyChain dec e n q r a i w) : ∀ l < n,
    |dec (w l) - (dec (a l) - ∑ k ∈ Finset.range i, dec (r k) * dec (q k l))| ≤
      ((1 + e) ^ i - 1) * (|dec (a l)| + ∑ k ∈ Finset.range i, |dec (r k) * dec (q k l)|) := by
  induction h with
  | zero => intro l _; simp
  | @step i w w' t _ ht hax ih =>
    intro l hl
    have ih := ih l hl
    have hx := hax l hl
    rw [ht, neg_mul] at hx
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← sub_sub, ← add_assoc]
    have hX : |dec (a l) - ∑ k ∈ Finset.range i, dec (r k) * dec (q k l)| ≤
        |dec (a l)| + ∑ k ∈ Finset.range i, |dec (r k) * dec (q k l)| :=
      (abs_sub _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    have hS : 0 ≤ ∑ k ∈ Finset.range i, |dec (r k) * dec (q k l)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hc : 0 ≤ (1 + e) ^ i - 1 := sub_nonneg.mpr (one_le_pow₀ (by linarith))
    rw [show (1 + e) ^ (i + 1) - 1 = (1 + e) * (1 + ((1 + e) ^ i - 1)) - 1 by ring]
    generalize (1 + e) ^ i - 1 = c at ih hc
    generalize dec (a l) - ∑ k ∈ Finset.range i, dec (r k) * dec (q k l) = X at ih hX
    generalize |dec (a l)| + ∑ k ∈ Finset.range i, |dec (r k) * dec (q k l)| = Mi at ih hX
    generalize dec (r i) * dec (q i l) = b at hx
    generalize dec (w l) = y at ih hx
    generalize dec (w' l) = y' at hx
    rw [abs_neg] at hx
    have hy : |y| ≤ (1 + c) * Mi := by
      have := abs_add_le X (y - X)
      rw [add_sub_cancel] at this
      linarith
    have hMi : 0 ≤ Mi := (abs_nonneg X).trans hX
    have h3 : |y' - (X - b)| ≤ |y' - (y + -b)| + |y - X| := by
      have := abs_add_le (y' - (y + -b)) (y - X)
      rwa [show y' - (y + -b) + (y - X) = y' - (X - b) by ring] at this
    have hb := abs_nonneg b
    nlinarith [mul_nonneg hc hb, mul_nonneg (mul_nonneg he hc) hb,
      mul_le_mul_of_nonneg_left hy he]

variable [Inhabited K]

/-- **One column of classical Gram–Schmidt, by its local errors.** `Qp` holds the `j` previous
columns, `a` the column of `A`, `rp` the coefficients, `ρ` the diagonal entry, `qj` the new
column. -/
structure CgsCol (dec : K → ℝ) (ε : Blas1Err) (n j : ℕ) (Qp a rp : List K) (ρ : K)
    (qj : List K) : Prop where
  /-- The coefficients are dot products with the column of `A`. -/
  dot : ∀ i < j, IsDotErr dec (ε.dot n) n (fun l => vec Qp (i * n + l)) (vec a) (vec rp i)
  /-- The projections are subtracted one by one, the norm is taken, the vector is scaled. -/
  proj : ∃ w : List K, AxpyChain dec ε.axpy n (fun i l => vec Qp (i * n + l)) (vec rp)
    (vec a) j (vec w) ∧ IsNrm2Err dec (ε.dot n) ε.sqrt n (vec w) ρ ∧
    IsScalErr dec ε.scal n ρ (vec w) (vec qj)

/-- **The componentwise backward error of a column of classical Gram–Schmidt**: if the diagonal
entry is not zero, `|a - Σ_{k<j} r_k q_k - ρ q| ≤ ((1 + ε_scal) (1 + ε_axpy) ^ j - 1)
(|a| + Σ_{k<j} |r_k| |q_k|)`, entry by entry. -/
theorem CgsCol.backward {dec : K → ℝ} {ε : Blas1Err} {n j : ℕ} {Qp a rp : List K} {ρ : K}
    {qj : List K} (h : CgsCol dec ε n j Qp a rp ρ qj) (hax : 0 ≤ ε.axpy) (hsc : 0 ≤ ε.scal)
    (hρ : dec ρ ≠ 0) : ∀ l < n,
    |dec (vec a l) - (∑ k ∈ Finset.range j, dec (vec rp k) * dec (vec Qp (k * n + l)) +
        dec ρ * dec (vec qj l))| ≤
      ((1 + ε.scal) * (1 + ε.axpy) ^ j - 1) * (|dec (vec a l)| +
        ∑ k ∈ Finset.range j, |dec (vec rp k) * dec (vec Qp (k * n + l))|) := by
  intro l hl
  obtain ⟨w, hc, -, hs⟩ := h.proj
  have h1 := hc.abs_sub_le hax l hl
  have h2 := hs l hl
  have hX : |dec (vec a l) - ∑ k ∈ Finset.range j, dec (vec rp k) * dec (vec Qp (k * n + l))| ≤
      |dec (vec a l)| + ∑ k ∈ Finset.range j, |dec (vec rp k) * dec (vec Qp (k * n + l))| :=
    (abs_sub _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
  have hc' : 0 ≤ (1 + ε.axpy) ^ j - 1 := sub_nonneg.mpr (one_le_pow₀ (by linarith))
  rw [← sub_sub, show (1 + ε.scal) * (1 + ε.axpy) ^ j - 1 =
    (1 + ε.scal) * (1 + ((1 + ε.axpy) ^ j - 1)) - 1 by ring]
  generalize (1 + ε.axpy) ^ j - 1 = c at h1 hc'
  generalize dec (vec a l) - ∑ k ∈ Finset.range j, dec (vec rp k) * dec (vec Qp (k * n + l)) = X
    at h1 hX
  generalize |dec (vec a l)| + ∑ k ∈ Finset.range j, |dec (vec rp k) *
    dec (vec Qp (k * n + l))| = Mj at h1 hX
  generalize dec (vec w l) = y at h1 h2
  generalize dec (vec qj l) = z at h2
  generalize dec ρ = r at h2 hρ
  have h3 : |r * z - y| ≤ ε.scal * |y| := by
    have := mul_le_mul_of_nonneg_left h2 (abs_nonneg r)
    rwa [← abs_mul, mul_sub, mul_div_cancel₀ _ hρ, mul_left_comm, ← abs_mul,
      mul_div_cancel₀ _ hρ] at this
  have hy : |y| ≤ (1 + c) * Mj := by
    have := abs_add_le X (y - X)
    rw [add_sub_cancel] at this
    linarith
  have h4 : |X - r * z| ≤ |y - X| + |r * z - y| := by
    have := abs_add_le (X - y) (y - r * z)
    rwa [sub_add_sub_cancel, abs_sub_comm X y, abs_sub_comm y (r * z)] at this
  nlinarith [mul_le_mul_of_nonneg_left hy hsc]

end NLAlib.Ops.Examples
