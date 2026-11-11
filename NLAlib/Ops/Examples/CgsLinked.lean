/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Count
public import NLAlib.Ops.Examples.CgsQR

/-!
# Classical Gram–Schmidt: the backward error and the two profiles

## Main results

* `NLAlib.Ops.Examples.CgsOut.backward` (mathematics on the final memory): the computed
  factors satisfy, in every column `j` whose diagonal entry is not zero,
  `|a_j - Σ_{i≤j} r̂_ij q̂_i| ≤ ((1 + ε_scal) (1 + ε_axpy) ^ j - 1)
  (|a_j| + Σ_{i<j} |r̂_ij| |q̂_i|)`,
  entry by entry.
* `NLAlib.Ops.Examples.runs_cgs_link_seq`, `NLAlib.Ops.Examples.runs_cgs_link_pairwise`: the
  programs linked through the two profiles, over scalar arithmetic meeting the standard model
  at `u`; one application of the certificate each. With `ε_scal = u` and
  `ε_axpy = (1 + u) ^ 2 - 1` the constant is `(1 + u) ^ (2 j + 1) - 1`
  (`NLAlib.Ops.Examples.cgs_backward_const`), for both profiles: the summation rule changes the
  accuracy of the coefficients and the counts, not the backward error.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Inhabited K]

omit [Has ScalarOp Op] [Has Blas1Op Op] in
/-- **The componentwise backward error of the computed factorization.** `rs` is `R̂` and `qs` is
`Q̂`, by columns; `r i j` is entry `(i, j)` of `R̂`. -/
theorem CgsOut.backward {dec : K → ℝ} {ε : Blas1Err} {n p : ℕ} {as qs rs : List K}
    (h : CgsOut dec ε n p as qs rs) (hlen : rs.length = p * p) (hax : 0 ≤ ε.axpy)
    (hsc : 0 ≤ ε.scal) :
    ∃ r : ℕ → ℕ → K, (∀ j < p, ∀ i ≤ j, vec rs (j * p + i) = r i j) ∧
      ∀ j < p, dec (r j j) ≠ 0 → ∀ l < n,
        |dec (vec as (j * n + l)) -
            ∑ i ∈ Finset.range (j + 1), dec (r i j) * dec (vec qs (i * n + l))| ≤
          ((1 + ε.scal) * (1 + ε.axpy) ^ j - 1) * (|dec (vec as (j * n + l))| +
            ∑ i ∈ Finset.range j, |dec (r i j) * dec (vec qs (i * n + l))|) := by
  obtain ⟨rp, ρ, hc⟩ := h
  have hrl : ∀ j < p, (rp j).length = j := fun j hj => by
    have hjp : j * p + (j + 1) ≤ p * p := by
      have := Nat.mul_le_mul_right p hj
      rw [Nat.succ_mul] at this
      omega
    have := congrArg List.length (hc j hj).1
    simp only [List.length_take, List.length_drop, List.length_append, List.length_singleton]
      at this
    have hrs : rs.length = p * p := hlen
    omega
  have hr : ∀ j < p, ∀ i < j, vec (rp j ++ [ρ j]) i = vec (rp j) i := fun j hj i hi =>
    vec_append_left (by rw [hrl j hj]; exact hi) _
  have hρ : ∀ j < p, vec (rp j ++ [ρ j]) j = ρ j := fun j hj => by
    have := vec_concat (rp j) (ρ j)
    rwa [hrl j hj] at this
  refine ⟨fun i j => vec (rp j ++ [ρ j]) i, fun j hj i hi => by
    change vec rs (j * p + i) = vec (rp j ++ [ρ j]) i
    rw [← (hc j hj).1]
    exact (Store.getD_drop_take rs _ _ _ (by omega) default).symm, fun j hj h0 l hl => ?_⟩
  dsimp only at h0 ⊢
  rw [hρ j hj] at h0
  have hb := (hc j hj).2.backward hax hsc h0 l hl
  have hQ : ∀ k < j, vec (qs.take (j * n)) (k * n + l) = vec qs (k * n + l) := fun k hk => by
    have : k * n + l < j * n := by
      have := Nat.mul_le_mul_right n hk
      rw [Nat.succ_mul] at this
      omega
    simp [vec, List.getD_eq_getElem?_getD, this]
  have ha : vec ((as.drop (j * n)).take n) l = vec as (j * n + l) :=
    Store.getD_drop_take as _ _ _ hl default
  have hqj : vec ((qs.drop (j * n)).take n) l = vec qs (j * n + l) :=
    Store.getD_drop_take qs _ _ _ hl default
  rw [ha, hqj] at hb
  have e1 : ∑ i ∈ Finset.range j, dec (vec (rp j ++ [ρ j]) i) * dec (vec qs (i * n + l)) =
      ∑ k ∈ Finset.range j, dec (vec (rp j) k) * dec (vec (qs.take (j * n)) (k * n + l)) :=
    Finset.sum_congr rfl fun k hk => by
      rw [hr j hj k (Finset.mem_range.mp hk), hQ k (Finset.mem_range.mp hk)]
  have e2 : ∑ i ∈ Finset.range j, |dec (vec (rp j ++ [ρ j]) i) * dec (vec qs (i * n + l))| =
      ∑ k ∈ Finset.range j, |dec (vec (rp j) k) * dec (vec (qs.take (j * n)) (k * n + l))| :=
    Finset.sum_congr rfl fun k hk => by
      rw [hr j hj k (Finset.mem_range.mp hk), hQ k (Finset.mem_range.mp hk)]
  rw [Finset.sum_range_succ, hρ j hj, e1, e2]
  exact hb

/-- The backward-error constant of `cgs` over scalar arithmetic at the unit roundoff `u`. -/
theorem cgs_backward_const (u : ℝ) (j : ℕ) :
    (1 + u) * (1 + ((1 + u) ^ 2 - 1)) ^ j - 1 = (1 + u) ^ (2 * j + 1) - 1 := by
  rw [show 1 + ((1 + u) ^ 2 - 1) = (1 + u) ^ 2 by ring, ← pow_mul]
  ring

variable [Apart Blas1Op ScalarOp Op] {M : Machine K} {u : ℝ} {dec : K → ℝ}

/-- **`cgs` under sequential summation**: over scalar arithmetic meeting the standard model at
`u`, the linked program computes factors meeting `CgsFactored` at the constants of the profile,
within the pushed-forward counts. One application of the certificate of the profile. -/
theorem runs_cgs_link_seq (hM : StdModel u dec M) (hu : 0 ≤ u) {I : Interp Op Tst K}
    (hI : IsScalar M I) {τ : Tape K} {n p : ℕ} {A Q R : ℕ × ℕ} {μ : Mem K}
    {as r₀ : List K} (hAQ : A.1 ≠ Q.1) (hAR : A.1 ≠ R.1) (hQR : Q.1 ≠ R.1)
    (hl : μ.Live [A, Q, R]) (hA : μ.store.readBlock A.1 A.2 (p * n) = some as)
    (hR₀ : μ.store.readBlock R.1 R.2 (p * p) = some r₀)
    (hQ : Q.2 + p * n ≤ μ.store.len Q.1) (hR : R.2 + p * p ≤ μ.store.len R.1) :
    ConditionalRuns I (Blas.ws 0) τ (cgs.link Blas.seq.table) (Env.frame [n, p] [A, R, Q, R]) μ
      ((p * (p - 1) / 2) • (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) • Blas.sc .copy +
          (n - 1) • Blas.sc .add)) + (Blas.sc .neg + n • (Blas.sc .mul + Blas.sc .add))) +
        p • (n • Blas.sc .copy + (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) •
          Blas.sc .copy + (n - 1) • Blas.sc .add) + Blas.sc .sqrt) +
          (n • Blas.sc .div + n • Blas.sc .copy))))
      (cgsPeak (Blas.ws 0 : Op → List ℕ → ℕ) n) (CgsFactored dec (Blas.seq.err u) n p Q R as μ) :=
  ((Blas.seq_certifies hM hu fun _ => True).runs
    (fun _ hJ => runs_cgs_rounded hJ.1 hJ.2 hM.neg _ trivial hAQ hAR hQR hl hA hR₀ hQ hR) hI).mono
    (by count_eval [cgsCount, cgsColCount]) le_rfl fun _ h => h

/-- **`cgs` under pairwise summation** of depth `k`, for `⌈log₂ n⌉ < k`. -/
theorem runs_cgs_link_pairwise (hM : StdModel u dec M) (hu : 0 ≤ u) {I : Interp Op Tst K}
    (hI : IsScalar M I) {τ : Tape K} {k n p : ℕ} (hk : Nat.clog 2 n < k)
    {A Q R : ℕ × ℕ} {μ : Mem K} {as r₀ : List K} (hAQ : A.1 ≠ Q.1) (hAR : A.1 ≠ R.1)
    (hQR : Q.1 ≠ R.1) (hl : μ.Live [A, Q, R])
    (hA : μ.store.readBlock A.1 A.2 (p * n) = some as)
    (hR₀ : μ.store.readBlock R.1 R.2 (p * p) = some r₀)
    (hQ : Q.2 + p * n ≤ μ.store.len Q.1) (hR : R.2 + p * p ≤ μ.store.len R.1) :
    ConditionalRuns I (Blas.ws Blas.pairWs) τ (cgs.link (Blas.pairwise k).table)
      (Env.frame [n, p] [A, R, Q, R]) μ
      ((p * (p - 1) / 2) • (n • Blas.sc .mul + Blas.pairCount n +
          (Blas.sc .neg + n • (Blas.sc .mul + Blas.sc .add))) +
        p • (n • Blas.sc .copy + (n • Blas.sc .mul + (Blas.pairCount n + Blas.sc .sqrt)) +
          (n • Blas.sc .div + n • Blas.sc .copy)))
      (cgsPeak (Blas.ws Blas.pairWs : Op → List ℕ → ℕ) n)
      (CgsFactored dec (Blas.pairwise.err u) n p Q R as μ) := by
  have h := (Blas.pairwise_certifies hM hu k).runs (τ := τ)
    (fun _ hJ => runs_cgs_rounded hJ.1 hJ.2 hM.neg _ hk hAQ hAR hQR hl hA hR₀ hQ hR) hI
  rw [Blas.pairwise_wsLo] at h
  exact h.mono (by count_eval [cgsCount, cgsColCount]) le_rfl fun _ h => h

omit [Inhabited K] in
/-- **The scalar counts of column `j` of `cgs` under sequential summation**, by evaluating the
push-forward: `(2 j + 1) n` multiplications, `j (n - 1) + j n + (n - 1)` additions, `j`
negations, `n` divisions, one square root, `2 n` copies of the vector, and the literals and
copies of the `j + 1` summations. -/
theorem push_seq_cgsColCount (n j : ℕ) :
    Count.push Blas.seq.cost (cgsColCount (Op := Op) (Tst := Tst) n j) =
      j • (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) • Blas.sc .copy +
        (n - 1) • Blas.sc .add))) + (n • Blas.sc .copy +
      (j • (Blas.sc .neg + n • (Blas.sc .mul + Blas.sc .add)) +
      (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) • Blas.sc .copy +
        (n - 1) • Blas.sc .add) + Blas.sc .sqrt) + (n • Blas.sc .div + n • Blas.sc .copy)))) := by
  count_eval [cgsColCount]

/-- **The backward error of the linked `cgs`**, under either profile: in every column `j` whose
diagonal entry is not zero, `|a_j - Σ_{i≤j} r̂_ij q̂_i| ≤ ((1 + u) ^ (2 j + 1) - 1)
(|a_j| + Σ_{i<j} |r̂_ij| |q̂_i|)` entry by entry. -/
theorem CgsOut.backward_std {es : ℕ → ℝ} {n p : ℕ} {as qs rs : List K} (hu : 0 ≤ u)
    (h : CgsOut dec (Blas.level1Err u es) n p as qs rs) (hlen : rs.length = p * p) :
    ∃ r : ℕ → ℕ → K, (∀ j < p, ∀ i ≤ j, vec rs (j * p + i) = r i j) ∧
      ∀ j < p, dec (r j j) ≠ 0 → ∀ l < n,
        |dec (vec as (j * n + l)) -
            ∑ i ∈ Finset.range (j + 1), dec (r i j) * dec (vec qs (i * n + l))| ≤
          ((1 + u) ^ (2 * j + 1) - 1) * (|dec (vec as (j * n + l))| +
            ∑ i ∈ Finset.range j, |dec (r i j) * dec (vec qs (i * n + l))|) := by
  obtain ⟨r, h2, h3⟩ := h.backward hlen (by simp only [Blas.level1Err]; nlinarith) hu
  refine ⟨r, h2, fun j hj h0 l hl => ?_⟩
  have := h3 j hj h0 l hl
  rwa [show (Blas.level1Err u es).scal = u from rfl,
    show (Blas.level1Err u es).axpy = (1 + u) ^ 2 - 1 from rfl, cgs_backward_const] at this

end NLAlib.Ops.Examples
