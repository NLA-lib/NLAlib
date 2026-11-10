/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.CgsQR

/-!
# Classical Gram–Schmidt: the backward error and the two profiles

* `NLAlib.Ops.Examples.CgsRounded.backward` (mathematics on the final memory): the computed
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
/-- **The componentwise backward error of the computed factorization.** `r i j` is entry
`(i, j)` of `R̂`, read from the final memory; `qs` is `Q̂` by columns. -/
theorem CgsRounded.backward {dec : K → ℝ} {ε : Blas1Err} {n p bQ oQ bR oR : ℕ} {as : List K}
    {μ μ' : Mem K} (h : CgsRounded dec ε n p bQ oQ bR oR as μ μ') (hax : 0 ≤ ε.axpy)
    (hsc : 0 ≤ ε.scal) :
    ∃ (qs : List K) (r : ℕ → ℕ → K), μ'.store.readBlock bQ oQ (p * n) = some qs ∧
      (∀ j < p, ∀ i ≤ j, μ'.store.get bR (oR + j * p + i) = some (r i j)) ∧
      ∀ j < p, dec (r j j) ≠ 0 → ∀ l < n,
        |dec (vec as (j * n + l)) -
            ∑ i ∈ Finset.range (j + 1), dec (r i j) * dec (vec qs (i * n + l))| ≤
          ((1 + ε.scal) * (1 + ε.axpy) ^ j - 1) * (|dec (vec as (j * n + l))| +
            ∑ i ∈ Finset.range j, |dec (r i j) * dec (vec qs (i * n + l))|) := by
  obtain ⟨-, -, qs, rp, ρ, hq, hc⟩ := h
  have hrl : ∀ j < p, (rp j).length = j := fun j hj => by
    simpa using Store.length_of_readBlock (hc j hj).1
  have hr : ∀ j < p, ∀ i < j, vec (rp j ++ [ρ j]) i = vec (rp j) i := fun j hj i hi =>
    vec_append_left (by rw [hrl j hj]; exact hi) _
  have hρ : ∀ j < p, vec (rp j ++ [ρ j]) j = ρ j := fun j hj => by
    have := vec_concat (rp j) (ρ j)
    rwa [hrl j hj] at this
  refine ⟨qs, fun i j => vec (rp j ++ [ρ j]) i, hq,
    fun j hj i hi => Store.get_of_readBlock (hc j hj).1 (by omega) default, fun j hj h0 l hl => ?_⟩
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
`u`, the linked program computes factors meeting `CgsRounded` at the constants of the profile,
within the pushed-forward counts. One application of the certificate of the profile. -/
theorem runs_cgs_link_seq (hM : StdModel u dec M) (hu : 0 ≤ u) {I : Interp Op Tst K}
    (hI : IsScalar M I) {τ : ℕ → K} {n p oA oQ oR : ℕ} {B : Fin 3 → ℕ} {μ : Mem K}
    {as : List K} (hB : Function.Injective B) (hl : ∀ i, B i < μ.store.length)
    (hA : μ.store.readBlock (B 0) oA (p * n) = some as)
    (hQ : oQ + p * n ≤ μ.store.len (B 1)) (hR : oR + p * p ≤ μ.store.len (B 2)) :
    Runs I (Blas.ws 0) τ (cgs.link Blas.seq.table) ⟨[n, p, oA, oQ, oR], [B 0, B 1, B 2]⟩ μ
      (Count.push Blas.seq.cost (cgsCount n p)) (cgsPeak (Blas.ws 0 : Op → List ℕ → ℕ) n)
      (CgsRounded dec (Blas.seq.err u) n p (B 1) oQ (B 2) oR as μ) :=
  (Blas.seq_certifies hM hu fun _ => True).runs
    (fun _ hJ => runs_cgs_rounded hJ.1 hJ.2 hM.neg _ trivial hB hl hA hQ hR) hI

/-- **`cgs` under pairwise summation** of depth `k`, for `⌈log₂ n⌉ < k`. -/
theorem runs_cgs_link_pairwise (hM : StdModel u dec M) (hu : 0 ≤ u) {I : Interp Op Tst K}
    (hI : IsScalar M I) {τ : ℕ → K} {k n p oA oQ oR : ℕ} (hk : Nat.clog 2 n < k)
    {B : Fin 3 → ℕ} {μ : Mem K} {as : List K} (hB : Function.Injective B)
    (hl : ∀ i, B i < μ.store.length) (hA : μ.store.readBlock (B 0) oA (p * n) = some as)
    (hQ : oQ + p * n ≤ μ.store.len (B 1)) (hR : oR + p * p ≤ μ.store.len (B 2)) :
    Runs I (Blas.ws Blas.pairWs) τ (cgs.link (Blas.pairwise k).table)
      ⟨[n, p, oA, oQ, oR], [B 0, B 1, B 2]⟩ μ
      (Count.push (Blas.pairwise k).cost (cgsCount n p))
      (cgsPeak (Blas.ws Blas.pairWs : Op → List ℕ → ℕ) n)
      (CgsRounded dec (Blas.pairwise.err u) n p (B 1) oQ (B 2) oR as μ) := by
  have h := (Blas.pairwise_certifies hM hu k).runs (τ := τ)
    (fun _ hJ => runs_cgs_rounded hJ.1 hJ.2 hM.neg _ hk hB hl hA hQ hR) hI
  rwa [Blas.pairwise_wsLo] at h

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
  simp only [cgsColCount, map_add, map_nsmul, Count.push_one, Blas.seq_cost_dot,
    Blas.seq_cost_axpy, Blas.seq_cost_nrm2, Blas.seq_cost_scal, Blas.seq_cost_copy,
    Blas.seq_cost_scalar]

/-- **The backward error of the linked `cgs`**, under either profile: in every column `j` whose
diagonal entry is not zero, `|a_j - Σ_{i≤j} r̂_ij q̂_i| ≤ ((1 + u) ^ (2 j + 1) - 1)
(|a_j| + Σ_{i<j} |r̂_ij| |q̂_i|)` entry by entry. -/
theorem CgsRounded.backward_std {es : ℕ → ℝ} {n p bQ oQ bR oR : ℕ} {as : List K} {μ μ' : Mem K}
    (hu : 0 ≤ u) (h : CgsRounded dec (Blas.level1Err u es) n p bQ oQ bR oR as μ μ') :
    ∃ (qs : List K) (r : ℕ → ℕ → K), μ'.store.readBlock bQ oQ (p * n) = some qs ∧
      (∀ j < p, ∀ i ≤ j, μ'.store.get bR (oR + j * p + i) = some (r i j)) ∧
      ∀ j < p, dec (r j j) ≠ 0 → ∀ l < n,
        |dec (vec as (j * n + l)) -
            ∑ i ∈ Finset.range (j + 1), dec (r i j) * dec (vec qs (i * n + l))| ≤
          ((1 + u) ^ (2 * j + 1) - 1) * (|dec (vec as (j * n + l))| +
            ∑ i ∈ Finset.range j, |dec (r i j) * dec (vec qs (i * n + l))|) := by
  obtain ⟨qs, r, h1, h2, h3⟩ := h.backward (by simp only [Blas.level1Err]; nlinarith) hu
  refine ⟨qs, r, h1, h2, fun j hj h0 l hl => ?_⟩
  have := h3 j hj h0 l hl
  rwa [show (Blas.level1Err u es).scal = u from rfl,
    show (Blas.level1Err u es).axpy = (1 + u) ^ 2 - 1 from rfl, cgs_backward_const] at this

end NLAlib.Ops.Examples
