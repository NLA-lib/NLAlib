/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.BlasCert

/-!
# Test case: the matrix product in finite precision

`NLAlib.Ops.Examples.gemm` computes `C = A B` by `m p` calls of `dot`: `A` is `m × n` stored by
rows, `B` is `n × p` stored by columns (so that a row of `A` and a column of `B` are contiguous
blocks), `C` is `m × p` stored by rows.

## Main results

* Mathematics: the postcondition `NLAlib.Ops.Examples.GemmRounded` is the classical componentwise
  forward bound `|ĉ_ij - Σ_k a_ik b_kj| ≤ ε Σ_k |a_ik| |b_kj|`; nothing else is needed.
* Abstract theorem (`NLAlib.Ops.Examples.runs_gemm_rounded`): for every interpretation meeting
  the level-1 contracts at `ε`, with `m p` calls of `dot` at the length `n`.
* Corollaries, one application of `Profile.Certifies.runs` each
  (`NLAlib.Ops.Examples.runs_gemm_link_seq`, `NLAlib.Ops.Examples.runs_gemm_link_pairwise`):
  `ε = (1 + u) ^ n - 1` under sequential summation and `(1 + u) ^ (⌈log₂ n⌉ + 1) - 1` under
  pairwise summation, with the scalar counts of
  `NLAlib.Ops.Examples.push_seq_gemmCount` and `NLAlib.Ops.Examples.push_pairwise_gemmCount`:
  `m p n` multiplications and `m p (n - 1)` additions in both.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} [Has Blas1Op Op]

/-- **The matrix product by rows times columns.** Index variables: `m`, `n`, `p`, the offsets of
`A`, `B`, `C`, then `i`, `j`; buffer variables: `A`, `B`, `C`. -/
def gemm : Stmt Op Tst :=
  .loop (.var 0) (.loop (.var 2) (.call (Has.inj Blas1Op.dot) [.var 1]
    [⟨0, .var 3 + .var 6 * .var 1⟩, ⟨1, .var 4 + .var 7 * .var 1⟩]
    [⟨2, .var 5 + (.var 6 * .var 2 + .var 7)⟩]))

/-- The call counts of `gemm`: `m p` calls of `dot` at the length `n`. -/
noncomputable def gemmCount (m n p : ℕ) : Count Op Tst :=
  (m * p) • Count.one (Has.inj Blas1Op.dot) [n]

theorem staticCost_gemm (m n p a b c : ℕ) :
    staticCost (gemm (Op := Op) (Tst := Tst)) [m, n, p, a, b, c] = gemmCount m n p := by
  simp [gemm, staticCost, useCost, gemmCount, mul_smul]

theorem staticPeak_gemm_le (W : Op → List ℕ → ℕ) (m n p a b c : ℕ) :
    staticPeak W (gemm (Op := Op) (Tst := Tst)) [m, n, p, a, b, c] ≤
      W (Has.inj Blas1Op.dot) [n] := by
  simp only [gemm, staticPeak]
  exact Finset.sup_le fun i _ => Finset.sup_le fun j _ => by simp

variable [Inhabited K]

/-- Entry `q` of `C`, in row-major order, is the dot product of a row of `A` and a column of `B`
up to the relative error `e`. -/
def GemmEntry (dec : K → ℝ) (e : ℝ) (n p : ℕ) (as bs : List K) (q : ℕ) (v : K) : Prop :=
  IsDotErr dec e n (fun k => vec as (q / p * n + k)) (fun k => vec bs (q % p * n + k)) v

/-- **The postcondition of `gemm`**: the block `C` holds `cs`, nothing else is written, and every
entry satisfies the componentwise forward bound
`|ĉ_ij - Σ_k a_ik b_kj| ≤ e Σ_k |a_ik| |b_kj|`. -/
def GemmRounded (dec : K → ℝ) (e : ℝ) (m n p : ℕ) (C : ℕ × ℕ) (as bs : List K)
    (μ μ' : Mem K) : Prop :=
  ∃ cs : List K, μ' = μ.updBlock C cs ∧ cs.length = m * p ∧ ∀ i < m, ∀ j < p,
    |dec (vec cs (i * p + j)) - ∑ k ∈ Finset.range n, dec (vec as (i * n + k)) *
      dec (vec bs (j * n + k))| ≤
      e * ∑ k ∈ Finset.range n, |dec (vec as (i * n + k)) * dec (vec bs (j * n + k))|

/-- The invariant of both loops of `gemm`, after `c` entries. -/
def GemmInv (dec : K → ℝ) (e : ℝ) (n p bC oC : ℕ) (as bs : List K) (μ : Mem K) (c : ℕ)
    (μ' : Mem K) : Prop :=
  ∃ s' cs, μ' = ⟨s', μ.pos⟩ ∧ μ.store.EqOff (Store.inBlock bC oC c) s' ∧
    s'.readBlock bC oC c = some cs ∧ ∀ q < c, GemmEntry dec e n p as bs q (vec cs q)

/-- **The run of `gemm`**, for every interpretation meeting the level-1 contracts. The handles
are an injective family. -/
theorem wp_gemm {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {J : Interp Op Tst K}
    (hJ : IsBlas1 dec ε ok J) {τ : ℕ → K} {m n p oA oB oC : ℕ} {H : Fin 3 → ℕ} {μ : Mem K}
    {as bs : List K} (hok : ok n) (hH : Function.Injective H) (hl : ∀ i, H i < μ.store.length)
    (hA : μ.store.readBlock (H 0) oA (m * n) = some as)
    (hB : μ.store.readBlock (H 1) oB (p * n) = some bs)
    (hC : oC + m * p ≤ μ.store.len (H 2)) :
    Wp .total J τ gemm ⟨[m, n, p, oA, oB, oC], [H 0, H 1, H 2]⟩
      (GemmInv dec (ε.dot n) n p (H 2) oC as bs μ (m * p)) μ := by
  refine wp_loop (k := m) rfl (fun i => GemmInv dec (ε.dot n) n p (H 2) oC as bs μ (i * p))
    ⟨_, [], rfl, by simpa using Store.EqOff.refl _ _, by simp, by simp⟩ ?_ fun _ h => h
  intro i hi μ₁ hinv
  have hip : i * p + p ≤ m * p := by
    have := Nat.mul_le_mul_right p hi
    rwa [Nat.succ_mul] at this
  have hin : i * n + n ≤ m * n := by
    have := Nat.mul_le_mul_right n hi
    rwa [Nat.succ_mul] at this
  refine wp_loop (k := p) rfl
    (fun j => GemmInv dec (ε.dot n) n p (H 2) oC as bs μ (i * p + j)) hinv ?_
    fun μ₂ h => by rwa [Nat.succ_mul]
  rintro j hj μ₂ ⟨s', cs, rfl, hfr, hr, hE⟩
  have hjn : j * n + n ≤ p * n := by
    have := Nat.mul_le_mul_right n hj
    rwa [Nat.succ_mul] at this
  have hlen := hfr.len_eq (H 2)
  have hlive : ∀ i, H i < s'.length := fun i => hfr.length_eq ▸ hl i
  have hra := hfr.readBlock_of (Store.readBlock_sub hA hin) (by store_side [hH.eq_iff])
  have hrb := hfr.readBlock_of (Store.readBlock_sub hB hjn) (by store_side [hH.eq_iff])
  refine wp_call_rel_cell hJ.dot rfl rfl rfl rfl rfl ⟨hok, by simp [hH.eq_iff]⟩ ?_
    (xs := [(as.drop (i * n)).take n, (bs.drop (j * n)).take n]) ?_ ?_ fun v hv => ?_
  · store_simp
  · store_simp
  · store_simp
  have hcl := Store.length_of_readBlock hr
  refine ⟨_, cs ++ [v], rfl, (hfr.mono fun b q h => ⟨h.1, h.2.1, by have := h.2.2; omega⟩).upd
    ⟨rfl, by omega, by omega⟩ _, Store.readBlock_upd_concat hr (by omega) _, fun q hq => ?_⟩
  obtain hlt | heq : q < i * p + j ∨ q = i * p + j := by omega
  · rw [vec_append_left (hcl ▸ hlt)]
    exact hE q hlt
  · rw [heq, ← hcl, vec_concat, hcl]
    have hp : 0 < p := by omega
    have e1 : (i * p + j) / p = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hj, zero_add]
    have e2 : (i * p + j) % p = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    unfold GemmEntry
    rw [e1, e2]
    exact IsDotErr.congr hv (fun k hk => Store.getD_drop_take as _ _ _ hk default)
      fun k hk => Store.getD_drop_take bs _ _ _ hk default

/-- **The abstract theorem of `gemm`**: for every interpretation meeting the level-1 contracts
at `ε` for the length `n`, the run terminates within `m p` calls of `dot` and the workspace of
one, and the computed product satisfies the componentwise forward bound with `ε.dot n`. -/
theorem runs_gemm_rounded {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {J : Interp Op Tst K}
    (hJ : IsBlas1 dec ε ok J) (W : Op → List ℕ → ℕ) {τ : ℕ → K} {m n p oA oB oC : ℕ}
    {H : Fin 3 → ℕ} {μ : Mem K} {as bs : List K} (hok : ok n) (hH : Function.Injective H)
    (hl : ∀ i, H i < μ.store.length) (hA : μ.store.readBlock (H 0) oA (m * n) = some as)
    (hB : μ.store.readBlock (H 1) oB (p * n) = some bs)
    (hC : oC + m * p ≤ μ.store.len (H 2)) :
    Runs J W τ gemm ⟨[m, n, p, oA, oB, oC], [H 0, H 1, H 2]⟩ μ (gemmCount m n p)
      (W (Has.inj Blas1Op.dot) [n]) (GemmRounded dec (ε.dot n) m n p (H 2, oC) as bs μ) := by
  obtain ⟨μ', hrun, s', cs, rfl, hfr, hr, hE⟩ := wp_gemm hJ (τ := τ) hok hH hl hA hB hC
  refine (Runs.of_run hrun ?_ W).mono (le_of_eq (staticCost_gemm ..)) (staticPeak_gemm_le ..)
    fun _ h => h
  refine ⟨cs, by simp [Mem.updBlock, hfr.eq_updBlock hr], Store.length_of_readBlock hr,
    fun i hi j hj => ?_⟩
  have hp : 0 < p := by omega
  have hq : i * p + j < m * p := by
    have := Nat.mul_le_mul_right p hi
    rw [Nat.succ_mul] at this
    omega
  have h := hE (i * p + j) hq
  have e1 : (i * p + j) / p = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hj, zero_add]
  have e2 : (i * p + j) % p = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rwa [GemmEntry, e1, e2] at h

/-! ### The two profiles -/

variable [Has ScalarOp Op] [Apart Blas1Op ScalarOp Op] {M : Machine K} {u : ℝ}

/-- **`gemm` under sequential summation**: over scalar arithmetic meeting the standard model at
`u`, the linked program computes `C` with `|Ĉ - A B| ≤ ((1 + u) ^ n - 1) |A| |B|`
componentwise (`n ≥ 1`), within the pushed-forward counts and `n` scratch cells. One application
of the certificate of the profile. -/
theorem runs_gemm_link_seq {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u)
    {I : Interp Op Tst K} (hI : IsScalar M I) {τ : ℕ → K} {m n p oA oB oC : ℕ} (hn : 1 ≤ n)
    {H : Fin 3 → ℕ} {μ : Mem K} {as bs : List K} (hH : Function.Injective H)
    (hl : ∀ i, H i < μ.store.length) (hA : μ.store.readBlock (H 0) oA (m * n) = some as)
    (hB : μ.store.readBlock (H 1) oB (p * n) = some bs)
    (hC : oC + m * p ≤ μ.store.len (H 2)) :
    Runs I (Blas.ws 0) τ (gemm.link Blas.seq.table) ⟨[m, n, p, oA, oB, oC], [H 0, H 1, H 2]⟩ μ
      (Count.push Blas.seq.cost (gemmCount m n p)) (Blas.ws 0 (Has.inj Blas1Op.dot : Op) [n])
      (GemmRounded dec ((1 + u) ^ n - 1) m n p (H 2, oC) as bs μ) :=
  Blas.seq.err_dot u hn ▸ (Blas.seq_certifies hM hu fun _ => True).runs
    (fun _ hJ => runs_gemm_rounded hJ.2 _ trivial hH hl hA hB hC) hI

/-- **`gemm` under pairwise summation** of depth `k`, for `⌈log₂ n⌉ < k`:
`|Ĉ - A B| ≤ ((1 + u) ^ (⌈log₂ n⌉ + 1) - 1) |A| |B|` componentwise. -/
theorem runs_gemm_link_pairwise {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u)
    {I : Interp Op Tst K} (hI : IsScalar M I) {τ : ℕ → K} {k m n p oA oB oC : ℕ}
    (hk : Nat.clog 2 n < k) {H : Fin 3 → ℕ} {μ : Mem K} {as bs : List K}
    (hH : Function.Injective H) (hl : ∀ i, H i < μ.store.length)
    (hA : μ.store.readBlock (H 0) oA (m * n) = some as)
    (hB : μ.store.readBlock (H 1) oB (p * n) = some bs)
    (hC : oC + m * p ≤ μ.store.len (H 2)) :
    Runs I (Blas.ws Blas.pairWs) τ (gemm.link (Blas.pairwise k).table)
      ⟨[m, n, p, oA, oB, oC], [H 0, H 1, H 2]⟩ μ
      (Count.push (Blas.pairwise k).cost (gemmCount m n p))
      (Blas.ws Blas.pairWs (Has.inj Blas1Op.dot : Op) [n])
      (GemmRounded dec ((1 + u) ^ (Nat.clog 2 n + 1) - 1) m n p (H 2, oC) as bs μ) := by
  have h := (Blas.pairwise_certifies hM hu k).runs (τ := τ)
    (fun _ hJ => runs_gemm_rounded hJ.2 _ hk hH hl hA hB hC) hI
  rwa [Blas.pairwise_wsLo, Blas.pairwise.err_dot] at h

omit [Inhabited K] in
/-- **The scalar counts of `gemm` under sequential summation**: per entry, `n` multiplications,
`n - 1` additions, a literal and a copy. -/
theorem push_seq_gemmCount (m n p : ℕ) :
    Count.push Blas.seq.cost (gemmCount (Op := Op) (Tst := Tst) m n p) =
      (m * p) • (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) • Blas.sc .copy +
        (n - 1) • Blas.sc .add))) := by
  simp only [gemmCount, map_nsmul, Count.push_one, Blas.seq_cost_dot]

omit [Inhabited K] in
/-- **The scalar counts of `gemm` under pairwise summation**: per entry, `n` multiplications,
`n - 1` additions and `n` copies. -/
theorem push_pairwise_gemmCount (k m n p : ℕ) (hk : Nat.clog 2 n < k) :
    Count.push (Blas.pairwise k).cost (gemmCount (Op := Op) (Tst := Tst) m n p) =
      (m * p) • (n • Blas.sc .mul + Blas.pairCount n) := by
  simp only [gemmCount, map_nsmul, Count.push_one, Blas.pairwise_cost_dot k n hk]

end NLAlib.Ops.Examples
