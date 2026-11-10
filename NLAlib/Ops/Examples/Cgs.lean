/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.CgsMath
public import NLAlib.Ops.Profiles.BlasCert

/-!
# Test case: classical Gram–Schmidt in finite precision, one column

`NLAlib.Ops.Examples.cgsCol` computes column `j` of the factorization `A = Q R` of an `n × p`
matrix stored by columns: the coefficients `r_ij := q_iᵀ a_j` (`cgsDots`), the work vector
`v := a_j`, the updates `v := v - r_ij q_i` (`cgsProj`), `r_jj := ‖v‖`, `v := v / r_jj`,
`q_j := v`. It calls `dot`, `copy`, `axpy`, `nrm2`, `scal` and the scalar negation.

The five buffers (`A`, `Q`, `R`, a scratch cell `t`, the work vector `v`) are an injective
family indexed by `NLAlib.Ops.Examples.CgsBuf`, so that all disjointness is one hypothesis.

## Main results

* `NLAlib.Ops.Examples.wp_cgsDots`, `NLAlib.Ops.Examples.wp_cgsProj`: the two loops.
* `NLAlib.Ops.Examples.wp_cgsCol`: the column, for every interpretation meeting the contracts:
  the store changes only in column `j` of `Q`, column `j` of `R` and the two scratch buffers,
  and the new entries are described by `NLAlib.Ops.Examples.CgsCol`.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]

/-- The buffers of classical Gram–Schmidt. -/
inductive CgsBuf where
  /-- The matrix `A`, `n × p` by columns. -/
  | A
  /-- The matrix `Q`, `n × p` by columns. -/
  | Q
  /-- The matrix `R`, `p × p` by columns. -/
  | R
  /-- A scratch cell. -/
  | t
  /-- The work vector, `n` cells. -/
  | v
  deriving DecidableEq

/-- The coefficients of column `j`: `r_ij := q_iᵀ a_j` for `i < j`. Index variables: `n`, `p`,
the offsets of `A`, `Q`, `R`, `j`, then `i`; buffer variables: `A`, `Q`, `R`, `t`, `v`. -/
def cgsDots : Stmt Op Tst :=
  .loop (.var 5) (.call (Has.inj Blas1Op.dot) [.var 0]
    [⟨1, .var 3 + .var 6 * .var 0⟩, ⟨0, .var 2 + .var 5 * .var 0⟩]
    [⟨2, .var 4 + .var 5 * .var 1 + .var 6⟩])

/-- The updates of column `j`: `t := -r_ij; v := v + t q_i` for `i < j`. -/
def cgsProj : Stmt Op Tst :=
  .loop (.var 5) (.seq
    (.call (Has.inj ScalarOp.neg) [] [⟨2, .var 4 + .var 5 * .var 1 + .var 6⟩] [⟨3, .const 0⟩])
    (.call (Has.inj Blas1Op.axpy) [.var 0]
      [⟨3, .const 0⟩, ⟨1, .var 3 + .var 6 * .var 0⟩, ⟨4, .const 0⟩] [⟨4, .const 0⟩]))

/-- **Column `j` of classical Gram–Schmidt.** -/
def cgsCol : Stmt Op Tst :=
  .seq cgsDots
    (.seq (.call (Has.inj Blas1Op.copy) [.var 0] [⟨0, .var 2 + .var 5 * .var 0⟩] [⟨4, .const 0⟩])
    (.seq cgsProj
    (.seq (.call (Has.inj Blas1Op.nrm2) [.var 0] [⟨4, .const 0⟩]
      [⟨2, .var 4 + .var 5 * .var 1 + .var 5⟩])
    (.seq (.call (Has.inj Blas1Op.scal) [.var 0]
      [⟨2, .var 4 + .var 5 * .var 1 + .var 5⟩, ⟨4, .const 0⟩] [⟨4, .const 0⟩])
    (.call (Has.inj Blas1Op.copy) [.var 0] [⟨4, .const 0⟩] [⟨1, .var 3 + .var 5 * .var 0⟩])))))

/-- The environment of a column: the sizes, the offsets, the column index, the five buffers. -/
abbrev cgsEnv (H : CgsBuf → ℕ) (n p oA oQ oR j : ℕ) : Env :=
  ⟨[n, p, oA, oQ, oR, j], [H .A, H .Q, H .R, H .t, H .v]⟩

variable [Inhabited K] {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
  {J : Interp Op Tst K} {τ : Tape K} {H : CgsBuf → ℕ} {n p oA oQ oR j : ℕ} {s : Store K}
  {pos : ℕ} {qs a : List K}

omit [Has ScalarOp Op] in
/-- **The coefficients of a column**: the block of `R` receives `j` dot products; nothing else
is written. -/
theorem wp_cgsDots (hJ : IsBlas1 dec ε ok J) (hok : ok n) (hH : Function.Injective H)
    (hl : ∀ b, H b < s.length) (hq : s.readBlock (H .Q) oQ (j * n) = some qs)
    (ha : s.readBlock (H .A) (oA + j * n) n = some a)
    (hR : oR + j * p + j ≤ s.len (H .R)) {P : Mem K → Prop}
    (hP : ∀ s₁ rp, s.EqOff (Store.inBlock (H .R) (oR + j * p) j) s₁ →
      s₁.readBlock (H .R) (oR + j * p) j = some rp →
      (∀ i < j, IsDotErr dec (ε.dot n) n (fun l => vec qs (i * n + l)) (vec a) (vec rp i)) →
      P ⟨s₁, pos⟩) :
    Wp .total J τ cgsDots (cgsEnv H n p oA oQ oR j) P ⟨s, pos⟩ := by
  refine wp_loop (k := j) rfl (fun i μ' => ∃ s₁ rp, μ' = ⟨s₁, pos⟩ ∧
    s.EqOff (Store.inBlock (H .R) (oR + j * p) i) s₁ ∧
    s₁.readBlock (H .R) (oR + j * p) i = some rp ∧
    ∀ i' < i, IsDotErr dec (ε.dot n) n (fun l => vec qs (i' * n + l)) (vec a) (vec rp i'))
    ⟨s, [], rfl, Store.EqOff.refl _ _, rfl, by simp⟩ ?_
    fun μ' ⟨s₁, rp, e, h1, h2, h3⟩ => e ▸ hP s₁ rp h1 h2 h3
  rintro i hi μ' ⟨s₁, rp, rfl, hfr, hr, hd⟩
  have hin : i * n + n ≤ j * n := by
    have := Nat.mul_le_mul_right n hi
    rwa [Nat.succ_mul] at this
  have hlen := hfr.len_eq (H .R)
  have hlive : ∀ b, H b < s₁.length := fun b => hfr.length_eq ▸ hl b
  have hrq := hfr.readBlock_of (Store.readBlock_sub hq hin) (by store_side [hH.eq_iff])
  have hra := hfr.readBlock_of ha (by store_side [hH.eq_iff])
  have hrl := Store.length_of_readBlock hr
  refine wp_call_rel_cell hJ.dot rfl rfl rfl rfl rfl ⟨hok, by simp [hH.eq_iff]⟩ ?_
    (xs := [(qs.drop (i * n)).take n, a]) ?_ ?_ fun v hv => ?_
  · store_simp
  · store_simp
  · store_simp
  refine ⟨_, rp ++ [v], rfl, (hfr.mono fun b q h => ⟨h.1, h.2.1, by have := h.2.2; omega⟩).upd
    ⟨rfl, by omega, by omega⟩ _, Store.readBlock_upd_concat hr (by omega) _, fun i' hi' => ?_⟩
  obtain hlt | heq : i' < i ∨ i' = i := by omega
  · rw [vec_append_left (hrl ▸ hlt)]
    exact hd i' hlt
  · rw [heq, ← hrl, vec_concat, hrl]
    exact IsDotErr.congr hv (fun k hk => Store.getD_drop_take qs _ _ _ hk default)
      fun _ _ => rfl

/-- **The updates of a column**: the work vector goes through the chain of updates; only the two
scratch buffers are written. -/
theorem wp_cgsProj (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ x, dec (M.neg x) = -dec x) (hok : ok n) (hH : Function.Injective H)
    (hl : ∀ b, H b < s.length) {rp w₀ : List K}
    (hq : s.readBlock (H .Q) oQ (j * n) = some qs)
    (hr : s.readBlock (H .R) (oR + j * p) j = some rp)
    (hv : s.readBlock (H .v) 0 n = some w₀) (ht : 0 < s.len (H .t)) (hvl : n ≤ s.len (H .v))
    {P : Mem K → Prop}
    (hP : ∀ s₁ w, s.EqOff (Store.inBuf (H .t) ⊔ Store.inBuf (H .v)) s₁ → w.length = n →
      s₁.readBlock (H .v) 0 n = some w →
      AxpyChain dec ε.axpy n (fun i l => vec qs (i * n + l)) (vec rp) (vec w₀) j (vec w) →
      P ⟨s₁, pos⟩) :
    Wp .total J τ cgsProj (cgsEnv H n p oA oQ oR j) P ⟨s, pos⟩ := by
  refine wp_loop (k := j) rfl (fun i μ' => ∃ s₁ w, μ' = ⟨s₁, pos⟩ ∧
    s.EqOff (Store.inBuf (H .t) ⊔ Store.inBuf (H .v)) s₁ ∧ w.length = n ∧
    s₁.readBlock (H .v) 0 n = some w ∧
    AxpyChain dec ε.axpy n (fun i l => vec qs (i * n + l)) (vec rp) (vec w₀) i (vec w))
    ⟨s, w₀, rfl, Store.EqOff.refl _ _, Store.length_of_readBlock hv, hv, .zero⟩ ?_
    fun μ' ⟨s₁, w, e, h1, h2, h3, h4⟩ => e ▸ hP s₁ w h1 h2 h3 h4
  rintro i hi μ' ⟨s₁, w, rfl, hfr, hwl, hw, hc⟩
  have hin : i * n + n ≤ j * n := by
    have := Nat.mul_le_mul_right n hi
    rwa [Nat.succ_mul] at this
  have hlt := hfr.len_eq (H .t)
  have hlv := hfr.len_eq (H .v)
  have hlive : ∀ b, H b < s₁.length := fun b => hfr.length_eq ▸ hl b
  have hrq := hfr.readBlock_of (Store.readBlock_sub hq hin) (by store_side [hH.eq_iff])
  have hgr : s₁.get (H .R) (oR + j * p + i) = some (vec rp i) :=
    (hfr.get_eq (by store_side [hH.eq_iff])).trans (Store.get_of_readBlock hr hi default)
  refine wp_seq (wp_call_un (hS .neg) rfl rfl rfl trivial hgr rfl (by store_simp) ?_)
  have hrt : (s₁.upd (H .t) 0 (M.neg (vec rp i))).readBlock (H .t) 0 1 =
      some [M.neg (vec rp i)] := Store.readBlock_one_of_get (by store_simp)
  refine wp_call_rel hJ.axpy rfl rfl rfl rfl ⟨hok, [_, _], rfl, by simp [hH.eq_iff]⟩ ?_
    (xs := [[M.neg (vec rp i)], (qs.drop (i * n)).take n, w]) ?_ ?_ fun zs hzl hzs => ?_
  · store_simp
  · store_simp [hH.eq_iff]
  · store_simp
  replace hzl : zs.length = n := hzl
  refine ⟨_, zs, rfl, (hfr.upd (Or.inl rfl) _).updBlock fun _ _ => Or.inr rfl, hzl,
    by store_simp [hH.eq_iff], hc.step (hneg _) (hzs.congr
      (fun k hk => Store.getD_drop_take qs _ _ _ hk default) (fun _ _ => rfl) fun _ _ => rfl)⟩

/-- The cells a column may write: column `j` of `R` and of `Q`, and the scratch buffers. -/
def cgsColFp (H : CgsBuf → ℕ) (n p oQ oR j : ℕ) : ℕ → ℕ → Prop :=
  Store.inBlock (H .R) (oR + j * p) (j + 1) ⊔ Store.inBlock (H .Q) (oQ + j * n) n ⊔
    Store.inBuf (H .t) ⊔ Store.inBuf (H .v)

/-- **Column `j` of classical Gram–Schmidt**, for every interpretation meeting the contracts:
from the `j` previous columns `qs` of `Q` and the column `a` of `A`, the run writes column `j` of
`R` and of `Q` (and the scratch buffers), and the new entries satisfy `CgsCol`. -/
theorem wp_cgsCol (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ x, dec (M.neg x) = -dec x) (hok : ok n) (hH : Function.Injective H)
    (hl : ∀ b, H b < s.length) (hq : s.readBlock (H .Q) oQ (j * n) = some qs)
    (ha : s.readBlock (H .A) (oA + j * n) n = some a)
    (hR : oR + j * p + j < s.len (H .R)) (hQ : oQ + j * n + n ≤ s.len (H .Q))
    (ht : 0 < s.len (H .t)) (hvl : n ≤ s.len (H .v)) {P : Mem K → Prop}
    (hP : ∀ s₁ rp ρ qj, s.EqOff (cgsColFp H n p oQ oR j) s₁ →
      s₁.readBlock (H .R) (oR + j * p) (j + 1) = some (rp ++ [ρ]) →
      s₁.readBlock (H .Q) (oQ + j * n) n = some qj → CgsCol dec ε n j qs a rp ρ qj →
      P ⟨s₁, pos⟩) :
    Wp .total J τ cgsCol (cgsEnv H n p oA oQ oR j) P ⟨s, pos⟩ := by
  have hal := Store.length_of_readBlock ha
  refine wp_seq (wp_cgsDots hJ hok hH hl hq ha (by omega) fun s₁ rp hf1 hr1 hd => ?_)
  have hl1 : ∀ b, H b < s₁.length := fun b => hf1.length_eq ▸ hl b
  have hlen1 := fun b => hf1.len_eq b
  have hq1 := hf1.readBlock_of hq (by store_side [hH.eq_iff])
  have ha1 := hf1.readBlock_of ha (by store_side [hH.eq_iff])
  -- the work vector
  refine wp_seq (wp_call_rel hJ.copy rfl rfl rfl rfl ⟨hok, by simp [hH.eq_iff]⟩ ?_ (xs := [a])
    ?_ ?_ fun ys hyl hys => ?_)
  · store_simp
  · store_simp
  · store_simp [hlen1]
  obtain rfl : a = ys := by simpa [copyRel] using hys
  -- the updates
  refine wp_seq (wp_cgsProj hS hJ hneg hok hH (by store_simp) (qs := qs) (rp := rp) (w₀ := a)
    (by store_simp [hH.eq_iff]) (by store_simp [hH.eq_iff]) (by store_simp [hlen1])
    (by store_simp [hlen1]) (by store_simp [hlen1]) fun s₃ w hf3 hwl hw hc => ?_)
  have hl3 : ∀ b, H b < s₃.length := fun b => by rw [hf3.length_eq]; store_simp
  have hlen3 : ∀ b, s₃.len b = s.len b := fun b => by rw [hf3.len_eq]; store_simp [hlen1]
  have hr3 : s₃.readBlock (H .R) (oR + j * p) j = some rp :=
    hf3.readBlock_of (by store_simp [hH.eq_iff]) (by store_side [hH.eq_iff])
  -- the norm
  refine wp_seq (wp_call_rel_cell hJ.nrm2 rfl rfl rfl rfl rfl ⟨hok, by simp [hH.eq_iff]⟩ ?_
    (xs := [w]) ?_ ?_ fun ρ hρ => ?_)
  · store_simp
  · store_simp
  · store_simp [hlen3]
  -- the scaling
  have hgρ : ((s₃.upd (H .R) (oR + j * p + j) ρ).readBlock (H .R) (oR + j * p + j) 1) =
      some [ρ] := Store.readBlock_one_of_get (by store_simp [hlen3])
  refine wp_seq (wp_call_rel hJ.scal rfl rfl rfl rfl ⟨hok, [_], rfl, by simp [hH.eq_iff]⟩ ?_
    (xs := [[ρ], w]) ?_ ?_ fun zs hzl hzs => ?_)
  · store_simp
  · store_simp [hH.eq_iff]
  · store_simp [hlen3]
  replace hzl : zs.length = n := hzl
  -- the column of `Q`
  refine wp_call_rel hJ.copy rfl rfl rfl rfl ⟨hok, by simp [hH.eq_iff]⟩ ?_ (xs := [zs]) ?_ ?_
    fun ys hyl hys => ?_
  · store_simp
  · store_simp [hlen3]
  · store_simp [hlen3]
  obtain rfl : zs = ys := by simpa [copyRel] using hys
  refine hP _ rp ρ zs ?_ ?_ (by store_simp [hlen3]) ⟨hd, w, hc, hρ, hzs⟩
  · refine ((((hf1.mono fun b i h => ?_).updBlock fun _ _ => Or.inr rfl).trans
      (hf3.mono fun b i h => ?_)).upd (Or.inl (Or.inl (Or.inl ⟨rfl, by omega, by omega⟩)))
      _).updBlock (fun _ _ => Or.inr rfl) |>.updBlock
      fun i hi => Or.inl (Or.inl (Or.inr ⟨rfl, by omega, by omega⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨h.1, h.2.1, by have := h.2.2; omega⟩))
    · exact h.elim (fun h => Or.inl (Or.inr h)) Or.inr
  · store_simp [hH.eq_iff]
    exact Store.readBlock_upd_concat hr3 (by rw [hlen3]; omega) _

end NLAlib.Ops.Examples
