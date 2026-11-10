/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Cgs

/-!
# Test case: classical Gram–Schmidt in finite precision

`NLAlib.Ops.Examples.cgs` computes the factorization `A ≈ Q R` of an `n × p` matrix stored by
columns, by `p` runs of `NLAlib.Ops.Examples.cgsCol`, with a scratch cell and a work vector.

## Main results

* Abstract theorem (`NLAlib.Ops.Examples.runs_cgs_rounded`): for every interpretation meeting
  the contracts of scalar arithmetic and of the level-1 operations at `ε`, the run terminates
  within `NLAlib.Ops.Examples.cgsCount n p` calls, writes only the blocks `Q` and `R`, and every
  column of the computed factors satisfies `NLAlib.Ops.Examples.CgsCol`
  (`NLAlib.Ops.Examples.CgsRounded`).
* Backward error (`NLAlib.Ops.Examples.CgsRounded.backward`, mathematics): if no diagonal entry
  of `R̂` is zero, `|A - Q̂ R̂| ≤ ((1 + ε_scal) (1 + ε_axpy) ^ j - 1) (|A| + |Q̂| |R̂|)` entry by
  entry in column `j` (the last factor without the diagonal term).
* Corollaries (`NLAlib.Ops.Examples.runs_cgs_link_seq`,
  `NLAlib.Ops.Examples.runs_cgs_link_pairwise`): the linked programs over scalar arithmetic
  meeting the standard model at `u`, where the backward error constant is
  `(1 + u) ^ (2 j + 1) - 1` for both; one application of the certificate each.

Not proved: a bound on `|Q̂| |R̂|` in terms of the columns of `A`, and the loss of
orthogonality in terms of `κ(A) u`.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]

/-- **Classical Gram–Schmidt.** Index variables: `n`, `p`, the offsets of `A`, `Q`, `R`, then the
column index; buffer variables: `A`, `Q`, `R`, the scratch cell, the work vector. -/
def cgs : Stmt Op Tst := .alloc (.const 1) (.alloc (.var 0) (.loop (.var 1) cgsCol))

/-- The buffers of a run of `cgs`: the three operands and the two scratch buffers on top of a
store of length `L`. -/
def cgsH (B : Fin 3 → ℕ) (L : ℕ) : CgsBuf → ℕ
  | .A => B 0
  | .Q => B 1
  | .R => B 2
  | .t => L
  | .v => L + 1

theorem cgsH_injective {B : Fin 3 → ℕ} (hB : Function.Injective B) {L : ℕ}
    (hl : ∀ i, B i < L) : Function.Injective (cgsH B L) := by
  have h0 := hl 0; have h1 := hl 1; have h2 := hl 2
  intro x y h
  cases x <;> cases y <;> simp [cgsH, hB.eq_iff] at h ⊢ <;> omega

variable [Inhabited K]

/-- The columns computed so far: the first `j` columns of `Q` are `qs`, and each of them, with
its column of `R`, satisfies `CgsCol`. -/
def CgsCols (dec : K → ℝ) (ε : Blas1Err) (n p bQ oQ bR oR : ℕ) (as : List K) (j : ℕ)
    (s' : Store K) : Prop :=
  ∃ (qs : List K) (rp : ℕ → List K) (ρ : ℕ → K), s'.readBlock bQ oQ (j * n) = some qs ∧
    ∀ j' < j, s'.readBlock bR (oR + j' * p) (j' + 1) = some (rp j' ++ [ρ j']) ∧
      CgsCol dec ε n j' (qs.take (j' * n)) ((as.drop (j' * n)).take n) (rp j') (ρ j')
        ((qs.drop (j' * n)).take n)

/-- **The postcondition of `cgs`**: only the blocks `Q` and `R` are written, and the computed
columns satisfy `CgsCol`. -/
def CgsRounded (dec : K → ℝ) (ε : Blas1Err) (n p bQ oQ bR oR : ℕ) (as : List K)
    (μ μ' : Mem K) : Prop :=
  μ'.pos = μ.pos ∧
    μ.store.EqOff (Store.inBlock bQ oQ (p * n) ⊔ Store.inBlock bR oR (p * p)) μ'.store ∧
    CgsCols dec ε n p bQ oQ bR oR as p μ'.store

omit [Has ScalarOp Op] [Has Blas1Op Op] in
/-- The columns computed so far, after one more column. -/
theorem CgsCols.succ {dec : K → ℝ} {ε : Blas1Err} {n p bQ oQ bR oR j : ℕ} {as : List K}
    {s' s₁ : Store K} {F : ℕ → ℕ → Prop} (h : CgsCols dec ε n p bQ oQ bR oR as j s')
    (hfj : s'.EqOff F s₁) (hj : j < p)
    (hFQ : ∀ i < j * n, ¬ F bQ (oQ + i)) (hFR : ∀ i < j * p, ¬ F bR (oR + i))
    {rpj qj : List K} {ρj : K}
    (hRj : s₁.readBlock bR (oR + j * p) (j + 1) = some (rpj ++ [ρj]))
    (hQj : s₁.readBlock bQ (oQ + j * n) n = some qj)
    (hcol : ∀ qs, s'.readBlock bQ oQ (j * n) = some qs →
      CgsCol dec ε n j qs ((as.drop (j * n)).take n) rpj ρj qj) :
    CgsCols dec ε n p bQ oQ bR oR as (j + 1) s₁ := by
  obtain ⟨qs, rp, ρ, hq, hcols⟩ := h
  have hql := Store.length_of_readBlock hq
  have hqjl := Store.length_of_readBlock hQj
  refine ⟨qs ++ qj, Function.update rp j rpj, Function.update ρ j ρj, ?_, fun j' hj' => ?_⟩
  · rw [Nat.succ_mul]
    exact Store.readBlock_add (hfj.readBlock_of hq hFQ) hQj
  obtain hlt | rfl : j' < j ∨ j' = j := by omega
  · have hjn : j' * n + n ≤ j * n := by
      have := Nat.mul_le_mul_right n hlt
      rwa [Nat.succ_mul] at this
    have hjp' : j' * p + p ≤ j * p := by
      have := Nat.mul_le_mul_right p hlt
      rwa [Nat.succ_mul] at this
    have e1 : (qs ++ qj).take (j' * n) = qs.take (j' * n) :=
      List.take_append_of_le_length (by omega)
    have e2 : ((qs ++ qj).drop (j' * n)).take n = (qs.drop (j' * n)).take n := by
      rw [List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega)]
    rw [Function.update_of_ne hlt.ne, Function.update_of_ne hlt.ne, e1, e2]
    exact ⟨hfj.readBlock_of (hcols j' hlt).1 fun i hi => by
      rw [Nat.add_assoc]; exact hFR _ (by omega), (hcols j' hlt).2⟩
  · have e3 : ((qs ++ qj).drop (j' * n)).take n = qj := by
      rw [List.drop_left' hql, List.take_of_length_le (by omega)]
    rw [Function.update_self, Function.update_self, List.take_left' hql, e3]
    exact ⟨hRj, hcol qs hq⟩

/-- **The run of `cgs`**, for every interpretation meeting the contracts. -/
theorem wp_cgs {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    {J : Interp Op Tst K} (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ x, dec (M.neg x) = -dec x) {τ : Tape K} {n p oA oQ oR : ℕ} {B : Fin 3 → ℕ}
    {μ : Mem K} {as : List K} (hok : ok n) (hB : Function.Injective B)
    (hl : ∀ i, B i < μ.store.length) (hA : μ.store.readBlock (B 0) oA (p * n) = some as)
    (hQ : oQ + p * n ≤ μ.store.len (B 1)) (hR : oR + p * p ≤ μ.store.len (B 2)) :
    Wp .total J τ cgs ⟨[n, p, oA, oQ, oR], [B 0, B 1, B 2]⟩
      (CgsRounded dec ε n p (B 1) oQ (B 2) oR as μ) μ := by
  have h0 := hl 0; have h1 := hl 1; have h2 := hl 2
  have hH := cgsH_injective hB hl
  have hS1 : (μ.store.push 1).length = μ.store.length + 1 := Store.length_push _ _
  refine wp_alloc rfl (wp_alloc rfl ?_)
  simp only [hS1]
  have hlS : ∀ b, cgsH B μ.store.length b < ((μ.store.push 1).push n).length := fun b => by
    cases b <;> simp [cgsH] <;> omega
  have hlen : ∀ i, ((μ.store.push 1).push n).len (B i) = μ.store.len (B i) := fun i => by
    rw [Store.len_push_of_lt (Store.lt_length_push (hl i) 1), Store.len_push_of_lt (hl i)]
  have hlt : ((μ.store.push 1).push n).len μ.store.length = 1 := by
    rw [Store.len_push_of_lt (by simp), Store.len_push_top]
  have hlv : ((μ.store.push 1).push n).len (μ.store.length + 1) = n := by
    rw [← hS1, Store.len_push_top]
  have hAS : ((μ.store.push 1).push n).readBlock (B 0) oA (p * n) = some as := by
    rw [Store.readBlock_push_of_lt (Store.lt_length_push h0 1), Store.readBlock_push_of_lt h0, hA]
  refine wp_loop (k := p) rfl (fun j μ' => ∃ s', μ' = ⟨s', μ.pos⟩ ∧
    ((μ.store.push 1).push n).EqOff (Store.inBlock (B 1) oQ (p * n) ⊔
      Store.inBlock (B 2) oR (p * p) ⊔ Store.inBuf μ.store.length ⊔
      Store.inBuf (μ.store.length + 1)) s' ∧ CgsCols dec ε n p (B 1) oQ (B 2) oR as j s')
    ⟨_, rfl, Store.EqOff.refl _ _, [], fun _ => [], fun _ => default, by simp, by simp⟩ ?_ ?_
  · rintro j hj μ' ⟨s', rfl, hfr, hcols⟩
    obtain ⟨qs, -, -, hq, -⟩ := id hcols
    have hjn : j * n + n ≤ p * n := by
      have := Nat.mul_le_mul_right n hj
      rwa [Nat.succ_mul] at this
    have hjp : j * p + p ≤ p * p := by
      have := Nat.mul_le_mul_right p hj
      rwa [Nat.succ_mul] at this
    have ha := hfr.readBlock_of (Store.readBlock_sub hAS hjn) (by store_side [hB.eq_iff])
    refine wp_cgsCol (H := cgsH B μ.store.length) hS hJ hneg hok hH
      (fun b => hfr.length_eq ▸ hlS b) hq ha (by rw [hfr.len_eq]; simp only [cgsH, hlen]; omega)
      (by rw [hfr.len_eq]; simp only [cgsH, hlen]; omega)
      (by rw [hfr.len_eq]; simp only [cgsH, hlt]; omega)
      (by rw [hfr.len_eq]; simp only [cgsH, hlv]; omega)
      fun s₁ rpj ρj qj hfj hRj hQj hcol => ⟨s₁, rfl, hfr.trans (hfj.mono fun b i h => ?_),
        hcols.succ hfj hj (fun i hi => ?_) (fun i hi => ?_) hRj hQj fun qs' hq' => ?_⟩
    · simp only [cgsColFp, cgsH, Pi.sup_apply, sup_Prop_eq, Store.inBlock, Store.inBuf] at h ⊢
      omega
    · simp only [cgsColFp, cgsH, Pi.sup_apply, sup_Prop_eq, Store.inBlock, Store.inBuf,
        hB.eq_iff]
      simp
      omega
    · simp only [cgsColFp, cgsH, Pi.sup_apply, sup_Prop_eq, Store.inBlock, Store.inBuf,
        hB.eq_iff]
      simp
      omega
    · obtain rfl : qs' = qs := Option.some.inj (hq'.symm.trans hq)
      exact hcol
  · rintro μ' ⟨s', rfl, hfr, hcols⟩
    have hlen' : s'.length = μ.store.length + 2 := by
      rw [hfr.length_eq, Store.length_push, Store.length_push]
    have hpop : ∀ b off k, b < μ.store.length →
        s'.pop.pop.readBlock b off k = s'.readBlock b off k := fun b off k hb => by
      rw [Store.readBlock_pop_of_lt (by rw [Store.length_pop]; omega),
        Store.readBlock_pop_of_lt (by omega)]
    obtain ⟨qs, rp, ρ, hq, hc⟩ := hcols
    refine ⟨rfl, Store.EqOff.pop (Store.EqOff.pop (hfr.mono fun b i h => ?_)),
      qs, rp, ρ, (hpop _ _ _ h1).trans hq, fun j hj => ⟨(hpop _ _ _ h2).trans (hc j hj).1,
        (hc j hj).2⟩⟩
    simpa [Store.inBuf, hS1] using h

/-! ### The abstract theorem -/

omit [Inhabited K] in
/-- The calls of column `j`: `j` times `dot`, `neg`, `axpy`, and two `copy`, one `nrm2`, one
`scal`. -/
noncomputable def cgsColCount (n j : ℕ) : Count Op Tst :=
  j • Count.one (Has.inj Blas1Op.dot) [n] + (Count.one (Has.inj Blas1Op.copy) [n] +
    (j • (Count.one (Has.inj ScalarOp.neg) [] + Count.one (Has.inj Blas1Op.axpy) [n]) +
      (Count.one (Has.inj Blas1Op.nrm2) [n] + (Count.one (Has.inj Blas1Op.scal) [n] +
        Count.one (Has.inj Blas1Op.copy) [n]))))

omit [Inhabited K] in
/-- The call counts of `cgs`: the columns, added up. -/
noncomputable def cgsCount (n p : ℕ) : Count Op Tst := ∑ j ∈ Finset.range p, cgsColCount n j

/-- The workspace of `cgs`: the scratch cell, the work vector and the workspace of the operation
that needs most. -/
def cgsPeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  1 + (n + max (W (Has.inj Blas1Op.dot) [n]) (max (W (Has.inj Blas1Op.copy) [n])
    (max (max (W (Has.inj ScalarOp.neg) []) (W (Has.inj Blas1Op.axpy) [n]))
      (max (W (Has.inj Blas1Op.nrm2) [n]) (W (Has.inj Blas1Op.scal) [n])))))

omit [Inhabited K] in
theorem staticCost_cgs (n p a b c : ℕ) :
    staticCost (cgs (Op := Op) (Tst := Tst)) [n, p, a, b, c] = cgsCount n p := by
  simp [cgs, cgsCol, cgsDots, cgsProj, staticCost, useCost, cgsCount, cgsColCount]

omit [Inhabited K] in
theorem staticPeak_cgs_le (W : Op → List ℕ → ℕ) (n p a b c : ℕ) :
    staticPeak W (cgs (Op := Op) (Tst := Tst)) [n, p, a, b, c] ≤ cgsPeak W n := by
  simp only [cgs, cgsCol, cgsDots, cgsProj, staticPeak, cgsPeak]
  refine Nat.add_le_add_left (Nat.add_le_add_left (Finset.sup_le fun j _ => ?_) _) _
  simp only [Finset.sup_le_iff, max_le_iff]
  simp

/-- **The abstract theorem of `cgs`**: for every interpretation meeting the contracts of scalar
arithmetic and of the level-1 operations at `ε`, the run terminates within `cgsCount n p` calls
and `cgsPeak W n` scratch cells, writes only `Q` and `R`, and every computed column satisfies
`CgsCol`. -/
theorem runs_cgs_rounded {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    {J : Interp Op Tst K} (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ x, dec (M.neg x) = -dec x) (W : Op → List ℕ → ℕ) {τ : Tape K}
    {n p oA oQ oR : ℕ} {B : Fin 3 → ℕ} {μ : Mem K} {as : List K} (hok : ok n)
    (hB : Function.Injective B) (hl : ∀ i, B i < μ.store.length)
    (hA : μ.store.readBlock (B 0) oA (p * n) = some as)
    (hQ : oQ + p * n ≤ μ.store.len (B 1)) (hR : oR + p * p ≤ μ.store.len (B 2)) :
    Runs J W τ cgs ⟨[n, p, oA, oQ, oR], [B 0, B 1, B 2]⟩ μ (cgsCount n p) (cgsPeak W n)
      (CgsRounded dec ε n p (B 1) oQ (B 2) oR as μ) := by
  obtain ⟨μ', hrun, hpost⟩ := wp_cgs hS hJ hneg (τ := τ) hok hB hl hA hQ hR
  exact (Runs.of_run hrun hpost W).mono (le_of_eq (staticCost_cgs ..)) (staticPeak_cgs_le ..)
    fun _ h => h

end NLAlib.Ops.Examples
