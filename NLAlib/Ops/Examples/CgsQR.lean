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

* The certificate (`NLAlib.Ops.Examples.cgs_spec`): for every interpretation meeting the
  contracts of scalar arithmetic and of the level-1 operations at `ε`, `cgs` meets its contract
  in operand form (`NLAlib.Ops.Examples.cgsRel`); proved in the program logic
  (`NLAlib.Ops.Logic`) from the column `NLAlib.Ops.Examples.cgsCol_writes`.
* Abstract theorem (`NLAlib.Ops.Examples.runs_cgs_rounded`): for every interpretation meeting
  the contracts of scalar arithmetic and of the level-1 operations at `ε`, the run terminates
  within `NLAlib.Ops.Examples.cgsCount n p` calls, writes only the blocks `Q` and `R`, and every
  column of the computed factors satisfies `NLAlib.Ops.Examples.CgsCol`
  (`NLAlib.Ops.Examples.CgsFactored`).
* Backward error (`NLAlib.Ops.Examples.CgsOut.backward`, mathematics): if no diagonal entry
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

/-- **Classical Gram–Schmidt.** Two inputs `A`, `R` and two outputs `Q`, `R`: the upper triangle
of `R` is written, the rest of `R` is kept. Index variables: `n`, `p`, the offsets of `A`, `R`,
`Q`, `R`, then the column index; buffer variables: `A`, `R`, `Q`, `R`, the scratch cell, the
work vector. -/
def cgs : Stmt Op Tst := .alloc (.const 1) (.alloc (.var 0) (.loop (.var 1) cgsCol))

/-- **`cgs` as an implementation**: two dimensions `n`, `p`, two inputs `A`, `R`, two outputs
`Q`, `R`. -/
def cgsImpl : Impl Op Tst := ⟨2, 2, 2, cgs⟩

variable [Inhabited K]

/-- The columns computed so far: the first `j` columns of `Q` are `qs`, and each of them, with
its column of `R`, satisfies `CgsCol`. -/
def CgsCols (dec : K → ℝ) (ε : Blas1Err) (n p bQ oQ bR oR : ℕ) (as : List K) (j : ℕ)
    (s' : Store K) : Prop :=
  ∃ (qs : List K) (rp : ℕ → List K) (ρ : ℕ → K), s'.readBlock bQ oQ (j * n) = some qs ∧
    ∀ j' < j, s'.readBlock bR (oR + j' * p) (j' + 1) = some (rp j' ++ [ρ j']) ∧
      CgsCol dec ε n j' (qs.take (j' * n)) ((as.drop (j' * n)).take n) (rp j') (ρ j')
        ((qs.drop (j' * n)).take n)

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

/-! ### The counts -/

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
theorem staticCost_cgs (n p a b c c' : ℕ) :
    staticCost (cgs (Op := Op) (Tst := Tst)) [n, p, a, c, b, c'] = cgsCount n p := by
  simp [cgs, cgsCol, cgsDots, cgsProj, staticCost, useCost, cgsCount, cgsColCount]

omit [Inhabited K] in
theorem staticPeak_cgs_le (W : Op → List ℕ → ℕ) (n p a b c c' : ℕ) :
    staticPeak W (cgs (Op := Op) (Tst := Tst)) [n, p, a, c, b, c'] ≤ cgsPeak W n := by
  simp only [cgs, cgsCol, cgsDots, cgsProj, staticPeak, cgsPeak]
  refine Nat.add_le_add_left (Nat.add_le_add_left (Finset.sup_le fun j _ => ?_) _) _
  simp only [Finset.sup_le_iff, max_le_iff]
  simp

/-! ### The certificate and the abstract theorem -/

/-- **The outputs of `cgs`**: the block `qs` of `Q̂` by columns and the block `rs` of `R̂` by
columns; in every column the entries of `R̂` up to the diagonal and the column of `Q̂` satisfy
`CgsCol`. Nothing is said of the entries of `rs` below the diagonal. -/
def CgsOut (dec : K → ℝ) (ε : Blas1Err) (n p : ℕ) (as qs rs : List K) : Prop :=
  ∃ (rp : ℕ → List K) (ρ : ℕ → K), ∀ j < p,
    (rs.drop (j * p)).take (j + 1) = rp j ++ [ρ j] ∧
    CgsCol dec ε n j (qs.take (j * n)) ((as.drop (j * n)).take n) (rp j) (ρ j)
      ((qs.drop (j * n)).take n)

/-- **The contract of `cgs`**, in operand form, with two output blocks: at the dimensions
`[n, p]`, from the blocks `A` (`p n` cells) and `R` (`p p` cells, updated in place) to the blocks
`Q` and `R`. -/
@[simps (attr := storeNF)]
def cgsRel (dec : K → ℝ) (ε : Blas1Err) : BlockRel K where
  nd := 2
  inLens d := match d with
    | [n, p] => [p * n, p * p]
    | _ => []
  outLens d := match d with
    | [n, p] => [p * n, p * p]
    | _ => []
  rel d X _ Y := match d, X, Y with
    | [n, p], [as, _], [qs, rs] => CgsOut dec ε n p as qs rs
    | _, _, _ => False

/-- The admitted operands of `cgs`: the length `n` is covered, `R` is updated in place, and
`A`, `Q`, `R` are in three buffers. -/
@[admNF] def CgsOperands (ok : ℕ → Prop) : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => ok (d.headD 0) ∧ ∃ A Q R, ins = [A, R] ∧ outs = [Q, R] ∧
    A.1 ≠ Q.1 ∧ A.1 ≠ R.1 ∧ Q.1 ≠ R.1

/-- **The postcondition of `cgs`**: the blocks `Q` and `R` hold `qs` and `rs`, nothing else is
written, and the computed columns satisfy `CgsCol`. -/
def CgsFactored (dec : K → ℝ) (ε : Blas1Err) (n p : ℕ) (Q R : ℕ × ℕ) (as : List K)
    (μ μ' : Mem K) : Prop :=
  ∃ qs rs : List K, qs.length = p * n ∧ rs.length = p * p ∧ CgsOut dec ε n p as qs rs ∧
    μ' = (μ.updBlock Q qs).updBlock R rs

/-- **The certificate of `cgs`**: for every interpretation meeting the contracts of scalar
arithmetic and of the level-1 operations at `ε`, `cgs` meets its contract, which has two output
blocks. Proved by block specifications: two allocations, the loop over the columns in the
standard invariant form, and `cgsCol_writes` in each column. -/
theorem cgs_spec {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    {J : Interp Op Tst K} (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ x, dec (M.neg x) = -dec x) :
    (cgsImpl (Op := Op) (Tst := Tst)).Meets J .total ((cgsRel dec ε).spec (CgsOperands ok)) := by
  cert_intro [n, p] (A, R₀) → (Q, R) reads (as, r₀)
  obtain ⟨hok, rfl, hAQ, hAR, hQR⟩ := hadm
  refine writes_alloc rfl fun s₁ hs₁ ht hB₁ => writes_alloc rfl fun s₂ hs₂ hv hB₂ => ?_
  simp only [hs₁] at hs₂ hv hB₂ ⊢
  refine Writes.mono (writes_loop rfl (fun j => Store.inBlock Q.1 Q.2 (j * n) ⊔
      Store.inBlock R.1 R.2 (j * p) ⊔ Store.inBuf μ.store.length ⊔
      Store.inBuf (μ.store.length + 1)) (fun j hj => by fp_sub)
    (fun j m' => m'.pos = μ.pos ∧ CgsCols dec ε n p Q.1 Q.2 R.1 R.2 as j m'.store ∧
      (m'.store.readBlock R.1 R.2 (p * p)).isSome)
    ⟨rfl, ⟨[], fun _ => [], fun _ => default, by simp, by simp⟩, by
      rw [Store.Below.readBlock_of (hB₁.trans (hB₂.mono (by omega))) hl.2.1 (o := R.2)
        (n := p * p) hr₀]; rfl⟩
    fun j hj m₁ hfr ⟨hpos, hcols, hRs⟩ => ?_) (by fp_sub) fun m' _ ⟨hpos, hcols, hRs⟩ => ?_
  · obtain ⟨qs, -, -, hqs, -⟩ := id hcols
    refine Writes.mono (F := Store.inBlock R.1 (R.2 + j * p) (j + 1) ⊔
        Store.inBlock Q.1 (Q.2 + j * n) n ⊔ Store.inBuf μ.store.length ⊔
        Store.inBuf (μ.store.length + 1))
      (P := fun m' => m'.pos = m₁.pos ∧ ∃ rp ρ qj,
        m'.store.readBlock R.1 (R.2 + j * p) (j + 1) = some (rp ++ [ρ]) ∧
        m'.store.readBlock Q.1 (Q.2 + j * n) n = some qj ∧
        CgsCol dec ε n j qs ((as.drop (j * n)).take n) rp ρ qj) ?_ (by fp_sub)
      fun m₂ hfr₂ ⟨hpos₂, rp, ρ, qj, hRj, hQj, hcol⟩ => ⟨hpos₂.trans hpos,
        hcols.succ hfr₂ hj (fun i hi => by disjoint) (fun i hi => by disjoint) hRj hQj
          fun qs' hq' => Option.some.inj (hq'.symm.trans hqs) ▸ hcol, ?_⟩
    · frame_facts
      exact cgsCol_writes hS hJ hneg hok hAQ hAR hQR ⟨hl.1, hl.2.1, hl.2.2.1⟩ (by room) hqs
        (by kept) (by room) (by room) (by room) (by room)
    · refine hfr₂.isSome_readBlock hRs fun i hi hG => ?_
      have hi' : R.2 + j * p ≤ R.2 + i ∧ R.2 + i < R.2 + j * p + (j + 1) := by
        simp only [fpNF] at hG; omega
      have := Store.get_of_readBlock hRj (j := i - j * p) (by omega) default
      rw [show R.2 + j * p + (i - j * p) = R.2 + i by omega] at this
      simp [this]
  · intro s₃ _ hB₃ s₄ _ hB₄
    obtain ⟨qs, rp, ρ, hq, hc⟩ := hcols
    obtain ⟨rs, hrs⟩ := Option.isSome_iff_exists.mp hRs
    have hB := (hB₃.mono (by omega)).trans hB₄
    refine ⟨by simp [hpos], [qs, rs], Mem.readBlocks_of_cons (hB.readBlock_of hl.2.2.1 hq)
      (Mem.readBlocks_of_cons (hB.readBlock_of hl.2.1 hrs) rfl), rp, ρ,
      fun j hj => ⟨Option.some.inj ((Store.readBlock_sub hrs
        (show j * p + (j + 1) ≤ p * p by idx)).symm.trans
        (hc j hj).1), (hc j hj).2⟩⟩

/-- **The abstract theorem of `cgs`**, from its certificate by the bridge: for every
interpretation meeting the contracts of scalar arithmetic and of the level-1 operations at `ε`,
the run terminates within `cgsCount n p` calls and `cgsPeak W n` scratch cells, writes only `Q`
and `R`, and every computed column satisfies `CgsCol`. The block `R` is an input too: it is
readable, and only its upper triangle is specified. -/
theorem runs_cgs_rounded {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    {J : Interp Op Tst K} (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ x, dec (M.neg x) = -dec x) (W : Op → List ℕ → ℕ) {τ : Tape K}
    {n p : ℕ} {A Q R : ℕ × ℕ} {μ : Mem K} {as r₀ : List K} (hok : ok n) (hAQ : A.1 ≠ Q.1)
    (hAR : A.1 ≠ R.1) (hQR : Q.1 ≠ R.1) (hl : μ.Live [A, Q, R])
    (hA : μ.store.readBlock A.1 A.2 (p * n) = some as)
    (hR₀ : μ.store.readBlock R.1 R.2 (p * p) = some r₀)
    (hQ : Q.2 + p * n ≤ μ.store.len Q.1) (hR : R.2 + p * p ≤ μ.store.len R.1) :
    Runs J W τ cgs (Env.frame [n, p] [A, R, Q, R]) μ (cgsCount n p) (cgsPeak W n)
      (CgsFactored dec ε n p Q R as μ) := by
  obtain ⟨hlA, hlQ, hlR⟩ : A.1 < μ.store.length ∧ Q.1 < μ.store.length ∧
      R.1 < μ.store.length := by simpa using hl
  refine ((cgs_spec hS hJ hneg).runs_rel W (d := [n, p]) (ins := [A, R]) (outs := [Q, R])
    (τ := τ) (xs := [as, r₀]) rfl ⟨hok, A, Q, R, rfl, rfl, hAQ, hAR, hQR⟩
    (by simp [hlA, hlQ, hlR]) (by simp [Mem.readBlocks, hA, hR₀]) trivial
    ⟨hQ, hR, trivial⟩).mono (le_of_eq (staticCost_cgs ..)) (staticPeak_cgs_le ..) ?_
  rintro μ' ⟨ys, hlen, hb, rfl⟩
  obtain ⟨qs, rs, rfl, h1, h2⟩ := map_length_eq_two hlen
  exact ⟨qs, rs, h1, h2, hb, rfl⟩

end NLAlib.Ops.Examples
