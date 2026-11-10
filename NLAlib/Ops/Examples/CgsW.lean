/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Examples.CgsQR

/-!
# Test case: classical Gram–Schmidt in the logic layer

The certificate of `NLAlib.Ops.Examples.cgs` against `cgsRel`, proved with block
specifications: two allocations, the loop over the columns in the standard invariant form, and
in each column a relational fill (the coefficients), a loop of updates and three steps.

## Main results

* `NLAlib.Ops.Examples.cgs_spec_w`: the certificate (the statement of `cgs_spec`).
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Inhabited K]

/-- **Column `j` of `cgs`** as one block specification, from facts at its first memory: the
coefficients (a relational fill of column `j` of `R`), the work vector, the updates (a loop), the
norm, the scaling and the copy into column `j` of `Q`. -/
theorem cgsCol_w {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    {J : Interp Op Tst K} (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ x, dec (M.neg x) = -dec x) {τ : Tape K} {n p j L : ℕ} {A Q R : ℕ × ℕ}
    {m₁ : Mem K} {qs a : List K} (hok : ok n) (_hAQ : A.1 ≠ Q.1) (hAR : A.1 ≠ R.1)
    (hQR : Q.1 ≠ R.1) (hL : A.1 < L ∧ R.1 < L ∧ Q.1 < L) (hlen : m₁.store.length = L + 2)
    (hqs : m₁.store.readBlock Q.1 Q.2 (j * n) = some qs)
    (ha : m₁.store.readBlock A.1 (A.2 + j * n) n = some a)
    (hRz : R.2 + j * p + j < m₁.store.len R.1) (hQz : Q.2 + j * n + n ≤ m₁.store.len Q.1)
    (ht : m₁.store.len L = 1) (hv : m₁.store.len (L + 1) = n) :
    Writes .total J τ cgsCol
      ((((Env.frame [n, p] ([A, R] ++ [Q, R])).pushBuf L).pushBuf (L + 1)).pushIdx j)
      (Store.inBlock R.1 (R.2 + j * p) (j + 1) ⊔ Store.inBlock Q.1 (Q.2 + j * n) n ⊔
        Store.inBuf L ⊔ Store.inBuf (L + 1))
      (fun m' => m'.pos = m₁.pos ∧ ∃ rp ρ qj,
        m'.store.readBlock R.1 (R.2 + j * p) (j + 1) = some (rp ++ [ρ]) ∧
        m'.store.readBlock Q.1 (Q.2 + j * n) n = some qj ∧ CgsCol dec ε n j qs a rp ρ qj) m₁ := by
  -- the coefficients `r_ij := q_iᵀ a_j`, `i < j`
  refine Writes.seq_le (writes_fillRel (b := R.1) (o := R.2 + j * p) rfl (fun i x =>
      IsDotErr dec (ε.dot n) n (fun l => vec qs (i * n + l)) (vec a) x) (fun _ => m₁.pos) rfl
      fun i hi m₃ hfr₃ _ hpos₃ => ?_) (by fp_sub) fun m₃ hfr₃ ⟨⟨v, hvH, hvR⟩, hpos₃⟩ => ?_
  · step hJ.dot as m₄ hfr₄ ⟨hpos₄, x, hx, hrel⟩
    exact ⟨⟨x, hx, hrel.congr (fun l hl => vec_drop_take hl) fun _ _ => rfl⟩,
      by simp [hpos₄, hpos₃]⟩
  -- the work vector `v := a_j`
  step hJ.copy as m₄ hfr₄ ⟨hpos₄, w₀, hw₀, hwa⟩
  subst w₀
  -- the updates `v := v - r_ij q_i`, `i < j`
  have hrp := Store.holdsVec_iff_readBlock.mp hvH
  refine Writes.seq_le (writes_loop rfl (fun _ => Store.inBuf L ⊔ Store.inBuf (L + 1))
      (fun _ _ => le_rfl)
      (fun i m' => m'.pos = m₁.pos ∧ ∃ w, m'.store.readBlock (L + 1) 0 n = some w ∧
        AxpyChain dec ε.axpy n (fun i l => vec qs (i * n + l)) (vec ((List.range j).map v))
          (vec a) i (vec w))
      ⟨by simp [hpos₄, hpos₃], _, hw₀, .zero⟩ fun i hi m₅ hfr₅ ⟨hpos₅, w, hw, hc⟩ => ?_)
    (by fp_sub) fun m₅ hfr₅ ⟨hpos₅, w, hw, hc⟩ => ?_
  · have hvi := hvH i hi
    step (hS .neg) as m₆ hfr₆ ⟨hpos₆, t, ht, htrel⟩
    step hJ.axpy as m₇ hfr₇ ⟨hpos₇, zs, hzs, hzrel⟩
    exact ⟨by simp [hpos₇, hpos₆, hpos₅], zs, hzs, hc.step
      (by rw [← htrel]; simpa only [vec_map_range v hi] using hneg (v i))
      (hzrel.congr (fun l hl => vec_drop_take hl) (fun _ _ => rfl) fun _ _ => rfl)⟩
  -- the norm, the scaling, the copy into `Q`
  step hJ.nrm2 as m₆ hfr₆ ⟨hpos₆, ρ, hρ, hρrel⟩
  step hJ.scal as m₇ hfr₇ ⟨hpos₇, zs, hzs, hzrel⟩
  step hJ.copy as m₈ hfr₈ ⟨hpos₈, qj, hqj, hqz⟩
  subst qj
  exact ⟨by simp [hpos₈, hpos₇, hpos₆, hpos₅], _, ρ, zs,
    Store.readBlock_succ_of (by kept) (by kept), hqj,
    ⟨fun i hi => by simpa only [vec_map_range v hi] using hvR i hi, w, hc, hρrel, hzrel⟩⟩

/-- **The certificate of `cgs`**, by block specifications. -/
theorem cgs_spec_w {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
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
      exact cgsCol_w hS hJ hneg hok hAQ hAR hQR ⟨hl.1, hl.2.1, hl.2.2.1⟩ (by room) hqs (by kept)
        (by room) (by room) (by room) (by room)
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

end NLAlib.Ops.Examples
