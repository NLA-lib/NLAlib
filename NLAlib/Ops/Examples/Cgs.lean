/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.CgsMath
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Profiles.BlasCert

/-!
# Test case: classical Gram–Schmidt in finite precision, one column

`NLAlib.Ops.Examples.cgsCol` computes column `j` of the factorization `A = Q R` of an `n × p`
matrix stored by columns: the coefficients `r_ij := q_iᵀ a_j` (`cgsDots`), the work vector
`v := a_j`, the updates `v := v - r_ij q_i` (`cgsProj`), `r_jj := ‖v‖`, `v := v / r_jj`,
`q_j := v`. It calls `dot`, `copy`, `axpy`, `nrm2`, `scal` and the scalar negation.

## Main results

* `NLAlib.Ops.Examples.cgsCol_writes`: the column as one block specification, for every
  interpretation meeting the contracts: the store changes only in column `j` of `R` (up to the
  diagonal), column `j` of `Q` and the two scratch buffers, and the new entries are described by
  `NLAlib.Ops.Examples.CgsCol`. Proved in the program logic (`NLAlib.Ops.Logic`): a relational
  fill (the coefficients), a loop of updates and three steps.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]

/-- The coefficients of column `j`: `r_ij := q_iᵀ a_j` for `i < j`. Index variables: `n`, `p`,
the offsets of `A`, `R`, `Q`, `R`, `j`, then `i`; buffer variables: `A`, `R`, `Q`, `R`, `t`,
`v` (the inputs `A`, `R` and the outputs `Q`, `R`: `R` is updated in place). -/
def cgsDots : Stmt Op Tst :=
  .loop (.var 6) (.call (Has.inj Blas1Op.dot) [.var 0]
    [⟨2, .var 4 + .var 7 * .var 0⟩, ⟨0, .var 2 + .var 6 * .var 0⟩]
    [⟨3, .var 5 + .var 6 * .var 1 + .var 7⟩])

/-- The updates of column `j`: `t := -r_ij; v := v + t q_i` for `i < j`. -/
def cgsProj : Stmt Op Tst :=
  .loop (.var 6) (.seq
    (.call (Has.inj ScalarOp.neg) [] [⟨3, .var 5 + .var 6 * .var 1 + .var 7⟩] [⟨4, .const 0⟩])
    (.call (Has.inj Blas1Op.axpy) [.var 0]
      [⟨4, .const 0⟩, ⟨2, .var 4 + .var 7 * .var 0⟩, ⟨5, .const 0⟩] [⟨5, .const 0⟩]))

/-- **Column `j` of classical Gram–Schmidt.** -/
def cgsCol : Stmt Op Tst :=
  .seq cgsDots
    (.seq (.call (Has.inj Blas1Op.copy) [.var 0] [⟨0, .var 2 + .var 6 * .var 0⟩] [⟨5, .const 0⟩])
    (.seq cgsProj
    (.seq (.call (Has.inj Blas1Op.nrm2) [.var 0] [⟨5, .const 0⟩]
      [⟨3, .var 5 + .var 6 * .var 1 + .var 6⟩])
    (.seq (.call (Has.inj Blas1Op.scal) [.var 0]
      [⟨3, .var 5 + .var 6 * .var 1 + .var 6⟩, ⟨5, .const 0⟩] [⟨5, .const 0⟩])
    (.call (Has.inj Blas1Op.copy) [.var 0] [⟨5, .const 0⟩] [⟨2, .var 4 + .var 6 * .var 0⟩])))))

variable [Inhabited K]

/-- **Column `j` of `cgs`** as one block specification, from facts at its first memory: the
coefficients (a relational fill of column `j` of `R`), the work vector, the updates (a loop), the
norm, the scaling and the copy into column `j` of `Q`. -/
theorem cgsCol_writes {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
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

end NLAlib.Ops.Examples
