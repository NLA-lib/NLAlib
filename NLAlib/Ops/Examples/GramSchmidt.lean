/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.BlasCert

/-!
# Example: modified Gram–Schmidt over the level-1 operations

The algorithm `NLAlib.Ops.Examples.mgs` orthogonalizes a vector `w` against the `k` rows of `Q`
and stores the `k` coefficients and the norm of the result in `R`. This is the example of the
first build, proved again with the rules on given operands, `store_simp` and frames.

## Main results

* Mathematics: the postcondition is the recurrence with local errors
  `NLAlib.Ops.Examples.MgsRec`, on decoded values; its analysis is not part of this file.
* Program logic (`NLAlib.Ops.Examples.wp_mgs`): for every interpretation meeting the contracts,
  the run ends in a memory described by the recurrence.
* The abstract theorem (`NLAlib.Ops.Examples.runs_mgs_rounded`): the same with the call counts
  `k (dot + neg + axpy) + nrm2`, by evaluating the static cost.
* The corollary (`NLAlib.Ops.Examples.runs_mgs_link_seq`): the program linked through the
  profile of sequential summation, down to scalar arithmetic meeting the standard model at `u`,
  by one application of the certificate; its scalar counts are
  `NLAlib.Ops.Examples.push_seq_mgsCount`.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]

/-! ### Mathematics: the recurrence with local errors -/

/-- **The modified Gram–Schmidt recurrence with local errors**: after `j` steps from `w₀`, the
vector is `w` and the coefficients are `r`; each step computes a coefficient `ρ` as a dot product
up to `εd` and updates `w` by `w - ρ q_j` up to `εa`. -/
inductive MgsRec (dec : K → ℝ) (εd εa : ℝ) (n : ℕ) (q : ℕ → ℕ → K) (w₀ : ℕ → K) :
    ℕ → (ℕ → K) → List K → Prop
  /-- No step. -/
  | zero : MgsRec dec εd εa n q w₀ 0 w₀ []
  /-- One more step. -/
  | step {j : ℕ} {w w' : ℕ → K} {r : List K} {ρ t : K} : MgsRec dec εd εa n q w₀ j w r →
      IsDotErr dec εd n (q j) w ρ → dec t = -dec ρ → IsAxpyErr dec εa n t (q j) w w' →
      MgsRec dec εd εa n q w₀ (j + 1) w' (r ++ [ρ])

/-! ### The algorithm -/

/-- One step: `R_j := dot Q_j w; t := neg R_j; w := w + t Q_j`. -/
def mgsBody : Stmt Op Tst :=
  .seq (.call (Has.inj Blas1Op.dot) [.var 0] [⟨0, .var 2 + .var 5 * .var 0⟩, ⟨1, .var 3⟩]
      [⟨2, .var 4 + .var 5⟩])
    (.seq (.call (Has.inj ScalarOp.neg) [] [⟨2, .var 4 + .var 5⟩] [⟨3, .const 0⟩])
      (.call (Has.inj Blas1Op.axpy) [.var 0]
        [⟨3, .const 0⟩, ⟨0, .var 2 + .var 5 * .var 0⟩, ⟨1, .var 3⟩] [⟨1, .var 3⟩]))

/-- **Modified Gram–Schmidt.** Index variables: `n`, `k`, the offsets of `Q`, `w`, `R`, then the
loop variable; buffer variables: `Q`, `w`, `R`, then the scratch cell. -/
def mgs : Stmt Op Tst :=
  .alloc (.const 1) (.seq (.loop (.var 1) mgsBody)
    (.call (Has.inj Blas1Op.nrm2) [.var 0] [⟨1, .var 3⟩] [⟨2, .var 4 + .var 1⟩]))

/-! ### Program logic -/

variable [Inhabited K]

/-- The postcondition of `mgs`: `w` holds `ws'` and `R` holds the coefficients and the norm,
related to the inputs by the recurrence with local errors; nothing else is written. -/
def MgsRounded (dec : K → ℝ) (ε : Blas1Err) (n k bw ow bR oR : ℕ) (qs ws : List K)
    (μ μ' : Mem K) : Prop :=
  ∃ (ws' r : List K) (ν : K), ws'.length = n ∧
    MgsRec dec (ε.dot n) ε.axpy n (fun j i => vec qs (j * n + i)) (vec ws) k (vec ws') r ∧
    IsNrm2Err dec (ε.dot n) ε.sqrt n (vec ws') ν ∧ μ'.pos = μ.pos ∧
    μ.store.EqOff (Store.inBlock bw ow n ⊔ Store.inBlock bR oR (k + 1)) μ'.store ∧
    μ'.store.readBlock bw ow n = some ws' ∧ μ'.store.readBlock bR oR (k + 1) = some (r ++ [ν])

/-- The invariant of the loop of `mgs` after `j` steps, on the store with the scratch cell. -/
def MgsInv (dec : K → ℝ) (ε : Blas1Err) (n bw ow bR oR : ℕ) (qs ws : List K) (μ : Mem K)
    (j : ℕ) (μ' : Mem K) : Prop :=
  ∃ (s' : Store K) (ws' r : List K), μ' = ⟨s', μ.pos⟩ ∧ ws'.length = n ∧
    (μ.store.push 1).EqOff
      (Store.inBlock bw ow n ⊔ Store.inBlock bR oR j ⊔ Store.inBuf μ.store.length) s' ∧
    s'.readBlock bw ow n = some ws' ∧ s'.readBlock bR oR j = some r ∧
    MgsRec dec (ε.dot n) ε.axpy n (fun j i => vec qs (j * n + i)) (vec ws) j (vec ws') r

/-- **One step of the loop**, by the contracts of `dot`, `neg` and `axpy`. -/
theorem wp_mgs_step {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    {J : Interp Op Tst K} (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ a, dec (M.neg a) = -dec a) {τ : Tape K} {n k oQ ow oR j : ℕ} {H : Fin 3 → ℕ}
    {μ μ₁ : Mem K} {qs ws : List K} (hok : ok n) (hH : Function.Injective H)
    (hl : ∀ i, H i < μ.store.length) (hj : j < k)
    (hq : μ.store.readBlock (H 0) oQ (k * n) = some qs)
    (hwl : ow + n ≤ μ.store.len (H 1)) (hR : oR + (k + 1) ≤ μ.store.len (H 2))
    (hinv : MgsInv dec ε n (H 1) ow (H 2) oR qs ws μ j μ₁) :
    Wp .total J τ mgsBody ⟨[n, k, oQ, ow, oR, j], [H 0, H 1, H 2, μ.store.length]⟩
      (MgsInv dec ε n (H 1) ow (H 2) oR qs ws μ (j + 1)) μ₁ := by
  obtain ⟨s', ws', r, rfl, hws, hfr, hw, hr, hrec⟩ := hinv
  have h0 := hl 0; have h1 := hl 1; have h2 := hl 2
  have hjn : j * n + n ≤ k * n := by
    have := Nat.mul_le_mul_right n hj
    rwa [Nat.succ_mul] at this
  have hlen : s'.length = μ.store.length + 1 := by rw [hfr.length_eq, Store.length_push]
  have hlR : s'.len (H 2) = μ.store.len (H 2) := by rw [hfr.len_eq, Store.len_push_of_lt h2]
  have hlt : s'.len μ.store.length = 1 := by rw [hfr.len_eq, Store.len_push_top]
  have hlw : s'.len (H 1) = μ.store.len (H 1) := by rw [hfr.len_eq, Store.len_push_of_lt h1]
  have hrow := hfr.readBlock_of (by store_simp [Store.readBlock_sub hq hjn] :
    (μ.store.push 1).readBlock (H 0) (oQ + j * n) n = some ((qs.drop (j * n)).take n))
    (by store_side [hH.eq_iff])
  have hrowv : ∀ i < n, vec ((qs.drop (j * n)).take n) i = vec qs (j * n + i) :=
    fun i hi => Store.getD_drop_take qs _ _ _ hi default
  -- the coefficient
  refine wp_seq (wp_call_rel_cell hJ.dot rfl rfl rfl rfl rfl ⟨hok, by simp [hH.eq_iff]⟩ ?_
    (xs := [(qs.drop (j * n)).take n, ws']) ?_ ?_ fun ρ hρ => ?_)
  · store_simp
  · store_simp
  · store_simp
  -- its negation, in the scratch cell
  refine wp_seq (wp_call_un (hS .neg) rfl rfl rfl trivial (a := ρ) ?_ rfl ?_ ?_)
  · store_simp
  · store_simp
  -- the update of `w`
  have ht : (((s'.upd (H 2) (oR + j) ρ).upd μ.store.length 0 (M.neg ρ)).readBlock
      μ.store.length 0 1) = some [M.neg ρ] := Store.readBlock_one_of_get (by store_simp)
  refine wp_call_rel hJ.axpy rfl rfl rfl rfl
    ⟨hok, [_, _], rfl, by simp [hH.eq_iff]; omega⟩ ?_
    (xs := [[M.neg ρ], (qs.drop (j * n)).take n, ws']) ?_ ?_ fun zs hzl hzs => ?_
  · store_simp
  · store_simp
  · store_simp
  replace hzl : zs.length = n := hzl
  refine ⟨_, zs, r ++ [ρ], rfl, hzl, (((hfr.mono fun b i h => ?_).upd
    (Or.inl (Or.inr ⟨rfl, by omega, by omega⟩)) _).upd (Or.inr rfl) _).updBlock
    fun i hi => Or.inl (Or.inl ⟨rfl, by omega, by rw [hzl] at hi; omega⟩), ?_, ?_,
    hrec.step (hρ.congr hrowv fun _ _ => rfl) (hneg ρ)
      (hzs.congr hrowv (fun _ _ => rfl) fun _ _ => rfl)⟩
  · exact h.imp (Or.imp id fun h => ⟨h.1, h.2.1, by have := h.2.2; omega⟩) id
  · store_simp
  · store_simp
    exact Store.readBlock_upd_concat hr (by omega) _

/-- **The run of `mgs`**, for every interpretation meeting the contracts: `Q`, `w`, `R` in three
buffers, `Q` and `w` readable, `R` with room for `k + 1` cells. -/
theorem wp_mgs {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    {J : Interp Op Tst K} (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ a, dec (M.neg a) = -dec a) {τ : Tape K} {n k oQ ow oR : ℕ} {H : Fin 3 → ℕ}
    {μ : Mem K} {qs ws : List K} (hok : ok n) (hH : Function.Injective H)
    (hl : ∀ i, H i < μ.store.length) (hq : μ.store.readBlock (H 0) oQ (k * n) = some qs)
    (hw : μ.store.readBlock (H 1) ow n = some ws) (hwl : ow + n ≤ μ.store.len (H 1))
    (hR : oR + (k + 1) ≤ μ.store.len (H 2)) :
    Wp .total J τ mgs ⟨[n, k, oQ, ow, oR], [H 0, H 1, H 2]⟩
      (MgsRounded dec ε n k (H 1) ow (H 2) oR qs ws μ) μ := by
  have h0 := hl 0; have h1 := hl 1; have h2 := hl 2
  refine wp_alloc rfl (wp_seq (wp_loop (k := k) rfl (MgsInv dec ε n (H 1) ow (H 2) oR qs ws μ)
    ⟨_, ws, [], rfl, Store.length_of_readBlock hw, Store.EqOff.refl _ _, by store_simp, rfl,
      .zero⟩ (fun j hj μ₁ hinv => wp_mgs_step hS hJ hneg hok hH hl hj hq hwl hR hinv) ?_))
  rintro μ₁ ⟨s', ws', r, rfl, hws, hfr, hw', hr, hrec⟩
  have hlen : s'.length = μ.store.length + 1 := by rw [hfr.length_eq, Store.length_push]
  have hlR : s'.len (H 2) = μ.store.len (H 2) := by rw [hfr.len_eq, Store.len_push_of_lt h2]
  refine wp_call_rel_cell hJ.nrm2 rfl rfl rfl rfl rfl ⟨hok, by simp [hH.eq_iff]⟩ ?_
    (xs := [ws']) ?_ ?_ fun ν hν => ⟨ws', r, ν, hws, hrec, hν, rfl, ?_, ?_, ?_⟩
  · store_simp
  · store_simp
  · store_simp
  · refine Store.EqOff.pop ((hfr.mono fun b i h => ?_).upd
      (Or.inl (Or.inr ⟨rfl, by omega, by omega⟩)) _)
    exact h.imp (Or.imp id fun h => ⟨h.1, h.2.1, by have := h.2.2; omega⟩) id
  · store_simp
  · store_simp
    exact Store.readBlock_upd_concat (by rw [Store.readBlock_pop_of_lt (by omega)]; exact hr)
      (by rw [Store.len_pop_of_lt (by omega)]; omega) _

/-! ### The abstract theorem and its corollary by linking -/

omit [Inhabited K] in
/-- The call counts of `mgs`: `k` times `dot`, `neg`, `axpy` at the dimension `n`, and one
`nrm2`. -/
noncomputable def mgsCount (n k : ℕ) : Count Op Tst :=
  k • (Count.one (Has.inj Blas1Op.dot) [n] + (Count.one (Has.inj ScalarOp.neg) [] +
    Count.one (Has.inj Blas1Op.axpy) [n])) + Count.one (Has.inj Blas1Op.nrm2) [n]

/-- The workspace of `mgs`: one cell and the workspace of the operation that needs most. -/
def mgsPeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  1 + max (max (W (Has.inj Blas1Op.dot) [n]) (max (W (Has.inj ScalarOp.neg) [])
    (W (Has.inj Blas1Op.axpy) [n]))) (W (Has.inj Blas1Op.nrm2) [n])

omit [Inhabited K] in
theorem staticCost_mgs (n k a b c : ℕ) :
    staticCost (mgs (Op := Op) (Tst := Tst)) [n, k, a, b, c] = mgsCount n k := by
  simp [mgs, mgsBody, staticCost, useCost, mgsCount]

omit [Inhabited K] in
theorem staticPeak_mgs_le (W : Op → List ℕ → ℕ) (n k a b c : ℕ) :
    staticPeak W (mgs (Op := Op) (Tst := Tst)) [n, k, a, b, c] ≤ mgsPeak W n := by
  simp only [mgs, mgsBody, staticPeak, mgsPeak]
  refine Nat.add_le_add_left (max_le_max (Finset.sup_le fun j _ => ?_) ?_) _ <;> simp

/-- **The abstract theorem of `mgs`**: for every interpretation meeting the contracts of scalar
arithmetic and of the level-1 operations, the run terminates within `mgsCount n k` calls, and
the memory is described by the recurrence with local errors. -/
theorem runs_mgs_rounded {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    {J : Interp Op Tst K} (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ a, dec (M.neg a) = -dec a) (W : Op → List ℕ → ℕ) {τ : Tape K}
    {n k oQ ow oR : ℕ} {H : Fin 3 → ℕ} {μ : Mem K} {qs ws : List K} (hok : ok n)
    (hH : Function.Injective H) (hl : ∀ i, H i < μ.store.length)
    (hq : μ.store.readBlock (H 0) oQ (k * n) = some qs)
    (hw : μ.store.readBlock (H 1) ow n = some ws) (hwl : ow + n ≤ μ.store.len (H 1))
    (hR : oR + (k + 1) ≤ μ.store.len (H 2)) :
    Runs J W τ mgs ⟨[n, k, oQ, ow, oR], [H 0, H 1, H 2]⟩ μ (mgsCount n k) (mgsPeak W n)
      (MgsRounded dec ε n k (H 1) ow (H 2) oR qs ws μ) := by
  obtain ⟨μ', hrun, hpost⟩ := wp_mgs hS hJ hneg (τ := τ) hok hH hl hq hw hwl hR
  exact (Runs.of_run hrun hpost W).mono (le_of_eq (staticCost_mgs ..)) (staticPeak_mgs_le ..)
    fun _ h => h

variable [Apart Blas1Op ScalarOp Op]

/-- **The concrete corollary**: `mgs` linked through the profile of sequential summation, down to
scalar arithmetic meeting the standard model at the unit roundoff `u`. One application of the
certificate of the profile; the accuracy parameters are those of the profile, the counts are
pushed forward. No proof about the algorithm or its loops. -/
theorem runs_mgs_link_seq {M : Machine K} {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M)
    (hu : 0 ≤ u) {I : Interp Op Tst K} (hI : IsScalar M I) {τ : Tape K} {n k oQ ow oR : ℕ}
    {H : Fin 3 → ℕ} {μ : Mem K} {qs ws : List K} (hH : Function.Injective H)
    (hl : ∀ i, H i < μ.store.length) (hq : μ.store.readBlock (H 0) oQ (k * n) = some qs)
    (hw : μ.store.readBlock (H 1) ow n = some ws) (hwl : ow + n ≤ μ.store.len (H 1))
    (hR : oR + (k + 1) ≤ μ.store.len (H 2)) :
    Runs I (Blas.ws 0) τ (mgs.link Blas.seq.table) ⟨[n, k, oQ, ow, oR], [H 0, H 1, H 2]⟩ μ
      (Count.push Blas.seq.cost (mgsCount n k)) (mgsPeak (Blas.ws 0 : Op → List ℕ → ℕ) n)
      (MgsRounded dec (Blas.seq.err u) n k (H 1) ow (H 2) oR qs ws μ) :=
  (Blas.seq_certifies hM hu fun _ => True).runs
    (fun _ hJ => runs_mgs_rounded hJ.1 hJ.2 hM.neg _ trivial hH hl hq hw hwl hR) hI

omit [Inhabited K] in
/-- **The scalar counts of the linked `mgs`**, by evaluating the push-forward. -/
theorem push_seq_mgsCount (n k : ℕ) :
    Count.push Blas.seq.cost (mgsCount (Op := Op) (Tst := Tst) n k) =
      k • (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) • Blas.sc .copy +
        (n - 1) • Blas.sc .add)) + (Blas.sc .neg + n • (Blas.sc .mul + Blas.sc .add))) +
      (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) • Blas.sc .copy +
        (n - 1) • Blas.sc .add) + Blas.sc .sqrt)) := by
  simp only [mgsCount, map_add, map_nsmul, Count.push_one, Blas.seq_cost_dot,
    Blas.seq_cost_axpy, Blas.seq_cost_nrm2, Blas.seq_cost_scalar]

end NLAlib.Ops.Examples
