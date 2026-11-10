/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Krylov

/-!
# Example: modified Gram–Schmidt over `dot`, `axpy`, `nrm2`, linked twice

The algorithm `NLAlib.Ops.Examples.mgs` orthogonalizes a vector `w` against the `k` rows of `Q`
and stores the `k` coefficients and the norm of the result in `R`.

## Main results

* Mathematics: the postcondition is the recurrence with local errors
  `NLAlib.Ops.Examples.MgsRec`, on decoded values; its analysis is not part of this file.
* Program logic (`NLAlib.Ops.Examples.wp_mgs`): for every interpretation meeting the contracts of
  the second level, the run ends in a memory described by the recurrence.
* The abstract theorem (`NLAlib.Ops.Examples.runs_mgs`): the same with the call counts
  `k (dot + neg + axpy) + nrm2` and two scratch cells, the counts by evaluating the static cost.
* The corollary (`NLAlib.Ops.Examples.runs_mgs_link`): the program linked twice, down to scalar
  arithmetic meeting the standard model at `u`, by two applications of `Runs.link`; its counts
  are the push-forward through both tables, evaluated in
  `NLAlib.Ops.Examples.push_blasCost_push_krylovCost_mgsCount`.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

variable {K : Type} [Inhabited K]

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
      DotErr dec εd n (q j) w ρ → dec t = -dec ρ → AxpyErr dec εa n t (q j) w w' →
      MgsRec dec εd εa n q w₀ (j + 1) w' (r ++ [ρ])

omit [Inhabited K] in
theorem MgsRec.length {dec : K → ℝ} {εd εa : ℝ} {n : ℕ} {q : ℕ → ℕ → K} {w₀ w : ℕ → K} {j : ℕ}
    {r : List K} (h : MgsRec dec εd εa n q w₀ j w r) : r.length = j := by
  induction h with
  | zero => rfl
  | step _ _ _ _ ih => simp [ih]

/-! ### The algorithm -/

/-- One step: `R_j := dot Q_j w; t := neg R_j; w := w + t Q_j`. -/
def mgsBody : Stmt KOp :=
  .seq (.call (.bl .dot) [.var 0] [⟨0, .var 2 + .var 5 * .var 0⟩, ⟨1, .var 3⟩]
      [⟨2, .var 4 + .var 5⟩])
    (.seq (.call (.bl (.ar .neg)) [] [⟨2, .var 4 + .var 5⟩] [⟨3, .const 0⟩])
      (.call (.bl .axpy) [.var 0] [⟨3, .const 0⟩, ⟨0, .var 2 + .var 5 * .var 0⟩, ⟨1, .var 3⟩]
        [⟨1, .var 3⟩]))

/-- **Modified Gram–Schmidt.** Index variables: `n`, `k`, the offsets of `Q`, `w`, `R`, then the
loop variable; buffer variables: `Q`, `w`, `R`, then the scratch cell. -/
def mgs : Stmt KOp :=
  .alloc (.const 1) (.seq (.loop (.var 1) mgsBody)
    (.call .nrm2 [.var 0] [⟨1, .var 3⟩] [⟨2, .var 4 + .var 1⟩]))

/-! ### Program logic -/

/-- The store during the run, below the scratch cell: `w` holds `ws` and `R` holds `r`. -/
def mgsStore (s : Store K) (w R : ℕ × ℕ) (ws r : List K) : Store K :=
  (s.updBlock R.1 R.2 r).updBlock w.1 w.2 ws

section StoreLemmas

omit [Inhabited K]

theorem length_mgsStore (s : Store K) (w R : ℕ × ℕ) (ws r : List K) :
    (mgsStore s w R ws r).length = s.length := by simp [mgsStore]

theorem len_mgsStore (s : Store K) (w R : ℕ × ℕ) (ws r : List K) (b : ℕ) :
    (mgsStore s w R ws r).len b = s.len b := by simp [mgsStore]

theorem mgsStore_readBlock_other {s : Store K} {w R : ℕ × ℕ} {b : ℕ} (hw : b ≠ w.1)
    (hR : b ≠ R.1) (ws r : List K) (off n : ℕ) :
    (mgsStore s w R ws r).readBlock b off n = s.readBlock b off n :=
  Store.readBlock_congr fun i _ => by
    rw [mgsStore, Store.get_updBlock_of_buf_ne hw, Store.get_updBlock_of_buf_ne hR]

theorem mgsStore_readBlock_w {s : Store K} {w R : ℕ × ℕ} (hwR : w.1 ≠ R.1) {n : ℕ}
    {ws₀ ws : List K} (h : s.readBlock w.1 w.2 n = some ws₀) (hl : ws.length = n) (r : List K) :
    (mgsStore s w R ws r).readBlock w.1 w.2 n = some ws :=
  Store.readBlock_updBlock_of_readBlock (ys := ws₀)
    (by rw [← h]; exact Store.readBlock_congr fun i _ => Store.get_updBlock_of_buf_ne hwR _ _ _)
    hl

theorem mgsStore_get_R {s : Store K} {w R : ℕ × ℕ} (hwR : w.1 ≠ R.1) (ws : List K) {r : List K}
    (hlen : R.2 + r.length ≤ s.len R.1) {j : ℕ} (hj : j < r.length) :
    (mgsStore s w R ws r).get R.1 (R.2 + j) = r[j]? := by
  rw [mgsStore, Store.get_updBlock_of_buf_ne hwR.symm, Store.get_updBlock hlen hj]

theorem mgsStore_upd_R {s : Store K} {w R : ℕ × ℕ} (hwR : w.1 ≠ R.1) (ws r : List K) (v : K) :
    (mgsStore s w R ws r).upd R.1 (R.2 + r.length) v = mgsStore s w R ws (r ++ [v]) := by
  rw [mgsStore, Store.upd_updBlock_comm (Or.inl hwR.symm), ← Store.updBlock_concat]
  rfl

theorem mgsStore_updBlock_w (s : Store K) (w R : ℕ × ℕ) {ws zs : List K}
    (h : ws.length = zs.length) (r : List K) :
    (mgsStore s w R ws r).updBlock w.1 w.2 zs = mgsStore s w R zs r :=
  Store.updBlock_updBlock h

end StoreLemmas

/-- **One step of the loop**, by the contracts of `dot`, `neg` and `axpy`. -/
theorem wp_mgs_step {M : Machine K} {dec : K → ℝ} {εd : ℕ → ℝ} {εa εs : ℝ} {J : Interp KOp K}
    (hJ : IsKrylov M dec εd εa εs J) (hneg : ∀ a, dec (M.neg a) = -dec a) {τ : ℕ → K}
    {n k : ℕ} {Q w R : ℕ × ℕ} {s : Store K} {p : ℕ} {qs ws₀ ws r : List K} {tb : Buf K}
    (hj : r.length < k) (hQw : Q.1 ≠ w.1) (hQR : Q.1 ≠ R.1) (hwR : w.1 ≠ R.1)
    (hbQ : Q.1 < s.length) (hbw : w.1 < s.length)
    (hq : s.readBlock Q.1 Q.2 (k * n) = some qs) (hw : s.readBlock w.1 w.2 n = some ws₀)
    (hR : R.2 + (k + 1) ≤ s.len R.1) (hws : ws.length = n) (htb : tb.length = 1)
    {P : Mem K → Prop}
    (hP : ∀ (ρ t : K) (zs : List K) (tb' : Buf K), zs.length = n → tb'.length = 1 →
      DotErr dec (εd n) n (fun i => vec qs (r.length * n + i)) (vec ws) ρ → dec t = -dec ρ →
      AxpyErr dec εa n t (fun i => vec qs (r.length * n + i)) (vec ws) (vec zs) →
      P ⟨mgsStore s w R zs (r ++ [ρ]) ++ [tb'], p⟩) :
    Wp .total J τ mgsBody ⟨[n, k, Q.2, w.2, R.2, r.length], [Q.1, w.1, R.1, s.length]⟩ P
      ⟨mgsStore s w R ws r ++ [tb], p⟩ := by
  have hbR : R.1 < s.length := Store.lt_length_of_lt_len (i := R.2) (by omega)
  have hL := fun ws' r' => length_mgsStore s w R ws' r'
  have hkn : r.length * n + n ≤ k * n := by
    have := Nat.mul_le_mul_right n hj
    rwa [Nat.succ_mul] at this
  have hrowv : ∀ i < n, vec ((qs.drop (r.length * n)).take n) i = vec qs (r.length * n + i) :=
    fun i hi => Store.getD_drop_take qs _ _ _ hi default
  have hrowS : ∀ (ws' r' : List K) (tb' : Buf K),
      (mgsStore s w R ws' r' ++ [tb']).readBlock Q.1 (Q.2 + r.length * n) n =
        some ((qs.drop (r.length * n)).take n) := fun ws' r' tb' => by
    rw [Store.readBlock_append_of_lt (by rw [hL]; exact hbQ), mgsStore_readBlock_other hQw hQR]
    exact Store.readBlock_sub hq hkn
  have hwS : ∀ (ws' r' : List K) (tb' : Buf K), ws'.length = n →
      (mgsStore s w R ws' r' ++ [tb']).readBlock w.1 w.2 n = some ws' := fun ws' r' tb' hl => by
    rw [Store.readBlock_append_of_lt (by rw [hL]; exact hbw), mgsStore_readBlock_w hwR hw hl]
  -- the coefficient
  refine wp_seq (wp_call hJ.dot (d := [n]) (a := [(Q.1, Q.2 + r.length * n), w])
    (b := [(R.1, R.2 + r.length)]) rfl rfl rfl ⟨n, _, _, _, rfl, rfl, rfl, hQR, hwR, ?_⟩ ?_)
  · refine (Mode.needs_total _).mpr ⟨by simp [hrowS], by simp [hwS _ _ _ hws], ?_⟩
    change R.2 + r.length < (mgsStore s w R ws r ++ [tb]).len R.1
    rw [Store.len_append_of_lt (by rw [hL]; exact hbR), len_mgsStore]
    omega
  rintro m₁ ⟨n', x', y', z', xs, ys, ρ, hd, hi, ho, hxs, hys, herr, rfl⟩
  cases hd
  cases hi
  cases ho
  obtain rfl : (qs.drop (r.length * n)).take n = xs :=
    Option.some.inj ((hrowS _ _ _).symm.trans hxs)
  obtain rfl : ws = ys := Option.some.inj ((hwS _ _ _ hws).symm.trans hys)
  have e1 : Mem.upd ⟨mgsStore s w R ws r ++ [tb], p⟩ (R.1, R.2 + r.length) ρ =
      ⟨mgsStore s w R ws (r ++ [ρ]) ++ [tb], p⟩ := by
    simp only [Mem.upd]
    rw [Store.upd_append_of_lt (by rw [hL]; exact hbR), mgsStore_upd_R hwR]
  rw [e1]
  -- its negation, in the scratch cell
  refine wp_seq (wp_call_un (hJ.ar .neg) (x := (R.1, R.2 + r.length)) (z := (s.length, 0)) rfl
    rfl rfl trivial (a := ρ) ?_ rfl ?_ ?_)
  · change (mgsStore s w R ws (r ++ [ρ]) ++ [tb]).get R.1 (R.2 + r.length) = some ρ
    rw [Store.get_append_of_lt (by rw [hL]; exact hbR),
      mgsStore_get_R hwR ws (by simp; omega) (by simp)]
    simp
  · change 0 < (mgsStore s w R ws (r ++ [ρ]) ++ [tb]).len s.length
    rw [Store.len_top (hL _ _).symm, htb]
    exact Nat.one_pos
  have e2 : Mem.upd ⟨mgsStore s w R ws (r ++ [ρ]) ++ [tb], p⟩ (s.length, 0) (M.neg ρ) =
      ⟨mgsStore s w R ws (r ++ [ρ]) ++ [tb.set 0 (some (M.neg ρ))], p⟩ := by
    simp only [Mem.upd]
    rw [Store.upd_top (hL _ _).symm]
  rw [e2]
  -- the update of `w`
  have hget : (mgsStore s w R ws (r ++ [ρ]) ++ [tb.set 0 (some (M.neg ρ))]).get s.length 0 =
      some (M.neg ρ) := by
    rw [Store.get_top (hL _ _).symm]
    simp [htb]
  refine wp_call hJ.axpy (d := [n]) (a := [(s.length, 0), (Q.1, Q.2 + r.length * n), w])
    (b := [w]) rfl rfl rfl ⟨n, _, _, _, rfl, rfl, rfl, Nat.ne_of_gt hbw, hQw,
      (Mode.needs_total _).mpr ⟨by simp [hget], by simp [hrowS], by simp [hwS _ _ _ hws]⟩⟩ ?_
  rintro m₃ ⟨n', al', x', y', a, xs, ys, zs, hd, hi, ho, ha, hxs, hys, hzl, herr2, rfl⟩
  cases hd
  cases hi
  cases ho
  obtain rfl : M.neg ρ = a := Option.some.inj (hget.symm.trans ha)
  obtain rfl : (qs.drop (r.length * n)).take n = xs :=
    Option.some.inj ((hrowS _ _ _).symm.trans hxs)
  obtain rfl : ws = ys := Option.some.inj ((hwS _ _ _ hws).symm.trans hys)
  have e3 : Mem.updBlock ⟨mgsStore s w R ws (r ++ [ρ]) ++ [tb.set 0 (some (M.neg ρ))], p⟩ w zs =
      ⟨mgsStore s w R zs (r ++ [ρ]) ++ [tb.set 0 (some (M.neg ρ))], p⟩ := by
    simp only [Mem.updBlock]
    rw [Store.updBlock_append_of_lt (by rw [hL]; exact hbw),
      mgsStore_updBlock_w s w R (hws.trans hzl.symm)]
  rw [e3]
  exact hP ρ (M.neg ρ) zs _ hzl (by simpa using htb) (herr.congr hrowv fun _ _ => rfl) (hneg ρ)
    (herr2.congr hrowv (fun _ _ => rfl) fun _ _ => rfl)

/-- The postcondition of `mgs`: the memory after the run, from the memory `m` before. -/
def MgsPost (dec : K → ℝ) (εd : ℕ → ℝ) (εa εs : ℝ) (n k : ℕ) (w R : ℕ × ℕ) (qs ws : List K)
    (m m' : Mem K) : Prop :=
  ∃ (ws' r : List K) (σ ν : K), ws'.length = n ∧
    MgsRec dec (εd n) εa n (fun j i => vec qs (j * n + i)) (vec ws) k (vec ws') r ∧
    DotErr dec (εd n) n (vec ws') (vec ws') σ ∧
    (0 ≤ dec σ → |dec ν - √(dec σ)| ≤ εs * √(dec σ)) ∧
    m' = ⟨mgsStore m.store w R ws' (r ++ [ν]), m.pos⟩

/-- **The run of `mgs`**, for every interpretation meeting the contracts of the second level:
`Q`, `w`, `R` in three buffers, `Q` and `w` readable, `R` with room for `k + 1` cells. -/
theorem wp_mgs {M : Machine K} {dec : K → ℝ} {εd : ℕ → ℝ} {εa εs : ℝ} {J : Interp KOp K}
    (hJ : IsKrylov M dec εd εa εs J) (hneg : ∀ a, dec (M.neg a) = -dec a) {τ : ℕ → K}
    {n k : ℕ} {Q w R : ℕ × ℕ} {m : Mem K} {qs ws : List K} (hQw : Q.1 ≠ w.1) (hQR : Q.1 ≠ R.1)
    (hwR : w.1 ≠ R.1) (hbQ : Q.1 < m.store.length) (hbw : w.1 < m.store.length)
    (hq : m.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hw : m.store.readBlock w.1 w.2 n = some ws) (hR : R.2 + (k + 1) ≤ m.store.len R.1) :
    Wp .total J τ mgs ⟨[n, k, Q.2, w.2, R.2], [Q.1, w.1, R.1]⟩
      (MgsPost dec εd εa εs n k w R qs ws m) m := by
  obtain ⟨s, p⟩ := m
  have hbR : R.1 < s.length := Store.lt_length_of_lt_len (i := R.2) (by simp at hR; omega)
  refine wp_alloc rfl (wp_seq (wp_loop (k := k) rfl (fun j m' => ∃ (ws' r : List K) (tb : Buf K),
    ws'.length = n ∧ tb.length = 1 ∧
    MgsRec dec (εd n) εa n (fun j i => vec qs (j * n + i)) (vec ws) j (vec ws') r ∧
    m' = ⟨mgsStore s w R ws' r ++ [tb], p⟩)
    ⟨ws, [], List.replicate 1 none, Store.length_of_readBlock hw, rfl, .zero, ?_⟩ ?_ ?_))
  · rw [mgsStore, Store.updBlock_nil, Store.updBlock_of_readBlock hw]
    rfl
  · rintro j hj m' ⟨ws', r, tb, hws', htb, hrec, rfl⟩
    obtain rfl := hrec.length
    exact wp_mgs_step hJ hneg hj hQw hQR hwR hbQ hbw hq hw hR hws' htb
      fun ρ t zs tb' hz ht h1 h2 h3 => ⟨zs, r ++ [ρ], tb', hz, ht, hrec.step h1 h2 h3, rfl⟩
  · rintro m' ⟨ws', r, tb, hws', htb, hrec, rfl⟩
    have hL := length_mgsStore s w R ws' r
    refine wp_call hJ.nrm2 (d := [n]) (a := [w]) (b := [(R.1, R.2 + k)]) rfl rfl rfl
      ⟨n, _, _, rfl, rfl, rfl, hwR, (Mode.needs_total _).mpr ⟨?_, ?_⟩⟩ ?_
    · change ((mgsStore s w R ws' r ++ [tb]).readBlock w.1 w.2 n).isSome
      rw [Store.readBlock_append_of_lt (by rw [hL]; exact hbw),
        mgsStore_readBlock_w hwR hw hws']
      rfl
    · change R.2 + k < (mgsStore s w R ws' r ++ [tb]).len R.1
      rw [Store.len_append_of_lt (by rw [hL]; exact hbR), len_mgsStore]
      simp at hR
      omega
    rintro m₂ ⟨n', x', z', xs, σ, ν, hd, hi, ho, hxs, h1, h2, rfl⟩
    cases hd
    cases hi
    cases ho
    have hxs' : (mgsStore s w R ws' r ++ [tb]).readBlock w.1 w.2 n = some xs := hxs
    rw [Store.readBlock_append_of_lt (by rw [hL]; exact hbw),
      mgsStore_readBlock_w hwR hw hws'] at hxs'
    obtain rfl := Option.some.inj hxs'
    refine ⟨ws', r, σ, ν, hws', hrec, h1, h2, ?_⟩
    simp only [Mem.upd]
    rw [Store.upd_append_of_lt (by rw [hL]; exact hbR), ← hrec.length, mgsStore_upd_R hwR,
      Store.pop_append_top]

/-! ### The abstract theorem and its corollary by linking -/

/-- The call counts of `mgs`: `k` times `dot`, `neg`, `axpy` at the dimension `n`, and one
`nrm2`. -/
noncomputable def mgsCount (n k : ℕ) : Count KOp :=
  k • (Count.one (.bl .dot) [n] + Count.one (.bl (.ar .neg)) [] + Count.one (.bl .axpy) [n]) +
    Count.one .nrm2 [n]

theorem staticCost_mgs (n k a b c : ℕ) : staticCost mgs [n, k, a, b, c] = mgsCount n k := by
  simp [mgs, mgsBody, staticCost, useCost, mgsCount, add_assoc]

theorem staticPeak_mgs_le (n k a b c : ℕ) : staticPeak krylovWs mgs [n, k, a, b, c] ≤ 2 := by
  simp [mgs, mgsBody, staticPeak, krylovWs, blasWs]

/-- **The abstract theorem of `mgs`**: for every interpretation meeting the contracts of the
second level, the run terminates within `mgsCount n k` calls and two scratch cells, in a memory
described by the recurrence with local errors. -/
theorem runs_mgs {M : Machine K} {dec : K → ℝ} {εd : ℕ → ℝ} {εa εs : ℝ} {J : Interp KOp K}
    (hJ : IsKrylov M dec εd εa εs J) (hneg : ∀ a, dec (M.neg a) = -dec a) {τ : ℕ → K}
    {n k : ℕ} {Q w R : ℕ × ℕ} {m : Mem K} {qs ws : List K} (hQw : Q.1 ≠ w.1) (hQR : Q.1 ≠ R.1)
    (hwR : w.1 ≠ R.1) (hbQ : Q.1 < m.store.length) (hbw : w.1 < m.store.length)
    (hq : m.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hw : m.store.readBlock w.1 w.2 n = some ws) (hR : R.2 + (k + 1) ≤ m.store.len R.1) :
    Runs J krylovWs τ mgs ⟨[n, k, Q.2, w.2, R.2], [Q.1, w.1, R.1]⟩ m (mgsCount n k) 2
      (MgsPost dec εd εa εs n k w R qs ws m) := by
  obtain ⟨m', hrun, hpost⟩ := wp_mgs hJ hneg (τ := τ) hQw hQR hwR hbQ hbw hq hw hR
  exact (Runs.of_run hrun hpost krylovWs).mono (le_of_eq (staticCost_mgs ..))
    (staticPeak_mgs_le ..) fun _ h => h

/-- **The concrete corollary**: `mgs` linked twice, down to scalar arithmetic meeting the
standard model at the unit roundoff `u`. Two applications of the linking theorem; the accuracy
parameters are those of the implementations, the counts are pushed forward through both tables,
the workspace is unchanged. No proof about the algorithm or its loops. -/
theorem runs_mgs_link {M : Machine K} {I : Interp AOp K} (hI : IsArith M I) {u : ℝ} {dec : K → ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) {τ : ℕ → K} {n k : ℕ} {Q w R : ℕ × ℕ} {m : Mem K}
    {qs ws : List K} (hQw : Q.1 ≠ w.1) (hQR : Q.1 ≠ R.1) (hwR : w.1 ≠ R.1)
    (hbQ : Q.1 < m.store.length) (hbw : w.1 < m.store.length)
    (hq : m.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hw : m.store.readBlock w.1 w.2 n = some ws) (hR : R.2 + (k + 1) ≤ m.store.len R.1) :
    Runs I (fun _ _ => 0) τ ((mgs.link krylovTable).link blasTable)
      ⟨[n, k, Q.2, w.2, R.2], [Q.1, w.1, R.1]⟩ m
      (Count.push blasCost (Count.push krylovCost (mgsCount n k))) 2
      (MgsPost dec (fun n => (1 + u) ^ (2 * n) - 1) (2 * u + u ^ 2) u n k w R qs ws m) :=
  ((runs_mgs (isKrylov_link (isBlas_link hI hM hu) hM) hM.neg hQw hQR hwR hbQ hbw hq hw
    hR).link (krylov_accounts _)).link (blas_accounts I)

/-- **The scalar counts of the linked `mgs`**, by evaluating the push-forward through both
tables: `k + 1` literals, `(2 k + 1) n` multiplications and additions, `k` negations, one square
root. -/
theorem push_blasCost_push_krylovCost_mgsCount (n k : ℕ) :
    Count.push blasCost (Count.push krylovCost (mgsCount n k)) =
      (k + 1) • Count.one (.lit 0) [] +
        ((2 * k + 1) * n) • (Count.one .mul [] + Count.one .add []) +
        k • Count.one .neg [] + Count.one .sqrt [] := by
  simp only [mgsCount, map_add, map_nsmul, Count.push_one, krylovCost, blasCost]
  module

end NLAlib.Ops.Examples
