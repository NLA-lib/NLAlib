/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Dot
public import NLAlib.Ops.Tape

/-!
# Example: stochastic rounding, in two formulations

**Explicit randomness.** `sradd [x, y, ξ] [z]` is an ordinary function `f` of three cells, the
third filled by a draw. Its contract (`NLAlib.Ops.Examples.IsSrAdd`, with the mathematics
`NLAlib.Ops.Examples.SrModel`): surely within `2 u` of the sum, and unbiased up to `β u` when
`ξ` is uniform on the finite set `Ξ` of values of a draw.

**As a program that draws.** `sraddD [x, y] [z]` is implemented by "draw `ξ` into scratch;
`sradd`". Its contract (`NLAlib.Ops.Examples.IsSrAddD`) is the same statement about the meaning
as a function `g` of its operands and of its tape window, one entry
(`NLAlib.Ops.Examples.drawBin`). No interpretation is indexed by a sample.

Linking transfers the contract: `NLAlib.Ops.Examples.isSrAddD_link` (the induced interpretation
meets the drawn contract with `g = f`, so the same `SrModel` holds) and
`NLAlib.Ops.Examples.sraddD_tapeLocal` (the window, by the window lemma).

An algorithm over the drawn operation, the stochastically rounded sum
`NLAlib.Ops.Examples.srsum`: abstract theorem, sure error bound
(`NLAlib.Ops.Examples.abs_dec_srsumF_sub_le`, mathematics), and the corollary by linking.
## Main results

* `NLAlib.Ops.Examples.isSrAddD_link`: the drawn contract, by linking.
* `NLAlib.Ops.Examples.sraddD_tapeLocal`: the window of the drawn operation.
* `NLAlib.Ops.Examples.runs_srsum`, `NLAlib.Ops.Examples.runs_srsum_link`: the sum, abstract and
  linked.
* `NLAlib.Ops.Examples.exists_isSrAdd`: the contracts can be met.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

variable {K : Type}

/-- The lower signature: a draw, and the stochastically rounded addition given its random word. -/
inductive S0 where
  /-- `draw [] [] [t]`: the next entry of the tape. -/
  | draw
  /-- `sradd [] [x, y, ξ] [z]`. -/
  | sradd
  deriving DecidableEq

/-- The upper signature: the stochastically rounded addition that draws. -/
inductive S1 where
  /-- `sraddD [] [x, y] [z]`. -/
  | sraddD
  deriving DecidableEq

/-! ### Mathematics: the contract of a stochastic rounding function -/

/-- **Stochastic rounding of a sum**, as a property of a function `f` of the summands and the
random word: surely within `2 u` relative; unbiased up to `β u` relative, for the random word
uniform on `Ξ`. -/
structure SrModel (u β : ℝ) (dec : K → ℝ) (Ξ : Finset K) (f : K → K → K → K) : Prop where
  /-- The sure bound. -/
  sure : ∀ a b ξ, |dec (f a b ξ) - (dec a + dec b)| ≤ 2 * u * |dec a + dec b|
  /-- Unbiasedness, for the random word uniform on `Ξ`. -/
  unbiased : ∀ a b, |(∑ ξ ∈ Ξ, dec (f a b ξ)) / Ξ.card - (dec a + dec b)| ≤
    β * u * |dec a + dec b|

/-! ### The two contracts -/

/-- **Explicit randomness**: `sradd` is the function `f` of three cells; `draw` is the draw. -/
structure IsSrAdd (f : K → K → K → K) (I : Interp S0 K) : Prop where
  /-- `sradd` is `f`. -/
  sradd : I.IsFn .total .sradd (.tern fun a b ξ => some (f a b ξ)) AnyOperands
  /-- `draw` is the draw of the model. -/
  draw : I.IsFn .total .draw .draw AnyOperands

/-- The block function of an operation of two cells that draws once: the result is `g` of the
operands and of the tape window. -/
def drawBin (g : K → K → K → K) : BlockFn K where
  win _ := 1
  inLens _ := [1, 1]
  fn d w xs := match d, w, xs with
    | [], [ξ], [[a], [b]] => some [g a b ξ]
    | _, _, _ => none

/-- A call of `drawBin`, on cells. -/
theorem drawBin_apply_of {g : K → K → K → K} {x y z : ℕ × ℕ} {τ : ℕ → K} {m : Mem K} {a b : K}
    (hx : m.store.get x.1 x.2 = some a) (hy : m.store.get y.1 y.2 = some b)
    (hz : z.2 < m.store.len z.1) :
    (drawBin g).apply [] [x, y] z τ m = some ((m.upd z (g a b (τ m.pos))).advance 1) :=
  BlockFn.apply_eq_some_iff.mpr ⟨[[a], [b]], [g a b (τ m.pos)],
    by simp [drawBin, Mem.readBlocks, BlockFn.readBlock_one, hx, hy], by simp [drawBin],
    by simpa using hz, rfl⟩

/-- What a successful call of `drawBin` is. -/
theorem drawBin_apply {g : K → K → K → K} {d : List ℕ} {ins : List (ℕ × ℕ)} {z : ℕ × ℕ}
    {τ : ℕ → K} {m m' : Mem K} (h : (drawBin g).apply d ins z τ m = some m') :
    ∃ x y a b, d = [] ∧ ins = [x, y] ∧ m.store.get x.1 x.2 = some a ∧
      m.store.get y.1 y.2 = some b ∧ z.2 < m.store.len z.1 ∧
      m' = (m.upd z (g a b (τ m.pos))).advance 1 := by
  obtain ⟨X, v, hread, hfn, hlen, rfl⟩ := BlockFn.apply_eq_some_iff.mp h
  obtain ⟨x, y, xs, ys, rfl, hx, hy, rfl⟩ := Mem.readBlocks_two hread
  rw [BlockFn.readBlock_one] at hx hy
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hy
  rcases d with _ | ⟨n, d⟩
  · simp only [drawBin, List.range_one, List.map_cons, List.map_nil, Nat.add_zero,
      Option.some.injEq] at hfn
    subst hfn
    exact ⟨x, y, a, b, rfl, rfl, ha, hb, by simpa using hlen, rfl⟩
  · simp [drawBin] at hfn

/-- **As an operation that draws**: `sraddD` is the function `g` of its two cells and of its tape
window. -/
def IsSrAddD (g : K → K → K → K) (J : Interp S1 K) : Prop :=
  J.IsFn .total .sraddD (drawBin g) AnyOperands

/-! ### The drawing implementation and the transfer through linking -/

/-- **The implementation of `sraddD`**: draw into a scratch cell, then `sradd`. Index variables:
the offsets of `x`, `y`, `z`. -/
def sraddDImpl : Impl S0 where
  nd := 0
  nin := 2
  nout := 1
  body := .alloc (.const 1) (.seq (.call .draw [] [] [⟨3, .const 0⟩])
    (.call .sradd [] [⟨0, .var 0⟩, ⟨1, .var 1⟩, ⟨3, .const 0⟩] [⟨2, .var 2⟩]))

/-- The table: `sraddD` by the drawing program. -/
def srTable : Table S1 S0
  | .sraddD => .inl sraddDImpl

/-- **The exact certificate of the drawing program**: its run is the block function of `f` with
the window entry as random word. -/
theorem sraddD_cert {f : K → K → K → K} {I : Interp S0 K} (hI : IsSrAdd f I) {d : List ℕ}
    {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : ℕ → K} {m m' : Mem K}
    (h : (drawBin f).apply d ins z τ m = some m') :
    sraddDImpl.Fits d.length ins.length 1 ∧
      run I τ sraddDImpl.body (Env.frame d (ins ++ [z])) m = some m' := by
  obtain ⟨x, y, a, b, rfl, rfl, hx, hy, hz, rfl⟩ := drawBin_apply h
  obtain ⟨s, p⟩ := m
  have hbz : z.1 < s.length := Store.lt_length_of_lt_len hz
  refine ⟨⟨rfl, rfl, rfl⟩, run_of_wp (wp_alloc rfl (wp_seq (wp_call_draw hI.draw
    (z := (s.length, 0)) rfl rfl rfl trivial ?_ ?_)))⟩
  · change 0 < (s ++ [List.replicate 1 none]).len s.length
    simp
  have e1 : ((⟨s.push 1, p⟩ : Mem K).upd (s.length, 0) (τ p)).advance 1 =
      ⟨s ++ [[some (τ p)]], p + 1⟩ := by
    simp only [Mem.upd, Mem.advance, Store.push]
    rw [Store.upd_append_top]
    rfl
  rw [e1]
  refine wp_call_tern hI.sradd (x := x) (y := y) (w := (s.length, 0)) (z := z) rfl rfl rfl
    trivial (a := a) (b := b) (c := τ p) ?_ ?_ ?_ rfl ?_ ?_
  · change (s ++ [_]).get x.1 x.2 = some a
    rw [Store.get_append_of_lt (Store.lt_length_of_get hx)]
    exact hx
  · change (s ++ [_]).get y.1 y.2 = some b
    rw [Store.get_append_of_lt (Store.lt_length_of_get hy)]
    exact hy
  · change (s ++ [[some (τ p)]]).get s.length 0 = some (τ p)
    rw [Store.get_append_top]
    rfl
  · change z.2 < (s ++ [_]).len z.1
    rwa [Store.len_append_of_lt hbz]
  · simp only [Mem.upd, Mem.advance]
    rw [Store.upd_append_of_lt hbz, Store.pop_append_top]

/-- **The contract transfers through linking**: the induced interpretation meets the drawn
contract with the same function `f`; so whatever `SrModel` holds of `f` holds of the drawn
operation, with the expectation over the window entry. -/
theorem isSrAddD_link {f : K → K → K → K} {I : Interp S0 K} (hI : IsSrAdd f I) :
    IsSrAddD f (I.link srTable) :=
  Interp.link_isFn rfl fun _ _ _ _ _ _ _ h => sraddD_cert hI h

/-- The tape windows of the lower operations, registered with the access model: one entry for a
draw, none for `sradd`. -/
def srWindow : S0 → List ℕ → ℕ
  | .draw, _ => 1
  | .sradd, _ => 0

/-- **The window of the drawn operation**, by the window lemma: the induced meaning reads one
entry of the tape at the position and advances by one. -/
theorem sraddD_tapeLocal {I : Interp S0 K} (hI : ∀ o, I.TapeLocal o (srWindow o)) :
    (I.link srTable).TapeLocal .sraddD fun _ => 1 :=
  Interp.TapeLocal.link hI (o := S1.sraddD) rfl (by simp [Stmt.Straight, sraddDImpl])
    fun d offs hd ho => by
      obtain rfl := List.length_eq_zero_iff.mp hd
      obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp ho
      simp [staticWindow, sraddDImpl, srWindow]

/-- The cost of the drawn operation: one draw and one `sradd`. -/
noncomputable def srCost : S1 → List ℕ → Count S0
  | .sraddD, _ => Count.one .draw [] + Count.one .sradd []

/-- The accounting certificate of the drawing program. -/
theorem sr_accounts (I : Interp S0 K) : srTable.Accounts I (fun _ _ => 0) srCost fun _ _ => 1 := by
  refine Table.accounts_of_static ?_ (fun o o' hT => by cases o; cases hT) I
  intro o R hT d offs hd ho
  cases o
  cases hT
  obtain rfl := List.length_eq_zero_iff.mp hd
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp ho
  simp [sraddDImpl, staticCost, staticPeak, useCost, srCost]

/-! ### An algorithm over the drawn operation: the stochastically rounded sum -/

/-- `z := z ⊕ x_0 ⊕ … ⊕ x_{n-1}` with stochastically rounded additions. Index variables: `n`,
the offsets of `x`, `z`, then the loop variable. -/
def srsum : Stmt S1 :=
  .loop (.var 0) (.call .sraddD [] [⟨1, .var 2⟩, ⟨0, .var 1 + .var 3⟩] [⟨1, .var 2⟩])

/-- The stochastically rounded sum as a function of the tape entries from the position `p`. -/
def srsumF (g : K → K → K → K) (z₀ : K) (x : ℕ → K) (τ : ℕ → K) (p : ℕ) : ℕ → K
  | 0 => z₀
  | k + 1 => g (srsumF g z₀ x τ p k) (x k) (τ (p + k))

/-- **The sure error of the stochastically rounded sum**, for every tape. -/
theorem abs_dec_srsumF_sub_le {u β : ℝ} {dec : K → ℝ} {Ξ : Finset K} {g : K → K → K → K}
    (hg : SrModel u β dec Ξ g) (hu : 0 ≤ u) (z₀ : K) (x τ : ℕ → K) (p n : ℕ) :
    |dec (srsumF g z₀ x τ p n) - (dec z₀ + ∑ k ∈ Finset.range n, dec (x k))| ≤
      ((1 + 2 * u) ^ n - 1) * (|dec z₀| + ∑ k ∈ Finset.range n, |dec (x k)|) := by
  induction n with
  | zero => simp [srsumF]
  | succ n ih =>
    rw [srsumF, Finset.sum_range_succ, Finset.sum_range_succ, ← add_assoc, ← add_assoc]
    have hST : |dec z₀ + ∑ k ∈ Finset.range n, dec (x k)| ≤
        |dec z₀| + ∑ k ∈ Finset.range n, |dec (x k)| :=
      (abs_add_le _ _).trans (by gcongr; exact Finset.abs_sum_le_sum_abs _ _)
    have hT : 0 ≤ |dec z₀| + ∑ k ∈ Finset.range n, |dec (x k)| :=
      add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hc : 0 ≤ (1 + 2 * u) ^ n - 1 := by
      have := one_le_pow₀ (show (1 : ℝ) ≤ 1 + 2 * u by linarith) (n := n)
      linarith
    have hc' : (1 + 2 * u) ^ (n + 1) - 1 = (1 + 2 * u) * ((1 + 2 * u) ^ n - 1 + 1) - 1 := by ring
    rw [hc']
    have h2 := hg.sure (srsumF g z₀ x τ p n) (x n) (τ (p + n))
    generalize (1 + 2 * u) ^ n - 1 = c at ih hc
    generalize dec z₀ + ∑ k ∈ Finset.range n, dec (x k) = S at ih hST
    generalize |dec z₀| + ∑ k ∈ Finset.range n, |dec (x k)| = T at ih hST hT
    generalize dec (g (srsumF g z₀ x τ p n) (x n) (τ (p + n))) = s' at h2
    generalize dec (srsumF g z₀ x τ p n) = s at ih h2
    generalize dec (x n) = y at h2
    have hs : |s| ≤ T + c * T := by
      have := abs_add_le S (s - S)
      rw [add_sub_cancel] at this
      linarith
    have hA : |s' - (s + y)| ≤ 2 * u * (T + c * T + |y|) :=
      h2.trans (mul_le_mul_of_nonneg_left ((abs_add_le s y).trans (by linarith)) (by linarith))
    have h3 : |s' - (S + y)| ≤ |s' - (s + y)| + |s - S| := by
      have := abs_add_le (s' - (s + y)) (s - S)
      rwa [show s' - (s + y) + (s - S) = s' - (S + y) by ring] at this
    nlinarith [mul_nonneg hu hT, mul_nonneg hc hT, mul_nonneg hu (mul_nonneg hc hT),
      mul_nonneg hc (abs_nonneg y), mul_nonneg hu (mul_nonneg hc (abs_nonneg y)),
      mul_nonneg hu (abs_nonneg y)]

/-- Each increment is conditionally unbiased up to `β u`, given the tape before its window: the
contract of the drawn operation at the value reached. -/
theorem abs_sum_dec_srsumF_div_sub_le {u β : ℝ} {dec : K → ℝ} {Ξ : Finset K} {g : K → K → K → K}
    (hg : SrModel u β dec Ξ g) (z₀ : K) (x τ : ℕ → K) (p k : ℕ) :
    |(∑ ξ ∈ Ξ, dec (g (srsumF g z₀ x τ p k) (x k) ξ)) / Ξ.card -
        (dec (srsumF g z₀ x τ p k) + dec (x k))| ≤
      β * u * |dec (srsumF g z₀ x τ p k) + dec (x k)| :=
  hg.unbiased _ _

variable [Inhabited K]

/-- **The abstract theorem of `srsum`**, for every interpretation meeting the drawn contract:
`n` calls, and the cell `z` holds the function `srsumF` of the `n` tape entries from the
position, which advances by `n`. -/
theorem runs_srsum {g : K → K → K → K} {J : Interp S1 K} (hJ : IsSrAddD g J)
    (W : S1 → List ℕ → ℕ) {τ : ℕ → K} {n : ℕ} {x z : ℕ × ℕ} {m : Mem K} {xs : List K} {z₀ : K}
    (hxz : x.1 ≠ z.1) (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hz : m.store.get z.1 z.2 = some z₀) :
    Runs J W τ srsum ⟨[n, x.2, z.2], [x.1, z.1]⟩ m (n • Count.one .sraddD []) (W .sraddD [])
      (· = (m.upd z (srsumF g z₀ (vec xs) τ m.pos n)).advance n) := by
  have hw : Wp .total J τ srsum ⟨[n, x.2, z.2], [x.1, z.1]⟩
      (· = (m.upd z (srsumF g z₀ (vec xs) τ m.pos n)).advance n) m := by
    refine wp_loop (k := n) rfl
      (fun i m' => m' = (m.upd z (srsumF g z₀ (vec xs) τ m.pos i)).advance i) ?_ ?_ fun _ h => h
    · simp [srsumF, Mem.upd, Mem.advance, Store.upd_of_get hz]
    · rintro i hi m' rfl
      refine wp_call_fn hJ (z := z) rfl rfl rfl trivial (drawBin_apply_of (a := srsumF g z₀ (vec xs)
        τ m.pos i) (b := vec xs i) (Store.get_upd_self (Store.lt_len_of_get hz) _) ?_ ?_) ?_
      · change (m.store.upd z.1 z.2 _).get x.1 (x.2 + i) = some _
        rw [Store.get_upd_of_ne (Or.inl hxz)]
        exact Store.get_of_readBlock hx hi default
      · change z.2 < (m.store.upd z.1 z.2 _).len z.1
        rw [Store.len_upd]
        exact Store.lt_len_of_get hz
      · simp [Mem.upd, Mem.advance, srsumF, add_assoc]
  obtain ⟨m', hrun, hpost⟩ := hw
  refine (Runs.of_run hrun hpost W).mono (by simp [srsum, staticCost, useCost]) ?_ fun _ h => h
  simp only [srsum, staticPeak, IExp.evalList_nil, Option.map_some, Option.getD_some]
  exact Finset.sup_le fun _ _ => le_rfl

/-- **The concrete corollary**: the sum over the program that draws and calls `sradd`, by one
application of the linking theorem: `n` draws and `n` `sradd`, one scratch cell, the result is
`srsumF f` of the tape, and it meets the sure bound of `abs_dec_srsumF_sub_le` for every tape. -/
theorem runs_srsum_link {f : K → K → K → K} {I : Interp S0 K} (hI : IsSrAdd f I) {u β : ℝ}
    {dec : K → ℝ} {Ξ : Finset K} (hf : SrModel u β dec Ξ f) (hu : 0 ≤ u) {τ : ℕ → K} {n : ℕ}
    {x z : ℕ × ℕ} {m : Mem K} {xs : List K} {z₀ : K} (hxz : x.1 ≠ z.1)
    (hx : m.store.readBlock x.1 x.2 n = some xs) (hz : m.store.get z.1 z.2 = some z₀) :
    Runs I (fun _ _ => 0) τ (srsum.link srTable) ⟨[n, x.2, z.2], [x.1, z.1]⟩ m
      (n • (Count.one .draw [] + Count.one .sradd [])) 1
      fun m' => ∃ v, m' = (m.upd z v).advance n ∧
        |dec v - (dec z₀ + ∑ k ∈ Finset.range n, dec (vec xs k))| ≤
          ((1 + 2 * u) ^ n - 1) * (|dec z₀| + ∑ k ∈ Finset.range n, |dec (vec xs k)|) :=
  ((runs_srsum (isSrAddD_link hI) (fun _ _ => 1) hxz hx hz).link (sr_accounts I)).mono
    (by simp [srCost]) le_rfl fun _ h => ⟨_, h, abs_dec_srsumF_sub_le hf hu _ _ _ _ _⟩

/-! ### Witness -/

/-- A stochastic rounding of real numbers with a relative perturbation `± u`: up for the random
word `0`, down otherwise. -/
noncomputable def srExact (u : ℝ) (a b ξ : ℝ) : ℝ := (a + b) * if ξ = 0 then 1 + u else 1 - u

theorem srModel_srExact {u β : ℝ} (hu : 0 ≤ u) (hβ : 0 ≤ β) :
    SrModel u β id {0, 1} (srExact u) where
  sure a b ξ := by
    have h : srExact u a b ξ - (a + b) = (a + b) * if ξ = 0 then u else -u := by
      unfold srExact
      split_ifs <;> ring
    simp only [id, h, abs_mul]
    have : |if ξ = 0 then u else -u| = u := by split_ifs <;> simp [abs_of_nonneg hu]
    rw [this]
    nlinarith [abs_nonneg (a + b)]
  unbiased a b := by
    have h : (∑ ξ ∈ ({0, 1} : Finset ℝ), id (srExact u a b ξ)) / ({0, 1} : Finset ℝ).card -
        (id a + id b) = 0 := by
      simp [srExact]
      ring
    rw [h, abs_zero]
    exact mul_nonneg (mul_nonneg hβ hu) (abs_nonneg _)

/-- **Witness**: for all `u, β ≥ 0` there are a stochastic rounding function meeting `SrModel`
and an interpretation meeting the explicit contract, with tape-local operations; hence also the
drawn contract, by linking. -/
theorem exists_isSrAdd {u β : ℝ} (hu : 0 ≤ u) (hβ : 0 ≤ β) :
    ∃ (K : Type) (dec : K → ℝ) (Ξ : Finset K) (f : K → K → K → K) (I : Interp S0 K),
      SrModel u β dec Ξ f ∧ IsSrAdd f I ∧ (∀ o, I.TapeLocal o (srWindow o)) ∧
        IsSrAddD f (I.link srTable) := by
  let F : S0 → BlockFn ℝ := fun o => match o with
    | .draw => .draw
    | .sradd => .tern fun a b ξ => some (srExact u a b ξ)
  have hI : IsSrAdd (srExact u) (Interp.ofFns F) :=
    ⟨Interp.ofFns_isFn F _ .sradd _, Interp.ofFns_isFn F _ .draw _⟩
  refine ⟨ℝ, id, {0, 1}, srExact u, Interp.ofFns F, srModel_srExact hu hβ, hI, fun o => ?_,
    isSrAddD_link hI⟩
  cases o <;> exact Interp.ofFns_tapeLocal F _

end NLAlib.Ops.Examples
