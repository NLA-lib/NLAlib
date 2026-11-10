/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Dot
public import NLAlib.Ops.Law

/-!
# Example: stochastic rounding, as an operation with hidden randomness

**At the level of an algorithm** the stochastically rounded addition is `srAdd [x, y] [z]`: two
operands, no random operand. Its contract (`NLAlib.Ops.Examples.IsSrAdd`, with the mathematics
`NLAlib.Ops.Examples.SrModel`) is conditional on the history: the result is a function `g` of
the two operands and of one entry of the tape that the operation reads for itself; for every
pair of operands, over a fresh uniform draw, the result is within `2 u` of the sum surely and
has the sum as its mean.

**Inside the implementation** only, there is a primitive `sraddXi [x, y, ξ] [z]` that is given
its random word: `srAdd` is implemented by "draw `ξ` into scratch; `sraddXi`". The scratch cell
is freed at the end of the call; no cell of the algorithm ever holds `ξ`.

The algorithm is the stochastically rounded sum `NLAlib.Ops.Examples.srsum`.

## Main results

* `NLAlib.Ops.Examples.integral_dec_srsumF`: **the stochastically rounded sum is unbiased**,
  `𝔼 ŝ = s`, by the conditional law of each window given the past; with the sure bound
  `NLAlib.Ops.Examples.abs_dec_srsumF_sub_le`. Mathematics.
* `NLAlib.Ops.Examples.runsLaw_srsum`: the abstract theorem, for every interpretation meeting
  the contract of `srAdd` and every law of the tape: `n` calls, the workspace of one, the sure
  bound for every sample and `𝔼 ŝ = s`.
* `NLAlib.Ops.Examples.sr_certifies`: the certificate of the profile (contract by linking,
  counts, window by the window lemma).
* `NLAlib.Ops.Examples.runsLaw_srsum_link`: the corollary for the program that draws, one
  application of `Profile.Certifies.runsLaw`: `n` draws, `n` `sraddXi`, one scratch cell.
* `NLAlib.Ops.Examples.exists_isSrLo`: the contracts can be met.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.Ops.Examples

variable {K : Type}

/-- The lower signature: a draw, and the stochastically rounded addition given its random word.
The second is a primitive for implementations; an algorithm does not call it. -/
inductive SrLo where
  /-- `draw [] [] [t]`: the next entry of the uniform stream. -/
  | draw
  /-- `sraddXi [] [x, y, ξ] [z]`. -/
  | sraddXi
  deriving DecidableEq

/-- The signature of the algorithm: the stochastically rounded addition. -/
inductive SrOp where
  /-- `srAdd [] [x, y] [z]`: no random operand. -/
  | srAdd
  deriving DecidableEq

/-! ### Mathematics: the contract of a stochastic rounding function -/

/-- **Stochastic rounding of a sum**, as a property of a function `f` of the summands and the
random word: surely within `2 u` relative; unbiased, for the random word of the law `μ`. -/
structure SrModel [MeasurableSpace K] (u : ℝ) (dec : K → ℝ) (μ : Measure K)
    (f : K → K → K → K) : Prop where
  /-- Decoding is measurable. -/
  measurable_dec : Measurable dec
  /-- The rounding is measurable in the first summand and the random word. -/
  measurable : ∀ b, Measurable fun q : K × K => f q.1 b q.2
  /-- The sure bound. -/
  sure : ∀ a b ξ, |dec (f a b ξ) - (dec a + dec b)| ≤ 2 * u * |dec a + dec b|
  /-- Unbiasedness, given the summands. -/
  unbiased : ∀ a b, ∫ ξ, dec (f a b ξ) ∂μ = dec a + dec b

/-! ### The two contracts -/

/-- **Below**: `sraddXi` is the function `f` of three cells; `draw` is the uniform draw. -/
structure IsSrLo (f : K → K → K → K) (I : Interp SrLo Empty K) : Prop where
  /-- `sraddXi` is `f`. -/
  sraddXi : I.IsFn .total .sraddXi (.tern fun a b ξ => some (f a b ξ)) AnyOperands
  /-- `draw` is the draw of the model, in the uniform stream. -/
  draw : I.IsFn .total .draw (.draw Stream.unif) AnyOperands

/-- The block function of an operation of two cells with one hidden uniform draw: the result is
`g` of the operands and of the window entry. -/
def drawBin (g : K → K → K → K) : BlockFn K where
  nd := 0
  stream := Stream.unif
  win _ := 1
  inLens _ := [1, 1]
  outLens _ := [1]
  fn _ w xs := match w, xs with
    | [ξ], [[a], [b]] => some [[g a b ξ]]
    | _, _ => none

/-- A call of `drawBin`, on cells. -/
theorem drawBin_apply_of {g : K → K → K → K} {x y z : ℕ × ℕ} {τ : Tape K} {m : Mem K} {a b : K}
    (hx : m.store.get x.1 x.2 = some a) (hy : m.store.get y.1 y.2 = some b)
    (hz : z.2 < m.store.len z.1) :
    (drawBin g).apply [] [x, y] [z] τ m =
      some ((m.upd z (g a b (τ m.pos Stream.unif))).advance 1) :=
  BlockFn.apply_eq_some_iff.mpr ⟨rfl, by simp [Store.lt_length_of_get hx,
    Store.lt_length_of_get hy, Store.lt_length_of_lt_len hz], [[a], [b]],
    [[g a b (τ m.pos Stream.unif)]], BlockFn.readBlocks_cells_two.mpr ⟨a, b, hx, hy, rfl⟩,
    by simp [drawBin, Tape.window_one], rfl, ⟨hz, trivial⟩, rfl⟩

/-- What a successful call of `drawBin` is. -/
theorem drawBin_apply {g : K → K → K → K} {d : List ℕ} {ins outs : List (ℕ × ℕ)}
    {τ : Tape K} {m m' : Mem K} (h : (drawBin g).apply d ins outs τ m = some m') :
    ∃ x y z a b, d = [] ∧ ins = [x, y] ∧ outs = [z] ∧ m.store.get x.1 x.2 = some a ∧
      m.store.get y.1 y.2 = some b ∧ z.2 < m.store.len z.1 ∧
      m' = (m.upd z (g a b (τ m.pos Stream.unif))).advance 1 := by
  obtain ⟨hnd, hlive, X, v, hread, hfn, hlen, hroom, rfl⟩ := BlockFn.apply_eq_some_iff.mp h
  obtain rfl : d = [] := List.length_eq_zero_iff.mp hnd
  obtain ⟨x, y, xs, ys, rfl, hx, hy, rfl⟩ := Mem.readBlocks_two hread
  obtain ⟨z, rfl, hz⟩ := Mem.room_one hroom
  rw [BlockFn.readBlock_one] at hx hy
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hy
  simp only [drawBin, Tape.window_one, Option.some.injEq] at hfn
  subst hfn
  exact ⟨x, y, z, a, b, rfl, rfl, rfl, ha, hb, hz, rfl⟩

/-- **The contract of `srAdd`**, conditional on the history: at every memory the result is the
function `g` of the two operands and of the next entry of the uniform stream, which the
operation consumes. With `SrModel` for `g` and the law of the tape, this is: given everything
computed so far, the result is within `2 u` of the sum and unbiased. -/
def IsSrAdd (g : K → K → K → K) (J : Interp SrOp Empty K) : Prop :=
  J.IsFn .total .srAdd (drawBin g) AnyOperands

/-! ### The drawing implementation and its profile -/

/-- **The implementation of `srAdd`**: draw into a scratch cell, then `sraddXi`. Index
variables: the offsets of `x`, `y`, `z`. -/
def srAddImpl : Impl SrLo Empty where
  nd := 0
  nin := 2
  nout := 1
  body := .alloc (.const 1) (.seq (.call .draw [] [] [⟨3, .const 0⟩])
    (.call .sraddXi [] [⟨0, .var 0⟩, ⟨1, .var 1⟩, ⟨3, .const 0⟩] [⟨2, .var 2⟩]))

/-- The table: `srAdd` by the drawing program. -/
def srTable : Table SrOp SrLo Empty
  | .srAdd => .inl srAddImpl

/-- **The exact certificate of the drawing program**: its run is the block function of `f` with
the window entry as random word. -/
theorem srAdd_cert {f : K → K → K → K} {I : Interp SrLo Empty K} (hI : IsSrLo f I) {d : List ℕ}
    {ins outs : List (ℕ × ℕ)} {τ : Tape K} {m m' : Mem K}
    (h : (drawBin f).apply d ins outs τ m = some m') :
    srAddImpl.Fits d.length ins.length outs.length ∧
      run I τ srAddImpl.body (Env.frame d (ins ++ outs)) m = some m' := by
  obtain ⟨x, y, z, a, b, rfl, rfl, rfl, hx, hy, hz, rfl⟩ := drawBin_apply h
  obtain ⟨s, p⟩ := m
  have hbz : z.1 < s.length := Store.lt_length_of_lt_len hz
  refine ⟨⟨rfl, rfl, rfl⟩, run_of_wp (wp_alloc rfl (wp_seq (wp_call_draw hI.draw
    (z := (s.length, 0)) rfl rfl rfl trivial ?_ ?_)))⟩
  · change 0 < (s ++ [List.replicate 1 none]).len s.length
    simp
  have e1 : ((⟨s.push 1, p⟩ : Mem K).upd (s.length, 0) (τ p Stream.unif)).advance 1 =
      ⟨s ++ [[some (τ p Stream.unif)]], p + 1⟩ := by
    simp only [Mem.upd, Mem.advance, Store.push]
    rw [Store.upd_append_top]
    rfl
  rw [e1]
  refine wp_call_tern hI.sraddXi (x := x) (y := y) (w := (s.length, 0)) (z := z) rfl rfl rfl
    trivial (a := a) (b := b) (c := τ p Stream.unif) ?_ ?_ ?_ rfl ?_ ?_
  · change (s ++ [_]).get x.1 x.2 = some a
    rw [Store.get_append_of_lt (Store.lt_length_of_get hx)]
    exact hx
  · change (s ++ [_]).get y.1 y.2 = some b
    rw [Store.get_append_of_lt (Store.lt_length_of_get hy)]
    exact hy
  · change (s ++ [[some (τ p Stream.unif)]]).get s.length 0 = some (τ p Stream.unif)
    rw [Store.get_append_top]
    rfl
  · change z.2 < (s ++ [_]).len z.1
    rwa [Store.len_append_of_lt hbz]
  · simp only [Mem.upd, Mem.advance]
    rw [Store.upd_append_of_lt hbz, Store.pop_append_top]

/-- **The contract by linking**: the induced interpretation meets the contract of `srAdd` with
the same function `f`. -/
theorem isSrAdd_link {f : K → K → K → K} {I : Interp SrLo Empty K} (hI : IsSrLo f I) :
    IsSrAdd f (I.link srTable) :=
  Interp.link_isFn rfl fun _ _ _ _ _ _ _ h => srAdd_cert hI h

/-- The tape windows of the lower operations, registered with the access model: one entry for a
draw, none for `sraddXi`. -/
def srWindow : SrLo → List ℕ → ℕ
  | .draw, _ => 1
  | .sraddXi, _ => 0

/-- **The profile of stochastic rounding by a drawing program**: one draw and one `sraddXi` per
`srAdd`, one scratch cell, a window of one entry. -/
noncomputable def srProfile : Profile SrOp SrLo Empty where
  table := srTable
  cost _ _ := Count.one .draw [] + Count.one .sraddXi []
  ws _ _ := 1
  wsLo _ _ := 0
  win _ _ := 1
  winLo := srWindow

/-- **The certificate of the profile.** The window is given by the window lemma: the scratch
draw of the implementation is the one entry the law of the tape assigns to the call. -/
theorem sr_certifies (f : K → K → K → K) : srProfile.Certifies (IsSrLo f) (IsSrAdd f) := by
  refine .of_accounts (fun I hI => isSrAdd_link hI) (fun I => Table.accounts_of_static ?_
    (fun o o' hT => by cases o; cases hT) I) fun I _ hloc o => ?_
  · intro o R hT d offs hd ho
    cases o
    cases hT
    obtain rfl := List.length_eq_zero_iff.mp hd
    obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp ho
    simp [srProfile, srAddImpl, staticCost, staticPeak, useCost]
  · cases o
    exact Interp.TapeLocal.link hloc (o := SrOp.srAdd) rfl (by simp [Stmt.Straight, srAddImpl])
      fun d offs hd ho => by
        obtain rfl := List.length_eq_zero_iff.mp hd
        obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp ho
        simp [staticWindow, srAddImpl, srProfile, srWindow]

/-! ### The algorithm: the stochastically rounded sum -/

/-- `z := z ⊕ x_0 ⊕ … ⊕ x_{n-1}` with stochastically rounded additions. Index variables: `n`,
the offsets of `x`, `z`, then the loop variable. The tree has no draw and no random operand. -/
def srsum : Stmt SrOp Empty :=
  .loop (.var 0) (.call .srAdd [] [⟨1, .var 2⟩, ⟨0, .var 1 + .var 3⟩] [⟨1, .var 2⟩])

/-- The stochastically rounded sum as a function of the tape entries from the position `p`. -/
def srsumF (g : K → K → K → K) (z₀ : K) (x : ℕ → K) (τ : Tape K) (p : ℕ) : ℕ → K
  | 0 => z₀
  | k + 1 => g (srsumF g z₀ x τ p k) (x k) (τ (p + k) Stream.unif)

section Math

variable [MeasurableSpace K]

/-- **The sure error of the stochastically rounded sum**, for every tape. -/
theorem abs_dec_srsumF_sub_le {u : ℝ} {dec : K → ℝ} {μ : Measure K} {g : K → K → K → K}
    (hg : SrModel u dec μ g) (hu : 0 ≤ u) (z₀ : K) (x : ℕ → K) (τ : Tape K) (p n : ℕ) :
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
    have h2 := hg.sure (srsumF g z₀ x τ p n) (x n) (τ (p + n) Stream.unif)
    generalize (1 + 2 * u) ^ n - 1 = c at ih hc
    generalize dec z₀ + ∑ k ∈ Finset.range n, dec (x k) = S at ih hST
    generalize |dec z₀| + ∑ k ∈ Finset.range n, |dec (x k)| = T at ih hST hT
    generalize dec (g (srsumF g z₀ x τ p n) (x n) (τ (p + n) Stream.unif)) = s' at h2
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

/-- The partial sum after `n` additions is a function of the tape before the position `p + n`. -/
theorem measurable_srsumF {u : ℝ} {dec : K → ℝ} {μ : Measure K} {g : K → K → K → K}
    (hg : SrModel u dec μ g) {Ω : Type} (ξ : Ω → Tape K) (z₀ : K) (x : ℕ → K) (p n : ℕ) :
    Measurable[Tape.past ξ (p + n)] fun ω => srsumF g z₀ x (ξ ω) p n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (hg.measurable (x n)).comp ((ih.mono (Tape.past_mono (by omega)) le_rfl).prodMk
      (Tape.measurable_entry (Set.mem_Iio.mpr (by omega)) Stream.unif))

/-- **The stochastically rounded sum is unbiased**, for every law of the tape whose uniform
stream has the law of `SrModel`. Each addition is unbiased given the past of its position
(`IsTapeLaw.integral_entry`); the sure bound gives the integrability. -/
theorem integral_dec_srsumF {u : ℝ} {dec : K → ℝ} {law : ℕ → Measure K} {g : K → K → K → K}
    (hg : SrModel u dec (law Stream.unif) g) (hu : 0 ≤ u) {Ω : Type} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {ξ : Ω → Tape K} (h : IsTapeLaw law P ξ) (z₀ : K) (x : ℕ → K) (p n : ℕ) :
    ∫ ω, dec (srsumF g z₀ x (ξ ω) p n) ∂P = dec z₀ + ∑ k ∈ Finset.range n, dec (x k) := by
  have := h.isProbabilityMeasure
  have hint : ∀ n, Integrable (fun ω => dec (srsumF g z₀ x (ξ ω) p n)) P := fun n => by
    refine Integrable.of_bound (hg.measurable_dec.comp ((measurable_srsumF hg ξ z₀ x p n).mono
      (h.sigma_le _) le_rfl)).aestronglyMeasurable
      (|dec z₀ + ∑ k ∈ Finset.range n, dec (x k)| + ((1 + 2 * u) ^ n - 1) *
        (|dec z₀| + ∑ k ∈ Finset.range n, |dec (x k)|)) (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := abs_dec_srsumF_sub_le hg hu z₀ x (ξ ω) p n
    have h2 := abs_add_le (dec (srsumF g z₀ x (ξ ω) p n) -
      (dec z₀ + ∑ k ∈ Finset.range n, dec (x k))) (dec z₀ + ∑ k ∈ Finset.range n, dec (x k))
    rw [sub_add_cancel] at h2
    rw [Real.norm_eq_abs]
    linarith
  induction n with
  | zero => simp [srsumF]
  | succ n ih =>
    have key := h.integral_entry (measurable_srsumF hg ξ z₀ x p n) Stream.unif
      (φ := fun a ζ => dec (g a (x n) ζ)) (hg.measurable_dec.comp (hg.measurable (x n)))
      (hint (n + 1))
    simp only [srsumF] at key ⊢
    rw [key]
    simp only [hg.unbiased]
    rw [integral_add (hint n) (integrable_const _), ih, integral_const, Finset.sum_range_succ]
    simp [add_assoc]

end Math

section Runs

variable [Inhabited K]

/-- **The run of `srsum`**, for every interpretation meeting the contract of `srAdd` and every
tape: `n` calls, and the cell `z` holds the function `srsumF` of the `n` tape entries from the
position, which advances by `n`. -/
theorem runs_srsum {g : K → K → K → K} {J : Interp SrOp Empty K} (hJ : IsSrAdd g J)
    (W : SrOp → List ℕ → ℕ) {τ : Tape K} {n : ℕ} {x z : ℕ × ℕ} {m : Mem K} {xs : List K} {z₀ : K}
    (hxz : x.1 ≠ z.1) (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hz : m.store.get z.1 z.2 = some z₀) :
    Runs J W τ srsum ⟨[n, x.2, z.2], [x.1, z.1]⟩ m (n • Count.one .srAdd []) (W .srAdd [])
      (· = (m.upd z (srsumF g z₀ (vec xs) τ m.pos n)).advance n) := by
  have hw : Wp .total J τ srsum ⟨[n, x.2, z.2], [x.1, z.1]⟩
      (· = (m.upd z (srsumF g z₀ (vec xs) τ m.pos n)).advance n) m := by
    refine wp_loop (k := n) rfl
      (fun i m' => m' = (m.upd z (srsumF g z₀ (vec xs) τ m.pos i)).advance i) ?_ ?_ fun _ h => h
    · simp [srsumF, Mem.upd, Mem.advance, Store.upd_of_get hz]
    · rintro i hi m' rfl
      refine wp_call_fn hJ (b := [z]) rfl rfl rfl trivial (drawBin_apply_of
        (a := srsumF g z₀ (vec xs) τ m.pos i) (b := vec xs i)
        (Store.get_upd_self (Store.lt_len_of_get hz) _) ?_ ?_) ?_
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

variable [MeasurableSpace K]

/-- The postcondition of `srsum` for the computed sum `v`: the cell `z` holds a word that decodes
to `v`, the position has advanced by `n`, and `v` is within the sure bound of the sum. -/
def SrsumPost (dec : K → ℝ) (u : ℝ) (n : ℕ) (z : ℕ × ℕ) (z₀ : K) (xs : List K) (m : Mem K)
    (v : ℝ) (m' : Mem K) : Prop :=
  ∃ w, m' = (m.upd z w).advance n ∧ dec w = v ∧
    |v - (dec z₀ + ∑ k ∈ Finset.range n, dec (vec xs k))| ≤
      ((1 + 2 * u) ^ n - 1) * (|dec z₀| + ∑ k ∈ Finset.range n, |dec (vec xs k)|)

/-- **The abstract theorem of `srsum`**, for every interpretation meeting the contract of
`srAdd` and every law of the tape: for every sample, `n` calls within the workspace of one and
the sure bound; and the computed sum is unbiased, `𝔼 ŝ = s`. -/
theorem runsLaw_srsum {g : K → K → K → K} {J : Interp SrOp Empty K} (hJ : IsSrAdd g J) {u : ℝ}
    {dec : K → ℝ} {law : ℕ → Measure K} (hg : SrModel u dec (law Stream.unif) g) (hu : 0 ≤ u)
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ξ : Ω → Tape K} (h : IsTapeLaw law P ξ)
    (W : SrOp → List ℕ → ℕ) {n : ℕ} {x z : ℕ × ℕ} {m : Mem K} {xs : List K} {z₀ : K}
    (hxz : x.1 ≠ z.1) (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hz : m.store.get z.1 z.2 = some z₀) :
    RunsLaw J W ξ srsum ⟨[n, x.2, z.2], [x.1, z.1]⟩ m (n • Count.one .srAdd []) (W .srAdd [])
      (SrsumPost dec u n z z₀ xs m)
      fun X => ∫ ω, X ω ∂P = dec z₀ + ∑ k ∈ Finset.range n, dec (vec xs k) :=
  ⟨fun ω => dec (srsumF g z₀ (vec xs) (ξ ω) m.pos n), fun _ =>
    (runs_srsum hJ W hxz hx hz).mono le_rfl le_rfl fun _ hm =>
      ⟨_, hm, rfl, abs_dec_srsumF_sub_le hg hu _ _ _ _ _⟩,
    integral_dec_srsumF hg hu h _ _ _ _⟩

/-- **The corollary for the program that draws**, one application of the law-level linking
lemma: `n` draws and `n` `sraddXi`, one scratch cell, the sure bound for every sample, and
`𝔼 ŝ = s`. -/
theorem runsLaw_srsum_link {f : K → K → K → K} {I : Interp SrLo Empty K} (hI : IsSrLo f I)
    (hloc : ∀ o, I.TapeLocal o (srWindow o)) {u : ℝ} {dec : K → ℝ} {law : ℕ → Measure K}
    (hf : SrModel u dec (law Stream.unif) f) (hu : 0 ≤ u) {Ω : Type} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {ξ : Ω → Tape K} (h : IsTapeLaw law P ξ) {n : ℕ} {x z : ℕ × ℕ} {m : Mem K}
    {xs : List K} {z₀ : K} (hxz : x.1 ≠ z.1) (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hz : m.store.get z.1 z.2 = some z₀) :
    RunsLaw I (fun _ _ => 0) ξ (srsum.link srTable) ⟨[n, x.2, z.2], [x.1, z.1]⟩ m
      (n • (Count.one .draw [] + Count.one .sraddXi [])) 1 (SrsumPost dec u n z z₀ xs m)
      fun X => ∫ ω, X ω ∂P = dec z₀ + ∑ k ∈ Finset.range n, dec (vec xs k) := by
  have := (sr_certifies f).runsLaw (ξ := ξ)
    (fun J hJ _ => runsLaw_srsum hJ hf hu h _ hxz hx hz) hI hloc
  simpa [srProfile] using this

end Runs

/-! ### Witness -/

/-- A stochastic rounding of real numbers, for any law `μ` of the random word: a relative
perturbation `u (c ξ - 𝔼 c)` with `c` the clamp to `[-1/2, 1/2]`. -/
noncomputable def srWit (u : ℝ) (μ : Measure ℝ) (a b ξ : ℝ) : ℝ :=
  (a + b) * (1 + u * (max (-1 / 2) (min (1 / 2) ξ) - ∫ ζ, max (-1 / 2) (min (1 / 2) ζ) ∂μ))

theorem srModel_srWit {u : ℝ} (hu : 0 ≤ u) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    SrModel u id μ (srWit u μ) := by
  have hc : ∀ ζ : ℝ, |max (-1 / 2) (min (1 / 2) ζ)| ≤ 1 / 2 := fun ζ =>
    abs_le.mpr ⟨by have := le_max_left (-1 / 2 : ℝ) (min (1 / 2) ζ); linarith,
      max_le (by norm_num) (min_le_left _ _)⟩
  have hm : Measurable fun ζ : ℝ => max (-1 / 2) (min (1 / 2) ζ) :=
    measurable_const.max (measurable_const.min measurable_id)
  have hi : Integrable (fun ζ : ℝ => max (-1 / 2) (min (1 / 2) ζ)) μ :=
    Integrable.of_bound hm.aestronglyMeasurable (1 / 2) (Filter.Eventually.of_forall hc)
  have hE : |∫ ζ, max (-1 / 2) (min (1 / 2) ζ) ∂μ| ≤ 1 / 2 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (C := 1 / 2)
      (Filter.Eventually.of_forall fun ζ => (Real.norm_eq_abs _).le.trans (hc ζ))
    simpa using this
  refine ⟨measurable_id, fun b => ?_, fun a b ξ => ?_, fun a b => ?_⟩
  · unfold srWit
    exact (measurable_fst.add measurable_const).mul (measurable_const.add (measurable_const.mul
      ((hm.comp measurable_snd).sub measurable_const)))
  · have e : srWit u μ a b ξ - (a + b) = (a + b) * (u * (max (-1 / 2) (min (1 / 2) ξ) -
        ∫ ζ, max (-1 / 2) (min (1 / 2) ζ) ∂μ)) := by
      unfold srWit
      ring
    have h1 := abs_sub (max (-1 / 2) (min (1 / 2) ξ)) (∫ ζ, max (-1 / 2) (min (1 / 2) ζ) ∂μ)
    have h2 := hc ξ
    simp only [id, e, abs_mul, abs_of_nonneg hu]
    nlinarith [abs_nonneg (a + b), mul_nonneg hu (abs_nonneg (a + b))]
  · simp only [id, srWit]
    have h1 : Integrable (fun ξ => u * (max (-1 / 2) (min (1 / 2) ξ) -
        ∫ ζ, max (-1 / 2) (min (1 / 2) ζ) ∂μ)) μ := (hi.sub (integrable_const _)).const_mul u
    rw [integral_const_mul, integral_add (integrable_const _) h1, integral_const_mul,
      integral_sub hi (integrable_const _)]
    simp

/-- **Witness**: for every `u ≥ 0` and every law of the uniform stream there are a stochastic
rounding function meeting `SrModel` and an interpretation meeting the lower contract with
tape-local operations; hence also the contract of `srAdd`, by linking. -/
theorem exists_isSrLo {u : ℝ} (hu : 0 ≤ u) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ (f : ℝ → ℝ → ℝ → ℝ) (I : Interp SrLo Empty ℝ),
      SrModel u id μ f ∧ IsSrLo f I ∧ (∀ o, I.TapeLocal o (srWindow o)) ∧
        IsSrAdd f (I.link srTable) := by
  let F : SrLo → BlockFn ℝ := fun o => match o with
    | .draw => .draw Stream.unif
    | .sraddXi => .tern fun a b ξ => some (srWit u μ a b ξ)
  have hI : IsSrLo (srWit u μ) (Interp.ofFns F) :=
    ⟨Interp.ofFns_isFn F _ .sraddXi _, Interp.ofFns_isFn F _ .draw _⟩
  refine ⟨srWit u μ, Interp.ofFns F, srModel_srWit hu μ, hI, fun o => ?_, isSrAdd_link hI⟩
  cases o <;> exact Interp.ofFns_tapeLocal F _

end NLAlib.Ops.Examples
