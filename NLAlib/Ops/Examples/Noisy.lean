/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Random
public import NLAlib.Ops.Examples.NoisyMath
public import NLAlib.Ops.Law

/-!
# Test case: a noisy product by a matrix (hidden randomness)

At the level of the algorithm the noisy product is `nmv [n] [x] [y]`: one input block, one
output block, **no random operand**. Its contract (`NLAlib.Ops.Examples.IsNoisy`, with the
mathematics `NLAlib.Ops.Examples.IsNoisyMv`) is conditional on the history: the output decodes
to `N v w`, where `v` is the decoded input and `w` is a window of the tape that the operation
reads for itself; given `v`, over a fresh window, `N v w` has the law of `A v + σ ‖v‖ g`.

The algorithm `NLAlib.Ops.Examples.npow` is the noisy power iteration, `2 k` products that
alternate between two blocks. Each input is the previous output, so it depends on all the
earlier noise.

## Main results

* `NLAlib.Ops.Examples.runs_npow`: the run, for every interpretation meeting the contract and
  every tape: `2 k` calls, the workspace of one call, the result is `noisyIter` of the tape.
* `NLAlib.Ops.Examples.runsLaw_npow`: **the abstract theorem**, for every law of the tape:
  `𝔼 x = A^(2k) x₀` and `𝔼 ‖x‖² ≤ (a + n σ²)^(2k) ‖x₀‖²`.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.Ops.Examples

variable {K Tst : Type}

/-- The signature of the algorithm: the noisy product. -/
inductive NOp where
  /-- `nmv [n] [x] [y]`: `y := A x + noise`. No random operand. -/
  | nmv
  deriving DecidableEq

variable [Inhabited K] {n : ℕ}

/-- **The noisy product in operand form**: the output block decodes to `N` of the decoded input
block and of the window of `n` Gaussian entries at the position, which the call consumes. -/
def nmvRel (dec : K → ℝ) (N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ) : WinRel K where
  nd := 1
  stream := Stream.gauss
  win d := d.headD 0
  inLens d := [d.headD 0]
  outLen d := d.headD 0
  rel _ X w ys := match X with
    | [xs] => decv dec n ys = N (decv dec n xs) fun i => vec w i
    | _ => False

@[storeNF] theorem nmvRel_inLens (dec : K → ℝ) (N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ)
    (d : List ℕ) : (nmvRel dec N).inLens d = [d.headD 0] := rfl

/-- **The contract of `nmv`**, conditional on the history: at every memory, the output is `N` of
the input and of a window that only the operation reads. -/
def IsNoisy (dec : K → ℝ) (N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ)
    (J : Interp NOp Tst K) : Prop :=
  J.Meets .total .nmv ((nmvRel dec N).spec (OutApart (· = n)))

/-- **The noisy power iteration**: `k` rounds of `y := nmv x; x := nmv y`. Index variables: `k`,
`n`, the offsets of `x`, `y`, then the loop variable; buffer variables: `x`, `y`. The tree has
no draw. -/
def npow : Stmt NOp Tst :=
  .loop (.var 0) (.seq (.call .nmv [.var 1] [⟨0, .var 2⟩] [⟨1, .var 3⟩])
    (.call .nmv [.var 1] [⟨1, .var 3⟩] [⟨0, .var 2⟩]))

/-- The call counts of `npow`: `2 k` noisy products. -/
noncomputable def npowCount (k n : ℕ) : Count NOp Tst := k • (2 • Count.one .nmv [n])

theorem staticCost_npow (k n a b : ℕ) :
    staticCost (npow (Tst := Tst)) [k, n, a, b] = npowCount k n := by
  simp [npow, staticCost, useCost, npowCount, two_nsmul]

theorem staticPeak_npow_le (W : NOp → List ℕ → ℕ) (k n a b : ℕ) :
    staticPeak W (npow (Tst := Tst)) [k, n, a, b] ≤ W .nmv [n] := by
  simp only [npow, staticPeak]
  exact Finset.sup_le fun i _ => by simp

omit [Inhabited K] in
theorem vec_window_eq_windowFn [Inhabited K] (τ : Tape K) (s q n : ℕ) :
    (fun i : Fin n => vec (τ.window s q n) i) = Tape.windowFn τ s q n :=
  funext fun i => vec_window τ s q i.2

/-- The postcondition of `npow` for the decoded result `v`: the block `x` decodes to `v`, the
position has advanced by `2 k n`, and nothing is written outside the two blocks. -/
def NpowPost (dec : K → ℝ) (n k : ℕ) (x y : ℕ × ℕ) (m : Mem K) (v : Fin n → ℝ) (m' : Mem K) :
    Prop :=
  ∃ s' xs q, m' = ⟨s', q⟩ ∧ q = m.pos + 2 * k * n ∧
    m.store.EqOff (Store.inBlock x.1 x.2 n ⊔ Store.inBlock y.1 y.2 n) s' ∧
    s'.readBlock x.1 x.2 n = some xs ∧ decv dec n xs = v

/-- **The run of `npow`**, for every interpretation meeting the contract of `nmv` and every
tape: the block `x` decodes to the noisy power iteration of the tape entries from the position. -/
theorem wp_npow {dec : K → ℝ} {N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ}
    {J : Interp NOp Tst K} (hJ : IsNoisy dec N J) {τ : Tape K} {k : ℕ} {x y : ℕ × ℕ}
    {m : Mem K} {xs₀ : List K} (hxy : x.1 ≠ y.1) (hl : m.Live [x, y])
    (hx : m.store.readBlock x.1 x.2 n = some xs₀) (hxl : x.2 + n ≤ m.store.len x.1)
    (hy : y.2 + n ≤ m.store.len y.1) :
    Wp .total J τ npow ⟨[k, n, x.2, y.2], [x.1, y.1]⟩
      (NpowPost dec n k x y m (noisyIter N (decv dec n xs₀) τ m.pos (2 * k))) m := by
  obtain ⟨s, p⟩ := m
  obtain ⟨bx, ox⟩ := x
  obtain ⟨by', oy⟩ := y
  obtain ⟨hlx, hly⟩ : bx < s.length ∧ by' < s.length := by simpa using hl
  refine wp_loop (k := k) rfl (fun i m' => NpowPost dec n i (bx, ox) (by', oy) ⟨s, p⟩
    (noisyIter N (decv dec n xs₀) τ p (2 * i)) m')
    ⟨s, xs₀, p, rfl, by simp, Store.EqOff.refl _ _, hx, rfl⟩ ?_ fun _ h => h
  rintro i hi m' ⟨s', xs, q, rfl, rfl, hfr, hr, hdx⟩
  have hlen := hfr.length_eq
  have hlx' := hfr.len_eq bx
  have hly' := hfr.len_eq by'
  have hxl := Store.length_of_readBlock hr
  -- `y := nmv x`
  refine wp_seq (wp_call_win hJ (k := n) (l := n) rfl rfl rfl rfl rfl rfl
    ⟨rfl, by simpa using hxy⟩ ?_ (xs := [xs]) ?_ ?_ fun ys hyl hys => ?_)
  · store_simp
  · store_simp
  · store_simp
  -- `x := nmv y`
  refine wp_call_win hJ (k := n) (l := n) rfl rfl rfl rfl rfl rfl
    ⟨rfl, by simpa using hxy.symm⟩ ?_ (xs := [ys]) ?_ ?_ fun zs hzl hzs =>
    ⟨_, zs, _, rfl, by simp [Mem.advance, Mem.updBlock]; ring,
      (hfr.updBlock fun j hj => Or.inr ⟨rfl, by omega, by omega⟩).updBlock
        fun j hj => Or.inl ⟨rfl, by omega, by omega⟩, ?_, ?_⟩
  · store_simp
  · store_simp
  · store_simp
  · store_simp
  · have hys' : decv dec n ys = N (decv dec n xs)
        fun j => vec (τ.window Stream.gauss (p + 2 * i * n) n) j := hys
    have hzs' : decv dec n zs = N (decv dec n ys)
        fun j => vec (τ.window Stream.gauss (p + 2 * i * n + n) n) j := hzs
    have e2 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    have e3 : p + (2 * i + 1) * n = p + 2 * i * n + n := by ring
    rw [e2]
    simp only [noisyIter]
    rw [e3, ← hdx, ← vec_window_eq_windowFn, ← vec_window_eq_windowFn, ← hys', ← hzs']

/-- The run of `npow` within its counts and workspace. -/
theorem runs_npow {dec : K → ℝ} {N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ}
    {J : Interp NOp Tst K} (hJ : IsNoisy dec N J) (W : NOp → List ℕ → ℕ) {τ : Tape K} {k : ℕ}
    {x y : ℕ × ℕ} {m : Mem K} {xs₀ : List K} (hxy : x.1 ≠ y.1) (hl : m.Live [x, y])
    (hx : m.store.readBlock x.1 x.2 n = some xs₀) (hxl : x.2 + n ≤ m.store.len x.1)
    (hy : y.2 + n ≤ m.store.len y.1) :
    Runs J W τ npow ⟨[k, n, x.2, y.2], [x.1, y.1]⟩ m (npowCount k n) (W .nmv [n])
      (NpowPost dec n k x y m (noisyIter N (decv dec n xs₀) τ m.pos (2 * k))) := by
  obtain ⟨m', hrun, hpost⟩ := wp_npow hJ (τ := τ) (k := k) hxy hl hx hxl hy
  exact (Runs.of_run hrun hpost W).mono (le_of_eq (staticCost_npow ..))
    (staticPeak_npow_le ..) fun _ h => h

/-- **The abstract theorem of the noisy power iteration**, for every interpretation meeting the
contract of `nmv`, every noise function with the conditional law of `A v + σ ‖v‖ g`, and every
law of the tape. For every sample: `2 k` calls within the workspace of one. In law: the result
is unbiased, `𝔼 x = A^(2k) x₀`, and `𝔼 ‖x‖² ≤ (a + n σ²)^(2k) ‖x₀‖²` when `‖A v‖² ≤ a ‖v‖²`. -/
theorem runsLaw_npow [MeasurableSpace K] {dec : K → ℝ}
    {N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ} {J : Interp NOp Tst K} (hJ : IsNoisy dec N J)
    {A : Matrix (Fin n) (Fin n) ℝ} {σ a : ℝ} {ν : Measure (Fin n → ℝ)} {law : ℕ → Measure K}
    (hN : IsNoisyMv A σ ν (law Stream.gauss) N) (ha : 0 ≤ a)
    (hA : ∀ v, sqNorm (A.mulVec v) ≤ a * sqNorm v) {Ω : Type} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {ξ : Ω → Tape K} (h : IsTapeLaw law P ξ) (W : NOp → List ℕ → ℕ) {k : ℕ}
    {x y : ℕ × ℕ} {m : Mem K} {xs₀ : List K} (hxy : x.1 ≠ y.1) (hl : m.Live [x, y])
    (hx : m.store.readBlock x.1 x.2 n = some xs₀) (hxl : x.2 + n ≤ m.store.len x.1)
    (hy : y.2 + n ≤ m.store.len y.1) :
    RunsLaw J W ξ npow ⟨[k, n, x.2, y.2], [x.1, y.1]⟩ m (npowCount k n) (W .nmv [n])
      (NpowPost dec n k x y m) fun X =>
        (∀ i, ∫ ω, X ω i ∂P = (A ^ (2 * k)).mulVec (decv dec n xs₀) i) ∧
        ∫ ω, sqNorm (X ω) ∂P ≤ (a + n * σ ^ 2) ^ (2 * k) * sqNorm (decv dec n xs₀) :=
  ⟨fun ω => noisyIter N (decv dec n xs₀) (ξ ω) m.pos (2 * k),
    fun _ => runs_npow hJ W hxy hl hx hxl hy,
    fun i => integral_noisyIter hN ha hA h _ _ _ i,
    (integral_sqNorm_noisyIter_le hN ha hA h _ _ _).2⟩

end NLAlib.Ops.Examples
