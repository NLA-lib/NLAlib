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
@[simps (attr := storeNF)]
def nmvRel (dec : K → ℝ) (N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ) : BlockRel K where
  nd := 1
  stream := Stream.gauss
  win d := d.headD 0
  inLens d := [d.headD 0]
  outLens d := [d.headD 0]
  rel _ X w Y := match X, Y with
    | [xs], [ys] => decv dec n ys = N (decv dec n xs) fun i => vec w i
    | _, _ => False

/-- **The contract of `nmv`**, conditional on the history: at every memory, the output is `N` of
the input and of a window that only the operation reads. -/
def IsNoisy (dec : K → ℝ) (N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ)
    (J : Interp NOp Tst K) : Prop :=
  J.Meets .total .nmv ((nmvRel dec N).spec (OutApart (· = n)))

/-- **The noisy power iteration**: `k` rounds of `y := nmv x; x := nmv y`, in place in `x`, with
a scratch block `y`. Index variables: `k`, `n`, the offset of `x` (twice), then the loop
variable; buffer variables: `x` (twice), then `y`. The tree has no draw. -/
def npow : Stmt NOp Tst :=
  .alloc (.var 1) (.loop (.var 0) (.seq (.call .nmv [.var 1] [⟨0, .var 2⟩] [⟨2, .const 0⟩])
    (.call .nmv [.var 1] [⟨2, .const 0⟩] [⟨0, .var 2⟩])))

/-- **`npow` as an implementation**: two dimensions `k`, `n`, one input and one output. -/
def npowImpl : Impl NOp Tst := ⟨2, 1, 1, npow⟩

/-- The call counts of `npow`: `2 k` noisy products. -/
noncomputable def npowCount (k n : ℕ) : Count NOp Tst := k • (2 • Count.one .nmv [n])

theorem staticCost_npow (k n a b : ℕ) :
    stmtCost (npow (Tst := Tst)) [k, n, a, b] = npowCount k n := by
  simp [npow, stmtCost, useCost, npowCount, two_nsmul]

theorem staticPeak_npow_le (W : NOp → List ℕ → ℕ) (k n a b : ℕ) :
    stmtPeak W (npow (Tst := Tst)) [k, n, a, b] ≤ n + W .nmv [n] := by
  simp only [npow, Stmt.alloc, stmtPeak, StorageFormat.bytes_cell, Nat.one_mul]
  exact Nat.add_le_add (by simp) (Finset.sup_le fun i _ => by simp)

omit [Inhabited K] in
theorem vec_window_eq_windowFn [Inhabited K] (τ : Tape K) (s q n : ℕ) :
    (fun i : Fin n => vec (τ.window s q n) i) = Tape.windowFn τ s q n :=
  funext fun i => vec_window τ s q i.2

omit [Inhabited K] in
/-- **The noisy power iteration reads the tape only in its window**: two tapes with the same
window give the same iterates. -/
theorem noisyIter_congr [Inhabited K] (N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ)
    (v₀ : Fin n → ℝ) {τ τ' : Tape K} {p p' j : ℕ}
    (h : τ.window Stream.gauss p (j * n) = τ'.window Stream.gauss p' (j * n)) :
    noisyIter N v₀ τ p j = noisyIter N v₀ τ' p' j := by
  have hw : ∀ i < j * n, τ (p + i) Stream.gauss = τ' (p' + i) Stream.gauss := fun i hi => by
    rw [← vec_window τ Stream.gauss p hi, ← vec_window τ' Stream.gauss p' hi, h]
  clear h
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj : j * n + n = (j + 1) * n := by rw [Nat.succ_mul]
    simp only [noisyIter]
    rw [ih fun i hi => hw i (by omega)]
    congr 1
    funext i
    have := hw (j * n + i) (by omega)
    simpa [Tape.windowFn, Nat.add_assoc] using this

/-- **The contract of `npow`**, in operand form, with a window: at the dimensions `[k, n]`, the
block `x` is replaced by a block that decodes to the noisy power iteration of its decoded value
along the window of `2 k n` Gaussian entries. The randomness is hidden from the caller. -/
@[simps (attr := storeNF)]
def npowRel (dec : K → ℝ) (N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ) : BlockRel K where
  nd := 2
  stream := Stream.gauss
  win d := 2 * d.headD 0 * n
  inLens _ := [n]
  outLens _ := [n]
  rel d X w Y := ∃ xs₀ xs τ p, X = [xs₀] ∧ Y = [xs] ∧
    τ.window Stream.gauss p (2 * d.headD 0 * n) = w ∧
    decv dec n xs = noisyIter N (decv dec n xs₀) τ p (2 * d.headD 0)

/-- The admitted operands of `npow`: the length of the vector is `n`, and it is updated in
place. -/
@[admNF] def NpowOperands (n : ℕ) : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d.getD 1 0 = n ∧ outs = ins

/-- The postcondition of `npow` for the decoded result `v`: the block `x` holds a block that
decodes to `v`, the position has advanced by `2 k n`, and nothing else is written. -/
def NpowPost (dec : K → ℝ) (n k : ℕ) (x : ℕ × ℕ) (m : Mem K) (v : Fin n → ℝ) (m' : Mem K) :
    Prop :=
  ∃ xs, m' = (m.updBlock x xs).advance (2 * k * n) ∧ xs.length = n ∧ decv dec n xs = v

/-- **The run of `npow`**, for every interpretation meeting the contract of `nmv` and every
tape: the block `x` decodes to the noisy power iteration of the tape entries from the position. -/
theorem wp_npow {dec : K → ℝ} {N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ}
    {J : Interp NOp Tst K} (hJ : IsNoisy dec N J) {τ : Tape K} {k : ℕ} {x : ℕ × ℕ}
    {m : Mem K} {xs₀ : List K} (hx : m.store.readBlock x.1 x.2 n = some xs₀)
    (hxl : x.2 + n ≤ m.store.len x.1) (hlx : x.1 < m.store.length) :
    Wp .total J τ npow (Env.frame [k, n] [x, x])
      (NpowPost dec n k x m (noisyIter N (decv dec n xs₀) τ m.pos (2 * k))) m := by
  obtain ⟨s, p⟩ := m
  obtain ⟨bx, ox⟩ := x
  simp only at hx hxl hlx
  refine wp_alloc rfl (wp_loop (k := k) rfl (fun i m' => ∃ s' xs q, m' = ⟨s', q⟩ ∧
    q = p + 2 * i * n ∧ (s.push n).EqOff (Store.inBlock bx ox n ⊔ Store.inBuf s.length) s' ∧
    s'.readBlock bx ox n = some xs ∧
    decv dec n xs = noisyIter N (decv dec n xs₀) τ p (2 * i))
    ⟨_, xs₀, p, rfl, by simp, Store.EqOff.refl _ _, by store_simp, rfl⟩ ?_ ?_)
  · rintro i hi m' ⟨s', xs, q, rfl, rfl, hfr, hr, hdx⟩
    have hlen : s'.length = s.length + 1 := by rw [hfr.length_eq, Store.length_push]
    have hlx' : s'.len bx = s.len bx := by rw [hfr.len_eq, Store.len_push_of_lt hlx]
    have hly : s'.len s.length = n := by rw [hfr.len_eq, Store.len_push_top]
    -- `y := nmv x`, then `x := nmv y`
    wp_call hJ with ys hyl hys
    wp_call hJ with zs hzl hzs
    refine ⟨_, zs, _, rfl, by simp [Mem.advance, Mem.updBlock]; ring,
      (hfr.updBlock fun j hj => Or.inr rfl).updBlock
        fun j hj => Or.inl ⟨rfl, by omega, by omega⟩, by store_simp, ?_⟩
    have e2 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    have e3 : p + (2 * i + 1) * n = p + 2 * i * n + n := by ring
    rw [e2]
    simp only [noisyIter]
    rw [e3, ← hdx, ← vec_window_eq_windowFn, ← vec_window_eq_windowFn, ← hys, ← hzs]
  · rintro m' ⟨s', xs, q, rfl, rfl, hfr, hr, hdx⟩
    have hlen : s'.length = s.length + 1 := by rw [hfr.length_eq, Store.length_push]
    have hg : s'.pop.readBlock bx ox n = some xs := by
      rw [Store.readBlock_pop_of_lt (by omega), hr]
    exact ⟨xs, by simp [Mem.updBlock, Mem.advance, hfr.pop.eq_updBlock hg],
      Store.length_of_readBlock hr, hdx⟩

/-- **The certificate of `npow`**: for every interpretation meeting the contract of `nmv`,
`npow` meets its contract with a window. -/
theorem npow_spec {dec : K → ℝ} {N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ}
    {J : Interp NOp Tst K} (hJ : IsNoisy dec N J) :
    (npowImpl (Tst := Tst)).Triple J .total ((npowRel dec N).spec (NpowOperands n)) := by
  refine Impl.meets_rel fun d ins outs τ m X hnd hadm hl hr _ hz => ?_
  obtain ⟨k, n', rfl⟩ := List.length_eq_two.mp hnd
  obtain ⟨rfl, rfl⟩ : n' = n ∧ outs = ins := hadm
  obtain ⟨x, xs₀, rfl, hx, rfl⟩ := Mem.readBlocks_one hr
  refine ⟨⟨rfl, rfl, rfl⟩, (wp_npow hJ (τ := τ) (k := k) hx hz.1 (by simpa using hl)).mono ?_⟩
  rintro m' ⟨xs, rfl, hlen, hv⟩
  exact ⟨[xs], by simp [hlen], ⟨xs₀, xs, τ, m.pos, rfl, rfl, rfl, hv⟩, rfl⟩

/-- **The abstract theorem of the noisy power iteration**, from its certificate by the law-level
bridge, for every interpretation meeting the contract of `nmv`, every noise function with the
conditional law of `A v + σ ‖v‖ g`, and every law of the tape. For every sample: `2 k` calls
within `n` scratch cells and the workspace of one call. In law: the result is unbiased,
`𝔼 x = A^(2k) x₀`, and `𝔼 ‖x‖² ≤ (a + n σ²)^(2k) ‖x₀‖²` when `‖A v‖² ≤ a ‖v‖²`. -/
theorem runsLaw_npow [MeasurableSpace K] {dec : K → ℝ}
    {N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ} {J : Interp NOp Tst K} (hJ : IsNoisy dec N J)
    {A : Matrix (Fin n) (Fin n) ℝ} {σ a : ℝ} {ν : Measure (Fin n → ℝ)} {law : ℕ → Measure K}
    (hN : IsNoisyMv A σ ν (law Stream.gauss) N) (ha : 0 ≤ a)
    (hA : ∀ v, sqNorm (A.mulVec v) ≤ a * sqNorm v) {Ω : Type} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {ξ : Ω → Tape K} (h : IsTapeLaw law P ξ) (W : NOp → List ℕ → ℕ) {k : ℕ}
    {x : ℕ × ℕ} {m : Mem K} {xs₀ : List K} (hx : m.store.readBlock x.1 x.2 n = some xs₀)
    (hxl : x.2 + n ≤ m.store.len x.1) (hlx : x.1 < m.store.length) :
    ConditionalRunsLaw J W ξ npow (Env.frame [k, n] [x, x]) m (npowCount k n) (n + W .nmv [n])
      (NpowPost dec n k x m) fun X =>
        (∀ i, ∫ ω, X ω i ∂P = (A ^ (2 * k)).mulVec (decv dec n xs₀) i) ∧
        ∫ ω, sqNorm (X ω) ∂P ≤ (a + n * σ ^ 2) ^ (2 * k) * sqNorm (decv dec n xs₀) := by
  refine ((npow_spec hJ).runsLaw W ξ (fun ys => decv dec n ys.flatten) (d := [k, n])
    (ins := [x]) (outs := [x]) (xs := [xs₀]) rfl ⟨rfl, rfl⟩ (by simp [hlx])
    (by simp [Mem.readBlocks, hx]) (fun _ => trivial) ⟨hxl, trivial⟩ fun X hX => ?_).mono
    (le_of_eq (staticCost_npow ..)) (staticPeak_npow_le ..) ?_
  · have hXe : X = fun ω => noisyIter N (decv dec n xs₀) (ξ ω) m.pos (2 * k) :=
      funext fun ω => by
        obtain ⟨ys, hx', -, xs₀', xs, τ, p, h1, rfl, hw, hv⟩ := hX ω
        obtain rfl : xs₀ = xs₀' := by simpa using h1
        rw [hx']
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
        rw [hv]
        exact noisyIter_congr N _ hw
    subst hXe
    exact ⟨fun i => integral_noisyIter hN ha hA h _ _ _ i,
      (integral_sqNorm_noisyIter_le hN ha hA h _ _ _).2⟩
  · rintro v m' ⟨ys, rfl, hlen, rfl⟩
    obtain ⟨y, rfl, hy⟩ := map_length_eq_one hlen
    exact ⟨y, rfl, hy, by simp⟩

end NLAlib.Ops.Examples
