/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Noisy
public import NLAlib.Ops.Profiles.Random

/-!
# The noisy product implemented with a drawn probe, and the linked iteration

**The implementation** of `nmv [n] [x] [y]`: `y := A x` by the exact product, a Gaussian probe
`g` drawn into scratch, the norm of `x` and its multiple by `σ` in a scratch cell, then
`y := y + (σ ‖x‖) g`. The probe and the cell are freed at the end of the call: the caller is
left with `y` and a tape position `n` further, and nothing that holds the noise.

## Main results

* `NLAlib.Ops.Examples.nmvImpl_spec`: the implementation meets the contract of `nmv` with the
  noise function `noiseFn`, whose conditional law is that of `A v + σ ‖v‖ g`
  (`isNoisyMv_noiseFn`).
* `NLAlib.Ops.Examples.noisy_certifies`: the certificate of the profile: contract, counts,
  `n + 1` scratch cells, window `n` by the window lemma.
* `NLAlib.Ops.Examples.runsLaw_npow_link`: the corollary for the noisy power iteration linked
  through this profile and then through the vector draw by scalar draws, by one application of
  the law-level linking lemma to the composed certificate.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.Ops.Examples

variable {K Tst : Type} [Inhabited K] {n : ℕ}

/-- **The implementation of the noisy product.** Index variables: `n`, the offsets of `x`, `y`;
buffer variables: `x`, `y`, then the scratch block `g` and the scratch cell `t`. -/
def nmvImpl (σ : ℚ) : Impl ROp Tst where
  nd := 1
  nin := 1
  nout := 1
  body := .alloc (.var 0) (.alloc (.const 1)
    (.seq (.call .matvec [.var 0] [⟨0, .var 1⟩] [⟨1, .var 2⟩])
      (.seq (.call .gauss [.var 0] [] [⟨2, .const 0⟩])
        (.seq (.call .nrm2 [.var 0] [⟨0, .var 1⟩] [⟨3, .const 0⟩])
          (.seq (.call (.mulc σ) [] [⟨3, .const 0⟩] [⟨3, .const 0⟩])
            (.call .axpy [.var 0] [⟨3, .const 0⟩, ⟨2, .const 0⟩, ⟨1, .var 2⟩]
              [⟨1, .var 2⟩]))))))

/-- **The implementation meets the contract of the noisy product**, over the exact operations
and the vector draw: the output decodes to `A v + σ ‖v‖ dec w` for the window `w` it drew. -/
theorem nmvImpl_spec {dec : K → ℝ} {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp ROp Tst K}
    (hI : IsRandLin dec A I) (σ : ℚ) :
    (nmvImpl (Tst := Tst) σ).MeetsWin I (nmvRel dec (noiseFn dec A σ)) (OutApart (· = n)) := by
  intro d ins z τ m X hnd hadm hl hr hz
  obtain ⟨n', rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain rfl : n' = n := hadm.1
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hr
  have hxz : x.1 ≠ z.1 := hadm.2 x (by simp)
  obtain ⟨s, p⟩ := m
  obtain ⟨hlx, hlz⟩ : x.1 < s.length ∧ z.1 < s.length := by simpa using hl
  replace hz : z.2 + n' ≤ s.len z.1 := hz
  replace hx : s.readBlock x.1 x.2 n' = some xs := hx
  have hl1 : (s.push n').length = s.length + 1 := Store.length_push _ _
  have hlt : ((s.push n').push 1).len (s.length + 1) = 1 := by rw [← hl1, Store.len_push_top]
  have hlg : ((s.push n').push 1).len s.length = n' := by
    rw [Store.len_push_of_lt (by simp), Store.len_push_top]
  have hlz' : ((s.push n').push 1).len z.1 = s.len z.1 := by
    rw [Store.len_push_of_lt (by simp; omega), Store.len_push_of_lt hlz]
  refine ⟨⟨rfl, rfl, rfl⟩, wp_alloc rfl (wp_alloc rfl ?_)⟩
  -- the exact product, into `y`
  refine wp_seq (wp_call_rel hI.matvec rfl rfl rfl rfl ⟨rfl, by simpa using hxz⟩ ?_
    (xs := [xs]) ?_ ?_ fun ws hwl hws => ?_)
  · store_simp
  · store_simp
  · store_simp
  replace hwl : ws.length = n' := hwl
  -- the probe, into the scratch block
  refine wp_seq (wp_call_win hI.gauss (k := n') (l := n') rfl rfl rfl rfl rfl rfl
    ⟨rfl, by simp⟩ ?_ (xs := []) rfl ?_ fun gs hgl hgs => ?_)
  · store_simp
  · store_simp
  obtain rfl : gs = τ.window Stream.gauss p n' := hgs
  -- the norm of `x` and its multiple by `σ`, in the scratch cell
  refine wp_seq (wp_call_rel_cell hI.nrm2 rfl rfl rfl rfl rfl ⟨rfl, by simp; omega⟩ ?_
    (xs := [xs]) ?_ ?_ fun t ht => ?_)
  · store_simp
  · store_simp
  · store_simp
  refine wp_seq (wp_call_rel_cell (hI.mulc σ) rfl rfl rfl rfl rfl trivial ?_ (xs := [[t]]) ?_
    ?_ fun t' ht' => ?_)
  · store_simp
  · store_simp [BlockFn.readBlock_one]
  · store_simp
  -- the update of `y`
  refine wp_call_rel hI.axpy rfl rfl rfl rfl ⟨rfl, [_, _], rfl, by simp; omega⟩ ?_
    (xs := [[t'], τ.window Stream.gauss p n', ws]) ?_ ?_ fun zs hzl hzs => ⟨zs, hzl, ?_, ?_⟩
  · store_simp
  · store_simp [BlockFn.readBlock_one]
  · store_simp
  · replace hws : decv dec n' ws = A.mulVec (decv dec n' xs) := hws
    replace ht : dec t = √(∑ i, decv dec n' xs i ^ 2) := ht
    replace ht' : dec t' = σ * dec t := ht'
    replace hzs : decv dec n' zs = fun i => decv dec n' ws i +
      dec t' * decv dec n' (τ.window Stream.gauss p n') i := hzs
    change decv dec n' zs = noiseFn dec A σ (decv dec n' xs)
      fun i => vec (τ.window Stream.gauss p n') i
    rw [hzs, hws, ht', ht]
    rfl
  · replace hzl : zs.length = n' := hzl
    have hfr : ((s.push n').push 1).EqOff ((Store.inBlock z.1 z.2 n' ⊔ Store.inBuf s.length) ⊔
        Store.inBuf (s.push n').length)
        (((((((s.push n').push 1).updBlock z.1 z.2 ws).updBlock s.length 0
          (τ.window Stream.gauss p n')).upd (s.push n').length 0 t).upd (s.push n').length 0
          t').updBlock z.1 z.2 zs) :=
      (((((Store.EqOff.refl _ _).updBlock fun j hj =>
        Or.inl (Or.inl ⟨rfl, by omega, by omega⟩)).updBlock fun _ _ =>
        Or.inl (Or.inr rfl)).upd (Or.inr rfl) _).upd (Or.inr rfl) _).updBlock fun j hj =>
        Or.inl (Or.inl ⟨rfl, by omega, by omega⟩)
    have hrd := hfr.pop.pop.eq_updBlock (xs := zs) (by store_simp)
    simp only [Mem.updBlock, Mem.advance, Mem.upd] at hrd ⊢
    rw [← hrd]
    rfl

/-- **The profile of the noisy product by a drawn probe**: one product, one vector draw, one
norm, one product by `σ` and one `axpy` per call; `n + 1` scratch cells; a window of `n`. -/
noncomputable def noisy (σ : ℚ) : Profile NOp ROp Tst where
  table _ := .inl (nmvImpl σ)
  cost _ d := Count.one .matvec d + (Count.one .gauss d + (Count.one .nrm2 d +
    (Count.one (.mulc σ) [] + Count.one .axpy d)))
  ws _ d := d.headD 0 + 1
  wsLo _ _ := 0
  win _ d := d.headD 0
  winLo := randWindow

/-- **The certificate of the profile.** The scratch draw of the implementation is the window
that the law of the tape assigns to the call, by the window lemma. -/
theorem noisy_certifies (dec : K → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (σ : ℚ) :
    (noisy (Tst := Tst) σ).Certifies (IsRandLin dec A) (IsNoisy dec (noiseFn dec A σ)) := by
  refine .of_accounts (fun I hI => Interp.link_meets_win (o := NOp.nmv) rfl (nmvImpl_spec hI σ))
    (fun I => Table.accounts_of_static ?_ (fun o o' hT => by cases hT) I) fun I _ hloc o => ?_
  · intro o R hT d offs hd ho
    cases hT
    obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hd
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp ho
    simp [noisy, nmvImpl, staticCost, staticPeak, useCost]
  · cases o
    exact Interp.TapeLocal.link hloc (o := NOp.nmv) rfl (by simp [Stmt.Straight, nmvImpl])
      fun d offs hd ho => by
        obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hd
        obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp ho
        simp [staticWindow, nmvImpl, noisy, randWindow]

/-- The noisy product by a drawn probe, with the probe drawn entry by entry. -/
noncomputable def noisyDraws (σ : ℚ) : Profile NOp ROp Tst := (noisy σ).over Rand.gaussLoop

theorem noisyDraws_certifies (dec : K → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (σ : ℚ) :
    (noisyDraws (Tst := Tst) σ).Certifies (IsRandBase dec A) (IsNoisy dec (noiseFn dec A σ)) :=
  (noisy_certifies dec A σ).over (Rand.gaussLoop_certifies dec A) rfl rfl

omit [Inhabited K] in
/-- **The counts of the linked iteration**, through both profiles: per noisy product, one exact
product, `n` scalar draws, one norm, one product by `σ` and one `axpy`. -/
theorem push_noisyDraws_npowCount (σ : ℚ) (k n : ℕ) :
    Count.push (noisyDraws σ).cost (npowCount (Tst := Tst) k n) =
      k • (2 • (Count.one .matvec [n] + (n • Count.one .draw [] + (Count.one .nrm2 [n] +
        (Count.one (.mulc σ) [] + Count.one .axpy [n]))))) := by
  simp [npowCount, noisyDraws, Profile.over, noisy, Rand.gaussLoop, Rand.gaussCost]

/-- **The corollary for the linked noisy power iteration.** Over every interpretation of the
exact operations and the scalar draw, with draws that decode to a standard law (the standard
Gaussian), the program obtained by linking the noisy product and then the vector draw runs, for
every sample, within the pushed-forward counts and `n + 1` scratch cells; the result is
unbiased, `𝔼 x = A^(2k) x₀`, and `𝔼 ‖x‖² ≤ (a + n σ²)^(2k) ‖x₀‖²`. One application of the
law-level linking lemma. -/
theorem runsLaw_npow_link [MeasurableSpace K] {dec : K → ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    {σ : ℚ} {a : ℝ} {I : Interp ROp Tst K} (hI : IsRandBase dec A I)
    (hloc : ∀ o, I.TapeLocal o (randWindow o)) {law : ℕ → Measure K} (hdec : Measurable dec)
    (hstd : IsStdLaw ((law Stream.gauss).map dec)) (ha : 0 ≤ a)
    (hA : ∀ v, sqNorm (A.mulVec v) ≤ a * sqNorm v) {Ω : Type} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {ξ : Ω → Tape K} (h : IsTapeLaw law P ξ) {k : ℕ} {x y : ℕ × ℕ}
    {m : Mem K} {xs₀ : List K} (hxy : x.1 ≠ y.1) (hl : m.Live [x, y])
    (hx : m.store.readBlock x.1 x.2 n = some xs₀) (hxl : x.2 + n ≤ m.store.len x.1)
    (hy : y.2 + n ≤ m.store.len y.1) :
    RunsLaw I (fun _ _ => 0) ξ (npow.link (noisyDraws σ).table)
      ⟨[k, n, x.2, y.2], [x.1, y.1]⟩ m (Count.push (noisyDraws σ).cost (npowCount k n)) (n + 1)
      (NpowPost dec n k x y m) fun X =>
        (∀ i, ∫ ω, X ω i ∂P = (A ^ (2 * k)).mulVec (decv dec n xs₀) i) ∧
        ∫ ω, sqNorm (X ω) ∂P ≤ (a + n * (σ : ℝ) ^ 2) ^ (2 * k) * sqNorm (decv dec n xs₀) :=
  (noisyDraws_certifies dec A σ).runsLaw (ξ := ξ)
    (fun _ hJ _ => runsLaw_npow hJ (isNoisyMv_noiseFn hdec hstd A σ) ha hA h _ hxy hl hx hxl hy)
    hI hloc

end NLAlib.Ops.Examples
