/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Count
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Examples.Noisy
public import NLAlib.Ops.Profiles.Random
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# The noisy product implemented with a drawn probe, and the linked iteration

**The implementation** of `nmv [n] [x] [y]`: `y := A x` by the exact product, a Gaussian probe
`g` drawn into scratch, the norm of `x` and its multiple by `σ` in a scratch cell, then
`y := y + (σ ‖x‖) g`. The probe and the cell are freed at the end of the call: the caller is
left with `y` and a tape position `n` further, and nothing that holds the noise.

## Main results

* `NLAlib.Ops.Examples.nmvRoutine_satisfies`: the implementation satisfies the contract of `nmv`
  with
  the
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
def nmvTree (σ : ℚ) : Stmt ROp Tst :=
  .alloc (.var 0) (.alloc (.const 1)
    (.seq (.call (.operator .matvec) [.var 0, .var 0] [⟨0, .var 1⟩] [⟨1, .var 2⟩])
      (.seq (.call .gauss [.var 0] [] [⟨2, .const 0⟩])
        (.seq (.call .nrm2 [.var 0] [⟨0, .var 1⟩] [⟨3, .const 0⟩])
          (.seq (.call (.mulc σ) [] [⟨3, .const 0⟩] [⟨3, .const 0⟩])
            (.call .axpy [.var 0] [⟨3, .const 0⟩, ⟨2, .const 0⟩, ⟨1, .var 2⟩]
              [⟨1, .var 2⟩]))))))

omit [Inhabited K] in
/-- The noisy product as a routine: `[n] (x : read n) → (y : write n)`, drawing `n` positions. -/
def nmvRoutine (σ : ℚ) : Routine ROp Tst :=
  routine% [n] (x : n) → (y : n) draws n := nmvTree σ

/-- The noisy product meets the specification read off its relation, over the exact operations
and the vector draw: the output decodes to `A v + σ ‖v‖ dec w` for the window `w` it drew. -/
theorem nmvRoutine_meets {dec : K → ℝ} {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp ROp Tst K}
    (hI : IsRandLin dec A I) (σ : ℚ) :
    (nmvRoutine (Tst := Tst) σ).Meets I
      (Routine.Spec.ofRel (nmvRel dec (noiseFn dec A σ)) fun d => d.headD 0 = n) := by
  refine Routine.meets_ofRel_of_post (fun d => by cases d <;> rfl)
    (fun d _ => by cases d <;> rfl)
    fun d args τ m X hnd hlen hl hsep hr hok _ hz => ?_
  obtain ⟨n', rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain rfl : n' = n := hok
  obtain ⟨x, z, rfl⟩ : ∃ x z, args = [x, z] := by
    match args, hlen with
    | [x, z], _ => exact ⟨x, z, rfl⟩
  have hxz : x.1 ≠ z.1 := (hsep.2.1 z (by simp [nmvRoutine, Routine.sel, Access.writable])
    x (by simp [nmvRoutine, Routine.sel, Access.readOnly])).symm
  change m.readBlocks [x] [n'] = some X at hr
  change m.Room [z] [n'] at hz
  obtain ⟨x', xs, he, hx, rfl⟩ := Mem.readBlocks_one hr
  obtain rfl : x = x' := by simpa using he
  change Wp .total I τ (nmvTree (Tst := Tst) σ) (Env.frame [n'] [x, z])
    ((nmvRel dec (noiseFn dec A σ)).Post [n'] [xs] [z] (τ.window Stream.gauss m.pos n') m) m
  obtain ⟨s, p⟩ := m
  obtain ⟨hlx, hlz⟩ : x.1 < s.length ∧ z.1 < s.length := by simpa using hl
  replace hz : z.2 + n' ≤ s.len z.1 := hz.1
  replace hx : s.readBlock x.1 x.2 n' = some xs := hx
  have hl1 : (s.push n').length = s.length + 1 := Store.length_push _ _
  have hlt : ((s.push n').push 1).len (s.length + 1) = 1 := by rw [← hl1, Store.len_push_top]
  have hlg : ((s.push n').push 1).len s.length = n' := by
    rw [Store.len_push_of_lt (by simp), Store.len_push_top]
  have hlz' : ((s.push n').push 1).len z.1 = s.len z.1 := by
    rw [Store.len_push_of_lt (by simp; omega), Store.len_push_of_lt hlz]
  refine wp_alloc rfl (wp_alloc rfl ?_)
  -- the exact product into `y`, the probe into the scratch block, the norm of `x` and its
  -- multiple by `σ` in the scratch cell, the update of `y`
  wp_call hI.matvec [List.getD_cons_succ, List.getD_cons_zero] with ws hwl hws
  wp_call hI.gauss with gs hgl hgs
  obtain rfl : gs = τ.window Stream.gauss p n' := (List.cons.inj hgs).1
  wp_call hI.nrm2 with t ht
  wp_call (hI.mulc σ) with t' ht'
  wp_call hI.axpy with zs hzl hzs
  refine ⟨[zs], by simp [hzl], ?_, ?_⟩
  · change decv dec n' zs = noiseFn dec A σ (decv dec n' xs)
      fun i => vec (τ.window Stream.gauss p n') i
    have haxpy : decv dec n' zs = fun i => decv dec n' ws i +
        dec t' * decv dec n' (τ.window Stream.gauss p n') i :=
      funext fun i => hzs i i.isLt
    have hnorm : dec t = √(sqNorm (decv dec n' xs)) := by
      exact ht.trans (congrArg Real.sqrt
        (Fin.sum_univ_eq_sum_range (fun j : ℕ => dec (vec xs j) ^ 2) n')).symm
    rw [haxpy, hws, ht', hnorm]
    rfl
  · have hfr : ((s.push n').push 1).EqOff ((Store.inBlock z.1 z.2 n' ⊔ Store.inBuf s.length) ⊔
        Store.inBuf (s.push n').length)
        (((((((s.push n').push 1).updBlock z.1 z.2 ws).updBlock s.length 0
          (τ.window Stream.gauss p n')).upd (s.push n').length 0 t).upd (s.push n').length 0
          t').updBlock z.1 z.2 zs) :=
      (((((Store.EqOff.refl _ _).updBlock fun j hj =>
        Or.inl (Or.inl ⟨rfl, by omega, by omega⟩)).updBlock fun _ _ =>
        Or.inl (Or.inr rfl)).upd (Or.inr rfl) _).upd (Or.inr rfl) _).updBlock fun j hj =>
        Or.inl (Or.inl ⟨rfl, by omega, by omega⟩)
    have hrd := hfr.pop.pop.eq_updBlock (xs := zs) (by store_simp)
    simp only [Mem.updBlock, Mem.advance, Mem.upd, Mem.updBlocks] at hrd ⊢
    rw [← hrd]
    rfl

/-- The routine of the noisy product implements the contract of `nmv`. -/
theorem nmvRoutine_implements (dec : K → ℝ) (N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ)
    (σ : ℚ) (ok : ℕ → Prop) :
    (nmvRoutine (Tst := Tst) σ).Implements (nmvRel dec N) (OutApart ok)
      (fun ins outs => ins ++ outs) := by
  implements [n] (x) → (z) with hadm

/-- The implementation satisfies the contract of the noisy product, over the exact operations
and the vector draw: the output decodes to `A v + σ ‖v‖ dec w` for the window `w` it drew. A
consequence of the judgment of its routine. -/
theorem nmvRoutine_satisfies {dec : K → ℝ} {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp ROp Tst K}
    (hI : IsRandLin dec A I) (σ : ℚ) :
    (nmvRoutine (Tst := Tst) σ).impl.Satisfies I .total
      ((nmvRel dec (noiseFn dec A σ)).spec (OutApart (· = n))) :=
  (nmvRoutine_meets hI σ).satisfies_ofRel (nmvRoutine_implements dec _ σ _) fun _ _ _ h => h.2.1.1

/-- **The profile of the noisy product by a drawn probe**: one product, one vector draw, one
norm, one product by `σ` and one `axpy` per call; `n + 1` scratch cells; a window of `n`. -/
noncomputable def noisy (σ : ℚ) : Profile NOp ROp Tst where
  table _ := .inl (nmvRoutine σ).impl
  cost _ d := Count.one (.operator .matvec) [d.headD 0, d.headD 0] +
    (Count.one .gauss d + (Count.one .nrm2 d + (Count.one (.mulc σ) [] + Count.one .axpy d)))
  ws _ d := d.headD 0 + 1
  wsLo _ _ := 0
  win _ d := d.headD 0
  winLo := randWindow

/-- **The certificate of the profile.** The scratch draw of the implementation is the window
that the law of the tape assigns to the call, by the window lemma. -/
theorem noisy_certifies (dec : K → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (σ : ℚ) :
    (noisy (Tst := Tst) σ).Refines (IsRandLin dec A) (IsNoisy dec (noiseFn dec A σ)) := by
  refine .of_accounts
    (fun I hI => Interp.link_satisfies (o := NOp.nmv) rfl (nmvRoutine_satisfies hI σ))
    (fun I => Table.accounts_of_static ?_ (fun o o' hT => by cases hT) I) fun I _ hloc o => ?_
  · intro o R hT d offs hd ho
    cases hT
    obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hd
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp ho
    simp [noisy, nmvRoutine, Routine.impl, Routine.nin, Routine.nout, routineNF, nmvTree, stmtCost,
      stmtPeak, useCost]
  · cases o
    exact Interp.TapeLocal.link hloc (o := NOp.nmv) rfl (by simp [Stmt.Straight, nmvRoutine,
      Routine.impl, Routine.nin, Routine.nout, routineNF, nmvTree])
      fun d offs hd ho => by
        obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hd
        obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp ho
        simp [staticWindow, nmvRoutine, Routine.impl, Routine.nin, Routine.nout, routineNF,
          nmvTree, noisy, randWindow]

/-- The noisy product by a drawn probe, with the probe drawn entry by entry. -/
noncomputable def noisyDraws (σ : ℚ) : Profile NOp ROp Tst := (noisy σ).over Rand.gaussLoop

theorem noisyDraws_certifies (dec : K → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (σ : ℚ) :
    (noisyDraws (Tst := Tst) σ).Refines (IsRandBase dec A) (IsNoisy dec (noiseFn dec A σ)) :=
  (noisy_certifies dec A σ).over (Rand.gaussLoop_certifies dec A) rfl rfl

omit [Inhabited K] in
/-- **The counts of the linked iteration**, through both profiles: per noisy product, one exact
product, `n` scalar draws, one norm, one product by `σ` and one `axpy`. -/
theorem push_noisyDraws_npowCount (σ : ℚ) (k n : ℕ) :
    Count.push (noisyDraws σ).cost (npowCount (Tst := Tst) k n) =
      k • (2 • (Count.one (.operator .matvec) [n, n] + (n • Count.one .draw [] +
        (Count.one .nrm2 [n] + (Count.one (.mulc σ) [] + Count.one .axpy [n]))))) := by
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
    {P : Measure Ω} {ξ : Ω → Tape K} (h : IsTapeLaw law P ξ) {k : ℕ} {x : ℕ × ℕ}
    {m : Mem K} {xs₀ : List K} (hx : m.store.readBlock x.1 x.2 n = some xs₀)
    (hxl : x.2 + n ≤ m.store.len x.1) (hlx : x.1 < m.store.length) :
    ConditionalRunsLaw I (fun _ _ => 0) ξ (npow.link (noisyDraws σ).table)
      (Env.frame [k, n] [x, x]) m
      (k • (2 • (Count.one (.operator .matvec) [n, n] + (n • Count.one .draw [] +
        (Count.one .nrm2 [n] + (Count.one (.mulc σ) [] + Count.one .axpy [n]))))))
      (n + (n + 1)) (NpowPost dec n k x m) fun X =>
        (∀ i, ∫ ω, X ω i ∂P = (A ^ (2 * k)).mulVec (decv dec n xs₀) i) ∧
        ∫ ω, sqNorm (X ω) ∂P ≤ (a + n * (σ : ℝ) ^ 2) ^ (2 * k) * sqNorm (decv dec n xs₀) :=
  ((noisyDraws_certifies dec A σ).runsLaw (ξ := ξ)
    (fun _ hJ _ => runsLaw_npow hJ (isNoisyMv_noiseFn hdec hstd A σ) ha hA h _ hx hxl hlx)
    hI hloc).mono (le_of_eq (push_noisyDraws_npowCount σ k n)) le_rfl fun _ _ h => h

end NLAlib.Ops.Examples
