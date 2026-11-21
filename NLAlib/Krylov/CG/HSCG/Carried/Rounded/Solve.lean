/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Rounded.Alg
public import NLAlib.Krylov.CG.HSCG.Carried.Rounded.Rounds

/-!
# Full rounded CG execution connected to the existing run mathematics

Input scalar/BLAS contracts, rounded matvec and spectral precision imply successful complete
execution. The actual output is either the zero-step state or an existing positive-length
CGRun with matching physical vectors and retained scalar. The accumulated residual gap is
then a direct application of the existing pure theorem, not a new program-specific estimate.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.solveRoutine_meets`: the solver meets its
  specification, from the judgments of initialization and the loop.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.runs_solve` returns a run and its residual-gap bound.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- The rounded capped solver as a routine: the right-hand side is read, the iterate updated in
place, the residual, the direction and the cell of the retained residual product written. -/
def solveRoutine : Routine Op Tst :=
  routine% [n, cap] (b : n, x : n) → (x, r : n, p : n, rho : 1) := solve

/-- From a zero iterate and a cap within the precision window, the written state is a successful
rounded prefix of some length $m \le \mathrm{cap}$ for the right-hand side read, with its retained
residual product, stopping early only at a zero residual. -/
noncomputable def solveSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (e a a' : ℝ) : Routine.Spec K :=
  spec% [k, cap] (bs, xs) → (xs', rs, ps, [v])
    requires k = n ∧ decv dec n xs = 0 ∧
      (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤ 1 / 10 ^ 5
    ensures ∃ m ≤ cap,
      IsPrefix A (decv dec n bs) e m (decodedState dec n xs' rs ps) (dec v) ∧
        (m < cap → (decodedState dec n xs' rs ps).r = 0)

/-- The rounded solver meets its specification under the standard model of arithmetic, rounded
vector and matrix-vector contracts, and spectral and precision bounds on the matrix; no
trajectory or successful-execution hypothesis is assumed. Initialization, then the capped loop,
each used by its judgment. -/
theorem solveRoutine_meets {M : Machine K} {dec : K → ℝ} {em u e : ℝ} {ε : Blas1Err}
    {ok : ℕ → Prop} {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec ε ok I) (hok : ok n)
    (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I) (hAT : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hu : 0 ≤ u) (hd : 0 ≤ ε.dot n) (haa : 0 ≤ ε.axpy)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ε.dot n ≤ e) (hae : ε.axpy ≤ e) (he : e ≤ 1 / 100)
    (hprec : 3 * e * a' ≤ a) :
    (solveRoutine (Op := Op) (Tst := Tst)).Meets I (solveSpec dec A e a a') := by
  routine_intro [n', cap] (b, x, r, p, v) reads (bs, xs)
  obtain ⟨hn, hx0, hwindow⟩ := hpre
  obtain rfl : n = n' := hn.symm
  call (initializeRoutine_meets (Tst := Tst) hB hok) [n] (b, x, r, p, v)
    (pre := ⟨rfl, hx0⟩) as m₁ hfr₁ hpos₁ (xs₁, rs₁, ps₁, vs₁) hst₁
  obtain ⟨rr₁, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs₁)
  have hst₁ : decodedState dec n xs₁ rs₁ ps₁ = ⟨0, decv dec n bs, decv dec n bs⟩ ∧
      IsDotErr dec (ε.dot n) n (vec rs₁) (vec rs₁) rr₁ := hst₁
  have hcache : |dec rr₁ - decv dec n bs ⬝ᵥ decv dec n bs| ≤
      ε.dot n * ∑ i, |decv dec n bs i * decv dec n bs i| := by
    simpa only [show decv dec n rs₁ = decv dec n bs from congrArg CGState.r hst₁.1] using
      hst₁.2.decoded
  call (roundsRoutine_meets (Tst := Tst) (b := decv dec n bs) hS hM hB hok hA hCmp hAT ha
    hspec hu hd haa hem hue hde hae he hprec) [n, cap] (x, r, p, v)
    (pre := ⟨rfl, hst₁.1, hcache, hwindow⟩) as m₂ hfr₂ hpos₂ (xs₂, rs₂, ps₂, vs₂) hst₂
  obtain ⟨rr₂, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs₂)
  routine_exit
  exact hst₂

/-- Actual outputs satisfy the existing run's accumulated residual-gap bound, or are the
zero-step state when the cap or right-hand side is zero. This predicate includes physical
vector and computed-cache ties; the run is not an unrelated mathematical witness. -/
def Output {n : ℕ} (dec : K → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (rhs : Fin n → ℝ)
    (e : ℝ) (cap : ℕ) (x r p v : ℕ × ℕ) (μ : Mem K) : Prop :=
  ((cap = 0 ∨ rhs = 0) ∧ ∃ rho, StoresValues dec n x r p v ⟨0, rhs, rhs⟩ rho μ) ∨
  ∃ m : ℕ, ∃ R : CGRun n m, m ≤ cap ∧ R.A = A ∧ R.b = rhs ∧ R.ε = e ∧
    StoresValues dec n x r p v ⟨R.x m, R.r m, R.p m⟩ (R.ν m) μ ∧
    (m < cap → R.r m = 0) ∧
    ‖WithLp.toLp 2 (R.b - R.A *ᵥ R.x m - R.r m)‖ ≤
      R.ε * ∑ j ∈ Finset.range m, (specNorm R.A * (‖WithLp.toLp 2 (R.x j)‖ +
        4 * R.γ j * ‖WithLp.toLp 2 (R.p j)‖) + R.ρ j)

/-- Under mathematical input spectral/precision bounds the full rounded program succeeds,
with an actual existing run, early-stop meaning and residual-gap guarantee. The error bound
`e` dominates scalar division, dot and axpy bounds. [StrakosTichy2002, (7.16)]. -/
theorem runs_solve {M : Machine K} {dec : K → ℝ} {em u e : ℝ} {ε : Blas1Err}
    {ok : ℕ → Prop} {n cap : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec ε ok I) (hok : ok n)
    (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I) (hAT : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hu : 0 ≤ u) (hd : 0 ≤ ε.dot n) (haa : 0 ≤ ε.axpy)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ε.dot n ≤ e) (hae : ε.axpy ≤ e) (he : e ≤ 1 / 100)
    (hprec : 3 * e * a' ≤ a)
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs) (hx0 : decv dec n xs = 0)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [b, x, x, r, p, v]) μ
      (solveCount n cap) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ Output dec A (decv dec n bs) e cap x r p v μ') := by
  have hw := (solveRoutine_meets (A := A) hS hM hB hok hA hCmp hAT ha hspec hu hd haa hem hue
    hde hae he hprec) [n, cap] [b, x, r, p, v] τ μ [bs, xs] rfl rfl hl (by routine_sep)
    (by reads) ⟨rfl, hx0, hwindow⟩ hz
  obtain ⟨μ', hrun, hpos, ys, hys, hrel⟩ := hw.wp fun _ _ h => h
  routine_nf at hys
  split_reads hys as (xs', rs, ps, vs)
  obtain ⟨rr, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs)
  obtain ⟨m, hm, hprefix, hstop⟩ := hrel
  have hpost : μ'.pos = μ.pos ∧ ∃ m ≤ cap, ∃ s rho,
      StoresValues dec n x r p v s rho μ' ∧ IsPrefix A (decv dec n bs) e m s rho ∧
        (m < cap → s.r = 0) :=
    ⟨hpos, m, hm, _, _, ⟨xs', rs, ps, rr, hys, rfl, rfl⟩, hprefix, hstop⟩
  refine (ConditionalRuns.of_run (Q := fun μ' => μ'.pos = μ.pos ∧ ∃ m ≤ cap, ∃ s rho,
    StoresValues dec n x r p v s rho μ' ∧ IsPrefix A (decv dec n bs) e m s rho ∧
      (m < cap → s.r = 0)) hrun hpost W).mono (le_of_eq (staticCost_solve ..))
    (staticPeak_solve_le ..) ?_
  rintro μ'' ⟨hpos, m, hm, s, rho, hstore, hprefix, hstop⟩
  refine ⟨hpos, ?_⟩
  rcases hprefix with ⟨rfl, rfl⟩ | ⟨R, hRA, hRb, hRe, hs, hrho⟩
  · left
    refine ⟨?_, rho, hstore⟩
    by_cases hc : cap = 0
    · exact Or.inl hc
    · exact Or.inr (hstop (Nat.pos_of_ne_zero hc))
  · right
    refine ⟨m, R, hm, hRA, hRb, hRe, ?_, ?_, R.norm_sub_mulVec_x_sub_r_le⟩
    · simpa only [hs, hrho] using hstore
    · simpa only [← hs] using hstop

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
