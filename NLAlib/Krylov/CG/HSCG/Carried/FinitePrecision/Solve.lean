/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Alg
public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Rounds

/-!
# Full rounded CG execution connected to the existing run mathematics

Input scalar/BLAS contracts, an exact oracle and spectral precision imply successful complete
execution. The actual output is either the zero-step state or an existing positive-length
CGRun with matching physical vectors and retained scalar. The accumulated residual gap is
then a direct application of the existing pure theorem, not a new program-specific estimate.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.solve_writes` composes initialization and rounds.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.runs_solve` returns a run and its residual-gap bound.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- A zero decoded initial iterate and spectral input precision suffice for complete rounded
execution and extraction; no trajectory or successful-execution hypothesis is assumed. -/
theorem solve_writes {M : Machine K} {dec : K → ℝ} {u e : ℝ} {ε : Blas1Err}
    {ok : ℕ → Prop} {n cap : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec ε ok I) (hok : ok n)
    (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hAT : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hu : 0 ≤ u) (hd : 0 ≤ ε.dot n) (haa : 0 ≤ ε.axpy)
    (hue : u ≤ e) (hde : ε.dot n ≤ e) (hae : ε.axpy ≤ e) (he : e ≤ 1 / 100)
    (hprec : 3 * e * a' ≤ a)
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {τ : Tape K} {μ : Mem K} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs) (hx0 : decv dec n xs = 0)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    Writes .total I τ solve (Env.frame [n, cap] [b, x, x, r, p, v])
      (Fp.blocks [x, r, p, v] [n, n, n, 1])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ m ≤ cap, ∃ s rho,
        StoresValues dec n x r p v s rho μ' ∧ IsPrefix A (decv dec n bs) e m s rho ∧
          (m < cap → s.r = 0)) μ := by
  have hl' : μ.Live [b, x, x, r, p, v] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.1, hl.2.2⟩
  refine Writes.seq_le (writes_frame rfl rfl hl'
    (initialize_writes hB hok hbx hbr hbp hbv hxr hxp hxv hrp hrv hpv hl hbs hxs hx0 hz))
    le_rfl fun μ₁ hfr ⟨hpos, rho, hstate, hcache⟩ => ?_
  have hl₁ : μ₁.Live [x, r, p, v] := by
    simp only [Mem.Live, hfr.length_eq]
    exact fun z hz' => hl z (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz' ⊢
      exact Or.inr hz')
  have hz₁ : μ₁.Room [x, r, p, v] [n, n, n, 1] := by
    simpa [Mem.Room, hfr.len_eq] using hz
  refine (writes_frame rfl rfl ((μ₁.live_append _ _).mpr ⟨hl₁, hl₁⟩)
    (rounds_writes hS hM hB hok hA hCmp hAT ha hspec hu hd haa hue hde hae he hprec
      hwindow hxr hxp hxv hrp hrv hpv hl₁ hstate hcache hz₁)).mono le_rfl ?_
  rintro μ₂ _ ⟨hpos₂, hpost⟩
  exact ⟨hpos₂.trans hpos, hpost⟩

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
theorem runs_solve {M : Machine K} {dec : K → ℝ} {u e : ℝ} {ε : Blas1Err}
    {ok : ℕ → Prop} {n cap : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec ε ok I) (hok : ok n)
    (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hAT : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hu : 0 ≤ u) (hd : 0 ≤ ε.dot n) (haa : 0 ≤ ε.axpy)
    (hue : u ≤ e) (hde : ε.dot n ≤ e) (hae : ε.axpy ≤ e) (he : e ≤ 1 / 100)
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
  have hw := solve_writes hS hM hB hok hA hCmp hAT ha hspec hu hd haa hue hde hae he hprec
    hwindow (τ := τ) hbx hbr hbp hbv hxr hxp hxv hrp hrv hpv hl hbs hxs hx0 hz
  obtain ⟨μ', hrun, hpost⟩ := hw.wp fun _ _ h => h
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
