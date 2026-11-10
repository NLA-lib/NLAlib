/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Hutch
public import NLAlib.Ops.Profiles.Random

/-!
# The Girard–Hutchinson estimator, linked: probes drawn entry by entry

One application of the law-level linking lemma to the profile `Rand.gaussLoop`.

## Main results

* `NLAlib.Ops.Examples.runsLaw_hutch_link`: the program that draws each probe by `n` scalar
  draws has the same law-level statement, within the same scratch cells.
* `NLAlib.Ops.Examples.push_gaussLoop_hutchCount`: its counts, pushed forward.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib.Ops.Examples

variable {K Tst : Type} [Inhabited K] [MeasurableSpace K]

/-- **The corollary for the program with scalar draws**: over every interpretation meeting the
base contracts whose operations read the tape only in their windows, for every sample `N n`
scalar draws and `N` products, dot products and additions within `2 n + 1` scratch cells; the
estimate is unbiased with the variance of one quadratic form divided by `N`. -/
theorem runsLaw_hutch_link {dec : K → ℝ} {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {I : Interp ROp Tst K} (hI : IsRandBase dec A I) (hloc : ∀ o, I.TapeLocal o (randWindow o))
    {law : ℕ → Measure K} {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ξ : Ω → Tape K}
    (h : IsTapeLaw law P ξ) (hdec : Measurable dec)
    (hiso : IsIsotropic (probeLaw dec (law Stream.gauss) n))
    (hq : MemLp (quadForm A) 2 (probeLaw dec (law Stream.gauss) n)) {N : ℕ} (hN : 0 < N)
    {e : ℕ × ℕ} {m : Mem K} {z₀ : K} (he : m.store.get e.1 e.2 = some z₀) (hz : dec z₀ = 0) :
    RunsLaw I (fun _ _ => 0) ξ (hutch.link Rand.gaussLoop.table) ⟨[N, n, e.2], [e.1]⟩ m
      (Count.push Rand.gaussLoop.cost (hutchCount N n)) (n + (n + 1))
      (HutchPost dec N n e m) fun X => ∫ ω, X ω / N ∂P = A.trace ∧
        Var[fun ω => X ω / N; P] = Var[quadForm A; probeLaw dec (law Stream.gauss) n] / N := by
  have := (Rand.gaussLoop_certifies dec A).runsLaw (ξ := ξ)
    (fun J hJ _ => runsLaw_hutch hJ h hdec hiso hq _ hN he hz) hI hloc
  simpa [Rand.gaussLoop, hutchPeak] using this

omit [Inhabited K] [MeasurableSpace K] in
/-- **The counts of the linked estimator**: per probe, `n` scalar draws, a product, a dot product
and an addition. -/
theorem push_gaussLoop_hutchCount (N n : ℕ) :
    Count.push Rand.gaussLoop.cost (hutchCount (Tst := Tst) N n) =
      N • (n • Count.one .draw [] + (Count.one .matvec [n] + (Count.one .dot [n] +
        Count.one .add []))) := by
  simp [hutchCount, Rand.gaussLoop, Rand.gaussCost]

end NLAlib.Ops.Examples
