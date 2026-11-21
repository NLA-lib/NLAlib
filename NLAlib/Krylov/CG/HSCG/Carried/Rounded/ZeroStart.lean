/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stability
public import NLAlib.Krylov.CG.HSCG.Carried.ZeroStart

/-!
# Rounded capped conjugate gradient from the zero iterate

The routine `NLAlib.Krylov.CG.HSCG.Carried.Rounded.zeroStartRoutine` reads the right-hand side
and writes the iterate, the residual, the direction and the cell of the retained residual
product: it fills the iterate with literal zeros and runs the rounded capped solver
`NLAlib.Krylov.CG.HSCG.Carried.Rounded.solveRoutine` on it, each used by its judgment. Its
specification states the stable output claim on the written blocks
(`NLAlib.Krylov.CG.HSCG.Carried.Rounded.StableValues`).

## Main definitions

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.zeroStart`: the tree.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.zeroStartRoutine`,
  `NLAlib.Krylov.CG.HSCG.Carried.Rounded.zeroStartSpec`: the routine and its specification.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.stableValues_of_solve`: the claim of the rounded solver
  gives the stable output claim on the output blocks.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.zeroStartRoutine_meets`: the routine meets its
  specification.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]

/-- The stable output claim from the claim of the rounded solver: a successful rounded
prefix of length at most the cap, stopping early only at a zero residual, held by the four output
blocks, gives the stable output claim on those blocks, under the spectral and precision bounds.
Both zero-start routines (matrix-free here, on a stored matrix in `StoredRoutine.lean`) state
their claim in this form. -/
theorem stableValues_of_solve {dec : K → ℝ} {n cap : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {e a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {bs xs rs ps : List K} {rr : K}
    (hpost : ∃ m ≤ cap, IsPrefix A (decv dec n bs) e m (decodedState dec n xs rs ps) (dec rr) ∧
      (m < cap → (decodedState dec n xs rs ps).r = 0)) :
    StableValues dec A (decv dec n bs) e a a' cap [xs, rs, ps, [rr]] := by
  obtain ⟨m, hm, hprefix, hstop⟩ := hpost
  have hhold : HoldsValues dec n [xs, rs, ps, [rr]] (decodedState dec n xs rs ps) (dec rr) :=
    ⟨xs, rs, ps, rr, rfl, rfl, rfl⟩
  generalize decodedState dec n xs rs ps = s at hhold hprefix hstop
  generalize dec rr = rho at hhold hprefix
  rcases hprefix with ⟨rfl, rfl⟩ | ⟨R, hRA, hRb, hRe, hs, hrho⟩
  · left
    refine ⟨?_, rho, hhold⟩
    by_cases hc : cap = 0
    · exact Or.inl hc
    · exact Or.inr (hstop (Nat.pos_of_ne_zero hc))
  · right
    refine ⟨m, R, hm, hRA, hRb, hRe, by simpa only [hs, hrho] using hhold,
      by simpa only [← hs] using hstop, ?_⟩
    have he0 := R.ε_nonneg
    have hsmall : (m : ℝ) ^ 2 * Real.sqrt m * R.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
      calc
        _ ≤ (cap : ℝ) ^ 2 * Real.sqrt cap * R.ε * (a' / a) ^ 2 := by gcongr
        _ ≤ _ := by rwa [hRe]
    exact stability_of_run R ha (by rwa [hRA]) hsmall

variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- Zero the iterate, then run the rounded solver. Index variables: `n`, `cap`, then the offsets
of `b`, `x`, `r`, `p`, `v`. -/
def zeroStart : Stmt Op Tst := ops% [n, cap] (B) → (X, R, P, RHO) {
  run (fillRoutine (Op := Op) (Tst := Tst) (Has.inj (ScalarOp.lit 0))) [n] (X);
  run (solveRoutine (Op := Op) (Tst := Tst)) [n, cap] (B, X, R, P, RHO)
}

/-- Rounded capped conjugate gradient from the zero iterate: the right-hand side is read, and
the iterate, the residual, the direction and the cell of the retained residual product are
written. -/
def zeroStartRoutine : Routine Op Tst :=
  routine% [n, cap] (b : n) → (x : n, r : n, p : n, rho : 1) := zeroStart

/-- For the order `n` and a cap within the precision window, the four written blocks satisfy the
stable output claim for the right-hand side read. -/
noncomputable def zeroStartSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (e a a' : ℝ) : Routine.Spec K :=
  spec% [m, cap] (bs) → (xs, rs, ps, vs)
    requires m = n ∧ (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤ 1 / 10 ^ 5
    ensures StableValues dec A (decv dec n bs) e a a' cap [xs, rs, ps, vs]

/-- Rounded capped conjugate gradient from the zero iterate meets its specification under the
standard model of arithmetic, rounded vector and matrix-vector contracts, and spectral and
precision bounds on the matrix: the iterate is zeroed by its routine, then the rounded solver
runs, each used by its judgment, and its claim gives the stable output claim. -/
theorem zeroStartRoutine_meets {M : Machine K} {dec : K → ℝ} {em u e : ℝ} {ε : Blas1Err}
    {ok : ℕ → Prop} {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec ε ok I) (hok : ok n)
    (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I) (hAT : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hu : 0 ≤ u) (hd : 0 ≤ ε.dot n) (haa : 0 ≤ ε.axpy)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ε.dot n ≤ e) (hae : ε.axpy ≤ e) (he : e ≤ 1 / 100)
    (hprec : 3 * e * a' ≤ a) :
    (zeroStartRoutine (Op := Op) (Tst := Tst)).Meets I (zeroStartSpec dec A e a a') := by
  routine_intro [n', cap] (b, x, r, p, v) reads (bs)
  obtain ⟨hn, hwindow⟩ := hpre
  obtain rfl : n = n' := hn.symm
  have hx0 : decv dec n (List.replicate n (M.lit 0)) = 0 := by
    ext i
    simp [decv, vec, i.isLt, hM.zero]
  call (fillRoutine_meets (Tst := Tst) (hS (.lit 0))) [n] (x) as m₁ hfr₁ hpos₁ (xs₀) hzero
  obtain rfl : xs₀ = List.replicate n (M.lit 0) := hzero
  call (solveRoutine_meets (A := A) hS hM hB hok hA hCmp hAT ha hspec hu hd haa hem hue hde hae
    he hprec) [n, cap] (b, x, r, p, v) (pre := ⟨rfl, hx0, hwindow⟩)
    as m₂ hfr₂ hpos₂ (xs', rs, ps, vs) hpost
  obtain ⟨rr, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs)
  routine_exit
  exact stableValues_of_solve ha hspec hwindow hpost

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
