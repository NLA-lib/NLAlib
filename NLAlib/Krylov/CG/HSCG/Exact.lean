/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Spec
public import NLAlib.Krylov.CG.HSCG.Alg
public import NLAlib.Ops.Blas.Decoded
public import NLAlib.Ops.Logic.Tactic

/-!
# Exact Hestenes–Stiefel rounds

The stored vectors decode to the existing mathematical CG state. A round is specified against
exact scalar, BLAS1 and matrix-vector contracts. The state must satisfy nonbreakdown because
the scalar contract constrains division only at nonzero divisors.

## Main results

* `NLAlib.Krylov.CG.HSCG.decodedState` reads a mathematical state from three lists.
* `NLAlib.Krylov.CG.HSCG.stepRel` is the exact one-round contract.
* `NLAlib.Krylov.CG.HSCG.step_spec` certifies the round against exact operation contracts.
* `NLAlib.Krylov.CG.HSCG.runs_step` supplies its operation counts and workspace.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- Decode the iterate, residual and direction blocks as the mathematical CG state. -/
def decodedState (dec : K → ℝ) (n : ℕ) (xs rs ps : List K) : CGState ℝ (Fin n) :=
  ⟨decv dec n xs, decv dec n rs, decv dec n ps⟩

/-- The round updates three different buffers in place, at the dimension of the matrix. -/
@[admNF] def StepOperands (n : ℕ) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d = [n] ∧ ∃ x r p, ins = [x, r, p] ∧ outs = [x, r, p] ∧
    x.1 ≠ r.1 ∧ x.1 ≠ p.1 ∧ r.1 ≠ p.1

/-- A round computes the existing Hestenes–Stiefel recurrence on the decoded state. -/
@[simps (attr := storeNF)]
noncomputable def stepRel (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    BlockRel K where
  nd := 1
  inLens d := [d.headD 0, d.headD 0, d.headD 0]
  outLens d := [d.headD 0, d.headD 0, d.headD 0]
  dom _ X _ := match X with
    | [xs, rs, ps] => Nonbreakdown A (decodedState dec n xs rs ps)
    | _ => False
  rel _ X _ Y := match X, Y with
    | [xs, rs, ps], [xs', rs', ps'] =>
        decodedState dec n xs' rs' ps' = cgStep A (decodedState dec n xs rs ps)
    | _, _ => False

private theorem decodedState_step {dec : K → ℝ} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (xs rs ps xs' rs' ps' : List K) (a b : ℝ)
    (ha : a = (decv dec n rs ⬝ᵥ decv dec n rs) /
      (decv dec n ps ⬝ᵥ (A *ᵥ decv dec n ps)))
    (hb : b = (decv dec n rs' ⬝ᵥ decv dec n rs') / (decv dec n rs ⬝ᵥ decv dec n rs))
    (hx : decv dec n xs' = decv dec n xs + a • decv dec n ps)
    (hr : decv dec n rs' = decv dec n rs - a • (A *ᵥ decv dec n ps))
    (hp : decv dec n ps' = decv dec n rs' + b • decv dec n ps) :
    decodedState dec n xs' rs' ps' = cgStep A (decodedState dec n xs rs ps) := by
  rw [cgStep_eq]
  change CGState.mk _ _ _ = CGState.mk
    (decv dec n xs + (_ : ℝ) • decv dec n ps)
    (decv dec n rs - (_ : ℝ) • (A *ᵥ decv dec n ps))
    ((decv dec n rs - (_ : ℝ) • (A *ᵥ decv dec n ps)) + (_ : ℝ) • decv dec n ps)
  dsimp only [decodedState]
  have hrf : (fun i => decv dec n rs i - a * (A *ᵥ decv dec n ps) i) =
      decv dec n rs' := hr.symm
  rw [← ha, ← hr, hrf, ← hb, ← hx, ← hp]

/-- Exact operation contracts implement one nonbreaking Hestenes–Stiefel round. -/
theorem step_spec {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I) :
    (stepImpl (Op := Op) (Tst := Tst)).Meets I .total
      ((stepRel dec A).spec (StepOperands n)) := by
  cert_intro [m] (x, r, p) → (x', r', p') reads (xs, rs, ps)
  obtain ⟨hd, hx, hr, hp, hxr, hxp, hrp⟩ := hadm
  subst m x' r' p'
  change Nonbreakdown A (decodedState dec n xs rs ps) at hdom
  refine writes_allocs (lens := [.var 0, .var 0, .const 4]) (ns := [n, n, 4]) rfl
    fun s₁ hs₁ hlen hB₁ => ?_
  have hq : s₁.len μ.store.length = n := by simpa using hlen 0 (by simp)
  have hz : s₁.len (μ.store.length + 1) = n := by simpa using hlen 1 (by simp)
  have ht : s₁.len (μ.store.length + 2) = 4 := by simpa using hlen 2 (by simp)
  dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
    List.length_cons, List.length_nil, Nat.add_zero] at *
  step hB.dot as m₁ hfr₁ ⟨hpos₁, rr, hrr, herr⟩
  step hA as m₂ hfr₂ ⟨hpos₂, qs, hqs, heq⟩
  step hB.dot as m₃ hfr₃ ⟨hpos₃, pq, hpq, hepq⟩
  step (hS .div) as m₄ hfr₄ ⟨hpos₄, a, ha, hea⟩
  step hB.axpy as m₅ hfr₅ ⟨hpos₅, xs', hxs', hex⟩
  step (hS .neg) as m₆ hfr₆ ⟨hpos₆, na, hna, hena⟩
  step hB.axpy as m₇ hfr₇ ⟨hpos₇, rs', hrs', her⟩
  step hB.dot as m₈ hfr₈ ⟨hpos₈, rr', hrr', herr'⟩
  -- Keep the reads needed by the direction update and discard the earlier frame chain.
  have hx₈ : m₈.store.readBlock x.1 x.2 n = some xs' := by kept
  have hr₈ : m₈.store.readBlock r.1 r.2 n = some rs' := by kept
  have hp₈ : m₈.store.readBlock p.1 p.2 n = some ps := by kept
  have hrr₈ : m₈.store.get (μ.store.length + 2) 0 = some rr := by kept
  clear hfr₁ hfr₂ hfr₃ hfr₄ hfr₅ hfr₆ hfr₇
  step (hS .div) as m₉ hfr₉ ⟨hpos₉, b, hb, heb⟩
  step hB.copy as m₁₀ hfr₁₀ ⟨hpos₁₀, zs, hzs, rfl⟩
  step hB.axpy as m₁₁ hfr₁₁ ⟨hpos₁₁, ps', hps', hep⟩
  step hB.copy as m₁₂ hfr₁₂ ⟨hpos₁₂, ps'', hps'', rfl⟩
  have hrrd := dotExactRel_decoded (dec := dec) (n := n) herr
  have hpqd := dotExactRel_decoded (dec := dec) (n := n) hepq
  have hrrd' := dotExactRel_decoded (dec := dec) (n := n) herr'
  have hrr0 : dec rr ≠ 0 := by rw [hrrd]; exact hdom.1
  have hpq0 : dec pq ≠ 0 := by rw [hpqd, heq]; exact hdom.2
  have had : dec a = (decv dec n rs ⬝ᵥ decv dec n rs) /
      (decv dec n ps ⬝ᵥ (A *ᵥ decv dec n ps)) := by
    rw [← hea, hM.div rr pq hpq0, hrrd, hpqd, heq]
  have hbd : dec b = (decv dec n zs ⬝ᵥ decv dec n zs) /
      (decv dec n rs ⬝ᵥ decv dec n rs) := by
    rw [← heb, hM.div rr' rr hrr0, hrrd', hrrd]
  have hnad : dec na = -dec a := hena ▸ hM.neg a
  have hrvec : decv dec n zs = decv dec n rs - dec a • (A *ᵥ decv dec n ps) := by
    simpa [heq, hnad, sub_eq_add_neg, neg_smul] using
      (axpyExactRel_decoded (dec := dec) (n := n) her)
  have hstep := decodedState_step A xs rs ps xs' zs ps'' (dec a) (dec b) had hbd
    (axpyExactRel_decoded hex) hrvec (axpyExactRel_decoded hep)
  intro s₂ hs₂ hB₂
  refine ⟨by simp [stepRel, hpos₁₂, hpos₁₁, hpos₁₀, hpos₉, hpos₈, hpos₇, hpos₆,
    hpos₅, hpos₄, hpos₃, hpos₂, hpos₁], [xs', zs, ps''], ?_, hstep⟩
  exact Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept)
    (Mem.readBlocks_of_cons (by kept) rfl))

/-- The exact round terminates with the specified CG state, its closed operation counts and
its declared workspace. The output contract also preserves every cell outside the three state
blocks and preserves the tape position. -/
theorem runs_step {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {x r p : ℕ × ℕ}
    {xs rs ps : List K} (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [x, r, p]) (hx : μ.store.readBlock x.1 x.2 n = some xs)
    (hr : μ.store.readBlock r.1 r.2 n = some rs)
    (hp : μ.store.readBlock p.1 p.2 n = some ps)
    (hdom : Nonbreakdown A (decodedState dec n xs rs ps))
    (hz : μ.Room [x, r, p] [n, n, n]) :
    Runs I W τ step (Env.frame [n] [x, r, p, x, r, p]) μ
      (stepCount n) (stepPeak W n)
      ((stepRel dec A).Post [n] [xs, rs, ps] [x, r, p] [] μ) := by
  refine ((step_spec hS hM hB hA).runs_rel W (d := [n]) (ins := [x, r, p])
    (outs := [x, r, p]) (xs := [xs, rs, ps]) rfl
    ⟨rfl, x, r, p, rfl, rfl, hxr, hxp, hrp⟩
    (by
      change μ.Live [x, r, p, x, r, p]
      simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
      exact ⟨hl.1, hl.2.1, hl.2.2, hl⟩)
    (Mem.readBlocks_of_cons hx (Mem.readBlocks_of_cons hr (Mem.readBlocks_of_cons hp rfl)))
    hdom hz).mono (le_of_eq (staticCost_step ..)) (staticPeak_step_le ..) ?_
  intro μ' hpost
  exact hpost

end NLAlib.Krylov.CG.HSCG
