/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Exact
public import NLAlib.Krylov.CG.Math.Recurrence

/-!
# Composition of exact conjugate-gradient rounds

The loop invokes the certified round through its block interface. Its invariant states that
the buffers hold the iterated mathematical CG state. Nonbreakdown is required only at the
rounds that the loop executes.

## Main results

* `NLAlib.Krylov.CG.HSCG.roundsRel` specifies a block of active rounds.
* `NLAlib.Krylov.CG.HSCG.rounds_spec` certifies their composition.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG

open Ops

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- The round loop updates the same three state buffers at the dimension of the matrix. -/
@[admNF] def RoundsOperands (n : ℕ) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => StepOperands n [d.headD 0] ins outs

/-- The result is the iterated mathematical CG state, on a nonbreaking prefix. -/
@[simps (attr := storeNF)]
noncomputable def roundsRel (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    BlockRel K where
  nd := 2
  inLens d := [d.headD 0, d.headD 0, d.headD 0]
  outLens d := [d.headD 0, d.headD 0, d.headD 0]
  dom d X _ := match X with
    | [xs, rs, ps] => ∀ j < d.getD 1 0,
        Nonbreakdown A ((cgStep A)^[j] (decodedState dec n xs rs ps))
    | _ => False
  rel d X _ Y := match X, Y with
    | [xs, rs, ps], [xs', rs', ps'] =>
        decodedState dec n xs' rs' ps' = (cgStep A)^[d.getD 1 0] (decodedState dec n xs rs ps)
    | _, _ => False

/-- Certified rounds compose into a certified loop without unfolding the round program. -/
theorem rounds_spec {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I) :
    (roundsImpl (Op := Op) (Tst := Tst)).Meets I .total
      ((roundsRel dec A).spec (RoundsOperands n)) := by
  cert_intro [m, k] (x, r, p) → (x', r', p') reads (xs, rs, ps)
  obtain ⟨hd, hx, hr, hp, hxr, hxp, hrp⟩ := hadm
  subst m x' r' p'
  change ∀ j < k, Nonbreakdown A ((cgStep A)^[j] (decodedState dec n xs rs ps)) at hdom
  have hl₀ : μ.Live [x, r, p] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.2.1⟩
  have hz₀ : μ.Room [x, r, p] [n, n, n] := by
    simpa only [Mem.room_cons, Mem.room_nil, and_true] using hz
  refine (writes_loop rfl (fun _ => Fp.blocks [x, r, p] [n, n, n])
    (fun _ _ => le_rfl)
    (fun j μ' => μ'.pos = μ.pos ∧ StoresState dec n x r p
      ((cgStep A)^[j] (decodedState dec n xs rs ps)) μ')
    ⟨rfl, xs, rs, ps, hr_0, rfl⟩ fun j hj μ' hfr ⟨hpos, hstate⟩ => ?_).mono le_rfl ?_
  · have hl' : μ'.Live [x, r, p] := by simpa only [Mem.Live, hfr.length_eq] using hl₀
    have hz' : μ'.Room [x, r, p] [n, n, n] := by simpa [Mem.Room, hfr.len_eq] using hz₀
    refine (writes_frame rfl rfl ((μ'.live_append _ _).mpr ⟨hl', hl'⟩)
      (step_writes hS hM hB hA hxr hxp hrp hl' hstate (hdom j hj) hz')).mono le_rfl ?_
    intro μ'' _ ⟨hpos', hstate'⟩
    exact ⟨hpos'.trans hpos, by simpa only [Function.iterate_succ_apply'] using hstate'⟩
  · rintro μ' _ ⟨hpos, xs', rs', ps', hread, hstate⟩
    exact ⟨by simpa using hpos, [xs', rs', ps'], hread, hstate⟩

/-- A nonbreaking prefix terminates with the iterated exact state, at the per-round operation
count and with scratch reused between rounds. -/
theorem runs_rounds {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {k : ℕ} {x r p : ℕ × ℕ}
    {xs rs ps : List K} (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [x, r, p]) (hx : μ.store.readBlock x.1 x.2 n = some xs)
    (hr : μ.store.readBlock r.1 r.2 n = some rs)
    (hp : μ.store.readBlock p.1 p.2 n = some ps)
    (hdom : ∀ j < k, Nonbreakdown A ((cgStep A)^[j] (decodedState dec n xs rs ps)))
    (hz : μ.Room [x, r, p] [n, n, n]) :
    Runs I W τ rounds (Env.frame [n, k] [x, r, p, x, r, p]) μ
      (k • stepCount n) (stepPeak W n)
      ((roundsRel dec A).Post [n, k] [xs, rs, ps] [x, r, p] [] μ) := by
  refine ((rounds_spec hS hM hB hA).runs_rel W (d := [n, k]) (ins := [x, r, p])
    (outs := [x, r, p]) (xs := [xs, rs, ps]) rfl
    ⟨rfl, x, r, p, rfl, rfl, hxr, hxp, hrp⟩ ((μ.live_append _ _).mpr ⟨hl, hl⟩)
    (Mem.readBlocks_of_cons hx (Mem.readBlocks_of_cons hr (Mem.readBlocks_of_cons hp rfl)))
    hdom hz).mono (le_of_eq (staticCost_rounds ..)) (staticPeak_rounds_le ..) ?_
  intro μ' hpost
  exact hpost

end NLAlib.Krylov.CG.HSCG
