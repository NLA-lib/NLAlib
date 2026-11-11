/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Exact
public import NLAlib.Krylov.CG.Math.Preconditioned

/-!
# Composition of exact conjugate-gradient rounds

The loop invokes the certified round through its block interface. Its invariant states that
the buffers hold the iterated mathematical PCG state. Nonbreakdown is required only at the
rounds that the loop executes.

## Main results

* `NLAlib.Krylov.CG.HSPCG.roundsRel` specifies a block of active rounds.
* `NLAlib.Krylov.CG.HSPCG.rounds_spec` certifies their composition.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open Ops

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]

/-- The round loop updates the same four state buffers at the dimension of the matrix. -/
@[admNF] def RoundsOperands (n : ℕ) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => StepOperands n [d.headD 0] ins outs

/-- The result is the iterated mathematical PCG state, on a nonbreaking prefix. -/
@[simps (attr := storeNF)]
noncomputable def roundsRel (dec : K → ℝ) {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) :
    BlockRel K where
  nd := 2
  inLens d := [d.headD 0, d.headD 0, d.headD 0, d.headD 0]
  outLens d := [d.headD 0, d.headD 0, d.headD 0, d.headD 0]
  dom d X _ := match X with
    | [xs, rs, zs, ps] => ∀ j < d.getD 1 0,
        Nonbreakdown A ((pcgStep A P)^[j] (decodedState dec n xs rs zs ps))
    | _ => False
  rel d X _ Y := match X, Y with
    | [xs, rs, zs, ps], [xs', rs', zs', ps'] =>
        decodedState dec n xs' rs' zs' ps' =
          (pcgStep A P)^[d.getD 1 0] (decodedState dec n xs rs zs ps)
    | _, _ => False

/-- The round loop advances an already stored state by the requested nonbreaking prefix. -/
theorem rounds_writes {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I)
    {τ : Tape K} {μ : Mem K} {k : ℕ} {x r z p : ℕ × ℕ} {s : PCGState ℝ (Fin n)}
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [x, r, z, p]) (hstate : StoresState dec n x r z p s μ)
    (hdom : ∀ j < k, Nonbreakdown A ((pcgStep A P)^[j] s))
    (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    Writes .total I τ rounds (Env.frame [n, k] [x, r, z, p, x, r, z, p])
      (Fp.blocks [x, r, z, p] [n, n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ StoresState dec n x r z p ((pcgStep A P)^[k] s) μ') μ := by
  refine writes_loop rfl (fun _ => Fp.blocks [x, r, z, p] [n, n, n, n])
    (fun _ _ => le_rfl)
    (fun j μ' => μ'.pos = μ.pos ∧ StoresState dec n x r z p ((pcgStep A P)^[j] s) μ')
    ⟨rfl, hstate⟩ fun j hj μ' hfr ⟨hpos, hstate'⟩ => ?_
  have hl' : μ'.Live [x, r, z, p] := by simpa only [Mem.Live, hfr.length_eq] using hl
  have hz' : μ'.Room [x, r, z, p] [n, n, n, n] := by simpa [Mem.Room, hfr.len_eq] using hz
  refine (writes_frame rfl rfl ((μ'.live_append _ _).mpr ⟨hl', hl'⟩)
    (step_writes hS hM hB hA hP hxr hxz hxp hrz hrp hzp hl' hstate' (hdom j hj) hz')).mono le_rfl ?_
  intro μ'' _ ⟨hpos', hstate''⟩
  exact ⟨hpos'.trans hpos, by simpa only [Function.iterate_succ_apply'] using hstate''⟩

/-- Certified rounds compose into a certified loop without unfolding the round program. -/
theorem rounds_spec {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I) :
    (roundsImpl (Op := Op) (Tst := Tst)).Meets I .total
      ((roundsRel dec A P).spec (RoundsOperands n)) := by
  cert_intro [m, k] (x, r, z, p) → (x', r', z', p') reads (xs, rs, zs, ps)
  obtain ⟨hd, hx, hr, hz, hp, hxr, hxz, hxp, hrz, hrp, hzp⟩ := hadm
  subst m x' r' z' p'
  change ∀ j < k, Nonbreakdown A ((pcgStep A P)^[j] (decodedState dec n xs rs zs ps)) at hdom
  have hl₀ : μ.Live [x, r, z, p] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1⟩
  have hz₀ : μ.Room [x, r, z, p] [n, n, n, n] := by
    simpa only [Mem.room_cons, Mem.room_nil, and_true] using hz
  refine (rounds_writes hS hM hB hA hP hxr hxz hxp hrz hrp hzp hl₀
    ⟨xs, rs, zs, ps, hr_0, rfl⟩ hdom hz₀).mono le_rfl ?_
  rintro μ' _ ⟨hpos, xs', rs', zs', ps', hread, hstate⟩
  exact ⟨by simpa using hpos, [xs', rs', zs', ps'], hread, hstate⟩

end NLAlib.Krylov.CG.HSPCG
