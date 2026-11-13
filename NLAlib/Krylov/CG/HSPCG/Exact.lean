/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Alg
public import NLAlib.Krylov.CG.HSPCG.Spec
public import NLAlib.Ops.Blas.Decoded
public import NLAlib.Ops.Logic.Tactic

/-!
# Exact preconditioned Hestenes–Stiefel rounds

A round computes the existing PCG state recurrence. The two divisions use explicit
nonbreakdown of the incoming mathematical state. The preconditioner is the same exact
matrix-vector contract as the system matrix, under a separately counted operation name.

## Main results

* `NLAlib.Krylov.CG.HSPCG.step_spec` certifies the exact state update.
* `NLAlib.Krylov.CG.HSPCG.step_writes` composes a certified round as a stored-state update.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
  [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]

/-- Decode all four PCG state blocks. -/
def decodedState (dec : K → ℝ) (n : ℕ) (xs rs zs ps : List K) : PCGState ℝ (Fin n) :=
  ⟨decv dec n xs, decv dec n rs, decv dec n zs, decv dec n ps⟩

/-- The four state buffers are distinct and updated in place at the matrix dimension. -/
@[admNF] def StepOperands (n : ℕ) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d = [n] ∧ ∃ x r z p, ins = [x, r, z, p] ∧ outs = [x, r, z, p] ∧
    x.1 ≠ r.1 ∧ x.1 ≠ z.1 ∧ x.1 ≠ p.1 ∧ r.1 ≠ z.1 ∧ r.1 ≠ p.1 ∧ z.1 ≠ p.1

/-- The exact PCG state update, with both scalar divisors included in its domain. -/
@[simps (attr := storeNF)]
noncomputable def stepRel (dec : K → ℝ) {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℝ) :
    BlockRel K where
  nd := 1
  inLens d := [d.headD 0, d.headD 0, d.headD 0, d.headD 0]
  outLens d := [d.headD 0, d.headD 0, d.headD 0, d.headD 0]
  dom _ X _ := match X with
    | [xs, rs, zs, ps] => Nonbreakdown A (decodedState dec n xs rs zs ps)
    | _ => False
  rel _ X _ Y := match X, Y with
    | [xs, rs, zs, ps], [xs', rs', zs', ps'] =>
        decodedState dec n xs' rs' zs' ps' = pcgStep A M (decodedState dec n xs rs zs ps)
    | _, _ => False

private theorem decodedState_pcgStep {dec : K → ℝ} {n : ℕ}
    (A M : Matrix (Fin n) (Fin n) ℝ) (xs rs zs ps xs' rs' zs' ps' : List K) (a b : ℝ)
    (ha : a = (decv dec n rs ⬝ᵥ decv dec n zs) /
      (decv dec n ps ⬝ᵥ (A *ᵥ decv dec n ps)))
    (hb : b = (decv dec n rs' ⬝ᵥ decv dec n zs') / (decv dec n rs ⬝ᵥ decv dec n zs))
    (hx : decv dec n xs' = decv dec n xs + a • decv dec n ps)
    (hr : decv dec n rs' = decv dec n rs - a • (A *ᵥ decv dec n ps))
    (hz : decv dec n zs' = M *ᵥ decv dec n rs')
    (hp : decv dec n ps' = decv dec n zs' + b • decv dec n ps) :
    decodedState dec n xs' rs' zs' ps' = pcgStep A M (decodedState dec n xs rs zs ps) := by
  rw [pcgStep_eq]
  dsimp only [decodedState]
  rw [← ha, ← hr, ← hz, ← hb, ← hx, ← hp]

/-- Exact scalar, BLAS1, system and preconditioner contracts implement one nonbreaking PCG round. -/
theorem step_spec {F : Machine K} {dec : K → ℝ} {n : ℕ}
    {A M : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar F I) (hF : ExactModel dec F)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hM : IsExactPreconditioner dec M I) :
    (stepImpl (Op := Op) (Tst := Tst)).Triple I .total
      ((stepRel dec A M).spec (StepOperands n)) := by
  cert_intro [m] (x, r, z, p) → (x', r', z', p') reads (xs, rs, zs, ps)
  obtain ⟨hd, hx, hr, hz, hp, hxr, hxz, hxp, hrz, hrp, hzp⟩ := hadm
  subst m x' r' z' p'
  change Nonbreakdown A (decodedState dec n xs rs zs ps) at hdom
  refine writes_allocs (lens := [.var 0, .var 0, .const 4]) (ns := [n, n, 4]) rfl
    fun s₁ hs₁ hlen hB₁ => ?_
  have hq : s₁.len μ.store.length = n := by simpa using hlen 0 (by simp)
  have hu : s₁.len (μ.store.length + 1) = n := by simpa using hlen 1 (by simp)
  have ht : s₁.len (μ.store.length + 2) = 4 := by simpa using hlen 2 (by simp)
  dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
    List.length_cons, List.length_nil, Nat.add_zero] at *
  step hB.dot as m₁ hfr₁ ⟨hpos₁, ρ, hρ, heρ⟩
  step hA as m₂ hfr₂ ⟨hpos₂, qs, hqs, heq⟩
  step hB.dot as m₃ hfr₃ ⟨hpos₃, pq, hpq, hepq⟩
  step (hS .div) as m₄ hfr₄ ⟨hpos₄, a, ha, hea⟩
  step hB.axpy as m₅ hfr₅ ⟨hpos₅, xs', hxs', hex⟩
  step (hS .neg) as m₆ hfr₆ ⟨hpos₆, na, hna, hena⟩
  step hB.axpy as m₇ hfr₇ ⟨hpos₇, rs', hrs', her⟩
  step hM as m₈ hfr₈ ⟨hpos₈, zs', hzs', hez⟩
  step hB.dot as m₉ hfr₉ ⟨hpos₉, ρ', hρ', heρ'⟩
  have hx₉ : m₉.store.readBlock x.1 x.2 n = some xs' := by kept
  have hr₉ : m₉.store.readBlock r.1 r.2 n = some rs' := by kept
  have hz₉ : m₉.store.readBlock z.1 z.2 n = some zs' := by kept
  have hp₉ : m₉.store.readBlock p.1 p.2 n = some ps := by kept
  have hρ₉ : m₉.store.get (μ.store.length + 2) 0 = some ρ := by kept
  clear hfr₁ hfr₂ hfr₃ hfr₄ hfr₅ hfr₆ hfr₇ hfr₈
  step (hS .div) as m₁₀ hfr₁₀ ⟨hpos₁₀, b, hb, heb⟩
  step hB.copy as m₁₁ hfr₁₁ ⟨hpos₁₁, us, hus, hcopy₁⟩
  step hB.axpy as m₁₂ hfr₁₂ ⟨hpos₁₂, ps', hps', hep⟩
  step hB.copy as m₁₃ hfr₁₃ ⟨hpos₁₃, ps'', hps'', hcopy₂⟩
  have hρd := dotExactRel_decoded (dec := dec) (n := n) heρ
  have hpqd := dotExactRel_decoded (dec := dec) (n := n) hepq
  have hρd' := dotExactRel_decoded (dec := dec) (n := n) heρ'
  have hρ0 : dec ρ ≠ 0 := by rw [hρd]; exact hdom.1
  have hpq0 : dec pq ≠ 0 := by rw [hpqd, heq]; exact hdom.2
  have had : dec a = (decv dec n rs ⬝ᵥ decv dec n zs) /
      (decv dec n ps ⬝ᵥ (A *ᵥ decv dec n ps)) := by
    rw [← hea, hF.div ρ pq hpq0, hρd, hpqd, heq]
  have hbd : dec b = (decv dec n rs' ⬝ᵥ decv dec n zs') /
      (decv dec n rs ⬝ᵥ decv dec n zs) := by rw [← heb, hF.div ρ' ρ hρ0, hρd', hρd]
  have hnad : dec na = -dec a := hena ▸ hF.neg a
  have hrvec : decv dec n rs' = decv dec n rs - dec a • (A *ᵥ decv dec n ps) := by
    simpa [heq, hnad, sub_eq_add_neg, neg_smul] using axpyExactRel_decoded her
  have hpvec : decv dec n ps'' = decv dec n zs' + dec b • decv dec n ps := by
    rw [hcopy₂, axpyExactRel_decoded hep, hcopy₁]
  have hstep := decodedState_pcgStep A M xs rs zs ps xs' rs' zs' ps'' (dec a) (dec b)
    had hbd (axpyExactRel_decoded hex) hrvec hez hpvec
  intro s₂ hs₂ hB₂
  refine ⟨by simp [stepRel, hpos₁₃, hpos₁₂, hpos₁₁, hpos₁₀, hpos₉, hpos₈, hpos₇,
    hpos₆, hpos₅, hpos₄, hpos₃, hpos₂, hpos₁], [xs', rs', zs', ps''], ?_, hstep⟩
  exact Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept)
    (Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl)))

/-- The four buffers store a decoded mathematical PCG state. -/
def StoresState (dec : K → ℝ) (n : ℕ) (x r z p : ℕ × ℕ) (s : PCGState ℝ (Fin n))
    (μ : Mem K) : Prop :=
  ∃ xs rs zs ps, μ.readBlocks [x, r, z, p] [n, n, n, n] = some [xs, rs, zs, ps] ∧
    decodedState dec n xs rs zs ps = s

/-- A certified round advances a stored PCG state without exposing its implementation. -/
theorem step_writes {F : Machine K} {dec : K → ℝ} {n : ℕ}
    {A M : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar F I) (hF : ExactModel dec F)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hM : IsExactPreconditioner dec M I) {τ : Tape K} {μ : Mem K}
    {x r z p : ℕ × ℕ} {s : PCGState ℝ (Fin n)}
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [x, r, z, p]) (hstate : StoresState dec n x r z p s μ)
    (hdom : Nonbreakdown A s) (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    Writes .total I τ step (Env.frame [n] [x, r, z, p, x, r, z, p])
      (Fp.blocks [x, r, z, p] [n, n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ StoresState dec n x r z p (pcgStep A M s) μ') μ := by
  obtain ⟨xs, rs, zs, ps, hread, hstate⟩ := hstate
  refine ((step_spec hS hF hB hA hM).writes_blocks rfl
    ⟨rfl, x, r, z, p, rfl, rfl, hxr, hxz, hxp, hrz, hrp, hzp⟩
    ((μ.live_append _ _).mpr ⟨hl, hl⟩) hread
    (by change Nonbreakdown A (decodedState dec n xs rs zs ps); rwa [hstate])
    hz (by disjoint)).mono le_rfl ?_
  rintro μ' _ ⟨hpos, ys, hys, hrel⟩
  obtain ⟨xs', rs', zs', ps', rfl⟩ := List.length_eq_four.mp
    (by simpa [stepRel] using congrArg List.length (Mem.map_length_of_readBlocks hys))
  exact ⟨by simpa [stepRel] using hpos, xs', rs', zs', ps', hys,
    by simpa only [stepRel_rel, hstate] using hrel⟩

end NLAlib.Krylov.CG.HSPCG
