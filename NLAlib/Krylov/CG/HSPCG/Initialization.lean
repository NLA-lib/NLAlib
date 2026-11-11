/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Exact

/-!
# Initialization of the Hestenes–Stiefel state

The initial iterate is retained while the residual and search direction are initialized to
the right-hand side minus its matrix-vector product. All arithmetic is performed through
the shared operations. The exact certificate identifies the stored state with the existing
PCG recurrence at index zero.

## Main results

* `NLAlib.Krylov.CG.HSPCG.initialize_spec` certifies its exact state.
* `NLAlib.Krylov.CG.HSPCG.initialize_writes` composes the stored initial state with later blocks.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]

/-- The right-hand side, iterate, residual and direction use four different buffers; the
initial iterate is retained in place. -/
@[admNF] def InitializeOperands (n : ℕ) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d = [n] ∧ ∃ b x r z p, ins = [b, x] ∧ outs = [x, r, z, p] ∧
    b.1 ≠ x.1 ∧ b.1 ≠ r.1 ∧ b.1 ≠ z.1 ∧ b.1 ≠ p.1 ∧
    x.1 ≠ r.1 ∧ x.1 ≠ z.1 ∧ x.1 ≠ p.1 ∧ r.1 ≠ z.1 ∧ r.1 ≠ p.1 ∧ z.1 ≠ p.1

/-- Initialization outputs the exact mathematical state at index zero. -/
@[simps (attr := storeNF)]
noncomputable def initializeRel (dec : K → ℝ) {n : ℕ}
    (A P : Matrix (Fin n) (Fin n) ℝ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0, d.headD 0]
  outLens d := [d.headD 0, d.headD 0, d.headD 0, d.headD 0]
  rel _ X _ Y := match X, Y with
    | [bs, xs], [xs', rs, zs, ps] =>
        decodedState dec n xs' rs zs ps = pcgState A P (decv dec n bs) (decv dec n xs) 0
    | _, _ => False

/-- Exact scalar, vector and operator contracts establish the initial PCG recurrence state. -/
theorem initialize_spec {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I) :
    (initializeImpl (Op := Op) (Tst := Tst)).Meets I .total
      ((initializeRel dec A P).spec (InitializeOperands n)) := by
  cert_intro [m] (b, x) → (x', r, z, p) reads (bs, xs)
  obtain ⟨hd, hx, hbx, hbr, hbz, hbp, hxr, hxz, hxp, hrz, hrp, hzp⟩ := hadm
  subst m x'
  refine writes_allocs (lens := [.var 0, .const 1]) (ns := [n, 1]) rfl
    fun s₁ hs₁ hlen hB₁ => ?_
  have hq : s₁.len μ.store.length = n := by simpa using hlen 0 (by simp)
  have ht : s₁.len (μ.store.length + 1) = 1 := by simpa using hlen 1 (by simp)
  dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
    List.length_cons, List.length_nil, Nat.add_zero] at *
  step hB.copy as m₁ hfr₁ ⟨hpos₁, rs₀, hrs₀, hcopy₀⟩
  subst rs₀
  step hA as m₂ hfr₂ ⟨hpos₂, qs, hqs, heq⟩
  step (hS (.lit (-1))) as m₃ hfr₃ ⟨hpos₃, a, ha, hea⟩
  step hB.axpy as m₄ hfr₄ ⟨hpos₄, rs, hrs, her⟩
  step hP as m₅ hfr₅ ⟨hpos₅, zs, hzs, hez⟩
  step hB.copy as m₆ hfr₆ ⟨hpos₆, ps, hps, hcopy⟩
  subst ps
  have had : dec a = -1 := by rw [← hea, hM.lit]; norm_num
  have hrd : decv dec n rs = decv dec n bs - A *ᵥ decv dec n xs := by
    simpa [had, heq, sub_eq_add_neg] using
      (axpyExactRel_decoded (dec := dec) (n := n) her)
  intro s₂ hs₂ hB₂
  refine ⟨by simp [initializeRel, hpos₆, hpos₅, hpos₄, hpos₃, hpos₂, hpos₁],
    [xs, rs, zs, zs], ?_, ?_⟩
  · exact Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept)
      (Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl)))
  · change decodedState dec n xs rs zs zs = pcgState A P (decv dec n bs) (decv dec n xs) 0
    simp only [decodedState, pcgState]
    rw [hrd, hez, hrd]

/-- Initialization composes as a block that establishes the stored initial PCG state. -/
theorem initialize_writes {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I)
    {τ : Tape K} {μ : Mem K} {b x r z p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbz : b.1 ≠ z.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [b, x, r, z, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    Writes .total I τ initializeState (Env.frame [n] [b, x, x, r, z, p])
      (Fp.blocks [x, r, z, p] [n, n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ StoresState dec n x r z p
        (pcgState A P (decv dec n bs) (decv dec n xs) 0) μ') μ := by
  have hread : μ.readBlocks [b, x] [n, n] = some [bs, xs] :=
    Mem.readBlocks_of_cons hbs (Mem.readBlocks_of_cons hxs rfl)
  have hl' : μ.Live ([b, x] ++ [x, r, z, p]) := by
    change μ.Live [b, x, x, r, z, p]
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.1, hl.2.2⟩
  have hpre : (((initializeRel dec A P).spec (InitializeOperands n)).on .total [n]
      [b, x] [x, r, z, p] τ μ).pre μ :=
    ⟨rfl, ⟨rfl, b, x, r, z, p, rfl, rfl, hbx, hbr, hbz, hbp, hxr, hxz, hxp, hrz, hrp, hzp⟩,
      fun _ => ⟨hl', ⟨[bs, xs], hread, trivial⟩, hz⟩⟩
  refine ((initialize_spec hS hM hB hA hP).writes hpre hl').mono le_rfl ?_
  rintro μ' _ ⟨X, hX, _, ys, hlen, hrel, rfl⟩
  obtain rfl : X = [bs, xs] := Option.some.inj (hX.symm.trans hread)
  obtain ⟨xs', rs, zs, ps, rfl⟩ := List.length_eq_four.mp
    (show ys.length = 4 by simpa using congrArg List.length hlen)
  have hap : Fp.Apart [x, r, z, p] [n, n, n, n] := by disjoint
  have hout := Mem.readBlocks_updBlocks (m := μ) (ys := [xs', rs, zs, ps])
    (by rw [hlen]; exact hap) (by rw [hlen]; exact hz)
  rw [hlen] at hout
  exact ⟨by simp [initializeRel], xs', rs, zs, ps, by simpa [initializeRel] using hout,
    by simpa only [initializeRel_rel] using hrel⟩

end NLAlib.Krylov.CG.HSPCG
