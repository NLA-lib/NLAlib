/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.CgsMath
public import NLAlib.Ops.Blas.Dot
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.Count

/-!
# A reusable classical reorthogonalization pass

All coefficients are computed from the original input vector before any projection update.
The scalar and vector operations stay abstract. The total certificate records the actual dot
and axpy errors, so it supports exact and rounded interpretations of the same program.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.cgsPassRoutine_meets`: a total pass with local error witnesses.
* `NLAlib.Krylov.Lanczos.Reorth.PassOut.abs_sub_le`: the accumulated projection error.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops Ops.Examples

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]

/-- One classical Gram–Schmidt pass, returning its coefficients and updated vector. -/
def cgsPass : Stmt Op Tst := ops% [n, k] (Q, W) → (W, H) {
  let t ← alloc 1;
  for j < k {
    call (Has.inj Blas1Op.dot) [n] (Q[j * n], W) → (H[j])
  };
  for j < k {
    call (Has.inj ScalarOp.neg) [] (H[j]) → (t);
    call (Has.inj Blas1Op.axpy) [n] (t, Q[j * n], W) → (W)
  }
}

/-- One dot, one negation and one vector update per basis column. -/
noncomputable def cgsPassCount (n k : ℕ) : Count Op Tst :=
  k • (Count.one (Has.inj Blas1Op.dot) [n] + Count.one (Has.inj ScalarOp.neg) [] +
    Count.one (Has.inj Blas1Op.axpy) [n])

/-- One scalar scratch cell and the largest called operation's workspace. -/
def cgsPassPeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  1 + max (W (Has.inj Blas1Op.dot) [n])
    (max (W (Has.inj ScalarOp.neg) []) (W (Has.inj Blas1Op.axpy) [n]))

/-- Static accounting counts the complete coefficient and update phases. -/
theorem stmtCost_cgsPass (n k q w w' h : ℕ) :
    stmtCost (cgsPass (Op := Op) (Tst := Tst)) [n, k, q, w, w', h] = cgsPassCount n k := by
  simp [cgsPass, stmtCost, useCost, cgsPassCount]
  module

/-- The two phases reuse a single scalar scratch cell. -/
theorem stmtPeak_cgsPass_le (W : Op → List ℕ → ℕ) (n k q w w' h : ℕ) :
    stmtPeak W (cgsPass (Op := Op) (Tst := Tst)) [n, k, q, w, w', h] ≤ cgsPassPeak W n := by
  simp only [cgsPass, Stmt.alloc, stmtPeak, cgsPassPeak]
  refine Nat.add_le_add_left (max_le_max (Finset.sup_le fun j _ => ?_)
    (Finset.sup_le fun j _ => ?_)) _ <;> simp

variable [Inhabited K]

/-- Actual coefficient errors and sequential projection errors from a classical pass. -/
structure PassOut (dec : K → ℝ) (ed ea : ℝ) (n k : ℕ) (qs ws ws' hs : List K) : Prop where
  /-- Every coefficient uses the unchanged pass input. -/
  dot : ∀ j < k, IsDotErr dec ed n (fun i => vec qs (j * n + i)) (vec ws) (vec hs j)
  /-- The coefficient projections are subtracted in order. -/
  update : AxpyChain dec ea n (fun j i => vec qs (j * n + i)) (vec hs) (vec ws) k (vec ws')

/-- The residual update reproduces the input minus the computed projections, with an explicit
componentwise accumulated axpy error. -/
theorem PassOut.abs_sub_le {dec : K → ℝ} {ed ea : ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec ed ea n k qs ws ws' hs) (ha : 0 ≤ ea) (i : Fin n) :
    |dec (vec ws' i) - (dec (vec ws i) -
        ∑ j ∈ Finset.range k, dec (vec hs j) * dec (vec qs (j * n + i)))| ≤
      ((1 + ea) ^ k - 1) * (|dec (vec ws i)| +
        ∑ j ∈ Finset.range k, |dec (vec hs j) * dec (vec qs (j * n + i))|) :=
  h.update.abs_sub_le ha i i.isLt

/-- The classical pass as a routine: the basis `Q` is read, the vector `w` updated in place and
the coefficients `H` written. -/
def cgsPassRoutine : Routine Op Tst :=
  routine% [n, k] (Q : k * n, w : n) → (w, H : k) := cgsPass

/-- The full classical-pass error specification, at admitted dimensions. -/
def cgsPassSpec (dec : K → ℝ) (ed : ℕ → ℝ) (ea : ℝ) (ok : ℕ → Prop) : Routine.Spec K :=
  spec% [n, k] (qs, ws) → (ws', hs) requires ok n
    ensures PassOut dec (ed n) ea n k qs ws ws' hs

/-- Every admitted classical pass succeeds under dot/axpy contracts and exact scalar negation.
Exact negation is explicit and is satisfied by the genuinely rounded inflating machine. -/
theorem cgsPassRoutine_meets {M : Machine K} {dec : K → ℝ} {ed : ℕ → ℝ} {ea : ℝ}
    {ok : ℕ → Prop} {I : Interp Op Tst K} (hS : IsScalar M I)
    (hD : I.Satisfies .total (Has.inj Blas1Op.dot) ((dotRel dec ed).spec (OutApart ok)))
    (hA : I.Satisfies .total (Has.inj Blas1Op.axpy) ((axpyRel dec ea).spec (InPlace ok)))
    (hneg : ∀ a, dec (M.neg a) = -dec a) :
    (cgsPassRoutine (Op := Op) (Tst := Tst)).Meets I (cgsPassSpec dec ed ea ok) := by
  routine_intro [n, k] (Q, w, H) reads (qs, ws)
  have hok : ok n := hpre
  refine writes_alloc rfl fun s₁ hs₁ ht hBelow => ?_
  refine Writes.seq_le (writes_fillRel (b := H.1) (o := H.2) rfl (fun j a =>
    IsDotErr dec (ed n) n (fun i => vec qs (j * n + i)) (vec ws) a)
    (fun _ => m.pos) rfl fun j hj m₁ hfr _ hpos => ?_) (by fp_sub)
    fun m₁ hfr ⟨⟨v, hvH, hvR⟩, hpos⟩ => ?_
  · step hD as m₂ hfr₂ ⟨hpos₂, a, ha, hdot⟩
    exact ⟨⟨a, ha, hdot.congr (fun i hi => vec_drop_take hi) fun _ _ => rfl⟩,
      by simpa [hpos₂] using hpos⟩
  · have hH := Store.holdsVec_iff_readBlock.mp hvH
    refine Writes.mono (writes_loop (N := k) rfl (fun _ => Store.inBlock w.1 w.2 n ⊔
      Store.inBuf m.store.length) (fun _ _ => le_rfl)
      (fun j m' => m'.pos = m.pos ∧ ∃ ws', m'.store.readBlock w.1 w.2 n = some ws' ∧
        AxpyChain dec ea n (fun j i => vec qs (j * n + i))
          (vec ((List.range k).map v)) (vec ws) j (vec ws'))
      ⟨hpos, ws, by kept, .zero⟩ fun j hj m₂ hfr₂ ⟨hpos₂, ws', hws', hchain⟩ => ?_)
      (by fp_sub) ?_
    · have hvi := hvH j hj
      step (hS .neg) as m₃ hfr₃ ⟨hpos₃, a, ha, hnegrel⟩
      step hA as m₄ hfr₄ ⟨hpos₄, zs, hzs, hax⟩
      exact ⟨by simp [hpos₄, hpos₃, hpos₂], zs, hzs,
        hchain.step (by rw [← hnegrel]; simpa only [vec_map_range v hj] using hneg (v j))
          (hax.congr (fun i hi => vec_drop_take hi) (fun _ _ => rfl) fun _ _ => rfl)⟩
    · rintro m₂ hfr₂ ⟨hpos₂, ws', hws', hchain⟩ s₂ hs₂ hBelow₂
      exact ⟨by simp [hpos₂], [ws', (List.range k).map v],
        Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl),
        show PassOut dec (ed n) ea n k qs ws ws' ((List.range k).map v) from
          ⟨fun j hj => by simpa only [vec_map_range v hj] using hvR j hj, hchain⟩⟩

end NLAlib.Krylov.Lanczos.Reorth
