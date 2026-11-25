/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RightSteps
public import NLAlib.Matrix.Factorizations.Cholesky.RightPrefix
public import NLAlib.Matrix.Factorizations.LU.Schur
public import NLAlib.Matrix.Factorizations.Cholesky.Initialize
public import NLAlib.Ops.Logic.Allocation

/-!
# Right-looking Cholesky factorization

The actual scalar routine copies its input into a scoped Gaussian residual, initializes every
output entry with a zero literal, and commits one normalized column suffix before each full
saved-pivot Schur update. Entries above the diagonal are never overwritten after initialization.

## Main definitions

* `NLAlib.Cholesky.rightLooking`: the fixed scalar routine.
* `NLAlib.Cholesky.rightLookingSpec`: the canonical factor and actual literal upper zeros.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- The copy, initialization and complete column loop of `rightLooking`, on caller-owned
scratch. Copying the source first permits an in-place caller of this same fragment. -/
def rightWithScratch : Stmt Op Tst := ops% [n] (A, L, R) → () {
  run initializeLower [n] (A, R, L);
  run rightLoop [n] (R, L)
}

/-- Scalar right-looking Cholesky on a copied residual. The source is read only, and scoped
scratch is released on return. An empty matrix performs no pivot or division. -/
def rightLooking : Routine Op Tst := routine% [n] (A : n * n) → (L : n * n) {
  ifPos n {
    let R ← alloc (n * n);
    run rightWithScratch [n] (A, L, R)
  }
}

/-- At order zero the raw scalar body reads no operands and leaves the complete memory
unchanged, for arbitrary handles, offsets, aliases and even an empty caller store. -/
theorem eval_rightLooking_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (rightLooking (Op := Op) (Tst := Tst)).body (Env.frame [0] args) m = some m := by
  rfl

variable [Inhabited K]

/-- Positive definite input gives its canonical Cholesky factor, with actual zero-literal
upper words. Positive diagonal and the Gram identity are stated for the actual decoded output.
The precondition is mathematical and includes order zero. -/
def rightLookingSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (as) → (ls) requires (decodeMatrix dec n n as).PosDef ensures
    decodeMatrix dec n n ls = choleskyLower (decodeMatrix dec n n as) ∧
      IsCholesky (decodeMatrix dec n n as) (decodeMatrix dec n n ls) ∧
      (∀ i j : Fin n, i < j → vec ls (j.val * n + i.val) = M.lit 0)

/-- The numerical postcondition at order zero holds for the actual empty output words.
No matrix entries or strict diagonal values exist at this order. -/
theorem rightLookingSpec_empty (M : Machine K) (dec : K → ℝ) (as : List K) (τ : Tape K) :
    (rightLookingSpec M dec).post [0] τ [as] [[]] := by
  refine ⟨?_, ⟨?_, fun i => Fin.elim0 i, ?_⟩, fun i => Fin.elim0 i⟩
  · ext i j
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · ext i j
    exact Fin.elim0 i

/-- The copy and complete scalar loop compute the canonical factor on caller-owned scratch.
Only scratch must be apart from the source and output; the source and output may overlap.
The statement is the internal fragment used by `rightLooking`, with no run premise. -/
theorem rightWithScratch_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) {N : ℕ}
    {τ : Tape K} {m : Mem K} {A L R : ℕ × ℕ} {as : List K}
    (hl : m.Live [A, L, R]) (hRA : R.1 ≠ A.1) (hRL : R.1 ≠ L.1)
    (has : m.store.readBlock A.1 A.2 (N * N) = some as)
    (hA : (decodeMatrix dec N N as).PosDef)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1) :
    Writes .total I τ (rightWithScratch (Op := Op) (Tst := Tst))
      (Env.frame [N] [A, L, R])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧ ∃ ls : List K,
        m'.store.readBlock L.1 L.2 (N * N) = some ls ∧
        decodeMatrix dec N N ls = choleskyLower (decodeMatrix dec N N as) ∧
        (∀ i j : Fin N, i < j → vec ls (j.val * N + i.val) = M.lit 0)) m := by
  have hlARL : m.Live [A, R, L] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl A (by simp), hl R (by simp), hl L (by simp), trivial⟩
  unfold rightWithScratch
  refine ((initializeLower_writes_of_scratch_apart hI hlARL hRA hRL has hRroom hLroom).in_frame
    rfl rfl hlARL).seq_le le_rfl ?_
  intro m₁ hfr₁ ⟨hpos₁, hR₁, hL₁⟩
  have hpref := IsRightPrefix.initial hM hR₁ hL₁
  have hlRL : m.Live [R, L] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl R (by simp), hl L (by simp), trivial⟩
  have hlRL₁ := hlRL.congr hfr₁.length_eq
  refine ((rightLoop_writes hI hM hA hlRL₁ hRL
    (by simpa only [hfr₁.len_eq] using hRroom)
    (by simpa only [hfr₁.len_eq] using hLroom) hpref).in_frame
      rfl rfl hlRL₁).mono le_rfl ?_
  intro m₂ hfr₂ ⟨hpos₂, hfinal⟩
  obtain ⟨ls, hls, hnum, hupper⟩ := hfinal.read_factor
  exact ⟨by omega, ls, hls, hnum, hupper⟩

/-- The scoped scalar body at arbitrary source/output operands. The copy occurs before
output initialization, so this common body also admits coincident operands. Only the factor
block can change; scoped residual storage and the tape position are restored. -/
theorem rightLooking_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) {n : ℕ}
    {τ : Tape K} {m : Mem K} {A L : ℕ × ℕ} {as : List K}
    (hlive : m.Live [A, L])
    (has : m.store.readBlock A.1 A.2 (n * n) = some as)
    (hpre : (decodeMatrix dec n n as).PosDef)
    (hroom : L.2 + n * n ≤ m.store.len L.1) :
    Writes .total I τ (rightLooking (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [A, L]) (Store.inBlock L.1 L.2 (n * n))
      (fun m' => m'.pos = m.pos ∧ ∃ ls : List K,
        m'.store.readBlock L.1 L.2 (n * n) = some ls ∧
        decodeMatrix dec n n ls = choleskyLower (decodeMatrix dec n n as) ∧
        (∀ i j : Fin n, i < j → vec ls (j.val * n + i.val) = M.lit 0)) m := by
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    have hlA : A.1 < m.store.length := hlive A (by simp)
    have hlL : L.1 < m.store.length := hlive L (by simp)
    apply writes_allocs_preserving_post (lens := [.var 0 * .var 0]) (ns := [n * n]) rfl
    · intro s s' p hBelow hp
      obtain ⟨hpos, ls, hls, hnum, hupper⟩ := hp
      exact ⟨hpos, ls, (hBelow.readBlock hlL L.2 (n * n)).trans hls, hnum, hupper⟩
    · intro store hlength hlens hBelow
      have hRlen : store.len m.store.length = n * n := by simpa using hlens 0 (by simp)
      have hRlive : m.store.length < store.length := by
        simp only [List.length_singleton] at hlength
        omega
      have hLive : (Mem.mk store m.pos).Live [A, L, (m.store.length, 0)] := by
        simp only [Mem.live_cons, Mem.live_nil]
        exact ⟨by omega, by omega, hRlive, trivial⟩
      refine ((rightWithScratch_writes hI hM hLive (by omega) (by omega)
        (by kept) hpre (by simpa using hRlen.ge)
        (by simpa only [(hBelow L.1 hlL).1] using hroom)).in_frame
          rfl rfl hLive).mono (by fp_sub) (fun _ _ h => h)
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    obtain ⟨hnum, -, hupper⟩ := rightLookingSpec_empty M dec as (τ.shift m.pos)
    exact ⟨rfl, [], rfl, hnum, hupper⟩

/-- The full scalar right-looking routine meets its canonical positive definite
specification. Scratch is scoped and only the output block can change. The input includes
all positive definite orders, including zero; no execution assumption is used. -/
theorem rightLooking_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) :
    (rightLooking (Op := Op) (Tst := Tst)).Meets I (rightLookingSpec M dec) := by
  routine_intro [n] (A, L) reads (as)
  refine (rightLooking_writes hI hM hlive has hpre hroom).mono (by fp_sub) ?_
  rintro m' hfr ⟨hpos, ls, hls, hnum, hupper⟩
  refine ⟨by omega, [ls], Mem.readBlocks_of_cons hls rfl, hnum, ?_, hupper⟩
  rw [hnum]
  exact hpre.isCholesky_choleskyLower

end NLAlib.Cholesky
