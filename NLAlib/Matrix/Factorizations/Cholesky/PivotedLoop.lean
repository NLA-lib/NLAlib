/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.PivotedStep

/-!
# Completing diagonal-pivoted Cholesky prefixes

The actual scalar loop carries the finite log determined by its stored selected indices.
Initialization copies the source before writing any output, so the common operand body
permits source/output overlap. Only its residual scratch must be separate.

## Main results

* `NLAlib.Cholesky.pivotedLoop_writes`: actual full-loop success from semidefinite input.
* `NLAlib.Cholesky.pivotedWithScratch_writes`: complete factors and the actual absolute log.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Every actual scan and zero-safe pivot step completes the factor and absolute log prefix.
Singular semidefinite inputs and the empty matrix require no nonzero-pivot assumption. -/
theorem pivotedLoop_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hlit : IsIndexLit M I) (hcmp : IsCmp dec I) (hQ : IsToNat dec I)
    (hM : ExactModel dec M) {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosSemidef)
    {p : Fin N → Fin N} {τ : Tape K} {m : Mem K} {R L H : ℕ × ℕ}
    (hlive : m.Live [R, L, H]) (hRL : R.1 ≠ L.1) (hRH : R.1 ≠ H.1) (hLH : L.1 ≠ H.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hHroom : H.2 + N ≤ m.store.len H.1)
    (hstate : IsDiagonalPrefix dec (M.lit 0) A p 0 R L H m.store) :
    Writes .total I τ (pivotedLoop (Op := Op) (Tst := Tst)) (Env.frame [N] [R, L, H])
      ((Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N)) ⊔
        Store.inBlock H.1 H.2 N)
      (fun m' => ∃ p' : Fin N → Fin N, m'.pos = m.pos ∧
        IsDiagonalPrefix dec (M.lit 0) A p' N R L H m'.store) m := by
  unfold pivotedLoop
  refine (writes_loop rfl (fun _ =>
    (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N)) ⊔
      Store.inBlock H.1 H.2 N) (fun _ _ => le_rfl)
    (fun count m' => ∃ p' : Fin N → Fin N, m'.pos = m.pos ∧
      IsDiagonalPrefix dec (M.lit 0) A p' count R L H m'.store)
    ⟨p, rfl, hstate⟩ ?_).mono le_rfl (fun _ _ h => h)
  intro k hk m' hfr ⟨p', hpos, hstate'⟩
  have hl' := hlive.congr hfr.length_eq
  refine ((pivotedStep_writes hI hlit hcmp hQ hM hA ⟨k, hk⟩ hl' hRL hRH hLH
    (by rw [hfr.len_eq]; exact hRroom) (by rw [hfr.len_eq]; exact hLroom)
    (by rw [hfr.len_eq]; exact hHroom) hstate').in_frame rfl rfl hl').mono le_rfl ?_
  rintro m'' hfr' ⟨r, hpos', hstate''⟩
  exact ⟨Function.update p' ⟨k, hk⟩ r, hpos'.trans hpos, hstate''⟩

/-- The common copy-first body computes actual factor and pivot-log output blocks. The source
may overlap either output; the factor and log have different buffers. No successful run is
assumed, and its numerical guarantee includes the actual first-maximum diagonal history. -/
theorem pivotedWithScratch_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hlit : IsIndexLit M I) (hcmp : IsCmp dec I) (hQ : IsToNat dec I)
    (hM : ExactModel dec M) {N : ℕ} {τ : Tape K} {m : Mem K} {A L H R : ℕ × ℕ}
    {as : List K} (hlive : m.Live [A, L, H, R])
    (hRA : R.1 ≠ A.1) (hRL : R.1 ≠ L.1) (hRH : R.1 ≠ H.1) (hLH : L.1 ≠ H.1)
    (has : m.store.readBlock A.1 A.2 (N * N) = some as)
    (hA : (decodeMatrix dec N N as).PosSemidef)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hHroom : H.2 + N ≤ m.store.len H.1) :
    Writes .total I τ (pivotedWithScratch (Op := Op) (Tst := Tst))
      (Env.frame [N] [A, L, H, R])
      ((Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N)) ⊔
        Store.inBlock H.1 H.2 N)
      (fun m' => m'.pos = m.pos ∧ ∃ ls hs : List K,
        m'.store.readBlock L.1 L.2 (N * N) = some ls ∧
        m'.store.readBlock H.1 H.2 N = some hs ∧
        (pivotedRightLookingSpec M dec).post [N] (τ.shift m.pos) [as] [ls, hs]) m := by
  have hlARL : m.Live [A, R, L] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hlive A (by simp), hlive R (by simp), hlive L (by simp), trivial⟩
  have hlRLH : m.Live [R, L, H] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hlive R (by simp), hlive L (by simp), hlive H (by simp), trivial⟩
  unfold pivotedWithScratch
  refine ((initializeLower_writes_of_scratch_apart hI hlARL hRA hRL has hRroom hLroom).in_frame
    rfl rfl hlARL).seq_le (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hpos₁, hR₁, hL₁⟩
  have hstart := IsDiagonalPrefix.initial (H := H) hM (fun i => i) hR₁ hL₁
  have hlRLH₁ := hlRLH.congr hfr₁.length_eq
  refine ((pivotedLoop_writes hI hlit hcmp hQ hM hA hlRLH₁ hRL hRH hLH
    (by rw [hfr₁.len_eq]; exact hRroom) (by rw [hfr₁.len_eq]; exact hLroom)
    (by rw [hfr₁.len_eq]; exact hHroom) hstart).in_frame
      rfl rfl hlRLH₁).mono le_rfl ?_
  rintro m₂ hfr₂ ⟨p, hpos₂, hpre, hfuture, hlog, hquality⟩
  obtain ⟨ls, hls, hnum, hupper⟩ := hpre.read_factor
  obtain ⟨hs, hhs, hhistory⟩ := Store.indexPrefix_readBlock (fun j => hlog j j.isLt)
  refine ⟨hpos₂.trans hpos₁, ls, hs, hls, hhs, p, hhistory, hquality, hnum, ?_, ?_, ?_, hupper⟩
  · rw [hnum]
    exact isLowerTriangular_choleskyLower _
  · intro i
    rw [hnum]
    exact (hA.submatrix _).isHermitian.choleskyLower_apply_self_nonneg i
  · rw [hnum]
    exact (hA.submatrix _).eq_choleskyLower_mul_conjTranspose

end NLAlib.Cholesky
