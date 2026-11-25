/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.MixedSteps
public import NLAlib.Matrix.Factorizations.Cholesky.RightLooking
public import NLAlib.Matrix.Perturbation.CholeskyForwardError

/-!
# Full Cholesky success with finite range and additive underflow

The original matrix's spectral scale and positive lower margin, together with scalar range
inequalities, guarantee every operation of the actual right-looking routine succeeds under
a rejecting interpretation. Its actual factor has triangular zeros, positive diagonal and
an absolute spectral residual bound retaining additive underflow.

## Main results

* `NLAlib.Cholesky.rightLooking_meets_mixed`: full routine success from original input bounds.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Cholesky

open Ops Computation

variable {K Op Tst : Type} [Has ScalarOp Op] [Inhabited K]

/-- Copy-before-initialization also runs under rejecting arithmetic when zero is accepted.
The source and factor can overlap; only residual scratch must be apart. -/
theorem initializeLower_writes_guarded {M : Machine K} {I : Interp Op Tst K}
    {dec : K → ℝ} {safe : ℝ → Prop} (hI : IsGuardedScalar M dec safe I) (hacc : safe 0)
    {N : ℕ} {τ : Tape K} {m : Mem K} {A R L : ℕ × ℕ} {as : List K}
    (hlive : m.Live [A, R, L]) (hRA : R.1 ≠ A.1) (hRL : R.1 ≠ L.1)
    (has : m.store.readBlock A.1 A.2 (N * N) = some as)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1) :
    Writes .total I τ (initializeLower (Op := Op) (Tst := Tst)).body
      (Env.frame [N] [A, R, L])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock R.1 R.2 (N * N) = some as ∧
        m'.store.readBlock L.1 L.2 (N * N) =
          some (List.replicate (N * N) (M.lit 0))) m := by
  have hlitfn : M.guardedFn dec safe (.lit 0) = BlockFn.const (M.lit 0) := by
    have hq : safe ((0 : ℚ) : ℝ) := by simpa using hacc
    simp only [Machine.guardedFn, Machine.fn, if_pos hq]
  have hconst : I.IsFn .total (Has.inj (ScalarOp.lit 0)) (.const (M.lit 0)) AnyOperands :=
    by simpa only [hlitfn] using hI (.lit 0)
  obtain ⟨hlA, hlR, hlL, -⟩ :=
    (show A.1 < m.store.length ∧ R.1 < m.store.length ∧ L.1 < m.store.length ∧ True from
      by simpa only [Mem.live_cons, Mem.live_nil] using hlive)
  call (copyLoopRoutine_meets_guarded hI) [N * N] (A, R)
    as m₁ hfr₁ hpos₁ (rs) hcopy
  have hcopy_eq : rs = as := (List.cons.inj hcopy).1
  rw [hcopy_eq] at hrs
  call (fillRoutine_meets hconst) [N * N] (L)
    as m₂ hfr₂ hpos₂ (ls) hfill
  have hR₂ : m₂.store.readBlock R.1 R.2 (N * N) = some as := by keep
  have hfill_eq : ls = List.replicate (N * N) (M.lit 0) := hfill
  exact ⟨by omega, hR₂, by simpa only [hfill_eq] using hls⟩

/-- The actual copied-residual fragment completes from the original input band. The result
refers to actual output words, rather than an assumed factorization or successful run. -/
theorem rightWithScratch_writes_mixed {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {safe : ℝ → Prop} {N : ℕ} {u η B μ Ω e : ℝ}
    (hI : IsGuardedScalar M dec safe I) (hM : MixedModel u η dec M safe)
    (hzero : dec (M.lit 0) = 0) (hc : CholeskyRangeConditions N u η B μ Ω)
    (hrange : ∀ x, |x| ≤ Ω → safe x) (he : 0 ≤ e)
    (hbudget : choleskyMixedColumnErrorBound u η B μ
      (choleskyMixedSchurErrorBound u η B μ N) ≤ e)
    {τ : Tape K} {m : Mem K} {A L R : ℕ × ℕ} {as : List K}
    (hl : m.Live [A, L, R]) (hRA : R.1 ≠ A.1) (hRL : R.1 ≠ L.1)
    (has : m.store.readBlock A.1 A.2 (N * N) = some as)
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ decodeMatrix dec N N as)
    (hscale : specNorm (decodeMatrix dec N N as) ≤ B)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1) :
    Writes .total I τ (rightWithScratch (Op := Op) (Tst := Tst))
      (Env.frame [N] [A, L, R])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧ ∃ ls : List K,
        m'.store.readBlock L.1 L.2 (N * N) = some ls ∧
        (decodeMatrix dec N N ls).IsLowerTriangular ∧
        (∀ i : Fin N, 0 < decodeMatrix dec N N ls i i) ∧
        (∀ i j : Fin N, |decodeMatrix dec N N ls i j -
          choleskyLower (decodeMatrix dec N N as) i j| ≤ e) ∧
        (∀ i j : Fin N, i < j → vec ls (j.val * N + i.val) = M.lit 0)) m := by
  have hlARL : m.Live [A, R, L] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl A (by simp), hl R (by simp), hl L (by simp), trivial⟩
  have hacc : safe 0 := hrange 0 (by simpa only [abs_zero] using
    (le_trans zero_le_one hc.literal_le))
  unfold rightWithScratch
  refine ((initializeLower_writes_guarded hI hacc hlARL hRA hRL has hRroom hLroom).in_frame
    rfl rfl hlARL).seq_le le_rfl ?_
  intro m₁ hfr₁ ⟨hpos₁, hR₁, hL₁⟩
  have hpref := IsMixedPrefix.initial (dec := dec) (u := u) (η := η) (B := B) (μ := μ)
    (e := e) hR₁ hL₁
  have hlRL : m.Live [R, L] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl R (by simp), hl L (by simp), trivial⟩
  have hlRL₁ := hlRL.congr hfr₁.length_eq
  refine ((rightLoop_writes_mixed hI hM hzero hc hrange hlo hscale he hbudget hlRL₁ hRL
    (by simpa only [hfr₁.len_eq] using hRroom)
    (by simpa only [hfr₁.len_eq] using hLroom) hpref).in_frame
      rfl rfl hlRL₁).mono le_rfl ?_
  intro m₂ hfr₂ ⟨hpos₂, hfinal⟩
  obtain ⟨ls, hls, hlower, hdiag, hentry, hupper⟩ := hfinal.read_factor hzero
  exact ⟨by omega, ls, hls, hlower, hdiag, hentry, hupper⟩

/-- The scoped factorization succeeds under the input band and numerical range conditions.
Copying precedes output writes, so this body also permits overlapping source and output.
At order zero there is no live-handle, separation or output-capacity requirement. -/
theorem rightLooking_writes_mixed {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {safe : ℝ → Prop} {n : ℕ} {u η B μ Ω e : ℝ}
    (hI : IsGuardedScalar M dec safe I) (hM : MixedModel u η dec M safe)
    (hzero : dec (M.lit 0) = 0) (hc : CholeskyRangeConditions n u η B μ Ω)
    (hrange : ∀ x, |x| ≤ Ω → safe x) (he : 0 ≤ e)
    (hbudget : choleskyMixedColumnErrorBound u η B μ
      (choleskyMixedSchurErrorBound u η B μ n) ≤ e)
    {τ : Tape K} {m : Mem K} {A L : ℕ × ℕ} {as : List K}
    (hlive : 0 < n → m.Live [A, L])
    (has : m.store.readBlock A.1 A.2 (n * n) = some as)
    (hlo : μ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ decodeMatrix dec n n as)
    (hscale : specNorm (decodeMatrix dec n n as) ≤ B)
    (hroom : 0 < n → L.2 + n * n ≤ m.store.len L.1) :
    Writes .total I τ (rightLooking (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [A, L]) (Store.inBlock L.1 L.2 (n * n))
      (fun m' => m'.pos = m.pos ∧ ∃ ls : List K,
        m'.store.readBlock L.1 L.2 (n * n) = some ls ∧
        (decodeMatrix dec n n ls).IsLowerTriangular ∧
        (∀ i : Fin n, 0 < decodeMatrix dec n n ls i i) ∧
        (∀ i j : Fin n, |decodeMatrix dec n n ls i j -
          choleskyLower (decodeMatrix dec n n as) i j| ≤ e) ∧
        (∀ i j : Fin n, i < j → vec ls (j.val * n + i.val) = M.lit 0)) m := by
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    have hlA : A.1 < m.store.length := hlive hn A (by simp)
    have hlL : L.1 < m.store.length := hlive hn L (by simp)
    apply writes_allocs_preserving_post (lens := [.var 0 * .var 0]) (ns := [n * n]) rfl
    · intro s s' p hBelow hp
      obtain ⟨hpos, ls, hls, hlower, hdiag, hentry, hupper⟩ := hp
      exact ⟨hpos, ls, (hBelow.readBlock hlL L.2 (n * n)).trans hls,
        hlower, hdiag, hentry, hupper⟩
    · intro store hlength hlens hBelow
      have hRlen : store.len m.store.length = n * n := by simpa using hlens 0 (by simp)
      have hRlive : m.store.length < store.length := by
        simp only [List.length_singleton] at hlength
        omega
      have hLive : (Mem.mk store m.pos).Live [A, L, (m.store.length, 0)] := by
        simp only [Mem.live_cons, Mem.live_nil]
        exact ⟨by omega, by omega, hRlive, trivial⟩
      refine ((rightWithScratch_writes_mixed hI hM hzero hc hrange he hbudget
        hLive (by omega) (by omega) (by kept) hlo hscale (by simpa using hRlen.ge)
        (by simpa only [(hBelow L.1 hlL).1] using hroom hn)).in_frame
          rfl rfl hLive).mono (by fp_sub) (fun _ _ h => h)
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    exact ⟨rfl, [], rfl, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

/-- The original source spectral band and explicit scalar range conditions, followed by an
absolute spectral residual bound for the actual output factor. -/
def rightLookingMixedSpec (M : Machine K) (dec : K → ℝ) (u η B μ Ω : ℝ) : Routine.Spec K :=
  spec% [n] (as) → (ls) requires
    (CholeskyRangeConditions n u η B μ Ω ∧
      μ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ decodeMatrix dec n n as ∧
      specNorm (decodeMatrix dec n n as) ≤ B) ensures
    (let e := choleskyMixedColumnErrorBound u η B μ
      (choleskyMixedSchurErrorBound u η B μ n)
    IsCholeskyErr ((n * e) * (2 * Real.sqrt B + n * e))
      (decodeMatrix dec n n as) (decodeMatrix dec n n ls)) ∧
      (∀ i j : Fin n, i < j → vec ls (j.val * n + i.val) = M.lit 0)

/-- The actual scalar Cholesky routine succeeds from original input spectral and range
conditions under rejecting primitive contracts. Its residual bound retains additive underflow;
there is no successful-run, computed-pivot or trace-safety premise. -/
theorem rightLooking_meets_mixed {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {safe : ℝ → Prop} {u η B μ Ω : ℝ}
    (hI : IsGuardedScalar M dec safe I) (hM : MixedModel u η dec M safe)
    (hzero : dec (M.lit 0) = 0) (hrange : ∀ x, |x| ≤ Ω → safe x) :
    (rightLooking (Op := Op) (Tst := Tst)).Meets I (rightLookingMixedSpec M dec u η B μ Ω) := by
  routine_intro [n] (A, L) reads (as)
  obtain ⟨hc, hlo, hscale⟩ := hpre
  let e := choleskyMixedColumnErrorBound u η B μ (choleskyMixedSchurErrorBound u η B μ n)
  have hB : 0 ≤ B := hc.margin_pos.le.trans hc.margin_le_scale
  have he : 0 ≤ e := choleskyMixedColumnErrorBound_nonneg hc.roundoff_nonneg
    hc.underflow_nonneg hB hc.margin_pos
    (choleskyMixedSchurErrorBound_nonneg hc.roundoff_nonneg hc.underflow_nonneg
      hB hc.margin_pos n) hc.root_margin_pos
  refine (rightLooking_writes_mixed hI hM hzero hc hrange he le_rfl
    (fun _ => hlive) has hlo hscale (fun _ => hroom)).mono (by fp_sub) ?_
  rintro m' hfr ⟨hpos, ls, hls, hlower, hdiag, hentry, hupper⟩
  refine ⟨by omega, [ls], Mem.readBlocks_of_cons hls rfl, ?_, hupper⟩
  have hA : (decodeMatrix dec n n as).PosDef := by
    have hp := (Matrix.PosDef.one.smul hc.margin_pos).add_posSemidef (Matrix.le_iff.mp hlo)
    simpa only [add_sub_cancel] using hp
  simpa only [Fintype.card_fin] using
    hA.isCholesky_choleskyLower.isCholeskyErr_of_forall_abs_sub_le
      hscale he hlower hdiag (fun i j => (abs_sub_comm _ _).trans_le (hentry i j))

end NLAlib.Cholesky
