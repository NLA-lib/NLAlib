/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RelativeSteps
public import NLAlib.Matrix.Factorizations.Cholesky.RightLooking
public import NLAlib.Matrix.Perturbation.CholeskyForwardError

/-!
# Full Cholesky success with standard relative rounding

The original matrix's spectral scale and positive lower margin, together with the terminal
active-residual budget, guarantee every operation succeeds. The actual factor has triangular
zeros, positive diagonal and the preserved conservative absolute spectral residual bound.

## Main results

* `NLAlib.Cholesky.rightLooking_meets_relative`: full routine success from original input bounds.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Cholesky

open Ops Computation

variable {K Op Tst : Type} [Has ScalarOp Op] [Inhabited K]

/-- The actual copied-residual fragment completes from the original input band. The result
refers to actual output words, rather than an assumed factorization or successful run. -/
theorem rightWithScratch_writes_relative {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {N : ℕ} {u B μ e : ℝ}
    (hI : IsScalar M I) (hM : StdModel u dec M) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10)
    (hμ : 0 < μ) (hμB : μ ≤ B)
    (hη : choleskySchurErrorBound u B μ N < μ / 2) (he : 0 ≤ e)
    (hbudget : ((2 * (1 + B / μ) * choleskySchurErrorBound u B μ N + 16 * u * B) / Real.sqrt μ) ≤ e)
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
  have hzero : dec (M.lit 0) = 0 := by
    have hh := hM.lit 0
    norm_num at hh
    exact hh
  unfold rightWithScratch
  refine ((initializeLower_writes_of_scratch_apart hI hlARL hRA hRL has hRroom hLroom).in_frame
    rfl rfl hlARL).seq_le le_rfl ?_
  intro m₁ hfr₁ ⟨hpos₁, hR₁, hL₁⟩
  have hpref := IsRelativePrefix.initial (dec := dec) (u := u) (B := B) (μ := μ)
    (e := e) hR₁ hL₁
  have hlRL : m.Live [R, L] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl R (by simp), hl L (by simp), trivial⟩
  have hlRL₁ := hlRL.congr hfr₁.length_eq
  refine ((rightLoop_writes_relative hI hM hu hu1 hμ hμB hη hlo hscale he hbudget hlRL₁ hRL
    (by simpa only [hfr₁.len_eq] using hRroom)
    (by simpa only [hfr₁.len_eq] using hLroom) hpref).in_frame
      rfl rfl hlRL₁).mono le_rfl ?_
  intro m₂ hfr₂ ⟨hpos₂, hfinal⟩
  obtain ⟨ls, hls, hlower, hdiag, hentry, hupper⟩ := hfinal.read_factor hzero
  exact ⟨by omega, ls, hls, hlower, hdiag, hentry, hupper⟩

/-- The scoped factorization succeeds under the input band and numerical range conditions.
Copying precedes output writes, so this body also permits overlapping source and output.
At order zero there is no live-handle, separation or output-capacity requirement. -/
theorem rightLooking_writes_relative {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {n : ℕ} {u B μ e : ℝ}
    (hI : IsScalar M I) (hM : StdModel u dec M) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10)
    (hμ : 0 < μ) (hμB : μ ≤ B)
    (hη : choleskySchurErrorBound u B μ n < μ / 2) (he : 0 ≤ e)
    (hbudget : ((2 * (1 + B / μ) * choleskySchurErrorBound u B μ n + 16 * u * B) / Real.sqrt μ) ≤ e)
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
      refine ((rightWithScratch_writes_relative hI hM hu hu1 hμ hμB hη he hbudget
        hLive (by omega) (by omega) (by kept) hlo hscale (by simpa using hRlen.ge)
        (by simpa only [(hBelow L.1 hlL).1] using hroom hn)).in_frame
          rfl rfl hLive).mono (by fp_sub) (fun _ _ h => h)
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    exact ⟨rfl, [], rfl, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

/-- The original spectral source band and relative-error conditions, followed by the
earlier conservative absolute spectral residual bound for the actual factor. -/
def rightLookingRelativeSpec (M : Machine K) (dec : K → ℝ) (u B μ : ℝ) : Routine.Spec K :=
  spec% [n] (as) → (ls) requires
    (0 ≤ u ∧ u ≤ 1 / 10 ∧ 0 < μ ∧ μ ≤ B ∧
      choleskySchurErrorBound u B μ n < μ / 2 ∧
      μ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ decodeMatrix dec n n as ∧
      specNorm (decodeMatrix dec n n as) ≤ B) ensures
    (let e := (2 * (1 + B / μ) * choleskySchurErrorBound u B μ n + 16 * u * B) / Real.sqrt μ
    IsCholeskyErr ((n * e) * (2 * Real.sqrt B + n * e))
      (decodeMatrix dec n n as) (decodeMatrix dec n n ls)) ∧
      (∀ i j : Fin n, i < j → vec ls (j.val * n + i.val) = M.lit 0)

/-- The actual right-looking routine retains the earlier relative-only input conditions and
error budget. Every pivot margin follows from the original source band and propagated active
residual error; no computed-pivot or successful-execution assumption is introduced. -/
theorem rightLooking_meets_relative {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u B μ : ℝ} (hI : IsScalar M I) (hM : StdModel u dec M) :
    (rightLooking (Op := Op) (Tst := Tst)).Meets I (rightLookingRelativeSpec M dec u B μ) := by
  routine_intro [n] (A, L) reads (as)
  obtain ⟨hu, hu1, hμ, hμB, hη, hlo, hscale⟩ := hpre
  let e := (2 * (1 + B / μ) * choleskySchurErrorBound u B μ n + 16 * u * B) / Real.sqrt μ
  have hB : 0 ≤ B := hμ.le.trans hμB
  have he : 0 ≤ e := by
    have herror := choleskySchurErrorBound_nonneg hu hB hμ n
    dsimp only [e]
    positivity
  refine (rightLooking_writes_relative hI hM hu hu1 hμ hμB hη he le_rfl
    (fun _ => hlive) has hlo hscale (fun _ => hroom)).mono (by fp_sub) ?_
  rintro m' hfr ⟨hpos, ls, hls, hlower, hdiag, hentry, hupper⟩
  refine ⟨by omega, [ls], Mem.readBlocks_of_cons hls rfl, ?_, hupper⟩
  have hA : (decodeMatrix dec n n as).PosDef := by
    have hp := (Matrix.PosDef.one.smul hμ).add_posSemidef (Matrix.le_iff.mp hlo)
    simpa only [add_sub_cancel] using hp
  simpa only [Fintype.card_fin] using
    hA.isCholesky_choleskyLower.isCholeskyErr_of_forall_abs_sub_le
      hscale he hlower hdiag (fun i j => (abs_sub_comm _ _).trans_le (hentry i j))

end NLAlib.Cholesky
