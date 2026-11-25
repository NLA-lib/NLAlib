/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.MixedPrefix
public import NLAlib.Matrix.Factorizations.Cholesky.RightSteps
public import NLAlib.Matrix.Factorizations.Cholesky.RightColumnMixed
public import NLAlib.Matrix.Factorizations.LU.SchurGuarded

/-!
# Finite-range success of stored Cholesky steps

The original spectral input band and scalar range inequalities establish each next primitive
contract before execution. The actual column and saved-pivot update advance the residual and
factor error invariant, retaining additive underflow and the literal triangular zeros.

## Main results

* `NLAlib.Cholesky.rightStep_writes_mixed`: one actual rejecting-arithmetic step.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Cholesky

open Ops Computation

variable {K Op Tst : Type} [Has ScalarOp Op] [Inhabited K]

omit [Has ScalarOp Op] in
private theorem column_error_mixed {M : Machine K} {dec : K → ℝ} {safe : ℝ → Prop}
    {N : ℕ} {u η B μ Ω : ℝ} (hM : MixedModel u η dec M safe)
    (hc : CholeskyRangeConditions N u η B μ Ω) (hrange : ∀ x, |x| ≤ Ω → safe x)
    {A : Matrix (Fin N) (Fin N) ℝ}
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (k : Fin N) (rw : ℕ → ℕ → K) {xs ys : List K} {τ : Tape K}
    (hres : ∀ i j : Fin N, |dec (rw i j) - gaussState A k.val i j| ≤
      choleskyMixedSchurErrorBound u η B μ k.val)
    (hp : μ / 2 ≤ dec (rw k.val k.val)) (hpB : dec (rw k.val k.val) ≤ 2 * B)
    (hx : ∀ i < N - k.val - 1, vec xs i = rw (k.val + 1 + i) k.val)
    (hxsB : ∀ i < N - k.val - 1, |dec (vec xs i)| ≤ 2 * B)
    (hcol : (rightColumnSpec M).post [N - k.val - 1] τ [[rw k.val k.val], xs] [ys]) :
    0 < dec (vec ys 0) ∧ ∀ i : Fin N, k ≤ i →
      |dec (vec ys (i.val - k.val)) - choleskyLower A i k| ≤
        choleskyMixedColumnErrorBound u η B μ (choleskyMixedSchurErrorBound u η B μ N) := by
  obtain ⟨hypos, hylo, hyroot, hydiv⟩ :=
    rightColumnSpec_mixed (τ := τ) hM hc hrange hcol hp hpB hxsB
  let w : Fin N → ℝ := fun i => if k ≤ i then dec (vec ys (i.val - k.val)) else 0
  have hwroot : w k = dec (vec ys 0) := by simp only [w, le_refl, if_true, Nat.sub_self]
  have hwe := CholeskyRange.abs_column_sub_choleskyLower_le hc.margin_pos
    hc.margin_le_scale hlo hscale hc.roundoff_nonneg hc.underflow_nonneg hc.root_margin_pos
    k.isLt hc.residual_error_lt hres w
    (by intro i hi; exact if_neg (by exact not_le.mpr hi))
    (by simpa only [hwroot] using hylo) (by simpa only [hwroot] using hyroot)
    (by
      intro i hi
      have hidx : i.val - k.val - 1 < N - k.val - 1 := by omega
      have hidxeq : k.val + 1 + (i.val - k.val - 1) = i.val := by omega
      have hout : i.val - k.val - 1 + 1 = i.val - k.val := by omega
      have hv := hydiv (i.val - k.val - 1) hidx
      change AbsRelErr u η (dec (vec xs (i.val - k.val - 1)) / dec (vec ys 0))
        (dec (vec ys (i.val - k.val - 1 + 1))) at hv
      rw [hx _ hidx, hidxeq, hout] at hv
      change AbsRelErr u η (dec (rw i.val k.val) / w k) (w i)
      simpa only [hwroot, w, if_pos (show k ≤ i from le_of_lt hi)] using hv)
  refine ⟨hypos, fun i hi => ?_⟩
  simpa only [w, if_pos hi] using hwe i

/-- The input spectral band and propagated residual error guarantee success of the actual
column and Schur step. No run, trace safety or computed-pivot premise is assumed. -/
theorem rightStep_writes_mixed {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {safe : ℝ → Prop} {N : ℕ} {u η B μ Ω e : ℝ}
    (hI : IsGuardedScalar M dec safe I) (hM : MixedModel u η dec M safe)
    (hzero : dec (M.lit 0) = 0) (hc : CholeskyRangeConditions N u η B μ Ω)
    (hrange : ∀ x, |x| ≤ Ω → safe x)
    {A : Matrix (Fin N) (Fin N) ℝ}
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (he : 0 ≤ e) (hbudget : choleskyMixedColumnErrorBound u η B μ
      (choleskyMixedSchurErrorBound u η B μ N) ≤ e) (k : Fin N)
    {τ : Tape K} {m : Mem K} {R L : ℕ × ℕ}
    (hl : m.Live [R, L]) (hRL : R.1 ≠ L.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hpref : IsMixedPrefix dec (M.lit 0) u η B μ e A k.val R L m.store) :
    Writes .total I τ (rightStep (Op := Op) (Tst := Tst))
      (Env.frame [N, k.val] [R, L])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧
        IsMixedPrefix dec (M.lit 0) u η B μ e A (k.val + 1) R L m'.store) m := by
  have hlR : R.1 < m.store.length := hl R (by simp)
  have hlL : L.1 < m.store.length := hl L (by simp)
  obtain ⟨rw, lw, hR, hL, hres, hfac, hdiag, hupper⟩ := hpref
  let V : Matrix (Fin N) (Fin N) ℝ := fun i j => dec (rw i j)
  obtain ⟨hpE, hE, hp, hVs, herror⟩ :=
    CholeskyRange.residual_bounds hc hlo hscale k.isLt hres
  have hdiagR := Store.readBlock_one_of_get (hR k.val k.isLt k.val k.isLt)
  have htail : m.store.readBlock R.1 (R.2 + k.val * N + k.val + 1) (N - k.val - 1) =
      some ((List.range (N - k.val - 1)).map fun i => rw (k.val + 1 + i) k.val) := by
    simpa only [Nat.sub_sub, Nat.add_assoc] using
      hR.readBlock_column_suffix k.val k.isLt (k.val + 1) (Nat.succ_le_of_lt k.isLt)
  let xs := (List.range (N - k.val - 1)).map fun i => rw (k.val + 1 + i) k.val
  have hx (i : ℕ) (hi : i < N - k.val - 1) :
      vec xs i = rw (k.val + 1 + i) k.val := vec_map_range _ hi
  have hxsB (i : ℕ) (hi : i < N - k.val - 1) : |dec (vec xs i)| ≤ 2 * B := by
    rw [hx i hi]
    exact hVs ⟨k.val + 1 + i, by omega⟩ k
  have hpB : dec (rw k.val k.val) ≤ 2 * B := (le_abs_self _).trans (hVs k k)
  have hs : N - k.val - 1 + 1 = N - k.val := by omega
  have hend : k.val * N + k.val + (N - k.val - 1 + 1) ≤ N * N := by
    have hmul := Nat.mul_le_mul_right N (Nat.succ_le_of_lt k.isLt)
    rw [Nat.succ_mul] at hmul
    omega
  unfold rightStep
  call (rightColumn_meets_guarded hI) [N - k.val - 1]
    ((R.1, R.2 + k.val * N + k.val), (R.1, R.2 + k.val * N + k.val + 1),
      (L.1, L.2 + k.val * N + k.val))
    (pre := rightColumnGuardedSpec_pre hM hc hrange hp hpB hxsB)
    as m₁ hfr₁ hpos₁ (ys) hcol
  have hfrL : m.store.EqOff
      (Store.inBlock L.1 (L.2 + k.val * N + k.val) (N - k.val)) m₁.store := by
    simpa [hs, Fp.blocks_cons, Fp.blocks_nil] using hfr₁
  have hys : m₁.store.readBlock L.1 (L.2 + k.val * N + k.val) (N - k.val) = some ys := by
    simpa only [hs] using hys
  let lw' : ℕ → ℕ → K := fun i j =>
    if j = k.val ∧ k.val ≤ i then vec ys (i - k.val) else lw i j
  have hL₁ : m₁.store.HoldsMat ⟨L.1, L.2, N, N, N⟩ lw' :=
    hL.update_column_suffix_of_frame (by exact le_rfl) k.val k.val k.isLt.le hfrL hys
  have hR₁ : m₁.store.HoldsMat ⟨R.1, R.2, N, N, N⟩ rw := by keep
  obtain ⟨hypos, hwe⟩ := column_error_mixed (τ := τ.shift m.pos)
    hM hc hrange hlo hscale k rw hres hp hpB hx hxsB hcol
  obtain ⟨rs, hrs, -, hdata⟩ := hR₁.readBlock rfl
  have hwords (i j : ℕ) (hi : i < N) (hj : j < N) :
      vec rs (j * N + i) = rw i j := hdata i hi j hj
  obtain ⟨hsafe, hlocal⟩ := LU.schurValues_mixed hM hc hrange
    (fun i j => vec rs (j * N + i)) k.isLt
    (by simpa only [hwords _ _ k.isLt k.isLt] using hp)
    (by intro i hi j hj; simpa only [hwords i j hi hj] using hVs ⟨i, hi⟩ ⟨j, hj⟩)
  call (LU.schurStep_meets_guarded hI) [N, k.val] (R) (pre := ⟨k.isLt, hsafe⟩)
    as m₂ hfr₂ hpos₂ (bs) hschur
  have hL₂ : m₂.store.HoldsMat ⟨L.1, L.2, N, N, N⟩ lw' := by keep
  have hb : ∀ i j : Fin N, dec (vec bs (j.val * N + i.val)) =
      dec (LU.schurValues M (fun i j => vec rs (j * N + i)) k.val i.val j.val) := by
    have hbsEq : bs = (EntryCodec.scalar K).packMatrix N N
      (LU.schurValues M (fun i j => vec rs (j * N + i)) k.val) := hschur
    intro i j
    rw [hbsEq]
    have hd := congrFun (congrFun ((EntryCodec.scalar K).matrix_packMatrix N N
      (LU.schurValues M (fun i j => vec rs (j * N + i)) k.val)) i) j
    simpa only [EntryCodec.matrix, EntryCodec.scalar_entry] using congrArg dec hd
  refine ⟨by omega, IsMixedPrefix.succ k (fun i j => vec bs (j * N + i)) lw ys
    (Store.holdsMat_of_readBlock rfl hbs) hL₂ ?_ hfac hdiag hupper hzero he ?_ hypos⟩
  · intro i j
    rw [gaussState_succ A k.isLt]
    refine abs_sub_eliminationStep_le_choleskyMixedSchurErrorBound
      (M' := fun i j : Fin N => dec (vec bs (j.val * N + i.val)))
      hc.margin_pos hc.margin_le_scale herror hpE hE hres ?_ i j
    intro a b
    rw [hb a b]
    have hv := hlocal a.val a.isLt b.val b.isLt
    rw [hwords _ _ a.isLt b.isLt, hwords _ _ a.isLt k.isLt,
      hwords _ _ k.isLt b.isLt, hwords _ _ k.isLt k.isLt] at hv
    change |dec (LU.schurValues M (fun i j => vec rs (j * N + i)) k.val a.val b.val) -
      (dec (rw a.val b.val) - (dec (rw k.val k.val))⁻¹ *
        (dec (rw a.val k.val) * dec (rw k.val b.val)))| ≤ _
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hv
  · intro i hi
    exact (hwe i hi).trans hbudget

/-- Every actual column and Schur update executes from the original numerical input band.
The complete stored prefix retains the terminal factor error and positive diagonal. -/
theorem rightLoop_writes_mixed {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {safe : ℝ → Prop} {N : ℕ} {u η B μ Ω e : ℝ}
    (hI : IsGuardedScalar M dec safe I) (hM : MixedModel u η dec M safe)
    (hzero : dec (M.lit 0) = 0) (hc : CholeskyRangeConditions N u η B μ Ω)
    (hrange : ∀ x, |x| ≤ Ω → safe x)
    {A : Matrix (Fin N) (Fin N) ℝ}
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (he : 0 ≤ e) (hbudget : choleskyMixedColumnErrorBound u η B μ
      (choleskyMixedSchurErrorBound u η B μ N) ≤ e)
    {τ : Tape K} {m : Mem K} {R L : ℕ × ℕ}
    (hl : m.Live [R, L]) (hRL : R.1 ≠ L.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hpref : IsMixedPrefix dec (M.lit 0) u η B μ e A 0 R L m.store) :
    Writes .total I τ (rightLoop (Op := Op) (Tst := Tst)) (Env.frame [N] [R, L])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧ IsMixedPrefix dec (M.lit 0) u η B μ e A N R L m'.store) m := by
  unfold rightLoop
  refine (writes_loop rfl
    (fun _ => Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
    (fun _ _ => le_rfl)
    (fun k m' => m'.pos = m.pos ∧ IsMixedPrefix dec (M.lit 0) u η B μ e A k R L m'.store)
    ⟨rfl, hpref⟩ ?_).mono le_rfl (fun _ _ h => h)
  intro k hk m' hfr ⟨hpos, hpref'⟩
  have hl' := hl.congr hfr.length_eq
  refine ((rightStep_writes_mixed hI hM hzero hc hrange hlo hscale he hbudget ⟨k, hk⟩
    hl' hRL (by simpa only [hfr.len_eq] using hRroom)
    (by simpa only [hfr.len_eq] using hLroom) hpref').in_frame rfl rfl hl').mono le_rfl ?_
  intro m'' hfr' ⟨hpos', hpref''⟩
  exact ⟨hpos'.trans hpos, hpref''⟩

end NLAlib.Cholesky
