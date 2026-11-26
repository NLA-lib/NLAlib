/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RelativePrefix
public import NLAlib.Matrix.Factorizations.Cholesky.RightSteps
public import NLAlib.Matrix.Factorizations.Cholesky.RightColumnRelative
public import NLAlib.Matrix.Factorizations.LU.SchurRelative

/-!
# Relative-error success of stored Cholesky steps

The original spectral input band and scalar range inequalities establish each next primitive
contract before execution. The actual column and saved-pivot update advance the residual and
factor error invariant, retaining additive underflow and the literal triangular zeros.

## Main results

* `NLAlib.Cholesky.rightStep_writes_relative`: one actual rejecting-arithmetic step.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Cholesky

open Ops Computation

variable {K Op Tst : Type} [Has ScalarOp Op] [Inhabited K]

omit [Has ScalarOp Op] in
private theorem column_error_relative {M : Machine K} {dec : K → ℝ}
    {N : ℕ} {u B μ : ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10)
    (hμ : 0 < μ) (hμB : μ ≤ B) {A : Matrix (Fin N) (Fin N) ℝ}
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (hη : choleskySchurErrorBound u B μ N < μ / 2)
    (k : Fin N) (rw : ℕ → ℕ → K) {xs ys : List K} {τ : Tape K}
    (hres : ∀ i j : Fin N, k.val ≤ i.val → k.val ≤ j.val →
      |dec (rw i j) - gaussState A k.val i j| ≤ choleskySchurErrorBound u B μ k.val)
    (hp : 0 < dec (rw k.val k.val))
    (hx : ∀ i < N - k.val - 1, vec xs i = rw (k.val + 1 + i) k.val)
    (hcol : (rightColumnSpec M).post [N - k.val - 1] τ [[rw k.val k.val], xs] [ys]) :
    0 < dec (vec ys 0) ∧ ∀ i : Fin N, k ≤ i →
      |dec (vec ys (i.val - k.val)) - choleskyLower A i k| ≤
        (2 * (1 + B / μ) * choleskySchurErrorBound u B μ N + 16 * u * B) / Real.sqrt μ := by
  obtain ⟨hypos, hyroot, hydiv⟩ :=
    rightColumnSpec_relative (τ := τ) hM hu (by linarith) hcol hp
  let w : Fin N → ℝ := fun i => if k ≤ i then dec (vec ys (i.val - k.val)) else 0
  have hwroot : w k = dec (vec ys 0) := by simp only [w, le_refl, if_true, Nat.sub_self]
  have hwe := CholeskyRounding.abs_column_sub_choleskyLower_le hμ hμB hlo hscale hu hu1
    k.isLt hη hres w
    (by intro i hi; exact if_neg (by exact not_le.mpr hi))
    (by simpa only [hwroot] using hyroot)
    (by
      intro i hi
      have hidx : i.val - k.val - 1 < N - k.val - 1 := by omega
      have hidxeq : k.val + 1 + (i.val - k.val - 1) = i.val := by omega
      have hout : i.val - k.val - 1 + 1 = i.val - k.val := by omega
      have hv := hydiv (i.val - k.val - 1) hidx
      change RelErr u (dec (vec xs (i.val - k.val - 1)) / dec (vec ys 0))
        (dec (vec ys (i.val - k.val - 1 + 1))) at hv
      rw [hx _ hidx, hidxeq, hout] at hv
      change RelErr u (dec (rw i.val k.val) / w k) (w i)
      simpa only [hwroot, w, if_pos (show k ≤ i from le_of_lt hi)] using hv)
  refine ⟨hypos, fun i hi => ?_⟩
  simpa only [w, if_pos hi] using hwe i

/-- The input spectral band and propagated residual error guarantee success of the actual
column and Schur step. No run, trace safety or computed-pivot premise is assumed. -/
theorem rightStep_writes_relative {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {N : ℕ} {u B μ e : ℝ}
    (hI : IsScalar M I) (hM : StdModel u dec M) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10)
    (hμ : 0 < μ) (hμB : μ ≤ B)
    (hη : choleskySchurErrorBound u B μ N < μ / 2)
    {A : Matrix (Fin N) (Fin N) ℝ}
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (he : 0 ≤ e) (hbudget : (2 * (1 + B / μ) * choleskySchurErrorBound u B μ N +
      16 * u * B) / Real.sqrt μ ≤ e) (k : Fin N)
    {τ : Tape K} {m : Mem K} {R L : ℕ × ℕ}
    (hl : m.Live [R, L]) (hRL : R.1 ≠ L.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hpref : IsRelativePrefix dec (M.lit 0) u B μ e A k.val R L m.store) :
    Writes .total I τ (rightStep (Op := Op) (Tst := Tst))
      (Env.frame [N, k.val] [R, L])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧
        IsRelativePrefix dec (M.lit 0) u B μ e A (k.val + 1) R L m'.store) m := by
  have hlR : R.1 < m.store.length := hl R (by simp)
  have hlL : L.1 < m.store.length := hl L (by simp)
  obtain ⟨rw, lw, hR, hL, hres, hfac, hdiag, hupper⟩ := hpref
  let V : Matrix (Fin N) (Fin N) ℝ := fun i j => dec (rw i j)
  have hzero : dec (M.lit 0) = 0 := by
    have hh := hM.lit 0
    norm_num at hh
    exact hh
  obtain ⟨hpE, hE, hp, herror⟩ :=
    CholeskyRounding.residual_bounds hμ hμB hu hlo hscale hη k hres
  have hdiagR := Store.readBlock_one_of_get (hR k.val k.isLt k.val k.isLt)
  have htail : m.store.readBlock R.1 (R.2 + k.val * N + k.val + 1) (N - k.val - 1) =
      some ((List.range (N - k.val - 1)).map fun i => rw (k.val + 1 + i) k.val) := by
    simpa only [Nat.sub_sub, Nat.add_assoc] using
      hR.readBlock_column_suffix k.val k.isLt (k.val + 1) (Nat.succ_le_of_lt k.isLt)
  let xs := (List.range (N - k.val - 1)).map fun i => rw (k.val + 1 + i) k.val
  have hx (i : ℕ) (hi : i < N - k.val - 1) :
      vec xs i = rw (k.val + 1 + i) k.val := vec_map_range _ hi
  have hs : N - k.val - 1 + 1 = N - k.val := by omega
  have hend : k.val * N + k.val + (N - k.val - 1 + 1) ≤ N * N := by
    have hmul := Nat.mul_le_mul_right N (Nat.succ_le_of_lt k.isLt)
    rw [Nat.succ_mul] at hmul
    omega
  unfold rightStep
  call (rightColumn_meets hI) [N - k.val - 1]
    ((R.1, R.2 + k.val * N + k.val), (R.1, R.2 + k.val * N + k.val + 1),
      (L.1, L.2 + k.val * N + k.val))
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
  obtain ⟨hypos, hwe⟩ := column_error_relative (τ := τ.shift m.pos)
    hM hu hu1 hμ hμB hlo hscale hη k rw hres hp hx hcol
  obtain ⟨rs, hrs, -, hdata⟩ := hR₁.readBlock rfl
  have hwords (i j : ℕ) (hi : i < N) (hj : j < N) :
      vec rs (j * N + i) = rw i j := hdata i hi j hj
  have hnz : dec (vec rs (k.val * N + k.val)) ≠ 0 := by
    rw [hwords _ _ k.isLt k.isLt]
    exact hp.ne'
  have hlocal := LU.abs_sub_schurValues_le hM hu (by linarith : u < 1)
    (fun i j => vec rs (j * N + i)) k.val hnz
  call (LU.schurStep_meets hI) [N, k.val] (R) (pre := k.isLt)
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
  refine ⟨by omega, IsRelativePrefix.succ k (fun i j => vec bs (j * N + i)) lw ys
    (Store.holdsMat_of_readBlock rfl hbs) hL₂ ?_ hfac hdiag hupper hzero he ?_ hypos⟩
  · intro i j hi hj
    rw [gaussState_succ A k.isLt]
    refine abs_sub_eliminationStep_le_choleskySchurErrorBound
      (M' := fun i j : Fin N => dec (vec bs (j.val * N + i.val)))
      hμ hμB hu hu1 herror hpE hE hres ?_ i j
      (by change k.val ≤ i.val; omega) (by change k.val ≤ j.val; omega)
    intro a b
    rw [hb a b]
    have hv := hlocal a.val b.val
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
theorem rightLoop_writes_relative {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {N : ℕ} {u B μ e : ℝ}
    (hI : IsScalar M I) (hM : StdModel u dec M) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10)
    (hμ : 0 < μ) (hμB : μ ≤ B)
    (hη : choleskySchurErrorBound u B μ N < μ / 2)
    {A : Matrix (Fin N) (Fin N) ℝ}
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (he : 0 ≤ e) (hbudget : (2 * (1 + B / μ) * choleskySchurErrorBound u B μ N +
      16 * u * B) / Real.sqrt μ ≤ e)
    {τ : Tape K} {m : Mem K} {R L : ℕ × ℕ}
    (hl : m.Live [R, L]) (hRL : R.1 ≠ L.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hpref : IsRelativePrefix dec (M.lit 0) u B μ e A 0 R L m.store) :
    Writes .total I τ (rightLoop (Op := Op) (Tst := Tst)) (Env.frame [N] [R, L])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧ IsRelativePrefix dec (M.lit 0) u B μ e A N R L m'.store) m := by
  unfold rightLoop
  refine (writes_loop rfl
    (fun _ => Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
    (fun _ _ => le_rfl)
    (fun k m' => m'.pos = m.pos ∧ IsRelativePrefix dec (M.lit 0) u B μ e A k R L m'.store)
    ⟨rfl, hpref⟩ ?_).mono le_rfl (fun _ _ h => h)
  intro k hk m' hfr ⟨hpos, hpref'⟩
  have hl' := hl.congr hfr.length_eq
  refine ((rightStep_writes_relative hI hM hu hu1 hμ hμB hη hlo hscale he hbudget ⟨k, hk⟩
    hl' hRL (by simpa only [hfr.len_eq] using hRroom)
    (by simpa only [hfr.len_eq] using hLroom) hpref').in_frame rfl rfl hl').mono le_rfl ?_
  intro m'' hfr' ⟨hpos', hpref''⟩
  exact ⟨hpos'.trans hpos, hpref''⟩

end NLAlib.Cholesky
