/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.State
public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Prefix
public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Guards
public import NLAlib.Krylov.FinitePrecision.PCGContinuationPrecision
public import NLAlib.Ops.Logic.While

/-!
# Total capped rounded PCG rounds

Every active prefix has a nonzero search direction under the input spectral and
cap-dependent precision windows. The actual computed stopping pairing is identified
through functional dot semantics; an early stop implies an exactly zero residual.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.RunPrefix.direction_ne_zero` derives continuation.
* `NLAlib.Krylov.CG.HSPCG.Rounded.rounds_writes` extracts the actual rounded prefix.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded

open Ops
open scoped Matrix

/-- Every initialized numerical prefix retains the actual oracle output at its endpoint. -/
theorem RunPrefix.z_eq {n k : ℕ} {A P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {b : Fin n → ℝ} {e rho : ℝ} {s : PCGState ℝ (Fin n)}
    (h : RunPrefix A P O b e k s rho) : s.z = O.mulVec s.r := by
  rcases h with ⟨_, rfl, _, _⟩ | ⟨R, _, hM, hO, _, _, hs, _⟩
  · rfl
  · cases hM
    cases hO
    rw [← hs]
    exact R.z_eq k (le_refl k)

private theorem three_mul_le {m m' e : ℝ} (hm : 0 < m)
    (hp : 6 * e * m' ≤ m) : 3 * e * m' ≤ m := by
  linarith

/-- Raw positive spectral windows and the common cap-dependent precision window derive
the direction guard for every nonzero endpoint residual, including the initialized state. -/
theorem RunPrefix.direction_ne_zero {n k cap : ℕ} {A P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {b : Fin n → ℝ} {e rho : ℝ} {s : PCGState ℝ (Fin n)}
    (h : RunPrefix A P O b e k s rho) (hP : Pᵀ = P)
    {a a' m m' : ℝ} (ha : 0 < a) (hAs : spectrum ℝ A ⊆ Set.Icc a a')
    (hm : 0 < m) (hMs : spectrum ℝ P ⊆ Set.Icc m m') (he : 0 ≤ e)
    (hAp : 6 * e * a' ≤ a) (hMp : 6 * e * m' ≤ m) (hO : O.ε ≤ e)
    (hk : k ≤ cap) (hsmall : e * (1024 * (a' / a) * (m' / m)) ^ (cap + 1) ≤ 1 / 2)
    (hr : s.r ≠ 0) : s.p ≠ 0 := by
  rcases h with ⟨_, rfl, _, _⟩ | ⟨R, hA, hM, hRO, _, hε, hs, _⟩
  · have hprec := three_mul_le hm hMp
    have hpos := HSCG.Carried.Rounded.curvature_margin hP hm hMs he hprec
      (le_refl 0) he hO hr (O.mulVec b) (O.norm_sub_mulVec_le b)
    intro hz
    change O.mulVec b = 0 at hz
    simp only [hz, dotProduct_zero, zero_mul] at hpos
    exact lt_irrefl _ hpos
  · cases hA
    cases hM
    cases hRO
    cases hε
    rw [← hs] at hr ⊢
    exact R.p_ne_zero_of_r_ne_zero_of_le_cap ha hAs hm hMs hAp hMp hO hk hsmall hr

private theorem pairing_pos {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {s : PCGState ℝ (Fin n)} {rho m m' e ed : ℝ}
    (hP : Pᵀ = P) (hm : 0 < m) (hs : spectrum ℝ P ⊆ Set.Icc m m')
    (he : 0 ≤ e) (hp : 6 * e * m' ≤ m) (hd : 0 ≤ ed) (hde : ed ≤ e)
    (hO : O.ε ≤ e) (hz : s.z = O.mulVec s.r) (hr : s.r ≠ 0)
    (herr : |rho - s.r ⬝ᵥ s.z| ≤ ed * ∑ i, |s.r i * s.z i|) : 0 < rho := by
  have hmarg := HSCG.Carried.Rounded.curvature_margin hP hm hs he
    (three_mul_le hm hp) hd hde hO hr s.z
      (by simpa only [hz] using O.norm_sub_mulVec_le s.r)
  have hl := (abs_le.mp herr).1
  linarith

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op] [Has CmpTst Tst]

/-- The capped loop returns its actual initialized numerical prefix. Active divisors are
derived from raw matrix and precision inputs, and every early exit has zero residual. -/
theorem rounds_writes {F : Machine ℝ} {em u e : ℝ} {ε : Blas1Err}
    {ok : ℕ → Prop} {n cap : ℕ} {A P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {b : Fin n → ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar F I) (hF : StdModel u id F) (hB : IsBlas1 id ε ok I) (hok : ok n)
    (hA : IsMatvec id A (em * specNorm A) I)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n))
    (hD : I.IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn F) (OutApart (fun _ => True)))
    (hCmp : IsCmp id I) (hAT : Aᵀ = A) (hPT : Pᵀ = P) {a a' m m' : ℝ}
    (ha : 0 < a) (hAs : spectrum ℝ A ⊆ Set.Icc a a')
    (hm : 0 < m) (hMs : spectrum ℝ P ⊆ Set.Icc m m')
    (hu : 0 ≤ u) (hd : 0 ≤ ε.dot n) (haa : 0 ≤ ε.axpy)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ε.dot n ≤ e) (hae : ε.axpy ≤ e)
    (he : e ≤ 1 / 100) (hO : O.ε ≤ e)
    (hAp : 6 * e * a' ≤ a) (hMp : 6 * e * m' ≤ m)
    (hwindow : e * (1024 * (a' / a) * (m' / m)) ^ (cap + 1) ≤ 1 / 2)
    {τ : Tape ℝ} {μ : Mem ℝ} {x r z p v : ℕ × ℕ} {rho : ℝ}
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1)
    (hzp : z.1 ≠ p.1) (hzv : z.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [x, r, z, p, v])
    (hs : StoresCached n x r z p v ⟨0, b, O.mulVec b, O.mulVec b⟩ rho μ)
    (hcache : |rho - b ⬝ᵥ O.mulVec b| ≤ ε.dot n * ∑ i, |b i * O.mulVec b i|)
    (hfn : rho = pairingValue F b (O.mulVec b))
    (hz : μ.Room [x, r, z, p, v] [n, n, n, n, 1]) :
    Writes .total I τ rounds (Env.frame [n, cap] [x, r, z, p, v, x, r, z, p, v])
      (Fp.blocks [x, r, z, p, v] [n, n, n, n, 1])
      (fun ν => ν.pos = μ.pos ∧ ∃ j ≤ cap, ∃ s rho',
        StoresCached n x r z p v s rho' ν ∧ RunPrefix A P O b e j s rho' ∧
          (j < cap → s.r = 0)) μ := by
  classical
  let fp := Fp.blocks [x, r, z, p, v] [n, n, n, n, 1]
  let Inv := fun j ν => ν.pos = μ.pos ∧ ∃ s rho',
    StoresCached n x r z p v s rho' ν ∧ RunPrefix A P O b e j s rho' ∧
      |rho' - s.r ⬝ᵥ s.z| ≤ ε.dot n * ∑ i, |s.r i * s.z i| ∧
        rho' = pairingValue F s.r s.z
  have he0 := hu.trans hue
  have hMH : P.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hPT]
  have hPD : P.PosDef := hMH.posDef_iff_eigenvalue_pos.mpr fun i hi =>
    hm.trans_le (hMH.spectrum_subset_iff.mp hMs i hi).1
  have hAH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hAT]
  have h3M : 3 * e * m' ≤ m := three_mul_le hm hMp
  have hnonneg := pairing_nonneg_of_spectrum_subset_Icc hPT hm hMs he0 h3M
    hd hde hO rfl hcache
  have hnorm : |rho - b ⬝ᵥ O.mulVec b| ≤
      e * ‖WithLp.toLp 2 b‖ * ‖WithLp.toLp 2 (O.mulVec b)‖ := by
    have hsum := HSCG.Carried.Rounded.sum_abs_mul_le b (O.mulVec b)
    have h₁ := mul_le_mul_of_nonneg_left hsum hd
    have h₂ := mul_le_mul_of_nonneg_right hde
      (mul_nonneg (norm_nonneg (WithLp.toLp 2 b))
        (norm_nonneg (WithLp.toLp 2 (O.mulVec b))))
    nlinarith
  refine (writes_whileFuel rfl (fun _ => fp) (fun _ _ => le_rfl) ⊥ Inv _
    ⟨rfl, _, rho, hs, RunPrefix.zero hnorm hnonneg, hcache, hfn⟩ ?_ ?_).mono
      (by simp [fp]) (fun _ _ h => h)
  · rintro j hj ν hfr ⟨hpos, s, rho', hstored, hprefix, hcache', hfn'⟩
    by_cases hactive : 0 < rho'
    · refine ⟨true, ?_, ?_⟩
      · rw [Interp.testAt_eq rfl rfl, hCmp.test_isPos hstored.2]
        simp only [id_eq, hactive, decide_true]
      · have hrne : s.r ≠ 0 := by
          intro hr
          simp only [hr, zero_dotProduct, Pi.zero_apply, abs_zero,
            Finset.sum_const_zero, mul_zero, zero_mul, sub_zero] at hcache'
          exact hactive.not_ge ((le_abs_self _).trans hcache')
        have hpne := hprefix.direction_ne_zero hPT ha hAs hm hMs he0 hAp hMp hO
          (Nat.le_of_lt hj) hwindow hrne
        have h3A := three_mul_le ha hAp
        have hmarg := margins_of_spectrum_subset_Icc hAT hPT ha hm hAs hMs he0 h3A
          h3M hd hde hem hO hprefix.z_eq hrne hpne
        have hl' : ν.Live [x, r, z, p, v] := by
          simpa only [Mem.Live, hfr.length_eq] using hl
        have hz' : ν.Room [x, r, z, p, v] [n, n, n, n, 1] := by
          simpa [Mem.Room, hfr.len_eq] using hz
        refine (writes_frame rfl rfl ((ν.live_append _ _).mpr ⟨hl', hl'⟩)
          (guardedStep_writes hS hF hB hok hA hP hD
            hxr hxz hxp hxv hrz hrp hrv hzp hzv hpv hl' hstored hfn' hmarg hz')).mono
              le_rfl ?_
        rintro ω _ ⟨hpos', next, rho'', hnext, hbounds, hfn''⟩
        have hbounds' := hbounds
        obtain ⟨q, curv, alpha, beta, hmv, hn, hc, hi, hcurv, halpha, hx, hr,
          hznext, hnnext, hbeta, hpnext⟩ := hbounds'
        have hnonneg' := pairing_nonneg_of_spectrum_subset_Icc hPT hm hMs he0 h3M
          hd hde hO hznext hnnext
        exact ⟨hpos'.trans hpos, next, rho'', hnext,
          RoundBounds.append_prefix hprefix hbounds hAH hPD hu hd haa hem hue hde hae he hnonneg',
          hnnext, hfn''⟩
    · refine ⟨false, ?_, ?_⟩
      · rw [Interp.testAt_eq rfl rfl, hCmp.test_isPos hstored.2]
        simp only [id_eq, hactive, decide_false]
      · have hrzero : s.r = 0 := by
          by_contra hrne
          exact hactive (pairing_pos hPT hm hMs he0 hMp hd hde hO hprefix.z_eq hrne hcache')
        exact Writes.skip ⟨hpos, j, Nat.le_of_lt hj, s, rho', hstored, hprefix, fun _ => hrzero⟩
  · rintro ν _ ⟨hpos, s, rho', hstored, hprefix, _, _⟩
    exact Writes.skip ⟨hpos, cap, le_rfl, s, rho', hstored, hprefix, by omega⟩

end NLAlib.Krylov.CG.HSPCG.Rounded
