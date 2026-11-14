/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Solve

/-!
# Literal-zero initialization for total rounded PCG

The public zero-start tree consumes uninitialized iterate capacity. The same actual scalar
literal loop establishes its zero word vector before the total capped solver runs.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.zeroStart_writes`: total initialized-prefix execution.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op] [Has CmpTst Tst]

/-- Literal-zero initialization and raw spectral precision establish the actual capped
rounded prefix from supplied uninitialized iterate capacity. The right-hand side may be zero;
no successful execution or computed-trajectory assumption is required. -/
theorem zeroStart_writes {F : Machine ℝ} {em u e : ℝ} {ε : Blas1Err}
    {ok : ℕ → Prop} {n cap : ℕ} {A P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    (hS : IsScalar F I) (hF : StdModel u id F) (hB : IsBlas1 id ε ok I) (hok : ok n)
    (hA : IsMatvec id A (em * specNorm A) I)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n))
    (hD : I.IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn F) (OutApart (fun _ => True)))
    (hCmp : IsCmp id I) (hAT : Aᵀ = A) (hPT : Pᵀ = P) {a a' p p' : ℝ}
    (ha : 0 < a) (hp : 0 < p)
    (hAs : spectrum ℝ A ⊆ Set.Icc a a') (hPs : spectrum ℝ P ⊆ Set.Icc p p')
    (hu : 0 ≤ u) (hd : 0 ≤ ε.dot n) (haa : 0 ≤ ε.axpy)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ε.dot n ≤ e) (hae : ε.axpy ≤ e)
    (he : e ≤ 1 / 100) (hOe : O.ε ≤ e)
    (hAp : 6 * e * a' ≤ a) (hPp : 6 * e * p' ≤ p)
    (hwindow : e * (1024 * (a' / a) * (p' / p)) ^ (cap + 1) ≤ 1 / 2)
    {τ : Tape ℝ} {μ : Mem ℝ} {b x r z v : ℕ × ℕ} {bs : List ℝ}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbz : b.1 ≠ z.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxv : x.1 ≠ v.1)
    (hrz : r.1 ≠ z.1) (hrv : r.1 ≠ v.1) (hzv : z.1 ≠ v.1)
    (hl : μ.Live [b, x, r, z, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hz : μ.Room [x, r, z, v] [n, n, n, n]) :
    Writes .total I τ zeroStart (Env.frame [n, cap] [b, x, x, r, z, v])
      (Fp.blocks [x, r, z, v] [n, n, n, n])
      (fun ν => ν.pos = μ.pos ∧ ∃ m ≤ cap, ∃ s rho,
        StoresState id n x r z v s ν ∧ RunPrefix A P O (decv id n bs) e m s rho ∧
          (m < cap → s.r = 0)) μ := by
  have hzero := CG.writes_zeroVector_readBlock (m := μ) (τ := τ) (x := x) hS hz.1
  refine Writes.seq_le (hzero.in_frame rfl rfl (by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using hl x (by simp))) (by fp_sub)
    fun ν hfr ⟨hpos, hx⟩ => ?_
  have hlν : ν.Live [b, x, r, z, v] := by
    simpa only [Mem.Live, hfr.length_eq] using hl
  have hzν : ν.Room [x, r, z, v] [n, n, n, n] := by
    simpa only [Mem.Room, hfr.len_eq] using hz
  have hbν : ν.store.readBlock b.1 b.2 n = some bs :=
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hbs
  have hx0 : decv id n (List.replicate n (F.lit 0)) = 0 := by
    have hz0 : F.lit 0 = 0 := hF.zero
    ext i
    simp [decv, vec, i.isLt, hz0]
  refine (solve_writes hS hF hB hok hA hP hD hCmp hAT hPT ha hp hAs hPs
    hu hd haa hem hue hde hae he hOe hAp hPp hwindow
    hbx hbr hbz hbv hxr hxz hxv hrz hrv hzv hlν hbν hx hx0 hzν).mono le_rfl ?_
  rintro μ' _ ⟨hpos', hpost⟩
  exact ⟨hpos'.trans hpos, hpost⟩

end NLAlib.Krylov.CG.HSPCG.Rounded
