/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.DotMixed
public import NLAlib.Ops.Blas.DotExecution
public import NLAlib.Ops.Catalog.Operator
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Underflow-aware residual caches

The scalar-lowered sequential self-dot kernel writes the actual rounded cache. Its
input-only range condition gives a mixed relative/absolute error bound. A decoded zero
then certifies a small recursive residual, including dimension zero. This does not assert
that the true residual of the computed iterate vanishes. [Higham2002, §2.2 and §3.1].

## Main results

* `NLAlib.Krylov.CG.wp_residualCache`: total actual execution and its mixed-error certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG

open Ops

variable {K : Type}

/-- The self-product sum is the squared Euclidean norm, also for the empty vector. -/
theorem sum_self_mul_eq_norm_sq (r : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, r i * r i = ‖WithLp.toLp 2 (fun i : Fin n => r i)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [WithLp.ofLp_toLp, pow_two] using
    (Fin.sum_univ_eq_sum_range (fun i => r i * r i) n).symm

/-- The sum of absolute self-products has the same squared-norm value. -/
theorem sum_abs_self_mul_eq_norm_sq (r : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, |r i * r i| = ‖WithLp.toLp 2 (fun i : Fin n => r i)‖ ^ 2 := by
  rw [← sum_self_mul_eq_norm_sq]
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (mul_self_nonneg (r i))

/-- A mixed-error residual cache can vanish only within its explicit underflow threshold. -/
theorem norm_sq_le_of_residualCache_eq_zero {r : ℕ → ℝ} {n : ℕ} {u eta cache : ℝ}
    (herr : Computation.AbsRelErr ((1 + u) ^ (2 * n) - 1)
      (n * (1 + u) ^ (2 * n) * (2 + u) * eta)
      (‖WithLp.toLp 2 (fun i : Fin n => r i)‖ ^ 2) cache)
    (hsmall : (1 + u) ^ (2 * n) < 2) (hzero : cache = 0) :
    ‖WithLp.toLp 2 (fun i : Fin n => r i)‖ ^ 2 ≤
      (n * (1 + u) ^ (2 * n) * (2 + u) * eta) / (2 - (1 + u) ^ (2 * n)) := by
  rw [hzero] at herr
  have h := herr.abs_le_of_eq_zero (by linarith)
  simpa only [abs_of_nonneg (sq_nonneg ‖WithLp.toLp 2 (fun i : Fin n => r i)‖),
    show 1 - ((1 + u) ^ (2 * n) - 1) = 2 - (1 + u) ^ (2 * n) by ring] using h

/-- Mixed arithmetic and an input-only radius certificate bound the actual self-dot word. -/
theorem residualCache_error {M : Machine K} {dec : K → ℝ} {u eta B : ℝ}
    {safe : ℝ → Prop} (hM : MixedModel u eta dec M safe) (hzero : dec (M.lit 0) = 0)
    (n : ℕ) (r : ℕ → K) (hSafe : ∀ z : ℝ, |z| ≤ B → safe z)
    (hRange : (1 + u) ^ (2 * n) * ‖WithLp.toLp 2 (fun i : Fin n => dec (r i))‖ ^ 2 +
      n * (1 + u) ^ (2 * n) * (2 + u) * eta ≤ B) :
    Computation.AbsRelErr ((1 + u) ^ (2 * n) - 1)
      (n * (1 + u) ^ (2 * n) * (2 + u) * eta)
      (‖WithLp.toLp 2 (fun i : Fin n => dec (r i))‖ ^ 2)
      (dec (sumSeqF M (fun i => M.mul (r i) (r i)) n)) := by
  have hr : DotRange u eta dec safe n r r := DotRange.of_le
    (by simpa only [sum_abs_self_mul_eq_norm_sq] using hRange) hSafe
  have he := hM.abs_sum_mul_sub_sumSeqF_le hzero hr
  simpa only [Computation.AbsRelErr, sum_self_mul_eq_norm_sq, sum_abs_self_mul_eq_norm_sq,
    abs_of_nonneg (sq_nonneg ‖WithLp.toLp 2 (fun i : Fin n => dec (r i))‖)] using he

/-- The actual scalar-lowered CG cache kernel is total under ordinary storage conditions.
Only input values enter the range condition. The result includes the exact update, its
mixed error and the small-residual consequence of a computed zero; no successful run is assumed. -/
theorem wp_residualCache [Inhabited K] {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]
    [Apart Blas1Op ScalarOp Op] {M : Machine K} {dec : K → ℝ} {u eta B : ℝ}
    {safe : ℝ → Prop} {I : Interp Op Tst K} (hI : IsScalar M I)
    (hM : MixedModel u eta dec M safe) (hzero : dec (M.lit 0) = 0)
    {τ : Tape K} {n : ℕ} {r z : ℕ × ℕ} {m : Mem K} {rs : List K}
    (hl : m.Live [r, z]) (hr : m.store.readBlock r.1 r.2 n = some rs)
    (hz : z.2 < m.store.len z.1) (hSafe : ∀ a : ℝ, |a| ≤ B → safe a)
    (hRange : (1 + u) ^ (2 * n) * ‖WithLp.toLp 2 (decv dec n rs)‖ ^ 2 +
      n * (1 + u) ^ (2 * n) * (2 + u) * eta ≤ B) :
    Wp .total I τ (dotSum.body.link Blas.sumSeqTable) (Env.frame [n] [r, r, z])
      (fun out => ∃ cache, out = m.upd z cache ∧ out.store.get z.1 z.2 = some cache ∧
        Computation.AbsRelErr ((1 + u) ^ (2 * n) - 1)
          (n * (1 + u) ^ (2 * n) * (2 + u) * eta)
          (‖WithLp.toLp 2 (decv dec n rs)‖ ^ 2) (dec cache) ∧
        ((1 + u) ^ (2 * n) < 2 → dec cache = 0 →
          ‖WithLp.toLp 2 (decv dec n rs)‖ ^ 2 ≤
            (n * (1 + u) ^ (2 * n) * (2 + u) * eta) /
              (2 - (1 + u) ^ (2 * n)))) m := by
  have he := residualCache_error hM hzero n (vec rs) hSafe hRange
  have hLive : m.Live [r, r, z] := by simpa [Mem.Live] using hl
  have hWord := wp_dotSum_seq (I := I) (M := M) (τ := τ) (n := n)
    (x := r) (y := r) (z := z) (m := m) (xs := rs) (ys := rs) hI hLive hr hr hz
  apply Wp.mono hWord
  intro out hout
  subst out
  refine ⟨_, rfl, ?_, he, fun hs hc => norm_sq_le_of_residualCache_eq_zero
    (r := fun i => dec (vec rs i)) (n := n) (u := u) (eta := eta) he hs hc⟩
  exact Store.get_upd_self hz _

end NLAlib.Krylov.CG
