/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramRoundedRun
public import NLAlib.Krylov.Processes.LanczosProgramRoundedPrefixState
public import NLAlib.Krylov.Processes.LanczosProgramRoundedZero

/-!
# Executed rounded Lanczos prefixes and zero continuation

Each actual step either extends the existing positive-length LanczosRun or writes the
forced zero continuation. This separates the active compression from the allocated output
horizon; no near-unit assertion is made about continued zero columns.

## Main results

* `NLAlib.LanczosImplementation.exec_rounded_prefix_step`: a decoded active prefix advances.
* `NLAlib.LanczosImplementation.exec_rounded_loop`: every requested rounded step executes.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation Builder
open scoped Matrix

variable {P ι K : Type} [DecidableEq P] {u : P → ℝ} {dec : P → K → ℝ} {storedMatrix : Bool}
    {mv : ℕ → Builder P ι ℕ ℕ Unit}

local macro "prefixStep(" tag:term "," N:term "," j:term "," mv:term ")" : term => `(do
  ($mv ($j))
  ins (.un $tag .neg ⟨8, 1⟩ ⟨3, IExp.var ($j)⟩)
  axpy $tag ⟨8, 1⟩ 5 0 7 0 (IExp.const ($N))
  dot $tag ⟨2, IExp.var ($j)⟩ 1 (IExp.const ($N) * IExp.var ($j)) 7 0 (IExp.const ($N))
  ins (.un $tag .neg ⟨8, 1⟩ ⟨2, IExp.var ($j)⟩)
  axpy $tag ⟨8, 1⟩ 1 (IExp.const ($N) * IExp.var ($j)) 7 0 (IExp.const ($N))
  nrm2 $tag ⟨3, IExp.var ($j) + 1⟩ 7 0 (IExp.const ($N))
  copyv $tag 1 (IExp.const ($N) * IExp.var ($j)) 5 0 (IExp.const ($N))
  ifThenElse $tag .eq ⟨3, IExp.var ($j) + 1⟩ ⟨8, 0⟩
    (forRange (IExp.const ($N)) fun i =>
      ins (.lit $tag ⟨1, IExp.const ($N) * (IExp.var ($j) + 1) + IExp.var i⟩ 0)) (do
      copyv $tag 7 0 1 (IExp.const ($N) * (IExp.var ($j) + 1)) (IExp.const ($N))
      rscl $tag ⟨3, IExp.var ($j) + 1⟩ 1
        (IExp.const ($N) * (IExp.var ($j) + 1)) (IExp.const ($N))))


private theorem exec_prefix_one (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I) (tag : P)
    {N q : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b v1 : Fin N → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι))
    (hs : StoreContext tag dec N q 0 A b (Function.update (0 : ℕ → Fin N → ℝ) 1 v1)
      (fun _ => 0) (fun _ => 0) s st.store storedMatrix)
    (hq : 0 < q) (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hunit : |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ lanczosImplementationRoundoffBound N (u tag))
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A)
      (fun store => if storedMatrix then HoldsDecoded store dec tag 6 0 A else True)
      1 7 (IExp.const N * IExp.var t) 0 (mv t)) :
    ∃ out, exec I (prefixStep(tag,N,0,mv) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      RoundedPrefix tag dec N q 1 A b v1
        (lanczosImplementationRoundoffBound N (u tag)) s out.store storedMatrix := by
  obtain ⟨out, uv, wv, zv, an, bn, vn, hr, hctx, hu, hw, ha, hez, hd,
      hbn, _, hvzero, hvunit⟩ := exec_rounded_step (hmv := hmv) I h hz hc tag st hs hq hsmall
  simp only [Nat.zero_add, Function.update_self] at hu ha hez
  simp only [zero_smul, sub_zero, abs_zero, zero_mul, add_zero] at hw
  obtain ⟨R, hH, hε, hv, hα, hβ⟩ := exists_lanczosRun_one A hA
    (lanczosImplementationRoundoffBound N (u tag))
    (lanczosImplementationRoundoffBound_nonneg N (h.nonneg trivial)) hsmall
    v1 uv wv zv vn an bn hunit hu hw ha hez hd hbn hvunit
  refine ⟨out, hr, Or.inr ⟨1, R, le_rfl, hH, hε, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [hv]
  · simpa only [Nat.zero_add, hv, hα, hβ, Pi.zero_def] using hctx
  · intro i hi
    simp [hv, Function.update_of_ne (show i ≠ 1 by omega),
      Function.update_of_ne (show i ≠ 2 by omega)]
  · intro i hi
    simp [hα, hβ, Function.update_of_ne (show i ≠ 1 by omega)]
  · intro hzero
    have : bn = 0 := by simpa [hβ] using hzero
    simpa [hv] using hvzero this
  · omega

private theorem exec_prefix_zero (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b v1 : Fin N → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι))
    (hs : StoreContext tag dec N q j A b (Function.update (0 : ℕ → Fin N → ℝ) 1 v1)
      (fun _ => 0) (fun _ => 0) s st.store storedMatrix)
    (hj : j < q) (hb : b = 0) (hv1 : v1 = 0)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A)
      (fun store => if storedMatrix then HoldsDecoded store dec tag 6 0 A else True)
      1 7 (IExp.const N * IExp.var t) 0 (mv t)) :
    ∃ out, exec I (prefixStep(tag,N,j,mv) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      RoundedPrefix tag dec N q (j + 1) A b v1
        (lanczosImplementationRoundoffBound N (u tag)) s out.store storedMatrix := by
  have hv : (Function.update (0 : ℕ → Fin N → ℝ) 1 v1) (j + 1) = 0 := by simp [hv1]
  obtain ⟨out, hr, hs⟩ := exec_rounded_step_of_zero (hmv := hmv) I h hz hc tag st hs hj hsmall
    hv rfl
  refine ⟨out, hr, Or.inl ⟨Or.inr hb, ?_⟩⟩
  simpa [hv1] using hs

private theorem exec_prefix_terminal (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I) (tag : P)
    {N q j m : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b v1 : Fin N → ℝ} {s : ℝ}
    (R : LanczosRun N m) (st : St P K (OpCount P ι))
    (hs : StoreContext tag dec N q j A b R.v R.α R.β s st.store storedMatrix)
    (hj : j < q) (hm : m ≤ j) (hH : R.H = A)
    (hε : R.ε = lanczosImplementationRoundoffBound N (u tag)) (hv1 : R.v 1 = v1)
    (hv : ∀ i, m + 1 < i → R.v i = 0)
    (hab : ∀ i, m < i → R.α i = 0 ∧ R.β i = 0)
    (hterm : R.β m = 0 → R.v (m + 1) = 0) (hzero : R.β m = 0)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A)
      (fun store => if storedMatrix then HoldsDecoded store dec tag 6 0 A else True)
      1 7 (IExp.const N * IExp.var t) 0 (mv t)) :
    ∃ out, exec I (prefixStep(tag,N,j,mv) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      RoundedPrefix tag dec N q (j + 1) A b v1
        (lanczosImplementationRoundoffBound N (u tag)) s out.store storedMatrix := by
  have hvcur : R.v (j + 1) = 0 := by
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · exact hterm hzero
    · exact hv _ (by omega)
  have hβcur : R.β j = 0 := by
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · exact hzero
    · exact (hab j hlt).2
  obtain ⟨out, hr, hs⟩ :=
    exec_rounded_step_of_zero (hmv := hmv) I h hz hc tag st hs hj hsmall hvcur hβcur
  have hvn := hv (j + 2) (by omega)
  have han := (hab (j + 1) (by omega)).1
  have hbn := (hab (j + 1) (by omega)).2
  have ev : Function.update R.v (j + 2) 0 = R.v := by
    rw [← hvn, Function.update_eq_self]
  have ea : Function.update R.α (j + 1) 0 = R.α := by
    rw [← han, Function.update_eq_self]
  have eb : Function.update R.β (j + 1) 0 = R.β := by
    rw [← hbn, Function.update_eq_self]
  rw [ev, ea, eb] at hs
  exact ⟨out, hr, Or.inr ⟨m, R, by omega, hH, hε, hv1, hs, hv, hab, hterm,
    fun _ => hzero⟩⟩

private theorem exec_prefix_extend (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b v1 : Fin N → ℝ} {s : ℝ}
    (R : LanczosRun N j) (st : St P K (OpCount P ι))
    (hs : StoreContext tag dec N q j A b R.v R.α R.β s st.store storedMatrix)
    (hj : j < q) (hH : R.H = A)
    (hε : R.ε = lanczosImplementationRoundoffBound N (u tag)) (hv1 : R.v 1 = v1)
    (hv : ∀ i, j + 1 < i → R.v i = 0)
    (hab : ∀ i, j < i → R.α i = 0 ∧ R.β i = 0) (hactive : R.β j ≠ 0)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A)
      (fun store => if storedMatrix then HoldsDecoded store dec tag 6 0 A else True)
      1 7 (IExp.const N * IExp.var t) 0 (mv t)) :
    ∃ out, exec I (prefixStep(tag,N,j,mv) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      RoundedPrefix tag dec N q (j + 1) A b v1
        (lanczosImplementationRoundoffBound N (u tag)) s out.store storedMatrix := by
  obtain ⟨out, uv, wv, zv, an, bn, vn, hr, hctx, hu, hw, ha, hez, hd,
      hbn, _, hvzero, hvunit⟩ := exec_rounded_step (hmv := hmv) I h hz hc tag st hs hj hsmall
  rw [← hH, ← hε] at hu
  rw [← hε] at hw ha hez hd hvunit
  obtain ⟨S, hSH, hSε, hsv, hsα, hsβ⟩ :=
    exists_lanczosRun_succ R uv wv zv vn an bn hactive hu hw ha hez hd hbn hvunit
  refine ⟨out, hr, Or.inr ⟨j + 1, S, le_rfl, hSH.trans hH, hSε.trans hε,
    ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [hsv, Function.update_of_ne (show 1 ≠ j + 2 by omega)] using hv1
  · simpa only [hsv, hsα, hsβ] using hctx
  · intro i hi
    rw [hsv, Function.update_of_ne (show i ≠ j + 2 by omega)]
    exact hv i (by omega)
  · intro i hi
    rw [hsα, hsβ, Function.update_of_ne (show i ≠ j + 1 by omega),
      Function.update_of_ne (show i ≠ j + 1 by omega)]
    exact hab i (by omega)
  · intro hzero
    have : bn = 0 := by simpa [hsβ] using hzero
    simpa only [hsv, show j + 1 + 1 = j + 2 by omega, Function.update_self] using hvzero this
  · omega

/-- The next actual rounded step extends the active prefix until its next norm is zero.
After that point it executes the zero continuation. Nearly unit initial data and its zero
case are supplied by actual initialization, rather than assumed by the whole-program result. -/
theorem exec_rounded_prefix_step (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b v1 : Fin N → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι))
    (hs : RoundedPrefix tag dec N q j A b v1
      (lanczosImplementationRoundoffBound N (u tag)) s st.store storedMatrix)
    (hj : j < q) (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hzero : b = 0 → v1 = 0)
    (hunit : b ≠ 0 → |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤
      lanczosImplementationRoundoffBound N (u tag))
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A)
      (fun store => if storedMatrix then HoldsDecoded store dec tag 6 0 A else True)
      1 7 (IExp.const N * IExp.var t) 0 (mv t)) :
    ∃ out, exec I (prefixStep(tag,N,j,mv) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      RoundedPrefix tag dec N q (j + 1) A b v1
        (lanczosImplementationRoundoffBound N (u tag)) s out.store storedMatrix := by
  rcases hs with ⟨hj0, hs⟩ | ⟨m, R, hm, hH, hε, hv1, hs, hv, hab, ht, hearly⟩
  · by_cases hb : b = 0
    · exact exec_prefix_zero (hmv := hmv) I h hz hc tag st hs hj hb (hzero hb) hsmall
    · have : j = 0 := hj0.resolve_right hb
      subst j
      exact exec_prefix_one (hmv := hmv) I h hz hc tag st hs hj hA hsmall (hunit hb)
  · by_cases hterm : R.β m = 0
    · exact exec_prefix_terminal (hmv := hmv) I h hz hc tag R st hs hj hm hH hε hv1 hv hab ht
        hterm hsmall
    · have : m = j := by
        by_contra hmj
        exact hterm (hearly (by omega))
      subst m
      exact exec_prefix_extend (hmv := hmv) I h hz hc tag R st hs hj hH hε hv1 hv hab hterm hsmall

/-- Execute every requested rounded step from a certified decoded prefix. No accumulated
roundoff horizon is required for execution or for extraction of the active LanczosRun. -/
theorem exec_rounded_loop (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I) (tag : P)
    {N q : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b v1 : Fin N → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι))
    (hs : RoundedPrefix tag dec N q 0 A b v1
      (lanczosImplementationRoundoffBound N (u tag)) s st.store storedMatrix)
    (hA : Aᵀ = A) (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hzero : b = 0 → v1 = 0)
    (hunit : b ≠ 0 → |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤
      lanczosImplementationRoundoffBound N (u tag))
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A)
      (fun store => if storedMatrix then HoldsDecoded store dec tag 6 0 A else True)
      1 7 (IExp.const N * IExp.var t) 0 (mv t)) :
    ∃ out, exec I (forRange (.const q) fun j =>
      (prefixStep(tag,N,j,mv) : Builder P ι ℕ ℕ Unit)).run st = some out ∧
      RoundedPrefix tag dec N q q A b v1
        (lanczosImplementationRoundoffBound N (u tag)) s out.store storedMatrix := by
  obtain ⟨out, hr, hctx⟩ := exists_exec_loop_eq_some_of_forall I (n := IExp.const q)
    (body := fun j => (prefixStep(tag,N,j,mv) : Builder P ι ℕ ℕ Unit).run)
    (fun j st => RoundedPrefix tag dec N q j A b v1
      (lanczosImplementationRoundoffBound N (u tag)) s st.store storedMatrix) hs
    (fun j hj st hs => exec_rounded_prefix_step (hmv := hmv) I h hz hc tag st hs hj hA hsmall
      hzero hunit)
  refine ⟨out, ?_, hctx⟩
  change exec I (.seq (.loop (.const q)
    (fun j => (prefixStep(tag,N,j,mv) : Builder P ι ℕ ℕ Unit).run)) .skip) st = _
  rw [exec_seq_skip]
  exact hr

end NLAlib.LanczosImplementation
