/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramRoundedCommit

/-!
# Composing actual rounded Lanczos execution

The concrete Paige order is retained through matvec, previous-vector subtraction,
projection and the next norm. Every computed intermediate and stored coefficient comes
from primitive execution under the existing scalar contract. Resource bounds are supplied
independently by the static analysis of the registered dense tree.

## Main results

* `NLAlib.LanczosImplementation.exec_rounded_work`: actual projected work and next norm.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation Builder
open scoped Matrix

variable {P ι K : Type} [DecidableEq P]
    {u : P → ℝ} {dec : P → K → ℝ} {storedMatrix : Bool}
    {mv : ℕ → Builder P ι ℕ ℕ Unit}

local macro "roundedUpdate(" tag:term "," N:term "," j:term "," coeff:term ","
    src:term "," off:term ")" : term => `(do
  ins (.un $tag .neg ⟨8, 1⟩ ⟨$coeff, IExp.var ($j)⟩)
  axpy $tag ⟨8, 1⟩ $src $off 7 0 (IExp.const ($N)))

local macro "roundedWork(" tag:term "," N:term "," j:term "," mv:term ")" : term => `(do
  ($mv ($j))
  (roundedUpdate($tag,$N,$j,3,5,0))
  dot $tag ⟨2, IExp.var ($j)⟩ 1 (IExp.const ($N) * IExp.var ($j)) 7 0 (IExp.const ($N))
  (roundedUpdate($tag,$N,$j,2,1,IExp.const ($N) * IExp.var ($j)))
  nrm2 $tag ⟨3, IExp.var ($j) + 1⟩ 7 0 (IExp.const ($N)))

local macro "roundedCommit(" tag:term "," N:term "," j:term ")" : term => `(do
  copyv $tag 1 (IExp.const ($N) * IExp.var ($j)) 5 0 (IExp.const ($N))
  ifThenElse $tag .eq ⟨3, IExp.var ($j) + 1⟩ ⟨8, 0⟩
    (forRange (IExp.const ($N)) fun i =>
      ins (.lit $tag ⟨1, IExp.const ($N) * (IExp.var ($j) + 1) + IExp.var i⟩ 0)) (do
      copyv $tag 7 0 1 (IExp.const ($N) * (IExp.var ($j) + 1)) (IExp.const ($N))
      rscl $tag ⟨3, IExp.var ($j) + 1⟩ 1
        (IExp.const ($N) * (IExp.var ($j) + 1)) (IExp.const ($N))))

local macro "roundedStep(" tag:term "," N:term "," j:term "," mv:term ")" : term => `(do
  (roundedWork($tag,$N,$j,$mv))
  (roundedCommit($tag,$N,$j)))

private theorem executionComposable_roundedUpdate {C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P) (N j coeff src : ℕ) (off : IExp ℕ) :
    ExecutionComposable I
      (roundedUpdate(tag,N,j,coeff,src,off) : Builder P ι ℕ ℕ Unit) := by
  exact
    ExecutionComposable.bind (I := I)
      (a := ins (.un tag .neg ⟨8, 1⟩ ⟨coeff, IExp.var j⟩))
      (b := axpy tag ⟨8, 1⟩ src off 7 0 (IExp.const N))
      (executionComposable_single I
        (b := ins (.un tag .neg ⟨8, 1⟩ ⟨coeff, IExp.var j⟩)) (fun _ => rfl))
      (executionComposable_single I
        (b := axpy tag ⟨8, 1⟩ src off 7 0 (IExp.const N)) (fun _ => rfl))

private theorem executionComposable_roundedWork {C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P) (N j : ℕ)
    (hmv : ExecutionComposable I (mv j)) :
    ExecutionComposable I (roundedWork(tag,N,j,mv) : Builder P ι ℕ ℕ Unit) := by
  have cg : ExecutionComposable I (mv j) := hmv
  have cp := executionComposable_roundedUpdate I tag N j 3 5 0
  have cd : ExecutionComposable I (dot tag ⟨2, IExp.var j⟩ 1
      (IExp.const N * IExp.var j) 7 0 (IExp.const N)) :=
    executionComposable_single I (fun _ => rfl)
  have cz := executionComposable_roundedUpdate I tag N j 2 1 (IExp.const N * IExp.var j)
  have cn : ExecutionComposable I (nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (IExp.const N)) :=
    executionComposable_single I (fun _ => rfl)
  exact cg.bind (cp.bind (cd.bind (cz.bind cn)))

/-- Execute the actual Paige work prefix through the next norm. All intermediate vectors,
coefficient words and defects are conclusions. Previous coefficients may vanish, and the
zero-dimensional and zero-vector cases require no separate execution premise. -/
theorem exec_rounded_work (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store storedMatrix)
    (hj : j < q) (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A)
      (fun store => if storedMatrix then HoldsDecoded store dec tag 6 0 A else True)
      1 7 (IExp.const N * IExp.var t) 0 (mv t)) :
    ∃ (predot out : St P K (OpCount P ι)) (uv wv zv : Fin N → ℝ) (an bn : ℝ),
      exec I (roundedWork(tag,N,j,mv) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      exec I (nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (IExp.const N)).run predot = some out ∧
      StoreContext tag dec N q j A b v α β s predot.store storedMatrix ∧
      (∀ i : Fin N, ∃ w, predot.store.read tag 7 i = some w ∧ dec tag w = zv i) ∧
      StoreContext tag dec N q j A b v α β s out.store storedMatrix ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 7 i = some w ∧ dec tag w = zv i) ∧
      (∃ w, out.store.read tag 2 j = some w ∧ dec tag w = an) ∧
      (∃ w, out.store.read tag 3 (j + 1) = some w ∧ dec tag w = bn) ∧
      ‖WithLp.toLp 2 (A *ᵥ v (j + 1) - uv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * specNorm A *
          ‖WithLp.toLp 2 (v (j + 1))‖ ∧
      ‖WithLp.toLp 2 (uv - β j • v j - wv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 uv‖ + |β j| * ‖WithLp.toLp 2 (v j)‖) ∧
      |v (j + 1) ⬝ᵥ wv - an| ≤
        roundingFactor N (u tag) * ‖WithLp.toLp 2 (v (j + 1))‖ * ‖WithLp.toLp 2 wv‖ ∧
      ‖WithLp.toLp 2 (wv - an • v (j + 1) - zv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 wv‖ + |an| * ‖WithLp.toLp 2 (v (j + 1))‖) ∧
      0 ≤ bn ∧ (bn = 0 ↔ zv = 0) ∧
      |‖WithLp.toLp 2 zv‖ - bn| ≤
        roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 zv‖ := by
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N (h.nonneg trivial) hsmall
  have hn : (N : ℝ) * u tag < 1 := by
    have hu := h.nonneg (p := tag) trivial
    have hsucc := hwin.1
    push_cast at hsucc
    nlinarith
  obtain ⟨st₁, uv, hr₁, hs₁, hu, heu⟩ := exec_rounded_matvec I tag st hs (hmv j)
  obtain ⟨st₂, wv, hr₂, hs₂, hw, hew⟩ := exec_rounded_previous_update I h tag st₁ hs₁ uv hu hsmall
  obtain ⟨st₃, an, hr₃, hs₃, ha, hea, hf₃⟩ := exec_rounded_dot I h hz tag st₂ hs₂ hj wv hw hn
  have hw₃ (i : Fin N) : ∃ w, st₃.store.read tag 7 i = some w ∧ dec tag w = wv i := by
    rw [hf₃ tag 7 i (Or.inl (by omega))]
    exact hw i
  obtain ⟨st₄, zv, hr₄, hs₄, hzr, hez, hf₄⟩ :=
    exec_rounded_projection_update I h tag st₃ hs₃ an ha wv hw₃ hsmall
  have ha₄ : ∃ w, st₄.store.read tag 2 j = some w ∧ dec tag w = an := by
    rw [hf₄ tag 2 j (by omega) (by omega)]
    exact ha
  obtain ⟨out, bn, hr₅, hs₅, hb, hbn, hbzero, hnorm, hf₅⟩ :=
    exec_rounded_next_norm I h hz tag st₄ hs₄ hj zv hzr hsmall
  have haout : ∃ w, out.store.read tag 2 j = some w ∧ dec tag w = an := by
    rw [hf₅ tag 2 j (Or.inl (by omega))]
    exact ha₄
  have hzout (i : Fin N) : ∃ w, out.store.read tag 7 i = some w ∧ dec tag w = zv i := by
    rw [hf₅ tag 7 i (Or.inl (by omega))]
    exact hzr i
  refine ⟨st₄, out, uv, wv, zv, an, bn, ?_, hr₅, hs₄, hzr, hs₅, hzout, haout, hb,
    heu, hew, hea, hez,
    hbn, hbzero, hnorm⟩
  change exec I (do
    mv j
    (roundedUpdate(tag,N,j,3,5,0))
    dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N)
    (roundedUpdate(tag,N,j,2,1,IExp.const N * IExp.var j))
    nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (IExp.const N)).run st = some out
  have cp := executionComposable_roundedUpdate I tag N j 3 5 0
  have cz := executionComposable_roundedUpdate I tag N j 2 1 (IExp.const N * IExp.var j)
  rw [(hmv j).composable, hr₁, Option.bind_some,
    cp, hr₂, Option.bind_some,
    exec_run_bind I (b := dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j)
      7 0 (IExp.const N)) (fun _ => rfl), hr₃, Option.bind_some,
    cz, hr₄, Option.bind_some]
  exact hr₅

/-- **One actual rounded Paige step** of the registered stored-entry Lanczos tree.
Input-only scalar contracts, the initialized decoded workspace, a requested step and the
local precision window imply successful execution and all five local defects of the
existing finite-precision run model. Zero previous coefficients, zero dimension and a
terminal zero norm are allowed. Normalization executes after the actual previous-vector
copy; a zero norm writes a zero next column, and every nonzero next column has the stated
squared norm defect. No recurrence, desired local error or nonbreakdown assumption is input.
The kernel estimates retain the full ordered rounding factors [Higham2002, (3.5), (3.12)]. -/
theorem exec_rounded_step (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store storedMatrix)
    (hj : j < q) (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A)
      (fun store => if storedMatrix then HoldsDecoded store dec tag 6 0 A else True)
      1 7 (IExp.const N * IExp.var t) 0 (mv t)) :
    ∃ (out : St P K (OpCount P ι)) (uv wv zv : Fin N → ℝ) (an bn : ℝ) (vn : Fin N → ℝ),
      exec I (roundedStep(tag,N,j,mv) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag dec N q (j + 1) A b (Function.update v (j + 2) vn)
        (Function.update α (j + 1) an) (Function.update β (j + 1) bn) s out.store storedMatrix ∧
      ‖WithLp.toLp 2 (A *ᵥ v (j + 1) - uv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * specNorm A *
          ‖WithLp.toLp 2 (v (j + 1))‖ ∧
      ‖WithLp.toLp 2 (uv - β j • v j - wv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 uv‖ + |β j| * ‖WithLp.toLp 2 (v j)‖) ∧
      |v (j + 1) ⬝ᵥ wv - an| ≤
        lanczosImplementationRoundoffBound N (u tag) *
          ‖WithLp.toLp 2 (v (j + 1))‖ * ‖WithLp.toLp 2 wv‖ ∧
      ‖WithLp.toLp 2 (wv - an • v (j + 1) - zv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 wv‖ + |an| * ‖WithLp.toLp 2 (v (j + 1))‖) ∧
      ‖WithLp.toLp 2 (zv - bn • vn)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 zv‖ ∧
      0 ≤ bn ∧ (bn = 0 ↔ zv = 0) ∧ (bn = 0 → vn = 0) ∧
      (bn ≠ 0 → |‖WithLp.toLp 2 vn‖ ^ 2 - 1| ≤
        lanczosImplementationRoundoffBound N (u tag)) := by
  obtain ⟨predot, normed, uv, wv, zv, an, _, hwork, hnorm, hp, hzp, hsn, hzn, han, _,
      heu, hew, hea, hez, _⟩ := exec_rounded_work (hmv := hmv) I h hz tag st hs hj hsmall
  obtain ⟨out, vn, bn, hcommit, hctx, hbn, hzero, hvzero, hvunit, hres⟩ :=
    exec_rounded_commit I h hz hc tag predot normed hp hsn hj an han zv hzp hzn hnorm hsmall
  refine ⟨out, uv, wv, zv, an, bn, vn, ?_, hctx, heu, hew, ?_, hez, hres,
    hbn, hzero, hvzero, hvunit⟩
  · change exec I (do
      (roundedWork(tag,N,j,mv))
      (roundedCommit(tag,N,j))).run st = some out
    rw [executionComposable_roundedWork I tag N j (hmv j).composable, hwork, Option.bind_some]
    exact hcommit
  · exact hea.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (roundingFactor_le_lanczosImplementationRoundoffBound N (h.nonneg trivial) hsmall)
        (norm_nonneg _)) (norm_nonneg _))

end NLAlib.LanczosImplementation
