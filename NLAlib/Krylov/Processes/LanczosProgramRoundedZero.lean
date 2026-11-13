/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramRoundedExecution

/-!
# Actual zero continuation of rounded Lanczos

When the current stored vector and previous off-diagonal coefficient are zero, all local
defect bounds have zero right-hand sides. The actual matvec, both updates, projection and
normalization therefore compute zero. The previous vector may still be nonzero on the
first continued step after a terminal norm; its coefficient is already zero.

## Main results

* `NLAlib.LanczosImplementation.exec_rounded_step_of_zero`: actual zero successor execution.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation Builder

variable {P ι K : Type} [DecidableEq P]
    {u : P → ℝ} {dec : P → K → ℝ} {storedMatrix : Bool}
    {mv : ℕ → Builder P ι ℕ ℕ Unit}

local macro "zeroStep(" tag:term "," N:term "," j:term "," mv:term ")" : term => `(do
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

/-- A zero current column and zero previous coefficient force the actual rounded Paige
step to compute zero intermediates, diagonal, next coefficient and next vector. The
successor decoded context records those zero outputs. The previous vector is unrestricted,
so this also covers the first continued step after a terminal computed norm. This follows
from the executed local defects and their exact zero right-hand sides, without constructing
or padding a finite-precision run. -/
theorem exec_rounded_step_of_zero (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store storedMatrix)
    (hj : j < q) (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hv : v (j + 1) = 0) (hβ : β j = 0)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A)
      (fun store => if storedMatrix then HoldsDecoded store dec tag 6 0 A else True)
      1 7 (IExp.const N * IExp.var t) 0 (mv t)) :
    ∃ out, exec I (zeroStep(tag,N,j,mv) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag dec N q (j + 1) A b (Function.update v (j + 2) 0)
        (Function.update α (j + 1) 0) (Function.update β (j + 1) 0) s out.store storedMatrix := by
  obtain ⟨out, uv, wv, zv, an, bn, vn, hr, hctx, heu, hew, hea, hez, _, _, hbzero,
      hvzero, _⟩ := exec_rounded_step (hmv := hmv) I h hz hc tag st hs hj hsmall
  have hu0 : uv = 0 := by
    have hn : ‖WithLp.toLp 2 uv‖ ≤ 0 := by simpa [hv] using heu
    exact (WithLp.toLp_eq_zero 2).mp (norm_le_zero_iff.mp hn)
  have hw0 : wv = 0 := by
    have hn : ‖WithLp.toLp 2 wv‖ ≤ 0 := by simpa [hu0, hβ] using hew
    exact (WithLp.toLp_eq_zero 2).mp (norm_le_zero_iff.mp hn)
  have ha0 : an = 0 := by simpa [hv] using hea
  have hz0 : zv = 0 := by
    have hn : ‖WithLp.toLp 2 zv‖ ≤ 0 := by simpa [hw0, ha0] using hez
    exact (WithLp.toLp_eq_zero 2).mp (norm_le_zero_iff.mp hn)
  have hb0 : bn = 0 := hbzero.mpr hz0
  have hn0 : vn = 0 := hvzero hb0
  subst an bn vn
  exact ⟨out, hr, hctx⟩

end NLAlib.LanczosImplementation
