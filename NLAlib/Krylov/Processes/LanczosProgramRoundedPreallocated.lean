/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramRoundedPrefix
public import NLAlib.Krylov.Processes.LanczosProgramRoundedInitialization

/-!
# The actual dense rounded Lanczos body

The canonical ROM loop loads the matrix before the actual initializer and all requested
Paige steps. The active prefix is obtained from execution, including its first terminal
step. Whole-program scoping and resource analysis compose with this preallocated body.

## Main results

* `NLAlib.LanczosImplementation.exec_rounded_preallocated`: actual ROM, initialization and loop.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation Builder
open scoped Matrix

variable {P ι K : Type} [DecidableEq P] {u : P → ℝ} {dec : P → K → ℝ}

local macro "roundedInitialize(" tag:term "," N:term ")" : term => `(do
  ins (.lit $tag ⟨8, 0⟩ 0)
  ins (.lit $tag ⟨3, 0⟩ 0)
  forRange (.const $N) fun i => ins (.lit $tag ⟨5, .var i⟩ 0)
  nrm2 $tag ⟨4, 0⟩ 0 0 (.const $N)
  ifThenElse $tag .eq ⟨4, 0⟩ ⟨8, 0⟩
    (forRange (.const $N) fun i => ins (.lit $tag ⟨1, .var i⟩ 0))
    (do copyv $tag 0 0 1 0 (.const $N); rscl $tag ⟨4, 0⟩ 1 0 (.const $N)))

local macro "preallocatedStep(" tag:term "," N:term "," j:term ")" : term => `(do
  gemv $tag (IExp.const ($N)) (IExp.const ($N)) 6 0 1
    (IExp.const ($N) * IExp.var ($j)) 7 0
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

local macro "roundedBody(" tag:term "," N:term "," q:term ")" : term => `(do
  forRange ($N * $N) fun i => stmt (.rom $tag ⟨6, .var i⟩ (.var i))
  ins (.lit $tag ⟨8, 0⟩ 0)
  ins (.lit $tag ⟨3, 0⟩ 0)
  forRange $N fun i => ins (.lit $tag ⟨5, .var i⟩ 0)
  nrm2 $tag ⟨4, 0⟩ 0 0 $N
  ifThenElse $tag .eq ⟨4, 0⟩ ⟨8, 0⟩
    (forRange $N fun i => ins (.lit $tag ⟨1, .var i⟩ 0)) (do
      copyv $tag 0 0 1 0 $N
      rscl $tag ⟨4, 0⟩ 1 0 $N)
  forRange $q fun j => do
    gemv $tag $N $N 6 0 1 ($N * .var j) 7 0
    ins (.un $tag .neg ⟨8, 1⟩ ⟨3, .var j⟩)
    axpy $tag ⟨8, 1⟩ 5 0 7 0 $N
    dot $tag ⟨2, .var j⟩ 1 ($N * .var j) 7 0 $N
    ins (.un $tag .neg ⟨8, 1⟩ ⟨2, .var j⟩)
    axpy $tag ⟨8, 1⟩ 1 ($N * .var j) 7 0 $N
    nrm2 $tag ⟨3, .var j + 1⟩ 7 0 $N
    copyv $tag 1 ($N * .var j) 5 0 $N
    ifThenElse $tag .eq ⟨3, .var j + 1⟩ ⟨8, 0⟩
      (forRange $N fun i => ins (.lit $tag ⟨1, $N * (.var j + 1) + .var i⟩ 0)) (do
        copyv $tag 7 0 1 ($N * (.var j + 1)) $N
        rscl $tag ⟨3, .var j + 1⟩ 1 ($N * (.var j + 1)) $N))

/-- Execute the canonical preallocated dense body from actual input words and ROM entries.
The primitive scalar contract establishes the stored norm, normalized direction and active
LanczosRun. Zero dimension, zero input, zero requested steps and zero continuation are
included. Accumulated-error bounds impose their own horizon separately. -/
theorem exec_rounded_preallocated (I : Interp P ι K (OpCount P ι)) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (values : ℕ → K)
    (hshape : st.store.shape = workspaceShape tag N q)
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hrom : ∀ i < N * N, I.rom i = some (values i))
    (hdecode : ∀ i j : Fin N, dec tag (values (N * j + i)) = A i j)
    (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (s : ℝ) (v1 : Fin N → ℝ),
      exec I (roundedBody(tag,IExp.const N,IExp.const q) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      RoundedPrefix tag dec N q q A b v1
        (lanczosImplementationRoundoffBound N (u tag)) s out.store ∧
      0 ≤ s ∧ |‖WithLp.toLp 2 b‖ - s| ≤ roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 b‖ ∧
      (s = 0 ↔ b = 0) ∧ (s = 0 → v1 = 0) ∧
      (b ≠ 0 → |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ lanczosImplementationRoundoffBound N (u tag)) ∧
      ‖WithLp.toLp 2 (b - s • v1)‖ ≤ u tag * ‖WithLp.toLp 2 b‖ ∧
      ‖WithLp.toLp 2 (b - s • (‖WithLp.toLp 2 v1‖⁻¹ • v1))‖ ≤
        (2 * u tag + roundingFactor (N + 1) (u tag)) * ‖WithLp.toLp 2 b‖ := by
  have hcap : st.store.shape[6]? = some (tag, N * N) := by
    rw [hshape]
    simp [workspaceShape]
  obtain ⟨loaded, erom, shrom, reads, frame⟩ :=
    exec_forRange_rom I tag st (IExp.const N * IExp.const N) 6 values
      (by simpa only [IExp.eval_mul, IExp.eval_const] using hcap)
      (by simpa only [IExp.eval_mul, IExp.eval_const] using hrom)
  let mid : St P K (OpCount P ι) :=
    { st with store := loaded, cnt := st.cnt + (N * N) • I.charge (.rom tag) }
  have hmshape : mid.store.shape = workspaceShape tag N q := shrom.trans hshape
  have hmb (i : Fin N) : ∃ w, mid.store.read tag 0 i = some w ∧ dec tag w = b i := by
    change ∃ w, loaded.read tag 0 i = some w ∧ dec tag w = b i
    rw [frame tag 0 i (by omega)]
    exact hb i
  have hmA : HoldsDecoded mid.store dec tag 6 0 A := by
    intro i j
    refine ⟨values (N * j + i), ?_, hdecode i j⟩
    simpa only [zero_add, Nat.add_comm] using reads (N * j + i) (by
      change N * (j : ℕ) + (i : ℕ) < N * N
      calc
        N * (j : ℕ) + (i : ℕ) < N * (j : ℕ) + N := Nat.add_lt_add_left i.isLt _
        _ = N * ((j : ℕ) + 1) := by ring
        _ ≤ N * N := Nat.mul_le_mul_left N j.isLt)
  obtain ⟨initialized, s, v1, einit, ctx, hs, herr, hiff, hzero, hunit, hres, hdir⟩ :=
    exec_rounded_initialize I tag hsem hz hc mid N q A b hmshape hmb hmA hsmall
  have hzeroV : b = 0 → v1 = 0 := fun hb => hzero (hiff.mpr hb)
  obtain ⟨out, eloop, hprefix⟩ := exec_rounded_loop
      (hmv := isMatvecRoutine_dense I tag hsem hz N A hsmall) I hsem hz hc tag initialized
    (Or.inl ⟨Or.inl rfl, ctx⟩) hA hsmall hzeroV hunit
  refine ⟨out, s, v1, ?_, hprefix, hs, herr, hiff, hzero, hunit, hres, hdir⟩
  have erom' : exec I (forRange (IExp.const N * IExp.const N) fun i =>
      stmt (.rom tag ⟨6, .var i⟩ (.var i))).run st = some mid := by
    change exec I (.seq (.loop (IExp.const N * IExp.const N)
      (fun i => .seq (.rom tag ⟨6, .var i⟩ (.var i)) .skip)) .skip) st = _
    rw [exec_seq_skip]
    simpa only [IExp.eval_mul, IExp.eval_const] using erom
  have crom : ExecutionComposable I
      (forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨6, .var i⟩ (.var i))) :=
    executionComposable_single I (fun _ => rfl)
  change exec I (do
    forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨6, .var i⟩ (.var i))
    (roundedInitialize(tag,N))
    forRange (.const q) fun j => (preallocatedStep(tag,N,j))).run st = some out
  rw [crom, erom', Option.bind_some, executionComposable_rounded_initialize I tag N,
    einit, Option.bind_some]
  exact eloop

end NLAlib.LanczosImplementation
