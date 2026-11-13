/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramRoundedPreallocated
public import NLAlib.Krylov.Processes.LanczosProgramScope
public import NLAlib.Krylov.Processes.LanczosProgramStaticCost

/-!
# Rounded execution of the actual stored Lanczos program

Scope cleanup preserves the computed columns, coefficients, input norm and previous vector.
These are actual decoded buffer reads, with no numerical correctness premise in the cleanup
argument. The compiled execution theorem derives its context and existing run from primitive steps.

## Main results

* `NLAlib.LanczosImplementation.StoreContext.holdsDecoded_releaseWorkspace`:
  all six declared buffers survive actual workspace release.
* `NLAlib.LanczosImplementation.exec_rounded_compiled`: actual execution and decoded outputs.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation Computation.Builder
open scoped Matrix

variable {P ι K : Type} [DecidableEq P]

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


/-- Releasing the three Lanczos workspace buffers retains every decoded input, basis column,
coefficient, computed input norm and final previous vector. The matrix slot may hold the
dense matrix or be empty for the oracle variant. -/
theorem StoreContext.holdsDecoded_releaseWorkspace {tag : P} {dec : P → K → ℝ}
    {N q : ℕ} {storedMatrix : Bool} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ} {out : St P K (OpCount P ι)}
    (h : StoreContext tag dec N q q A b v α β s out.store storedMatrix) (width : ℕ) :
    let final := releaseWorkspace tag (if storedMatrix then N * N else 0) N width out
    final.store.shape =
      #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N)] ∧
    HoldsDecoded final.store dec tag 0 0 (fun i (_ : Fin 1) => b i) ∧
    HoldsDecoded final.store dec tag 1 0 (fun i (j : Fin (q + 1)) => v (j + 1) i) ∧
    HoldsDecoded final.store dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => α (j + 1)) ∧
    HoldsDecoded final.store dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => β j) ∧
    (∃ w, final.store.read tag 4 0 = some w ∧ dec tag w = s) ∧
    HoldsDecoded final.store dec tag 5 0 (fun i (_ : Fin 1) => v q i) := by
  have hs : out.store.size = 9 := by
    simpa [workspaceShape, Store.shape] using congrArg Array.size h.shape
  have hf := read_releaseWorkspace tag (if storedMatrix then N * N else 0) N width out hs
  refine ⟨shape_releaseWorkspace tag (if storedMatrix then N * N else 0) N q width out
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [workspaceShape] using h.shape
  · intro i j
    rw [hf tag 0 _ (by omega)]
    simpa using h.input i
  · intro i j
    rw [hf tag 1 _ (by omega)]
    simpa only [zero_add, Nat.add_comm] using h.basis j (Nat.le_of_lt_succ j.isLt) i
  · intro i j
    rw [hf tag 2 _ (by omega)]
    simpa using h.alpha i i.isLt
  · intro i j
    rw [hf tag 3 _ (by omega)]
    simpa using h.beta i (Nat.le_of_lt_succ i.isLt)
  · rw [hf tag 4 0 (by omega)]
    exact h.inputNorm
  · intro i j
    rw [hf tag 5 _ (by omega)]
    simpa using h.prev i

private theorem exec_compiled_eq_map (I : Interp P ι K (OpCount P ι)) (tag : P)
    (N q : ℕ) (st : St P K (OpCount P ι)) (hsize : st.store.size = 6) :
    (lanczosProg.compiled tag).exec I N ![q] st =
      (exec I (roundedBody(tag,IExp.const N,IExp.const q) : Builder P ι ℕ ℕ Unit).run
        (((st.allocate tag (N * N) (I.width tag)).allocate tag N (I.width tag)).allocate
          tag 2 (I.width tag))).map (releaseWorkspace tag (N * N) N (I.width tag)) := by
  rw [Prog.exec_eq_exec_toStmt, lanczosProg.toStmt_compiled]
  change exec I (.seq (.alloc tag (IExp.const N * IExp.const N) fun A =>
    .alloc tag (IExp.const N) fun work => .alloc tag 2 fun scalars => _) .skip) st = _
  rw [exec_seq_skip]
  simp only [exec_alloc, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat,
    St.allocate, hsize, Array.size_push, Nat.reduceAdd, Option.map_map]
  rfl

private theorem exec_compiled_outputs_of_prefix
    (I : Interp P ι K (OpCount P ι)) (tag : P) (N q : ℕ)
    (hc : IsUnitCharge I)
    (st workout : St P K (OpCount P ι)) (hsize : st.store.size = 6)
    (dec : P → K → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) (b v1 : Fin N → ℝ) (ε s : ℝ)
    (hvzero : b = 0 → v1 = 0)
    (hrun : exec I (roundedBody(tag,IExp.const N,IExp.const q) : Builder P ι ℕ ℕ Unit).run
      (((st.allocate tag (N * N) (I.width tag)).allocate tag N (I.width tag)).allocate
        tag 2 (I.width tag)) = some workout)
    (hpref : RoundedPrefix tag dec N q q A b v1 ε s workout.store) :
    ∃ out : St P K (OpCount P ι),
      (lanczosProg.compiled tag).exec I N ![q] st = some out ∧
      out.store.shape =
        #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N)] ∧
      HoldsDecoded out.store dec tag 0 0 (fun i (_ : Fin 1) => b i) ∧
      (∃ w, out.store.read tag 4 0 = some w ∧ dec tag w = s) ∧
      (StaticCost.mk (lanczosCount tag N q)
        (fun p => if p = tag then N ^ 2 + N + 3 else 0)
        ((N ^ 2 + N + 3) * I.width tag)).Bounds st out ∧
      (((q = 0 ∨ b = 0) ∧
        HoldsDecoded out.store dec tag 1 0
          (fun i (j : Fin (q + 1)) => (Function.update (0 : ℕ → Fin N → ℝ) 1 v1) (j + 1) i) ∧
        HoldsDecoded out.store dec tag 2 0 (0 : Matrix (Fin q) (Fin 1) ℝ) ∧
        HoldsDecoded out.store dec tag 3 0 (0 : Matrix (Fin (q + 1)) (Fin 1) ℝ) ∧
        HoldsDecoded out.store dec tag 5 0 (0 : Matrix (Fin N) (Fin 1) ℝ)) ∨
      ∃ (m : ℕ) (R : LanczosRun N m), 0 < m ∧ m ≤ q ∧ R.H = A ∧ R.ε = ε ∧ R.v 1 = v1 ∧
        HoldsDecoded out.store dec tag 1 0 (fun i (j : Fin (q + 1)) => R.v (j + 1) i) ∧
        HoldsDecoded out.store dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => R.α (j + 1)) ∧
        HoldsDecoded out.store dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => R.β j) ∧
        HoldsDecoded out.store dec tag 5 0 (fun i (_ : Fin 1) => R.v q i) ∧
        (∀ i, m + 1 < i → R.v i = 0) ∧
        (∀ i, m < i → R.α i = 0 ∧ R.β i = 0) ∧
        (R.β m = 0 → R.v (m + 1) = 0) ∧ (m < q → R.β m = 0)) := by
  let out := releaseWorkspace tag (N * N) N (I.width tag) workout
  have erun : (lanczosProg.compiled tag).exec I N ![q] st = some out := by
    rw [exec_compiled_eq_map I tag N q st hsize, hrun]
    rfl
  have hcost := lanczosProg.bounds_of_exec_eq_some I tag N q hc erun
  rcases hpref with ⟨hzero, hctx⟩ | ⟨m, R, hm, hH, hε, hv1, hctx, hv, hαβ, hlast, hstop⟩
  · obtain ⟨shape, input, basis, alpha, beta, norm, prev⟩ :=
      hctx.holdsDecoded_releaseWorkspace (I.width tag)
    have hvq : (Function.update (0 : ℕ → Fin N → ℝ) 1 v1) q = 0 := by
      rcases hzero with hq | hb
      · simp [hq]
      · simp [hvzero hb]
    refine ⟨out, erun, shape, input, norm, hcost, Or.inl ⟨hzero, basis, alpha, beta, ?_⟩⟩
    intro i j
    simpa only [hvq, Pi.zero_apply, Matrix.zero_apply, Bool.true_eq, ↓reduceIte, out]
      using prev i j
  · obtain ⟨shape, input, basis, alpha, beta, norm, prev⟩ :=
      hctx.holdsDecoded_releaseWorkspace (I.width tag)
    exact ⟨out, erun, shape, input, norm, hcost, Or.inr
      ⟨m, R, R.k_pos, hm, hH, hε, hv1, basis, alpha, beta, prev, hv, hαβ, hlast, hstop⟩⟩

/-- The actual stored Lanczos compiled tree executes under the unbounded relative-error
contract, with exact addition of zero. Let $N$ be the dimension and $q$ the requested budget.
The decoded matrix is symmetric. The local input budget is
shown by <!-- value lanczosImplementationRoundoffBound N u -->$\varepsilon=16(N+1)^2u$,
with $\varepsilon\le1/100$. No accumulated iteration-horizon condition is assumed.
The decoded input and matrix are the actual initial buffer/ROM words. All output columns,
coefficients, computed input norm and previous vector are retained after cleanup, together
with the original operation and workspace bounds. Zero input, dimension and budget are
explicit branches; a positive existing LanczosRun ends at the first zero beta. Its zero tail
is recorded separately. This does not assert an IEEE range contract or a matrix-function
postprocessing guarantee. -/
theorem exec_rounded_compiled {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (values : ℕ → K)
    (hshape : st.store.shape =
      #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hrom : ∀ i < N * N, I.rom i = some (values i))
    (hdecode : ∀ i j : Fin N, dec tag (values (N * j + i)) = A i j)
    (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (s : ℝ) (v1 : Fin N → ℝ),
      (lanczosProg.compiled tag).exec I N ![q] st = some out ∧
      out.store.shape =
        #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N)] ∧
      HoldsDecoded out.store dec tag 0 0 (fun i (_ : Fin 1) => b i) ∧
      (∃ w, out.store.read tag 4 0 = some w ∧ dec tag w = s) ∧
      (StaticCost.mk (lanczosCount tag N q)
        (fun p => if p = tag then N ^ 2 + N + 3 else 0)
        ((N ^ 2 + N + 3) * I.width tag)).Bounds st out ∧
      0 ≤ s ∧ |‖WithLp.toLp 2 b‖ - s| ≤
        roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 b‖ ∧
      (s = 0 ↔ b = 0) ∧ (s = 0 → v1 = 0) ∧
      (b ≠ 0 → |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤
        lanczosImplementationRoundoffBound N (u tag)) ∧
      ‖WithLp.toLp 2 (b - s • v1)‖ ≤ u tag * ‖WithLp.toLp 2 b‖ ∧
      ‖WithLp.toLp 2 (b - s • (‖WithLp.toLp 2 v1‖⁻¹ • v1))‖ ≤
        (2 * u tag + roundingFactor (N + 1) (u tag)) * ‖WithLp.toLp 2 b‖ ∧
      (((q = 0 ∨ b = 0) ∧
        HoldsDecoded out.store dec tag 1 0
          (fun i (j : Fin (q + 1)) => (Function.update (0 : ℕ → Fin N → ℝ) 1 v1) (j + 1) i) ∧
        HoldsDecoded out.store dec tag 2 0 (0 : Matrix (Fin q) (Fin 1) ℝ) ∧
        HoldsDecoded out.store dec tag 3 0 (0 : Matrix (Fin (q + 1)) (Fin 1) ℝ) ∧
        HoldsDecoded out.store dec tag 5 0 (0 : Matrix (Fin N) (Fin 1) ℝ)) ∨
      ∃ (m : ℕ) (R : LanczosRun N m), 0 < m ∧ m ≤ q ∧ R.H = A ∧
        R.ε = lanczosImplementationRoundoffBound N (u tag) ∧ R.v 1 = v1 ∧
        HoldsDecoded out.store dec tag 1 0 (fun i (j : Fin (q + 1)) => R.v (j + 1) i) ∧
        HoldsDecoded out.store dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => R.α (j + 1)) ∧
        HoldsDecoded out.store dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => R.β j) ∧
        HoldsDecoded out.store dec tag 5 0 (fun i (_ : Fin 1) => R.v q i) ∧
        (∀ i, m + 1 < i → R.v i = 0) ∧
        (∀ i, m < i → R.α i = 0 ∧ R.β i = 0) ∧
        (R.β m = 0 → R.v (m + 1) = 0) ∧ (m < q → R.β m = 0)) := by
  let pre := (((st.allocate tag (N * N) (I.width tag)).allocate tag N (I.width tag)).allocate
    tag 2 (I.width tag))
  have hsize : st.store.size = 6 := by
    simpa [Store.shape] using congrArg Array.size hshape
  have hpreshape : pre.store.shape = workspaceShape tag N q := by
    simp only [pre, St.allocate, Store.shape, Array.map_push, Array.size_replicate]
    change ((st.store.shape.push (tag, N * N)).push (tag, N)).push (tag, 2) = _
    rw [hshape]
    rfl
  have hbpre : ∀ i : Fin N, ∃ w, pre.store.read tag 0 i = some w ∧ dec tag w = b i := by
    intro i
    obtain ⟨w, hw, hd⟩ := hb i
    refine ⟨w, ?_, hd⟩
    change Store.read (((st.store.push _).push _).push _) tag 0 i = some w
    rw [Store.read_push_of_lt (by simp [hsize]), Store.read_push_of_lt (by simp [hsize]),
      Store.read_push_of_lt (by omega)]
    exact hw
  obtain ⟨workout, s, v1, hrun, hpref, hs, hnorm, hs0, hv0, hunit, hres, hdir⟩ :=
    exec_rounded_preallocated I tag hsem hz hc pre N q A b values hpreshape hbpre
      hrom hdecode hA hsmall
  obtain ⟨out, erun, shape, input, norm, cost, post⟩ :=
    exec_compiled_outputs_of_prefix I tag N q hc st workout hsize dec A b v1
      (lanczosImplementationRoundoffBound N (u tag)) s (fun hb0 => hv0 (hs0.mpr hb0)) hrun hpref
  exact ⟨out, s, v1, erun, shape, input, norm, cost, hs, hnorm, hs0, hv0, hunit, hres, hdir, post⟩

end NLAlib.LanczosImplementation
