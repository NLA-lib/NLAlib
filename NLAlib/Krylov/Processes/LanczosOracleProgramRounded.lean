/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramRounded
public import NLAlib.Krylov.Processes.LanczosOracleStaticCost
public import NLAlib.Krylov.Processes.LanczosProgramScope
public import NLAlib.Krylov.Processes.LanczosProgramStaticCost

/-!
# Rounded execution of the actual oracle Lanczos program

Scope cleanup preserves the computed columns, coefficients, input norm and previous vector.
These are actual decoded buffer reads, with no numerical correctness premise in the cleanup
argument. The compiled execution theorem derives its context and existing run from primitive steps.

Its scalar semantics and oracle contracts both require global success; finite-word range
obligations remain separate. The tree calls the oracle at each requested step, including zero
continuation after the active prefix ends. The additional scratch is linear in the dimension;
the declared output basis itself occupies $N(q+1)$ words. Polynomial backward-error corollaries
may require stronger horizons than this execution theorem.

## Main results

* `NLAlib.LanczosOracleImplementation.exec_rounded_compiled`: actual execution and decoded outputs.
-/

@[expose] public section

namespace NLAlib.LanczosOracleImplementation

open Computation Computation.Builder LanczosImplementation
open scoped Matrix

variable {P ι K : Type} [DecidableEq P]

local macro "roundedBody(" tag:term "," o:term "," N:term "," q:term ")" : term => `(do
  ins (.lit $tag ⟨8, 0⟩ 0)
  ins (.lit $tag ⟨3, 0⟩ 0)
  forRange $N fun i => ins (.lit $tag ⟨5, .var i⟩ 0)
  nrm2 $tag ⟨4, 0⟩ 0 0 $N
  ifThenElse $tag .eq ⟨4, 0⟩ ⟨8, 0⟩
    (forRange $N fun i => ins (.lit $tag ⟨1, .var i⟩ 0)) (do
      copyv $tag 0 0 1 0 $N
      rscl $tag ⟨4, 0⟩ 1 0 $N)
  forRange $q fun j => do
    stmt (.apply $o $tag 7 0 1 ($N * .var j) 1)
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


/-- The oracle body assembles the shared initializer and backend-parametric Paige loop.
No matrix entries, initialized trajectory or successful future execution are assumed. -/
theorem exec_rounded_preallocated {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (o : ι)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ)
    (hshape : st.store.shape = workspaceShape tag N q false)
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hmv : IsMatvecErr I o dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A))
    (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (s : ℝ) (v1 : Fin N → ℝ),
      exec I (roundedBody(tag,o,IExp.const N,IExp.const q) :
        Builder P ι ℕ ℕ Unit).run st = some out ∧
      RoundedPrefix tag dec N q q A b v1
        (lanczosImplementationRoundoffBound N (u tag)) s out.store false ∧
      0 ≤ s ∧ |‖WithLp.toLp 2 b‖ - s| ≤ roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 b‖ ∧
      (s = 0 ↔ b = 0) ∧ (s = 0 → v1 = 0) ∧
      (b ≠ 0 → |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ lanczosImplementationRoundoffBound N (u tag)) ∧
      ‖WithLp.toLp 2 (b - s • v1)‖ ≤ u tag * ‖WithLp.toLp 2 b‖ ∧
      ‖WithLp.toLp 2 (b - s • (‖WithLp.toLp 2 v1‖⁻¹ • v1))‖ ≤
        (2 * u tag + roundingFactor (N + 1) (u tag)) * ‖WithLp.toLp 2 b‖ := by
  obtain ⟨initialized, s, v1, einit, ctx, hs, herr, hiff, hzero, hunit, hres, hdir⟩ :=
    exec_rounded_initialize I tag hsem hz hc st N q A b hshape hb trivial hsmall
  have hzeroV : b = 0 → v1 = 0 := fun hb => hzero (hiff.mpr hb)
  obtain ⟨out, eloop, hprefix⟩ := exec_rounded_loop
    (hmv := fun j => hmv.isMatvecRoutine 1 7 (IExp.const N * IExp.var j) 0 (by omega))
    I hsem hz hc tag initialized (Or.inl ⟨Or.inl rfl, ctx⟩) hA hsmall hzeroV hunit
  refine ⟨out, s, v1, ?_, hprefix, hs, herr, hiff, hzero, hunit, hres, hdir⟩
  change exec I ((do
    ins (.lit tag ⟨8, 0⟩ 0)
    ins (.lit tag ⟨3, 0⟩ 0)
    forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
    nrm2 tag ⟨4, 0⟩ 0 0 (.const N)
    ifThenElse tag .eq ⟨4, 0⟩ ⟨8, 0⟩
      (forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0))
      (do copyv tag 0 0 1 0 (.const N); rscl tag ⟨4, 0⟩ 1 0 (.const N))) >>=
    fun _ => _).run st = some out
  rw [executionComposable_rounded_initialize I tag N, einit, Option.bind_some]
  exact eloop

private theorem exec_lanczosOracleProg_compiled_eq_map
    (I : Interp P ι K (OpCount P ι)) (tag : P) (o : ι)
    (N q : ℕ) (st : St P K (OpCount P ι)) (hsize : st.store.size = 6) :
    (lanczosOracleProg.compiled tag o).exec I N ![q] st =
      (exec I (roundedBody(tag,o,IExp.const N,IExp.const q) : Builder P ι ℕ ℕ Unit).run
        (((st.allocate tag 0 (I.width tag)).allocate tag N (I.width tag)).allocate
          tag 2 (I.width tag))).map (releaseWorkspace tag 0 N (I.width tag)) := by
  rw [Prog.exec_eq_exec_toStmt, lanczosOracleProg.toStmt_compiled]
  change exec I (.seq (.alloc tag (0 : IExp ℕ) fun A =>
    .alloc tag (IExp.const N) fun work => .alloc tag 2 fun scalars => _) .skip) st = _
  rw [exec_seq_skip]
  simp only [exec_alloc, IExp.eval_const, IExp.eval_ofNat,
    St.allocate, hsize, Array.size_push, Nat.reduceAdd, Option.map_map]
  rfl

private theorem exec_lanczosOracleProg_compiled_outputs_of_prefix
    (I : Interp P ι K (OpCount P ι)) (tag : P) (o : ι) (N q : ℕ)
    (hc : IsUnitCharge I)
    (st workout : St P K (OpCount P ι)) (hsize : st.store.size = 6)
    (dec : P → K → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) (b v1 : Fin N → ℝ) (ε s : ℝ)
    (hvzero : b = 0 → v1 = 0)
    (hrun : exec I (roundedBody(tag,o,IExp.const N,IExp.const q) : Builder P ι ℕ ℕ Unit).run
      (((st.allocate tag 0 (I.width tag)).allocate tag N (I.width tag)).allocate
        tag 2 (I.width tag)) = some workout)
    (hpref : RoundedPrefix tag dec N q q A b v1 ε s workout.store false) :
    ∃ out : St P K (OpCount P ι),
      (lanczosOracleProg.compiled tag o).exec I N ![q] st = some out ∧
      out.store.shape =
        #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N)] ∧
      HoldsDecoded out.store dec tag 0 0 (fun i (_ : Fin 1) => b i) ∧
      (∃ w, out.store.read tag 4 0 = some w ∧ dec tag w = s) ∧
      (StaticCost.mk (lanczosOracleCount tag o N q)
        (fun p => if p = tag then N + 3 else 0)
        ((N + 3) * I.width tag)).Bounds st out ∧
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
  let out := releaseWorkspace tag 0 N (I.width tag) workout
  have erun : (lanczosOracleProg.compiled tag o).exec I N ![q] st = some out := by
    rw [exec_lanczosOracleProg_compiled_eq_map I tag o N q st hsize, hrun]
    rfl
  have hcost := lanczosOracleProg.bounds_of_exec_eq_some I tag o N q hc erun
  rcases hpref with ⟨hzero, hctx⟩ | ⟨m, R, hm, hH, hε, hv1, hctx, hv, hαβ, hlast, hstop⟩
  · obtain ⟨shape, input, basis, alpha, beta, norm, prev⟩ :=
      hctx.holdsDecoded_releaseWorkspace (I.width tag)
    have hvq : (Function.update (0 : ℕ → Fin N → ℝ) 1 v1) q = 0 := by
      rcases hzero with hq | hb
      · simp [hq]
      · simp [hvzero hb]
    refine ⟨out, erun, shape, input, norm, hcost, Or.inl ⟨hzero, basis, alpha, beta, ?_⟩⟩
    intro i j
    simpa only [hvq, Pi.zero_apply, Matrix.zero_apply, Bool.false_eq_true, ↓reduceIte, out]
      using prev i j
  · obtain ⟨shape, input, basis, alpha, beta, norm, prev⟩ :=
      hctx.holdsDecoded_releaseWorkspace (I.width tag)
    exact ⟨out, erun, shape, input, norm, hcost, Or.inr
      ⟨m, R, R.k_pos, hm, hH, hε, hv1, basis, alpha, beta, prev, hv, hαβ, hlast, hstop⟩⟩

/-- The actual oracle Lanczos tree executes under an unbounded scalar relative-error
contract at unit roundoff $u$, exact addition of zero, and an independently specified oracle
error $\eta\|\mathbf{A}\|_2\|\mathbf{x}\|_2$. Choose an analysis allowance $v\ge u$ with
$\eta\le\varepsilon$, where the local budget is
shown by <!-- value lanczosImplementationRoundoffBound N v -->$\varepsilon=16(N+1)^2v$,
and assume $\varepsilon\le1/100$ and symmetric decoded $\mathbf{A}$.
No accumulated iteration-horizon condition is assumed. All six declared output buffers
are tied to the actual execution and active LanczosRun after cleanup. The returned input-norm
and direction estimates use the chosen allowance $v$. Zero dimension, zero input, zero
budget and terminal zero continuation are included. Backend storage and arithmetic are
excluded from the oracle resource bounds. -/
theorem exec_rounded_compiled {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (o : ι)
    (v : P → ℝ) (hv : ∀ p, u p ≤ v p) (η : ℝ)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ)
    (hshape : st.store.shape =
      #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hmv : IsMatvecErr I o dec tag A (η * specNorm A))
    (hη : η ≤ lanczosImplementationRoundoffBound N (v tag))
    (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (v tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (s : ℝ) (v1 : Fin N → ℝ),
      (lanczosOracleProg.compiled tag o).exec I N ![q] st = some out ∧
      out.store.shape =
        #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N)] ∧
      HoldsDecoded out.store dec tag 0 0 (fun i (_ : Fin 1) => b i) ∧
      (∃ w, out.store.read tag 4 0 = some w ∧ dec tag w = s) ∧
      (StaticCost.mk (lanczosOracleCount tag o N q)
        (fun p => if p = tag then N + 3 else 0)
        ((N + 3) * I.width tag)).Bounds st out ∧
      0 ≤ s ∧ |‖WithLp.toLp 2 b‖ - s| ≤
        roundingFactor (N + 1) (v tag) * ‖WithLp.toLp 2 b‖ ∧
      (s = 0 ↔ b = 0) ∧ (s = 0 → v1 = 0) ∧
      (b ≠ 0 → |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤
        lanczosImplementationRoundoffBound N (v tag)) ∧
      ‖WithLp.toLp 2 (b - s • v1)‖ ≤ v tag * ‖WithLp.toLp 2 b‖ ∧
      ‖WithLp.toLp 2 (b - s • (‖WithLp.toLp 2 v1‖⁻¹ • v1))‖ ≤
        (2 * v tag + roundingFactor (N + 1) (v tag)) * ‖WithLp.toLp 2 b‖ ∧
      (((q = 0 ∨ b = 0) ∧
        HoldsDecoded out.store dec tag 1 0
          (fun i (j : Fin (q + 1)) => (Function.update (0 : ℕ → Fin N → ℝ) 1 v1) (j + 1) i) ∧
        HoldsDecoded out.store dec tag 2 0 (0 : Matrix (Fin q) (Fin 1) ℝ) ∧
        HoldsDecoded out.store dec tag 3 0 (0 : Matrix (Fin (q + 1)) (Fin 1) ℝ) ∧
        HoldsDecoded out.store dec tag 5 0 (0 : Matrix (Fin N) (Fin 1) ℝ)) ∨
      ∃ (m : ℕ) (R : LanczosRun N m), 0 < m ∧ m ≤ q ∧ R.H = A ∧
        R.ε = lanczosImplementationRoundoffBound N (v tag) ∧ R.v 1 = v1 ∧
        HoldsDecoded out.store dec tag 1 0 (fun i (j : Fin (q + 1)) => R.v (j + 1) i) ∧
        HoldsDecoded out.store dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => R.α (j + 1)) ∧
        HoldsDecoded out.store dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => R.β j) ∧
        HoldsDecoded out.store dec tag 5 0 (fun i (_ : Fin 1) => R.v q i) ∧
        (∀ i, m + 1 < i → R.v i = 0) ∧
        (∀ i, m < i → R.α i = 0 ∧ R.β i = 0) ∧
        (R.β m = 0 → R.v (m + 1) = 0) ∧ (m < q → R.β m = 0)) := by
  have hsemv := hsem.mono hv
  have hmvv := hmv.mono (mul_le_mul_of_nonneg_right hη (specNorm_nonneg A))
  let pre := (((st.allocate tag 0 (I.width tag)).allocate tag N (I.width tag)).allocate
    tag 2 (I.width tag))
  have hsize : st.store.size = 6 := by
    simpa [Store.shape] using congrArg Array.size hshape
  have hpreshape : pre.store.shape = workspaceShape tag N q false := by
    simp only [pre, St.allocate, Store.shape, Array.map_push, Array.size_replicate]
    change ((st.store.shape.push (tag, 0)).push (tag, N)).push (tag, 2) = _
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
    exec_rounded_preallocated I tag o hsemv hz hc pre N q A b hpreshape hbpre
      hmvv hA hsmall
  obtain ⟨out, erun, shape, input, norm, cost, post⟩ :=
    exec_lanczosOracleProg_compiled_outputs_of_prefix I tag o N q hc st workout hsize dec A b v1
      (lanczosImplementationRoundoffBound N (v tag)) s (fun hb0 => hv0 (hs0.mpr hb0)) hrun hpref
  exact ⟨out, s, v1, erun, shape, input, norm, cost, hs, hnorm, hs0, hv0, hunit, hres, hdir, post⟩

end NLAlib.LanczosOracleImplementation
