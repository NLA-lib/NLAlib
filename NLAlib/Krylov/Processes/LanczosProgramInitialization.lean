/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramCounts
public import NLAlib.Computation.BLAS.GuardedNormalization
public import NLAlib.Computation.ScalarFrames

/-!
# Exact initialization of the approved concrete Lanczos tree

The actual initializer writes its comparison zero and initial beta, zeros the previous
vector, computes the norm of the unchanged input, then copies and divides into the first
basis column only when the norm is nonzero. The operation order is the approved program's
order. These local executions feed the complete stored-entry realization.

## Main results

* `NLAlib.LanczosImplementation.exec_initialize_zeros`: actual scalar and previous-vector setup.
* `NLAlib.LanczosImplementation.exec_initialize_zeros_of_lit_eq_some`: shared literal-only prefix.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation Computation.Builder

variable {P ι : Type} [DecidableEq P]

/-- The two scalar-zero literals and previous-vector fill execute in the canonical order
whenever the zero literal succeeds. No arithmetic accuracy, decoded values or global range
contract is used. Other cells and all non-store usage fields except the literal count are
preserved. The vector length and requested budget may be zero. -/
theorem exec_initialize_zeros_of_lit_eq_some {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P)
    (zero : K) (hz : I.sem.lit tag 0 = some zero) (N q : ℕ) (st : St P K C)
    (h3 : st.store.shape[3]? = some (tag, q + 1))
    (h5 : st.store.shape[5]? = some (tag, N))
    (h8 : st.store.shape[8]? = some (tag, 2)) :
    ∃ out, exec I (do
        ins (.lit tag ⟨8, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag 8 0 = some zero ∧ out.store.read tag 3 0 = some zero ∧
      (∀ i : Fin N, out.store.read tag 5 i = some zero) ∧
      (∀ p buf idx, buf ≠ 5 → (buf ≠ 3 ∨ idx ≠ 0) → (buf ≠ 8 ∨ idx ≠ 0) →
        out.store.read p buf idx = st.store.read p buf idx) ∧
      out = { st with
        store := out.store
        cnt := st.cnt + I.charge (.lit tag) + I.charge (.lit tag) +
          N • I.charge (.lit tag) } := by
  obtain ⟨s0, _, e0, sh0, r0, f0⟩ := exec_scalar_lit I tag st ⟨8, 0⟩ 0 zero hz
    ⟨2, h8, by norm_num⟩
  let st1 := { st with store := s0, cnt := st.cnt + I.charge (.lit tag) }
  obtain ⟨s1, _, e1, sh1, r1, f1⟩ := exec_scalar_lit I tag st1 ⟨3, 0⟩ 0 zero hz
    ⟨q + 1, sh0 ▸ h3, by simp only [IExp.eval_ofNat]; omega⟩
  let st2 := { st1 with store := s1, cnt := st1.cnt + I.charge (.lit tag) }
  obtain ⟨s2, e2, sh2, r2, f2⟩ := exec_forRange_literal_zero_var I tag zero hz st2
    (.const N) 5 (fun i hi => ⟨N, (sh1.trans sh0) ▸ h5, hi⟩)
  let out := { st2 with store := s2, cnt := st2.cnt + N • I.charge (.lit tag) }
  refine ⟨out, ?_, sh2.trans (sh1.trans sh0), ?_, ?_, ?_, ?_, rfl⟩
  · rw [exec_run_bind I (b := ins (.lit tag ⟨8, 0⟩ 0)) (fun _ => rfl), e0, Option.bind_some,
      exec_run_bind I (b := ins (.lit tag ⟨3, 0⟩ 0)) (fun _ => rfl), e1, Option.bind_some]
    exact e2
  · exact (f2 tag 8 0 (Or.inr (Or.inl (by norm_num)))).trans
      ((f1 tag 8 0 (Or.inr (Or.inl (by norm_num)))).trans r0)
  · exact (f2 tag 3 0 (Or.inr (Or.inl (by norm_num)))).trans r1
  · intro i
    exact r2 i i.isLt
  · intro p buf idx h5 h3 h8
    rw [f2 p buf idx (Or.inr (Or.inl h5)), f1 p buf idx (Or.inr h3)]
    exact f0 p buf idx (Or.inr h8)

/-- Execute the literal prefix in the fixed nine-buffer layout. The actual scalar zero,
initial beta and previous vector are initialized; the other buffers remain unchanged.
All non-store fields are retained except the exact literal count. -/
theorem exec_initialize_zeros_of_workspace (storedMatrix : Bool)
    (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I)
    (tag : P) (N q : ℕ) (st : St P ℝ (OpCount P ι))
    (hshape : st.store.shape = workspaceShape tag N q storedMatrix) :
    ∃ out, exec I (do
        ins (.lit tag ⟨8, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)).run st = some out ∧
      out = { st with
        store := out.store
        cnt := st.cnt + (N + 2) • Finsupp.single (.lit tag) 1 } ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag 8 0 = some 0 ∧ out.store.read tag 3 0 = some 0 ∧
      (∀ i < N, out.store.read tag 5 i = some 0) ∧
      ∀ p b i, b ≠ 3 → b ≠ 5 → b ≠ 8 →
        out.store.read p b i = st.store.read p b i := by
  have hlit : I.sem.lit tag 0 = some (0 : ℝ) := by simp [hI, exactSem]
  obtain ⟨out, he, sh, r8, r3, r5, frame, hout⟩ :=
    exec_initialize_zeros_of_lit_eq_some I tag 0 hlit N q st
      (by rw [hshape]; rfl) (by rw [hshape]; rfl) (by rw [hshape]; rfl)
  refine ⟨out, he, ?_, sh, r8, r3, fun i hi => r5 ⟨i, hi⟩, ?_⟩
  · have hc' : st.cnt + I.charge (.lit tag) + I.charge (.lit tag) +
        N • I.charge (.lit tag) = st.cnt + (N + 2) • Finsupp.single (.lit tag) 1 := by
      simp only [hc.charge_eq, add_nsmul, two_nsmul]
      abel
    simpa only [hc'] using hout
  · intro p b i h3 h5 h8
    exact frame p b i h5 (Or.inl h3) (Or.inl h8)

/-- The literal prefix consists only of certified single-statement builders, so it may be
composed with its actual continuation without introducing a scope or changing allocation. -/
theorem executionComposable_initialize_zeros (I : Interp P ι ℝ (OpCount P ι))
    (tag : P) (N : ℕ) : Computation.ExecutionComposable I (do
      ins (.lit tag ⟨8, 0⟩ 0)
      ins (.lit tag ⟨3, 0⟩ 0)
      forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)) :=
  (Computation.executionComposable_single I (b := ins (.lit tag ⟨8, 0⟩ 0))
    (fun _ => rfl)).bind
      ((Computation.executionComposable_single I (b := ins (.lit tag ⟨3, 0⟩ 0))
        (fun _ => rfl)).bind (Computation.executionComposable_single I
          (b := forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)) (fun _ => rfl)))

/-- The actual norm prefix follows literal initialization with `nrm2` on the unchanged input.
It retains all other buffers, gives the exact stored norm, and accounts for its actual square
root and scratch memory. This holds for zero input and zero dimension. -/
theorem exec_initialize_norm_of_workspace (storedMatrix : Bool)
    (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I)
    (tag : P) (N q : ℕ) (st : St P ℝ (OpCount P ι)) (b : Fin N → ℝ)
    (hshape : st.store.shape = workspaceShape tag N q storedMatrix)
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i)) :
    ∃ out, exec I (do
        ins (.lit tag ⟨8, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
        nrm2 tag ⟨4, 0⟩ 0 0 (.const N)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
      out.store.read tag 8 0 = some 0 ∧ out.store.read tag 3 0 = some 0 ∧
      (∀ i < N, out.store.read tag 5 i = some 0) ∧
      (∀ p d i, d ≠ 3 → d ≠ 5 → d ≠ 8 → d ≠ 4 →
        out.store.read p d i = st.store.read p d i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + (N + 2) • Finsupp.single (.lit tag) 1 +
        (N • (Finsupp.single (.un tag .conj) 1 + Finsupp.single (.bin tag .mul) 1 +
          Finsupp.single (.bin tag .add) 1) + Finsupp.single (.lit tag) 1 +
            Finsupp.single (.un tag .sqrt) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  obtain ⟨setupState, hprefix, hpstate, hpshape, hpzero, hpbeta, hpprev, hpframe⟩ :=
    exec_initialize_zeros_of_workspace storedMatrix I hI hc tag N q st hshape
  let xs : ℕ → ℝ := fun i => if hi : i < N then b ⟨i, hi⟩ else 0
  have hvec : (fun i : Fin N => xs i) = b := by ext i; exact dif_pos i.2
  have hinput : ∀ i < N, setupState.store.read tag 0 (0 + i) = some (xs i) := by
    intro i hi
    rw [zero_add, hpframe tag 0 i (by decide) (by decide) (by decide)]
    simpa only [xs, dif_pos hi] using hb ⟨i, hi⟩
  obtain ⟨s, hs⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) (0 : ℝ)
    (show setupState.store.shape[4]? = some (tag, 1) by rw [hpshape, hshape]; rfl) (by decide)
  obtain ⟨out, hnorm, houtshape, houtnorm, houtframe, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_nrm2_frame I hI hc tag setupState ⟨4, 0⟩ 0 0 (.const N) xs hinput
      (by decide) ⟨0, s, hs⟩
  refine ⟨out, ?_, houtshape.trans hpshape, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change exec I ((do
        ins (.lit tag ⟨8, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)) >>=
          fun _ => nrm2 tag ⟨4, 0⟩ 0 0 (.const N)).run st = some out
    rw [executionComposable_initialize_zeros I tag N, hprefix, Option.bind_some]
    exact hnorm
  · change out.store.read tag 4 0 = some ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at houtnorm
    rw [hvec] at houtnorm
    exact houtnorm
  · rw [houtframe tag 8 0 (Or.inl (by decide))]
    exact hpzero
  · rw [houtframe tag 3 0 (Or.inl (by decide))]
    exact hpbeta
  · intro i hi
    rw [houtframe tag 5 i (Or.inl (by decide))]
    exact hpprev i hi
  · intro p d i hd₃ hd₅ hd₈ hd₄
    exact (houtframe p d i (Or.inl hd₄)).trans (hpframe p d i hd₃ hd₅ hd₈)
  · rw [hpos, hpstate]
  · rw [hcur, hpstate]
  · rw [hcurW, hpstate]
  · rw [hcnt, hpstate]
    rfl
  · rw [hpeak, hpstate]
  · rw [hpeakW, hpstate]

/-- Flat initialized-buffer facts give the exact zero-step loop invariant. This constructor
has no execution conclusion: each read is supplied by the actual initialization proof. -/
theorem State.of_initial_reads_of_workspace (storedMatrix : Bool)
    (tag : P) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (st : St P ℝ (OpCount P ι))
    (hshape : st.store.shape = workspaceShape tag N q storedMatrix)
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hA : if storedMatrix then Holds st.store tag 6 0 A else True)
    (hV : ∀ i : Fin N, st.store.read tag 1 i = some (‖WithLp.toLp 2 b‖⁻¹ * b i))
    (hbeta : st.store.read tag 3 0 = some 0)
    (hnorm : st.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖)
    (hprev : ∀ i : Fin N, st.store.read tag 5 i = some 0)
    (hzero : st.store.read tag 8 0 = some 0) : State tag N q 0 A b st storedMatrix := by
  refine ⟨hshape, hb, hA, ?_, ?_, ?_, hnorm, ?_, hzero⟩
  · intro c hc i
    have hc0 : c = 0 := by omega
    subst c
    simpa only [Nat.mul_zero, zero_add, lanczosState, Pi.smul_apply, smul_eq_mul,
      RCLike.ofReal_real_eq_id, id] using hV i
  · intro c hc
    omega
  · intro c hc
    have hc0 : c = 0 := by omega
    subst c
    exact hbeta
  · intro i
    exact hprev i

/-- The actual input-norm prefix has a composition certificate derived only from its
single-statement instructions and kernels. -/
theorem executionComposable_initialize_norm (I : Interp P ι ℝ (OpCount P ι))
    (tag : P) (N : ℕ) : Computation.ExecutionComposable I (do
      ins (.lit tag ⟨8, 0⟩ 0)
      ins (.lit tag ⟨3, 0⟩ 0)
      forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
      nrm2 tag ⟨4, 0⟩ 0 0 (.const N)) :=
  (executionComposable_initialize_zeros I tag N).bind
    (Computation.executionComposable_single I
      (b := nrm2 tag ⟨4, 0⟩ 0 0 (.const N)) (fun _ => rfl))

/-- The actual full initializer of the approved program produces the zero-step stored
Lanczos recurrence state. The input norm is taken from the input buffer before copying
and dividing into the basis; zero input and zero dimension use the explicit zero branch.
Its counts and scratch peak are the compositional bounds used in the approved target. -/
theorem exec_initialize_of_workspace (storedMatrix : Bool)
    (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I)
    (tag : P) (N q : ℕ) (st : St P ℝ (OpCount P ι))
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hshape : st.store.shape = workspaceShape tag N q storedMatrix)
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hA : if storedMatrix then Holds st.store tag 6 0 A else True) :
    ∃ out, exec I (do
        ins (.lit tag ⟨8, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
        nrm2 tag ⟨4, 0⟩ 0 0 (.const N)
        ifThenElse tag .eq ⟨4, 0⟩ ⟨8, 0⟩
          (forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)) (do
            copyv tag 0 0 1 0 (.const N)
            rscl tag ⟨4, 0⟩ 1 0 (.const N))).run st = some out ∧
      State tag N q 0 A b out storedMatrix ∧ out.pos = st.pos ∧ out.cur = st.cur ∧
      out.curW = st.curW ∧
      out.cnt ≤ st.cnt + initializationCount tag N ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  obtain ⟨mid, hnorm, hsh, hn, hz, hβ, hp, hf, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_initialize_norm_of_workspace storedMatrix I hI hc tag N q st b hshape hb
  let xs : ℕ → ℝ := fun i => if hi : i < N then b ⟨i, hi⟩ else 0
  have hvec : (fun i : Fin N => xs i) = b := by ext i; exact dif_pos i.2
  have hx : ∀ i < N, mid.store.read tag 0 (0 + i) = some (xs i) := by
    intro i hi
    rw [zero_add, hf tag 0 i (by decide) (by decide) (by decide) (by decide)]
    simpa only [xs, dif_pos hi] using hb ⟨i, hi⟩
  obtain ⟨out, hbranch, hs', hread, hframe, hpos', hcur', hcurW', hcnt', hpeak', hpeakW'⟩ :=
    exec_normalize_branch I hI hc tag mid ![0, 1, 4, 8] (by decide)
      (.const N) 0 0 0 0 xs hx (by
        change mid.store.read tag 4 0 = some ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖
        rw [hvec]; exact hn) hz
      (fun i hi => ⟨N * (q + 1), by rw [hsh, hshape]; rfl, by
        change i < N at hi
        change 0 + i < N * (q + 1)
        rw [Nat.mul_succ]
        omega⟩)
  have hstate : State tag N q 0 A b out storedMatrix := by
    apply State.of_initial_reads_of_workspace storedMatrix tag N q A b out
      (hs'.trans (hsh.trans hshape))
    · intro i
      exact (hframe tag 0 i (Or.inl (by decide))).trans
        ((hf tag 0 i (by decide) (by decide) (by decide) (by decide)).trans (hb i))
    · cases storedMatrix with
      | false => trivial
      | true =>
        intro i j
        exact (hframe tag 6 _ (Or.inl (by decide))).trans
          ((hf tag 6 _ (by decide) (by decide) (by decide) (by decide)).trans (hA i j))
    · intro i
      have hi := hread i i.2
      change out.store.read tag 1 (0 + i) =
        some (xs i / ‖WithLp.toLp 2 (fun j : Fin N => xs j)‖) at hi
      rw [hvec] at hi
      simpa only [zero_add, congrFun hvec i, div_eq_mul_inv, mul_comm] using hi
    · exact (hframe tag 3 0 (Or.inl (by decide))).trans hβ
    · exact (hframe tag 4 0 (Or.inl (by decide))).trans hn
    · intro i
      exact (hframe tag 5 i (Or.inl (by decide))).trans (hp i i.2)
    · exact (hframe tag 8 0 (Or.inl (by decide))).trans hz
  refine ⟨out, ?_, hstate, hpos'.trans hpos, hcur'.trans hcur, hcurW'.trans hcurW, ?_,
    hpeak'.trans hpeak, hpeakW'.trans hpeakW⟩
  · change exec I ((do
        ins (.lit tag ⟨8, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
        nrm2 tag ⟨4, 0⟩ 0 0 (.const N)) >>= fun _ =>
          ifThenElse tag .eq ⟨4, 0⟩ ⟨8, 0⟩
            (forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)) (do
              copyv tag 0 0 1 0 (.const N)
              rscl tag ⟨4, 0⟩ 1 0 (.const N))).run st = some out
    rw [executionComposable_initialize_norm I tag N, hnorm, Option.bind_some]
    exact (exec_normalize_branch_var_eq I tag mid (.const N) 0 1 0 ⟨4, 0⟩ ⟨8, 0⟩).trans hbranch
  · rw [hcnt] at hcnt'
    simpa only [initializationCount, IExp.eval_const, add_assoc] using hcnt'

/-- The full actual initializer composes with the following loop. The certificate is built
from its actual scalar, loop and kernel atoms; no scope or alternate program is inserted. -/
theorem executionComposable_initialize (I : Interp P ι ℝ (OpCount P ι))
    (tag : P) (N : ℕ) : Computation.ExecutionComposable I (do
      ins (.lit tag ⟨8, 0⟩ 0)
      ins (.lit tag ⟨3, 0⟩ 0)
      forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
      nrm2 tag ⟨4, 0⟩ 0 0 (.const N)
      ifThenElse tag .eq ⟨4, 0⟩ ⟨8, 0⟩
        (forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)) (do
          copyv tag 0 0 1 0 (.const N)
          rscl tag ⟨4, 0⟩ 1 0 (.const N))) :=
  (executionComposable_initialize_norm I tag N).bind
    (Computation.executionComposable_single I (b :=
      ifThenElse tag .eq ⟨4, 0⟩ ⟨8, 0⟩
        (forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)) (do
          copyv tag 0 0 1 0 (.const N)
          rscl tag ⟨4, 0⟩ 1 0 (.const N))) (fun _ => rfl))

/-- Execute the literal prefix in the fixed nine-buffer layout. The actual scalar zero,
initial beta and previous vector are initialized; the other buffers remain unchanged.
All non-store fields are retained except the exact literal count. -/
theorem exec_initialize_zeros (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I)
    (tag : P) (N q : ℕ) (st : St P ℝ (OpCount P ι))
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, N * N), (tag, N), (tag, 2)]) :
    ∃ out, exec I (do
        ins (.lit tag ⟨8, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)).run st = some out ∧
      out = { st with
        store := out.store
        cnt := st.cnt + (N + 2) • Finsupp.single (.lit tag) 1 } ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag 8 0 = some 0 ∧ out.store.read tag 3 0 = some 0 ∧
      (∀ i < N, out.store.read tag 5 i = some 0) ∧
      ∀ p b i, b ≠ 3 → b ≠ 5 → b ≠ 8 →
        out.store.read p b i = st.store.read p b i := by
  exact exec_initialize_zeros_of_workspace true I hI hc tag N q st hshape

/-- The actual norm prefix follows literal initialization with `nrm2` on the unchanged input.
It retains all other buffers, gives the exact stored norm, and accounts for its actual square
root and scratch memory. This holds for zero input and zero dimension. -/
theorem exec_initialize_norm (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I)
    (tag : P) (N q : ℕ) (st : St P ℝ (OpCount P ι)) (b : Fin N → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, N * N), (tag, N), (tag, 2)])
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i)) :
    ∃ out, exec I (do
        ins (.lit tag ⟨8, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
        nrm2 tag ⟨4, 0⟩ 0 0 (.const N)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
      out.store.read tag 8 0 = some 0 ∧ out.store.read tag 3 0 = some 0 ∧
      (∀ i < N, out.store.read tag 5 i = some 0) ∧
      (∀ p d i, d ≠ 3 → d ≠ 5 → d ≠ 8 → d ≠ 4 →
        out.store.read p d i = st.store.read p d i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + (N + 2) • Finsupp.single (.lit tag) 1 +
        (N • (Finsupp.single (.un tag .conj) 1 + Finsupp.single (.bin tag .mul) 1 +
          Finsupp.single (.bin tag .add) 1) + Finsupp.single (.lit tag) 1 +
            Finsupp.single (.un tag .sqrt) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  exact exec_initialize_norm_of_workspace true I hI hc tag N q st b hshape hb

/-- Flat initialized-buffer facts give the exact zero-step loop invariant. This constructor
has no execution conclusion: each read is supplied by the actual initialization proof. -/
theorem State.of_initial_reads (tag : P) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (st : St P ℝ (OpCount P ι))
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, N * N), (tag, N), (tag, 2)])
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hA : Holds st.store tag 6 0 A)
    (hV : ∀ i : Fin N, st.store.read tag 1 i = some (‖WithLp.toLp 2 b‖⁻¹ * b i))
    (hbeta : st.store.read tag 3 0 = some 0)
    (hnorm : st.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖)
    (hprev : ∀ i : Fin N, st.store.read tag 5 i = some 0)
    (hzero : st.store.read tag 8 0 = some 0) : State tag N q 0 A b st := by
  exact State.of_initial_reads_of_workspace true tag N q A b st hshape hb hA hV
    hbeta hnorm hprev hzero

/-- The actual full initializer of the approved program produces the zero-step stored
Lanczos recurrence state. The input norm is taken from the input buffer before copying
and dividing into the basis; zero input and zero dimension use the explicit zero branch.
Its counts and scratch peak are the compositional bounds used in the approved target. -/
theorem exec_initialize (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I)
    (tag : P) (N q : ℕ) (st : St P ℝ (OpCount P ι))
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, N * N), (tag, N), (tag, 2)])
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hA : Holds st.store tag 6 0 A) :
    ∃ out, exec I (do
        ins (.lit tag ⟨8, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
        nrm2 tag ⟨4, 0⟩ 0 0 (.const N)
        ifThenElse tag .eq ⟨4, 0⟩ ⟨8, 0⟩
          (forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)) (do
            copyv tag 0 0 1 0 (.const N)
            rscl tag ⟨4, 0⟩ 1 0 (.const N))).run st = some out ∧
      State tag N q 0 A b out ∧ out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt ≤ st.cnt + initializationCount tag N ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  exact exec_initialize_of_workspace true I hI hc tag N q st A b hshape hb hA


end NLAlib.LanczosImplementation
