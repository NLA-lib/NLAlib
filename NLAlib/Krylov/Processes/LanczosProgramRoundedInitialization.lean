/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.GuardedNormalization
public import NLAlib.Computation.BLAS.NormalizationFrames
public import NLAlib.Computation.ScalarFrames
public import NLAlib.Krylov.Processes.LanczosProgramInitialization
public import NLAlib.Krylov.Processes.LanczosProgramRounding
public import NLAlib.Krylov.Processes.LanczosProgramRoundedState

/-!
# Actual rounded initialization of the stored Lanczos tree

The canonical zero-literal prefix needs only a successful zero literal for arbitrary
stored words. It preserves the actual input and matrix entries. Rounded normalization uses
the actual norm, comparison, copy and division order, with decoded norm-word provenance.

## Main results

* `NLAlib.LanczosImplementation.exec_rounded_initialize_zeros`: actual zero setup and frame.
* `NLAlib.LanczosImplementation.exec_rounded_initialize`: full initialized decoded context.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation Computation.Builder
open scoped Matrix

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u : P → ℝ} {dec : P → K → ℝ} {storedMatrix : Bool}

/-- The two scalar-zero literals and previous-vector zero fill execute in the exact
canonical order under the standard relative-error contract. The stored zero decodes to zero;
all other cells and non-store usage fields except literal count are preserved. This retains
the existing relative-model interface, while its execution is obtained from the weaker
literal-only setup. The vector length and requested budget may be zero. -/
theorem exec_rounded_initialize_zeros (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (N q : ℕ) (st : St P K C)
    (h3 : st.store.shape[3]? = some (tag, q + 1))
    (h5 : st.store.shape[5]? = some (tag, N))
    (h8 : st.store.shape[8]? = some (tag, 2)) :
    ∃ out zero, exec I (do
        ins (.lit tag ⟨8, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)).run st = some out ∧
      out.store.shape = st.store.shape ∧ dec tag zero = 0 ∧
      out.store.read tag 8 0 = some zero ∧ out.store.read tag 3 0 = some zero ∧
      (∀ i : Fin N, out.store.read tag 5 i = some zero) ∧
      (∀ p buf idx, buf ≠ 5 → (buf ≠ 3 ∨ idx ≠ 0) → (buf ≠ 8 ∨ idx ≠ 0) →
        out.store.read p buf idx = st.store.read p buf idx) ∧
      out = { st with
        store := out.store
        cnt := st.cnt + I.charge (.lit tag) + I.charge (.lit tag) +
          N • I.charge (.lit tag) } := by
  obtain ⟨zero, hz, hd⟩ := (hsem.isArithErrSem (fun _ => trivial)).lit_zero tag
  obtain ⟨out, he, sh, r8, r3, r5, hf, hu⟩ :=
    exec_initialize_zeros_of_lit_eq_some I tag zero hz N q st h3 h5 h8
  exact ⟨out, zero, he, sh, hd, r8, r3, r5, hf, hu⟩

/-- The actual zero-norm initialization branch fills the first basis column with the
successful zero-literal word when its stored comparison returns true. No arithmetic error
contract, input norm certificate or successful future execution is assumed. Every cell
outside that column window is preserved, with exactly one comparison and N literals charged.
The dimension and requested budget may be zero. -/
theorem exec_initial_normalization_of_cmp_eq_some_true
    (I : Interp P ι K C) (tag : P) (literal zero normword : K)
    (hz : I.sem.lit tag 0 = some literal) (N q : ℕ) (st : St P K C)
    (hn : st.store.read tag 4 0 = some normword)
    (hzero : st.store.read tag 8 0 = some zero)
    (hcmp : I.sem.cmp tag .eq normword zero = some true)
    (h1 : st.store.shape[1]? = some (tag, N * (q + 1))) :
    ∃ out, exec I (ifThenElse tag .eq ⟨4, 0⟩ ⟨8, 0⟩
        (forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0))
        (do copyv tag 0 0 1 0 (.const N); rscl tag ⟨4, 0⟩ 1 0 (.const N))).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, out.store.read tag 1 i = some literal) ∧
      (∀ p buf idx, (buf ≠ 1 ∨ N ≤ idx) →
        out.store.read p buf idx = st.store.read p buf idx) ∧
      out = { st with
        store := out.store
        cnt := st.cnt + I.charge (.cmp tag) + N • I.charge (.lit tag) } := by
  let compared : St P K C := { st with cnt := st.cnt + I.charge (.cmp tag) }
  have ec : cmpStep I tag .eq ⟨4, 0⟩ ⟨8, 0⟩ st = some (true, compared) := by
    simp only [cmpStep, IExp.eval_ofNat, hn, hzero, Option.bind_some, hcmp, Option.map_some]
    rfl
  have hNN : N ≤ N * (q + 1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N (Nat.succ_le_succ (Nat.zero_le q))
  obtain ⟨s, he, sh, hr, hf⟩ := exec_forRange_literal_zero_var I tag literal hz
    compared (.const N) 1 (fun i hi => ⟨N * (q + 1), h1, hi.trans_le hNN⟩)
  let out : St P K C :=
    { compared with store := s, cnt := compared.cnt + N • I.charge (.lit tag) }
  refine ⟨out, ?_, sh, fun i => hr i i.isLt, ?_, rfl⟩
  · change exec I (.seq (.ite tag .eq _ _ _ _) .skip) st = _
    rw [exec_seq_skip, exec_ite, ec]
    exact he
  · intro p buf idx h
    exact hf p buf idx (Or.inr h)

/-- The actual initial norm kernel supplies its nonnegative scale, relative norm bound
and strict zero test from the scalar contract. Empty input and empty dimension are included. -/
theorem exec_rounded_input_norm (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (N : ℕ) (st : St P K C) (b : Fin N → ℝ)
    (h4 : st.store.shape[4]? = some (tag, 1))
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hzero : ∃ w, st.store.read tag 8 0 = some w ∧ dec tag w = 0)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ out w, exec I (nrm2 tag ⟨4, 0⟩ 0 0 (.const N)).run st = some out ∧
      st.store.write tag 4 0 w = some out.store ∧ out.store.shape = st.store.shape ∧
      0 ≤ dec tag w ∧
      |‖WithLp.toLp 2 b‖ - dec tag w| ≤ roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 b‖ ∧
      (dec tag w = 0 ↔ b = 0) ∧
      ∀ p buf idx, (p ≠ tag ∨ buf ≠ 4 ∨ idx ≠ 0) →
        out.store.read p buf idx = st.store.read p buf idx := by
  let xs : ℕ → ℝ := fun i => if hi : i < N then b ⟨i, hi⟩ else 0
  have hx (i : ℕ) (hi : i < N) :
      ∃ w, st.store.read tag 0 (0 + i) = some w ∧ dec tag w = xs i := by
    simpa only [zero_add, xs, dif_pos hi] using hb ⟨i, hi⟩
  obtain ⟨zero, _, _⟩ := hzero
  obtain ⟨scratch, hs⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) zero h4
    (by norm_num)
  obtain ⟨hn, _, hg, _⟩ := lanczosImplementationRoundoffBound_kernel_bounds N
    (hsem.nonneg trivial) hsmall
  obtain ⟨out, w, he, hw, hnonneg, herr, hiff⟩ :=
    hsem.exec_nrm2_abs_norm_sub_le_zero_iff I tag hz st ⟨4, 0⟩ 0 0 (.const N) xs hn hg hx
      (by norm_num) ⟨zero, scratch, hs⟩
  have hxs : (fun i : Fin N => xs i) = b := by funext i; simp only [xs, dif_pos i.isLt]
  change |‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ - dec tag w| ≤
    roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at herr
  change dec tag w = 0 ↔ (fun i : Fin N => xs i) = 0 at hiff
  rw [hxs] at herr hiff
  refine ⟨out, w, he, hw, Store.shape_of_write_eq_some hw, hnonneg, herr, hiff, ?_⟩
  intro p buf idx hout
  rcases hout with hp | hcell
  · exact Store.read_of_write_eq_some_of_ne_tag hw hp
  · exact Store.read_of_write_eq_some_of_ne hw hcell

/-- The actual initial norm guard writes a zero first column or copies and divides the
input into it. The norm word comes from the executed kernel; the initial-direction bound
uses that computed scale and the mathematically normalized actual first column. -/
theorem exec_rounded_initial_normalization (I : Interp P ι K (OpCount P ι)) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I)
    (predot normed : St P K (OpCount P ι)) (N q : ℕ) (b : Fin N → ℝ)
    (h4 : predot.store.shape[4]? = some (tag, 1))
    (h1 : predot.store.shape[1]? = some (tag, N * (q + 1)))
    (hb : ∀ i : Fin N, ∃ w, predot.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hzero : ∃ w, predot.store.read tag 8 0 = some w ∧ dec tag w = 0)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hnorm : exec I (nrm2 tag ⟨4, 0⟩ 0 0 (.const N)).run predot = some normed) :
    ∃ (out : St P K (OpCount P ι)) (s : ℝ) (v1 : Fin N → ℝ),
      exec I (ifThenElse tag .eq ⟨4, 0⟩ ⟨8, 0⟩
        (forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0))
        (do copyv tag 0 0 1 0 (.const N); rscl tag ⟨4, 0⟩ 1 0 (.const N))).run normed = some out ∧
      out.store.shape = normed.store.shape ∧
      (∃ w, out.store.read tag 4 0 = some w ∧ dec tag w = s) ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 1 i = some w ∧ dec tag w = v1 i) ∧
      (∀ p buf idx, (buf ≠ 1 ∨ N ≤ idx) →
        out.store.read p buf idx = normed.store.read p buf idx) ∧
      0 ≤ s ∧ |‖WithLp.toLp 2 b‖ - s| ≤ roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 b‖ ∧
      (s = 0 ↔ b = 0) ∧ (s = 0 → v1 = 0) ∧
      (b ≠ 0 → |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ lanczosImplementationRoundoffBound N (u tag)) ∧
      ‖WithLp.toLp 2 (b - s • v1)‖ ≤ u tag * ‖WithLp.toLp 2 b‖ ∧
      ‖WithLp.toLp 2 (b - s • (‖WithLp.toLp 2 v1‖⁻¹ • v1))‖ ≤
        (2 * u tag + roundingFactor (N + 1) (u tag)) * ‖WithLp.toLp 2 b‖ := by
  obtain ⟨actual, normword, en, hw, shn, _, _, _, fn⟩ :=
    exec_rounded_input_norm I tag hsem hz N predot b h4 hb hzero hsmall
  have ha : actual = normed := Option.some.inj (en.symm.trans hnorm)
  subst actual
  let xs : ℕ → ℝ := fun i => if hi : i < N then b ⟨i, hi⟩ else 0
  have hx (i : ℕ) (hi : i < N) :
      ∃ w, predot.store.read tag 0 (0 + i) = some w ∧ dec tag w = xs i := by
    simpa only [zero_add, xs, dif_pos hi] using hb ⟨i, hi⟩
  have hxN (i : ℕ) (hi : i < N) :
      ∃ w, normed.store.read tag 0 (0 + i) = some w ∧ dec tag w = xs i := by
    rw [fn tag 0 (0 + i) (Or.inr (Or.inl (by norm_num)))]
    exact hx i hi
  obtain ⟨zero, rz, dz⟩ := hzero
  have hzN : ∃ w, normed.store.read tag 8 0 = some w ∧ dec tag w = 0 :=
    ⟨zero, (fn tag 8 0 (Or.inr (Or.inl (by norm_num)))).trans rz, dz⟩
  obtain ⟨scratch, hs⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) zero h4
    (by norm_num)
  have hNN : N ≤ N * (q + 1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N (Nat.succ_le_succ (Nat.zero_le q))
  have hcap (i : ℕ) (hi : i < N) : ∃ len,
      normed.store.shape[1]? = some (tag, len) ∧ (0 : IExp ℕ).eval + i < len :=
    ⟨N * (q + 1), shn ▸ h1, by simpa only [IExp.eval_zero, zero_add] using hi.trans_le hNN⟩
  obtain ⟨hn, _, hg, _⟩ := lanczosImplementationRoundoffBound_kernel_bounds N
    (hsem.nonneg trivial) hsmall
  obtain ⟨out, w, W, eg, shape, _, rnorm, hnonneg, herr, hiff, hW, frame, hzv, hunit,
      hres, hdir⟩ := hsem.exec_guarded_copyv_rscl_of_nrm2_execution I tag hz hc
    predot normed normed ⟨4, 0⟩ ⟨8, 0⟩ 0 1 0 0 (.const N) xs hn hg hx hxN
      (by norm_num) (by norm_num) (by norm_num) ⟨zero, scratch, hs⟩ hcap hnorm rfl hzN
  have hxs : (fun i : Fin N => xs i) = b := by funext i; simp only [xs, dif_pos i.isLt]
  change |‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ - dec tag w| ≤
    roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at herr
  change dec tag w = 0 ↔ (fun i : Fin N => xs i) = 0 at hiff
  change ‖WithLp.toLp 2 ((fun i : Fin N => xs i) - dec tag w •
    (fun i : Fin N => dec tag (W i)))‖ ≤
      u tag * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at hres
  change ‖WithLp.toLp 2 ((fun i : Fin N => xs i) - dec tag w •
    (‖WithLp.toLp 2 (fun i : Fin N => dec tag (W i))‖⁻¹ •
      (fun i : Fin N => dec tag (W i))))‖ ≤
      (2 * u tag + roundingFactor (N + 1) (u tag)) *
        ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at hdir
  rw [hxs] at herr hiff hres hdir
  refine ⟨out, dec tag w, fun i => dec tag (W i), ?_, shape, ⟨w, rnorm, rfl⟩,
    (fun i => ⟨W i, by simpa only [IExp.eval_zero, zero_add] using hW i, rfl⟩), ?_,
    hnonneg, herr, hiff, hzv, ?_, hres, hdir⟩
  · exact (exec_normalize_branch_var_eq I tag normed (.const N) 0 1 0 ⟨4, 0⟩ ⟨8, 0⟩).trans eg
  · intro p buf idx hout
    exact frame p buf idx (hout.elim Or.inl (fun hi => Or.inr (Or.inr
      (by simpa only [IExp.eval_zero, IExp.eval_const, zero_add] using hi))))
  · intro hbne
    exact (hunit (fun he => hbne (hiff.mp he))).trans
      (normalizationRoundingFactor_le_lanczosImplementationRoundoffBound N
        (hsem.nonneg trivial) hsmall)

/-- Actual initialized decoded reads give the zero-step storage context. Future numerical
indices are zero defaults, and no arithmetic or near-unit facts are assumed here. -/
theorem StoreContext.of_initial_reads (tag : P) (N q : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b v1 : Fin N → ℝ) (s : ℝ) (store : Store P K)
    (hshape : store.shape = workspaceShape tag N q storedMatrix)
    (hb : ∀ i : Fin N, ∃ w, store.read tag 0 i = some w ∧ dec tag w = b i)
    (hA : if storedMatrix then HoldsDecoded store dec tag 6 0 A else True)
    (hV : ∀ i : Fin N, ∃ w, store.read tag 1 i = some w ∧ dec tag w = v1 i)
    (hbeta : ∃ w, store.read tag 3 0 = some w ∧ dec tag w = 0)
    (hs : ∃ w, store.read tag 4 0 = some w ∧ dec tag w = s)
    (hp : ∀ i : Fin N, ∃ w, store.read tag 5 i = some w ∧ dec tag w = 0)
    (hz : ∃ w, store.read tag 8 0 = some w ∧ dec tag w = 0) :
    StoreContext tag dec N q 0 A b (Function.update (0 : ℕ → Fin N → ℝ) 1 v1)
      (fun _ => 0) (fun _ => 0) s store storedMatrix := by
  refine ⟨hshape, hb, hA, ?_, ?_, ?_, hs, ?_, hz⟩
  · intro c hc i
    have hc0 : c = 0 := by omega
    subst c
    simpa only [Nat.mul_zero, zero_add, Function.update_self] using hV i
  · intro c hc
    omega
  · intro c hc
    have hc0 : c = 0 := by omega
    subst c
    exact hbeta
  · intro i
    simpa only [Function.update_of_ne (by omega : 0 ≠ 1), Pi.zero_apply] using hp i

/-- The actual canonical initializer executes from loaded matrix and input words. It
proves every zero-step stored field and the normalization guarantees, including zero input,
zero requested budget and empty dimension. The stored scale is the computed input norm. -/
theorem exec_rounded_initialize (I : Interp P ι K (OpCount P ι)) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hshape : st.store.shape = workspaceShape tag N q storedMatrix)
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hA : if storedMatrix then HoldsDecoded st.store dec tag 6 0 A else True)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (s : ℝ) (v1 : Fin N → ℝ),
      exec I (do
        ins (.lit tag ⟨8, 0⟩ 0)
        ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
        nrm2 tag ⟨4, 0⟩ 0 0 (.const N)
        ifThenElse tag .eq ⟨4, 0⟩ ⟨8, 0⟩
          (forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0))
          (do copyv tag 0 0 1 0 (.const N); rscl tag ⟨4, 0⟩ 1 0 (.const N))).run st = some out ∧
      StoreContext tag dec N q 0 A b (Function.update (0 : ℕ → Fin N → ℝ) 1 v1)
        (fun _ => 0) (fun _ => 0) s out.store storedMatrix ∧
      0 ≤ s ∧ |‖WithLp.toLp 2 b‖ - s| ≤ roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 b‖ ∧
      (s = 0 ↔ b = 0) ∧ (s = 0 → v1 = 0) ∧
      (b ≠ 0 → |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ lanczosImplementationRoundoffBound N (u tag)) ∧
      ‖WithLp.toLp 2 (b - s • v1)‖ ≤ u tag * ‖WithLp.toLp 2 b‖ ∧
      ‖WithLp.toLp 2 (b - s • (‖WithLp.toLp 2 v1‖⁻¹ • v1))‖ ≤
        (2 * u tag + roundingFactor (N + 1) (u tag)) * ‖WithLp.toLp 2 b‖ := by
  obtain ⟨predot, zero, ez, shz, dz, rz, rb, rp, fz, _⟩ :=
    exec_rounded_initialize_zeros I tag hsem N q st
      (by simp [hshape, workspaceShape]) (by simp [hshape, workspaceShape])
      (by simp [hshape, workspaceShape])
  have hbp (i : Fin N) :
      ∃ w, predot.store.read tag 0 i = some w ∧ dec tag w = b i := by
    rw [fz tag 0 i (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    exact hb i
  have h4 : predot.store.shape[4]? = some (tag, 1) := by simp [shz, hshape, workspaceShape]
  obtain ⟨normed, w, en, hw, shn, _, _, _, fn⟩ := exec_rounded_input_norm I tag hsem hz N
    predot b h4 hbp ⟨zero, rz, dz⟩ hsmall
  obtain ⟨out, s, v1, eg, sho, rs, rv, fo, hnonneg, herr, hiff, hzv, hunit, hres, hdir⟩ :=
    exec_rounded_initial_normalization I tag hsem hz hc predot normed N q b h4
      (by simp [shz, hshape, workspaceShape]) hbp ⟨zero, rz, dz⟩ hsmall en
  have frame (p : P) (buf idx : ℕ) (h1 : buf ≠ 1) (h4 : buf ≠ 4) :
      out.store.read p buf idx = predot.store.read p buf idx :=
    (fo p buf idx (Or.inl h1)).trans (fn p buf idx (Or.inr (Or.inl h4)))
  refine ⟨out, s, v1, ?_, ?_, hnonneg, herr, hiff, hzv, hunit, hres, hdir⟩
  · have hcomp : ExecutionComposable I (do
        ins (.lit tag ⟨8, 0⟩ 0); ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)) :=
      (executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          (executionComposable_single I (fun _ => rfl)))
    change exec I ((do
        ins (.lit tag ⟨8, 0⟩ 0); ins (.lit tag ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)) >>= fun _ => _).run st = _
    rw [hcomp, ez, Option.bind_some, exec_run_bind I
      (b := nrm2 tag ⟨4, 0⟩ 0 0 (.const N)) (fun _ => rfl), en, Option.bind_some]
    exact eg
  · apply StoreContext.of_initial_reads tag N q A b v1 s out.store
      ((sho.trans (shn.trans shz)).trans hshape)
    · intro i
      rw [frame tag 0 i (by norm_num) (by norm_num),
        fz tag 0 i (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      exact hb i
    · cases storedMatrix with
      | false => trivial
      | true =>
        intro i j
        rw [frame tag 6 _ (by norm_num) (by norm_num),
          fz tag 6 _ (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        exact hA i j
    · exact rv
    · exact ⟨zero, (frame tag 3 0 (by norm_num) (by norm_num)).trans rb, dz⟩
    · exact rs
    · intro i
      exact ⟨zero, (frame tag 5 i (by norm_num) (by norm_num)).trans (rp i), dz⟩
    · exact ⟨zero, (frame tag 8 0 (by norm_num) (by norm_num)).trans rz, dz⟩

/-- The entire canonical initializer composes with its actual continuation, for every
word carrier and counter monoid. This certificate is derived only from single-statement
atoms and certified binds, with no arbitrary Builder bind law or inserted scope. -/
theorem executionComposable_rounded_initialize (I : Interp P ι K C) (tag : P) (N : ℕ) :
    ExecutionComposable I (do
      ins (.lit tag ⟨8, 0⟩ 0)
      ins (.lit tag ⟨3, 0⟩ 0)
      forRange (.const N) fun i => ins (.lit tag ⟨5, .var i⟩ 0)
      nrm2 tag ⟨4, 0⟩ 0 0 (.const N)
      ifThenElse tag .eq ⟨4, 0⟩ ⟨8, 0⟩
        (forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0))
        (do copyv tag 0 0 1 0 (.const N); rscl tag ⟨4, 0⟩ 1 0 (.const N))) := by
  exact (executionComposable_single I (fun _ => rfl)).bind
    ((executionComposable_single I (fun _ => rfl)).bind
      ((executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          (executionComposable_single I (fun _ => rfl)))))

end NLAlib.LanczosImplementation
