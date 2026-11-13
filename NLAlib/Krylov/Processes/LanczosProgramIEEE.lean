/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.IEEE
public import NLAlib.Krylov.Processes.LanczosProgramRoundedInitialization

/-!
# Literal-only Lanczos initialization with finite binary64 words

The actual Lanczos zero prefix uses no arithmetic operation. Its execution follows from
the checked binary64 zero literal, with arbitrary pre-existing input and matrix words.
The zero-norm branch also executes when the stored norm and zero header decode to zero,
including signed zeros. The successful comparison is proved from finite-word semantics.

These results retain the actual store, frame and operation charges. They do not certify
the preceding norm computation, the nonzero normalization branch or a complete Lanczos run.

## Main results

* `NLAlib.LanczosImplementation.exec_initialize_zeros_of_sem_eq_finiteFloatSem`:
  actual binary64 zero-prefix execution without an arithmetic accuracy assumption.
* `NLAlib.LanczosImplementation.exec_initial_normalization_of_sem_eq_finiteFloatSem_of_zero`:
  actual binary64 zero-norm branch, with comparison and literal success proved.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation Computation.Builder

/-- The checked finite binary64 zero literal suffices to execute the actual Lanczos scalar
zero setup and previous-vector fill. The dimension and budget may be zero; input and matrix
words may be arbitrary finite words. Only the three stated workspace capacities are needed.
All other cells and all usage fields except the exact literal charges are preserved. -/
theorem exec_initialize_zeros_of_sem_eq_finiteFloatSem {ι C : Type} [AddMonoid C]
    (I : Interp Unit ι FiniteFloat C) (hsem : I.sem = finiteFloatSem)
    (N q : ℕ) (st : St Unit FiniteFloat C)
    (h3 : st.store.shape[3]? = some ((), q + 1))
    (h5 : st.store.shape[5]? = some ((), N))
    (h8 : st.store.shape[8]? = some ((), 2)) :
    ∃ out zero, exec I (do
        ins (.lit () ⟨8, 0⟩ 0)
        ins (.lit () ⟨3, 0⟩ 0)
        forRange (.const N) fun i => ins (.lit () ⟨5, .var i⟩ 0)).run st = some out ∧
      out.store.shape = st.store.shape ∧ floatDecode zero.val = 0 ∧
      out.store.read () 8 0 = some zero ∧ out.store.read () 3 0 = some zero ∧
      (∀ i : Fin N, out.store.read () 5 i = some zero) ∧
      (∀ p buf idx, buf ≠ 5 → (buf ≠ 3 ∨ idx ≠ 0) → (buf ≠ 8 ∨ idx ≠ 0) →
        out.store.read p buf idx = st.store.read p buf idx) ∧
      out = { st with
        store := out.store
        cnt := st.cnt + I.charge (.lit ()) + I.charge (.lit ()) + N • I.charge (.lit ()) } := by
  obtain ⟨zero, hz, hd⟩ := isArithErrSem_finiteFloatSem.lit_zero ()
  have hzI : I.sem.lit () 0 = some zero := by rw [hsem]; exact hz
  obtain ⟨out, he, sh, r8, r3, r5, hf, hu⟩ :=
    exec_initialize_zeros_of_lit_eq_some I () zero hzI N q st h3 h5 h8
  exact ⟨out, zero, he, sh, hd, r8, r3, r5, hf, hu⟩

/-- With the actual stored norm and zero header both decoding to zero, the finite binary64
Lanczos initialization branch succeeds and fills its first basis column with decoded zeros.
Either signed zero is allowed in either comparison operand. The comparison and literal
success are proved; no global relative-error model or successful-execution premise is assumed.
Every other cell is retained, with exactly one comparison and N literals charged. -/
theorem exec_initial_normalization_of_sem_eq_finiteFloatSem_of_zero
    {ι C : Type} [AddMonoid C] (I : Interp Unit ι FiniteFloat C)
    (hsem : I.sem = finiteFloatSem) (N q : ℕ) (st : St Unit FiniteFloat C)
    (normword zero : FiniteFloat)
    (hn : st.store.read () 4 0 = some normword)
    (hz : st.store.read () 8 0 = some zero)
    (hdn : floatDecode normword.val = 0) (hdz : floatDecode zero.val = 0)
    (h1 : st.store.shape[1]? = some ((), N * (q + 1))) :
    ∃ out literal, exec I (ifThenElse () .eq ⟨4, 0⟩ ⟨8, 0⟩
        (forRange (.const N) fun i => ins (.lit () ⟨1, .var i⟩ 0))
        (do copyv () 0 0 1 0 (.const N); rscl () ⟨4, 0⟩ 1 0 (.const N))).run st = some out ∧
      out.store.shape = st.store.shape ∧ floatDecode literal.val = 0 ∧
      (∀ i : Fin N, out.store.read () 1 i = some literal) ∧
      (∀ p buf idx, (buf ≠ 1 ∨ N ≤ idx) →
        out.store.read p buf idx = st.store.read p buf idx) ∧
      out = { st with
        store := out.store
        cnt := st.cnt + I.charge (.cmp ()) + N • I.charge (.lit ()) } := by
  obtain ⟨literal, hl, hdl⟩ := isArithErrSem_finiteFloatSem.lit_zero ()
  have hlI : I.sem.lit () 0 = some literal := by rw [hsem]; exact hl
  have hcI : I.sem.cmp () .eq normword zero = some true := by
    rw [hsem]
    exact cmp_eq_eq_some_true_finiteFloatSem_of_zero normword zero hdn hdz
  obtain ⟨out, he, sh, hr, hf, hu⟩ := exec_initial_normalization_of_cmp_eq_some_true
    I () literal zero normword hlI N q st hn hz hcI h1
  exact ⟨out, literal, he, sh, hdl, hr, hf, hu⟩

end NLAlib.LanczosImplementation
