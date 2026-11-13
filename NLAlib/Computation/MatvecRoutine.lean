/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract
public import NLAlib.Computation.RoutineFrames

/-!
# Certified matrix-vector routines

A rounded solver uses the same product contract for a stored kernel and an external oracle.
The certificate records actual successful execution, its block-write frame and its normwise
error. Scalar arithmetic accuracy remains a separate contract. Each invocation may incur a
different error; no fixed perturbed matrix is assumed.

## Main results

* `NLAlib.Computation.IsMatvecErrOn.exec_apply`: an input-domain oracle executes on stored words.
* `NLAlib.Computation.IsMatvecErr.exec_apply`: an accurate oracle executes on stored words.
* `NLAlib.Computation.IsMatvecErr.isMatvecRoutine`: the oracle supplies a routine certificate.
* `NLAlib.Computation.IsMatvecRoutine.toBlockRoutine`: the footprint of the certificate.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder
open scoped Matrix

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- A successful matrix-vector routine at absolute operator-error coefficient `c`.
The precondition records backend storage, independently of the input/output blocks. The
actual output is a block write, so its shape and every outside cell are preserved. -/
structure IsMatvecRoutine (I : Interp P ι K C) (dec : P → K → ℝ) (tag : P)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (c : ℝ)
    (pre : Store P K → Prop) (src dst : ℕ) (sOff dOff : IExp ℕ)
    (routine : Builder P ι ℕ ℕ Unit) : Prop where
  /-- The routine composes with the following program without escaping allocations. -/
  composable : ExecutionComposable I routine
  /-- Actual input words and writable output imply execution and its decoded error. -/
  run : ∀ (st : St P K C) (x : Fin N → ℝ), pre st.store →
    (∀ i : Fin N, ∃ w, st.store.read tag src (sOff.eval + i) = some w ∧
      dec tag w = x i) →
    (∀ i < N, ∃ len, st.store.shape[dst]? = some (tag, len) ∧ dOff.eval + i < len) →
    ∃ (out : St P K C) (W : Fin N → K), exec I routine.run st = some out ∧
      st.store.writeBlock tag dst dOff.eval (Array.ofFn W) =
        some out.store ∧
      ‖WithLp.toLp 2 (A *ᵥ x - fun i : Fin N => dec tag (W i))‖ ≤
        c * ‖WithLp.toLp 2 x‖

/-- A routine certificate remains valid when its allowed operator error is increased. -/
theorem IsMatvecRoutine.mono {I : Interp P ι K C} {dec : P → K → ℝ} {tag : P}
    {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {c d : ℝ} {pre : Store P K → Prop}
    {src dst : ℕ} {sOff dOff : IExp ℕ} {routine : Builder P ι ℕ ℕ Unit}
    (h : IsMatvecRoutine I dec tag A c pre src dst sOff dOff routine) (hc : c ≤ d) :
    IsMatvecRoutine I dec tag A d pre src dst sOff dOff routine where
  composable := h.composable
  run st x hp hx hy := by
    obtain ⟨out, W, hr, hw, he⟩ := h.run st x hp hx hy
    exact ⟨out, W, hr, hw, he.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))⟩

/-- The footprint of a certified matrix-vector routine: from a state satisfying `pre` whose
source block is decoded, it writes exactly the destination block
(`NLAlib.Computation.IsBlockRoutine`). -/
theorem IsMatvecRoutine.toBlockRoutine {I : Interp P ι K C} {dec : P → K → ℝ} {tag : P}
    {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {c : ℝ} {pre : Store P K → Prop}
    {src dst : ℕ} {sOff dOff : IExp ℕ} {routine : Builder P ι ℕ ℕ Unit}
    (h : IsMatvecRoutine I dec tag A c pre src dst sOff dOff routine) :
    IsBlockRoutine I tag (fun s => pre s ∧ ∃ x : Fin N → ℝ, ReadsDecoded s dec tag src sOff.eval x)
      [(dst, dOff.eval, N)] routine where
  composable := h.composable
  run st hp hw := by
    obtain ⟨hp, x, hx⟩ := hp
    obtain ⟨out, W, hr, hwr, -⟩ := h.run st x hp hx (hw _ List.mem_cons_self)
    exact ⟨out, [Array.ofFn W], hr, Store.writeBlocks_singleton_eq_some_iff.mpr ⟨by simp, hwr⟩⟩

/-- An oracle with an input-domain mixed-error certificate executes one actual column
when its decoded input satisfies the domain, into a disjoint writable destination buffer. The
result retains its raw block write, including when the dimension is zero. -/
theorem IsMatvecErrOn.exec_apply {I : Interp P ι K C} {o : ι} {dec : P → K → ℝ}
    {tag : P} {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {c η : ℝ} {domain : (Fin N → ℝ) → Prop}
    (h : IsMatvecErrOn I o dec tag A domain c η) (st : St P K C)
    (src dst : ℕ) (sOff dOff : IExp ℕ) (hne : dst ≠ src) (x : Fin N → ℝ) (hdomain : domain x)
    (hx : ∀ i : Fin N, ∃ w, st.store.read tag src (sOff.eval + i) = some w ∧
      dec tag w = x i)
    (hy : ∀ i < N, ∃ len, st.store.shape[dst]? = some (tag, len) ∧ dOff.eval + i < len) :
    ∃ (out : St P K C) (W : Fin N → K),
      exec I (.apply o tag dst dOff src sOff 1) st = some out ∧
      st.store.writeBlock tag dst dOff.eval (Array.ofFn W) =
        some out.store ∧
      ‖WithLp.toLp 2 (A *ᵥ x - fun i : Fin N => dec tag (W i))‖ ≤
        c * ‖WithLp.toLp 2 x‖ + η := by
  classical
  let words : Fin N → K := fun i => (hx i).choose
  let X := Array.ofFn words
  have hXsize : X.size = N := by simp [X]
  have hdecode : (fun i : Fin N => dec tag (X[i.val]'(by omega))) = x := by
    funext i
    simpa only [X, Array.getElem_ofFn, words] using (hx i).choose_spec.2
  obtain ⟨Y, hYsize, horacle, herr⟩ := h.2 X hXsize (hdecode ▸ hdomain)
  let W : Fin N → K := fun i => Y[i.val]'(by omega)
  have hY : Array.ofFn W = Y := by
    apply Array.ext (by simp [hYsize])
    intro i hi hj
    simp [W]
  obtain ⟨store, hwrite⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape
    (xs := Y) (fun i hi => hy i (by omega))
  let out : St P K C := { st with
    store := store
    cnt := st.cnt + (I.charge (.load tag o) + I.charge (.matvec tag o)) }
  have hread : st.store.readBlock tag src sOff.eval N = some X := by
    by_cases hN : N = 0
    · have hXempty : X = #[] := Array.eq_empty_of_size_eq_zero (hXsize.trans hN)
      simp [hN, Store.readBlock, hXempty]
    · let f : ℕ → K := fun i =>
        if hi : i < N then words ⟨i, hi⟩ else words ⟨0, Nat.pos_of_ne_zero hN⟩
      have hr := Store.readBlock_eq_some_map_range f (s := st.store) (p := tag)
        (b := src) (off := sOff.eval) (len := N) (fun i hi => by
          simpa only [f, dif_pos hi] using (hx ⟨i, hi⟩).choose_spec.1)
      convert hr using 2
      apply Array.ext (by simp [X])
      intro i hi hj
      simp [X, f, show i < N by simpa [X] using hi]
  refine ⟨out, W, ?_, by simpa only [hY] using hwrite, ?_⟩
  · simp only [exec, if_pos (Or.inl hne), h.1, IExp.eval_ofNat, mul_one, hread,
      Option.bind_some, horacle, hwrite, Option.map_some, one_nsmul, out]
  · simpa only [hdecode, W] using herr

/-- An oracle satisfying the normwise accuracy and success contract executes one actual
column from any readable source block into a disjoint writable destination buffer. The
result retains its raw block write, including when the dimension is zero. -/
theorem IsMatvecErr.exec_apply {I : Interp P ι K C} {o : ι} {dec : P → K → ℝ}
    {tag : P} {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {c : ℝ}
    (h : IsMatvecErr I o dec tag A c) (st : St P K C)
    (src dst : ℕ) (sOff dOff : IExp ℕ) (hne : dst ≠ src) (x : Fin N → ℝ)
    (hx : ∀ i : Fin N, ∃ w, st.store.read tag src (sOff.eval + i) = some w ∧
      dec tag w = x i)
    (hy : ∀ i < N, ∃ len, st.store.shape[dst]? = some (tag, len) ∧ dOff.eval + i < len) :
    ∃ (out : St P K C) (W : Fin N → K),
      exec I (.apply o tag dst dOff src sOff 1) st = some out ∧
      st.store.writeBlock tag dst dOff.eval (Array.ofFn W) =
        some out.store ∧
      ‖WithLp.toLp 2 (A *ᵥ x - fun i : Fin N => dec tag (W i))‖ ≤
        c * ‖WithLp.toLp 2 x‖ := by
  simpa only [add_zero] using
    (h.toOn (fun _ => True)).exec_apply st src dst sOff dOff hne x trivial hx hy

/-- An accurate oracle supplies the routine certificate without any stored-matrix
precondition. Its success clause is used, not merely the error of successful calls. -/
theorem IsMatvecErr.isMatvecRoutine {I : Interp P ι K C} {o : ι} {dec : P → K → ℝ}
    {tag : P} {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {c : ℝ}
    (h : IsMatvecErr I o dec tag A c) (src dst : ℕ) (sOff dOff : IExp ℕ)
    (hne : dst ≠ src) :
    IsMatvecRoutine I dec tag A c (fun _ => True) src dst sOff dOff
      (stmt (.apply o tag dst dOff src sOff 1)) where
  composable := executionComposable_single I (fun _ => rfl)
  run st x _ hx hy := by
    obtain ⟨out, W, hr, hw, he⟩ := h.exec_apply st src dst sOff dOff hne x hx hy
    refine ⟨out, W, ?_, hw, he⟩
    change exec I (.seq (.apply o tag dst dOff src sOff 1) .skip) st = some out
    rwa [exec_seq_skip]

end NLAlib.Computation
