/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramRoundedStep

/-!
# Committing an actual rounded Lanczos column

The canonical step copies the current column into the previous-vector buffer after the
next norm has been computed and before testing that norm. The raw frame below retains
the norm word and the projected work vector across this intervening executed copy.

## Main results

* `NLAlib.LanczosImplementation.exec_rounded_previous_copy`: actual copy and provenance frame.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation Builder

variable {P ι K : Type} [DecidableEq P]
    {u : P → ℝ} {dec : P → K → ℝ} {storedMatrix : Bool}
    {mv : ℕ → Builder P ι ℕ ℕ Unit}

/-- The actual copy into the previous-vector buffer keeps all other raw words, including
the norm and work words. Source words are copied exactly, without a numerical assumption
on their decodings or their norm. -/
theorem exec_rounded_previous_copy (I : Interp P ι K (OpCount P ι))
    (hc : IsUnitCharge I) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store
      storedMatrix) :
    ∃ out, exec I (copyv tag 1 (IExp.const N * IExp.var j) 5 0 (IExp.const N)).run st =
        some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 5 i = some w ∧ dec tag w = v (j + 1) i) ∧
      (∀ p k i, k ≠ 5 → out.store.read p k i = st.store.read p k i) := by
  classical
  choose words hread hdec using hs.basis j le_rfl
  obtain ⟨fallback, _, _⟩ := hs.zero
  let W : ℕ → K := fun i => if hi : i < N then words ⟨i, hi⟩ else fallback
  have hW (i : ℕ) (hi : i < N) :
      st.store.read tag 1 ((IExp.const N * IExp.var j).eval + i) = some (W i) := by
    simpa only [W, dif_pos hi, IExp.eval_mul, IExp.eval_const, IExp.eval_var] using
      hread ⟨i, hi⟩
  obtain ⟨out, hr, hshape, hprev, hframe, _⟩ := exec_copyv_frame I hc tag st
    (IExp.const N) 1 5 (IExp.const N * IExp.var j) 0 W hW (by omega)
    (by intro i hi; exact ⟨N, by rw [hs.shape]; rfl, by simpa using hi⟩)
  refine ⟨out, hr, hshape, ?_, ?_⟩
  · intro i
    refine ⟨W i, by simpa using hprev i i.isLt, ?_⟩
    simpa only [W, dif_pos i.isLt] using hdec i
  · intro p k i hk
    exact hframe p k i (Or.inl hk)

/-- Copy the actual current column into the previous buffer, then execute the canonical
zero guard and either literal-zero fill or copy and divide. Norm-word provenance crosses
the intervening copy. The returned normalization defect and near-unit property follow
from the preceding actual nrm2 trace, including its zero case. -/
theorem exec_rounded_commit (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ}
    (predot normed : St P K (OpCount P ι))
    (hp : StoreContext tag dec N q j A b v α β s predot.store storedMatrix)
    (hs : StoreContext tag dec N q j A b v α β s normed.store storedMatrix)
    (hj : j < q) (an : ℝ)
    (han : ∃ w, normed.store.read tag 2 j = some w ∧ dec tag w = an)
    (zv : Fin N → ℝ)
    (hzp : ∀ i : Fin N, ∃ w, predot.store.read tag 7 i = some w ∧ dec tag w = zv i)
    (hzn : ∀ i : Fin N, ∃ w, normed.store.read tag 7 i = some w ∧ dec tag w = zv i)
    (hnorm : exec I (nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (IExp.const N)).run predot =
      some normed)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (vn : Fin N → ℝ) (bn : ℝ),
      exec I (do
        copyv tag 1 (IExp.const N * IExp.var j) 5 0 (IExp.const N)
        ifThenElse tag .eq ⟨3, IExp.var j + 1⟩ ⟨8, 0⟩
          (forRange (IExp.const N) fun i =>
            ins (.lit tag ⟨1, IExp.const N * (IExp.var j + 1) + IExp.var i⟩ 0)) (do
            copyv tag 7 0 1 (IExp.const N * (IExp.var j + 1)) (IExp.const N)
            rscl tag ⟨3, IExp.var j + 1⟩ 1
              (IExp.const N * (IExp.var j + 1)) (IExp.const N))).run normed = some out ∧
      StoreContext tag dec N q (j + 1) A b (Function.update v (j + 2) vn)
        (Function.update α (j + 1) an) (Function.update β (j + 1) bn) s out.store storedMatrix ∧
      0 ≤ bn ∧ (bn = 0 ↔ zv = 0) ∧ (bn = 0 → vn = 0) ∧
      (bn ≠ 0 → |‖WithLp.toLp 2 vn‖ ^ 2 - 1| ≤
        lanczosImplementationRoundoffBound N (u tag)) ∧
      ‖WithLp.toLp 2 (zv - bn • vn)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * ‖WithLp.toLp 2 zv‖ := by
  let xs : ℕ → ℝ := fun i => if hi : i < N then zv ⟨i, hi⟩ else 0
  have hxs : (fun i : Fin N => xs i) = zv := by funext i; simp [xs]
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N (h.nonneg trivial) hsmall
  obtain ⟨ready, hcopy, shcopy, hprev, fcopy⟩ := exec_rounded_previous_copy I hc tag normed hs
  have hdst : ∃ w store, predot.store.write tag 3 (j + 1) w = some store := by
    obtain ⟨w, _, _⟩ := hp.zero
    exact ⟨w, Store.exists_write_eq_some_of_getElem?_shape w
      (by rw [hp.shape]; rfl) (by omega)⟩
  have hy (i : ℕ) (hi : i < N) : ∃ len,
      ready.store.shape[1]? = some (tag, len) ∧ N * (j + 1) + i < len := by
    refine ⟨N * (q + 1), ?_, ?_⟩
    · rw [shcopy, hs.shape]
      rfl
    · calc
        N * (j + 1) + i < N * (j + 1) + N := Nat.add_lt_add_left hi _
        _ = N * (j + 2) := by ring
        _ ≤ N * (q + 1) := Nat.mul_le_mul_left N (by omega)
  obtain ⟨out, w, W, hg, shg, _, hrout, hbn, _, hbzero, hvout, fg,
      hvzero, hvunit, hres, _⟩ := h.exec_guarded_copyv_rscl_of_nrm2_execution I tag hz hc
    predot normed ready ⟨3, IExp.var j + 1⟩ ⟨8, 0⟩ 7 1 0
    (IExp.const N * (IExp.var j + 1)) (IExp.const N) xs hwin.1 hwin.2.2.1
    (by intro i hi; change i < N at hi; simpa [xs, hi] using hzp ⟨i, hi⟩)
    (by
      intro i hi
      change i < N at hi
      rw [show ready.store.read tag 7 (IExp.eval 0 + i) = normed.store.read tag 7 i by
        simpa using fcopy tag 7 i (by omega)]
      simpa only [xs, dif_pos hi] using hzn ⟨i, hi⟩)
    (by simp) (by omega) (by simp) hdst (by simpa using hy) hnorm
    (by simpa using fcopy tag 3 (j + 1) (by omega))
    (by
      change ∃ w, ready.store.read tag 8 0 = some w ∧ dec tag w = 0
      rw [fcopy tag 8 0 (by omega)]
      exact hs.zero)
  have hff (p : P) (k i : ℕ) (hk : k ≠ 5)
      (hi : k = 1 → i < N * (j + 1) ∨ N * (j + 2) ≤ i) :
      out.store.read p k i = normed.store.read p k i := by
    refine (fg p k i ?_).trans (fcopy p k i hk)
    by_cases he : k = 1
    · rcases hi he with hlt | hge
      · exact Or.inr (Or.inl (by simpa using hlt))
      · right; right
        simpa only [IExp.eval_mul, IExp.eval_const, IExp.eval_add, IExp.eval_var,
          IExp.eval_one, Nat.mul_add, Nat.mul_one, Nat.mul_succ, Nat.add_assoc] using hge
    · exact Or.inl he
  refine ⟨out, (fun i => dec tag (W i)), dec tag w, ?_,
    hs.succ_of_commit _ an _ (shg.trans shcopy) hff ?_ ?_ ?_ ?_, hbn, ?_, hvzero, ?_, ?_⟩
  · rw [exec_run_bind I (b := copyv tag 1 (IExp.const N * IExp.var j) 5 0
      (IExp.const N)) (fun _ => rfl), hcopy, Option.bind_some]
    exact hg
  · intro i
    exact ⟨W i, by simpa using hvout i, rfl⟩
  · rw [hff tag 2 j (by omega) (by omega)]
    exact han
  · exact ⟨w, hrout, rfl⟩
  · intro i
    rw [fg tag 5 i (Or.inl (by omega))]
    exact hprev i
  · change dec tag w = 0 ↔ (fun i : Fin N => xs i) = 0 at hbzero
    rwa [hxs] at hbzero
  · intro hne
    exact (hvunit hne).trans
      (normalizationRoundingFactor_le_lanczosImplementationRoundoffBound N
        (h.nonneg trivial) hsmall)
  · have heq : (fun i : Fin N => xs i - dec tag w * dec tag (W i)) =
        zv - dec tag w • (fun i : Fin N => dec tag (W i)) := by
      ext i
      simp [xs]
    change ‖WithLp.toLp 2 (fun i : Fin N => xs i - dec tag w * dec tag (W i))‖ ≤
      _ * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at hres
    rw [heq, hxs] at hres
    exact hres.trans (mul_le_mul_of_nonneg_right hwin.2.2.2.2 (norm_nonneg _))

end NLAlib.LanczosImplementation
