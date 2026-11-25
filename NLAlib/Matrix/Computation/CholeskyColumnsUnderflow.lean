/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyColumnsRounding
public import NLAlib.Matrix.Computation.CholeskyUnderflow

/-!
# Finite-range Cholesky columns from a stored residual

The actual copied-column normalization and upper-prefix zeroing succeed from numerical
pivot/root/quotient margins under mixed arithmetic errors. Their net write is a full column.

## Main results

* `NLAlib.Computation.IsArithErrSem.exec_choleskyColumnOfResidual`: copied-column success.
* `NLAlib.Computation.IsArithErrSem.exec_choleskyColumnOfResidual_zero_upper`: success and
  exact decoded triangular prefix zeros.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Numerical pivot, root and quotient range margins suffice for the actual copied-column
operation to succeed with mixed errors. The full packed write preserves the copied prefix,
and exposes the actual square-root lower bound and root/division error witnesses. -/
theorem IsArithErrSem.exec_choleskyColumnOfResidual {u τ : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop}
    (I : Interp P ι K C)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (R L : ℕ) (ro lo k : IExp ℕ)
    (B : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hB : HoldsDecoded st.store dec p R ro.eval B) (hRL : R ≠ L)
    (hu : u p < 1) {m H Ω : ℝ} (hm : 0 < m)
    (hp : m ≤ B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩) (hMs : ∀ i j, |B i j| ≤ H)
    (hrange : ∀ b, |b| ≤ Ω → safe p b)
    (hsqrt : ∀ v, 0 ≤ dec p v → |Real.sqrt (dec p v)| ≤ Ω →
      ∃ d, I.sem.un p .sqrt v = some d ∧ AbsRelErr (u p) (τ p) (Real.sqrt (dec p v)) (dec p d))
    (hsr : Real.sqrt H ≤ Ω) (hdmin : 0 < (1 - u p) * Real.sqrt m - τ p)
    (hqr : H / ((1 - u p) * Real.sqrt m - τ p) ≤ Ω)
    (hL : Writable st.store p L (lo.eval + n.eval * k.eval) n.eval) :
    ∃ (out : St P K C) (W : Fin n.eval → K),
      exec I (choleskyColumnOfResidual p n R L ro lo k).run st = some out ∧
      st.store.writeBlock p L (lo.eval + n.eval * k.eval) (Array.ofFn W) = some out.store ∧
      (∀ i, i.val < k.eval → dec p (W i) = B i ⟨k.eval, hk⟩) ∧
      (1 - u p) * Real.sqrt m - τ p ≤ dec p (W ⟨k.eval, hk⟩) ∧
      AbsRelErr (u p) (τ p) (Real.sqrt (B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)) (dec p (W ⟨k.eval, hk⟩)) ∧
      ∀ i, k.eval < i.val → AbsRelErr (u p) (τ p)
        (B i ⟨k.eval, hk⟩ / dec p (W ⟨k.eval, hk⟩)) (dec p (W i)) := by
  classical
  choose Mw hMw hdMw using hB
  change Matrix (Fin n.eval) (Fin n.eval) K at Mw
  let r : Fin n.eval := ⟨k.eval, hk⟩
  obtain ⟨s₁, hr₁, hsh₁, hrds, hfr₁⟩ := exec_copyv_block I p st n R L
    (ro + n * k) (lo + n * k) (fun i hi => ⟨Mw ⟨i, hi⟩ r, by
      simpa only [IExp.eval_add, IExp.eval_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hMw ⟨i, hi⟩ r⟩) hRL hL
  have hread : ∀ i : Fin n.eval,
      s₁.store.read p L (lo.eval + n.eval * k.eval + i.val) = some (Mw i r) := by
    intro i
    exact (hrds i i.isLt).trans (by simpa only [IExp.eval_add, IExp.eval_mul,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hMw i r)
  have hdiag : Writable s₁.store p L (lo + k + n * k).eval 1 := by
    intro i hi
    have hh := hL k.eval hk
    rw [hsh₁]
    simpa [show i = 0 by omega, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  let xs : ℕ → ℝ := fun i => if hi : i < n.eval then B ⟨i, hi⟩ r else 0
  obtain ⟨out, d, ws, hr₂, hw, hdpos, hdrel, hwrel⟩ := h.exec_choleskyColumn I p s₁
    ⟨R, ro + k + n * k⟩ ⟨L, lo + k + n * k⟩ L
    (lo + (k + 1) + n * k) (n - (k + 1)) (B r r)
    (fun i => xs (k.eval + 1 + i)) hu hm hp ((le_abs_self _).trans (hMs r r))
    (by
      intro i hi
      have hi' : k.eval + 1 + i < n.eval := by change i < n.eval - (k.eval + 1) at hi; omega
      simpa only [xs, dif_pos hi'] using hMs ⟨k.eval + 1 + i, hi'⟩ r)
    hrange hsqrt hsr hdmin hqr
    ⟨Mw r r, (hfr₁ p R _ (Or.inl hRL)).trans (by simpa only [IExp.eval_add,
      IExp.eval_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hMw r r), hdMw r r⟩
    (by
      intro i hi
      have hi' : k.eval + 1 + i < n.eval := by change i < n.eval - (k.eval + 1) at hi; omega
      exact ⟨Mw ⟨k.eval + 1 + i, hi'⟩ r,
        by simpa [IExp.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hread ⟨k.eval + 1 + i, hi'⟩, by simpa [xs, hi'] using hdMw ⟨k.eval + 1 + i, hi'⟩ r⟩)
    hdiag (by simp [blockDisjoint_iff])
  obtain ⟨_, _, mid, hm, hf⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
  let W : Fin n.eval → K := fun i =>
    if i.val < k.eval then Mw i r else if i.val = k.eval then d else ws (i.val - (k.eval + 1))
  have hwrite := writeBlock_column_of_normalize (fun i => Mw i r) d ws hk hsh₁ hread
    (by simpa only [IExp.eval_add, IExp.eval_mul] using hfr₁)
    (by simpa [IExp.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm)
    (by simpa [IExp.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf)
  refine ⟨out, W, ?_, hwrite, ?_, ?_, ?_, ?_⟩
  · change exec I (.seq _ .skip) st = some out
    rw [exec_seq_skip]
    have hcomp : ExecutionComposable I (copyv p R (ro + n * k) L (lo + n * k) n) :=
      executionComposable_single I (fun _ => rfl)
    rw [hcomp, hr₁, Option.bind_some]
    exact hr₂
  · intro i hi
    simp only [W, if_pos hi, hdMw, r]
  · simpa [W, r] using hdpos
  · simpa [W, r] using hdrel
  · intro i hi
    have ht : i.val - (k.eval + 1) < n.eval - (k.eval + 1) := by omega
    have he : k.eval + 1 + (i.val - (k.eval + 1)) = i.val := by omega
    simpa [W, show ¬i.val < k.eval by omega, show i.val ≠ k.eval by omega,
      r, xs, he, i.isLt] using hwrel (i.val - (k.eval + 1)) ht

/-- The original full driver's copied-column operation followed by actual zero literals
succeeds and writes exact decoded upper zeros. The mixed-error root lower bound and suffix
division witnesses are preserved, with one full column as the complete net store effect. -/
theorem IsArithErrSem.exec_choleskyColumnOfResidual_zero_upper {u τ : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop}
    (I : Interp P ι K C)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (R L : ℕ) (ro lo k : IExp ℕ)
    (B : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hB : HoldsDecoded st.store dec p R ro.eval B) (hRL : R ≠ L)
    (hu : u p < 1) {m H Ω : ℝ} (hm : 0 < m)
    (hp : m ≤ B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩) (hMs : ∀ i j, |B i j| ≤ H)
    (hrange : ∀ b, |b| ≤ Ω → safe p b)
    (hsqrt : ∀ v, 0 ≤ dec p v → |Real.sqrt (dec p v)| ≤ Ω →
      ∃ d, I.sem.un p .sqrt v = some d ∧ AbsRelErr (u p) (τ p) (Real.sqrt (dec p v)) (dec p d))
    (hsr : Real.sqrt H ≤ Ω) (hdmin : 0 < (1 - u p) * Real.sqrt m - τ p)
    (hqr : H / ((1 - u p) * Real.sqrt m - τ p) ≤ Ω)
    (hL : Writable st.store p L (lo.eval + n.eval * k.eval) n.eval) :
    ∃ (out : St P K C) (W : Fin n.eval → K),
      exec I (do
        choleskyColumnOfResidual p n R L ro lo k
        forRange k fun i => ins (.lit p ⟨L, lo + n * k + IExp.var i⟩ 0)).run st = some out ∧
      st.store.writeBlock p L (lo.eval + n.eval * k.eval) (Array.ofFn W) = some out.store ∧
      (∀ i, i.val < k.eval → dec p (W i) = 0) ∧
      (1 - u p) * Real.sqrt m - τ p ≤ dec p (W ⟨k.eval, hk⟩) ∧
      AbsRelErr (u p) (τ p) (Real.sqrt (B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)) (dec p (W ⟨k.eval, hk⟩)) ∧
      ∀ i, k.eval < i.val → AbsRelErr (u p) (τ p)
        (B i ⟨k.eval, hk⟩ / dec p (W ⟨k.eval, hk⟩)) (dec p (W i)) := by
  obtain ⟨s₁, W, hrun, hw, -, hdpos, hdrel, hrel⟩ :=
    h.exec_choleskyColumnOfResidual I p st n R L ro lo k B hk hB hRL hu hm hp hMs
      hrange hsqrt hsr hdmin hqr hL
  obtain ⟨z, hz, hdz⟩ := h.lit_zero p
  obtain ⟨store, hzero, hsh, hr, hf⟩ := exec_forRange_literal_zero I p z hz s₁ k L (lo + n * k)
    (fun i hi => by
      have hh := (hL.of_shape_eq (Store.shape_of_writeBlock_eq_some hw)) i (by omega)
      simpa only [IExp.eval_add, IExp.eval_mul] using hh)
  let out : St P K C := { s₁ with store := store, cnt := s₁.cnt + k.eval • I.charge (.lit p) }
  have hwrite := writeBlock_column_prefix W z (Nat.le_of_lt hk) hw hsh
    (by simpa only [IExp.eval_add, IExp.eval_mul] using hr)
    (by simpa only [IExp.eval_add, IExp.eval_mul] using hf)
  refine ⟨out, (fun i => if i.val < k.eval then z else W i), ?_, hwrite, ?_, ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := choleskyColumnOfResidual p n R L ro lo k) (fun _ => rfl),
      hrun, Option.bind_some]
    exact hzero
  · intro i hi
    simp only [if_pos hi, hdz]
  · simpa only [lt_self_iff_false, if_false] using hdpos
  · simpa only [lt_self_iff_false, if_false] using hdrel
  · intro i hi
    simpa only [lt_self_iff_false, if_false, if_neg (show ¬i.val < k.eval by omega)] using hrel i hi


end NLAlib.Computation
