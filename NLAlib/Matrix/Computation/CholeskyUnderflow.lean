/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.Cholesky
public import NLAlib.Computation.Underflow
public import NLAlib.Computation.BLAS.RoundingErrors

/-!
# Finite-range Cholesky square root and column normalization

A positive pivot margin and a mixed-error lower bound for the rounded square root control
the exact quotient range before every division. The backend's in-range square-root law is
explicit because the arithmetic-only contract does not include square roots.

## Main results

* `NLAlib.Computation.IsArithErrSem.exec_choleskyColumn`: success, both exact block writes,
  and the actual mixed square-root and division witnesses.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The actual Cholesky column succeeds under mixed arithmetic errors when the stored pivot
is at least $m>0$, the exact root and quotients fit the finite range, and
$(1-u_p)\sqrt m-\tau_p>0$. The output root stays above that lower bound. Both output blocks
have their exact net writes, with arbitrary offsets, word carriers and charge monoids.
The divisor singleton and vector output must be disjoint; the pivot source may alias them.
The backend square-root success and mixed accuracy law is explicit. -/
theorem IsArithErrSem.exec_choleskyColumn {u τ : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop}
    (I : Interp P ι K C)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem) (p : P)
    (st : St P K C) (pivot diag : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ)
    (a : ℝ) (xs : ℕ → ℝ) {m H Ω : ℝ} (hu1 : u p < 1)
    (hm : 0 < m) (ha : m ≤ a) (haH : a ≤ H)
    (hxs : ∀ i < n.eval, |xs i| ≤ H) (hrange : ∀ b, |b| ≤ Ω → safe p b)
    (hsqrt : ∀ v, 0 ≤ dec p v → |Real.sqrt (dec p v)| ≤ Ω →
      ∃ d, I.sem.un p .sqrt v = some d ∧ AbsRelErr (u p) (τ p) (Real.sqrt (dec p v)) (dec p d))
    (hsr : Real.sqrt H ≤ Ω) (hdmin : 0 < (1 - u p) * Real.sqrt m - τ p)
    (hqr : H / ((1 - u p) * Real.sqrt m - τ p) ≤ Ω)
    (hp : ∃ v, st.store.read p pivot.buf pivot.idx.eval = some v ∧ dec p v = a)
    (hx : ∀ i < n.eval, ∃ v, st.store.read p x (xo.eval + i) = some v ∧ dec p v = xs i)
    (hd : Writable st.store p diag.buf diag.idx.eval 1)
    (hdis : blockDisjoint (diag.buf, diag.idx.eval, 1) (x, xo.eval, n.eval) = true) :
    ∃ (out : St P K C) (d : K) (W : ℕ → K),
      exec I (choleskyColumn p pivot diag x xo n).run st = some out ∧
      st.store.writeBlocks p [(diag.buf, diag.idx.eval, 1), (x, xo.eval, n.eval)]
        [#[d], (List.range n.eval).toArray.map W] = some out.store ∧
      (1 - u p) * Real.sqrt m - τ p ≤ dec p d ∧
      AbsRelErr (u p) (τ p) (Real.sqrt a) (dec p d) ∧
      ∀ i < n.eval, AbsRelErr (u p) (τ p) (xs i / dec p d) (dec p (W i)) := by
  obtain ⟨v, hp, hda⟩ := hp
  have ha0 : 0 ≤ a := hm.le.trans ha
  have hH : 0 ≤ H := ha0.trans haH
  obtain ⟨d, hroot, hdroot⟩ := hsqrt v (hda ▸ ha0) (by
    rw [hda, abs_of_nonneg (Real.sqrt_nonneg a)]
    exact (Real.sqrt_le_sqrt haH).trans hsr)
  rw [hda] at hdroot
  have hdlower : (1 - u p) * Real.sqrt m - τ p ≤ dec p d := by
    have he := (le_abs_self (Real.sqrt a - dec p d)).trans hdroot.abs_sub_le
    rw [abs_of_nonneg (Real.sqrt_nonneg a)] at he
    have hlo := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ha) (sub_nonneg.mpr hu1.le)
    linarith
  have hdpos : 0 < dec p d := hdmin.trans_le hdlower
  obtain ⟨len, hlen, hlt⟩ := hd 0 (by omega)
  obtain ⟨mid, hm⟩ := Store.exists_write_eq_some_of_getElem?_shape d hlen (by simpa using hlt)
  have hne : ∀ i < n.eval, x ≠ diag.buf ∨ xo.eval + i ≠ diag.idx.eval := by
    intro i hi
    have hh := blockDisjoint_iff.mp hdis
    dsimp only at hh
    omega
  have hx' : ∀ i < n.eval, ∃ v, mid.read p x (xo.eval + i) = some v ∧ dec p v = xs i := by
    intro i hi
    obtain ⟨w, hw, hdw⟩ := hx i hi
    exact ⟨w, (Store.read_of_write_eq_some_of_ne hm (hne i hi)).trans hw, hdw⟩
  let ready : St P K C :=
    { st with store := mid, cnt := st.cnt + I.charge (.un p .sqrt) }
  obtain ⟨out, W, hr, hw, hW⟩ := h.exec_rscl I p ready diag x xo n (dec p d) xs hdpos.ne'
    ⟨d, Store.read_of_write_eq_some hm, rfl⟩ hx'
    (fun he i hi => ((hne i hi).resolve_left (fun hne => hne he.symm)).symm)
    (fun i hi => hrange _ (by
      rw [abs_div, abs_of_pos hdpos]
      exact (div_le_div₀ hH (hxs i hi) hdmin hdlower).trans hqr))
  have hm' : st.store.writeBlock p diag.buf diag.idx.eval #[d] = some mid := by
    simpa [Store.writeBlock] using hm
  refine ⟨out, d, W, ?_, ?_, hdlower, hdroot, hW⟩
  · change exec I (.seq (.seq (.instr (.un p .sqrt diag pivot))
      (rscl p diag x xo n).run) .skip) st = some out
    rw [exec_seq_skip]
    exact (exec_seq_instr_un I hp hroot hm).trans hr
  · exact Store.writeBlocks_pair_eq_some_iff.mpr
      ⟨by simp, by simp, mid, hm', hw⟩


end NLAlib.Computation
