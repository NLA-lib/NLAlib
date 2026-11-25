/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SchurUpdate
public import NLAlib.Computation.BLAS.RankOneUnderflow
public import NLAlib.Matrix.Perturbation.SchurMixedError

/-!
# Finite-range saved-pivot Schur updates

Numerical entry and pivot bounds control every exact scalar result before execution. The
actual unchanged builder succeeds, including its rounded minus-one literal and reciprocal,
while additive underflow remains visible in its error witnesses.

## Main results

* `NLAlib.Computation.IsArithErrSem.exec_schurStep`: actual finite-range success and full frame.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

namespace SchurUnderflow

omit [DecidableEq P] [AddMonoid C] in
private theorem exists_coefficient {u τ : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (I : Interp P ι K C)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem)
    (p : P) (pivot : K) {m Ω : ℝ} (hu : 0 ≤ u p) (hτ : 0 ≤ τ p)
    (hm : 0 < m) (hp : m ≤ dec p pivot) (hrange : ∀ a, |a| ≤ Ω → safe p a)
    (hminus : ∃ ell, I.sem.lit p (-1) = some ell ∧ AbsRelErr (u p) (τ p) (-1) (dec p ell))
    (hcr : (1 + u p + τ p) / m ≤ Ω) :
    ∃ ell c, I.sem.lit p (-1) = some ell ∧ I.sem.bin p .div ell pivot = some c ∧
      AbsRelErr (u p) (τ p) (-1) (dec p ell) ∧
      AbsRelErr (u p) (τ p) (dec p ell / dec p pivot) (dec p c) ∧
      |dec p c| ≤ (1 + u p) * (1 + u p + τ p) / m + τ p := by
  obtain ⟨ell, hellrun, hell⟩ := hminus
  have hp0 : 0 < dec p pivot := hm.trans_le hp
  have hellabs : |dec p ell| ≤ 1 + u p + τ p := by simpa using hell.abs_le
  have hdiv : |dec p ell / dec p pivot| ≤ (1 + u p + τ p) / m := by
    rw [abs_div, abs_of_pos hp0]
    exact div_le_div₀ (by positivity) hellabs hm hp
  obtain ⟨c, hcrun⟩ := h.bin_ok p .div ell pivot trivial (fun _ => hp0.ne')
    (hrange _ (hdiv.trans hcr))
  have hc := h.bin_err p .div ell pivot c trivial hcrun
  refine ⟨ell, c, hellrun, hcrun, hell, hc, ?_⟩
  calc |dec p c| ≤ (1 + u p) * |dec p ell / dec p pivot| + τ p := hc.abs_le
       _ ≤ (1 + u p) * ((1 + u p + τ p) / m) + τ p := by gcongr
       _ = (1 + u p) * (1 + u p + τ p) / m + τ p := by ring

private theorem exec_schurBody (I : Interp P ι K C) {u τ : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop}
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem) (p : P)
    (initial : Store P K) (st : St P K C) (n : IExp ℕ) (R : ℕ) (off pivot : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : pivot.eval < n.eval)
    (hM : HoldsDecoded initial dec p R off.eval M)
    {H m Ω : ℝ} (hu : 0 ≤ u p) (hτ : 0 ≤ τ p) (hH : 0 ≤ H) (hm : 0 < m)
    (hp : m ≤ M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩) (hMs : ∀ i j, |M i j| ≤ H)
    (hrange : ∀ a, |a| ≤ Ω → safe p a)
    (hminus : ∃ ell, I.sem.lit p (-1) = some ell ∧ AbsRelErr (u p) (τ p) (-1) (dec p ell))
    (hcr : (1 + u p + τ p) / m ≤ Ω)
    (hct : ((1 + u p) * (1 + u p + τ p) / m + τ p) * H ≤ Ω)
    (hcq : H * ((1 + u p) * ((1 + u p) * (1 + u p + τ p) / m + τ p) * H + τ p) ≤ Ω)
    (hcz : H + ((1 + u p) * H *
      ((1 + u p) * ((1 + u p) * (1 + u p + τ p) / m + τ p) * H + τ p) + τ p) ≤ Ω)
    (hst : st.store = initial.push (p, Array.replicate (2 * n.eval + 1) none)) :
    ∃ (out : St P K C) (W : Array K) (ell c : ℝ) (t : Fin n.eval → ℝ)
      (q : Matrix (Fin n.eval) (Fin n.eval) ℝ),
      exec I (do
        prepareSchur p n R initial.size off pivot
        ger p n n ⟨initial.size, 2 * n⟩ initial.size 0 initial.size n R off).run st = some out ∧
      W.size = n.eval * n.eval ∧ initial.writeBlock p R off.eval W = some out.store.pop ∧
      AbsRelErr (u p) (τ p) (-1) ell ∧
      AbsRelErr (u p) (τ p) (ell / M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩) c ∧
      (∀ j, AbsRelErr (u p) (τ p) (c * M ⟨pivot.eval, hk⟩ j) (t j)) ∧
      ∀ i j, AbsRelErr (u p) (τ p) (M i ⟨pivot.eval, hk⟩ * t j) (q i j) ∧
        AbsRelErr (u p) (τ p) (M i j + q i j)
          (unflatten n.eval n.eval (W.map (dec p)) i j) := by
  classical
  let k : Fin n.eval := ⟨pivot.eval, hk⟩
  choose Mw hMw hdMw using hM
  have hraw : Holds initial p R off.eval Mw := hMw
  have hR : R < initial.size := Store.lt_size_of_read_eq_some (hMw k k)
  have hMp : Holds st.store p R off.eval Mw := fun i j => by
    rw [hst, Store.read_push_of_lt hR]
    exact hMw i j
  obtain ⟨ell, c, hellrun, hcrun, hell, hc, hcabs⟩ := exists_coefficient I h p
    (Mw k k) hu hτ hm (by rwa [hdMw]) hrange hminus hcr
  obtain ⟨mid, hr₁, hsh, hfr, hcol, hrow, hcoeff⟩ := exec_prepareSchur_of_scalar_results
    I p st n R initial.size off pivot Mw hk hMp (Nat.ne_of_lt hR)
    (hst ▸ Store.getElem?_shape_push_size initial p (2 * n.eval + 1)) ell c hellrun hcrun
  have hMm : HoldsDecoded mid.store dec p R off.eval M := fun i j =>
    ⟨Mw i j, (hfr p R _ (Nat.ne_of_lt hR)).trans (hMp i j), hdMw i j⟩
  obtain ⟨out, W, t, q, hWs, hr₂, hw₂, ht, hq⟩ := h.exec_ger I p mid n n
    ⟨initial.size, 2 * n⟩ initial.size 0 initial.size n R off (dec p c)
    (fun i => M i k) (M k) M hu hH (by positivity) hcabs
    (fun i => hMs i k) (hMs k) hMs hrange hct hcq hcz (fun _ => ⟨c, by
      simpa only [IExp.eval_mul, IExp.eval_ofNat] using hcoeff, rfl⟩)
    (fun _ i => ⟨Mw i k, by
      simpa only [IExp.eval_zero, Nat.zero_add] using hcol i, hdMw i k⟩)
    (fun j => ⟨Mw k j, hrow j, hdMw k j⟩) hMm
    (by simp only [blockDisjoint_iff]; exact Or.inl (Nat.ne_of_gt hR))
    (by simp only [blockDisjoint_iff]; exact Or.inl (Nat.ne_of_gt hR))
    (by simp only [blockDisjoint_iff]; exact Or.inl (Nat.ne_of_gt hR))
  have hF : Store.BlockFrame st.store p initial.size R off.eval (n.eval * n.eval)
      mid.store (fun i => mid.store.read p R (off.eval + i)) :=
    ⟨hsh, fun q b i hb _ => hfr q b i hb, fun _ _ => rfl⟩
  have hF' := hF.writeBlock (off := 0) (by simpa only [Nat.add_zero] using hw₂)
    (by rw [Nat.zero_add, hWs])
  obtain ⟨goal, hgoal⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape
    (s := initial) (xs := W) (by intro i hi; exact hraw.writable i (hWs ▸ hi))
  have hFout : Store.BlockFrame
      (initial.push (p, Array.replicate (2 * n.eval + 1) none)) p initial.size R off.eval
      (n.eval * n.eval) out.store (fun i => W[i]?) := by
    exact (hst ▸ hF').congr (fun i hi => by simp only [hWs, Nat.zero_le,
      Nat.zero_add, true_and, if_pos hi, Nat.sub_zero])
  have hpop : out.store.pop = goal := hFout.pop_eq hgoal hWs (fun _ _ => rfl)
  refine ⟨out, W, dec p ell, dec p c, t, q, ?_, hWs, hpop ▸ hgoal, hell, ?_, ht, hq⟩
  · rw [executionComposable_prepareSchur I p n R initial.size off pivot, hr₁, Option.bind_some]
    exact hr₂
  · simpa only [hdMw] using hc

end SchurUnderflow

/-- Input entry and pivot envelopes bound the exact coefficient division, both products and
addition before running the actual saved-pivot Schur builder. Its output witnesses retain the
literal, reciprocal, row-scaling, rank-one and sum mixed errors, with one full matrix write.
The backend's minus-one literal law is explicit; the arithmetic contract alone does not
supply that literal. Arbitrary words and charges are supported. [Higham2002, §2.2]. -/
theorem IsArithErrSem.exec_schurStep {u τ : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop}
    (I : Interp P ι K C)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (R : ℕ) (off pivot : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : pivot.eval < n.eval)
    (hM : HoldsDecoded st.store dec p R off.eval M)
    {H m Ω : ℝ} (hu : 0 ≤ u p) (hτ : 0 ≤ τ p) (hH : 0 ≤ H) (hm : 0 < m)
    (hp : m ≤ M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩) (hMs : ∀ i j, |M i j| ≤ H)
    (hrange : ∀ a, |a| ≤ Ω → safe p a)
    (hminus : ∃ ell, I.sem.lit p (-1) = some ell ∧ AbsRelErr (u p) (τ p) (-1) (dec p ell))
    (hcr : (1 + u p + τ p) / m ≤ Ω)
    (hct : ((1 + u p) * (1 + u p + τ p) / m + τ p) * H ≤ Ω)
    (hcq : H * ((1 + u p) * ((1 + u p) * (1 + u p + τ p) / m + τ p) * H + τ p) ≤ Ω)
    (hcz : H + ((1 + u p) * H *
      ((1 + u p) * ((1 + u p) * (1 + u p + τ p) / m + τ p) * H + τ p) + τ p) ≤ Ω) :
    ∃ (out : St P K C) (W : Array K) (ell c : ℝ) (t : Fin n.eval → ℝ)
      (q : Matrix (Fin n.eval) (Fin n.eval) ℝ),
      exec I (schurStep p n R off pivot).run st = some out ∧
      W.size = n.eval * n.eval ∧ st.store.writeBlock p R off.eval W = some out.store ∧
      AbsRelErr (u p) (τ p) (-1) ell ∧
      AbsRelErr (u p) (τ p) (ell / M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩) c ∧
      (∀ j, AbsRelErr (u p) (τ p) (c * M ⟨pivot.eval, hk⟩ j) (t j)) ∧
      ∀ i j, AbsRelErr (u p) (τ p) (M i ⟨pivot.eval, hk⟩ * t j) (q i j) ∧
        AbsRelErr (u p) (τ p) (M i j + q i j)
          (unflatten n.eval n.eval (W.map (dec p)) i j) := by
  obtain ⟨out, hr, W, ell, c, t, q, hWs, hw, hell, hc, ht, hq⟩ := exists_exec_alloc I p
    (2 * n + 1) (fun work => (do
      prepareSchur p n R work off pivot
      ger p n n ⟨work, 2 * n⟩ work 0 work n R off).run) st
    (fun s => ∃ (W : Array K) (ell c : ℝ) (t : Fin n.eval → ℝ)
      (q : Matrix (Fin n.eval) (Fin n.eval) ℝ),
      W.size = n.eval * n.eval ∧ st.store.writeBlock p R off.eval W = some s ∧
      AbsRelErr (u p) (τ p) (-1) ell ∧
      AbsRelErr (u p) (τ p) (ell / M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩) c ∧
      (∀ j, AbsRelErr (u p) (τ p) (c * M ⟨pivot.eval, hk⟩ j) (t j)) ∧
      ∀ i j, AbsRelErr (u p) (τ p) (M i ⟨pivot.eval, hk⟩ * t j) (q i j) ∧
        AbsRelErr (u p) (τ p) (M i j + q i j) (unflatten n.eval n.eval (W.map (dec p)) i j))
    (fun σ hσ => by
      obtain ⟨out, W, ell, c, t, q, hr, hs⟩ := SchurUnderflow.exec_schurBody I h p st.store
        σ n R off pivot M hk hM hu hτ hH hm hp hMs hrange hminus hcr hct hcq hcz
        (by simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat] using hσ)
      exact ⟨out, hr, W, ell, c, t, q, hs⟩)
  refine ⟨out, W, ell, c, t, q, ?_, hWs, hw, hell, hc, ht, hq⟩
  change exec I (.seq (.alloc p (2 * n + 1) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

/-- The actual finite-range saved-pivot update succeeds and its entrywise defect from the
exact Schur map is bounded by the explicit mixed-error budget, including additive underflow.
The numerical range conditions control every actual instruction before execution. -/
theorem IsArithErrSem.exec_schurStep_abs_sub_le {u τ : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop}
    (I : Interp P ι K C)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (R : ℕ) (off pivot : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : pivot.eval < n.eval)
    (hM : HoldsDecoded st.store dec p R off.eval M)
    {H m Ω : ℝ} (hu : 0 ≤ u p) (hτ : 0 ≤ τ p) (hH : 0 ≤ H) (hm : 0 < m)
    (hp : m ≤ M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩) (hMs : ∀ i j, |M i j| ≤ H)
    (hrange : ∀ a, |a| ≤ Ω → safe p a)
    (hminus : ∃ ell, I.sem.lit p (-1) = some ell ∧ AbsRelErr (u p) (τ p) (-1) (dec p ell))
    (hcr : (1 + u p + τ p) / m ≤ Ω)
    (hct : ((1 + u p) * (1 + u p + τ p) / m + τ p) * H ≤ Ω)
    (hcq : H * ((1 + u p) * ((1 + u p) * (1 + u p + τ p) / m + τ p) * H + τ p) ≤ Ω)
    (hcz : H + ((1 + u p) * H *
      ((1 + u p) * ((1 + u p) * (1 + u p + τ p) / m + τ p) * H + τ p) + τ p) ≤ Ω) :
    ∃ (out : St P K C) (W : Array K),
      exec I (schurStep p n R off pivot).run st = some out ∧
      W.size = n.eval * n.eval ∧ st.store.writeBlock p R off.eval W = some out.store ∧
      ∀ i j, |unflatten n.eval n.eval (W.map (dec p)) i j -
        eliminationStep M ⟨pivot.eval, hk⟩ i j| ≤ schurMixedErrorBound (u p) (τ p) H m := by
  obtain ⟨out, W, ell, c, t, q, hr, hWs, hw, hell, hc, ht, hq⟩ :=
    h.exec_schurStep I p st n R off pivot M hk hM hu hτ hH hm hp hMs hrange hminus
      hcr hct hcq hcz
  refine ⟨out, W, hr, hWs, hw, fun i j => ?_⟩
  have hb := abs_sub_schurUpdate_le_schurMixedErrorBound hu hτ hH hm hp
    (hMs i j) (hMs i ⟨pivot.eval, hk⟩) (hMs ⟨pivot.eval, hk⟩ j)
    hell hc (ht j) (hq i j).1 (hq i j).2
  simpa only [eliminationStep_apply, div_eq_mul_inv, mul_comm] using hb

end NLAlib.Computation
