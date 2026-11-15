/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Recurrence
public import NLAlib.Krylov.FinitePrecision.PCGRunPrefix

/-!
# Rounded PCG prefixes including the initial state

The zero-length case records the actual initializer and its computed pairing. Every positive
prefix is an existing `PCGRun`, with the same matrix, oracle and allowance. Appending a local
rounded step retains the actual endpoint and both adjacent pairings.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.RunPrefix.exists_run` extracts a positive-length run.
* `NLAlib.Krylov.CG.HSPCG.Rounded.RoundBounds.append_prefix` appends actual local bounds.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded

open scoped Matrix

/-- An initialized zero-start PCG prefix. At zero length the state is exactly the initializer
and the computed pairing has its normwise error certificate and is nonnegative. At positive
length the witness is the existing numerical run, with the same problem and oracle. -/
def RunPrefix {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) (O : MatvecOracle P)
    (b : Fin n → ℝ) (e : ℝ) (k : ℕ) (s : PCGState ℝ (Fin n)) (rho : ℝ) : Prop :=
  (k = 0 ∧ s = ⟨0, b, O.mulVec b, O.mulVec b⟩ ∧
    |rho - b ⬝ᵥ O.mulVec b| ≤ e * ‖WithLp.toLp 2 b‖ * ‖WithLp.toLp 2 (O.mulVec b)‖ ∧
    0 ≤ rho) ∨
  ∃ R : PCGRun n k, R.A = A ∧ R.M = P ∧ HEq R.preconditioner O ∧ R.b = b ∧ R.ε = e ∧
    R.state k = s ∧ R.ν k = rho

/-- The exact oracle initializer together with its actual bounded nonnegative pairing is
an initialized prefix of length zero. -/
theorem RunPrefix.zero {n : ℕ} {A P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {b : Fin n → ℝ} {e rho : ℝ}
    (hnu : |rho - b ⬝ᵥ O.mulVec b| ≤
      e * ‖WithLp.toLp 2 b‖ * ‖WithLp.toLp 2 (O.mulVec b)‖) (hn : 0 ≤ rho) :
    RunPrefix A P O b e 0 ⟨0, b, O.mulVec b, O.mulVec b⟩ rho :=
  Or.inl ⟨rfl, rfl, hnu, hn⟩

/-- Every initialized prefix has a nonnegative terminal computed pairing, including the
zero-length prefix and an exact early stop. -/
theorem RunPrefix.pairing_nonneg {n k : ℕ} {A P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {b : Fin n → ℝ} {e rho : ℝ} {s : PCGState ℝ (Fin n)}
    (h : RunPrefix A P O b e k s rho) : 0 ≤ rho := by
  rcases h with ⟨_, _, _, hn⟩ | ⟨R, _, _, _, _, _, _, hn⟩
  · exact hn
  · rw [← hn]
    exact R.ν_last_nonneg

/-- A positive initialized prefix exposes an existing numerical PCG run at its actual
endpoint and computed pairing. -/
theorem RunPrefix.exists_run {n k : ℕ} {A P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {b : Fin n → ℝ} {e rho : ℝ} {s : PCGState ℝ (Fin n)}
    (h : RunPrefix A P O b e k s rho) (hk : 0 < k) :
    ∃ R : PCGRun n k, R.A = A ∧ R.M = P ∧ HEq R.preconditioner O ∧ R.b = b ∧ R.ε = e ∧
      R.state k = s ∧ R.ν k = rho := by
  rcases h with ⟨rfl, _⟩ | h
  · omega
  · exact h

/-- One rounded step appends to an existing positive-length PCG run. The supplied incoming
pairing is that run's terminal pairing; actual operation functionality establishes this
identity when composing execution. The final pairing is allowed to vanish. -/
theorem RoundBounds.exists_extend {n k : ℕ} {em u ed ea : ℝ} (R : PCGRun n k)
    {next : PCGState ℝ (Fin n)} {rho' : ℝ}
    (h : RoundBounds em u ed ea R.A R.preconditioner (R.state k) next (R.ν k) rho')
    (hu : 0 ≤ u) (hd : 0 ≤ ed) (ha : 0 ≤ ea)
    (hem : em ≤ R.ε) (hue : u ≤ R.ε) (hde : ed ≤ R.ε) (hae : ea ≤ R.ε)
    (hlast : 0 ≤ rho') :
    ∃ S : PCGRun n (k + 1), S.A = R.A ∧ S.M = R.M ∧
      HEq S.preconditioner R.preconditioner ∧ S.b = R.b ∧ S.ε = R.ε ∧
      S.state (k + 1) = next ∧ S.ν (k + 1) = rho' := by
  obtain ⟨q, curv, alpha, beta, eg, eb, hmv, hrho, hcurv, _, hc, halpha, heg,
    hbeta, heb, hz, hn', hx, hr, hdir⟩ := h.exists_run_errors hu hd ha hem hue hde hae
  obtain ⟨S, hA, hM, hO, hb, he, hx', hr', hz', hp', hn, _⟩ :=
    R.exists_extend next q rho' curv alpha eg beta eb hrho hcurv hz hn' hlast hmv
      (by simpa only [abs_sub_comm, PCGRun.state] using hc) halpha heg hbeta heb hx hr hdir
  refine ⟨S, hA, hM, hO, hb, he, ?_, ?_⟩
  · simp only [PCGRun.state, hx', hr', hz', hp', Function.update_self]
  · simp only [hn, Function.update_self]

/-- A bounded actual rounded step extends an initialized PCG prefix, including the first
step. Current positivity is contained in the step's proved bounds. The caller supplies the
mathematically derived final nonnegativity; execution success is not a hypothesis. -/
theorem RoundBounds.append_prefix {n k : ℕ} {em u ed ea e : ℝ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {b : Fin n → ℝ}
    {s next : PCGState ℝ (Fin n)} {rho rho' : ℝ}
    (hprefix : RunPrefix A P O b e k s rho)
    (h : RoundBounds em u ed ea A O s next rho rho')
    (hA : A.IsHermitian) (hP : P.PosDef)
    (hu : 0 ≤ u) (hd : 0 ≤ ed) (ha : 0 ≤ ea)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ed ≤ e) (hae : ea ≤ e) (he : e ≤ 1 / 100)
    (hlast : 0 ≤ rho') : RunPrefix A P O b e (k + 1) next rho' := by
  right
  rcases hprefix with ⟨rfl, rfl, _, _⟩ | ⟨R, hRA, hRM, hRO, hRb, hRe, hRs, hRn⟩
  · obtain ⟨q, curv, alpha, beta, eg, eb, hmv, hrho, hcurv, hn, hc, halpha, heg,
      hbeta, heb, hz, hn', hx, hr, hdir⟩ := h.exists_run_errors hu hd ha hem hue hde hae
    let R := PCGRun.ofOneStep n A P O b next q e rho rho' curv alpha eg beta eb hA hP
      (hu.trans hue) he hz hn hn' hlast hrho hcurv hmv
      (by simpa only [abs_sub_comm] using hc) halpha heg hbeta heb
      (by simpa only [WithLp.toLp_zero, norm_zero, zero_add] using hx) hr hdir
    exact ⟨R, rfl, rfl, HEq.rfl, rfl, rfl, by cases next; rfl, rfl⟩
  · cases hRA
    cases hRM
    cases hRO
    cases hRb
    cases hRe
    rw [← hRs, ← hRn] at h
    exact h.exists_extend R hu hd ha hem hue hde hae hlast

end NLAlib.Krylov.CG.HSPCG.Rounded
