/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyRangeSteps
public import NLAlib.Matrix.Computation.CholeskyFactorization

/-!
# Successful full finite-range Cholesky loop

The original input is copied before any output factor writes, so original input and factor
blocks may alias. The zero-dimensional loop reads no inputs and requires no valid handles.

## Main results

* `NLAlib.Computation.CholeskyRange.exec_body`: the complete existing finite-range loop succeeds
  under explicit input spectral and roundoff margins.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Computation.CholeskyRange

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The complete existing Cholesky loop succeeds under mixed errors and finite range from
explicit input numerical conditions and a source spectral band. Input and output blocks may
alias. The empty loop reads no matrix cells. No successful run or computed-pivot margin
is assumed. -/
theorem exec_body {dec : P → K → ℝ} {u τ : P → ℝ} {safe : P → ℝ → Prop}
    (I : Interp P ι K C)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem) (p : P)
    (n : IExp ℕ) {μ B Ω : ℝ} (hc : CholeskyRangeConditions n.eval (u p) (τ p) B μ Ω)
    (hrange : ∀ a, |a| ≤ Ω → safe p a)
    (hminus : ∃ ell, I.sem.lit p (-1) = some ell ∧ AbsRelErr (u p) (τ p) (-1) (dec p ell))
    (hsqrt : ∀ v, 0 ≤ dec p v → |Real.sqrt (dec p v)| ≤ Ω →
      ∃ d, I.sem.un p .sqrt v = some d ∧ AbsRelErr (u p) (τ p) (Real.sqrt (dec p v)) (dec p d))
    (initial : Store P K) (st : St P K C) (Ab L : ℕ) (ao lo : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hlo : μ • (1 : Matrix (Fin n.eval) (Fin n.eval) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (hinput : HoldsDecoded initial dec p Ab ao.eval A)
    (hL : Writable initial p L lo.eval (n.eval * n.eval))
    (hst : st.store = initial.push (p, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (do
      copyv p Ab ao initial.size 0 (n * n)
      forRange n fun k => do
        choleskyColumnOfResidual p n initial.size L 0 lo (.var k)
        forRange (IExp.var k) fun i => ins (.lit p ⟨L, lo + n * IExp.var k + IExp.var i⟩ 0)
        schurStep p n initial.size 0 (.var k)).run st = some out ∧
      State dec (u p) (τ p) μ B
        (choleskyMixedColumnErrorBound (u p) (τ p) B μ
        (choleskyMixedSchurErrorBound (u p) (τ p) B μ n.eval))
        st.store p initial.size L lo.eval A n.eval out.store := by
  by_cases hn : n.eval = 0
  · refine ⟨st, exec_choleskyBody_of_eval_eq_zero I p st n Ab initial.size L ao lo hn, ?_⟩
    refine ⟨⟨_, rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩, ⟨A, ?_, ?_⟩, ?_⟩
    all_goals intro i; have hh := i.isLt; omega
  have hN : 0 < n.eval := Nat.pos_of_ne_zero hn
  have hLb : L < initial.size := hL.lt_size (Nat.mul_pos hN hN)
  obtain ⟨w, hw, _⟩ := hinput ⟨0, hN⟩ ⟨0, hN⟩
  have hAb : Ab < initial.size := Store.lt_size_of_read_eq_some hw
  have hinput' : HoldsDecoded st.store dec p Ab ao.eval A := by
    rw [hst]
    exact hinput.push _
  have hR : Writable st.store p initial.size 0 (n.eval * n.eval) := by
    intro i hi
    exact ⟨n.eval * n.eval, by rw [hst]; exact
      Store.getElem?_shape_push_size initial p (n.eval * n.eval), by omega⟩
  have hL' : Writable st.store p L lo.eval (n.eval * n.eval) := by
    rw [hst]
    exact hL.push _
  obtain ⟨s₁, hr₁, hsh, hR₁, hframe⟩ := exec_copyv_matrix I p st n Ab initial.size ao A
    hinput' (Nat.ne_of_lt hAb) hR
  have hstart : State dec (u p) (τ p) μ B
      (choleskyMixedColumnErrorBound (u p) (τ p) B μ
        (choleskyMixedSchurErrorBound (u p) (τ p) B μ n.eval))
      st.store p initial.size L lo.eval A 0 s₁.store := by
    refine ⟨⟨_, hsh, fun q b i hb _ => hframe q b i hb, fun _ _ => rfl⟩,
      ⟨A, hR₁, ?_⟩, fun _ _ hj => by omega⟩
    intro i j
    simp only [gaussState_zero, sub_self, abs_zero, choleskyMixedSchurErrorBound]
    exact le_rfl
  obtain ⟨out, hr₂, hs⟩ := exists_exec_loop_eq_some_of_forall I
    (fun k σ => State dec (u p) (τ p) μ B
      (choleskyMixedColumnErrorBound (u p) (τ p) B μ
        (choleskyMixedSchurErrorBound (u p) (τ p) B μ n.eval))
      st.store p initial.size L lo.eval A k σ.store) hstart
    (fun k hk σ hσ => exec_iteration I h p n hc hrange hminus hsqrt st.store initial.size L lo A
      hlo hscale (Nat.ne_of_gt hLb) hL' k hk σ hσ)
  refine ⟨out, ?_, hs⟩
  rw [exec_run_bind I (b := copyv p Ab ao initial.size 0 (n * n)) (fun _ => rfl), hr₁,
    Option.bind_some]
  change exec I (.seq (.loop n _) .skip) s₁ = some out
  rw [exec_seq_skip]
  exact hr₂

end NLAlib.Computation.CholeskyRange
