/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyRoundingSteps
public import NLAlib.Matrix.Computation.CholeskyFactorization

/-!
# Successful full rounded Cholesky loop

The original input is copied before any output factor writes, so original input and factor
blocks may alias. The zero-dimensional loop reads no inputs and requires no valid handles.

## Main results

* `NLAlib.Computation.CholeskyRounding.exec_body`: the complete existing rounded loop succeeds
  under explicit input spectral and roundoff margins.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Computation.CholeskyRounding

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

private theorem State.empty {dec : P → K → ℝ} {u μ B e : ℝ} {s : Store P K} {p : P}
    {R L lo N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hn : N = 0) :
    State dec u μ B e s p R L lo A N s := by
  refine ⟨⟨_, rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩, ⟨A, ?_, ?_⟩, ?_⟩
  · intro i
    have := i.isLt
    omega
  · intro i
    have := i.isLt
    omega
  · intro i
    have := i.isLt
    omega

/-- The complete existing Cholesky loop succeeds under standard relative-error semantics
from a positive lower spectral input margin, an input norm bound and a terminal active-entry
budget below half the margin. Input and output blocks may alias. The empty loop reads no
matrix cells. This theorem assumes no successful run or computed-pivot margin. -/
theorem exec_body {dec : P → K → ℝ} {u : P → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    {μ B : ℝ} (hμ : 0 < μ) (hμB : μ ≤ B) (hu1 : u p ≤ 1 / 10)
    (initial : Store P K) (st : St P K C) (n : IExp ℕ) (Ab L : ℕ) (ao lo : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hlo : μ • (1 : Matrix (Fin n.eval) (Fin n.eval) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (hη : choleskySchurErrorBound (u p) B μ n.eval < μ / 2)
    (hinput : HoldsDecoded initial dec p Ab ao.eval A)
    (hL : Writable initial p L lo.eval (n.eval * n.eval))
    (hst : st.store = initial.push (p, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (do
      copyv p Ab ao initial.size 0 (n * n)
      forRange n fun k => do
        choleskyColumnOfResidual p n initial.size L 0 lo (.var k)
        forRange (IExp.var k) fun i => ins (.lit p ⟨L, lo + n * IExp.var k + IExp.var i⟩ 0)
        schurStep p n initial.size 0 (.var k)).run st = some out ∧
      State dec (u p) μ B
        ((2 * (1 + B / μ) * choleskySchurErrorBound (u p) B μ n.eval + 16 * u p * B) / Real.sqrt μ)
        st.store p initial.size L lo.eval A n.eval out.store := by
  by_cases hn : n.eval = 0
  · exact ⟨st, exec_choleskyBody_of_eval_eq_zero I p st n Ab initial.size L ao lo hn,
      State.empty A hn⟩
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
  have hstart : State dec (u p) μ B
      ((2 * (1 + B / μ) * choleskySchurErrorBound (u p) B μ n.eval + 16 * u p * B) / Real.sqrt μ)
      st.store p initial.size L lo.eval A 0 s₁.store := by
    refine ⟨⟨_, hsh, fun q b i hb _ => hframe q b i hb, fun _ _ => rfl⟩,
      ⟨A, hR₁, ?_⟩, fun _ _ hj => by omega⟩
    intro i j _ _
    simp only [gaussState_zero, sub_self, abs_zero, choleskySchurErrorBound]
    exact le_rfl
  obtain ⟨out, hr₂, hs⟩ := exists_exec_loop_eq_some_of_forall I
    (fun k σ => State dec (u p) μ B
      ((2 * (1 + B / μ) * choleskySchurErrorBound (u p) B μ n.eval + 16 * u p * B) / Real.sqrt μ)
      st.store p initial.size L lo.eval A k σ.store) hstart
    (fun k hk σ hσ => exec_iteration I h p hμ hμB hu1 st.store n initial.size L lo A
      hlo hscale hη (Nat.ne_of_gt hLb) hL' k hk σ hσ)
  refine ⟨out, ?_, hs⟩
  rw [exec_run_bind I (b := copyv p Ab ao initial.size 0 (n * n)) (fun _ => rfl), hr₁,
    Option.bind_some]
  change exec I (.seq (.loop n _) .skip) s₁ = some out
  rw [exec_seq_skip]
  exact hr₂

end NLAlib.Computation.CholeskyRounding
