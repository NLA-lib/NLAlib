/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Completion
public import NLAlib.Eigensolvers.Schur.ShiftedTriSolveWrites
public import NLAlib.Matrix.Spectral.TriangularEigenvectors
public import NLAlib.Ops.Profiles.RoundedScalarBlas
public import NLAlib.Ops.Logic.ScalarLoop
public import NLAlib.Eigensolvers.ShiftedQR.RowSolveStorage

/-!
# The eigenvector stage of the dense eigensolver

After a Schur solver has stored $\widehat{\mathbf{U}}$ and an upper triangular
$\widehat{\mathbf{T}}$, the eigenvector stage `NLAlib.Schur.triEigvecStage` computes the
eigenvectors of $\widehat{\mathbf{T}}$ by rounded back substitution with a pivot floor
$s_{\min} = \mathrm{fl}(\rho\,\mathrm{fl}\|\widehat{\mathbf{T}}\|_{\mathsf F})$ (LAPACK `xTREVC`,
`NLAlib.shiftedTriSolve`), normalizes each column and multiplies by $\widehat{\mathbf{U}}$. For
$\widehat{\mathbf{T}} = \mathbf{0}$ it copies $\widehat{\mathbf{U}}$. It meets the normwise
contract `NLAlib.Schur.EigenvectorStageContract`: the columns are approximate eigenvectors of
$\widehat{\mathbf{T}}$ with a gap-free residual
(`NLAlib.IsTriangularEigenbasisApprox.norm_mulVec_col_le`), the floor enters the residual only
when the flag is set, and no pivot is floored when the diagonal gaps exceed
$4\rho\|\widehat{\mathbf{T}}\|_{\mathsf F}$.

## Main definitions

* `NLAlib.Schur.triEigColumn`, `NLAlib.Schur.triEigenvectors`: one column and all columns.
* `NLAlib.Schur.triEigvecStage`: the stage `[N, ne] (T, U, Pe) → (V, G)`.

## Main results

* `NLAlib.Schur.triEigColumn_writes`, `NLAlib.Schur.triEigenvectors_writes`,
  `NLAlib.Schur.triEigenvectors_isTriangularEigenbasisApprox`, `NLAlib.Schur.triEigenvectors_flag`:
  the columns.
* `NLAlib.Schur.triEigvecStage_eigenvectorStageContract`: the stage meets the contract.
* `NLAlib.Schur.triEigvecStage_completes`: the stage completes on any scalar machine.
* `NLAlib.Schur.size_stmtCost_triEigvecStage_le`: its static count is $O(N^3)$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Schur

open Ops
open NLAlib.ShiftedQR (vectorColumn HoldsVector)

variable {O Q : Type}

/-! ### The programs -/

section Program

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **One eigenvector column**: `[N, j] (T, Sm, Y, G) → (Y, G)` runs `NLAlib.shiftedTriSolve` on
column $j$ with the floor `Sm`, stores the unit entry and the zeros below it, and scales the
column by $\mathrm{fl}(1/\hat\nu)$, $\hat\nu$ the rounded norm of the column ($\hat\nu \ge 1$ up to
rounding, because of the unit entry).
Algorithm: dense-eigendecomposition -/
def triEigColumn : Stmt O Q := ops% [N, j] (T, Sm, Y, G) → (Y, G) {
  let Nu ← alloc 1;
  let R ← alloc 1;
  run (shiftedTriSolve (O := O) (Q := Q)) [N, j] (T, Sm, Y, G, Y, G);
  call (Has.inj (ScalarOp.lit 1)) [] () → (Y[2 * (j * N + j)]);
  call (Has.inj (ScalarOp.lit 0)) [] () → (Y[2 * (j * N + j) + 1]);
  for l < N - 1 - j {
    call (Has.inj (ScalarOp.lit 0)) [] () → (Y[2 * (j * N + (j + 1 + l))]);
    call (Has.inj (ScalarOp.lit 0)) [] () → (Y[2 * (j * N + (j + 1 + l)) + 1])
  };
  run (RoundedScalarBlas.nrm2 (Op := O) (Tst := Q)) [2 * N] (Y[2 * (j * N)], Nu);
  call (Has.inj (ScalarOp.lit 1)) [] () → (R);
  call (Has.inj ScalarOp.div) [] (R, Nu) → (R);
  for t < 2 * N {
    call (Has.inj ScalarOp.mul) [] (Y[2 * (j * N) + t], R) → (Y[2 * (j * N) + t])
  }
}

/-- **The eigenvector columns**: `[N] (T, Sm, Y, G) → (Y, G)` runs `NLAlib.Schur.triEigColumn` for
$j = 0, \dots, N - 1$.
Algorithm: dense-eigendecomposition -/
def triEigenvectors : Stmt O Q := ops% [N] (T, Sm, Y, G) → (Y, G) {
  for j < N {
    run (triEigColumn (O := O) (Q := Q)) [N, j] (T, Sm, Y, G, Y, G)
  }
}

/-- **The eigenvector stage**: `[N, ne] (T, U, Pe) → (V, G)` with the floor parameter $\rho$ =
`Pe[0]`. It stores the flag $0$ and the rounded Frobenius norm $\hat s$ of $\mathbf{T}$
(`NLAlib.Schur.frobNormStage`); if $\hat s > 0$, the floor $s_{\min} = \mathrm{fl}(\rho\hat s)$,
the columns `NLAlib.Schur.triEigenvectors` into scratch $\mathbf{Y}$ and $\mathbf{V} =
\mathrm{fl}(\mathbf{U}\mathbf{Y})$ (`NLAlib.matMulOn`); otherwise $\mathbf{V} = \mathbf{U}$
exactly.
Algorithm: dense-eigendecomposition -/
def triEigvecStage : Stmt O Q := ops% [N, ne] (T, U, Pe) → (V, G) {
  let S ← alloc 1;
  let Sm ← alloc 1;
  let Y ← alloc (2 * (N * N));
  call (Has.inj IndexOp.lit) [0] () → (G);
  run (frobNormStage (O := O) (Q := Q)) [N] (T, S);
  if (Has.inj CmpTst.isPos) [] (S) {
    call (Has.inj ScalarOp.mul) [] (Pe, S) → (Sm);
    run (triEigenvectors (O := O) (Q := Q)) [N] (T, Sm, Y, G, Y, G);
    run (matMulOn (O := O) (Q := Q)) [N, N, N, N, N, N, 0] (U, Y, V)
  } else {
    run (PairMatrix.copyRoutine (Op := O) (Tst := Q)) [N, N] (U, V)
  }
}

end Program

/-! ### Scaling a backward solution -/

section Scaling

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A rounded scaling of a componentwise backward solution**: if $\mathbf{y}$ is a
componentwise backward solution of $\mathbf{M}\mathbf{y} = \mathbf{0}$ with $(\varepsilon,
\sigma)$ and every $z_k$ is within $\delta\lvert cy_k\rvert$ of $cy_k$, $0 \le \delta < 1$, then
$\mathbf{z}$ is one with $((\varepsilon + \delta)/(1 - \delta), \sigma/(1 - \delta))$. -/
private theorem isComponentwiseBackwardSolution_of_norm_sub_smul_le {ε σ δ : ℝ}
    {M : Matrix n n ℂ} {y z : n → ℂ} {c : ℂ} (h : IsComponentwiseBackwardSolution ε σ M 0 y)
    (hδ0 : 0 ≤ δ) (hδ : δ < 1) (hz : ∀ k, ‖z k - c * y k‖ ≤ δ * ‖c * y k‖) :
    IsComponentwiseBackwardSolution ((ε + δ) / (1 - δ)) (σ / (1 - δ)) M 0 z := by
  obtain ⟨Δ, hΔ, hsol⟩ := h
  have h1δ : 0 < 1 - δ := by linarith
  have hzlo : ∀ k, (1 - δ) * ‖c * y k‖ ≤ ‖z k‖ := fun k => by
    have := norm_sub_norm_le (c * y k) (z k)
    rw [norm_sub_rev] at this
    linarith [hz k]
  have hz0 : ∀ k, c * y k = 0 → z k = 0 := fun k h0 => by
    have := hz k; rw [h0, norm_zero, mul_zero, sub_zero] at this
    exact norm_le_zero_iff.mp this
  have hzne : ∀ k, c * y k ≠ 0 → z k ≠ 0 := fun k hne h0 => by
    have := hzlo k
    rw [h0, norm_zero] at this
    have : 0 < (1 - δ) * ‖c * y k‖ := mul_pos h1δ (norm_pos_iff.mpr hne)
    linarith
  refine ⟨fun i k => if c * y k = 0 then 0 else (M i k + Δ i k) * (c * y k) / z k - M i k,
    fun i k => ?_, ?_⟩
  · have hb := hΔ i k
    have hRHS : (ε + δ) / (1 - δ) * ‖M i k‖ + (if i = k then σ / (1 - δ) else 0) =
        ((ε * ‖M i k‖ + (if i = k then σ else 0)) + δ * ‖M i k‖) / (1 - δ) := by
      split_ifs <;> field_simp <;> ring
    rw [hRHS]
    have hM := norm_nonneg (M i k)
    change ‖if c * y k = 0 then 0 else (M i k + Δ i k) * (c * y k) / z k - M i k‖ ≤ _
    by_cases h0 : c * y k = 0
    · rw [if_pos h0, norm_zero]
      exact div_nonneg (by nlinarith [norm_nonneg (Δ i k)]) h1δ.le
    · have hzk := hzne k h0
      have e : (M i k + Δ i k) * (c * y k) / z k - M i k =
          (Δ i k * (c * y k) + M i k * (c * y k - z k)) / z k := by
        field_simp; ring
      rw [if_neg h0, e, norm_div, div_le_div_iff₀ (norm_pos_iff.mpr hzk) h1δ]
      have hcy := norm_pos_iff.mpr h0
      have h2 : ‖Δ i k * (c * y k) + M i k * (c * y k - z k)‖ ≤
          (‖Δ i k‖ + δ * ‖M i k‖) * ‖c * y k‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul (Δ i k), norm_mul (M i k), norm_sub_rev (c * y k)]
        nlinarith [mul_le_mul_of_nonneg_left (hz k) hM]
      calc ‖Δ i k * (c * y k) + M i k * (c * y k - z k)‖ * (1 - δ)
          ≤ (‖Δ i k‖ + δ * ‖M i k‖) * ‖c * y k‖ * (1 - δ) :=
            mul_le_mul_of_nonneg_right h2 h1δ.le
        _ = (‖Δ i k‖ + δ * ‖M i k‖) * ((1 - δ) * ‖c * y k‖) := by ring
        _ ≤ (‖Δ i k‖ + δ * ‖M i k‖) * ‖z k‖ :=
            mul_le_mul_of_nonneg_left (hzlo k) (by positivity)
        _ ≤ (ε * ‖M i k‖ + (if i = k then σ else 0) + δ * ‖M i k‖) * ‖z k‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  · funext i
    have hi := congrFun hsol i
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Pi.zero_apply] at hi ⊢
    have e : ∀ k, (M i k + (if c * y k = 0 then 0 else
        (M i k + Δ i k) * (c * y k) / z k - M i k)) * z k = c * ((M i k + Δ i k) * y k) := by
      intro k
      split_ifs with h0
      · rw [hz0 k h0, mul_zero]
        have : c = 0 ∨ y k = 0 := mul_eq_zero.mp h0
        rcases this with hc | hy
        · rw [hc, zero_mul]
        · rw [hy, mul_zero, mul_zero]
      · have hzk := hzne k h0
        field_simp
        ring
    refine (Finset.sum_congr rfl fun k _ => e k).trans ?_
    rw [← Finset.mul_sum, hi, mul_zero]

end Scaling

/-! ### The columns -/

section Columns

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The column before its scaling** on the machine `M`: the computed entries above position
$j$, the pair of the literals $1$, $0$ at $j$ and pairs of the literal $0$ below it. -/
noncomputable def triEigColumnWord (M : Machine ℝ) {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (smin : ℝ) (j : ℕ) : Fin N → ℂ :=
  fun i => if (i : ℕ) < j then (shiftedTriSolveWord M T smin j j).1 i
    else if (i : ℕ) = j then ⟨M.lit 1, M.lit 0⟩ else ⟨M.lit 0, M.lit 0⟩

/-- The environment of a column after its two scratch cells. -/
private def colEnv (N j : ℕ) (t sm y g : ℕ × ℕ) (L : ℕ) : Env :=
  ⟨[N, j, t.2, sm.2, y.2, g.2, y.2, g.2], [t.1, sm.1, y.1, g.1, y.1, g.1, L, L + 1]⟩

/-- The end of a column: its rounded norm, the rounded reciprocal and the scaling. -/
private def colTail : Stmt O Q :=
  .seq (.frame [.const 2 * .var 0] [⟨2, .var 4 + .const 2 * (.var 1 * .var 0)⟩, ⟨6, .const 0⟩]
    (RoundedScalarBlas.nrm2 (Op := O) (Tst := Q)).body) <|
  .seq (.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨7, .const 0⟩]) <|
  .seq (.call (Has.inj ScalarOp.div) [] [⟨7, .const 0⟩, ⟨6, .const 0⟩] [⟨7, .const 0⟩]) <|
  .loop (.const 2 * .var 0) (.call (Has.inj ScalarOp.mul) []
    [⟨2, .var 4 + .const 2 * (.var 1 * .var 0) + .var 8⟩, ⟨7, .const 0⟩]
    [⟨2, .var 4 + .const 2 * (.var 1 * .var 0) + .var 8⟩])

omit [Has IndexOp O] [Has CmpTst Q] in
/-- The end of a column stores the words of the column times the rounded reciprocal of a norm
word `ν` with the property `Pν` of the rounded norm. -/
private theorem colTail_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {N j : ℕ} {t sm y g : ℕ × ℕ} {L : ℕ} {w : Fin N → ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    {Pν : ℝ → Prop} (hyL : y.1 < L) (hlen : μ.store.length = L + 2)
    (hl0 : μ.store.len L = 1) (hl1 : μ.store.len (L + 1) = 1)
    (hw : μ.store.readBlock y.1 (y.2 + 2 * (j * N)) (2 * N) = some (matrixWords (vectorColumn w)))
    (hν : ∀ m : Mem ℝ, m.Live [(y.1, y.2 + 2 * (j * N)), (L, 0)] →
      m.store.readBlock y.1 (y.2 + 2 * (j * N)) (2 * N) =
        some (matrixWords (vectorColumn w)) → 0 < m.store.len L →
      Writes .total I τ (RoundedScalarBlas.nrm2 (Op := O) (Tst := Q)).body
        (Env.frame [2 * N] [(y.1, y.2 + 2 * (j * N)), (L, 0)]) (Store.inBlock L 0 1)
        (fun μ' => ∃ v : ℝ, μ'.store.get L 0 = some v ∧ Pν v) m) :
    Writes .total I τ (colTail (O := O) (Q := Q)) (colEnv N j t sm y g L)
      (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) ⊔ Store.inBlock L 0 1 ⊔
        Store.inBlock (L + 1) 0 1)
      (fun μ' => ∃ ν : ℝ, Pν ν ∧ ∀ k < 2 * N, ∀ v, μ.store.get y.1 (y.2 + 2 * (j * N) + k) = some v →
        μ'.store.get y.1 (y.2 + 2 * (j * N) + k) = some (M.mul v (M.div (M.lit 1) ν))) μ := by
  have hlive : μ.Live [(y.1, y.2 + 2 * (j * N)), (L, 0)] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true, hlen]; omega
  refine (hν μ hlive hw (by omega)).frame_seq_le rfl rfl hlive
    (le_sup_of_le_left le_sup_right) fun μ₁ h₁ ⟨v, hv, hP⟩ => ?_
  refine (writes_call_const (hS (.lit 1)) (out := ⟨7, .const 0⟩) (z := (L + 1, 0)) rfl trivial
    (by simp [h₁.len_eq, hl1])).seq_le le_sup_right fun μ₂ h₂ ⟨p₂, g₂⟩ => ?_
  have hv₂ : μ₂.store.get L 0 = some v := by
    rw [h₂.2 _ _ (by simp [Store.inBlock])]; exact hv
  have hdiv := writes_call_bin (ins := [⟨7, .const 0⟩, ⟨6, .const 0⟩]) (outs := [⟨7, .const 0⟩])
    (x := (L + 1, 0)) (y := (L, 0)) (z := (L + 1, 0)) (ρ := colEnv N j t sm y g L) (τ := τ)
    (hS .div) rfl rfl trivial g₂ hv₂ rfl fun _ => ⟨by
      simp only [Mem.live_cons, Mem.live_nil, and_true, h₂.length_eq, h₁.length_eq, hlen]; omega,
      by simp [h₂.len_eq, h₁.len_eq, hl1]⟩
  refine hdiv.seq_le le_sup_right fun μ₃ h₃ ⟨p₃, g₃⟩ => ?_
  have hkeep : ∀ k v, μ.store.get y.1 (y.2 + 2 * (j * N) + k) = some v →
      μ₃.store.get y.1 (y.2 + 2 * (j * N) + k) = some v := fun k v h => by
    have hn : ∀ b, b ≠ y.1 → ¬ Store.inBlock b 0 1 y.1 (y.2 + 2 * (j * N) + k) :=
      fun b hb h' => hb h'.1.symm
    rw [h₃.2 _ _ (hn _ (by omega)), h₂.2 _ _ (hn _ (by omega)), h₁.2 _ _ (hn _ (by omega))]
    exact h
  have hex : ∀ k < 2 * N, ∃ v, μ₃.store.get y.1 (y.2 + 2 * (j * N) + k) = some v := fun k hk => by
    have hlw : (matrixWords (vectorColumn w)).length = 2 * N := by simp
    exact ⟨_, hkeep k _ (Store.get_of_readBlock hw hk 0)⟩
  have hmul := writes_loop_mul_cell (τ := τ) (ρ := colEnv N j t sm y g L) (m := μ₃) hS
    (n := .const 2 * .var 0) (N := 2 * N) (b := y.1) (o := y.2 + 2 * (j * N)) (y := (L + 1, 0))
    (X := ⟨2, .var 4 + .const 2 * (.var 1 * .var 0) + .var 8⟩) (Y := ⟨7, .const 0⟩)
    rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (by simp only [Mem.live_cons, Mem.live_nil, and_true, h₃.length_eq, h₂.length_eq,
      h₁.length_eq, hlen]; omega) hex g₃ (fun h => by have := h.1; omega)
  refine hmul.mono (le_sup_of_le_left le_sup_left) fun μ₄ _ ⟨_, hm⟩ => ⟨v, hP, fun k hk x hx => ?_⟩
  exact hm k hk x (hkeep k x hx)

/-- The start of a column: the back substitution, the unit entry and the zeros below it. -/
private def colHead (next : Stmt O Q) : Stmt O Q :=
  .seq (.frame [.var 0, .var 1] [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩, ⟨2, .var 4⟩,
    ⟨3, .var 5⟩] shiftedTriSolve) <|
  .seq (.call (Has.inj (ScalarOp.lit 1)) [] []
    [⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + .var 1)⟩]) <|
  .seq (.call (Has.inj (ScalarOp.lit 0)) [] []
    [⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + .var 1) + .const 1⟩]) <|
  .seq (.loop (.var 0 - .const 1 - .var 1)
    (.seq (.call (Has.inj (ScalarOp.lit 0)) [] []
      [⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + (.var 1 + .const 1 + .var 8))⟩])
      (.call (Has.inj (ScalarOp.lit 0)) [] []
        [⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + (.var 1 + .const 1 + .var 8)) + .const 1⟩])))
    next

/-- The tree of a column is its start and its end. -/
private theorem triEigColumn_eq :
    (triEigColumn : Stmt O Q) = Stmt.allocs [.const 1, .const 1] (colHead colTail) := rfl

/-- An entry of column `j` lies in the stored block. -/
private theorem col_lt {N j k : ℕ} (hj : j < N) (hk : k < N) :
    2 * (j * N + k) + 1 < 2 * (N * N) := by
  have : (j + 1) * N ≤ N * N := Nat.mul_le_mul_right N hj
  have e : (j + 1) * N = j * N + N := by ring
  omega

omit [Has IndexOp O] [Has CmpTst Q] in
/-- The zeros below the unit entry of a column. -/
private theorem colZeros_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {N j : ℕ} (hj : j < N) {t sm y g : ℕ × ℕ} {L : ℕ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hry : y.2 + 2 * (N * N) ≤ μ.store.len y.1) :
    Writes .total I τ (.loop (.var 0 - .const 1 - .var 1)
      (.seq (.call (Has.inj (ScalarOp.lit 0)) [] []
        [⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + (.var 1 + .const 1 + .var 8))⟩])
        (.call (Has.inj (ScalarOp.lit 0)) [] []
          [⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + (.var 1 + .const 1 + .var 8)) +
            .const 1⟩]))) (colEnv N j t sm y g L)
      (Store.inBlock y.1 (y.2 + 2 * (j * N + (j + 1))) (2 * (N - 1 - j)))
      (fun μ' => ∀ k, j < k → k < N → μ'.store.get y.1 (y.2 + 2 * (j * N + k)) = some (M.lit 0) ∧
        μ'.store.get y.1 (y.2 + 2 * (j * N + k) + 1) = some (M.lit 0)) μ := by
  refine (writes_loop (N := N - 1 - j) rfl
    (fun l => Store.inBlock y.1 (y.2 + 2 * (j * N + (j + 1))) (2 * l))
    (fun l _ => Fp.inBlock_le_inBlock le_rfl (by omega))
    (fun l μ' => ∀ k, j < k → k < j + 1 + l →
      μ'.store.get y.1 (y.2 + 2 * (j * N + k)) = some (M.lit 0) ∧
      μ'.store.get y.1 (y.2 + 2 * (j * N + k) + 1) = some (M.lit 0))
    (fun k h₁ h₂ => by omega) fun l hl μ' hfr hP => ?_).mono le_rfl
    fun μ' _ h k h₁ h₂ => h k h₁ (by omega)
  have hl' : l < N - 1 - j := hl
  have hc := col_lt hj (show j + 1 + l < N by omega)
  have hsub : ∀ o, o = y.2 + 2 * (j * N + (j + 1 + l)) ∨ o = y.2 + 2 * (j * N + (j + 1 + l)) + 1 →
      Store.inBlock y.1 o 1 ≤ Store.inBlock y.1 (y.2 + 2 * (j * N + (j + 1))) (2 * (l + 1)) := by
    rintro o (rfl | rfl) <;> exact Fp.inBlock_le_inBlock (by omega) (by omega)
  refine (writes_call_const (hS (.lit 0)) (z := (y.1, y.2 + 2 * (j * N + (j + 1 + l)))) rfl trivial
    (by dsimp only; rw [hfr.len_eq]; omega)).seq_le (hsub _ (Or.inl rfl))
    fun μ₁ h₁ ⟨_, g₁⟩ => ?_
  refine (writes_call_const (hS (.lit 0)) (z := (y.1, y.2 + 2 * (j * N + (j + 1 + l)) + 1)) rfl
    trivial (by dsimp only; rw [h₁.len_eq, hfr.len_eq]; omega)).mono (hsub _ (Or.inr rfl))
    fun μ₂ h₂ ⟨_, g₂⟩ k hk₁ hk₂ => ?_
  by_cases hk : k = j + 1 + l
  · subst hk
    refine ⟨?_, g₂⟩
    rw [h₂.2 _ _ (by simp [Store.inBlock])]
    exact g₁
  · have ⟨a, b⟩ := hP k hk₁ (by omega)
    have hn : ∀ o c, (o = y.2 + 2 * (j * N + k) ∨ o = y.2 + 2 * (j * N + k) + 1) →
        (c = y.2 + 2 * (j * N + (j + 1 + l)) ∨ c = y.2 + 2 * (j * N + (j + 1 + l)) + 1) →
        ¬ Store.inBlock y.1 c 1 y.1 o := by
      rintro o c (rfl | rfl) (rfl | rfl) ⟨-, h₁, h₂⟩ <;> omega
    constructor
    · rw [h₂.2 _ _ (hn _ _ (Or.inl rfl) (Or.inr rfl)), h₁.2 _ _ (hn _ _ (Or.inl rfl) (Or.inl rfl))]
      exact a
    · rw [h₂.2 _ _ (hn _ _ (Or.inr rfl) (Or.inr rfl)), h₁.2 _ _ (hn _ _ (Or.inr rfl) (Or.inl rfl))]
      exact b

/-- The unit entry and the zeros below it complete the stored column. -/
private theorem colFill_holds {M : Machine ℝ} {N j : ℕ} {y : ℕ × ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {s : Store ℝ}
    (hup : ∀ i < j, s.get y.1 (y.2 + 2 * (j * N + i)) =
        some ((shiftedTriSolveWord M T smin j j).1 i).re ∧
      s.get y.1 (y.2 + 2 * (j * N + i) + 1) = some ((shiftedTriSolveWord M T smin j j).1 i).im)
    (hd₀ : s.get y.1 (y.2 + 2 * (j * N + j)) = some (M.lit 1))
    (hd₁ : s.get y.1 (y.2 + 2 * (j * N + j) + 1) = some (M.lit 0))
    (hlo : ∀ k, j < k → k < N → s.get y.1 (y.2 + 2 * (j * N + k)) = some (M.lit 0) ∧
      s.get y.1 (y.2 + 2 * (j * N + k) + 1) = some (M.lit 0)) :
    HoldsVector (y.1, y.2 + 2 * (j * N)) (triEigColumnWord M T smin j) s := by
  have e : ∀ i : ℕ, y.2 + 2 * (j * N) + 2 * i = y.2 + 2 * (j * N + i) := fun i => by ring
  refine ShiftedQR.HoldsVector.of_get (fun i => ?_) (fun i => ?_)
  · simp only [e, triEigColumnWord]
    split_ifs with h₁ h₂
    · exact (hup i h₁).1
    · rw [h₂]; exact hd₀
    · exact (hlo i (by omega) i.isLt).1
  · simp only [e, triEigColumnWord]
    split_ifs with h₁ h₂
    · exact (hup i h₁).2
    · rw [h₂]; exact hd₁
    · exact (hlo i (by omega) i.isLt).2

omit [Has IndexOp O] [Has CmpTst Q] in
/-- A column after its back substitution: the unit entry, the zeros, the norm and the scaling. -/
private theorem colRest_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {N j : ℕ} (hj : j < N) {t sm y g : ℕ × ℕ} {L : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ}
    {τ : Tape ℝ} {μ : Mem ℝ} {Pν : ℝ → Prop} (hyL : y.1 < L) (hgL : g.1 < L)
    (hlen : μ.store.length = L + 2) (hl0 : μ.store.len L = 1) (hl1 : μ.store.len (L + 1) = 1)
    (hry : y.2 + 2 * (N * N) ≤ μ.store.len y.1)
    (hgc : ¬ Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) g.1 g.2)
    (hup : ∀ i < j, μ.store.get y.1 (y.2 + 2 * (j * N + i)) =
        some ((shiftedTriSolveWord M T smin j j).1 i).re ∧
      μ.store.get y.1 (y.2 + 2 * (j * N + i) + 1) =
        some ((shiftedTriSolveWord M T smin j j).1 i).im)
    (hν : ∀ m : Mem ℝ, m.Live [(y.1, y.2 + 2 * (j * N)), (L, 0)] →
      m.store.readBlock y.1 (y.2 + 2 * (j * N)) (2 * N) =
        some (matrixWords (vectorColumn (triEigColumnWord M T smin j))) → 0 < m.store.len L →
      Writes .total I τ (RoundedScalarBlas.nrm2 (Op := O) (Tst := Q)).body
        (Env.frame [2 * N] [(y.1, y.2 + 2 * (j * N)), (L, 0)]) (Store.inBlock L 0 1)
        (fun μ' => ∃ v : ℝ, μ'.store.get L 0 = some v ∧ Pν v) m) :
    Writes .total I τ
      (.seq (.call (Has.inj (ScalarOp.lit 1)) [] []
        [⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + .var 1)⟩]) <|
       .seq (.call (Has.inj (ScalarOp.lit 0)) [] []
        [⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + .var 1) + .const 1⟩]) <|
       .seq (.loop (.var 0 - .const 1 - .var 1)
        (.seq (.call (Has.inj (ScalarOp.lit 0)) [] []
          [⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + (.var 1 + .const 1 + .var 8))⟩])
          (.call (Has.inj (ScalarOp.lit 0)) [] []
            [⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + (.var 1 + .const 1 + .var 8)) +
              .const 1⟩]))) colTail)
      (colEnv N j t sm y g L)
      (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) ⊔ Store.inBlock L 0 1 ⊔
        Store.inBlock (L + 1) 0 1)
      (fun μ' => ∃ ν : ℝ, Pν ν ∧
        (∀ i : Fin N, μ'.store.get y.1 (y.2 + 2 * (j * N + i)) =
            some (M.mul (triEigColumnWord M T smin j i).re (M.div (M.lit 1) ν)) ∧
          μ'.store.get y.1 (y.2 + 2 * (j * N + i) + 1) =
            some (M.mul (triEigColumnWord M T smin j i).im (M.div (M.lit 1) ν))) ∧
        μ'.store.get g.1 g.2 = μ.store.get g.1 g.2) μ := by
  have hc := col_lt hj hj
  have hF : ∀ {o n}, y.2 + 2 * (j * N) ≤ o → o + n ≤ y.2 + 2 * (j * N) + 2 * N →
      Store.inBlock y.1 o n ≤ Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) ⊔
        Store.inBlock L 0 1 ⊔ Store.inBlock (L + 1) 0 1 := fun h₁ h₂ =>
    (Fp.inBlock_le_inBlock h₁ h₂).trans (le_sup_of_le_left le_sup_left)
  have hjN : j * N + N ≤ N * N := by
    have : (j + 1) * N ≤ N * N := Nat.mul_le_mul_right N hj
    have e : (j + 1) * N = j * N + N := by ring
    omega
  refine (writes_call_const (hS (.lit 1)) (z := (y.1, y.2 + 2 * (j * N + j))) rfl trivial
    (by dsimp only; omega)).seq_le (hF (by omega) (by omega)) fun μ₁ h₁ ⟨_, g₁⟩ => ?_
  refine (writes_call_const (hS (.lit 0)) (z := (y.1, y.2 + 2 * (j * N + j) + 1)) rfl trivial
    (by dsimp only; rw [h₁.len_eq]; omega)).seq_le (hF (by omega) (by omega))
    fun μ₂ h₂ ⟨_, g₂⟩ => ?_
  have hry₂ : y.2 + 2 * (N * N) ≤ μ₂.store.len y.1 := by rw [h₂.len_eq, h₁.len_eq]; exact hry
  refine (colZeros_writes hS hj (t := t) (sm := sm) (g := g) (L := L) hry₂).seq_le
    (hF (by omega) (by
      have : j + 1 + (N - 1 - j) = N := by omega
      have e : 2 * (j * N + (j + 1)) + 2 * (N - 1 - j) = 2 * (j * N) + 2 * N := by omega
      omega)) fun μ₃ h₃ hlo => ?_
  have hn₃ : ∀ o, o < y.2 + 2 * (j * N + (j + 1)) →
      ¬ Store.inBlock y.1 (y.2 + 2 * (j * N + (j + 1))) (2 * (N - 1 - j)) y.1 o :=
    fun o ho h => by have := h.2.1; omega
  have hh := colFill_holds (M := M) (T := T) (smin := smin) (y := y) (N := N) (j := j) (s := μ₃.store)
    (fun i hi => by
      have ⟨a, b⟩ := hup i hi
      have hne : ∀ c d, (c = y.2 + 2 * (j * N + i) ∨ c = y.2 + 2 * (j * N + i) + 1) →
          (d = y.2 + 2 * (j * N + j) ∨ d = y.2 + 2 * (j * N + j) + 1) →
          ¬ Store.inBlock y.1 d 1 y.1 c := by
        rintro c d (rfl | rfl) (rfl | rfl) ⟨-, h₁, h₂⟩ <;> omega
      constructor
      · rw [h₃.2 _ _ (hn₃ _ (by omega)), h₂.2 _ _ (hne _ _ (Or.inl rfl) (Or.inr rfl)),
          h₁.2 _ _ (hne _ _ (Or.inl rfl) (Or.inl rfl))]
        exact a
      · rw [h₃.2 _ _ (hn₃ _ (by omega)), h₂.2 _ _ (hne _ _ (Or.inr rfl) (Or.inr rfl)),
          h₁.2 _ _ (hne _ _ (Or.inr rfl) (Or.inl rfl))]
        exact b)
    (by
      rw [h₃.2 _ _ (hn₃ _ (by omega)), h₂.2 _ _ (by simp [Store.inBlock])]
      exact g₁)
    (by rw [h₃.2 _ _ (hn₃ _ (by omega))]; exact g₂) hlo
  have hrd : μ₃.store.readBlock y.1 (y.2 + 2 * (j * N)) (2 * N) =
      some (matrixWords (vectorColumn (triEigColumnWord M T smin j))) := by
    simpa [HoldsMatrix] using hh
  have hlen₃ : μ₃.store.length = L + 2 := by rw [h₃.length_eq, h₂.length_eq, h₁.length_eq, hlen]
  have hl₃0 : μ₃.store.len L = 1 := by rw [h₃.len_eq, h₂.len_eq, h₁.len_eq, hl0]
  have hl₃1 : μ₃.store.len (L + 1) = 1 := by rw [h₃.len_eq, h₂.len_eq, h₁.len_eq, hl1]
  refine (colTail_writes hS hyL hlen₃ hl₃0 hl₃1 hrd hν).mono le_rfl
    fun μ₄ h₄ ⟨ν, hP, hm⟩ => ⟨ν, hP, fun i => ?_, ?_⟩
  · have e : y.2 + 2 * (j * N) + 2 * (i : ℕ) = y.2 + 2 * (j * N + i) := by ring
    have hre := hm (2 * i) (by omega) _ (ShiftedQR.HoldsVector.get_re hh i)
    have him := hm (2 * i + 1) (by omega) _ (by
      have := ShiftedQR.HoldsVector.get_im hh i
      simpa [Nat.add_assoc] using this)
    rw [e] at hre
    refine ⟨hre, ?_⟩
    have e' : y.2 + 2 * (j * N) + (2 * (i : ℕ) + 1) = y.2 + 2 * (j * N + i) + 1 := by ring
    rw [e'] at him
    exact him
  · have ng : ∀ {o n}, y.2 + 2 * (j * N) ≤ o → o + n ≤ y.2 + 2 * (j * N) + 2 * N →
        ¬ Store.inBlock y.1 o n g.1 g.2 := fun h₁ h₂ h =>
      hgc (Fp.inBlock_le_inBlock h₁ h₂ _ _ h)
    rw [h₄.2 _ _ ?_, h₃.2 _ _ (ng (by omega) (by
        have e : 2 * (j * N + (j + 1)) + 2 * (N - 1 - j) = 2 * (j * N) + 2 * N := by omega
        omega)), h₂.2 _ _ (ng (by omega) (by omega)), h₁.2 _ _ (ng (by omega) (by omega))]
    rintro ((h | h) | h)
    · exact hgc h
    · have := h.1; omega
    · have := h.1; omega

/-- **The words of one column**, on any scalar machine with index literals and exact comparisons:
the run stores the column `NLAlib.Schur.triEigColumnWord` times the rounded reciprocal of a word
`ν` with the property `Pν` of the rounded norm of that column, and sets the flag as
`NLAlib.shiftedTriSolve_writes_word`. -/
theorem triEigColumn_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) {N j : ℕ} (hj : j < N) {t sm y g : ℕ × ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {τ : Tape ℝ} {μ : Mem ℝ} {Pν : ℝ → Prop}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1])
    (hν : ∀ (m : Mem ℝ) (z : ℕ × ℕ), m.Live [(y.1, y.2 + 2 * (j * N)), z] → z.1 ≠ y.1 →
      z.2 < m.store.len z.1 → m.store.readBlock y.1 (y.2 + 2 * (j * N)) (2 * N) =
        some (matrixWords (vectorColumn (triEigColumnWord M T smin j))) →
      Writes .total I τ (RoundedScalarBlas.nrm2 (Op := O) (Tst := Q)).body
        (Env.frame [2 * N] [(y.1, y.2 + 2 * (j * N)), z]) (Store.inBlock z.1 z.2 1)
        (fun μ' => ∃ v : ℝ, μ'.store.get z.1 z.2 = some v ∧ Pν v) m) :
    Writes .total I τ (triEigColumn (O := O) (Q := Q)) (Env.frame [N, j] [t, sm, y, g, y, g])
      (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ ν : ℝ, Pν ν ∧
        (∀ i : Fin N, μ'.store.get y.1 (y.2 + 2 * (j * N + i)) =
            some (M.mul (triEigColumnWord M T smin j i).re (M.div (M.lit 1) ν)) ∧
          μ'.store.get y.1 (y.2 + 2 * (j * N + i) + 1) =
            some (M.mul (triEigColumnWord M T smin j i).im (M.div (M.lit 1) ν))) ∧
        (shiftedTriSolveFlag M T smin j = true → μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        (shiftedTriSolveFlag M T smin j = false →
          μ'.store.get g.1 g.2 = μ.store.get g.1 g.2)) μ := by
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  obtain ⟨htl, hsl, hyl, hgl⟩ := hl
  simp only [Mem.room_cons, Mem.room_nil, and_true] at hroom
  obtain ⟨hyr, hgr⟩ := hroom
  have hyg : Fp.Disj (Store.inBlock y.1 y.2 (2 * (N * N))) (Store.inBlock g.1 g.2 1) :=
    hap.2.2.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)
  have hcol : Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) ≤
      Store.inBlock y.1 y.2 (2 * (N * N)) := by
    have := col_lt hj (show N - 1 < N by omega)
    exact Fp.inBlock_le_inBlock (by omega) (by omega)
  have hgc : ¬ Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) g.1 g.2 := fun h =>
    hyg g.1 g.2 (hcol _ _ h) ⟨rfl, le_rfl, by omega⟩
  rw [triEigColumn_eq]
  refine writes_allocs_preserving_post (ns := [1, 1]) rfl
    (fun {s s' p} hB ⟨ν, hP, h₁, h₂, h₃⟩ => ⟨ν, hP, fun i =>
      ⟨hB.get_of hyl (h₁ i).1, hB.get_of hyl (h₁ i).2⟩, fun h => hB.get_of hgl (h₂ h),
      fun h => ((hB g.1 hgl).2 g.2).trans (h₃ h)⟩) ?_
  intro s₁ hlen hlens hB
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  have hl0 : s₁.len L = 1 := by simpa using hlens 0 (by simp)
  have hl1 : s₁.len (L + 1) = 1 := by simpa using hlens 1 (by simp)
  have hry : y.2 + 2 * (N * N) ≤ s₁.len y.1 := by rw [(hB y.1 hyl).1]; exact hyr
  have hrg : g.2 + 1 ≤ s₁.len g.1 := by rw [(hB g.1 hgl).1]; exact hgr
  have hsolve := shiftedTriSolve_writes_word (τ := τ) (μ := ⟨s₁, μ.pos⟩) hS hL hC hj
    (hT.of_below hB htl) (hB.get_of hsl hsm)
    (by simp only [Mem.live_cons, Mem.live_nil, and_true, hlen]; omega)
    (by simp only [Mem.room_cons, Mem.room_nil, and_true]; exact ⟨hry, hrg⟩) hap
  have hBig : ∀ {G : Fp}, G ≤ Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) ⊔
      Store.inBlock g.1 g.2 1 → G ≤ (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) ⊔
        Store.inBlock g.1 g.2 1) ⊔ Fp.above L := fun h => h.trans le_sup_left
  have hsub : Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j) ≤
      Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) :=
    Fp.inBlock_le_inBlock le_rfl (by omega)
  refine hsolve.frame_seq_le rfl rfl
    (by simp only [Mem.live_cons, Mem.live_nil, and_true, hlen]; omega)
    (hBig (sup_le_sup hsub le_rfl)) fun μ₁ h₁ ⟨hup, hf1, hf0⟩ => ?_
  have hlen₁ : μ₁.store.length = L + 2 := by rw [h₁.length_eq]; simpa using hlen
  refine (colRest_writes (t := t) (sm := sm) (g := g) (L := L) hS hj hyl hgl hlen₁
    (by rw [h₁.len_eq]; exact hl0) (by rw [h₁.len_eq]; exact hl1)
    (by rw [h₁.len_eq]; exact hry) hgc hup fun m hm hrd hz =>
      hν m (L, 0) hm (by dsimp only; omega) hz hrd).mono ?_
    fun μ₂ _ ⟨ν, hP, hc, hg⟩ => ⟨ν, hP, hc, fun h => hg.trans (hf1 h), fun h => ?_⟩
  · refine sup_le (sup_le (le_sup_of_le_left le_sup_left) ?_) ?_
    · exact fun b o h => Or.inr (show L ≤ b from h.1 ▸ le_rfl)
    · exact fun b o h => Or.inr (show L ≤ b by have := h.1; omega)
  · rw [hg, hf0 h]
    exact (hB g.1 hgl).2 g.2

/-- **One eigenvector column under the standard model**: on a scalar machine with the standard
model at $\boldsymbol{u}$, $64(N + 1)\boldsymbol{u} \le 1$, index literals and exact comparisons,
from a memory holding an upper triangular $\mathbf{T}$ of order $N$ at `t`, the floor
$s_{\min} \ge 0$ at `sm`, room for `Y` and a flag word at `g`, the four blocks live and apart, the
run for $j < N$ writes only column $j$ of `Y` and the flag: column $j$ holds a vector
$\mathbf{y}$ with $\lvert\|\mathbf{y}\| - 1\rvert \le 4(N + 2)\boldsymbol{u}$ that is a
componentwise
backward solution of $(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y} = \mathbf{0}$ with
$16(N + 1)\boldsymbol{u}$ and the floor $\tfrac72 s_{\min}$ if a pivot was floored (the flag the
literal $1$), $0$ otherwise (the flag unchanged); no pivot is floored when
$\lvert t_{ii} - t_{jj}\rvert > 2s_{\min}$ for $i < j$. -/
theorem triEigColumn_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ}
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {t sm y g : ℕ × ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    (hTu : T.IsUpperTriangular) {smin : ℝ} (hsmin : 0 ≤ smin) (j : Fin N) {τ : Tape ℝ}
    {μ : Mem ℝ} (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (triEigColumn (O := O) (Q := Q))
      (Env.frame [N, j] [t, sm, y, g, y, g])
      (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ (yv : Fin N → ℂ) (fl : Bool),
        (∀ i : Fin N, μ'.store.get y.1 (y.2 + 2 * (j * N + i)) = some (yv i).re ∧
          μ'.store.get y.1 (y.2 + 2 * (j * N + i) + 1) = some (yv i).im) ∧
        |‖WithLp.toLp 2 yv‖ - 1| ≤ 4 * ((N : ℝ) + 2) * u ∧
        IsComponentwiseBackwardSolution (16 * ((N : ℝ) + 1) * u)
          (if fl then 7 / 2 * smin else 0) (T - T j j • 1) 0 yv ∧
        (fl = true → μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        (fl = false → μ'.store.get g.1 g.2 = μ.store.get g.1 g.2) ∧
        ((∀ i : Fin N, i < j → 2 * smin < ‖T i i - T j j‖) → fl = false)) μ := by
  sorry

/-- **The eigenvector columns complete**: on a scalar machine with index literals and exact
comparisons, from a memory holding a matrix $\mathbf{T}$ of order $N$ at `t`, a word at `sm`,
room for `Y` and a flag word at `g`, the four blocks live and apart, the run writes only `Y` and
the flag, and stores a matrix in `Y` and a word in the flag. -/
theorem triEigenvectors_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ} {t sm y g : ℕ × ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hg : ∃ x : ℝ, μ.store.get g.1 g.2 = some x)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (triEigenvectors (O := O) (Q := Q))
      (Env.frame [N] [t, sm, y, g, y, g])
      (Store.inBlock y.1 y.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => (∃ Y : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix y Y μ'.store) ∧
        ∃ x : ℝ, μ'.store.get g.1 g.2 = some x) μ := by
  sorry

/-- **The eigenvector columns are an approximate triangular eigenbasis**: on a scalar machine with
the standard model at $\boldsymbol{u}$, $64(N + 1)\boldsymbol{u} \le 1$, index literals and exact
comparisons, from a memory holding an upper triangular $\mathbf{T}$ of order $N$ at `t`, the floor
$s_{\min} \ge 0$ at `sm`, room for `Y` and the flag $0$ at `g`, the four blocks live and apart,
the run stores a $\mathbf{Y}$ with `NLAlib.IsTriangularEigenbasisApprox` at
$(16(N + 1)\boldsymbol{u}, \tfrac72 s_{\min}, 4(N + 2)\boldsymbol{u})$, and the flag $0$ or the
literal $1$; with the flag $0$, the same with no floor. -/
theorem triEigenvectors_isTriangularEigenbasisApprox {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ}
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {t sm y g : ℕ × ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    (hTu : T.IsUpperTriangular) {smin : ℝ} (hsmin : 0 ≤ smin) {τ : Tape ℝ} {μ : Mem ℝ}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hg : μ.store.get g.1 g.2 = some 0)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (triEigenvectors (O := O) (Q := Q))
      (Env.frame [N] [t, sm, y, g, y, g])
      (Store.inBlock y.1 y.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ Y : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix y Y μ'.store ∧
        (μ'.store.get g.1 g.2 = some 0 ∨ μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        IsTriangularEigenbasisApprox (16 * ((N : ℝ) + 1) * u) (7 / 2 * smin)
          (4 * ((N : ℝ) + 2) * u) T Y ∧
        (μ'.store.get g.1 g.2 = some 0 →
          IsTriangularEigenbasisApprox (16 * ((N : ℝ) + 1) * u) 0 (4 * ((N : ℝ) + 2) * u) T Y))
      μ := by
  sorry

/-- **No pivot is floored when the diagonal is separated**: on a scalar machine with the standard
model at $\boldsymbol{u}$, $64(N + 1)\boldsymbol{u} \le 1$, index literals and exact comparisons,
from the memory of `NLAlib.Schur.triEigenvectors_isTriangularEigenbasisApprox`, if
$\lvert t_{ii} - t_{jj}\rvert > 2s_{\min}$ for $i \ne j$, the run stores the flag $0$. -/
theorem triEigenvectors_flag {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ}
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {t sm y g : ℕ × ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    {smin : ℝ} (hsmin : 0 ≤ smin) {τ : Tape ℝ} {μ : Mem ℝ}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hg : μ.store.get g.1 g.2 = some 0)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1])
    (hgap : ∀ i j, i ≠ j → 2 * smin < ‖T i i - T j j‖) :
    Writes .total I τ (triEigenvectors (O := O) (Q := Q))
      (Env.frame [N] [t, sm, y, g, y, g])
      (Store.inBlock y.1 y.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => μ'.store.get g.1 g.2 = some 0) μ := by
  sorry

end Columns

/-! ### The stage -/

section Stage

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The eigenvector stage meets its contract**: on a scalar machine with the standard model at
$\boldsymbol{u}$, $64(N_{\max} + 1)^2\boldsymbol{u} \le 1$, index literals, exact literals $0$, $1$
and exact comparisons, for the floor parameter $\rho > 0$, `NLAlib.Schur.triEigvecStage` with the
word $\rho$ meets `NLAlib.Schur.EigenvectorStageContract` with $c_{R,0} = 16(1 +
\sqrt{N_{\max}})(N_{\max} + 1)\boldsymbol{u}$, $c_R = c_{R,0} + 4\rho$,
$c_V = 8(N_{\max} + 1)\boldsymbol{u}$, $c_N = 4(N_{\max} + 2)\boldsymbol{u}$ and $g_0 = 4\rho$.
No printed source; the floor is that of LAPACK `xTREVC`. -/
theorem triEigvecStage_eigenvectorStageContract {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M 1) (hC : IsCmp id I) {nmax : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : 64 * ((nmax : ℝ) + 1) ^ 2 * u ≤ 1) :
    EigenvectorStageContract (16 * (1 + √(nmax : ℝ)) * ((nmax : ℝ) + 1) * u)
      (16 * (1 + √(nmax : ℝ)) * ((nmax : ℝ) + 1) * u + 4 * ρ) (8 * ((nmax : ℝ) + 1) * u)
      (4 * ((nmax : ℝ) + 2) * u) (4 * ρ) nmax [ρ] (triEigvecStage (O := O) (Q := Q)) I := by
  sorry

/-- **The eigenvector stage completes** on any scalar machine with index literals and exact
comparisons: for every order at most $N_{\max}$ and every stored pair it succeeds on every tape,
writing only $\mathbf{V}$ and the flag, and stores a matrix and a word. -/
theorem triEigvecStage_completes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) (nmax : ℕ) (ρ : ℝ) :
    CompletingEigenvectorStage nmax [ρ] (triEigvecStage (O := O) (Q := Q)) I := by
  sorry

/-- **The static count of the eigenvector stage**: its instrumented static count at the order
$n + 1$, $n_e$ words and zero offsets is at most $10^4(n + 1)^3$. -/
theorem size_stmtCost_triEigvecStage_le (n ne : ℕ) :
    Count.size (stmtCost (triEigvecStage (O := O) (Q := Q)).instrument
      [n + 1, ne, 0, 0, 0, 0, 0]) ≤ 10000 * (n + 1) ^ 3 := by
  sorry

end Stage

end NLAlib.Schur
