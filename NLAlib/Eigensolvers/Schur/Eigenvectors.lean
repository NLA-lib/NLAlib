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

/-- The norm of a rounded scaled column: if $\nu$ is within the factors $1 \pm a$ of $W > 0$,
$\ell$ within $\boldsymbol{u}$ of $1$, $r$ a rounded $\ell/\nu$ and $Z$ within the relative error
$\boldsymbol{u}$ of $\lvert r\rvert W$, then $\lvert Z - 1\rvert \le 2a + 4\boldsymbol{u}$, for
$a \le 1/16$ and $\boldsymbol{u} \le 1/64$. -/
private theorem abs_column_norm_sub_one_le {u a W ν l r Z : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 64)
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 16) (hW : 0 < W) (h1 : (1 - a) * W ≤ ν) (h2 : ν ≤ (1 + a) * W)
    (hl : |l - 1| ≤ u) (hr : |r - l / ν| ≤ u * |l / ν|) (hZ : |Z - |r| * W| ≤ u * (|r| * W)) :
    |Z - 1| ≤ 2 * a + 4 * u := by
  have hν : 0 < ν := lt_of_lt_of_le (mul_pos (by linarith) hW) h1
  obtain ⟨hl₁, hl₂⟩ := abs_le.mp hl
  have hl0 : 0 < l := by linarith
  have hq : 0 < l / ν := div_pos hl0 hν
  rw [abs_of_pos hq] at hr
  obtain ⟨hr₁, hr₂⟩ := abs_le.mp hr
  have hr0 : 0 < r := by nlinarith
  rw [abs_of_pos hr0] at hZ
  obtain ⟨hZ₁, hZ₂⟩ := abs_le.mp hZ
  set p := W / ν with hp
  have hp0 : 0 < p := div_pos hW hν
  have hpν : p * ν = W := by rw [hp]; field_simp
  have hp₁ : 1 ≤ (1 + a) * p := by
    have : ν ≤ (1 + a) * (p * ν) := by rw [hpν]; exact h2
    have h' : 1 * ν ≤ ((1 + a) * p) * ν := by linarith [this, mul_assoc (1 + a) p ν]
    exact le_of_mul_le_mul_right h' hν
  have hp₂ : (1 - a) * p ≤ 1 := by
    have : (1 - a) * (p * ν) ≤ ν := by rw [hpν]; exact h1
    have h' : ((1 - a) * p) * ν ≤ 1 * ν := by linarith [this, mul_assoc (1 - a) p ν]
    exact le_of_mul_le_mul_right h' hν
  have hpu : p ≤ 1 + 2 * a := by nlinarith
  have hpl : 1 - a ≤ p := by nlinarith
  have hqW : l / ν * W = l * p := by rw [hp]; ring
  have hX₁ : (1 - u) * (l * p) ≤ r * W := by
    have := mul_le_mul_of_nonneg_right (show (1 - u) * (l / ν) ≤ r by linarith) hW.le
    rwa [mul_assoc, hqW] at this
  have hX₂ : r * W ≤ (1 + u) * (l * p) := by
    have := mul_le_mul_of_nonneg_right (show r ≤ (1 + u) * (l / ν) by linarith) hW.le
    rwa [mul_assoc, hqW] at this
  have hlp₁ : (1 - u) * (1 - a) ≤ l * p :=
    mul_le_mul (by linarith) hpl (by linarith) hl0.le
  have hlp₂ : l * p ≤ (1 + u) * (1 + 2 * a) :=
    mul_le_mul (by linarith) hpu hp0.le (by linarith)
  have hup : Z ≤ 1 + 2 * a + 4 * u := by
    have h3 : r * W ≤ (1 + u) * ((1 + u) * (1 + 2 * a)) :=
      hX₂.trans (mul_le_mul_of_nonneg_left hlp₂ (by linarith))
    have h4 : Z ≤ (1 + u) * (r * W) := by linarith
    have h5 : (1 + u) * (r * W) ≤ (1 + u) * ((1 + u) * ((1 + u) * (1 + 2 * a))) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    have h6 : (1 + u) * ((1 + u) * ((1 + u) * (1 + 2 * a))) ≤ 1 + 2 * a + 4 * u := by
      have hc : (1 + u) * ((1 + u) * (1 + u)) ≤ 1 + 7 / 2 * u := by nlinarith [mul_nonneg hu0 hu0]
      have : (1 + u) * ((1 + u) * ((1 + u) * (1 + 2 * a))) =
          (1 + u) * ((1 + u) * (1 + u)) * (1 + 2 * a) := by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ 1 + 2 * a by linarith),
        mul_nonneg hu0 ha0]
    linarith
  have hlo : 1 - 2 * a - 4 * u ≤ Z := by
    have h3 : (1 - u) * ((1 - u) * (1 - a)) ≤ r * W :=
      (mul_le_mul_of_nonneg_left hlp₁ (by linarith)).trans hX₁
    have h4 : (1 - u) * (r * W) ≤ Z := by linarith
    have h5 : (1 - u) * ((1 - u) * ((1 - u) * (1 - a))) ≤ (1 - u) * (r * W) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    have h6 : 1 - 2 * a - 4 * u ≤ (1 - u) * ((1 - u) * ((1 - u) * (1 - a))) := by
      have hc : 1 - 3 * u ≤ (1 - u) * ((1 - u) * (1 - u)) := by
        nlinarith [mul_nonneg hu0 hu0, mul_nonneg (mul_nonneg hu0 hu0) hu0]
      have : (1 - u) * ((1 - u) * ((1 - u) * (1 - a))) =
          (1 - u) * ((1 - u) * (1 - u)) * (1 - a) := by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ 1 - a by linarith), mul_nonneg hu0 ha0]
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A rounded real scaling of a complex number: each part of $z$ times $r$ is rounded with the
relative error $\boldsymbol{u}$. -/
private theorem norm_mul_pair_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    (z : ℂ) (r : ℝ) :
    ‖(⟨M.mul z.re r, M.mul z.im r⟩ : ℂ) - (r : ℂ) * z‖ ≤ u * ‖(r : ℂ) * z‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  have h1 := hM.mul z.re r
  have h2 := hM.mul z.im r
  simp only [id] at h1 h2
  have e1 := mul_self_le_mul_self (abs_nonneg _) h1
  have e2 := mul_self_le_mul_self (abs_nonneg _) h2
  rw [abs_mul_abs_self, mul_mul_mul_comm, abs_mul_abs_self] at e1 e2
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  nlinarith [mul_self_nonneg u]

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

/-- The sum of the squared words of a stored column is its squared norm. -/
private theorem sqrt_sum_sq_columnWords {N : ℕ} (w : Fin N → ℂ) :
    √(∑ i ∈ Finset.range (2 * N), (vec (matrixWords (vectorColumn w)) i) ^ 2) =
      ‖WithLp.toLp 2 w‖ := by
  have h := ShiftedQR.sum_sq_matrixWords (vectorColumn w)
  rw [Nat.one_mul] at h
  have e : frobNorm (vectorColumn w) ^ 2 = ‖WithLp.toLp 2 w‖ ^ 2 := by
    simp [frobNorm_sq_eq_sum, vectorColumn, EuclideanSpace.norm_sq_eq]
  rw [h, e, Real.sqrt_sq (norm_nonneg _)]

/-- The rounded scaling of a stored column, in the Euclidean norm. -/
private theorem norm_scaled_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    {N : ℕ} (w : Fin N → ℂ) (r : ℝ) :
    ‖WithLp.toLp 2 (fun i => (⟨M.mul (w i).re r, M.mul (w i).im r⟩ : ℂ)) -
        (r : ℂ) • WithLp.toLp 2 w‖ ≤ u * (|r| * ‖WithLp.toLp 2 w‖) := by
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [EuclideanSpace.norm_sq_eq, mul_pow, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := norm_mul_pair_sub_le hM hu (w k) r
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  calc _ ≤ (u * (|r| * ‖w k‖)) ^ 2 := h2
    _ = _ := by ring

/-- **The scaled column** under the standard model: from the bounds of the rounded norm $\nu$ of
the column before scaling, the stored column has norm within $4(N + 2)\boldsymbol{u}$ of $1$ and
is a componentwise backward solution with $16(N + 1)\boldsymbol{u}$ and the floor
$\tfrac72 s_{\min}$ if a pivot was floored. -/
private theorem triEigColumn_scaled {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) {N : ℕ}
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {T : Matrix (Fin N) (Fin N) ℂ} (hTu : T.IsUpperTriangular)
    {smin : ℝ} (hsmin : 0 < smin) (j : Fin N) {ν : ℝ}
    (hν₁ : (1 - (((2 * N : ℕ) : ℝ) + 2) * u) * ‖WithLp.toLp 2 (triEigColumnWord M T smin j)‖ ≤ ν)
    (hν₂ : ν ≤ (1 + (((2 * N : ℕ) : ℝ) + 2) * u) * ‖WithLp.toLp 2 (triEigColumnWord M T smin j)‖) :
    |‖WithLp.toLp 2 (fun i => (⟨M.mul (triEigColumnWord M T smin j i).re (M.div (M.lit 1) ν),
        M.mul (triEigColumnWord M T smin j i).im (M.div (M.lit 1) ν)⟩ : ℂ))‖ - 1| ≤
        4 * ((N : ℝ) + 2) * u ∧
      IsComponentwiseBackwardSolution (16 * ((N : ℝ) + 1) * u)
        (if shiftedTriSolveFlag M T smin j then 7 / 2 * smin else 0) (T - T j j • 1) 0
        (fun i => (⟨M.mul (triEigColumnWord M T smin j i).re (M.div (M.lit 1) ν),
          M.mul (triEigColumnWord M T smin j i).im (M.div (M.lit 1) ν)⟩ : ℂ)) := by
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hu64 : u ≤ 1 / 64 := by nlinarith
  set w := triEigColumnWord M T smin j with hw
  set r := M.div (M.lit 1) ν with hr
  have hl : |M.lit 1 - 1| ≤ u := by simpa using hM.lit 1
  have hl0 : M.lit 0 = 0 := hM.zero
  have hwj : w j = ⟨M.lit 1, 0⟩ := by simp [hw, triEigColumnWord, hl0]
  have hwk : ∀ k, k ≠ j → w k = shiftedTriSolveColumn M T smin j k := fun k hk => by
    have hk' : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
    simp only [hw, triEigColumnWord, shiftedTriSolveColumn, if_neg hk', hl0]
    split_ifs <;> rfl
  have hyj : shiftedTriSolveColumn M T smin j j = 1 := by simp [shiftedTriSolveColumn]
  have hW : 0 < ‖WithLp.toLp 2 w‖ := by
    have h1 : ‖w j‖ ≤ ‖WithLp.toLp 2 w‖ := PiLp.norm_apply_le (WithLp.toLp 2 w) j
    have h2 : |(w j).re| ≤ ‖w j‖ := Complex.abs_re_le_norm _
    rw [hwj] at h1 h2
    have h3 := (abs_le.mp hl).1
    have h4 := le_abs_self (M.lit 1)
    simp only at h2
    linarith
  have ha : (((2 * N : ℕ) : ℝ) + 2) * u ≤ 1 / 16 := by push_cast; nlinarith
  have ha0 : 0 ≤ (((2 * N : ℕ) : ℝ) + 2) * u := by positivity
  have hν0 : ν ≠ 0 := by
    have : 0 < ν := lt_of_lt_of_le (mul_pos (by linarith) hW) hν₁
    exact this.ne'
  have hrdiv : |r - M.lit 1 / ν| ≤ u * |M.lit 1 / ν| := by
    simpa [hr] using hM.div (M.lit 1) ν hν0
  constructor
  · have hd := norm_scaled_sub_le hM hu0 w r
    have hn : ‖(r : ℂ) • WithLp.toLp 2 w‖ = |r| * ‖WithLp.toLp 2 w‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hZ := (abs_norm_sub_norm_le _ _).trans hd
    rw [hn] at hZ
    have := abs_column_norm_sub_one_le hu0 hu64 ha0 ha hW hν₁ hν₂ hl hrdiv hZ
    push_cast at this
    calc _ ≤ _ := this
      _ = 4 * ((N : ℝ) + 2) * u := by ring
  · have hb := shiftedTriSolve_isComponentwiseBackwardSolution_of_le hM hu le_rfl hTu hsmin j
    have hz : ∀ k, ‖(⟨M.mul (w k).re r, M.mul (w k).im r⟩ : ℂ) -
        (r : ℂ) * shiftedTriSolveColumn M T smin j k‖ ≤
        (3 * u) * ‖(r : ℂ) * shiftedTriSolveColumn M T smin j k‖ := fun k => by
      by_cases hk : k = j
      · subst hk
        rw [hyj, mul_one, Complex.norm_real, Real.norm_eq_abs, hwj]
        have h0 : M.mul 0 r = 0 := by
          have := hM.mul 0 r
          simpa using this
        have e : (⟨M.mul (M.lit 1) r, M.mul 0 r⟩ : ℂ) - (r : ℂ) = ((M.mul (M.lit 1) r - r : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [h0]
        simp only
        rw [e, Complex.norm_real, Real.norm_eq_abs]
        have h1 := hM.mul (M.lit 1) r
        simp only [id, abs_mul] at h1
        have h2 : |M.lit 1| ≤ 1 + u := by
          have := abs_sub_abs_le_abs_sub (M.lit 1) 1
          simp only [abs_one] at this
          linarith
        have h3 : |M.lit 1 * r - r| ≤ u * |r| := by
          rw [show M.lit 1 * r - r = (M.lit 1 - 1) * r by ring, abs_mul]
          exact mul_le_mul_of_nonneg_right hl (abs_nonneg _)
        have h4 := abs_sub_le (M.mul (M.lit 1) r) (M.lit 1 * r) r
        have h5 : u * (|M.lit 1| * |r|) ≤ u * ((1 + u) * |r|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) hu0
        nlinarith [abs_nonneg r, mul_nonneg hu0 (abs_nonneg r)]
      · have := norm_mul_pair_sub_le hM hu0 (w k) r
        rw [hwk k hk] at this ⊢
        have h3 : u * ‖(r : ℂ) * shiftedTriSolveColumn M T smin j k‖ ≤
            3 * u * ‖(r : ℂ) * shiftedTriSolveColumn M T smin j k‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        exact this.trans h3
    have hs := isComponentwiseBackwardSolution_of_norm_sub_smul_le hb (by linarith : 0 ≤ 3 * u)
      (by linarith) hz
    refine hs.mono ?_ ?_
    · rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg hu0 hN0, mul_nonneg (mul_nonneg hu0 hN0) hu0]
    · split_ifs
      · rw [div_le_iff₀ (by linarith)]
        nlinarith
      · simp

/-- The invariant of the loop over the columns: the first `k` columns are stored with the
property `Φ`, and the flag records whether one of their pivots was floored. -/
private def ColsInv {N : ℕ} (M : Machine ℝ) (T : Matrix (Fin N) (Fin N) ℂ) (smin : ℝ)
    (t sm y g : ℕ × ℕ) (g₀ : Option ℝ) (Φ : Fin N → (Fin N → ℂ) → Bool → Prop) (k : ℕ)
    (μ : Mem ℝ) : Prop :=
  HoldsMatrix t T μ.store ∧ μ.store.get sm.1 sm.2 = some smin ∧
    ∃ (Yp : Fin N → Fin N → ℂ) (fp : Fin N → Bool),
      (∀ c : Fin N, (c : ℕ) < k →
        (∀ i : Fin N, μ.store.get y.1 (y.2 + 2 * (c * N + i)) = some (Yp c i).re ∧
          μ.store.get y.1 (y.2 + 2 * (c * N + i) + 1) = some (Yp c i).im) ∧ Φ c (Yp c) (fp c)) ∧
      ((∃ c : Fin N, (c : ℕ) < k ∧ fp c = true) → μ.store.get g.1 g.2 = some (M.lit 1)) ∧
      ((∀ c : Fin N, (c : ℕ) < k → fp c = false) → μ.store.get g.1 g.2 = g₀)

/-- One column extends the invariant of the loop over the columns. -/
private theorem ColsInv.step {N : ℕ} {M : Machine ℝ} {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ}
    {t sm y g : ℕ × ℕ} {g₀ : Option ℝ} {Φ : Fin N → (Fin N → ℂ) → Bool → Prop} {k : ℕ}
    (hk : k < N) {μ μ' : Mem ℝ} (h : ColsInv M T smin t sm y g g₀ Φ k μ)
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1])
    (hfr : μ.store.EqOff (Store.inBlock y.1 (y.2 + 2 * (k * N)) (2 * N) ⊔
      Store.inBlock g.1 g.2 1) μ'.store) {yv : Fin N → ℂ} {fl : Bool}
    (hcells : ∀ i : Fin N, μ'.store.get y.1 (y.2 + 2 * (k * N + i)) = some (yv i).re ∧
      μ'.store.get y.1 (y.2 + 2 * (k * N + i) + 1) = some (yv i).im)
    (hΦ : Φ ⟨k, hk⟩ yv fl) (h1 : fl = true → μ'.store.get g.1 g.2 = some (M.lit 1))
    (h0 : fl = false → μ'.store.get g.1 g.2 = μ.store.get g.1 g.2) :
    ColsInv M T smin t sm y g g₀ Φ (k + 1) μ' := by
  obtain ⟨hT, hsm, Yp, fp, hc, hf1, hf0⟩ := h
  have hcb : Store.inBlock y.1 (y.2 + 2 * (k * N)) (2 * N) ≤
      Store.inBlock y.1 y.2 (2 * (N * N)) := by
    have := col_lt hk (show N - 1 < N by omega)
    exact Fp.inBlock_le_inBlock (by omega) (by omega)
  have hyT : Fp.Disj (Store.inBlock y.1 y.2 (2 * (N * N))) (Store.inBlock t.1 t.2 (2 * (N * N))) :=
    (hap.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)).symm
  have hyS : Fp.Disj (Store.inBlock y.1 y.2 (2 * (N * N))) (Store.inBlock sm.1 sm.2 1) :=
    (hap.2.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)).symm
  have hgT : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock t.1 t.2 (2 * (N * N))) :=
    (hap.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)).symm
  have hgS : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock sm.1 sm.2 1) :=
    (hap.2.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)).symm
  have hyg : Fp.Disj (Store.inBlock y.1 y.2 (2 * (N * N))) (Store.inBlock g.1 g.2 1) :=
    hap.2.2.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)
  have hold : ∀ c : Fin N, (c : ℕ) < k → ∀ i : Fin N, ∀ e ≤ 1,
      μ'.store.get y.1 (y.2 + 2 * (c * N + i) + e) = μ.store.get y.1 (y.2 + 2 * (c * N + i) + e) := by
    intro c hck i e he
    have hcN : (c + 1) * N ≤ k * N := Nat.mul_le_mul_right N hck
    have e₁ : (c + 1) * N = c * N + N := by ring
    have hi := i.isLt
    have hlt := col_lt c.isLt i.isLt
    refine hfr.2 _ _ ?_
    rintro (hb | hb)
    · have := hb.2.1; omega
    · exact hyg y.1 _ ⟨rfl, by omega, by omega⟩ hb
  refine ⟨hT.of_eqOff hfr (Fp.disj_sup_left.mpr ⟨hyT.mono hcb le_rfl, hgT⟩),
    hfr.keep (Store.readsOnly_get _ _ _) (Fp.disj_sup_left.mpr ⟨hyS.mono hcb le_rfl, hgS⟩) hsm,
    Function.update Yp ⟨k, hk⟩ yv, Function.update fp ⟨k, hk⟩ fl, fun c hc' => ?_, ?_, ?_⟩
  · by_cases hck : (c : ℕ) = k
    · obtain rfl : c = ⟨k, hk⟩ := Fin.ext hck
      simpa only [Function.update_self] using And.intro hcells hΦ
    · have hlt : (c : ℕ) < k := by omega
      have hne : c ≠ ⟨k, hk⟩ := fun h => hck (by rw [h])
      simp only [Function.update_of_ne hne]
      refine ⟨fun i => ⟨?_, ?_⟩, (hc c hlt).2⟩
      · have := hold c hlt i 0 (by omega)
        simp only [Nat.add_zero] at this
        rw [this]; exact ((hc c hlt).1 i).1
      · rw [hold c hlt i 1 le_rfl]; exact ((hc c hlt).1 i).2
  · rintro ⟨c, hck, hfc⟩
    by_cases hcq : (c : ℕ) = k
    · obtain rfl : c = ⟨k, hk⟩ := Fin.ext hcq
      rw [Function.update_self] at hfc
      exact h1 hfc
    · have hne : c ≠ ⟨k, hk⟩ := fun h => hcq (by rw [h])
      rw [Function.update_of_ne hne] at hfc
      cases hfl : fl with
      | true => exact h1 hfl
      | false => rw [h0 hfl]; exact hf1 ⟨c, by omega, hfc⟩
  · intro hall
    have hfl : fl = false := by simpa using hall ⟨k, hk⟩ (by simp)
    rw [h0 hfl]
    refine hf0 fun c hck => ?_
    have hne : c ≠ ⟨k, hk⟩ := fun h => by
      have : (c : ℕ) = k := by rw [h]
      omega
    simpa [Function.update_of_ne hne] using hall c (by omega)

/-- **The loop over the columns**: if every column stores a vector with the property `Φ` and
updates the flag, the program stores a matrix whose columns have `Φ`, with the flag the literal
$1$ when a pivot of some column was floored and unchanged otherwise. -/
private theorem triEigenvectors_loop {M : Machine ℝ} {I : Interp O Q ℝ} {N : ℕ} {t sm y g : ℕ × ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {τ : Tape ℝ} {μ : Mem ℝ}
    {Φ : Fin N → (Fin N → ℂ) → Bool → Prop}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1])
    (hcol : ∀ (j : Fin N) (μ' : Mem ℝ), HoldsMatrix t T μ'.store →
      μ'.store.get sm.1 sm.2 = some smin → μ'.Live [t, sm, y, g] →
      μ'.Room [y, g] [2 * (N * N), 1] →
      Writes .total I τ (triEigColumn (O := O) (Q := Q)) (Env.frame [N, j] [t, sm, y, g, y, g])
        (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) ⊔ Store.inBlock g.1 g.2 1)
        (fun μ'' => ∃ (yv : Fin N → ℂ) (fl : Bool),
          (∀ i : Fin N, μ''.store.get y.1 (y.2 + 2 * (j * N + i)) = some (yv i).re ∧
            μ''.store.get y.1 (y.2 + 2 * (j * N + i) + 1) = some (yv i).im) ∧ Φ j yv fl ∧
          (fl = true → μ''.store.get g.1 g.2 = some (M.lit 1)) ∧
          (fl = false → μ''.store.get g.1 g.2 = μ'.store.get g.1 g.2)) μ') :
    Writes .total I τ (triEigenvectors (O := O) (Q := Q)) (Env.frame [N] [t, sm, y, g, y, g])
      (Store.inBlock y.1 y.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ (Y : Matrix (Fin N) (Fin N) ℂ) (f : Fin N → Bool), HoldsMatrix y Y μ'.store ∧
        (∀ j, Φ j (Y.col j) (f j)) ∧ ((∃ j, f j = true) → μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        ((∀ j, f j = false) → μ'.store.get g.1 g.2 = μ.store.get g.1 g.2)) μ := by
  have hle : ∀ k < N, Store.inBlock y.1 (y.2 + 2 * (k * N)) (2 * N) ⊔ Store.inBlock g.1 g.2 1 ≤
      Store.inBlock y.1 y.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1 := fun k hk => by
    have := col_lt hk (show N - 1 < N by omega)
    exact sup_le_sup (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl
  simp only [Mem.room_cons, Mem.room_nil, and_true] at hroom
  refine (writes_loop (N := N) rfl (fun _ => Store.inBlock y.1 y.2 (2 * (N * N)) ⊔
      Store.inBlock g.1 g.2 1) (fun _ _ => le_rfl)
    (ColsInv M T smin t sm y g (μ.store.get g.1 g.2) Φ)
    ⟨hT, hsm, fun _ _ => 0, fun _ => false, fun c hc => absurd hc (by omega),
      fun ⟨c, hc, _⟩ => absurd hc (by omega), fun _ => rfl⟩ fun k hk μ' hfr hI => ?_).mono le_rfl ?_
  · have hlv : μ'.Live [t, sm, y, g] := hl.congr hfr.length_eq
    have hrm : μ'.Room [y, g] [2 * (N * N), 1] := by
      simp only [Mem.room_cons, Mem.room_nil, and_true, hfr.len_eq]
      exact hroom
    have hlv' : μ'.Live [t, sm, y, g, y, g] := by
      have h := hlv
      simp only [Mem.live_cons, Mem.live_nil, and_true] at h ⊢
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, h.2.2.1, h.2.2.2⟩
    refine ((hcol ⟨k, hk⟩ μ' hI.1 hI.2.1 hlv hrm).in_frame rfl rfl hlv').mono (hle k hk) ?_
    rintro μ'' h'' ⟨yv, fl, hc, hΦ, h1, h0⟩
    exact ColsInv.step hk hI hap h'' hc hΦ h1 h0
  · rintro μ' - ⟨-, -, Yp, fp, hc, hf1, hf0⟩
    refine ⟨Matrix.of fun i j => Yp j i, fp, ?_, fun j => (hc j j.isLt).2, fun ⟨c, hfc⟩ =>
      hf1 ⟨c, c.isLt, hfc⟩, fun hall => hf0 fun c _ => hall c⟩
    exact HoldsMatrix.of_get (fun i j => ((hc j j.isLt).1 i).1) fun i j => ((hc j j.isLt).1 i).2

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

/-- **One eigenvector column under the standard model, with a positive floor**: the conclusion
of `NLAlib.Schur.triEigColumn_writes` for $s_{\min} > 0$. A zero floor can divide by a zero
pivot. -/
theorem triEigColumn_writes_of_pos {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ}
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {t sm y g : ℕ × ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    (hTu : T.IsUpperTriangular) {smin : ℝ} (hsmin : 0 < smin) (j : Fin N) {τ : Tape ℝ}
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
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hun : (((2 * N : ℕ) : ℝ) + 2) * u ≤ 1 / 2 := by push_cast; nlinarith
  have hu32 : u ≤ 1 / 32 := by nlinarith
  refine (triEigColumn_writes_word (Pν := fun ν =>
      (1 - (((2 * N : ℕ) : ℝ) + 2) * u) * ‖WithLp.toLp 2 (triEigColumnWord M T smin j)‖ ≤ ν ∧
      ν ≤ (1 + (((2 * N : ℕ) : ℝ) + 2) * u) * ‖WithLp.toLp 2 (triEigColumnWord M T smin j)‖)
    hS hL hC j.isLt hT hsm hl hroom hap fun m z hlv hne hz hrd => ?_).mono le_rfl ?_
  · refine (RoundedScalarBlas.nrm2_writes_stdModel hS hM hun hlv hrd hz (Ne.symm hne)).mono le_rfl
      fun μ' _ ⟨_, v, hv, h₁, h₂⟩ => ⟨v, hv, ?_, ?_⟩
    · rwa [sqrt_sum_sq_columnWords] at h₁
    · rwa [sqrt_sum_sq_columnWords] at h₂
  · rintro μ' - ⟨ν, ⟨hν₁, hν₂⟩, hc, h1, h0⟩
    obtain ⟨hn, hb⟩ := triEigColumn_scaled hM hu hTu hsmin j hν₁ hν₂
    exact ⟨(fun i => (⟨M.mul (triEigColumnWord M T smin j i).re (M.div (M.lit 1) ν),
      M.mul (triEigColumnWord M T smin j i).im (M.div (M.lit 1) ν)⟩ : ℂ)),
      shiftedTriSolveFlag M T smin j, hc, hn, hb, h1, h0,
      fun hgap => shiftedTriSolve_flag hM hu32 hsmin.le j hgap⟩

/-- The columns on any scalar machine: a stored matrix and the flags of the pivots. -/
private theorem triEigenvectors_writes_flags {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ} {t sm y g : ℕ × ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (triEigenvectors (O := O) (Q := Q)) (Env.frame [N] [t, sm, y, g, y, g])
      (Store.inBlock y.1 y.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ (Y : Matrix (Fin N) (Fin N) ℂ) (f : Fin N → Bool), HoldsMatrix y Y μ'.store ∧
        (∀ j, f j = shiftedTriSolveFlag M T smin j) ∧
        ((∃ j, f j = true) → μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        ((∀ j, f j = false) → μ'.store.get g.1 g.2 = μ.store.get g.1 g.2)) μ := by
  refine (triEigenvectors_loop (Φ := fun j _ fl => fl = shiftedTriSolveFlag M T smin j)
    hT hsm hl hroom hap fun j μ' hT' hsm' hl' hrm' => ?_).mono le_rfl fun _ _ h => h
  refine (triEigColumn_writes_word (Pν := fun _ => True) hS hL hC j.isLt hT' hsm' hl' hrm' hap
    fun m z hlv hne hz hrd => ?_).mono le_rfl ?_
  · exact (RoundedScalarBlas.nrm2_writes hS hlv hrd hz (Ne.symm hne)).mono le_rfl
      fun _ _ ⟨v, hv⟩ => ⟨v, hv, trivial⟩
  · rintro μ'' - ⟨ν, -, hc, h1, h0⟩
    exact ⟨(fun i => (⟨M.mul (triEigColumnWord M T smin j i).re (M.div (M.lit 1) ν),
      M.mul (triEigColumnWord M T smin j i).im (M.div (M.lit 1) ν)⟩ : ℂ)), _, hc, rfl, h1, h0⟩

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
  refine (triEigenvectors_writes_flags hS hL hC hT hsm hl hroom hap).mono le_rfl ?_
  rintro μ' - ⟨Y, f, hY, -, h1, h0⟩
  refine ⟨⟨Y, hY⟩, ?_⟩
  by_cases hex : ∃ j, f j = true
  · exact ⟨_, h1 hex⟩
  · obtain ⟨x, hx⟩ := hg
    refine ⟨x, (h0 fun j => ?_).trans hx⟩
    cases hj : f j with
    | false => rfl
    | true => exact absurd ⟨j, hj⟩ hex

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

/-- **The eigenvector columns are an approximate triangular eigenbasis, with a positive floor**:
the conclusion of `NLAlib.Schur.triEigenvectors_isTriangularEigenbasisApprox` for
$s_{\min} > 0$. -/
theorem triEigenvectors_isTriangularEigenbasisApprox_of_pos {M : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {N : ℕ} (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {t sm y g : ℕ × ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    (hTu : T.IsUpperTriangular) {smin : ℝ} (hsmin : 0 < smin) {τ : Tape ℝ} {μ : Mem ℝ}
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
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hu1 : u < 1 := by nlinarith
  have hσ : (0 : ℝ) ≤ 7 / 2 * smin := by positivity
  refine (triEigenvectors_loop (Φ := fun j yv fl => |‖WithLp.toLp 2 yv‖ - 1| ≤
      4 * ((N : ℝ) + 2) * u ∧ IsComponentwiseBackwardSolution (16 * ((N : ℝ) + 1) * u)
        (if fl then 7 / 2 * smin else 0) (T - T j j • 1) 0 yv)
    hT hsm hl hroom hap fun j μ' hT' hsm' hl' hrm' =>
      (triEigColumn_writes_of_pos hS hM hL hC hu hTu hsmin j hT' hsm' hl' hrm' hap).mono le_rfl
        fun μ'' _ ⟨yv, fl, hc, hn, hb, h1, h0, _⟩ => ⟨yv, fl, hc, ⟨hn, hb⟩, h1, h0⟩).mono le_rfl ?_
  rintro μ' - ⟨Y, f, hY, hΦ, h1, h0⟩
  have hwide : IsTriangularEigenbasisApprox (16 * ((N : ℝ) + 1) * u) (7 / 2 * smin)
      (4 * ((N : ℝ) + 2) * u) T Y := fun j =>
    ⟨(hΦ j).1, (hΦ j).2.mono le_rfl (by split_ifs <;> first | exact le_rfl | exact hσ)⟩
  by_cases hex : ∃ j, f j = true
  · refine ⟨Y, hY, Or.inr (h1 hex), hwide, fun h => ?_⟩
    have e : M.lit 1 = 0 := Option.some.inj ((h1 hex).symm.trans h)
    have hl1 := hM.lit 1
    simp only [id, e, Rat.cast_one, abs_one, mul_one, zero_sub, abs_neg] at hl1
    linarith
  · have hall : ∀ j, f j = false := fun j => by
      cases hj : f j with
      | false => rfl
      | true => exact absurd ⟨j, hj⟩ hex
    refine ⟨Y, hY, Or.inl ((h0 hall).trans hg), hwide, fun _ j => ⟨(hΦ j).1, ?_⟩⟩
    simpa [hall j] using (hΦ j).2

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
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hu32 : u ≤ 1 / 32 := by nlinarith
  refine (triEigenvectors_writes_flags hS hL hC hT hsm hl hroom hap).mono le_rfl ?_
  rintro μ' - ⟨Y, f, -, hf, -, h0⟩
  refine (h0 fun j => ?_).trans hg
  rw [hf j]
  exact shiftedTriSolve_flag hM hu32 hsmin j fun i hi => hgap i j hi.ne

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
