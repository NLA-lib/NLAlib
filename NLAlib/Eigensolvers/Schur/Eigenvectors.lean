/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Completion
public import NLAlib.Eigensolvers.Schur.ShiftedTriSolveWrites
public import NLAlib.Matrix.FinitePrecision.RoundedScaling
public import NLAlib.Matrix.Spectral.TriangularEigenvectors
public import NLAlib.Ops.Profiles.RoundedScalarBlas
public import NLAlib.Ops.Logic.ScalarLoop
public import NLAlib.Ops.Blas.MatrixCorrect
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

* `NLAlib.Schur.triEigColumn_writes_word`: the words of one column on any scalar machine.
* `NLAlib.Schur.triEigColumn_writes_of_pos`,
  `NLAlib.Schur.triEigenvectors_isTriangularEigenbasisApprox_of_pos`: the columns at a positive
  floor.
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
      (fun μ' => ∃ ν : ℝ, Pν ν ∧ ∀ k < 2 * N, ∀ v,
        μ.store.get y.1 (y.2 + 2 * (j * N) + k) = some v →
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
  have hh := colFill_holds (M := M) (T := T) (smin := smin) (y := y) (N := N) (j := j)
    (s := μ₃.store)
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
  · have hd := hM.norm_scaled_sub_le hu0 w r
    have hn : ‖(r : ℂ) • WithLp.toLp 2 w‖ = |r| * ‖WithLp.toLp 2 w‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hZ := (abs_norm_sub_norm_le _ _).trans hd
    rw [hn] at hZ
    have := abs_norm_roundedScale_sub_one_le hu0 hu64 ha0 ha hW hν₁ hν₂ hl hrdiv hZ
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
        exact hM.norm_mul_unit_sub_le hu0 (by linarith) hl r
      · have := hM.norm_mul_pair_sub_le hu0 (w k) r
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
      μ'.store.get y.1 (y.2 + 2 * (c * N + i) + e) =
        μ.store.get y.1 (y.2 + 2 * (c * N + i) + e) := by
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
$s_{\min} > 0$, with the flag $0$ when $\lvert t_{ii} - t_{jj}\rvert > 2s_{\min}$ for $i \ne j$. -/
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
          IsTriangularEigenbasisApprox (16 * ((N : ℝ) + 1) * u) 0 (4 * ((N : ℝ) + 2) * u) T Y) ∧
        ((∀ i j, i ≠ j → 2 * smin < ‖T i i - T j j‖) → μ'.store.get g.1 g.2 = some 0))
      μ := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hu1 : u < 1 := by nlinarith
  have hσ : (0 : ℝ) ≤ 7 / 2 * smin := by positivity
  refine (triEigenvectors_loop (Φ := fun j yv fl => |‖WithLp.toLp 2 yv‖ - 1| ≤
      4 * ((N : ℝ) + 2) * u ∧ IsComponentwiseBackwardSolution (16 * ((N : ℝ) + 1) * u)
        (if fl then 7 / 2 * smin else 0) (T - T j j • 1) 0 yv ∧
        ((∀ i : Fin N, i < j → 2 * smin < ‖T i i - T j j‖) → fl = false))
    hT hsm hl hroom hap fun j μ' hT' hsm' hl' hrm' =>
      (triEigColumn_writes_of_pos hS hM hL hC hu hTu hsmin j hT' hsm' hl' hrm' hap).mono le_rfl
        fun μ'' _ ⟨yv, fl, hc, hn, hb, h1, h0, hgp⟩ =>
          ⟨yv, fl, hc, ⟨hn, hb, hgp⟩, h1, h0⟩).mono le_rfl ?_
  rintro μ' - ⟨Y, f, hY, hΦ, h1, h0⟩
  have hwide : IsTriangularEigenbasisApprox (16 * ((N : ℝ) + 1) * u) (7 / 2 * smin)
      (4 * ((N : ℝ) + 2) * u) T Y := fun j =>
    ⟨(hΦ j).1, (hΦ j).2.1.mono le_rfl (by split_ifs <;> first | exact le_rfl | exact hσ)⟩
  have hgapg : (∀ i j, i ≠ j → 2 * smin < ‖T i i - T j j‖) → μ'.store.get g.1 g.2 = some 0 :=
    fun hgap => (h0 fun j => (hΦ j).2.2 fun i hi => hgap i j hi.ne).trans hg
  by_cases hex : ∃ j, f j = true
  · refine ⟨Y, hY, Or.inr (h1 hex), hwide, fun h => ?_, hgapg⟩
    have e : M.lit 1 = 0 := Option.some.inj ((h1 hex).symm.trans h)
    have hl1 := hM.lit 1
    simp only [id, e, Rat.cast_one, abs_one, mul_one, zero_sub, abs_neg] at hl1
    linarith
  · have hall : ∀ j, f j = false := fun j => by
      cases hj : f j with
      | false => rfl
      | true => exact absurd ⟨j, hj⟩ hex
    refine ⟨Y, hY, Or.inl ((h0 hall).trans hg), hwide, fun _ j => ⟨(hΦ j).1, ?_⟩, hgapg⟩
    simpa [hall j] using (hΦ j).2.1

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

/-- The branch of the stage on a positive norm: the floor, the columns and the product. -/
private def stageThen : Stmt O Q :=
  .seq (.call (Has.inj ScalarOp.mul) [] [⟨2, .var 4⟩, ⟨5, .const 0⟩] [⟨6, .const 0⟩]) <|
  .seq (.frame [.var 0] [⟨0, .var 2⟩, ⟨6, .const 0⟩, ⟨7, .const 0⟩, ⟨4, .var 6⟩, ⟨7, .const 0⟩,
    ⟨4, .var 6⟩] triEigenvectors)
    (.frame [.var 0, .var 0, .var 0, .var 0, .var 0, .var 0, .const 0]
      [⟨1, .var 3⟩, ⟨7, .const 0⟩, ⟨3, .var 5⟩] matMulOn)

/-- The environment of the stage after its three scratch blocks. -/
private def stageEnv (N ne : ℕ) (a uo pe v g : ℕ × ℕ) (L : ℕ) : Env :=
  ⟨[N, ne, a.2, uo.2, pe.2, v.2, g.2], [a.1, uo.1, pe.1, v.1, g.1, L, L + 1, L + 2]⟩

/-- The branch of the stage on a positive norm stores the rounded product of $\mathbf{U}$ and the
columns. -/
private theorem stageThen_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {N ne : ℕ} {a uo pe v g : ℕ × ℕ} {L : ℕ} {T U : Matrix (Fin N) (Fin N) ℂ} {ρ x : ℝ}
    {τ : Tape ℝ} {μ : Mem ℝ} {Ψ : Matrix (Fin N) (Fin N) ℂ → Option ℝ → Prop}
    (hlt : a.1 < L ∧ uo.1 < L ∧ pe.1 < L ∧ v.1 < L ∧ g.1 < L) (hlen : μ.store.length = L + 3)
    (hl0 : μ.store.len (L + 1) = 1) (hl2 : μ.store.len (L + 2) = 2 * (N * N))
    (hT : HoldsMatrix a T μ.store) (hU : HoldsMatrix uo U μ.store)
    (hρ : μ.store.get pe.1 pe.2 = some ρ) (hx : μ.store.get L 0 = some x)
    (hg : μ.store.get g.1 g.2 = some (M.lit 0))
    (hv : v.2 + 2 * (N * N) ≤ μ.store.len v.1) (hgr : g.2 + 1 ≤ μ.store.len g.1)
    (huv : Fp.Disj (Store.inBlock uo.1 uo.2 (2 * (N * N))) (Store.inBlock v.1 v.2 (2 * (N * N))))
    (hug : Fp.Disj (Store.inBlock uo.1 uo.2 (2 * (N * N))) (Store.inBlock g.1 g.2 1))
    (hag : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock g.1 g.2 1))
    (hvg : ¬ Store.inBlock v.1 v.2 (2 * (N * N)) g.1 g.2)
    (hev : ∀ m : Mem ℝ, HoldsMatrix a T m.store → m.store.get (L + 1) 0 = some (M.mul ρ x) →
      m.store.get g.1 g.2 = some (M.lit 0) → m.Live [a, (L + 1, 0), (L + 2, 0), g] →
      m.Room [(L + 2, 0), g] [2 * (N * N), 1] →
      Fp.Apart [a, (L + 1, 0), (L + 2, 0), g] [2 * (N * N), 1, 2 * (N * N), 1] →
      Writes .total I τ (triEigenvectors (O := O) (Q := Q))
        (Env.frame [N] [a, (L + 1, 0), (L + 2, 0), g, (L + 2, 0), g])
        (Store.inBlock (L + 2) 0 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
        (fun μ' => ∃ Y : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix (L + 2, 0) Y μ'.store ∧
          Ψ Y (μ'.store.get g.1 g.2)) m) :
    Writes .total I τ (stageThen (O := O) (Q := Q)) (stageEnv N ne a uo pe v g L)
      (Store.inBlock v.1 v.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1 ⊔ Fp.above L)
      (fun μ' => ∃ Y : Matrix (Fin N) (Fin N) ℂ, Ψ Y (μ'.store.get g.1 g.2) ∧
        HoldsMatrix v (matMulWord M U Y) μ'.store) μ := by
  obtain ⟨hal, hul, hpl, hvl, hgl⟩ := hlt
  have hdiv := writes_call_bin (ins := [⟨2, .var 4⟩, ⟨5, .const 0⟩]) (outs := [⟨6, .const 0⟩])
    (x := pe) (y := (L, 0)) (z := (L + 1, 0)) (ρ := stageEnv N ne a uo pe v g L) (τ := τ) (m := μ)
    (hS .mul) rfl rfl trivial hρ hx rfl fun _ => ⟨by
      simp only [Mem.live_cons, Mem.live_nil, and_true, hlen]; omega, by simp [hl0]⟩
  refine hdiv.seq_le (fun b _ h => Or.inr (show L ≤ b by have := h.1; omega))
    fun μ₁ h₁ ⟨_, g₁⟩ => ?_
  have hnL : ∀ {b o}, b < L → ¬ Store.inBlock (L + 1) 0 1 b o := fun hb h => by
    have := h.1; omega
  have hT₁ : HoldsMatrix a T μ₁.store :=
    hT.of_eqOff h₁ fun b i h h' => by have := h.1; have := h'.1; omega
  have hU₁ : HoldsMatrix uo U μ₁.store :=
    hU.of_eqOff h₁ fun b i h h' => by have := h.1; have := h'.1; omega
  have hg₁ : μ₁.store.get g.1 g.2 = some (M.lit 0) := by rw [h₁.2 _ _ (hnL hgl)]; exact hg
  have hap₁ : Fp.Apart [a, (L + 1, 0), (L + 2, 0), g] [2 * (N * N), 1, 2 * (N * N), 1] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Fp.blocks]
      refine Fp.disj_sup_right.mpr ⟨fun b i h h' => ?_, Fp.disj_sup_right.mpr
        ⟨fun b i h h' => ?_, Fp.disj_sup_right.mpr ⟨hag, fun _ _ _ h' => h'⟩⟩⟩
      · have := h.1; have := h'.1; omega
      · have := h.1; have := h'.1; omega
    · simp only [Fp.blocks]
      refine Fp.disj_sup_right.mpr ⟨fun b i h h' => ?_, Fp.disj_sup_right.mpr
        ⟨fun b i h h' => ?_, fun _ _ _ h' => h'⟩⟩
      · have := h.1; have := h'.1; omega
      · have := h.1; have := h'.1; omega
    · simp only [Fp.blocks]
      refine Fp.disj_sup_right.mpr ⟨fun b i h h' => ?_, fun _ _ _ h' => h'⟩
      have := h.1; have := h'.1; omega
    · simp only [Fp.blocks, Fp.Apart]
      exact ⟨fun _ _ _ h' => h', trivial⟩
  have hlv₁ : μ₁.Live [a, (L + 1, 0), (L + 2, 0), g] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true, h₁.length_eq, hlen]; omega
  have hrm₁ : μ₁.Room [(L + 2, 0), g] [2 * (N * N), 1] := by
    simp only [Mem.room_cons, Mem.room_nil, and_true, h₁.len_eq, hl2]
    exact ⟨by omega, hgr⟩
  have hlv₁' : μ₁.Live [a, (L + 1, 0), (L + 2, 0), g, (L + 2, 0), g] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true, h₁.length_eq, hlen]; omega
  refine (hev μ₁ hT₁ g₁ hg₁ hlv₁ hrm₁ hap₁).frame_seq_le rfl rfl hlv₁'
    (sup_le (fun b _ h => Or.inr (show L ≤ b by have := h.1; omega))
      (le_sup_of_le_left le_sup_right)) fun μ₂ h₂ ⟨Y, hY, hΨ⟩ => ?_
  have hU₂ : HoldsMatrix uo U μ₂.store := hU₁.of_eqOff h₂ (Fp.disj_sup_left.mpr
    ⟨fun b i h h' => by have := h.1; have := h'.1; omega, hug.symm⟩)
  have hlv₂ : μ₂.Live [uo, (L + 2, 0), v] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true, h₂.length_eq, h₁.length_eq, hlen]; omega
  have hmul := matMulOn_writes_word (O := O) (Q := Q) hS (τ := τ) (μ := μ₂) (z := v) hU₂ hY hlv₂
    (by rw [h₂.len_eq, h₁.len_eq]; exact hv) huv
    (fun b i h h' => by have := h.1; have := h'.1; omega)
  refine (hmul.in_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hlv₂ ⊢; exact hlv₂)).mono
    (le_sup_of_le_left le_sup_left) fun μ₃ h₃ ⟨_, hV⟩ => ⟨Y, ?_, hV⟩
  have hgv : μ₃.store.get g.1 g.2 = μ₂.store.get g.1 g.2 := h₃.2 _ _ hvg
  rwa [hgv]

/-- The disjointness facts of the stage, from the apartness of its operands. -/
private theorem stage_disj {N ne : ℕ} {a uo pe v g : ℕ × ℕ}
    (hap : Fp.Apart [a, uo, pe, v, g] [2 * (N * N), 2 * (N * N), ne, 2 * (N * N), 1]) :
    Fp.Disj (Store.inBlock uo.1 uo.2 (2 * (N * N))) (Store.inBlock v.1 v.2 (2 * (N * N))) ∧
      Fp.Disj (Store.inBlock uo.1 uo.2 (2 * (N * N))) (Store.inBlock g.1 g.2 1) ∧
      Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock g.1 g.2 1) ∧
      ¬ Store.inBlock v.1 v.2 (2 * (N * N)) g.1 g.2 := by
  have hvg : Fp.Disj (Store.inBlock v.1 v.2 (2 * (N * N))) (Store.inBlock g.1 g.2 1) :=
    hap.2.2.2.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)
  exact ⟨hap.2.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub),
    hap.2.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub),
    hap.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub),
    fun h => hvg _ _ h ⟨rfl, le_rfl, by omega⟩⟩

/-- **The run of the stage**, for a norm word with the property `Pn` and columns with the property
`Ψ`: on a positive norm word the stage stores the rounded product of $\mathbf{U}$ and the columns;
otherwise $\mathbf{U}$ and the literal $0$ in the flag. -/
private theorem triEigvecStage_writes_of {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) {N ne : ℕ} (hne0 : 0 < ne) {a uo pe v g : ℕ × ℕ}
    {T U : Matrix (Fin N) (Fin N) ℂ} {ρ : ℝ} {τ : Tape ℝ} {μ : Mem ℝ} {Pn : ℝ → Prop}
    {Ψ : ℝ → Matrix (Fin N) (Fin N) ℂ → Option ℝ → Prop} (hpair : HoldsSchurPair a uo U T μ.store)
    (hρ : μ.store.get pe.1 pe.2 = some ρ) (hl : μ.Live [a, uo, pe, v, g])
    (hroom : μ.Room [v, g] [2 * (N * N), 1])
    (hap : Fp.Apart [a, uo, pe, v, g] [2 * (N * N), 2 * (N * N), ne, 2 * (N * N), 1])
    (hnorm : ∀ (m : Mem ℝ) (s : ℕ × ℕ), HoldsMatrix a T m.store → m.Live [a, s] →
      s.2 + 1 ≤ m.store.len s.1 → a.1 ≠ s.1 →
      Writes .total I τ (frobNormStage (O := O) (Q := Q)) (Env.frame [N] [a, s])
        (Store.inBlock s.1 s.2 1) (fun μ' => ∃ x : ℝ, μ'.store.get s.1 s.2 = some x ∧ Pn x) m)
    (hev : ∀ x, Pn x → 0 < x → ∀ (L : ℕ) (m : Mem ℝ), HoldsMatrix a T m.store →
      m.store.get (L + 1) 0 = some (M.mul ρ x) → m.store.get g.1 g.2 = some (M.lit 0) →
      m.Live [a, (L + 1, 0), (L + 2, 0), g] → m.Room [(L + 2, 0), g] [2 * (N * N), 1] →
      Fp.Apart [a, (L + 1, 0), (L + 2, 0), g] [2 * (N * N), 1, 2 * (N * N), 1] →
      Writes .total I τ (triEigenvectors (O := O) (Q := Q))
        (Env.frame [N] [a, (L + 1, 0), (L + 2, 0), g, (L + 2, 0), g])
        (Store.inBlock (L + 2) 0 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
        (fun μ' => ∃ Y : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix (L + 2, 0) Y μ'.store ∧
          Ψ x Y (μ'.store.get g.1 g.2)) m) :
    Writes .total I τ (triEigvecStage (O := O) (Q := Q)) (Env.frame [N, ne] [a, uo, pe, v, g])
      (Store.inBlock v.1 v.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ V : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix v V μ'.store ∧ ∃ x, Pn x ∧
        ((0 < x ∧ ∃ Y, Ψ x Y (μ'.store.get g.1 g.2) ∧ V = matMulWord M U Y) ∨
          (¬ 0 < x ∧ V = U ∧ μ'.store.get g.1 g.2 = some (M.lit 0)))) μ := by
  obtain ⟨hT, hU⟩ := hpair
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  obtain ⟨hal, hul, hpl, hvl, hgl⟩ := hl
  simp only [Mem.room_cons, Mem.room_nil, and_true] at hroom
  obtain ⟨hvr, hgr⟩ := hroom
  obtain ⟨huv, hug, hag, hvg⟩ := stage_disj hap
  change Writes .total I τ (Stmt.allocs [.const 1, .const 1, .const 2 * (.var 0 * .var 0)]
    (.seq (.call (Has.inj IndexOp.lit) [.const 0] [] [⟨4, .var 6⟩])
      (.seq (.frame [.var 0] [⟨0, .var 2⟩, ⟨5, .const 0⟩] frobNormStage)
        (.ite (Has.inj CmpTst.isPos) [] [⟨5, .const 0⟩] stageThen
          (.frame [.var 0, .var 0] [⟨1, .var 3⟩, ⟨3, .var 5⟩]
            (PairMatrix.copyRoutine (Op := O) (Tst := Q)).body))))) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [1, 1, 2 * (N * N)]) rfl
    (fun {s s' p} hB ⟨V, hV, x, hP, hc⟩ => ⟨V, hV.of_below hB hvl, x, hP, ?_⟩) ?_
  · have hge : Store.get s' g.1 g.2 = Store.get s g.1 g.2 := (hB g.1 hgl).2 g.2
    simpa only [hge] using hc
  intro s₁ hlen hlens hB
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  have hl0 : s₁.len L = 1 := by simpa using hlens 0 (by simp)
  have hl1 : s₁.len (L + 1) = 1 := by simpa using hlens 1 (by simp)
  have hl2 : s₁.len (L + 2) = 2 * (N * N) := by simpa using hlens 2 (by simp)
  have hrg : g.2 < s₁.len g.1 := by rw [(hB g.1 hgl).1]; omega
  refine (writes_indexLit (n := 0) (z := g) (out := ⟨4, .var 6⟩) hL rfl rfl hrg).seq_le
    (le_sup_of_le_left le_sup_right) fun μ₁ h₁ ⟨_, g₁⟩ => ?_
  have hne : ∀ {b}, b ≠ g.1 → ∀ o, ¬ Store.inBlock g.1 g.2 1 b o := fun hb _ h => hb h.1
  have hT₁ : HoldsMatrix a T μ₁.store :=
    (hT.of_below hB hal).of_eqOff h₁ fun b i h h' => hag b i h' h
  have hU₁ : HoldsMatrix uo U μ₁.store :=
    (hU.of_below hB hul).of_eqOff h₁ fun b i h h' => hug b i h' h
  have hlv : μ₁.Live [a, (L, 0)] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true, h₁.length_eq, hlen]; omega
  refine (hnorm μ₁ (L, 0) hT₁ hlv (by simp [h₁.len_eq, hl0])
    (by dsimp only; omega)).frame_seq_le rfl rfl hlv
    (fun b _ h => Or.inr (show L ≤ b from h.1 ▸ le_rfl)) fun μ₂ h₂ ⟨x, hx, hP⟩ => ?_
  have hL₂ : ∀ {b o}, b < L → μ₂.store.get b o = μ₁.store.get b o := fun hb =>
    h₂.2 _ _ fun h => by have := h.1; omega
  have hg₂ : μ₂.store.get g.1 g.2 = some (M.lit 0) := by
    rw [hL₂ hgl]; simpa using g₁
  have hT₂ : HoldsMatrix a T μ₂.store :=
    hT₁.of_eqOff h₂ fun b i h h' => by have := h.1; have := h'.1; omega
  have hU₂ : HoldsMatrix uo U μ₂.store :=
    hU₁.of_eqOff h₂ fun b i h h' => by have := h.1; have := h'.1; omega
  have hρ₂ : μ₂.store.get pe.1 pe.2 = some ρ := by
    rw [hL₂ hpl, h₁.2 _ _ ?_, (hB pe.1 hpl).2]
    · exact hρ
    · intro h
      have hpg : Fp.Disj (Store.inBlock pe.1 pe.2 ne) (Store.inBlock g.1 g.2 1) :=
        hap.2.2.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)
      exact hpg _ _ ⟨rfl, le_rfl, by omega⟩ h
  have hlen₂ : μ₂.store.length = L + 3 := by rw [h₂.length_eq, h₁.length_eq, hlen]
  have htest := hC.test_isPos (d := []) (x := (L, 0)) (m := μ₂) hx
  by_cases hpos : 0 < x
  · have hc : decide (0 < id x) = true := decide_eq_true hpos
    rw [hc] at htest
    refine writes_ite (c := true) (d := []) (a := [(L, 0)]) rfl rfl htest ?_
    refine (stageThen_writes (ne := ne) (Ψ := Ψ x) hS ⟨hal, hul, hpl, hvl, hgl⟩ hlen₂
      (by rw [h₂.len_eq, h₁.len_eq]; exact hl1) (by rw [h₂.len_eq, h₁.len_eq]; exact hl2)
      hT₂ hU₂ hρ₂ hx hg₂ (by rw [h₂.len_eq, h₁.len_eq, (hB v.1 hvl).1]; exact hvr)
      (by rw [h₂.len_eq, h₁.len_eq, (hB g.1 hgl).1]; omega) huv hug hag hvg
      (hev x hP hpos L)).mono le_rfl ?_
    rintro μ₃ - ⟨Y, hΨ, hV⟩
    exact ⟨_, hV, x, hP, Or.inl ⟨hpos, Y, hΨ, rfl⟩⟩
  · have hc : decide (0 < id x) = false := decide_eq_false hpos
    rw [hc] at htest
    refine writes_ite (c := false) (d := []) (a := [(L, 0)]) rfl rfl htest ?_
    have hlvc : μ₂.Live [uo, v] := by
      simp only [Mem.live_cons, Mem.live_nil, and_true, h₂.length_eq, h₁.length_eq, hlen]; omega
    have hcp := PairMatrix.copy_writes (Op := O) (Tst := Q) hS (τ := τ) (m := μ₂) (rows := N)
      (cols := N) hlvc huv hU₂ (by rw [h₂.len_eq, h₁.len_eq, (hB v.1 hvl).1]; exact hvr)
    refine (Writes.in_frame (ds := [.var 0, .var 0]) (args := [⟨1, .var 3⟩, ⟨3, .var 5⟩])
      (ρ := stageEnv N ne a uo pe v g L) hcp rfl rfl hlvc).mono
      (le_sup_of_le_left le_sup_left) ?_
    rintro μ₃ h₃ ⟨_, hV⟩
    refine ⟨U, hV, x, hP, Or.inr ⟨hpos, rfl, ?_⟩⟩
    rw [h₃.2 _ _ hvg]
    exact hg₂

/-- What the stage knows of its columns on a positive norm word, at the floor `smin`. -/
private def StageColumns {N : ℕ} (M : Machine ℝ) (u : ℝ) (T : Matrix (Fin N) (Fin N) ℂ)
    (smin : ℝ) (Y : Matrix (Fin N) (Fin N) ℂ) (gw : Option ℝ) : Prop :=
  (gw = some 0 ∨ gw = some (M.lit 1)) ∧ (T.IsUpperTriangular →
    IsTriangularEigenbasisApprox (16 * ((N : ℝ) + 1) * u) (7 / 2 * smin)
      (4 * ((N : ℝ) + 2) * u) T Y ∧
    (gw = some 0 →
      IsTriangularEigenbasisApprox (16 * ((N : ℝ) + 1) * u) 0 (4 * ((N : ℝ) + 2) * u) T Y) ∧
    ((∀ i j, i ≠ j → 2 * smin < ‖T i i - T j j‖) → gw = some 0))

/-- The columns of the stage at a positive floor, for any stored $\mathbf{T}$. -/
private theorem triEigenvectors_stageColumns {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ}
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {t sm y g : ℕ × ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    {smin : ℝ} (hsmin : 0 < smin) {τ : Tape ℝ} {μ : Mem ℝ}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hg : μ.store.get g.1 g.2 = some 0)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (triEigenvectors (O := O) (Q := Q)) (Env.frame [N] [t, sm, y, g, y, g])
      (Store.inBlock y.1 y.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ Y : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix y Y μ'.store ∧
        StageColumns M u T smin Y (μ'.store.get g.1 g.2)) μ := by
  by_cases hTu : T.IsUpperTriangular
  · refine (triEigenvectors_isTriangularEigenbasisApprox_of_pos hS hM hL hC hu hTu hsmin hT hsm
      hg hl hroom hap).mono le_rfl ?_
    rintro μ' - ⟨Y, hY, hf, ha, ha0, hgp⟩
    exact ⟨Y, hY, hf, fun _ => ⟨ha, ha0, hgp⟩⟩
  · refine (triEigenvectors_writes_flags hS hL hC hT hsm hl hroom hap).mono le_rfl ?_
    rintro μ' - ⟨Y, f, hY, -, h1, h0⟩
    refine ⟨Y, hY, ?_, fun h => absurd h hTu⟩
    by_cases hex : ∃ j, f j = true
    · exact Or.inr (h1 hex)
    · refine Or.inl ((h0 fun j => ?_).trans hg)
      cases hj : f j with
      | false => rfl
      | true => exact absurd ⟨j, hj⟩ hex

/-- The clauses of the contract on a positive norm word. -/
private theorem stage_post_pos {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hNat : IsExactNatLit id M 1) {nmax N : ℕ} (hN : N ≤ nmax) {ρ x : ℝ} (hρ : 0 < ρ)
    (hu : 64 * ((nmax : ℝ) + 1) ^ 2 * u ≤ 1) {T U Y : Matrix (Fin N) (Fin N) ℂ} {gw : Option ℝ}
    (hx₂ : x ≤ (1 + (2 * (nmax : ℝ) ^ 2 + 2) * u) * frobNorm T) (hxp : 0 < x)
    (hΨ : StageColumns M u T (M.mul ρ x) Y gw) :
    (gw = some 0 ∨ gw = some 1) ∧ (T = 0 → matMulWord M U Y = U ∧ gw = some 0) ∧
      (T.IsUpperTriangular →
        (∃ Y' : Matrix (Fin N) (Fin N) ℂ,
          (∀ j, |‖WithLp.toLp 2 (Y'.col j)‖ - 1| ≤ 4 * ((nmax : ℝ) + 2) * u ∧
            ‖WithLp.toLp 2 ((T - T j j • 1) *ᵥ Y'.col j)‖ ≤
              (if gw = some 0 then 16 * (1 + √(nmax : ℝ)) * ((nmax : ℝ) + 1) * u
                else 16 * (1 + √(nmax : ℝ)) * ((nmax : ℝ) + 1) * u + 4 * ρ) * frobNorm T *
                ‖WithLp.toLp 2 (Y'.col j)‖) ∧
          specNorm (matMulWord M U Y - U * Y') ≤
            8 * ((nmax : ℝ) + 1) * u * frobNorm U * frobNorm Y') ∧
        ((∀ i j, i ≠ j → 4 * ρ * frobNorm T < ‖T i i - T j j‖) → gw = some 0)) := by
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hn0 : (0 : ℝ) ≤ nmax := Nat.cast_nonneg nmax
  have hNr : (N : ℝ) ≤ nmax := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsq : (1 : ℝ) ≤ ((nmax : ℝ) + 1) ^ 2 := by nlinarith
  have hu64 : u ≤ 1 / 64 := by nlinarith
  have hnu : ((nmax : ℝ) + 1) * u ≤ 1 / 64 := by nlinarith [mul_nonneg hn0 hu0]
  have hc₂ : (2 * (nmax : ℝ) ^ 2 + 2) * u ≤ 1 / 32 := by nlinarith [mul_nonneg hn0 hu0]
  have hF0 : 0 < frobNorm T := by
    by_contra h
    have hF : frobNorm T = 0 := le_antisymm (not_lt.mp h) (frobNorm_nonneg T)
    rw [hF, mul_zero] at hx₂
    linarith
  have hlit : M.lit 1 = 1 := by simpa using hNat 1 le_rfl
  have hρx : 0 < ρ * x := mul_pos hρ hxp
  have hm := hM.mul ρ x
  simp only [id, abs_of_pos hρx] at hm
  obtain ⟨hm₁, hm₂⟩ := abs_le.mp hm
  have hx₃ : x ≤ 33 / 32 * frobNorm T :=
    hx₂.trans (mul_le_mul_of_nonneg_right (by linarith) hF0.le)
  have hρx₂ : ρ * x ≤ ρ * (33 / 32 * frobNorm T) := mul_le_mul_of_nonneg_left hx₃ hρ.le
  have hsm : M.mul ρ x ≤ 8 / 7 * (ρ * frobNorm T) := by nlinarith [mul_pos hρ hF0]
  have hsm0 : 0 ≤ M.mul ρ x := by nlinarith
  refine ⟨hΨ.1.imp id (fun h => by rw [h, hlit]), fun h0 => ?_, fun hTu => ?_⟩
  · exact absurd (h0 ▸ hF0) (by simp)
  obtain ⟨happ, happ0, hgp⟩ := hΨ.2 hTu
  have hcard : (√(Fintype.card (Fin N) : ℝ)) ≤ √(nmax : ℝ) := by
    rw [Fintype.card_fin]; exact Real.sqrt_le_sqrt hNr
  have hsq0 : 0 ≤ √(Fintype.card (Fin N) : ℝ) := Real.sqrt_nonneg _
  have hε : 16 * ((N : ℝ) + 1) * u * (1 + √(Fintype.card (Fin N) : ℝ)) ≤
      16 * (1 + √(nmax : ℝ)) * ((nmax : ℝ) + 1) * u := by
    have h1 : ((N : ℝ) + 1) * u ≤ ((nmax : ℝ) + 1) * u :=
      mul_le_mul_of_nonneg_right (by linarith) hu0
    have h2 : ((N : ℝ) + 1) * u * (1 + √(Fintype.card (Fin N) : ℝ)) ≤
        ((nmax : ℝ) + 1) * u * (1 + √(nmax : ℝ)) :=
      mul_le_mul h1 (by linarith) (by positivity) (by positivity)
    nlinarith
  have hnε : 0 ≤ 16 * ((N : ℝ) + 1) * u := by positivity
  refine ⟨⟨Y, fun j => ⟨(happ j).1.trans (by nlinarith), ?_⟩, ?_⟩,
    fun hgap => hgp fun i j hij => ?_⟩
  · have hyn := norm_nonneg (WithLp.toLp 2 (Y.col j))
    by_cases hg0 : gw = some 0
    · rw [if_pos hg0]
      refine ((happ0 hg0).norm_mulVec_col_le hnε le_rfl j).trans
        (mul_le_mul_of_nonneg_right ?_ hyn)
      rw [add_zero]
      exact mul_le_mul_of_nonneg_right hε hF0.le
    · rw [if_neg hg0]
      refine (happ.norm_mulVec_col_le hnε (by positivity) j).trans
        (mul_le_mul_of_nonneg_right ?_ hyn)
      have h1 := mul_le_mul_of_nonneg_right hε hF0.le
      have h2 : 7 / 2 * M.mul ρ x ≤ 4 * ρ * frobNorm T := by nlinarith [mul_pos hρ hF0]
      nlinarith
  · have hb := hM.specNorm_matMulWord_sub_le (by nlinarith) U Y
    refine hb.trans ?_
    have hUY := mul_nonneg (frobNorm_nonneg U) (frobNorm_nonneg Y)
    have : 8 * ((N : ℝ) + 1) * u ≤ 8 * ((nmax : ℝ) + 1) * u := by nlinarith
    calc _ ≤ 8 * ((nmax : ℝ) + 1) * u * (frobNorm U * frobNorm Y) :=
          mul_le_mul_of_nonneg_right this hUY
      _ = _ := by ring
  · have h2 : 2 * M.mul ρ x ≤ 4 * ρ * frobNorm T := by nlinarith [mul_pos hρ hF0]
    exact lt_of_le_of_lt h2 (hgap i j hij)

/-- The clauses of the contract when the norm word is not positive: $\mathbf{T} = \mathbf{0}$,
$\mathbf{V} = \mathbf{U}$ and $\mathbf{Y} = \mathbf{I}$. -/
private theorem stage_post_zero {nmax N : ℕ} {ρ u c₁ x : ℝ} (hu0 : 0 ≤ u)
    (hc₁ : 0 < c₁) {T U : Matrix (Fin N) (Fin N) ℂ} {gw : Option ℝ}
    (hx₁ : c₁ * frobNorm T ≤ x) (hxp : ¬ 0 < x) (hg : gw = some 0) :
    (gw = some 0 ∨ gw = some 1) ∧ (T = 0 → U = U ∧ gw = some 0) ∧
      (T.IsUpperTriangular →
        (∃ Y : Matrix (Fin N) (Fin N) ℂ,
          (∀ j, |‖WithLp.toLp 2 (Y.col j)‖ - 1| ≤ 4 * ((nmax : ℝ) + 2) * u ∧
            ‖WithLp.toLp 2 ((T - T j j • 1) *ᵥ Y.col j)‖ ≤
              (if gw = some 0 then 16 * (1 + √(nmax : ℝ)) * ((nmax : ℝ) + 1) * u
                else 16 * (1 + √(nmax : ℝ)) * ((nmax : ℝ) + 1) * u + 4 * ρ) * frobNorm T *
                ‖WithLp.toLp 2 (Y.col j)‖) ∧
          specNorm (U - U * Y) ≤ 8 * ((nmax : ℝ) + 1) * u * frobNorm U * frobNorm Y) ∧
        ((∀ i j, i ≠ j → 4 * ρ * frobNorm T < ‖T i i - T j j‖) → gw = some 0)) := by
  have hF : frobNorm T = 0 := by
    have h0 := frobNorm_nonneg T
    have : c₁ * frobNorm T ≤ 0 := hx₁.trans (not_lt.mp hxp)
    nlinarith
  have hT : T = 0 := frobNorm_eq_zero_iff.mp hF
  subst hT
  refine ⟨Or.inl hg, fun _ => ⟨rfl, hg⟩, fun _ => ⟨⟨1, fun j => ⟨?_, ?_⟩, ?_⟩, fun _ => hg⟩⟩
  · have e : WithLp.toLp 2 ((1 : Matrix (Fin N) (Fin N) ℂ).col j) =
        EuclideanSpace.single j (1 : ℂ) := by
      ext i
      simp [Matrix.col, Matrix.one_apply, eq_comm]
    have h1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
    rw [e, h1, sub_self, abs_zero]
    positivity
  · simp [frobNorm_zero]
  · rw [mul_one, sub_self, specNorm_zero]
    have := frobNorm_nonneg U
    have h1 := frobNorm_nonneg (1 : Matrix (Fin N) (Fin N) ℂ)
    positivity

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
  intro N a uo pe v g τ μ U T hN hpair hrd hl hroom hap
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hn0 : (0 : ℝ) ≤ nmax := Nat.cast_nonneg nmax
  have hNr : (N : ℝ) ≤ nmax := by exact_mod_cast hN
  have hc : (2 * (nmax : ℝ) ^ 2 + 2) * u ≤ 1 / 32 := by nlinarith [mul_nonneg hn0 hu0]
  have huN : 64 * ((N : ℝ) + 1) * u ≤ 1 := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_nonneg hn0 hu0]
  have hρg : μ.store.get pe.1 pe.2 = some ρ := by
    simpa using Store.get_of_readBlock hrd (j := 0) (by simp) 0
  have hl00 : M.lit 0 = 0 := hM.zero
  have hnorm : FrobNormEstimateContract (1 - (2 * (nmax : ℝ) ^ 2 + 2) * u)
      (1 + (2 * (nmax : ℝ) ^ 2 + 2) * u) nmax (frobNormStage (O := O) (Q := Q)) I :=
    frobNormStage_frobNormEstimateContract hS hM (by linarith)
  refine (triEigvecStage_writes_of (ne := 1) (ρ := ρ)
    (Pn := fun x => (1 - (2 * (nmax : ℝ) ^ 2 + 2) * u) * frobNorm T ≤ x ∧
      x ≤ (1 + (2 * (nmax : ℝ) ^ 2 + 2) * u) * frobNorm T)
    (Ψ := fun x Y gw => StageColumns M u T (M.mul ρ x) Y gw) hS hL hC one_pos hpair hρg hl hroom hap
    (fun m s hT hlv hs hne => (hnorm T hN hT hlv hs hne).mono le_rfl
      fun _ _ ⟨x, hx, h₁, h₂⟩ => ⟨x, hx, h₁, h₂⟩)
    (fun x _ hxp L m hT hsm hg hlv hrm hap' => ?_)).mono le_rfl ?_
  · have hmx := hM.mul ρ x
    have hρx : 0 < ρ * x := mul_pos hρ hxp
    simp only [id, abs_of_pos hρx] at hmx
    have hu1 : u ≤ 1 / 64 := by nlinarith
    have hpos : 0 < M.mul ρ x := by nlinarith [(abs_le.mp hmx).1]
    exact triEigenvectors_stageColumns hS hM hL hC huN hpos hT hsm (hg.trans (congrArg some hl00))
      hlv hrm hap'
  · rintro μ' - ⟨V, hV, x, ⟨hx₁, hx₂⟩, hcase⟩
    refine ⟨V, hV, ?_⟩
    rcases hcase with ⟨hxp, Y, hΨ, rfl⟩ | ⟨hxp, rfl, hgw⟩
    · exact stage_post_pos hM hNat hN hρ hu hx₂ hxp hΨ
    · exact stage_post_zero hu0 (by linarith) hx₁ hxp (hgw.trans (congrArg some hl00))

/-- **The eigenvector stage completes** on any scalar machine with index literals and exact
comparisons: for every order at most $N_{\max}$ and every stored pair it succeeds on every tape,
writing only $\mathbf{V}$ and the flag, and stores a matrix and a word. -/
theorem triEigvecStage_completes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) (nmax : ℕ) (ρ : ℝ) :
    CompletingEigenvectorStage nmax [ρ] (triEigvecStage (O := O) (Q := Q)) I := by
  intro N a uo pe v g τ μ U T hN hpair hrd hl hroom hap
  have hρg : μ.store.get pe.1 pe.2 = some ρ := by
    simpa using Store.get_of_readBlock hrd (j := 0) (by simp) 0
  refine (triEigvecStage_writes_of (ne := 1) (ρ := ρ) (Pn := fun _ => True)
    (Ψ := fun _ _ gw => ∃ x, gw = some x) hS hL hC one_pos hpair hρg hl hroom hap
    (fun m s hT hlv hs hne => (frobNormStage_completing hS nmax T hN hT hlv hs hne).mono le_rfl
      fun _ _ ⟨x, hx⟩ => ⟨x, hx, trivial⟩)
    (fun x _ _ L m hT hsm hg hlv hrm hap' =>
      (triEigenvectors_writes hS hL hC hT hsm ⟨_, hg⟩ hlv hrm hap').mono le_rfl
        fun _ _ ⟨⟨Y, hY⟩, w, hw⟩ => ⟨Y, hY, w, hw⟩)).mono le_rfl ?_
  rintro μ' - ⟨V, hV, x, -, hcase⟩
  refine ⟨⟨V, hV⟩, ?_⟩
  rcases hcase with ⟨-, Y, ⟨w, hw⟩, -⟩ | ⟨-, -, hw⟩
  · exact ⟨w, hw⟩
  · exact ⟨_, hw⟩

/-- **The static count of the eigenvector stage**: its instrumented static count at the order
$n + 1$, $n_e$ words and zero offsets is at most $10^4(n + 1)^3$. -/
theorem size_stmtCost_triEigvecStage_le (n ne : ℕ) :
    Count.size (stmtCost (triEigvecStage (O := O) (Q := Q)).instrument
      [n + 1, ne, 0, 0, 0, 0, 0]) ≤ 10000 * (n + 1) ^ 3 := by
  have hw : stmtWorkMono (triEigvecStage (O := O) (Q := Q)).instrument
      (⟨1, [1, 0]⟩ :: ⟨1, [0, 1]⟩ :: List.replicate 5 (WorkMono.const 0)) = ⟨1579, [3, 0]⟩ := by
    rw [stmtWorkMono_instrument]; kernel_rfl
  have hσ : SlotsLe [n + 1, ne + 1] [n + 1, ne, 0, 0, 0, 0, 0]
      (⟨1, [1, 0]⟩ :: ⟨1, [0, 1]⟩ :: List.replicate 5 (WorkMono.const 0)) := by
    simp [SlotsLe, WorkMono.eval, WorkMono.const]
  have h := size_stmtCost_le_stmtWorkMono (bs := [n + 1, ne + 1]) (by simp)
    (triEigvecStage (O := O) (Q := Q)).instrument hσ
  rw [hw] at h
  have h' : Count.size (stmtCost (triEigvecStage (O := O) (Q := Q)).instrument
      [n + 1, ne, 0, 0, 0, 0, 0]) ≤ 1579 * (n + 1) ^ 3 := by
    simpa [WorkMono.eval, mul_assoc] using h
  exact h'.trans (Nat.mul_le_mul_right _ (by omega))

end Stage

end NLAlib.Schur
