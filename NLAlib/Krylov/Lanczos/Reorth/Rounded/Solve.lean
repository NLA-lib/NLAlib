/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.Rounded.Initialization
public import NLAlib.Krylov.Lanczos.Reorth.Rounded.Rounds
public import NLAlib.Krylov.Lanczos.Reorth.Rounded.Output
public import NLAlib.Krylov.Lanczos.Reorth.Exact
public import NLAlib.Ops.RoutineSyntax

/-!
# Complete rounded full reorthogonalized Lanczos with rounded matvec

Primitive models and input precision suffice for actual initialization, every active round,
safe early breakdown and packed output readback. The same actual transition history
accounts for every stored basis/coefficient value and saved raw norm. No unproved
orthogonality or tau-admissibility claim is attached to this unconditional output.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.solveSpec`: the rounded specification of the solver
  `NLAlib.Krylov.Lanczos.Reorth.solveRoutine`.
* `NLAlib.Krylov.Lanczos.Reorth.Rounded.solveRoutine_meets`: complete total execution, with its
  footprint and packed output.
* `NLAlib.Krylov.Lanczos.Reorth.Rounded.runs_solve`: actual output with conditional
  static accounting.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- At the order `n` of the matrix, the written blocks are the packed basis and coefficients of
the rounded recurrence for the starting vector read. -/
noncomputable def solveSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (em u E : ℝ) (e : Blas1Err) : Routine.Spec K :=
  spec% [m, cap] (bs) → (vs, cs) requires m = n
    ensures Output dec A (decv dec n bs) em u E e cap vs cs

/-- The complete rounded program succeeds from readable inputs and ordinary output capacity,
for every interpretation satisfying the primitive models and every input, at every cap. -/
theorem solveRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {em u E : ℝ} {e : Blas1Err} {A : Matrix (Fin n) (Fin n) ℝ}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec e ok I) (hok : ok n)
    (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hprec : Lanczos.Rounded.Precision em u E e n) :
    (solveRoutine (Op := Op) (Tst := Tst)).Meets I (solveSpec dec A em u E e) := by
  routine_intro [n', cap] (B, V, C) reads (bs)
  obtain rfl : n = n' := Eq.symm hpre
  rename' m => μ, hbs => hb
  have hl' : μ.Live [B, V, C] := by simpa using hl
  have hz : μ.Room [V, C] [(cap + 1) * n, 3 * cap + 2] := by simpa using hroom
  obtain ⟨hBL, hVL, hCL⟩ : B.1 < μ.store.length ∧ V.1 < μ.store.length ∧
      C.1 < μ.store.length := by simpa using hl'
  obtain ⟨hv, hc⟩ : V.2 + (cap + 1) * n ≤ μ.store.len V.1 ∧
      C.2 + (3 * cap + 2) ≤ μ.store.len C.1 := by simpa using hz
  refine writes_allocs (lens := [.var 0, .var 0, .const 2]) (ns := [n, n, 2]) rfl
    fun s₁ hs₁ hlens hBelow => ?_
  have hp : s₁.len μ.store.length = n := by simpa using hlens 0 (by simp)
  have hw : s₁.len (μ.store.length + 1) = n := by simpa using hlens 1 (by simp)
  have ht : s₁.len (μ.store.length + 2) = 2 := by simpa using hlens 2 (by simp)
  dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
    List.length_cons, List.length_nil, Nat.add_zero] at *
  have hv₁ : V.2 + (cap + 1) * n ≤ s₁.len V.1 := by
    rw [hBelow.len_of V.1 hVL]; exact hv
  have hc₁ : C.2 + (3 * cap + 2) ≤ s₁.len C.1 := by
    rw [hBelow.len_of C.1 hCL]; exact hc
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true]; omega)
    (initialize_writes (A := A) hS hM hB hok hCmp hprec hBV hBC hVC
      hBL hVL hCL hs₁ hp ht (by kept) hv₁ hc₁)) le_rfl ?_
  rintro μ₁ hfr₁ ⟨hpos₁, z, nus, hstate⟩
  refine (rounds_writes hS hM hB hok hA hCmp hprec hVL hCL hVC
    (by simpa only [hfr₁.length_eq] using hs₁)
    (by simpa only [hfr₁.len_eq] using hp) (by simpa only [hfr₁.len_eq] using hw)
    (by simpa only [hfr₁.len_eq] using ht) (by simpa only [hfr₁.len_eq] using hv₁)
    (by simpa only [hfr₁.len_eq, Nat.add_assoc] using hc₁) hstate).mono le_rfl ?_
  rintro μ₂ _ ⟨hpos₂, done, hdone, z', nus', hprefix, hstop⟩ s₂ hs₂ hBelow₂
  obtain ⟨vs, cs, hvs, hcs, hpacked⟩ := hprefix.readback
  exact ⟨by simp [hpos₂, hpos₁], [vs, cs],
    Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl),
    done, hdone, z', nus', hprefix.history, hpacked, hstop⟩

/-- Actual complete rounded execution, its packed numerical outcome and existing static
primitive/workspace bounds. This conditional proof does not assert a canonical full budget. -/
theorem runs_solve {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {em u E : ℝ} {e : Blas1Err} {A : Matrix (Fin n) (Fin n) ℝ}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec e ok I) (hok : ok n)
    (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hprec : Lanczos.Rounded.Precision em u E e n)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 3 * cap + 2]) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [B, V, C]) μ
      (solveCount n cap) (solvePeak W n cap)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (3 * cap + 2) = some cs ∧
        Output dec A (decv dec n bs) em u E e cap vs cs) := by
  obtain ⟨μ', hrun, hpos, Y, hout, hrel⟩ :=
    (solveRoutine_meets hS hM hB hok hA hCmp hprec [n, cap] [B, V, C] τ μ _ rfl rfl hl
      (by routine_sep) (Mem.readBlocks_of_cons hb rfl) rfl hz).wp
      (Q := fun m' => m'.pos = μ.pos ∧ ∃ Y,
        m'.readBlocks [V, C] [(cap + 1) * n, 3 * cap + 2] = some Y ∧
          (solveSpec dec A em u E e).post [n, cap] (τ.shift μ.pos) [bs] Y) fun _ _ h => h
  split_reads hout as (vs, cs)
  exact (ConditionalRuns.of_run hrun ⟨hpos, vs, cs, hvs, hcs, hrel⟩ W).mono
    (le_of_eq (stmtCost_solve ..))
    (stmtPeak_solve_le ..) (fun _ h => h)

end NLAlib.Krylov.Lanczos.Reorth.Rounded
