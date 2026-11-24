/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Initialization
public import NLAlib.Krylov.Lanczos.Reorth.Rounds
public import NLAlib.Krylov.Lanczos.Reorth.Alg
public import NLAlib.Ops.RoutineSyntax

/-!
# Total exact fully reorthogonalized Lanczos

The program initializes all basis/coefficient storage, then stops safely at exact breakdown or
at the requested cap. Its output is the total pure Lanczos recurrence, with zero tails after
breakdown. Exact operation assumptions and a Hermitian matrix imply successful execution for
every input
and cap.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.solveRoutine`, `NLAlib.Krylov.Lanczos.Reorth.solveSpec`: the
  solver and what it computes.
* `NLAlib.Krylov.Lanczos.Reorth.solveRoutine_meets` certifies successful packed recurrence output.
* `NLAlib.Krylov.Lanczos.Reorth.runs_solve` adds the program's operation and workspace bounds.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- The solver as a routine: the starting vector `B` is read, the packed basis `V` and the
coefficients `C`, with the saved raw norms, are written. -/
def solveRoutine : Routine Op Tst :=
  routine% [n, cap] (B : n) → (V : (cap + 1) * n, C : 3 * cap + 2) := solve

/-- Packed basis columns and tridiagonal coefficients agree with the pure recurrence. -/
noncomputable def solveSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Routine.Spec K :=
  spec% [m, cap] (bs) → (vs, cs) requires m = n ensures Output dec A (decv dec n bs) cap vs cs

/-- Ordinary readable inputs and operation models suffice for successful execution at any
cap. Zero dimension, zero input and exact early breakdown require no extra premise. -/
theorem solveRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hAT : A.IsHermitian) :
    (solveRoutine (Op := Op) (Tst := Tst)).Meets I (solveSpec dec A) := by
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
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true]; omega)
    (Lanczos.initialize_writes (A := A) hS hM hB hok hCmp hBV hBC hVC hBL hVL hCL
      hs₁ hp ht (by omega)
      (by kept) (by simpa only [(hBelow V.1 hVL).1] using hv)
      (by simpa only [(hBelow C.1 hCL).1] using hc))) le_rfl ?_
  rintro μ₁ hfr₁ ⟨hpos₁, hstate₁, hsuffix⟩
  have hstateR : State dec A (decv dec n bs) cap 0 V C μ.store.length μ₁.store := by
    refine ⟨hstate₁, fun j hj => ?_⟩
    simpa only [nuValue, Nat.not_lt_zero, ↓reduceIte, Nat.add_assoc] using
      hsuffix (2 * cap + 2 + j) (by omega) (by omega)
  refine (rounds_writes hS hM hB hok hA hCmp hAT hVL hCL hVC
    (by simpa only [hfr₁.length_eq] using hs₁)
    (by simpa only [hfr₁.len_eq] using hp) (by simpa only [hfr₁.len_eq] using hw)
    (by simpa only [hfr₁.len_eq] using ht)
    (by simpa only [hfr₁.len_eq, (hBelow V.1 hVL).1] using hv)
    (by simpa only [hfr₁.len_eq, (hBelow C.1 hCL).1, Nat.add_assoc] using hc) hstateR).mono
      le_rfl ?_
  rintro μ₂ _ ⟨hpos₂, hprefix, hν⟩ s₂ hs₂ hBelow₂
  obtain ⟨vs, cs, hv₂, hc₂, hout⟩ := readback hprefix hAT hν
  exact ⟨by simp [hpos₂, hpos₁], [vs, cs],
    Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl), hout⟩

/-- Successful capped Lanczos returns the pure recurrence within the evaluated static budget.
For Hermitian matrices, `Output.toOrdinary` identifies its canonical Krylov basis. -/
theorem runs_solve {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hAT : A.IsHermitian)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 3 * cap + 2]) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [B, V, C]) μ
      (solveCount n cap) (solvePeak W n cap)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (3 * cap + 2) = some cs ∧
        Output dec A (decv dec n bs) cap vs cs) := by
  obtain ⟨μ', hrun, hpos, Y, hout, hrel⟩ :=
    (solveRoutine_meets hS hM hB hok hA hCmp hAT [n, cap] [B, V, C] τ μ _ rfl rfl hl
      (by routine_sep) (Mem.readBlocks_of_cons hb rfl) rfl hz).wp
      (Q := fun m' => m'.pos = μ.pos ∧ ∃ Y,
        m'.readBlocks [V, C] [(cap + 1) * n, 3 * cap + 2] = some Y ∧
          (solveSpec dec A).post [n, cap] (τ.shift μ.pos) [bs] Y) fun _ _ h => h
  split_reads hout as (vs, cs)
  exact (ConditionalRuns.of_run hrun ⟨hpos, vs, cs, hvs, hcs, hrel⟩ W).mono
    (le_of_eq (stmtCost_solve ..))
    (stmtPeak_solve_le ..) (fun _ h => h)

end NLAlib.Krylov.Lanczos.Reorth
