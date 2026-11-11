/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Initialization
public import NLAlib.Krylov.Lanczos.Reorth.Rounds
public import NLAlib.Krylov.Lanczos.Reorth.Alg

/-!
# Total exact fully reorthogonalized Lanczos

The program initializes all basis/coefficient storage, then stops safely at exact breakdown or
at the requested cap. Its output is the total pure Lanczos recurrence, with zero tails after
breakdown. Exact operation assumptions and a Hermitian matrix imply successful execution for
every input
and cap.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.solve_spec` certifies successful packed recurrence output.
* `NLAlib.Krylov.Lanczos.Reorth.runs_solve` adds the program's operation and workspace bounds.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- Input, basis and coefficient storage use different buffers. -/
@[admNF] def SolveOperands (n : ℕ) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d.headD 0 = n ∧ ∃ b v c,
    ins = [b] ∧ outs = [v, c] ∧ b.1 ≠ v.1 ∧ b.1 ≠ c.1 ∧ v.1 ≠ c.1

/-- Packed basis columns and tridiagonal coefficients agree with the pure recurrence. -/
@[simps (attr := storeNF)]
noncomputable def solveRel (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    BlockRel K where
  nd := 2
  inLens d := [d.headD 0]
  outLens d := [(d.getD 1 0 + 1) * d.headD 0, 3 * d.getD 1 0 + 2]
  rel d X _ Y := match X, Y with
    | [bs], [vs, cs] => Output dec A (decv dec n bs) (d.getD 1 0) vs cs
    | _, _ => False

/-- Ordinary readable inputs and operation models suffice for successful execution at any
cap. Zero dimension, zero input and exact early breakdown require no extra premise. -/
theorem solve_writes {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hAT : A.IsHermitian)
    {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 3 * cap + 2]) :
    Writes .total I τ solve (Env.frame [n, cap] [B, V, C])
      (Fp.blocks [V, C] [(cap + 1) * n, 3 * cap + 2])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (3 * cap + 2) = some cs ∧
        Output dec A (decv dec n bs) cap vs cs) μ := by
  obtain ⟨hBL, hVL, hCL⟩ : B.1 < μ.store.length ∧ V.1 < μ.store.length ∧
      C.1 < μ.store.length := by simpa using hl
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
  exact ⟨hpos₂.trans hpos₁, vs, cs, by kept, by kept, hout⟩

/-- The full concrete algorithm satisfies its mathematical output contract in total mode. -/
theorem solve_spec {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hAT : A.IsHermitian) :
    (solveImpl (Op := Op) (Tst := Tst)).Triple I .total
      ((solveRel dec A).spec (SolveOperands n)) := by
  cert_intro [m, cap] (b) → (v, c) reads (bs)
  obtain ⟨hd, hBV, hBC, hVC⟩ := hadm
  subst m
  refine (solve_writes (μ := μ) hS hM hB hok hA hCmp hAT hBV hBC hVC
    (by simpa using hl) hbs (by simpa using hz)).mono le_rfl ?_
  rintro μ' _ ⟨hpos, vs, cs, hv, hc, hout⟩
  exact ⟨by simpa using hpos, [vs, cs],
    Mem.readBlocks_of_cons hv (Mem.readBlocks_of_cons hc rfl), hout⟩

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
  have hw := solve_writes hS hM hB hok hA hCmp hAT (τ := τ) hBV hBC hVC hl hb hz
  obtain ⟨μ', hrun, hout⟩ := hw.wp fun _ _ h => h
  exact (ConditionalRuns.of_run hrun hout W).mono (le_of_eq (staticCost_solve ..))
    (staticPeak_solve_le ..) (fun _ h => h)

end NLAlib.Krylov.Lanczos.Reorth
