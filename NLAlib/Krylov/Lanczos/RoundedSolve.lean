/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedInitialization
public import NLAlib.Krylov.Lanczos.RoundedRounds
public import NLAlib.Krylov.Lanczos.RoundedOutput
public import NLAlib.Krylov.Lanczos.Exact

/-!
# Complete standard-model Lanczos with rounded matvec

Primitive models and input precision suffice for actual initialization, every active round,
safe early breakdown and packed output readback. The same extracted existing LanczosRun
accounts for every stored basis/coefficient value. Zero cap and zero input remain explicit.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.solve_spec`: complete total block certificate.
* `NLAlib.Krylov.Lanczos.Rounded.runs_solve`: actual output and conditional static accounting.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- The complete rounded program succeeds from readable inputs and ordinary output capacity.
There is no assumed successful execution, no future nonbreakdown and no assumed initial unit
vector. Every matrix-vector call carries its stated rounding error. -/
theorem solve_writes {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {em u E : ℝ} {e : Blas1Err} {A : Matrix (Fin n) (Fin n) ℝ}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec e ok I) (hok : ok n)
    (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hAT : Aᵀ = A) (hprec : Precision em u E e n)
    {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 2 * cap + 2]) :
    Writes .total I τ solve (Env.frame [n, cap] [B, V, C])
      (Fp.blocks [V, C] [(cap + 1) * n, 2 * cap + 2])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (2 * cap + 2) = some cs ∧
        Output dec A (decv dec n bs) E cap vs cs) μ := by
  obtain ⟨hBL, hVL, hCL⟩ : B.1 < μ.store.length ∧ V.1 < μ.store.length ∧
      C.1 < μ.store.length := by simpa using hl
  obtain ⟨hv, hc⟩ : V.2 + (cap + 1) * n ≤ μ.store.len V.1 ∧
      C.2 + (2 * cap + 2) ≤ μ.store.len C.1 := by simpa using hz
  refine writes_allocs (lens := [.var 0, .var 0, .const 2]) (ns := [n, n, 2]) rfl
    fun s₁ hs₁ hlens hBelow => ?_
  have hp : s₁.len μ.store.length = n := by simpa using hlens 0 (by simp)
  have hw : s₁.len (μ.store.length + 1) = n := by simpa using hlens 1 (by simp)
  have ht : s₁.len (μ.store.length + 2) = 2 := by simpa using hlens 2 (by simp)
  dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
    List.length_cons, List.length_nil, Nat.add_zero] at *
  have hv₁ : V.2 + (cap + 1) * n ≤ s₁.len V.1 := by
    rw [hBelow.len_of V.1 hVL]; exact hv
  have hc₁ : C.2 + (2 * cap + 2) ≤ s₁.len C.1 := by
    rw [hBelow.len_of C.1 hCL]; exact hc
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true]; omega)
    (initialize_writes (A := A) hS hM hB hok hCmp hprec hBV hBC hVC
      hBL hVL hCL hs₁ hp ht le_rfl (by kept) hv₁ hc₁)) le_rfl ?_
  rintro μ₁ hfr₁ ⟨hpos₁, z, hstate⟩
  refine (rounds_writes hS hM hB hok hA hCmp hAT hprec hVL hCL hVC
    (by simpa only [hfr₁.length_eq] using hs₁)
    (by simpa only [hfr₁.len_eq] using hp) (by simpa only [hfr₁.len_eq] using hw)
    (by simpa only [hfr₁.len_eq] using ht) (by simpa only [hfr₁.len_eq] using hv₁)
    (by simpa only [hfr₁.len_eq, Nat.add_assoc] using hc₁) hstate).mono le_rfl ?_
  rintro μ₂ _ ⟨hpos₂, done, hdone, z', hprefix, hstop⟩ s₂ hs₂ hBelow₂
  obtain ⟨vs, cs, hvs, hcs, hpacked⟩ := hprefix.readback
  exact ⟨hpos₂.trans hpos₁, vs, cs, by kept, by kept,
    done, hdone, z', hprefix.toOutcome, hpacked, hstop⟩

/-- Rounded output relation on the actual packed basis and coefficients. -/
@[simps (attr := storeNF)]
noncomputable def solveRel (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (E : ℝ) : BlockRel K where
  nd := 2
  inLens d := [d.headD 0]
  outLens d := [(d.getD 1 0 + 1) * d.headD 0, 2 * d.getD 1 0 + 2]
  rel d X _ Y := match X, Y with
    | [bs], [vs, cs] => Output dec A (decv dec n bs) E (d.getD 1 0) vs cs
    | _, _ => False

/-- Total correctness for the same fixed Lanczos implementation at every admitted cap. -/
theorem solve_spec {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {em u E : ℝ} {e : Blas1Err} {A : Matrix (Fin n) (Fin n) ℝ}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec e ok I) (hok : ok n)
    (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hAT : Aᵀ = A) (hprec : Precision em u E e n) :
    (solveImpl (Op := Op) (Tst := Tst)).Triple I .total
      ((solveRel dec A E).spec (SolveOperands n)) := by
  cert_intro [m, cap] (b) → (v, c) reads (bs)
  obtain ⟨hd, hBV, hBC, hVC⟩ := hadm
  subst m
  refine (solve_writes hS hM hB hok hA hCmp hAT hprec hBV hBC hVC
    (by simpa only [Mem.live_cons, Mem.live_nil, and_true] using hl) hbs
    (by simpa only [Mem.room_cons, Mem.room_nil, and_true] using hz)).mono le_rfl ?_
  rintro μ' _ ⟨hpos, vs, cs, hv, hc, hout⟩
  exact ⟨by simpa using hpos, [vs, cs],
    Mem.readBlocks_of_cons hv (Mem.readBlocks_of_cons hc rfl), hout⟩

/-- Actual complete rounded execution, its packed numerical outcome and existing static
primitive/workspace bounds. This conditional proof does not assert a canonical full budget. -/
theorem runs_solve {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {em u E : ℝ} {e : Blas1Err} {A : Matrix (Fin n) (Fin n) ℝ}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec e ok I) (hok : ok n)
    (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hAT : Aᵀ = A) (hprec : Precision em u E e n)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 2 * cap + 2]) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [B, V, C]) μ
      (solveCount n cap) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (2 * cap + 2) = some cs ∧
        Output dec A (decv dec n bs) E cap vs cs) := by
  have hw := solve_writes hS hM hB hok hA hCmp hAT hprec (τ := τ) hBV hBC hVC hl hb hz
  obtain ⟨μ', hrun, hout⟩ := hw.wp fun _ _ h => h
  exact (ConditionalRuns.of_run hrun hout W).mono (le_of_eq (stmtCost_solve ..))
    (stmtPeak_solve_le ..) (fun _ h => h)

end NLAlib.Krylov.Lanczos.Rounded
