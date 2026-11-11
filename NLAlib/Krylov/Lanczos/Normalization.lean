/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Alg
public import NLAlib.Krylov.Lanczos.Spec
public import NLAlib.Ops.Blas.Decoded
public import NLAlib.Ops.Logic.Tactic

/-!
# Successful Lanczos normalization, including zero input

A computed exact self-dot controls the branch. Positive input permits a square root and
reciprocal scaling; zero input preserves the initialized zero outputs. Thus the total
certificate never uses a square root or division at zero norm.

## Main results

* `NLAlib.Krylov.Lanczos.normalize_spec` proves total guarded normalization.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- The vector, squared norm, output vector and output norm occupy four different buffers;
the two outputs alias their initially zero input blocks. -/
@[admNF] def NormalizeOperands (n : ℕ) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d = [n] ∧ ∃ w s q b, ins = [w, s, q, b] ∧ outs = [q, b] ∧
    w.1 ≠ s.1 ∧ w.1 ≠ q.1 ∧ w.1 ≠ b.1 ∧ s.1 ≠ q.1 ∧ s.1 ≠ b.1 ∧ q.1 ≠ b.1

/-- Exact self-dot input and initially zero outputs give the normalized vector and its norm,
including the total zero-input case. -/
@[simps (attr := storeNF)]
noncomputable def normalizeRel (dec : K → ℝ) (n : ℕ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0, 1, d.headD 0, 1]
  outLens d := [d.headD 0, 1]
  dom _ X _ := match X with
    | [ws, [s], qs, [b]] => dec s = decv dec n ws ⬝ᵥ decv dec n ws ∧
        decv dec n qs = 0 ∧ dec b = 0
    | _ => False
  rel _ X _ Y := match X, Y with
    | [ws, [_], _, [_]], [qs, [b]] =>
        decv dec n qs = ‖WithLp.toLp 2 (decv dec n ws)‖⁻¹ • decv dec n ws ∧
          dec b = ‖WithLp.toLp 2 (decv dec n ws)‖
    | _, _ => False

/-- Input self-dot and zero-output facts, together with the operation models, suffice for
successful normalization in both branches. No nonzero-input premise is needed. -/
theorem normalize_spec {M : Machine K} {dec : K → ℝ} {n : ℕ} {I : Interp Op Tst K}
    {ok : ℕ → Prop} (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec ok I) (hok : ok n) (hCmp : IsCmp dec I) :
    (normalizeImpl (Op := Op) (Tst := Tst)).Meets I .total
      ((normalizeRel dec n).spec (NormalizeOperands n)) := by
  classical
  cert_intro [m] (w, s, q, b) → (q', b') reads (ws, ss, qs, bs)
  obtain ⟨hd, hq, hb, hws, hwq, hwb, hsq, hsb, hqb⟩ := hadm
  subst m q' b'
  obtain ⟨σ, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hss)
  obtain ⟨β₀, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hbs)
  change dec σ = decv dec n ws ⬝ᵥ decv dec n ws ∧ decv dec n qs = 0 ∧ dec β₀ = 0 at hdom
  have hσ : μ.store.get s.1 s.2 = some σ := by
    simpa using Store.get_of_readBlock hss (j := 0) (by omega) σ
  have hnorm : dec σ = ‖WithLp.toLp 2 (decv dec n ws)‖ ^ 2 :=
    hdom.1.trans (EuclideanSpace.norm_toLp_sq_eq_dotProduct_self _).symm
  refine writes_ite rfl rfl (hCmp.test_isPos hσ) ?_
  by_cases hp : 0 < dec σ
  · simp only [hp, decide_true, ite_true]
    step (hS .sqrt) as μ₁ hfr₁ ⟨hpos₁, β, hβ, hβword⟩
    step hB.copy as μ₂ hfr₂ ⟨hpos₂, copied, hcopied, hcopy⟩
    subst copied
    step hB.scal as μ₃ hfr₃ ⟨hpos₃, ys, hys, hscaled⟩
    have hβdec : dec β = ‖WithLp.toLp 2 (decv dec n ws)‖ := by
      rw [← hβword, hM.sqrt σ hp.le, hnorm, Real.sqrt_sq (norm_nonneg _)]
    have hβne : dec β ≠ 0 := by
      rw [hβdec]
      intro hz
      rw [hz] at hnorm
      exact hp.ne' (by simpa using hnorm)
    refine ⟨by simp [normalizeRel, hpos₃, hpos₂, hpos₁], [ys, [β]],
      Mem.readBlocks_of_cons hys (Mem.readBlocks_of_cons (by kept) rfl), ?_, hβdec⟩
    funext i
    simpa [decv, hβdec, div_eq_mul_inv, mul_comm] using hscaled hβne i i.isLt
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
    have hn : ‖WithLp.toLp 2 (decv dec n ws)‖ = 0 := by
      have hσle : dec σ ≤ 0 := le_of_not_gt hp
      nlinarith [norm_nonneg (WithLp.toLp 2 (decv dec n ws))]
    have hwzero : decv dec n ws = 0 := by
      simpa only [norm_eq_zero, WithLp.toLp_eq_zero] using hn
    refine (Writes.skip ?_).mono bot_le (fun _ _ h => h)
    exact ⟨by simp [normalizeRel], [qs, [β₀]],
      Mem.readBlocks_of_cons hqs (Mem.readBlocks_of_cons hbs rfl),
      by simpa [hwzero, hn] using hdom.2.1, by simpa only [hn] using hdom.2.2⟩

end NLAlib.Krylov.Lanczos
