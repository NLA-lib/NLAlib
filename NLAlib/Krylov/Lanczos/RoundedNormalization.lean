/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Alg
public import NLAlib.Krylov.Lanczos.Normalization
public import NLAlib.Krylov.Lanczos.Math.NormGuard
public import NLAlib.Ops.Blas.Decoded
public import NLAlib.Ops.Logic.Tactic

/-!
# Rounded Lanczos normalization with domain guards

A rounded self-dot with relative error below one controls the branch. Positive input permits
a square root and
reciprocal scaling; zero input preserves the initialized zero outputs. Thus the total
certificate never uses a square root or division at zero norm.

## Main results

* `NLAlib.Krylov.Lanczos.normalize_rounded_spec` proves total guarded normalization.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- Rounded self-dot input and zero initial outputs give a rounded norm and reciprocal scaling. -/
@[simps (attr := storeNF)]
def normalizeRoundedRel (dec : K → ℝ) (ed es ec : ℝ) (n : ℕ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0, 1, d.headD 0, 1]
  outLens d := [d.headD 0, 1]
  dom _ X _ := match X with
    | [ws, [s], qs, [b]] => IsDotErr dec ed n (vec ws) (vec ws) s ∧
        decv dec n qs = 0 ∧ dec b = 0
    | _ => False
  rel _ X _ Y := match X, Y with
    | [ws, [_], _, [_]], [qs, [b]] =>
        IsNrm2Err dec ed es n (vec ws) b ∧ IsScalErr dec ec n b (vec ws) (vec qs) ∧
          (decv dec n ws = 0 → decv dec n qs = 0)
    | _, _ => False

/-- Input self-dot and zero-output facts, together with the operation models, suffice for
successful rounded normalization in both branches. No nonzero-input premise is needed. -/
theorem normalize_rounded_spec {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {u : ℝ} {ε : Blas1Err} {I : Interp Op Tst K}
    {ok : ℕ → Prop} (hS : IsScalar M I) (hM : StdModel u dec M) (hu : u < 1) (hd : ε.dot n < 1)
    (hB : IsBlas1 dec ε ok I) (hok : ok n) (hCmp : IsCmp dec I) :
    (normalizeImpl (Op := Op) (Tst := Tst)).Meets I .total
      ((normalizeRoundedRel dec (ε.dot n) u ε.scal n).spec (NormalizeOperands n)) := by
  classical
  cert_intro [m] (w, s, q, b) → (q', b') reads (ws, ss, qs, bs)
  obtain ⟨hd, hq, hb, hws, hwq, hwb, hsq, hsb, hqb⟩ := hadm
  subst m q' b'
  obtain ⟨σ, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hss)
  obtain ⟨β₀, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hbs)
  change IsDotErr dec (ε.dot n) n (vec ws) (vec ws) σ ∧ decv dec n qs = 0 ∧ dec β₀ = 0 at hdom
  have hσ : μ.store.get s.1 s.2 = some σ := by
    simpa using Store.get_of_readBlock hss (j := 0) (by omega) σ
  refine writes_ite rfl rfl (hCmp.test_isPos hσ) ?_
  by_cases hp : 0 < dec σ
  · simp only [hp, decide_true, ite_true]
    step (hS .sqrt) as μ₁ hfr₁ ⟨hpos₁, β, hβ, hβword⟩
    step hB.copy as μ₂ hfr₂ ⟨hpos₂, copied, hcopied, hcopy⟩
    subst copied
    have hβpos : 0 < dec β := by rw [← hβword]; exact hM.sqrt_pos hu hp
    have hnorm : IsNrm2Err dec (ε.dot n) u n (vec ws) β :=
      ⟨σ, hdom.1, fun hσ => by rw [← hβword]; exact hM.sqrt σ hσ⟩
    step hB.scal as μ₃ hfr₃ ⟨hpos₃, ys, hys, hscaled⟩
    refine ⟨by simp [normalizeRoundedRel, hpos₃, hpos₂, hpos₁], [ys, [β]],
      Mem.readBlocks_of_cons hys (Mem.readBlocks_of_cons (by kept) rfl),
      hnorm, hscaled, ?_⟩
    intro hzero
    have hbzero := hnorm.eq_zero_of_decoded_eq_zero hzero
    exact False.elim (hβpos.ne' hbzero)
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
    have hwzero : decv dec n ws = 0 := by
      by_contra hne
      exact hp (hdom.1.self_pos_of_ne_zero hd hne)
    have hσzero : dec σ = 0 := by simpa [hwzero] using hdom.1.decoded
    refine (Writes.skip ?_).mono bot_le (fun _ _ h => h)
    refine ⟨by simp [normalizeRoundedRel], [qs, [β₀]],
      Mem.readBlocks_of_cons hqs (Mem.readBlocks_of_cons hbs rfl), ?_, ?_, ?_⟩
    · exact ⟨σ, hdom.1, fun _ => by simp [hσzero, hdom.2.2]⟩
    · intro hne
      exact False.elim (hne hdom.2.2)
    · exact fun _ => hdom.2.1

end NLAlib.Krylov.Lanczos
