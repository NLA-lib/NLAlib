/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.TwoPass

/-!
# Composing two-pass reorthogonalization

The two-pass certificate supplies a footprint rule with actual vector and coefficient reads.
No division, square root, rank assumption or execution-success premise is needed.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.cgs2_writes`: a total compositional two-pass interface.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has Blas1Op Op]

/-- A two-pass routine writes only its residual and exposes the resulting vector read. -/
theorem cgs2_writes {M : Machine K} {dec : K → ℝ} {ed : ℕ → ℝ} {ea : ℝ}
    {ok : ℕ → Prop} {I : Interp Op Tst K} (hS : IsScalar M I)
    (hD : I.Meets .total (Has.inj Blas1Op.dot) ((dotRel dec ed).spec (OutApart ok)))
    (hA : I.Meets .total (Has.inj Blas1Op.axpy) ((axpyRel dec ea).spec (InPlace ok)))
    (hneg : ∀ a, dec (M.neg a) = -dec a)
    {n k : ℕ} {τ : Tape K} {μ : Mem K} {Q w : ℕ × ℕ} {qs ws : List K}
    (hok : ok n) (hQw : Q.1 ≠ w.1) (hl : μ.Live [Q, w])
    (hqs : μ.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hws : μ.store.readBlock w.1 w.2 n = some ws) (hz : μ.Room [w] [n]) :
    Writes .total I τ cgs2 (Env.frame [n, k] [Q, w, w])
      (Fp.blocks [w] [n])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ws', μ'.store.readBlock w.1 w.2 n = some ws' ∧
        TwoPassOut dec (ed n) ea n k qs ws ws') μ := by
  have hl' : μ.Live ([Q, w] ++ [w]) := by
    simp only [Mem.live_cons, Mem.live_nil, List.cons_append, List.nil_append, and_true] at hl ⊢
    exact ⟨hl.1, hl.2, hl.2⟩
  have hread : μ.readBlocks [Q, w] [k * n, n] = some [qs, ws] :=
    Mem.readBlocks_of_cons hqs (Mem.readBlocks_of_cons hws rfl)
  have hpre : (((twoPassRel dec ed ea).spec (TwoPassOperands ok)).on .total
      [n, k] [Q, w] [w] τ μ).pre μ :=
    ⟨rfl, ⟨hok, Q, w, rfl, rfl, hQw⟩,
      fun _ => ⟨hl', ⟨[qs, ws], hread, trivial⟩, hz⟩⟩
  refine ((cgs2_spec hS hD hA hneg).writes hpre hl').mono le_rfl ?_
  rintro μ' _ ⟨X, hX, _, Y, hlen, hrel, rfl⟩
  obtain rfl : X = [qs, ws] := Option.some.inj (hX.symm.trans hread)
  obtain ⟨ws', rfl⟩ := List.length_eq_one_iff.mp
    (show Y.length = 1 by simpa using congrArg List.length hlen)
  have hout := Mem.readBlocks_updBlocks (m := μ) (zs := [w]) (ys := [ws'])
    (by rw [hlen]; simp [Fp.Apart]) (by rw [hlen]; exact hz)
  rw [hlen] at hout
  obtain ⟨w₁, vs, hops, hv, hwords⟩ := Mem.readBlocks_one hout
  have heq : w₁ = w := (List.cons.inj hops).1.symm
  subst w₁
  have heq' : vs = ws' := (List.cons.inj hwords).1.symm
  subst vs
  exact ⟨by simp [twoPassRel], ws', by simpa using hv, hrel⟩

/-- Readable inputs and output room suffice for total execution and the declared budget. -/
theorem runs_cgs2 {M : Machine K} {dec : K → ℝ} {ed : ℕ → ℝ} {ea : ℝ}
    {ok : ℕ → Prop} {I : Interp Op Tst K} (hS : IsScalar M I)
    (hD : I.Meets .total (Has.inj Blas1Op.dot) ((dotRel dec ed).spec (OutApart ok)))
    (hA : I.Meets .total (Has.inj Blas1Op.axpy) ((axpyRel dec ea).spec (InPlace ok)))
    (hneg : ∀ a, dec (M.neg a) = -dec a)
    (W : Op → List ℕ → ℕ) {n k : ℕ} {τ : Tape K} {μ : Mem K}
    {Q w : ℕ × ℕ} {qs ws : List K} (hok : ok n) (hQw : Q.1 ≠ w.1)
    (hl : μ.Live [Q, w]) (hqs : μ.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hws : μ.store.readBlock w.1 w.2 n = some ws) (hz : μ.Room [w] [n]) :
    Runs I W τ cgs2 (Env.frame [n, k] [Q, w, w]) μ (cgs2Count n k) (cgs2Peak W n k)
      ((twoPassRel dec ed ea).Post [n, k] [qs, ws] [w] [] μ) := by
  have hl' : μ.Live ([Q, w] ++ [w]) := by
    simp only [List.cons_append, List.nil_append, Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2, hl.2⟩
  refine ((cgs2_spec hS hD hA hneg).runs_rel W (d := [n, k]) (ins := [Q, w]) (outs := [w])
    rfl ⟨hok, Q, w, rfl, rfl, hQw⟩ hl'
    (Mem.readBlocks_of_cons hqs (Mem.readBlocks_of_cons hws rfl)) trivial hz).mono
      (le_of_eq (staticCost_cgs2 ..)) (staticPeak_cgs2_le ..) ?_
  intro μ' h
  exact h

end NLAlib.Krylov.Lanczos.Reorth
