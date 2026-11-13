/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.Sweep

/-!
# Composing classical reorthogonalization passes

The pass certificate supplies a footprint rule with actual vector and coefficient reads.
No division, square root, rank assumption or execution-success premise is needed.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.cgsPass_writes`: a total compositional pass interface.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has Blas1Op Op]

/-- A classical pass writes only its residual and coefficient blocks and exposes their reads. -/
theorem cgsPass_writes {M : Machine K} {dec : K → ℝ} {ed : ℕ → ℝ} {ea : ℝ}
    {ok : ℕ → Prop} {I : Interp Op Tst K} (hS : IsScalar M I)
    (hD : I.Meets .total (Has.inj Blas1Op.dot) ((dotRel dec ed).spec (OutApart ok)))
    (hA : I.Meets .total (Has.inj Blas1Op.axpy) ((axpyRel dec ea).spec (InPlace ok)))
    (hneg : ∀ a, dec (M.neg a) = -dec a)
    {n k : ℕ} {τ : Tape K} {μ : Mem K} {Q w H : ℕ × ℕ} {qs ws : List K}
    (hok : ok n) (hQw : Q.1 ≠ w.1) (hQH : Q.1 ≠ H.1) (hwH : w.1 ≠ H.1)
    (hl : μ.Live [Q, w, H]) (hqs : μ.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hws : μ.store.readBlock w.1 w.2 n = some ws) (hz : μ.Room [w, H] [n, k]) :
    Writes .total I τ cgsPass (Env.frame [n, k] [Q, w, w, H])
      (Fp.blocks [w, H] [n, k])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ws' hs,
        μ'.store.readBlock w.1 w.2 n = some ws' ∧
        μ'.store.readBlock H.1 H.2 k = some hs ∧ PassOut dec (ed n) ea n k qs ws ws' hs) μ := by
  have hl' : μ.Live ([Q, w] ++ [w, H]) := by
    simp only [Mem.live_cons, Mem.live_nil, List.cons_append, List.nil_append, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.1, hl.2.2⟩
  have hread : μ.readBlocks [Q, w] [k * n, n] = some [qs, ws] :=
    Mem.readBlocks_of_cons hqs (Mem.readBlocks_of_cons hws rfl)
  have hpre : (((passRel dec ed ea).spec (PassOperands ok)).on .total
      [n, k] [Q, w] [w, H] τ μ).pre μ :=
    ⟨rfl, ⟨hok, Q, w, H, rfl, rfl, hQw, hQH, hwH⟩,
      fun _ => ⟨hl', ⟨[qs, ws], hread, trivial⟩, hz⟩⟩
  refine ((cgsPass_spec hS hD hA hneg).writes hpre hl').mono le_rfl ?_
  rintro μ' _ ⟨X, hX, _, Y, hlen, hrel, rfl⟩
  obtain rfl : X = [qs, ws] := Option.some.inj (hX.symm.trans hread)
  obtain ⟨ws', hs, rfl⟩ := List.length_eq_two.mp
    (show Y.length = 2 by simpa using congrArg List.length hlen)
  have hap : Fp.Apart [w, H] [n, k] := by disjoint
  have hout := Mem.readBlocks_updBlocks (m := μ) (zs := [w, H]) (ys := [ws', hs])
    (by rw [hlen]; exact hap) (by rw [hlen]; exact hz)
  rw [hlen] at hout
  have hout' : ((μ.updBlocks [w, H] [ws', hs]).advance 0).readBlocks [w, H] [n, k] =
      some [ws', hs] := by simpa using hout
  obtain ⟨w₁, H₁, vs, cs, hops, hv, hc, hwords⟩ := Mem.readBlocks_two hout'
  simp only [List.cons.injEq, and_true] at hops hwords
  rcases hops with ⟨hw, hH⟩
  subst w₁ H₁
  rcases hwords with ⟨hvs, hcs⟩
  subst vs cs
  exact ⟨by simp [passRel], ws', hs, hv, hc, hrel⟩

end NLAlib.Krylov.Lanczos.Reorth
