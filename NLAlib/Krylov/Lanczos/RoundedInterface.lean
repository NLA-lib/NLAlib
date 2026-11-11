/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedNormalization

/-!
# Composing rounded guarded Lanczos normalization

The rounded total normalization certificate exposes the vector and scalar reads required by
an enclosing recurrence invariant. Its footprint covers only the two output blocks.

## Main results

* `NLAlib.Krylov.Lanczos.normalize_rounded_writes`: rounded normalization with actual readback.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- Guarded normalization writes only the next vector and its coupling coefficient. Actual
output reads and local norm/scaling bounds support the next iteration, including breakdown. -/
theorem normalize_rounded_writes {M : Machine K} {dec : K → ℝ} {n : ℕ} {I : Interp Op Tst K}
    {u : ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hu : u < 1) (hd : ε.dot n < 1)
    (hB : IsBlas1 dec ε ok I) (hok : ok n) (hCmp : IsCmp dec I)
    {τ : Tape K} {μ : Mem K} {w s q b : ℕ × ℕ} {ws qs : List K} {σ β₀ : K}
    (hws : w.1 ≠ s.1) (hwq : w.1 ≠ q.1) (hwb : w.1 ≠ b.1)
    (hsq : s.1 ≠ q.1) (hsb : s.1 ≠ b.1) (hqb : q.1 ≠ b.1)
    (hl : μ.Live [w, s, q, b])
    (hreadw : μ.store.readBlock w.1 w.2 n = some ws) (hσ : μ.store.get s.1 s.2 = some σ)
    (hreadq : μ.store.readBlock q.1 q.2 n = some qs) (hβ₀ : μ.store.get b.1 b.2 = some β₀)
    (hself : IsDotErr dec (ε.dot n) n (vec ws) (vec ws) σ)
    (hqzero : decv dec n qs = 0) (hbzero : dec β₀ = 0) (hz : μ.Room [q, b] [n, 1]) :
    Writes .total I τ normalize (Env.frame [n] [w, s, q, b, q, b]) (Fp.blocks [q, b] [n, 1])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys β,
        μ'.store.readBlock q.1 q.2 n = some ys ∧ μ'.store.get b.1 b.2 = some β ∧
        IsNrm2Err dec (ε.dot n) u n (vec ws) β ∧
        IsScalErr dec ε.scal n β (vec ws) (vec ys) ∧
        (decv dec n ws = 0 → decv dec n ys = 0)) μ := by
  have hl' : μ.Live ([w, s, q, b] ++ [q, b]) := by
    simp only [Mem.live_cons, Mem.live_nil, List.cons_append, List.nil_append, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.2.1, hl.2.2.2, hl.2.2.1, hl.2.2.2⟩
  have hread : μ.readBlocks [w, s, q, b] [n, 1, n, 1] = some [ws, [σ], qs, [β₀]] :=
    Mem.readBlocks_of_cons hreadw (Mem.readBlocks_of_cons (Store.readBlock_one_of_get hσ)
      (Mem.readBlocks_of_cons hreadq (Mem.readBlocks_of_cons
        (Store.readBlock_one_of_get hβ₀) rfl)))
  have hpre : (((normalizeRoundedRel dec (ε.dot n) u ε.scal n).spec (NormalizeOperands n)).on .total
      [n] [w, s, q, b] [q, b] τ μ).pre μ :=
    ⟨rfl, ⟨rfl, w, s, q, b, rfl, rfl, hws, hwq, hwb, hsq, hsb, hqb⟩,
      fun _ => ⟨hl', ⟨[ws, [σ], qs, [β₀]], hread, hself, hqzero, hbzero⟩, hz⟩⟩
  refine ((normalize_rounded_spec hS hM hu hd hB hok hCmp).writes hpre hl').mono le_rfl ?_
  rintro μ' _ ⟨X, hX, _, Y, hlen, hrel, rfl⟩
  obtain rfl : X = [ws, [σ], qs, [β₀]] := Option.some.inj (hX.symm.trans hread)
  obtain ⟨ys, bs, rfl⟩ := List.length_eq_two.mp
    (show Y.length = 2 by simpa using congrArg List.length hlen)
  have hbslen : bs.length = 1 := by
    simpa using congrArg (fun ls => ls.getD 1 0) hlen
  obtain ⟨β, rfl⟩ := List.length_eq_one_iff.mp hbslen
  have hap : Fp.Apart [q, b] [n, 1] := by disjoint
  have hout := Mem.readBlocks_updBlocks (m := μ) (zs := [q, b]) (ys := [ys, [β]])
    (by rw [hlen]; exact hap) (by rw [hlen]; exact hz)
  rw [hlen] at hout
  obtain ⟨q₁, b₁, vs, cs, hops, hv, hc, hwords⟩ := Mem.readBlocks_two hout
  simp only [List.cons.injEq, and_true] at hops hwords
  rcases hops with ⟨hq, hb⟩
  subst q₁ b₁
  rcases hwords with ⟨hvs, hcs⟩
  subst vs cs
  exact ⟨by simp, ys, β, by simpa using hv,
    by simpa using Store.get_of_readBlock hc (j := 0) (by omega) β, hrel⟩

end NLAlib.Krylov.Lanczos
