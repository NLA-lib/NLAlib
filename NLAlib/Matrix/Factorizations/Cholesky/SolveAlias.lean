/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.Solve
public import NLAlib.Matrix.Factorizations.TriangularSolve.Alias

/-!
# Actual Cholesky solve with RHS and source aliases

The existing guarded factor-and-solve body first computes its scoped factors, then writes the
solution. Its source may overlap that final output. The RHS may be exactly the output or
block-disjoint from it. All source words in the postcondition refer to the original reads.

## Main results

* `NLAlib.Cholesky.solve_writes`: actual original-system solution with source/RHS aliases.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op] [Inhabited K]

/-- The guarded actual Cholesky solve permits source/output overlap and an exact or disjoint RHS.
Only the solution block changes after scoped factors are released. Nonbreakdown is a property
of the original matrix; empty order needs no live handle or output capacity. -/
theorem solve_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M)
    {n : ℕ} {τ : Tape K} {m : Mem K} {A b x : ℕ × ℕ} {as bs : List K}
    (hlive : 0 < n → m.Live [A, b, x])
    (hbx : Fp.Disj (Store.inBlock b.1 b.2 n) (Store.inBlock x.1 x.2 n) ∨ b = x)
    (has : m.store.readBlock A.1 A.2 (n * n) = some as)
    (hbs : m.store.readBlock b.1 b.2 n = some bs)
    (hroom : 0 < n → x.2 + n ≤ m.store.len x.1)
    (hA : (decodeMatrix dec n n as).PosDef) :
    Writes .total I τ (solve (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [A, b, x]) (Store.inBlock x.1 x.2 n)
      (fun μ => μ.pos = m.pos ∧ ∃ xs, μ.store.readBlock x.1 x.2 n = some xs ∧
        decodeMatrix dec n n as *ᵥ decv dec n xs = decv dec n bs) m := by
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    obtain ⟨hlA, hlb, hlx⟩ : A.1 < m.store.length ∧ b.1 < m.store.length ∧
        x.1 < m.store.length := by
      simpa only [Mem.live_cons, Mem.live_nil, and_true] using hlive hn
    have hxroom := hroom hn
    change Writes .total I τ _ _ _ _ m
    alloc as L
    have hAL : A.1 ≠ L := by change A.1 ≠ m.store.length + 0; omega
    have hbL : b.1 ≠ L := by change b.1 ≠ m.store.length + 0; omega
    have hxL : x.1 ≠ L := by change x.1 ≠ m.store.length + 0; omega
    call (rightLooking_meets hI hM) [n] (A, (L, 0)) (pre := hA)
      as μ hfr hpos (ls) hfactor
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      change A.1 < s_L.length ∧ m.store.length < s_L.length
      simp only [List.length_singleton] at hlen_L
      omega
    case' hroom =>
      change (0 + n * n ≤ s_L.len L) ∧ True
      exact ⟨by simpa only [Nat.zero_add] using hL.ge, trivial⟩
    have hf : IsCholesky (decodeMatrix dec n n as) (decodeMatrix dec n n ls) := hfactor.2.1
    have htri : (TriangularSolve.choleskySpec dec).pre [n] (τ.shift μ.pos) [ls, bs] := by
      refine ⟨hf.isLowerTriangular, ?_⟩
      intro i hi
      have hp := hf.apply_self_pos (⟨i, hi⟩ : Fin n)
      simpa only [decodeMatrix_apply] using hp.ne'
    have hlenμ : μ.store.length = s_L.length := hfr.length_eq
    have hLive : μ.Live [(L, 0), b, x] := by
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      change m.store.length < μ.store.length ∧ b.1 < μ.store.length ∧ x.1 < μ.store.length
      simp only [List.length_singleton] at hlen_L
      omega
    have hbs' : μ.store.readBlock b.1 b.2 n = some bs := by keep
    refine ((TriangularSolve.cholesky_writes hI hM (fun _ => hLive) (fun _ => hxL.symm)
      hbx hls hbs' (fun _ => by
        rw [hfr.len_eq, (hbelow_L x.1 hlx).1]; exact hxroom) htri).in_frame
      rfl rfl hLive).mono (by fp_sub) ?_
    rintro ν hfr' ⟨hpos', xs, hxs, hsolve⟩ s₂ hs₂ hB₂
    refine ⟨hpos'.trans hpos, xs, Store.Below.readBlock_of hB₂ hlx hxs, ?_⟩
    rw [hf.eq_mul_conjTranspose]
    exact hsolve
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    refine ⟨rfl, [], rfl, ?_⟩
    ext i
    exact i.elim0

/-- In-place RHS interface of the existing guarded factor-then-solve tree. No factor or
solution is supplied as semantic input, and the instruction body is unchanged. -/
def solveInPlace : Routine Op Tst :=
  routine% [n] (A : n * n, b : n) → (b) :=
    (solve (Op := Op) (Tst := Tst)).body

/-- The in-place interface shares the complete existing guarded scalar body. -/
theorem body_solveInPlace :
    (solveInPlace (Op := Op) (Tst := Tst)).body =
      (solve (Op := Op) (Tst := Tst)).body := rfl

/-- The actual factorization overwrites its own RHS with an original-system solution.
The declared matrix domain and numerical conclusion are the ordinary solve specification. -/
theorem solveInPlace_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) :
    (solveInPlace (Op := Op) (Tst := Tst)).Meets I (solveSpec dec) := by
  routine_intro [n] (A, b) reads (as, bs)
  have hLive : m.Live [A, b, b] := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using And.intro hl.1 ⟨hl.2, hl.2⟩
  refine (solve_writes hI hM (fun _ => hLive) (Or.inr rfl) has hbs
    (fun _ => hroom) hpre).mono (by fp_sub) ?_
  rintro μ hfr ⟨hpos, xs, hxs, hpost⟩
  exact ⟨hpos, [xs], Mem.readBlocks_of_cons hxs rfl, hpost⟩

end NLAlib.Cholesky
