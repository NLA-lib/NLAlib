/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Ops.Logic.Scalar
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# Actual rounded constants of spectral bisection

One and two are stored by their declared literal operations. Division, negation and square
root then compute the remaining words using the same scalar machine.

## Main results

* `NLAlib.SpectralBisection.writes_initialConstants`: the five actual stored constant words.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] {M : Machine K}

private def constantTail : Impl Op Tst := opsImpl% [] () → (c) {
  call (Has.inj ScalarOp.div) [] (c, c[1]) → (c[2]);
  call (Has.inj ScalarOp.neg) [] (c) → (c[3]);
  call (Has.inj ScalarOp.sqrt) [] (c[2]) → (c[4])
}

omit [Has IndexOp Op] in
private theorem writes_constantTail {I : Interp Op Tst K} (hS : IsScalar M I) {τ : Tape K}
    {b off : ℕ} {m : Mem K} (h0 : m.store.get b off = some (M.lit 1))
    (h1 : m.store.get b (off + 1) = some (M.lit 2)) (hroom : off + 5 ≤ m.store.len b) :
    Writes .total I τ constantTail.body (Env.frame [] [(b, off)])
      (Store.inBlock b off 5)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock b off 5 =
        some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1),
          M.sqrt (M.div (M.lit 1) (M.lit 2))]) m := by
  let half := M.div (M.lit 1) (M.lit 2)
  let xs : List (ScalarIns ScalarOp) :=
    [⟨.div, [⟨0, .var 0⟩, ⟨0, .var 0 + .const 1⟩], ⟨0, .var 0 + .const 2⟩⟩,
      ⟨.neg, [⟨0, .var 0⟩], ⟨0, .var 0 + .const 3⟩⟩,
      ⟨.sqrt, [⟨0, .var 0 + .const 2⟩], ⟨0, .var 0 + .const 4⟩⟩]
  let ws := [((b, off + 2), half), ((b, off + 3), M.neg (M.lit 1)),
    ((b, off + 4), M.sqrt half)]
  have hev : ScalarIns.evalBlock M.eval (Env.frame [] [(b, off)]) xs m.store.cellFn =
      some ws := by
    simp [xs, ws, half, ScalarIns.evalBlock, Operand.evalList, Operand.eval, IExp.eval,
      Env.frame, Store.cellFn, Machine.eval, h0, h1, Prod.mk.injEq]
  have hcap : ∀ z ∈ ws, z.1.2 < m.store.len z.1.1 := by
    intro z hz
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> dsimp <;> omega
  have hw := writes_machineScalarBlock (τ := τ) hS hev hcap
  change Writes .total I τ constantTail.body _ _ _ m at hw
  refine hw.mono ?_ ?_
  · intro cb i hi
    simp only [ws, List.map_cons, List.map_nil, Fp.cells, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨rfl, by omega, by omega⟩
  · rintro μ _ rfl
    have hg0 : (m.updCells ws).store.get b off = some (M.lit 1) := by
      exact (get_updCells_of_notMem (m := m) (ws := ws)
        (z := (b, off)) (by simp [ws])).trans h0
    have hg1 : (m.updCells ws).store.get b (off + 1) = some (M.lit 2) := by
      exact (get_updCells_of_notMem (m := m) (ws := ws)
        (z := (b, off + 1)) (by simp [ws])).trans h1
    have hg2 := get_updCells (m := m) (ws₁ := [])
      (ws₂ := [((b, off + 3), M.neg (M.lit 1)), ((b, off + 4), M.sqrt half)])
      (z := (b, off + 2)) (v := half) (by dsimp; omega) (by simp)
    have hg3 := get_updCells (m := m) (ws₁ := [((b, off + 2), half)])
      (ws₂ := [((b, off + 4), M.sqrt half)])
      (z := (b, off + 3)) (v := M.neg (M.lit 1)) (by dsimp; omega) (by simp)
    have hg4 := get_updCells (m := m)
      (ws₁ := [((b, off + 2), half), ((b, off + 3), M.neg (M.lit 1))])
      (ws₂ := []) (z := (b, off + 4)) (v := M.sqrt half) (by dsimp; omega) (by simp)
    refine ⟨by simp [ws, Mem.updCells], Store.readBlock_eq_some_iff.mpr ⟨rfl, ?_⟩⟩
    intro j hj
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;> first
    | simpa [ws, half] using hg0
    | simpa [ws, half] using hg1
    | simpa [ws, half] using hg2
    | simpa [ws, half] using hg3
    | simpa [ws, half] using hg4

/-- Capacity alone suffices to compute the actual constants; exactness of their decoding is a
separate numerical hypothesis. The operations consume no random words. -/
theorem writes_initialConstants {I : Interp Op Tst K} (hS : IsScalar M I)
    (hIndex : IsIndexLit M I) {τ : Tape K} {b off : ℕ} {m : Mem K}
    (hroom : off + 5 ≤ m.store.len b) :
    Writes .total I τ initialConstants.body (Env.frame [] [(b, off)]) (Store.inBlock b off 5)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock b off 5 =
        some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1),
          M.sqrt (M.div (M.lit 1) (M.lit 2))]) m := by
  have hone := writes_call_const (md := .total) (τ := τ) (m := m)
    (ρ := Env.frame [] [(b, off)]) (hS (.lit 1)) (out := ⟨0, .var 0⟩)
    rfl trivial (by dsimp; omega)
  refine hone.seq_le (Fp.inBlock_le_inBlock (by omega) (by omega)) fun μ hfr0 h0 => ?_
  have htwo := writes_indexLit (m := μ) (τ := τ) (ρ := Env.frame [] [(b, off)]) hIndex
    (e := .const 2) (out := ⟨0, .var 0 + .const 1⟩) rfl rfl
    (by rw [hfr0.len_eq]; dsimp; omega)
  refine htwo.seq_le (Fp.inBlock_le_inBlock (by omega) (by omega)) fun ν hfr1 h1 => ?_
  have h0' := hfr1.keep (Store.readsOnly_get b off (M.lit 1)) (by disjoint) h0.2
  exact (writes_constantTail (τ := τ) hS h0' h1.2
    (by rw [hfr1.len_eq, hfr0.len_eq]; exact hroom)).mono le_rfl
    fun _ _ h => ⟨h.1.trans (h1.1.trans h0.1), h.2⟩

end NLAlib.SpectralBisection
