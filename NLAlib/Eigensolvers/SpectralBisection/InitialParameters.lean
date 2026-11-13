/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Ops.Logic.Scalar
public import NLAlib.Ops.Logic.SpatialScalar

/-!
# Root radius and tolerance initialization

The two scalar copies preserve the actual supplied parameter words. Their proof uses the
shared scalar-block rule and spatial separation, including views of the same buffer.

## Main results

* `NLAlib.SpectralBisection.writes_initialParameters`: the root level stores its supplied words.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] {M : Machine K}

/-- The actual supplied radius and tolerance are copied into the root level pair. -/
theorem writes_initialParameters {I : Interp Op Tst K} (hS : IsScalar M I)
    {τ : Tape K} {pb po lb lo : ℕ} {m : Mem K} (R eps : K)
    (hPar : m.store.readBlock pb po 2 = some [R, eps])
    (hdis : Fp.Disj (Store.inBlock pb po 2) (Store.inBlock lb lo 2))
    (hroom : lo + 2 ≤ m.store.len lb) :
    Writes .total I τ initialParameters.body (Env.frame [] [(pb, po), (lb, lo)])
      (Store.inBlock lb lo 2)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock lb lo 2 = some [R, eps]) m := by
  let xs : List (ScalarIns ScalarOp) :=
    [⟨.copy, [⟨0, .var 0⟩], ⟨1, .var 1⟩⟩,
      ⟨.copy, [⟨0, .var 0 + .const 1⟩], ⟨1, .var 1 + .const 1⟩⟩]
  let ws := [((lb, lo), R), ((lb, lo + 1), eps)]
  have hR : m.store.get pb po = some R := by
    simpa using Store.get_of_readBlock hPar (j := 0) (by simp) R
  have hE : m.store.get pb (po + 1) = some eps := by
    simpa using Store.get_of_readBlock hPar (j := 1) (by simp) R
  have hne := hdis.ne_offsets (i := 1) (j := 0) (by simp) (by simp)
  simp only [Nat.add_zero] at hne
  have hev : ScalarIns.evalBlock M.eval (Env.frame [] [(pb, po), (lb, lo)]) xs
      m.store.cellFn = some ws := by
    simp [xs, ws, ScalarIns.evalBlock, Operand.evalList, Operand.eval, IExp.eval, Env.frame,
      Store.cellFn, Machine.eval, hR, hE, hne]
  have hcap : ∀ z ∈ ws, z.1.2 < m.store.len z.1.1 := by
    intro z hz
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> dsimp <;> omega
  have hw := writes_machineScalarBlock (τ := τ) hS hev hcap
  change Writes .total I τ initialParameters.body _ _ _ m at hw
  refine hw.mono ?_ ?_
  · intro b i hi
    simp only [ws, List.map_cons, List.map_nil, Fp.cells, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, by omega, by omega⟩
  · rintro μ _ rfl
    have hg0 := get_updCells (m := m) (ws₁ := []) (ws₂ := [((lb, lo + 1), eps)])
      (z := (lb, lo)) (v := R) (by dsimp; omega) (by simp)
    have hg1 := get_updCells (m := m) (ws₁ := [((lb, lo), R)]) (ws₂ := [])
      (z := (lb, lo + 1)) (v := eps) (by dsimp; omega) (by simp)
    change (m.updCells ws).store.get lb lo = some R at hg0
    change (m.updCells ws).store.get lb (lo + 1) = some eps at hg1
    refine ⟨rfl, ?_⟩
    rw [Store.readBlock_succ, hg0, Option.bind_some, Store.readBlock_succ, hg1,
      Option.bind_some]
    rfl

end NLAlib.SpectralBisection
