/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Ops.Logic.IndexLiteral
public import NLAlib.Ops.Logic.Loop

/-!
# Initial stored sizes of the bisection tree

Every size slot is explicitly initialized to the machine's zero literal. The root slot is
then overwritten by its actual dimension literal. No uninitialized metadata is read.

## Main results

* `NLAlib.SpectralBisection.writes_initialSizes`: the root size and every empty slot are stored.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {K Op Tst : Type} [Has IndexOp Op] {M : Machine K}

/-- The root dimension and zero literals are the actual stored words. Numerical exactness
of decoding them is not needed to execute initialization. -/
theorem writes_initialSizes {I : Interp Op Tst K} (hIndex : IsIndexLit M I)
    {τ : Tape K} {n L b off : ℕ} {m : Mem K}
    (hroom : off + (n * (L + 2) + 1) ≤ m.store.len b) :
    Writes .total I τ initialSizes.body (Env.frame [n, L] [(b, off)])
      (Store.inBlock b off (n * (L + 2) + 1))
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock b off (n * (L + 2) + 1) =
        some ((List.range (n * (L + 2) + 1)).map
          (fun i => if i = 0 then M.lit (n : ℚ) else M.lit 0))) m := by
  have hz : Writes .total I τ
      (.loop (.var 0 * (.var 1 + .const 2) + .const 1)
        (.call (Has.inj IndexOp.lit) [.const 0] [] [⟨0, .var 2 + .var 3⟩]))
      (Env.frame [n, L] [(b, off)]) (Store.inBlock b off (n * (L + 2) + 1))
      (fun μ => μ.store.HoldsVec b off (n * (L + 2) + 1) (fun _ => M.lit 0) ∧
        μ.pos = m.pos) m := by
    refine writes_fill rfl (fun _ => M.lit 0) (fun _ => m.pos) rfl ?_
    intro i hi μ hfr _ hp
    exact (writes_indexLit (m := μ) (τ := τ) hIndex rfl rfl
      (by rw [hfr.len_eq]; dsimp; omega)).mono le_rfl fun _ _ h => ⟨h.2, h.1.trans hp⟩
  refine hz.seq_le le_rfl fun μ hfr0 hzero => ?_
  have hr := writes_indexLit (m := μ) (τ := τ)
    (ρ := Env.frame [n, L] [(b, off)]) hIndex
    (e := .var 0) (out := ⟨0, .var 2⟩) rfl rfl (by rw [hfr0.len_eq]; dsimp; omega)
  refine hr.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  intro ν hfr1 hroot
  refine ⟨hroot.1.trans hzero.2, Store.holdsVec_iff_readBlock.mp ?_⟩
  intro i hi
  by_cases h0 : i = 0
  · subst i
    simpa using hroot.2
  · have hkept := hfr1.keep (Store.readsOnly_get b (off + i) (M.lit 0))
      (by disjoint) (hzero.1 i hi)
    simpa [h0] using hkept

end NLAlib.SpectralBisection
