/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Loop

/-!
# Sparse updates of stored vectors

A patch loop changes a mathematical vector by `Function.update` at an arbitrary sequence of
addresses. Addresses may repeat. Clients prove only the local write and the mathematical
update equation; this rule supplies the loop invariant, the untouched entries and the complete
buffer footprint. Initializing a matrix and overwriting its diagonal is one such patch loop.

## Main results

* `NLAlib.Ops.Store.HoldsVec.update_of_eqOff`: a local write is a mathematical vector update.
* `NLAlib.Ops.writes_patch`: a loop of local writes follows its mathematical vector recurrence.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-- A vector-cell write may reuse disjoint scratch while still representing exactly
one mathematical update. The scratch need not preserve its previous contents. -/
theorem Store.HoldsVec.update_of_frame {s s' : Store K} {b off len i : ℕ} {v : ℕ → K}
    {w : K} {scratch : Fp} (h : s.HoldsVec b off len v)
    (hfr : s.EqOff (Store.inBlock b (off + i) 1 ⊔ scratch) s')
    (hScratch : Fp.Disj scratch (Store.inBlock b off len))
    (hw : s'.get b (off + i) = some w) :
    s'.HoldsVec b off len (Function.update v i w) := by
  intro j hj
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using hw
  · rw [Function.update_of_ne hji, hfr.get_eq ?_]
    · exact h j hj
    · rintro (⟨-, hlo, hhi⟩ | hs)
      · omega
      · exact hScratch _ _ hs ⟨rfl, by omega, by omega⟩

/-- A run changing only one vector cell, and writing its new word there, performs exactly the
corresponding mathematical `Function.update` on the represented vector. -/
theorem Store.HoldsVec.update_of_eqOff {s s' : Store K} {b off len i : ℕ} {v : ℕ → K} {w : K}
    (h : s.HoldsVec b off len v) (hfr : s.EqOff (Store.inBlock b (off + i) 1) s')
    (hw : s'.get b (off + i) = some w) :
    s'.HoldsVec b off len (Function.update v i w) := by
  apply h.update_of_frame (scratch := ⊥) (by simpa using hfr) (Fp.disj_bot_left _) hw

/-- A loop of single-cell patches follows any supplied mathematical update recurrence. No
injectivity of the addresses is needed. All capacity and source facts outside the block remain
available to each round through the frame from the initial store. -/
theorem writes_patch {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {m : Mem K}
    {n : IExp} {body : Stmt Op Tst} {N b off len : ℕ}
    (hn : n.eval ρ.idx = some N) (state : ℕ → ℕ → K) (address : ℕ → ℕ) (value : ℕ → K)
    (hinit : m.store.HoldsVec b off len (state 0))
    (haddr : ∀ i < N, address i < len)
    (hnext : ∀ i < N, state (i + 1) = Function.update (state i) (address i) (value i))
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (Store.inBlock b off len) m'.store →
      m'.store.HoldsVec b off len (state i) → m'.pos = m.pos →
      Writes md I τ body (ρ.pushIdx i) (Store.inBlock b (off + address i) 1)
        (fun m'' => m''.store.get b (off + address i) = some (value i) ∧
          m''.pos = m.pos) m') :
    Writes md I τ (.loop n body) ρ (Store.inBlock b off len)
      (fun m' => m'.store.HoldsVec b off len (state N) ∧ m'.pos = m.pos) m := by
  refine writes_loop hn (fun _ => Store.inBlock b off len) (fun _ _ => le_rfl)
    (fun i m' => m'.store.HoldsVec b off len (state i) ∧ m'.pos = m.pos) ⟨hinit, rfl⟩
    fun i hi m' hfr ⟨hv, hp⟩ => ?_
  refine (hstep i hi m' hfr hv hp).mono
    (Fp.inBlock_le_inBlock (by omega) (by have := haddr i hi; omega)) ?_
  intro m'' hfr' ⟨hw, hp'⟩
  rw [hnext i hi]
  exact ⟨hv.update_of_eqOff hfr' hw, hp'⟩

end NLAlib.Ops
