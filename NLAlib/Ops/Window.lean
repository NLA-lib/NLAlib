/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Frame
public import NLAlib.Ops.StoreSimp
public import NLAlib.Ops.Cert
public import NLAlib.Ops.Tape

/-!
# Operations with a tape window: draws and hidden randomness

A contract in operand form (`NLAlib.Ops.BlockRel`) may read a window of the tape: the output
blocks are related to the input blocks **and to the entries of the window**, and the position
advances by the length of the window. The operation takes no random operand. Two uses:

* **visible randomness**: `NLAlib.Ops.drawRel s`, a vector draw; the output block *is* the
  window, so the values are in the store of the algorithm that called it;
* **hidden randomness**: the output is some function of the inputs and of the window (a noisy
  product, a stochastically rounded sum). The algorithm holds no cell with the window entries
  and no operation hands them out, so it cannot compute with them.

The call rule is the one rule `NLAlib.Ops.wp_call_rel`, and the certificate of an implementation
that draws into its own scratch is the one certificate `NLAlib.Ops.Impl.Triple`.

The statement about the law is separate and is mathematics: with the law of the tape
(`NLAlib.Ops.IsTapeLaw`), the window of a call at the position `p` is independent of the past of
`p`, with the product law (`NLAlib.Ops.IsTapeLaw.integral_window`). So a contract of this form
is a contract **conditional on the history**: for inputs that are any function of the past, the
output has the law that the relation gives it from a fresh window.

## Main results

* `NLAlib.Ops.drawRel`, `NLAlib.Ops.Interp.IsFn.meets_drawRel`: the vector draw; the vector draw
  of the model meets its contract.
* `NLAlib.Ops.wp_loop_fill`: the loop that fills a block cell by cell.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Op₁ Op₂ Tst K : Type}

section Rules

variable {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {Q : Mem K → Prop} {m : Mem K}

/-- **The loop that fills a block cell by cell**: round `i` writes the value `v i` in the cell
`o + i` of the buffer `b` and moves the position from `pos i` to `pos (i + 1)`; it may read the
cells already written and everything outside the block. -/
theorem wp_loop_fill {n : IExp} {body : Stmt Op Tst} {N b o : ℕ} {S : Store K} (v : ℕ → K)
    (pos : ℕ → ℕ) (hn : n.eval ρ.idx = some N)
    (hstep : ∀ i < N, ∀ s', S.EqOff (Store.inBlock b o i) s' →
      s'.readBlock b o i = some ((List.range i).map v) →
      Wp md I τ body (ρ.pushIdx i) (· = ⟨s'.upd b (o + i) (v i), pos (i + 1)⟩) ⟨s', pos i⟩)
    (hlen : o + N ≤ S.len b)
    (hQ : ∀ s', S.EqOff (Store.inBlock b o N) s' →
      s'.readBlock b o N = some ((List.range N).map v) → Q ⟨s', pos N⟩) :
    Wp md I τ (.loop n body) ρ Q ⟨S, pos 0⟩ := by
  refine wp_loop hn (fun i m' => ∃ s', m' = ⟨s', pos i⟩ ∧ S.EqOff (Store.inBlock b o i) s' ∧
    s'.readBlock b o i = some ((List.range i).map v)) ⟨S, rfl, by
      simpa using Store.EqOff.refl _ _, by simp⟩ ?_ fun m' ⟨s', h1, h2, h3⟩ => h1 ▸ hQ s' h2 h3
  rintro i hi m' ⟨s', rfl, hfr, hr⟩
  refine (hstep i hi s' hfr hr).mono ?_
  rintro m' rfl
  refine ⟨_, rfl, (hfr.mono fun b' q h => ⟨h.1, h.2.1, by have := h.2.2; omega⟩).upd
    ⟨rfl, by omega, by omega⟩ _, ?_⟩
  rw [List.range_succ, List.map_append]
  have := Store.readBlock_upd_concat hr (by rw [hfr.len_eq]; omega) (v i)
  simpa using this

end Rules

/-! ### Visible randomness: the vector draw -/

/-- **The vector draw** `draw [n] [] [g]` of the stream `s`: the block `g` receives the window of
`n` entries. The values drawn are in the store of the caller. -/
@[simps (attr := storeNF)]
def drawRel (s : ℕ) : BlockRel K where
  nd := 1
  stream := s
  win d := d.headD 0
  inLens _ := []
  outLens d := [d.headD 0]
  rel _ _ w ys := ys = [w]

/-- The vector draw of the model meets the contract of the vector draw. -/
theorem Interp.IsFn.meets_drawRel {I : Interp Op Tst K} {o : Op} {s : ℕ}
    {adm adm' : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    (h : I.IsFn .total o (.drawVec s) adm')
    (hsub : ∀ d ins outs, adm d ins outs → adm' d ins outs) :
    I.Meets .total o ((drawRel s).spec adm) := by
  refine h.meets_rel hsub rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
  intro d w xs m ins outs hnd hw _ hr _
  obtain ⟨rfl, rfl⟩ := Mem.readBlocks_zero hr
  exact ⟨[w], rfl, by simpa [drawRel] using hw, rfl⟩

end NLAlib.Ops
