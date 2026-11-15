/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.Backward

/-!
# Backward steps through a frame and an allocation

A program calls a fixed implementation through a frame: its dimensions and buffer views are
evaluated in the caller's environment, and the body runs in the frame environment. A backward
step proved for the body in its own frame environment is a backward step of the framed call,
provided the views are live in every memory of the precondition. This is the backward-step form
of `NLAlib.Ops.Writes.in_frame`; without it a composed proof unfolds every framed body by hand.

Scratch allocation is the same: the body runs on the caller's store extended by fresh handles
after its length $L$, and the allocation removes them at the end. A backward step of the body,
for each $L$, from the memories obtained by allocating after a precondition memory of length
$L$, is a backward step of the allocation, provided the postcondition only reads below the
caller's handles (it survives replacing the handles from $L$ on).

## Main results

* `NLAlib.Ops.BackwardStep.in_frame`: a backward step of a body is one of its framed call.
* `NLAlib.Ops.BackwardStep.allocs`: a backward step of a body is one of its scratch
  allocation.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type} {α : Type*}

namespace BackwardStep

variable {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {F : Fp}
  {R : ℝ → α → α → Prop} {S S' : α → Mem K → Prop} {ε : ℝ}

/-- **A backward step through a frame**: if the body is a backward step in the frame environment
of the evaluated dimensions $d$ and views $a$, and every memory of the precondition has the
views $a$ live, the framed call is the same backward step in the caller's environment. -/
theorem in_frame {ds : List IExp} {args : List Operand} {body : Stmt Op Tst}
    {d : List ℕ} {a : List (ℕ × ℕ)}
    (h : BackwardStep md I τ body (Env.frame d a) F R S S' ε)
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ args = some a)
    (hl : ∀ x m, S x m → m.Live a) :
    BackwardStep md I τ (.frame ds args body) ρ F R S S' ε :=
  fun x m hx => (h x m hx).in_frame hd ha (hl x m hx)

/-- **A backward step through a scratch allocation**: let the dimensions `lens` evaluate to
`ns`. Suppose that for every caller store length $L$ the body is a backward step, in the
environment with the fresh handles $L, \dots, L + |ns| - 1$ appended to the buffers and with
footprint `F ⊔ Fp.above L`, from every memory obtained by allocating after a precondition
memory of length $L$ (same tape position, the old handles unchanged below $L$, the new handles
of lengths `ns`). If the postcondition of every state survives replacing the handles from the
caller's length on, the allocation is the same backward step in the caller's environment. -/
theorem allocs {lens : List IExp} {body : Stmt Op Tst} {ns : List ℕ}
    (hn : IExp.evalList ρ.idx lens = some ns)
    (hkeep : ∀ a m, S a m → ∀ b {s s' : Store K} {p : ℕ},
      Store.Below m.store.length s s' → S' b ⟨s, p⟩ → S' b ⟨s', p⟩)
    (h : ∀ L : ℕ, BackwardStep md I τ body
      ⟨ρ.idx, ρ.buf ++ (List.range ns.length).map (L + ·)⟩ (F ⊔ Fp.above L) R
      (fun a m₁ => ∃ m : Mem K, S a m ∧ m.store.length = L ∧ m₁.pos = m.pos ∧
        m₁.store.length = L + ns.length ∧
        (∀ i (hi : i < ns.length), m₁.store.len (L + i) = ns[i]) ∧
        Store.Below L m.store m₁.store) S' ε) :
    BackwardStep md I τ (.allocs lens body) ρ F R S S' ε := fun a m hS =>
  writes_allocs_preserving_post hn (fun hB ⟨b, hab, hb⟩ => ⟨b, hab, hkeep a m hS b hB hb⟩)
    fun s₁ hs₁ hlens hBelow => h m.store.length a ⟨s₁, m.pos⟩ ⟨m, hS, rfl, rfl, hs₁, hlens, hBelow⟩

end BackwardStep

end NLAlib.Ops
