/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Backward

/-!
# Backward steps through a frame

A program calls a fixed implementation through a frame: its dimensions and buffer views are
evaluated in the caller's environment, and the body runs in the frame environment. A backward
step proved for the body in its own frame environment is a backward step of the framed call,
provided the views are live in every memory of the precondition. This is the backward-step form
of `NLAlib.Ops.Writes.in_frame`; without it a composed proof unfolds every framed body by hand.

## Main results

* `NLAlib.Ops.BackwardStep.in_frame`: a backward step of a body is one of its framed call.
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

end BackwardStep

end NLAlib.Ops
