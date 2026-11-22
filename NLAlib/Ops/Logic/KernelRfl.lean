/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public meta import Lean.Elab.Tactic.Basic

/-!
# Closing a closed computation by the kernel

`kernel_rfl` closes an equation `a = b` by `Eq.refl a` and leaves the definitional check to the
kernel, which evaluates closed terms with sharing. It is the tactic for the instruction
polynomial and the monomial bound of a fixed program: the elaborator's `rfl` unfolds the
instrumented tree without sharing and exceeds its recursion depth, the kernel does not.

## Main results

* `kernel_rfl`: an equation closed by reflexivity, checked by the kernel only.
-/

@[expose] public section

namespace NLAlib.Ops

open Lean Elab Tactic Meta in
/-- **`kernel_rfl`**: close an equation `a = b` by `Eq.refl a` without the elaborator's
definitional check; the kernel checks it when the declaration is added (and fails it there if
`a` and `b` are not definitionally equal). For closed computations, such as the monomial bound
of a fixed program, that the kernel evaluates with sharing. -/
elab (name := kernelRfl) "kernel_rfl" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (_, a, _) := t.eq? | throwError "kernel_rfl: not an equation"
  g.assign (← mkEqRefl a)
  replaceMainGoal []

end NLAlib.Ops
