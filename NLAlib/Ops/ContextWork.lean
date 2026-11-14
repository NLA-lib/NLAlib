/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.IndexDegrees

/-!
# Context-sensitive fixed-program work measures

A fixed statement has a structural coefficient, a work exponent relative to its index slots,
and separate bounds on primitive dimension degrees and arities. Frames pass the individual
slot degrees to their bodies; loops and bounded queries append their bound's degree. Sequence
adds coefficients while taking the larger exponent, avoiding exponent growth from sequence
length alone. Applied to instrumented syntax, these measures include structural calls.

## Main results

* `NLAlib.Ops.Stmt.workCoefficient`: the structural coefficient of a fixed tree.
* `NLAlib.Ops.Stmt.workDegreeAt`: the work exponent relative to individual index degrees.
* `NLAlib.Ops.Stmt.callDegreeAt`: a separate exponent for primitive dimension values.
* `NLAlib.Ops.Stmt.callArity`: the largest operation or query dimension-list length.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst : Type}

/-- A structural coefficient independent of index values and degree assignments. Sequential
and alternative branches contribute additively; each query contributes one weight unit. -/
def Stmt.workCoefficient : Stmt Op Tst → ℕ
  | .skip | .abort => 0
  | .call _ _ _ _ => 1
  | .seq s t => s.workCoefficient + t.workCoefficient
  | .ite _ _ _ s t | .whileFuel _ _ _ _ s t => 1 + s.workCoefficient + t.workCoefficient
  | .bindIdx _ _ _ s => 1 + s.workCoefficient
  | .loop _ s | .allocAs _ _ s | .frame _ _ s => s.workCoefficient

/-- A work exponent relative to separate initial slot degrees. Bounded loops add their
iteration-count exponent to the body's exponent; frame substitution retains slot distinctions. -/
def Stmt.workDegreeAt : Stmt Op Tst → List ℕ → ℕ
  | .skip, _ | .abort, _ | .call _ _ _ _, _ => 0
  | .seq s t, degrees | .ite _ _ _ s t, degrees =>
    max (s.workDegreeAt degrees) (t.workDegreeAt degrees)
  | .whileFuel fuel _ _ _ s t, degrees =>
    let d := fuel.degreeAt degrees
    max (d + s.workDegreeAt (degrees ++ [d])) (t.workDegreeAt (degrees ++ [d]))
  | .bindIdx _ _ bound s, degrees => s.workDegreeAt (degrees ++ [bound.degreeAt degrees])
  | .loop bound s, degrees =>
    let d := bound.degreeAt degrees
    d + s.workDegreeAt (degrees ++ [d])
  | .allocAs _ _ s, degrees => s.workDegreeAt degrees
  | .frame ds args s, degrees =>
    s.workDegreeAt (ds.map (IExp.degreeAt degrees) ++
      args.map (fun a => a.off.degreeAt degrees))

/-- The largest primitive dimension degree at any operation or query in the fixed tree.
Frame and binder contexts agree with the work-exponent analysis; no call shape is inferred
from the total work exponent. Index queries have an empty dimension list. -/
def Stmt.callDegreeAt : Stmt Op Tst → List ℕ → ℕ
  | .skip, _ | .abort, _ => 0
  | .call _ ds _ _, degrees => IExp.listDegreeAt degrees ds
  | .seq s t, degrees => max (s.callDegreeAt degrees) (t.callDegreeAt degrees)
  | .ite _ ds _ s t, degrees =>
    max (IExp.listDegreeAt degrees ds) (max (s.callDegreeAt degrees) (t.callDegreeAt degrees))
  | .whileFuel fuel _ ds _ s t, degrees =>
    let extended := degrees ++ [fuel.degreeAt degrees]
    max (IExp.listDegreeAt extended ds) (max (s.callDegreeAt extended) (t.callDegreeAt extended))
  | .bindIdx _ _ bound s, degrees | .loop bound s, degrees =>
    s.callDegreeAt (degrees ++ [bound.degreeAt degrees])
  | .allocAs _ _ s, degrees => s.callDegreeAt degrees
  | .frame ds args s, degrees =>
    s.callDegreeAt (ds.map (IExp.degreeAt degrees) ++
      args.map (fun a => a.off.degreeAt degrees))

/-- The largest operation or query dimension-list length, independent of index values.
An index query's list is empty; dimensions used only to enter a frame are not primitive calls. -/
def Stmt.callArity : Stmt Op Tst → ℕ
  | .skip | .abort => 0
  | .call _ ds _ _ => ds.length
  | .seq s t => max s.callArity t.callArity
  | .ite _ ds _ s t | .whileFuel _ _ ds _ s t => max ds.length (max s.callArity t.callArity)
  | .bindIdx _ _ _ s | .loop _ s | .allocAs _ _ s | .frame _ _ s => s.callArity

end NLAlib.Ops
