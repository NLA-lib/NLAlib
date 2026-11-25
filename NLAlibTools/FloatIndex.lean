/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.Float

/-!
# Bounded Float index conversion for executable examples

The tool Float interpreter predates dynamic index binders. This adapter supplies their
conversion on finite nonnegative words through binary64's exact-integer range. It is shared
by the executable pivot examples, without asserting a formal scalar-accuracy or range model.
-/

open NLAlib.Computation

namespace NLAlibTools

/-- Convert finite nonnegative tool words no larger than $2^{53}$ to natural indices.
The bounded unsigned conversion truncates fractional words; callers expecting an integer
must check that separately. No formal decoding or floating-point accuracy theorem is assumed. -/
def boundedFloatToNat (x : Float) : Option ℕ :=
  if x.isFinite && decide (0 ≤ x) && decide (x ≤ 9007199254740992) then
    some x.toUInt64.toNat
  else none

/-- The existing tool Float interpreter with bounded dynamic-index conversion. Matrix-oracle
and tape behavior are retained. This is an executable example backend, not a proof of the
library's index-exactness or relative-error assumptions. -/
def floatIndexedInterp (A : Array (Array Float)) (tape : List Float) :
    Interp Unit Unit Float (ℕ × ℕ × ℕ) :=
  { floatInterp A tape with sem := { floatSem with toNat := fun _ => boundedFloatToNat } }

end NLAlibTools
