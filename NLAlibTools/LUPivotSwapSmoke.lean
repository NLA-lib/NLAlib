/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.LU.Swap
import NLAlib.Ops.Tools.Machines

/-!
# Actual pivot row and column exchange regressions

The diagnostic executes every ordered pivot pair of a small packed matrix, including equal
indices. Only scalar copy is provided by the backend. Source words, output offsets, sentinels,
shape, tape position and the scoped temporary are checked independently of the word specs.
-/

set_option linter.hashCommand false

open NLAlib.Ops NLAlib.Ops.Tools

namespace NLAlibTools.LUPivotSwapSmoke

private def interpreter : Interp ScalarOp Empty Float :=
  Interp.ofFns fun op => if op == .copy then floatMachine.fn op else
    { floatMachine.fn op with fn := fun _ _ _ => none }

private def check (n k r : ℕ) (columns : Bool) : Bool := Id.run do
  let routine : Routine ScalarOp Empty := if columns then NLAlib.LU.swapColumns
    else NLAlib.LU.swapRows
  let words := (List.range (n * n)).map fun i => Float.ofNat (i + 1)
  let input := vals ([191, 193] ++ words ++ [197])
  let initial : Mem Float := ⟨[input], 13⟩
  let some final := NLAlib.Ops.eval interpreter (fun _ _ => 0) routine.body
    (Env.frame [n, k, r] [(0, 2), (0, 2)]) initial | return false
  let some output := final.store.readBlock 0 2 (n * n) | return false
  let expected := (List.range (n * n)).map fun q =>
    let i := q % n
    let j := q / n
    let swap := fun a => if a == k then r else if a == r then k else a
    words.getD (if columns then swap j * n + i else j * n + swap i) 0
  return output == expected && final.pos == 13 && final.store.length == 1 &&
    final.store.len 0 == input.length && final.store.get 0 0 == some 191 &&
    final.store.get 0 1 == some 193 && final.store.get 0 (2 + n * n) == some 197

#guard check 1 0 0 false
#guard check 1 0 0 true
#guard check 2 0 1 false
#guard check 2 0 1 true
#guard check 3 0 0 false
#guard check 3 0 0 true
#guard check 3 0 1 false
#guard check 3 0 1 true
#guard check 3 0 2 false
#guard check 3 0 2 true
#guard check 3 1 1 false
#guard check 3 1 1 true
#guard check 3 1 2 false
#guard check 3 1 2 true
#guard check 3 2 2 false
#guard check 3 2 2 true

end NLAlibTools.LUPivotSwapSmoke
