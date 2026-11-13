import proposals.polar.Horner
import NLAlibTools.Float

/-! Executable examples for the proposed Horner tree. All test outputs are small integers
represented exactly by Float. The interpreter supplies one dense matrix-product kernel. -/

open NLAlib NLAlib.Computation

namespace Proposal.Polar.Smoke

private def denseMM : List ℕ → List (Array Float) → Option (List (Array Float))
  | [l, m, n], [x, y] => some [Array.ofFn fun t : Fin (l*n) =>
      (List.range m).foldl (fun a j =>
        a + x[(t : ℕ) % l + l*j]! * y[j + m*((t : ℕ) / l)]!) 0]
  | _, _ => none

private def run (m n d k : ℕ) (rom coeff : Array Float) : Option (Array Float × ℕ) := do
  let interp := { NLAlibTools.floatInterp #[] [] with
    rom := fun i => rom[i]?
    romSize := fun _ => rom.size
    charge := fun op => (OpKind.kernelWeight (fun _ => 1) op, 0, 0) }
  let machine := interp.withKernel () denseMM (mmShape (realLayout (K := Float)))
  let st ← horner.compiled.exec machine m ![n,d,k]
    (NLAlibTools.initState [Array.replicate (m*n) none, coeff.map some])
  return (← st.store.readBlock () 0 0 (m*n), st.cnt.1)

/- Zero stages copy a genuinely rectangular input and use zero matrix products. -/
#guard run 3 2 2 0 #[1,3,0,2,-1,1] #[] == some (#[1,3,0,2,-1,1], 0)

/- A nondiagonal Gram, two stages with different coefficients, and a zero highest coefficient. -/
#guard run 3 2 0 2 #[1,3,0,2,-1,1] #[2,1,2,0] == some (#[20,74,-2,30,-22,16], 4)

/- Degree two with a signed inner coefficient. -/
#guard run 1 2 1 1 #[1,2] #[1,-1,1] == some (#[21,42], 3)

/- Degree three checks both passes through the inner Horner loop and reverse indexing. -/
#guard run 1 1 2 1 #[2] #[1,2,3,4] == some (#[626], 4)

/- The zero-row and zero-column shapes both execute the declared kernel calls. -/
#guard run 0 2 0 1 #[] #[1,1] == some (#[], 2)
#guard run 2 0 0 1 #[] #[1,1] == some (#[], 2)

end Proposal.Polar.Smoke
