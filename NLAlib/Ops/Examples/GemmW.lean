/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Examples.Gemm

/-!
# Test case: the matrix product in the logic layer

The certificate of `NLAlib.Ops.Examples.gemm` against `gemmRel`, proved with the relational 2-D
fill rule: `C` is the layout of `Cᵀ` by columns, one `step` per entry.

## Main results

* `NLAlib.Ops.Examples.gemm_spec_w`: the certificate (the statement of `gemm_spec`).
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} [Has Blas1Op Op] [Inhabited K]

/-- **The certificate of `gemm`**, by the relational 2-D fill rule. -/
theorem gemm_spec_w {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {J : Interp Op Tst K}
    (hJ : IsBlas1 dec ε ok J) :
    (gemmImpl (Op := Op) (Tst := Tst)).Meets J .total
      ((gemmRel dec ε.dot).spec (GemmOperands ok)) := by
  cert_intro [m, n, p] (A, B) → (C) reads (as, bs)
  refine Writes.mono (writes_fillRel₂ ⟨C.1, C.2, p, m, p⟩ le_rfl rfl (fun _ => rfl)
    (fun j i x => IsDotErr dec (ε.dot n) n (fun k => vec as (i * n + k))
      (fun k => vec bs (j * n + k)) x) (fun _ => μ.pos) rfl fun i hi j hj m₁ hfr _ hpos => ?_)
    ((MatLayout.fp_le_inBlock le_rfl).trans (by fp_sub)) fun m' _ ⟨⟨Cm, hC, hR⟩, hpos⟩ => ?_
  · dsimp only at hi hj
    step hJ.dot as m₂ hfr₂ ⟨hpos₂, v, hv, hrel⟩
    exact ⟨⟨v, by simpa [MatLayout.cell, Nat.add_assoc] using hv,
      hrel.congr (fun k hk => vec_drop_take hk) fun k hk => vec_drop_take hk⟩,
      by simp [hpos₂, hpos]⟩
  · obtain ⟨cs, hcs, -, hcC⟩ := hC.readBlock rfl
    exact ⟨by simp [hpos], [cs], Mem.readBlocks_of_cons hcs rfl,
      fun i hi j hj => by rw [hcC j hj i hi]; exact hR j hj i hi⟩

end NLAlib.Ops.Examples
