/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Alg
public import NLAlib.Ops.Logic.Tactic

/-!
# Literal initialization of Lanczos output tails

Every output cell is initialized by an actual scalar literal call. The certificate records the
machine words themselves, so exact and rounded model proofs can decode the same initialized
blocks as zero. Empty blocks are included.

## Main results

* `NLAlib.Krylov.Lanczos.zero_writes` fills one block and proves its readback.
* `NLAlib.Krylov.Lanczos.zero_spec` exposes the same fill as a total block certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- A zero fill stores precisely the machine's literal-zero word in every requested cell. -/
theorem zero_writes {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I)
    {τ : Tape K} {μ : Mem K} {n : ℕ} {q : ℕ × ℕ}
    (hl : q.1 < μ.store.length) (hz : q.2 + n ≤ μ.store.len q.1) :
    Writes .total I τ zero (Env.frame [n] [q]) (Store.inBlock q.1 q.2 n)
      (fun μ' => μ'.pos = μ.pos ∧
        μ'.store.readBlock q.1 q.2 n = some (List.replicate n (M.lit 0))) μ := by
  refine (writes_fill rfl (fun _ => M.lit 0) (fun _ => μ.pos) rfl ?_).mono le_rfl ?_
  · intro i hi μ₁ hfr hprev hpos
    step (hS (.lit 0)) as μ₂ hfr₂ ⟨hpos₂, v, hv, rfl⟩
    exact ⟨hv, hpos₂.trans hpos⟩
  · intro μ' _ ⟨hvec, hpos⟩
    exact ⟨hpos, by simpa using Store.holdsVec_iff_readBlock.mp hvec⟩

/-- The word-level fill relation, independent of any mathematical decoding model. -/
@[simps (attr := storeNF)]
def zeroRel (v : K) : BlockRel K where
  nd := 1
  inLens _ := []
  outLens d := [d.headD 0]
  rel d _ _ Y := Y = [List.replicate (d.headD 0) v]

/-- The literal fill succeeds for every admitted output block under its scalar contract. -/
theorem zero_spec {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I) :
    (zeroImpl (Op := Op) (Tst := Tst)).Triple I .total ((zeroRel (M.lit 0)).spec AnyOperands) := by
  cert_intro [n] () → (q) reads ()
  have hq : q.1 < μ.store.length := by simpa only [Mem.live_cons, Mem.live_nil, and_true] using hl
  have hqn : q.2 + n ≤ μ.store.len q.1 := by
    simpa only [Mem.room_cons, Mem.room_nil, and_true] using hz
  refine (zero_writes hS hq hqn).mono (by fp_sub) ?_
  rintro μ' _ ⟨hpos, hread⟩
  exact ⟨by simpa using hpos, [List.replicate n (M.lit 0)],
    Mem.readBlocks_of_cons hread rfl, rfl⟩

end NLAlib.Krylov.Lanczos
