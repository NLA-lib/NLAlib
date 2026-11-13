/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Preconditioner
public import NLAlib.Ops.Blas.DotFunction

/-!
# Functional computed PCG pairings

The sequential scalar dot kernel depends only on its finite operand vectors. Combining that
functional fact with the numerical dot contract retains both the actual word and its error.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.pairingValue` is the actual scalar-backend pairing.
* `NLAlib.Krylov.CG.HSPCG.Rounded.dot_function_meets` retains its numerical and functional laws.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded

open Ops

/-- The sequential scalar dot kernel on finite real-word vectors, using canonical operand
lists. This is the actual rounded word rather than the exact real inner product. -/
def pairingValue (F : Machine ℝ) {n : ℕ} (r z : Fin n → ℝ) : ℝ :=
  sumSeqF F (fun k => F.mul (vec (List.ofFn r) k) (vec (List.ofFn z) k)) n

/-- A numerical dot contract retaining an additional predicate of its decoded finite
operand vectors and actual output word. -/
@[simps (attr := storeNF)]
def dotEvidenceRel (ε : Blas1Err)
    (Q : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ → Prop) : BlockRel ℝ :=
  { dotRel id ε.dot with rel := fun d X w Y => (dotRel id ε.dot).rel d X w Y ∧
      match X, Y with
      | [xs, zs], [[v]] => Q (d.headD 0) (decv id (d.headD 0) xs) (decv id (d.headD 0) zs) v
      | _, _ => False }

/-- The ordinary numerical dot law supplies the evidence contract with a trivial additional
predicate. The domain and admitted operands are unchanged. -/
theorem dot_trivial_meets {Op Tst : Type} {I : Interp Op Tst ℝ} {o : Op}
    {ε : Blas1Err} {ok : ℕ → Prop}
    (h : I.Meets .total o ((dotRel id ε.dot).spec (OutApart ok))) :
    I.Meets .total o ((dotEvidenceRel ε (fun _ _ _ _ => True)).spec (OutApart ok)) := by
  refine h.mono (fun _ _ _ _ _ hp => hp) ?_
  rintro d ins outs τ m m' _ ⟨X, hread, hroom, Y, hlen, hrel, hm⟩
  refine ⟨X, hread, hroom, Y, hlen, ⟨hrel, ?_⟩, hm⟩
  obtain ⟨x, z, xs, zs, rfl, _, _, rfl⟩ := Mem.readBlocks_two hread
  have hYlen : Y.length = 1 := by
    simpa only [List.length_map, dotRel, List.length_cons, List.length_nil] using
      congrArg List.length hlen
  obtain ⟨ys, rfl⟩ := List.length_eq_one_iff.mp hYlen
  have hyl : ys.length = 1 := (List.cons.inj hlen).1
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hyl
  trivial

/-- A numerical dot contract and the sequential functional kernel describe the same actual
word. The outputs are read back from the shared operation call before the relations combine. -/
theorem dot_function_meets {Op Tst : Type} [Has Blas1Op Op]
    {F : Machine ℝ} {I : Interp Op Tst ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    (hB : I.Meets .total (Has.inj Blas1Op.dot) ((dotRel id ε.dot).spec (OutApart ok)))
    (hD : I.IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn F) (OutApart (fun _ => True))) :
    I.Meets .total (Has.inj Blas1Op.dot)
      ((dotEvidenceRel ε (fun _ r z v => v = pairingValue F r z)).spec (OutApart ok)) := by
  refine hB.and_rel ?_ ?_
  · refine hD.mono ?_ ?_
    · rintro d ins outs τ m ⟨hnd, hadm, hpre⟩
      obtain ⟨hl, ⟨X, hread, _⟩, hz⟩ := hpre rfl
      obtain ⟨x, z, xs, zs, rfl, hx, hz', rfl⟩ := Mem.readBlocks_two hread
      refine ⟨hnd, ⟨trivial, hadm.2⟩, fun _ => ⟨hl, ⟨[xs, zs], ?_, ?_⟩, hz⟩⟩
      · exact Mem.readBlocks_of_cons hx (Mem.readBlocks_of_cons hz' rfl)
      · exact ⟨[[_]], rfl, rfl⟩
    · rintro d ins outs τ m m' _ ⟨X, hread, hroom, Y, hlen, hrel, hm⟩
      obtain ⟨x, z, xs, zs, rfl, hx, hz, rfl⟩ := Mem.readBlocks_two hread
      have hxs := (Store.readBlock_eq_some_iff.mp hx).1
      have hzs := (Store.readBlock_eq_some_iff.mp hz).1
      have hY : Y = [[sumSeqF F (fun k => F.mul (vec xs k) (vec zs k)) (d.headD 0)]] := by
        simpa only [dotSeqFn, BlockFn.rel, BlockFn.of2, Option.map_some, Option.some.injEq]
          using hrel.symm
      subst Y
      refine ⟨[xs, zs], hread, hroom, [[_]], hlen, ?_, hm⟩
      change _ = pairingValue F (decv id (d.headD 0) xs) (decv id (d.headD 0) zs)
      simp only [pairingValue, ofFn_decv hxs, ofFn_decv hzs]
  · intro d ins outs m _ hz
    obtain ⟨z, rfl, _⟩ := Mem.room_one hz
    exact ⟨fun _ _ _ h => h, trivial⟩

end NLAlib.Krylov.CG.HSPCG.Rounded
