/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.RCLikeBlas
public import NLAlib.Ops.Logic.Tactic

/-!
# Real decoded contracts from exact Hermitian vector operations

On real words conjugation is the identity. The functional Hermitian vector contracts therefore
supply the ordinary exact decoded BLAS contracts. Their spatial admission follows from actual
readable operands and output capacity; malformed operand lists are never assumed admissible.

## Main results

* `NLAlib.Ops.RCLikeBlas.IsExact.toExactBlas1` transfers the six exact real contracts.
-/

@[expose] public section

namespace NLAlib.Ops.RCLikeBlas

private def realRelation : Blas1Op → BlockRel ℝ
  | .sum => sumExactRel id
  | .dot => dotExactRel id
  | .axpy => axpyExactRel id
  | .nrm2 => nrm2ExactRel id
  | .scal => scalExactRel id
  | .copy => copyRel

private def realAdmission : Blas1Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop
  | .axpy | .scal => InPlace (fun _ => True)
  | _ => OutApart (fun _ => True)

private theorem admissible_of_read (o : Blas1Op) (d : List ℕ)
    (ins outs : List (ℕ × ℕ)) (m : Mem ℝ) (xs : List (List ℝ))
    (ha : realAdmission o d ins outs)
    (hr : m.readBlocks ins ((functions (𝕜 := ℝ) o).inLens d) = some xs)
    (hz : m.Room outs ((functions (𝕜 := ℝ) o).outLens d)) : admissible o d ins outs := by
  have hzlen : outs.length = 1 := by cases o <;> exact hz.length_eq
  obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hzlen
  cases o with
  | sum | nrm2 =>
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp ((Mem.length_of_readBlocks hr).trans rfl)
    exact Fp.disj_inBlock_of_ne (ha.2 x (by simp) z (by simp)).symm
  | dot =>
    obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp ((Mem.length_of_readBlocks hr).trans rfl)
    exact ⟨Fp.disj_inBlock_of_ne (ha.2 x (by simp) z (by simp)).symm,
      Fp.disj_inBlock_of_ne (ha.2 y (by simp) z (by simp)).symm⟩
  | axpy =>
    obtain ⟨a, x, y, rfl⟩ := List.length_eq_three.mp ((Mem.length_of_readBlocks hr).trans rfl)
    have he : z = y := by simpa [realAdmission, InPlace] using ha.2.1
    subst z
    exact ⟨Fp.disj_inBlock_of_ne (ha.2.2 a (by simp) y (by simp)),
      Or.inl (Fp.disj_inBlock_of_ne (ha.2.2 x (by simp) y (by simp))), Or.inr rfl⟩
  | scal =>
    obtain ⟨a, x, rfl⟩ := List.length_eq_two.mp ((Mem.length_of_readBlocks hr).trans rfl)
    have he : z = x := by simpa [realAdmission, InPlace] using ha.2.1
    subst z
    exact ⟨Fp.disj_inBlock_of_ne (ha.2.2 a (by simp) x (by simp)), Or.inr rfl⟩
  | copy =>
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp ((Mem.length_of_readBlocks hr).trans rfl)
    exact Or.inl (Fp.disj_inBlock_of_ne (ha.2 x (by simp) z (by simp)))

private theorem getD_eq_vec (xs : List ℝ) {i : ℕ} (hi : i < xs.length) :
    xs.getD i 0 = vec xs i := by
  simp only [vec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem values_real (o : Blas1Op) (d : List ℕ) (w : List ℝ) (xs : List (List ℝ))
    (hlen : xs.map List.length = (functions (𝕜 := ℝ) o).inLens d) :
    ∃ ys, (functions o).fn d w xs = some ys ∧
      ys.map List.length = (realRelation o).outLens d ∧ (realRelation o).rel d xs w ys := by
  have hc := congrArg List.length hlen
  cases o with
  | sum =>
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (by simpa [functions] using hc)
    refine ⟨[[∑ i : Fin (d.headD 0), x.getD i 0]], rfl, rfl, ?_⟩
    have hx : x.length = d.headD 0 := by simpa [functions] using hlen
    change (∑ i : Fin (d.headD 0), x.getD i 0) = ∑ i ∈ Finset.range (d.headD 0), vec x i
    calc
      _ = ∑ i ∈ Finset.range (d.headD 0), x.getD i 0 := Fin.sum_univ_eq_sum_range _ _
      _ = _ := Finset.sum_congr rfl fun i hi => getD_eq_vec x (by simpa [hx] using hi)
  | dot =>
    obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp (by simpa [functions] using hc)
    refine ⟨[[dot (d.headD 0) x y]], rfl, rfl, ?_⟩
    have hx : x.length = d.headD 0 := by
      simpa [functions] using congrArg (fun ns => ns.headD 0) hlen
    have hy : y.length = d.headD 0 := by
      simpa [functions] using congrArg (fun ns => ns.getD 1 0) hlen
    change dot (d.headD 0) x y = ∑ i ∈ Finset.range (d.headD 0), vec x i * vec y i
    simp only [dot, star_trivial]
    calc
      _ = ∑ i ∈ Finset.range (d.headD 0), x.getD i 0 * y.getD i 0 :=
        Fin.sum_univ_eq_sum_range _ _
      _ = _ := Finset.sum_congr rfl fun i hi => by
        rw [getD_eq_vec x (i := i) (by simpa [hx] using hi),
          getD_eq_vec y (i := i) (by simpa [hy] using hi)]
  | axpy =>
    obtain ⟨a, x, y, rfl⟩ := List.length_eq_three.mp (by simpa [functions] using hc)
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (by
      simpa [functions] using congrArg (fun ls => ls.headD 0) hlen)
    refine ⟨[List.ofFn fun i : Fin (d.headD 0) => y.getD i 0 + a * x.getD i 0],
      rfl, by simp [realRelation, axpyExactRel, axpyRel], ?_⟩
    have hx : x.length = d.headD 0 := by
      simpa [functions] using congrArg (fun ns => ns.getD 1 0) hlen
    have hy : y.length = d.headD 0 := by
      simpa [functions] using congrArg (fun ns => ns.getD 2 0) hlen
    intro i hi
    change vec (List.ofFn _) i = vec y i + a * vec x i
    simp only [vec, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
      Option.getD_some]
    change y.getD i 0 + a * x.getD i 0 = vec y i + a * vec x i
    exact congrArg₂ (fun u v : ℝ => u + a * v)
      (getD_eq_vec y (i := i) (by omega)) (getD_eq_vec x (i := i) (by omega))
  | nrm2 =>
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (by simpa [functions] using hc)
    refine ⟨[[Real.sqrt (dot (d.headD 0) x x)]], rfl, rfl, ?_⟩
    have hx : x.length = d.headD 0 := by simpa [functions] using hlen
    change Real.sqrt (dot (d.headD 0) x x) =
      Real.sqrt (∑ i ∈ Finset.range (d.headD 0), vec x i ^ 2)
    congr 1
    simp only [dot, star_trivial]
    calc
      _ = ∑ i ∈ Finset.range (d.headD 0), x.getD i 0 * x.getD i 0 :=
        Fin.sum_univ_eq_sum_range _ _
      _ = _ := Finset.sum_congr rfl fun i hi => by
        rw [getD_eq_vec x (i := i) (by simpa [hx] using hi), pow_two]
  | scal =>
    obtain ⟨a, x, rfl⟩ := List.length_eq_two.mp (by simpa [functions] using hc)
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (by
      simpa [functions] using congrArg (fun ls => ls.headD 0) hlen)
    refine ⟨[List.ofFn fun i : Fin (d.headD 0) => x.getD i 0 / a],
      rfl, by simp [realRelation, scalExactRel, scalRel], ?_⟩
    have hx : x.length = d.headD 0 := by
      simpa [functions] using congrArg (fun ns => ns.getD 1 0) hlen
    intro _ i hi
    change vec (List.ofFn _) i = vec x i / a
    simp only [vec, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
      Option.getD_some]
    change x.getD i 0 / a = vec x i / a
    exact congrArg (fun u : ℝ => u / a) (getD_eq_vec x (i := i) (by omega))
  | copy =>
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (by simpa [functions] using hc)
    exact ⟨[x], rfl, hlen, rfl⟩

variable {Op Tst : Type} [Has Blas1Op Op] {I : Interp Op Tst ℝ}

private theorem meets_real (hI : IsExact I) (o : Blas1Op) :
    I.Meets .total (Has.inj o) ((realRelation o).spec (realAdmission o)) := by
  refine (hI o).meets_rel_of_pre ?_ (by cases o <;> rfl) (by cases o <;> rfl)
    (fun _ => by cases o <;> rfl) (fun _ => by cases o <;> rfl)
    (fun _ => by cases o <;> rfl) ?_
  · intro d ins outs m xs ha hr hz
    exact admissible_of_read o d ins outs m xs ha
      (by cases o <;> exact hr)
      (by cases o <;> exact hz)
  · intro d w xs m ins outs _ _ _ hr _
    apply values_real o d w xs
    have h := m.map_length_of_readBlocks hr
    cases o <;> exact h

/-- Exact Hermitian vector primitives on real words satisfy the six ordinary decoded BLAS
contracts. Reductions use separate output buffers; maps use their declared in-place operands.
Input reads and output capacity provide the required operand shapes, including empty vectors. -/
theorem IsExact.toExactBlas1 (hI : IsExact I) : IsExactBlas1 id (fun _ => True) I :=
  ⟨meets_real hI .sum, meets_real hI .dot, meets_real hI .axpy,
    meets_real hI .nrm2, meets_real hI .scal, meets_real hI .copy⟩

end NLAlib.Ops.RCLikeBlas
