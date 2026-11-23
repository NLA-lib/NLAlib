/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.TriangularSolve.Substitution
public import NLAlib.Ops.Catalog.Tagged

/-!
# The scalar kernels of iterative refinement

The residual, the update and the cast of a vector between two precisions, as routines over
scalar operations. Each is generic over the signature, so it can be run at a precision tag with
the instance `NLAlib.Ops.Tagged.has`, as three-precision refinement requires.

## Main definitions

* `NLAlib.LinearSystems.Refinement.residualRows`: $\mathbf{r} := \mathbf{b} - \mathbf{A}\mathbf{x}$,
  row by row, with $\mathbf{A}$ stored by columns.
* `NLAlib.LinearSystems.Refinement.addInPlace`: $\mathbf{x} := \mathbf{x} + \mathbf{d}$.
* `NLAlib.LinearSystems.Refinement.castLoop`: the entrywise cast between two precisions.

## Main results

* `NLAlib.LinearSystems.Refinement.residualRows_meets`: each row is a rounded accumulation.
* `NLAlib.LinearSystems.Refinement.addInPlace_meets`: each entry is a rounded sum.
* `NLAlib.LinearSystems.Refinement.castLoop_meets`: the entries are the casts of the input.
-/

@[expose] public section

namespace NLAlib.LinearSystems.Refinement

open Ops Computation TriangularSolve

variable {K Op Tst : Type}

section Scalar

variable [Has ScalarOp Op]

/-- **The residual, row by row**: $r_i$ starts at $b_i$, and the products $a_{ij} x_j$ are
subtracted in order of $j$, in the cell of $r_i$; one scratch cell holds the product. -/
def residualRows : Routine Op Tst := routine% [n] (A : n * n, b : n, x : n) → (r : n) {
  let t ← alloc 1;
  for i < n {
    call (Has.inj ScalarOp.copy) [] (b[i]) → (r[i]);
    for j < n {
      call (Has.inj ScalarOp.mul) [] (A[j * n + i], x[j]) → (t);
      call (Has.inj ScalarOp.sub) [] (r[i], t) → (r[i])
    }
  }
}

/-- **The update in place**: $x_i := x_i + d_i$. -/
def addInPlace : Routine Op Tst := routine% [n] (d : n, x : n) → (x) {
  for i < n {
    call (Has.inj ScalarOp.add) [] (x[i], d[i]) → (x[i])
  }
}

variable [Inhabited K]

/-- Each entry written is the last value of a row trace of the residual, at unit roundoff $u$,
on the decoded matrix, right-hand side and iterate. -/
def residualRowsSpec (u : ℝ) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (As, bs, xs) → (rs) ensures
    ∀ i < n, ∃ s, IsSubstRowTrace (fun _ => RelErr u) (fun i j => dec (vec As (j * n + i)))
      (fun i => dec (vec bs i)) (fun j => dec (vec xs j)) i n s ∧ s n = dec (vec rs i)

/-- Each entry written is the sum of the two entries read, with relative error at most $u$. -/
def addInPlaceSpec (u : ℝ) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (ds, xs) → (xs') ensures
    ∀ i < n, |dec (vec xs' i) - (dec (vec xs i) + dec (vec ds i))| ≤
      u * |dec (vec xs i) + dec (vec ds i)|

/-- The rows below `i` of the residual are row traces whose last values are the words `W`. -/
def ResidualPrefix (u : ℝ) (dec : K → ℝ) (n : ℕ) (As bs xs : List K) (W : ℕ → K) (i : ℕ) : Prop :=
  ∀ l < i, ∃ s, IsSubstRowTrace (fun _ => RelErr u) (fun i j => dec (vec As (j * n + i)))
    (fun i => dec (vec bs i)) (fun j => dec (vec xs j)) l n s ∧ s n = dec (W l)

/-- Writing the accumulated word of row `i` extends the prefix of the residual. -/
theorem ResidualPrefix.succ {M : Machine K} {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M)
    {n i : ℕ} {As bs xs : List K} {W : ℕ → K} (h : ResidualPrefix u dec n As bs xs W i) :
    ResidualPrefix u dec n As bs xs (Function.update W i
      (mulSubWord M (fun k => vec As (k * n + i)) (vec xs) (vec bs i) n)) (i + 1) := by
  intro l hl
  rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
  · obtain ⟨s, hs, he⟩ := h l hl
    exact ⟨s, hs, by rw [he, Function.update_of_ne (by omega)]⟩
  · exact ⟨_, isSubstRowTrace_mulSubWord hM (A := fun k => vec As (k * n + l)) (X := vec xs)
      (v := vec bs l) (fun _ _ => rfl) (fun _ _ => rfl) rfl, by simp only [Function.update_self]⟩

/-- The residual meets its specification under the standard model. -/
theorem residualRows_meets {M : Machine K} {I : Interp Op Tst K} {u : ℝ} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : StdModel u dec M) :
    (residualRows (Op := Op) (Tst := Tst)).Meets I (residualRowsSpec u dec) := by
  routine_intro [n] (A, b, x, r) reads (As, bs, xs)
  change Writes .total I τ _ (Env.frame [n] [A, b, x, r]) (Fp.blocks [r] [n]) _ m
  obtain ⟨hlA, hlb, hlx, hlr⟩ := hl
  alloc as t
  have hAs₁ := Store.Below.readBlock_of hbelow_t hlA hAs
  have hbs₁ := Store.Below.readBlock_of hbelow_t hlb hbs
  have hxs₁ := Store.Below.readBlock_of hbelow_t hlx hxs
  have hrlen : r.2 + n ≤ s_t.len r.1 := by rw [hbelow_t.len_of r.1 hlr]; exact hroom
  have htlen : 0 < s_t.len t := Nat.lt_of_lt_of_eq Nat.one_pos ht.symm
  refine Writes.mono (writes_loop (N := n) (by rfl)
    (fun _ => Store.inBlock r.1 r.2 n ⊔ Store.inBlock t 0 1) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ ∃ W, CellsHold m'.store r.1 r.2 i W ∧
      ResidualPrefix u dec n As bs xs W i)
    ⟨rfl, fun _ => default, fun _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩
    ?_) ?_ ?_
  · intro i hi m₁ hfr ⟨hpos₁, W, hW, hpre₁⟩
    have hoff : ∀ {y : ℕ × ℕ}, y.1 ≠ r.1 → y.1 ≠ t →
        ¬ (Store.inBlock r.1 r.2 n ⊔ Store.inBlock t 0 1) y.1 y.2 := by
      rintro y h₁ h₂ (⟨h, -⟩ | ⟨h, -⟩)
      · exact h₁ h
      · exact h₂ h
    have hbi : m₁.store.get b.1 (b.2 + i) = some (vec bs i) :=
      (hfr.get_eq (hoff (y := (b.1, b.2 + i)) hbr (Nat.ne_of_lt hlb))).trans
        (Store.get_of_readBlock hbs₁ hi default)
    step (hI .copy) as m₂ hfr₂ ⟨hpos₂, v, hv, rfl⟩
    have hkeep : ∀ {y : ℕ × ℕ} {a : K}, y.1 ≠ r.1 → y.1 ≠ t →
        s_t.get y.1 y.2 = some a → m₂.store.get y.1 y.2 = some a := by
      intro y a h₁ h₂ hy
      rw [hfr₂.get_eq (by rintro ⟨h, -⟩; exact h₁ h), hfr.get_eq (hoff h₁ h₂)]
      exact hy
    refine Writes.mono (writes_mulSubLoop (m := m₂) hI (N := n) (by rfl)
      (p := fun k => (A.1, A.2 + k * n + i)) (q := fun k => (x.1, x.2 + k))
      (z := (r.1, r.2 + i)) (w := (t, 0))
      (A := fun k => vec As (k * n + i)) (B := vec xs) (v := vec bs i)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun k hk => hkeep hAr (Nat.ne_of_lt hlA) (get_matrix_entry hAs₁ hk hi))
      (fun k hk => hkeep hxr (Nat.ne_of_lt hlx) (Store.get_of_readBlock hxs₁ hk default))
      hv (Nat.ne_of_lt hlr)
      (fun _ _ e => hAr (by simpa using congrArg Prod.fst e))
      (fun _ _ e => hxr (by simpa using congrArg Prod.fst e))
      (fun _ _ => Nat.ne_of_lt hlA) (fun _ _ => Nat.ne_of_lt hlx)
      (by
        change 0 < m₂.store.len t
        rw [hfr₂.len_eq, hfr.len_eq]
        exact htlen)) ?_
      fun m₃ hfr₃ ⟨hpos₃, hz₃⟩ => ⟨hpos₃.trans (hpos₂.trans hpos₁), _,
        hW.extend ((hfr₂.mono fun _ _ h => Or.inl h).trans hfr₃) (fun o ho => ?_) hz₃,
        hpre₁.succ hM⟩
    · rintro _ _ (⟨rfl, h₁, h₂⟩ | h)
      · have h₁' : r.2 + i ≤ _ := h₁
        have h₂' : _ < r.2 + i + 1 := h₂
        exact Or.inl ⟨rfl, by omega, by omega⟩
      · exact Or.inr h
    · rintro (⟨-, h, -⟩ | ⟨h, -⟩)
      · have h' : r.2 + i ≤ r.2 + o := h
        omega
      · exact Nat.ne_of_lt hlr h
  · fp_sub
  · rintro m' - ⟨hpos, W, hW, hpre₁⟩ s₂ - hB
    refine ⟨hpos, [(List.range n).map W],
      Mem.readBlocks_of_cons (Store.Below.readBlock_of hB hlr hW.readBlock) rfl, fun i hi => ?_⟩
    obtain ⟨s, hs, he⟩ := hpre₁ i hi
    exact ⟨s, hs, by rw [he, vec_map_range W hi]⟩

/-- The update in place meets its specification under the standard model. -/
theorem addInPlace_meets {M : Machine K} {I : Interp Op Tst K} {u : ℝ} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : StdModel u dec M) :
    (addInPlace (Op := Op) (Tst := Tst)).Meets I (addInPlaceSpec u dec) := by
  routine_intro [n] (d, x) reads (ds, xs)
  loop_inv (fun i => Store.inBlock x.1 x.2 i)
    (fun i m' => m'.pos = m.pos ∧ ∃ W, CellsHold m'.store x.1 x.2 i W ∧
      ∀ l < i, |dec (W l) - (dec (vec xs l) + dec (vec ds l))| ≤
        u * |dec (vec xs l) + dec (vec ds l)|)
    with i hi m₁ hfr hP
  case initial =>
    exact ⟨rfl, fun _ => default, fun _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩
  case round =>
    obtain ⟨hpos₁, W, hW, hbd⟩ := hP
    have hxi : m₁.store.get x.1 (x.2 + i) = some (vec xs i) :=
      (hfr.get_eq (by rintro ⟨-, -, h⟩; omega)).trans (Store.get_of_readBlock hxs hi default)
    have hds₁ : m₁.store.readBlock d.1 d.2 n = some ds := by keep
    have hdi : m₁.store.get d.1 (d.2 + i) = some (vec ds i) :=
      Store.get_of_readBlock hds₁ hi default
    step (hI .add) as m₂ hfr₂ ⟨hpos₂, v, hv, rfl⟩
    refine ⟨hpos₂.trans hpos₁, _, hW.extend hfr₂ (fun o ho => ?_) hv, fun l hl => ?_⟩
    · rintro ⟨-, h, -⟩
      omega
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
      · simpa only [Function.update_of_ne (Nat.ne_of_lt hl)] using hbd l hl
      · simpa only [Function.update_self] using hM.add (vec xs l) (vec ds l)
  case exit =>
    rintro m₁ - ⟨hpos₁, W, hW, hbd⟩
    refine ⟨hpos₁, [(List.range n).map W], Mem.readBlocks_of_cons hW.readBlock rfl, ?_⟩
    intro i hi
    simpa only [vec_map_range W hi] using hbd i hi

end Scalar

section Cast

variable {π ρ : Type} [Has (CastOp π ρ) Op]

/-- **The cast of a vector** from the precision `π` to the precision `ρ`, entry by entry. -/
def castLoop (π ρ : Type) [Has (CastOp π ρ) Op] : Routine Op Tst :=
  routine% [m] (x : m) → (y : m) {
    for i < m {
      call (Has.inj (CastOp.cast : CastOp π ρ)) [] (x[i]) → (y[i])
    }
  }

variable [Inhabited K]

/-- The block written is the entrywise image of the block read under the cast `c`. -/
def castLoopSpec (c : K → K) : Routine.Spec K :=
  spec% [m] (xs) → (ys) ensures ys = (List.range m).map fun i => c (vec xs i)

/-- The cast of a vector meets its specification, for a cast that is the function `c`. -/
theorem castLoop_meets {c : K → K} {I : Interp Op Tst K} (hC : IsCast π ρ c I) :
    (castLoop π ρ (Op := Op) (Tst := Tst)).Meets I (castLoopSpec c) := by
  routine_intro [k] (x, y) reads (xs)
  loop_inv (fun _ => Fp.blocks [y] [k])
    (fun i m' => m'.pos = m.pos ∧
      m'.store.readBlock y.1 y.2 i = some ((List.range i).map fun l => c (vec xs l)))
    with i hi m₁ hfr hP
  case round =>
    obtain ⟨hpos₁, hy₁⟩ := hP
    have hxs₁ : m₁.store.readBlock x.1 x.2 k = some xs := by keep
    have hxi : m₁.store.get x.1 (x.2 + i) = some (vec xs i) :=
      Store.get_of_readBlock hxs₁ hi default
    step hC as m₂ hfr₂ ⟨hpos₂, v, hv, rfl⟩
    refine ⟨hpos₂.trans hpos₁, ?_⟩
    rw [List.range_succ, List.map_append, List.map_singleton]
    exact Store.readBlock_succ_of (by keep) hv
  case exit =>
    rintro m₁ - ⟨hpos₁, hy₁⟩
    exact ⟨hpos₁, [(List.range k).map fun l => c (vec xs l)],
      Mem.readBlocks_of_cons hy₁ rfl, rfl⟩

end Cast

end NLAlib.LinearSystems.Refinement
