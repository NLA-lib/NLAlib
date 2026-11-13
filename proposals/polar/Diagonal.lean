import NLAlib.Matrix.Computation.KernelContracts
import NLAlib.Computation.Exact

/-! A one-word matrix diagonal shift for the proposed polar Horner tree. -/

open NLAlib NLAlib.Computation NLAlib.Computation.Builder

namespace Proposal.Polar

/-- Add one coefficient to all diagonal entries, preserving the off-diagonal entries. -/
def addDiagonal {VB VI : Type} (n : IExp VI) (poly coeff : VB) (offset : IExp VI) :
    Builder Unit Unit VB VI Unit :=
  forRange n fun j =>
    ins (.bin () .add ⟨poly, .var j * (n + 1)⟩ ⟨poly, .var j * (n + 1)⟩ ⟨coeff, offset⟩)

theorem oneWordHolds_iff {K : Type} {l n : ℕ} (s : Store Unit K) (b : ℕ)
    (A : Matrix (Fin l) (Fin n) K) :
    realLayout.Holds s () b 0 A ↔
      ∀ (i : Fin l) (j : Fin n), s.read () b (i + l*j) = some (A i j) := by
  constructor
  · intro h i j
    simpa [realLayout] using h i j (0 : Fin 1)
  · intro h i j t
    change Fin 1 at t
    have ht : t = 0 := Subsingleton.elim _ _
    simpa [ht, realLayout] using h i j

private theorem packed_diag_inj {n : ℕ} (i j k : Fin n) (h : i.val + n*j = k * (n+1)) :
    i = k ∧ j = k := by
  have h' : i.val + n*j = k + n*k := h.trans (by ring)
  have h₁ := congrArg (· % n) h'
  have h₂ := congrArg (· / n) h'
  constructor
  · exact Fin.ext (by simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt] using h₁)
  · exact Fin.ext (by simpa [Nat.add_mul_div_left, Nat.div_eq_of_lt, Fin.pos i] using h₂)

/-- Total and liberal specifications of the actual in-place shift, including its footprint. -/
theorem spec_addDiagonal {K C : Type} [RCLike K] [AddMonoid C] (md : Mode)
    (I : Interp Unit Unit K C) (hs : I.sem = exactSem) (n poly coeff : ℕ) (hpc : poly ≠ coeff)
    (offset : IExp ℕ) (A : Matrix (Fin n) (Fin n) K) (z : K) :
    RoutineSpec md I (fun st => realLayout.Holds st.store () poly 0 A ∧
      st.store.read () coeff offset.eval = some z)
      (addDiagonal (.const n) poly coeff offset) [matBlock poly 0 n n 1] fun st out =>
      realLayout.Holds out.store () poly 0 (A + z • (1 : Matrix (Fin n) (Fin n) K)) ∧
        PosKept st out := by
  let Inv (st₀ : St Unit K C) (j : ℕ) (st : St Unit K C) : Prop :=
    (∀ (r s : Fin n), st.store.read () poly (r + n*s) =
      some (if r = s ∧ r.val < j then A r s + z else A r s)) ∧
      st.store.read () coeff offset.eval = some z ∧ PosKept st₀ st
  apply (RoutineSpec.forRange_const [matBlock poly 0 n n 1] Inv ?_ ?_).conseq
    (fun _ h => h) (fun _ h => h)
  · intro st out _ ho
    refine ⟨(oneWordHolds_iff _ _ _).mpr fun i j => ?_, ho.2.2⟩
    by_cases h : i = j
    · subst j
      simpa [Matrix.one_apply, i.isLt] using ho.1 i i
    · simpa [h, Matrix.one_apply] using ho.1 i j
  · intro st hst
    exact ⟨by simpa using (oneWordHolds_iff _ _ _).mp hst.1, hst.2, rfl⟩
  · intro st₀ _ k hk
    let v : Fin n := ⟨k, hk⟩
    let e : IExp ℕ := .var k * (.const n + 1)
    have eval : e.eval = k*(n+1) := rfl
    change k < n at hk
    have hn : k*(n+1)+1 ≤ n*n := by nlinarith [Nat.mul_le_mul_right n hk]
    have writeSpec := RoutineSpec.ins (spec_bin (m := md) (I := I) (p := ())
      (op := .add) (dst := ⟨poly,e⟩) (x := ⟨poly,e⟩) (y := ⟨coeff,offset⟩)
      (a := A v v) (b := z) (v := A v v + z) (by rw [hs]; rfl))
    intro st hst
    have hv : st.store.read () poly e.eval = some (A v v) := by
      have eq : k*(n+1) = k + n*k := by ring
      simpa [v, eval, eq] using hst.1 v v
    refine writeSpec.wp_run ⟨hv, hst.2.1, Mode.needs_of ?_ md⟩ fun out hm ho => ?_
    · intro j hj
      have : j = 0 := by omega
      subst j
      simpa using Store.exists_getElem?_shape_of_read_eq_some hv
    refine ⟨hm.of_sub (fun x hx => ?_), ?_, ?_, ho.2.2.trans hst.2.2⟩
    · obtain rfl := List.mem_singleton.mp hx
      exact ⟨_, List.mem_cons_self, rfl, Nat.zero_le _, by simpa [matBlock, eval] using hn⟩
    · intro r s
      by_cases hr : r = v ∧ s = v
      · rcases hr with ⟨rfl,rfl⟩
        have eq : k*(n+1) = k+n*k := by ring
        simpa [v, eq, eval] using ho.1
      · have hloc : r.val+n*s ≠ k*(n+1) := fun h => hr (packed_diag_inj r s v h)
        have framed := hm.2 () poly (r+n*s) (by
          intro x hx
          obtain rfl := List.mem_singleton.mp hx
          apply blockDisjoint_iff.mpr
          dsimp only
          rw [eval]
          omega)
        rw [framed, hst.1]
        by_cases hrs : r = s
        · subst s
          have : r.val ≠ k := fun he => hr ⟨Fin.ext he, Fin.ext he⟩
          by_cases ht : r.val < k <;> simp [ht, show (r.val < k+1) ↔ (r.val < k) by omega]
        · simp [hrs]
    · exact (hm.2 () coeff offset.eval (by
          intro x hx
          obtain rfl := List.mem_singleton.mp hx
          exact blockDisjoint_of_fst_ne (Ne.symm hpc))).trans hst.2.1

end Proposal.Polar
