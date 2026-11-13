import NLAlib.Computation.RoutineSpec
import NLAlib.Matrix.Computation.KernelContracts

/-! Exact execution of the one-word conjugate-transpose loop used by polar Horner. -/

open NLAlib NLAlib.Computation NLAlib.Computation.Builder
open scoped Matrix

namespace Proposal.Polar

/-- Transpose a column-major rectangular matrix while conjugating each scalar. -/
def adjoint {VB VI : Type} (m n : IExp VI) (X adj : VB) : Builder Unit Unit VB VI Unit :=
  forRange n fun j => forRange m fun i =>
    ins (.un () .conj ⟨adj, .var j + n * .var i⟩ ⟨X, .var i + m * .var j⟩)

/-- Both loops write precisely the entries of the conjugate transpose in one-word layout.
The source and destination buffers are distinct and may have zero entries. -/
theorem routineSpec_adjoint {K C : Type} [RCLike K] [AddMonoid C] (md : Mode)
    (I : Interp Unit Unit K C) (hI : I.sem = exactSem) (m n : IExp ℕ) (X adj : ℕ)
    (hbuf : X ≠ adj) (A : Matrix (Fin m.eval) (Fin n.eval) K) :
    RoutineSpec md I (fun st => realLayout.Holds st.store () X 0 A ∧
        md.Needs (Writable st.store () adj 0 (n.eval * m.eval)))
      (adjoint m n X adj) [matBlock adj 0 n.eval m.eval 1]
      fun st st' => realLayout.Holds st'.store () adj 0 Aᴴ ∧ PosKept st st' := by
  let pre (st : St Unit K C) := realLayout.Holds st.store () X 0 A ∧
    md.Needs (Writable st.store () adj 0 (n.eval * m.eval))
  let fp := [matBlock adj 0 n.eval m.eval 1]
  let inv (st₀ : St Unit K C) (j i : ℕ) (st : St Unit K C) :=
    pre st ∧ PosKept st₀ st ∧ ∀ (a : Fin m.eval) (b : Fin n.eval),
      b.val < j ∨ (b.val = j ∧ a.val < i) →
        st.store.read () adj (b.val + n.eval * a.val) = some (star (A a b))
  let body (j i : ℕ) : Builder Unit Unit ℕ ℕ Unit :=
    ins (.un () .conj ⟨adj, .var j + n * .var i⟩ ⟨X, .var i + m * .var j⟩)
  have entry (st₀ : St Unit K C) (j i : ℕ) (hj : j < n.eval) (hi : i < m.eval) :
      Spec md I (inv st₀ j i) (body j i).run fp fun _ st' => inv st₀ j (i + 1) st' := by
    let a : Fin m.eval := ⟨i, hi⟩
    let b : Fin n.eval := ⟨j, hj⟩
    let val := A a b
    have hop : I.sem.un () .conj val = some (star val) := by rw [hI]; rfl
    have hlt : j + n.eval * i < n.eval * m.eval := Nat.add_mul_lt_mul_of_lt_of_lt hj hi
    have h := (RoutineSpec.ins (spec_un (m := md) (p := ()) (I := I)
      (dst := ⟨adj, .var j + n * .var i⟩) (x := ⟨X, .var i + m * .var j⟩) hop)).spec
    refine (h.with_modifies.sub (fp' := fp) ?_).conseq ?_ (fun _ h => h) ?_
    · intro z hz
      rw [List.mem_singleton.mp hz]
      exact ⟨_, List.mem_cons_self, rfl, Nat.zero_le _,
        by simpa [matBlock, IExp.eval] using hlt⟩
    · intro st hst
      refine ⟨?_, hst.1.2.mono fun hw => hw.of_le (Nat.zero_le _) ?_⟩
      · simpa [realLayout, a, b, val, IExp.eval] using hst.1.1 a b ⟨0, Nat.zero_lt_one⟩
      · simpa [IExp.eval] using hlt
    · intro st st' hst hpost
      have hm := hpost.1
      obtain ⟨hread, _, hpos⟩ := hpost.2
      refine ⟨⟨(readsOnly_entryLayoutHolds realLayout () X 0 A).of_modifies hst.1.1 hm
          (blocksDisjoint_singleton_of_fst_ne (fun z hz => by
            rw [List.mem_singleton.mp hz]; exact hbuf)),
        hst.1.2.mono fun hw => hw.of_modifies hm⟩, hpos.trans hst.2.1, ?_⟩
      intro a' b' hab
      by_cases he : b'.val + n.eval * a'.val = j + n.eval * i
      · obtain ⟨hb, ha⟩ := (Nat.add_mul_eq_add_mul_iff_of_lt b'.2 hj).mp he
        have haa : a' = a := Fin.ext ha
        have hbb : b' = b := Fin.ext hb
        subst a'; subst b'
        exact hread
      · have hprior : b'.val < j ∨ (b'.val = j ∧ a'.val < i) := by
          by_cases h : a'.val = i
          · rcases hab with hb | ⟨hb, _⟩
            · exact Or.inl hb
            · exact (he (by rw [h, hb])).elim
          · omega
        rw [hm.2 () adj _ (by
          intro z hz
          rw [List.mem_singleton.mp hz, blockDisjoint_iff_of_pos Nat.zero_lt_one Nat.zero_lt_one]
          change adj ≠ adj ∨ b'.val + n.eval * a'.val + 1 ≤ j + n.eval * i ∨
            j + n.eval * i + 1 ≤ b'.val + n.eval * a'.val
          omega)]
        exact hst.2.2 _ _ hprior
  have col (st₀ : St Unit K C) (j : ℕ) (hj : j < n.eval) :
      Spec md I (inv st₀ j 0) (forRange m (body j)).run fp fun _ st' => inv st₀ (j + 1) 0 st' := by
    refine ((RoutineSpec.forRange_const (m := md) (I := I) fp
        (fun _ k => inv st₀ j k) (fun _ h => h)
        (fun _ _ k hk => entry st₀ j k hj hk)).spec).conseq (fun _ h => h) (fun _ h => h) ?_
    intro _ _ _ h
    refine ⟨h.1, h.2.1, fun a b hb => h.2.2 a b ?_⟩
    have ha := a.2
    omega
  refine (RoutineSpec.forRange_const (m := md) (I := I) (n := n)
      (body := fun j => forRange m (body j)) (pre := pre) fp
      (fun st₀ j => inv st₀ j 0) (fun st h => ⟨h, rfl, by simp⟩)
      (fun st₀ _ j hj => col st₀ j hj)).conseq (fun _ h => h) (fun _ h => h) ?_
  intro st₀ st _ h
  refine ⟨?_, h.2.1⟩
  intro b a t
  have ht : t.val = 0 := by exact Nat.lt_one_iff.mp t.isLt
  simpa [realLayout, ht, Matrix.conjTranspose_apply] using h.2.2 a b (Or.inl b.isLt)

end Proposal.Polar
