import proposals.polar.Horner

/-! Execution of the descending square-matrix Horner loop in the polar iteration. -/

open NLAlib NLAlib.Computation NLAlib.Computation.Builder

namespace Proposal.Polar

private theorem gramHorner_suffix_succ {K : Type} [RCLike K] {n d j : ℕ} (hj : j < d)
    (c : ℕ → ℝ) (G : Matrix (Fin n) (Fin n) K) :
    G * gramHorner (j + 1) (fun i => c (d - j + i)) G + (c (d - 1 - j) : K) • 1 =
      gramHorner ((j + 1) + 1) (fun i => c (d - (j + 1) + i)) G := by
  rw [gramHorner, add_comm]
  have hshift : (fun i => c (d - (j + 1) + (i + 1))) = fun i => c (d - j + i) := by
    funext i
    congr 1
    omega
  rw [hshift, Nat.add_zero, show d - (j + 1) = d - 1 - j by omega,
    RCLike.real_smul_eq_coe_smul (K := K)]
  simp

/-- The inner loop accumulates the successive highest-degree coefficient suffixes and
leaves the complete Gram polynomial in the polynomial buffer. -/
theorem spec_inner {K C : Type} [RCLike K] [Inhabited K] [AddMonoid C]
    (I : Interp Unit Unit K C) (hs : I.sem = exactSem)
    (hmm : IsMatMulKernel I () realLayout (exactMM (𝕜 := K))) (n d stage : ℕ)
    (G : Matrix (Fin n) (Fin n) K) (c : ℕ → ℝ) :
    RoutineSpec .total I (fun st => realLayout.Holds st.store () 3 0 G ∧
      realLayout.Holds st.store () 4 0 (gramHorner 1 (fun i => c (d + i)) G) ∧
      (∀ j ≤ d + 1, st.store.read () 1 (stage * (d + 2) + j) = some (c j : K)) ∧
      Writable st.store () 4 0 (n * n) ∧ Writable st.store () 5 0 (n * n))
      (inner (.const n) (.const d) (.var stage * (.const d + 2)) 1 3 4 5)
      [matBlock 4 0 n n 1, matBlock 5 0 n n 1]
      fun _ out => realLayout.Holds out.store () 4 0 (gramHorner (d + 1) c G) := by
  let fp := [matBlock 4 0 n n 1, matBlock 5 0 n n 1]
  let suffix (j : ℕ) := gramHorner (j + 1) (fun i => c (d - j + i)) G
  let keep (s : Store Unit K) : Prop := realLayout.Holds s () 3 0 G ∧
    (∀ q ≤ d + 1, s.read () 1 (stage * (d + 2) + q) = some (c q : K)) ∧
    Writable s () 4 0 (n * n) ∧ Writable s () 5 0 (n * n)
  have frame {s s' : Store Unit K} (hk : keep s) (hm : Modifies fp s s') : keep s' := by
    refine ⟨(readsOnly_entryLayoutHolds realLayout () 3 0 G).of_modifies hk.1 hm
      (blocksDisjoint_singleton_of_fst_ne (fun x hx => ?_)), ?_,
      hk.2.2.1.of_modifies hm, hk.2.2.2.of_modifies hm⟩
    · rcases List.mem_cons.mp hx with rfl | h
      · simp [matBlock]
      · rw [List.mem_singleton.mp h]; simp [matBlock]
    · intro q hq
      rw [hm.2 () 1 _ (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | h
        · exact blockDisjoint_of_fst_ne (by simp [matBlock])
        · rw [List.mem_singleton.mp h]; exact blockDisjoint_of_fst_ne (by simp [matBlock]))]
      exact hk.2.1 q hq
  let inv (j : ℕ) (st : St Unit K C) := keep st.store ∧
    realLayout.Holds st.store () 4 0 (suffix j)
  let body (j : ℕ) : Builder Unit Unit ℕ ℕ Unit := do
    stmt (.kcall () () [.const n, .const n, .const n] [(3, 0), (4, 0)] [(5, 0)])
    addDiagonal (.const n) 5 1 (.var stage * (.const d + 2) + (.const d - 1 - .var j))
    copyv () 5 0 4 0 (.const n * .const n)
  have step (j : ℕ) (hj : j < d) :
      Spec .total I (inv j) (body j).run fp fun _ st' => inv (j + 1) st' := by
    let offset : IExp ℕ := .var stage * (.const d + 2) + (.const d - 1 - .var j)
    let z : K := c (d - 1 - j)
    have mm := RoutineSpec.stmt
      (hmm.spec_kcall realLayout.get_put .total () (3, 0) (4, 0) (5, 0) G (suffix j))
    have add := spec_addDiagonal .total I hs n 5 1 (by decide) offset (G * suffix j) z
    have cp := spec_copyMatrix .total I 5 4 (by decide)
      (G * suffix j + z • (1 : Matrix (Fin n) (Fin n) K))
    intro st hst
    refine mm.wp_bind ⟨hst.1.1, hst.2, blockDisjoint_of_fst_ne (by simp [matBlock]),
      blockDisjoint_of_fst_ne (by simp [matBlock]), ?_⟩ fun st₁ hm₁ hp₁ => ?_
    · simpa [realLayout, Mode.Needs] using hst.1.2.2.2
    · have hk₁ := frame hst.1 (hm₁.mono (by simp [fp, matBlock, realLayout, IExp.eval]))
      refine add.wp_bind ⟨hp₁.1, hk₁.2.1 (d - 1 - j) (by omega)⟩ fun st₂ hm₂ hp₂ => ?_
      have hk₂ := frame hk₁ (hm₂.mono (by simp [fp]))
      refine cp.wp_run ⟨hp₂.1, hk₂.2.2.1⟩ fun st₃ hm₃ hp₃ => ?_
      refine ⟨((hm₁.trans hm₂).trans hm₃).mono ?_, frame hk₂ (hm₃.mono (by simp [fp])), ?_⟩
      · simp [fp, matBlock, realLayout, IExp.eval]
      · simpa only [suffix, z, gramHorner_suffix_succ hj c G] using hp₃.1
  refine (RoutineSpec.forRange_const (m := .total) (I := I) (n := .const d)
    (body := body) (pre := inv 0) fp (fun _ k => inv k) (fun _ h => h)
    (fun _ _ j hj => step j hj)).conseq ?_ (fun _ h => h) ?_
  · intro st h
    exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩
  · intro _ _ _ h
    simpa [suffix] using h.2

end Proposal.Polar
