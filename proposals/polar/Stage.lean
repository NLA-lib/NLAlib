import proposals.polar.Inner

/-! Stage preservation for the proposed Horner tree. -/

open NLAlib NLAlib.Computation NLAlib.Computation.Builder

open scoped Matrix

namespace Proposal.Polar

private theorem holds_keep {K : Type} {fp : List (ℕ × ℕ × ℕ)} {s s' : Store Unit K}
    {b l n : ℕ} {A : Matrix (Fin l) (Fin n) K}
    (h : realLayout.Holds s () b 0 A) (hm : Modifies fp s s')
    (hne : ∀ x ∈ fp, b ≠ x.1) : realLayout.Holds s' () b 0 A :=
  h.of_forall_read_eq fun i _ _ => hm.2 () b i fun x hx => blockDisjoint_of_fst_ne (hne x hx)

private theorem read_keep {K : Type} {fp : List (ℕ × ℕ × ℕ)} {s s' : Store Unit K}
    {b i : ℕ} {value : K} (h : s.read () b i = some value) (hm : Modifies fp s s')
    (hne : ∀ x ∈ fp, b ≠ x.1) : s'.read () b i = some value :=
  (hm.2 () b i fun x hx => blockDisjoint_of_fst_ne (hne x hx)).trans h

private theorem mk_product {K C : Type} [RCLike K] [Inhabited K] [AddMonoid C]
    {I : Interp Unit Unit K C} (hmm : IsMatMulKernel I () realLayout (exactMM (𝕜:=K)))
    {l m n : ℕ} (a b out : ℕ) (ha : out ≠ a) (hb : out ≠ b)
    (A : Matrix (Fin l) (Fin m) K) (B : Matrix (Fin m) (Fin n) K) :
    RoutineSpec .total I (fun st => realLayout.Holds st.store () a 0 A ∧
      realLayout.Holds st.store () b 0 B ∧ Writable st.store () out 0 (l*n))
      (stmt (.kcall () () [.const l,.const m,.const n] [(a,0),(b,0)] [(out,0)]))
      [matBlock out 0 l n 1] (fun _ st => realLayout.Holds st.store () out 0 (A*B)) := by
  apply (RoutineSpec.stmt (hmm.spec_kcall realLayout.get_put .total () (a,0) (b,0) (out,0) A B)).conseq
  · rintro _ ⟨hA, hB, hw⟩
    exact ⟨hA, hB, blockDisjoint_of_fst_ne ha, blockDisjoint_of_fst_ne hb, by simpa [realLayout]⟩
  · intro x hx
    exact hx
  · exact fun _ _ _ h => h.1

/-- The unmodified coefficient row and the writable buffers used by every block. -/
private structure Ready {K : Type} (s : Store Unit K) (m n d index : ℕ) (c : ℕ → ℝ)
    [RCLike K] : Prop where
  coeff (j : ℕ) (hj : j ≤ d+1) : s.read () 1 (index*(d+2)+j) = some (c j : K)
  wx : Writable s () 0 0 (m*n)
  wa : Writable s () 2 0 (m*n)
  wg : Writable s () 3 0 (n*n)
  wp : Writable s () 4 0 (n*n)
  wt : Writable s () 5 0 (n*n)

private theorem Ready.keep {K : Type} [RCLike K] {s s' : Store Unit K} {m n d k : ℕ} {c : ℕ → ℝ}
    (ready : Ready s m n d k c) {fp : List (ℕ × ℕ × ℕ)} (hm : Modifies fp s s')
    (hc : ∀ x ∈ fp, 1 ≠ x.1) : Ready s' m n d k c :=
  ⟨fun j hj => read_keep (ready.coeff j hj) hm hc, ready.wx.of_modifies hm,
    ready.wa.of_modifies hm, ready.wg.of_modifies hm, ready.wp.of_modifies hm,
    ready.wt.of_modifies hm⟩

/-- The full compiled-stage body succeeds and stores the rectangular odd-polynomial update. -/
theorem spec_stage {K C : Type} [RCLike K] [Inhabited K] [AddMonoid C]
    (I : Interp Unit Unit K C) (hs : I.sem = exactSem)
    (hmm : IsMatMulKernel I () realLayout (exactMM (𝕜:=K))) (m n d index : ℕ)
    (A : Matrix (Fin m) (Fin n) K) (c : ℕ → ℝ) :
    RoutineSpec .total I (fun st => realLayout.Holds st.store () 0 0 A ∧
      (∀ j ≤ d+1, st.store.read () 1 (index*(d+2)+j) = some (c j : K)) ∧
      Writable st.store () 0 0 (m*n) ∧ Writable st.store () 2 0 (m*n) ∧
      Writable st.store () 3 0 (n*n) ∧ Writable st.store () 4 0 (n*n) ∧
      Writable st.store () 5 0 (n*n))
      (stage (.const m) (.const n) (.const d) (.var index) 0 1 2 3 4 5)
      [matBlock 0 0 m n 1, matBlock 2 0 m n 1, matBlock 3 0 n n 1,
        matBlock 4 0 n n 1, matBlock 5 0 n n 1]
      (fun _ out => realLayout.Holds out.store () 0 0 (A * gramHorner (d+1) c (Aᴴ*A))) := by
  let base : IExp ℕ := .var index * (.const d + 2)
  let G := Aᴴ*A
  let P := gramHorner (d+1) c G
  have specA := routineSpec_adjoint .total I hs (.const m) (.const n) 0 2 (by decide) A
  have specG := mk_product hmm 2 0 3 (by decide) (by decide) Aᴴ A
  have specS := spec_scaleMatrix .total I hs 3 4 1 (by decide) (by decide) (base+.const d+1) G
    (c (d+1) : K)
  have specD := spec_addDiagonal .total I hs n 4 1 (by decide) (base+.const d) ((c (d+1) : K) • G)
    (c d : K)
  have specP := spec_inner I hs hmm n d index G c
  have specM := mk_product hmm 0 4 2 (by decide) (by decide) A P
  have specC := spec_copyMatrix .total I 2 0 (by decide) (A*P)
  refine ⟨by unfold stage; exec_composable, ?_⟩
  rintro st ⟨hA,hrow,wx,wa,wg,wp,wt⟩
  have rr : Ready st.store m n d index c := ⟨hrow,wx,wa,wg,wp,wt⟩
  refine specA.wp_bind ⟨hA, by change Writable st.store () 2 0 (n*m); simpa [Nat.mul_comm] using wa⟩ fun s₁ hm₁ h₁ => ?_
  have r₁ := rr.keep hm₁ (by simp [matBlock])
  have a₁ := holds_keep hA hm₁ (by simp [matBlock])
  refine specG.wp_bind ⟨h₁.1, a₁, r₁.wg⟩ fun s₂ hm₂ h₂ => ?_
  have r₂ := r₁.keep hm₂ (by simp [matBlock])
  have a₂ := holds_keep a₁ hm₂ (by simp [matBlock])
  have top : s₂.store.read () 1 (base + .const d + 1).eval = some (c (d+1) : K) := by
    simpa [base, IExp.eval, Nat.add_assoc] using r₂.coeff (d+1) (by omega)
  refine specS.wp_bind ⟨h₂, top, r₂.wp⟩ fun s₃ hm₃ h₃ => ?_
  have r₃ := r₂.keep hm₃ (by simp [matBlock])
  have a₃ := holds_keep a₂ hm₃ (by simp [matBlock])
  have g₃ := holds_keep h₂ hm₃ (by simp [matBlock])
  refine specD.wp_bind ⟨h₃.1, r₃.coeff d (by omega)⟩ fun s₄ hm₄ h₄ => ?_
  have r₄ := r₃.keep hm₄ (by simp [matBlock])
  have a₄ := holds_keep a₃ hm₄ (by simp [matBlock])
  have g₄ := holds_keep g₃ hm₄ (by simp [matBlock])
  have p₄ : realLayout.Holds s₄.store () 4 0 (gramHorner 1 (fun i => c (d+i)) G) := by
    rw [gramHorner, Nat.add_zero, RCLike.real_smul_eq_coe_smul (K := K) (c d),
      RCLike.real_smul_eq_coe_smul (K := K) (c (d+1)), add_comm]
    exact h₄.1
  refine specP.wp_bind ⟨g₄,p₄,r₄.coeff,r₄.wp,r₄.wt⟩ fun s₅ hm₅ h₅ => ?_
  have r₅ := r₄.keep hm₅ (by simp [matBlock])
  have a₅ := holds_keep a₄ hm₅ (by simp [matBlock])
  refine specM.wp_bind ⟨a₅, h₅, r₅.wa⟩ fun s₆ hm₆ h₆ => ?_
  refine specC.wp_run ⟨h₆, r₅.wx.of_modifies hm₆⟩ fun out hm₇ h₇ => ?_
  refine ⟨?_,h₇.1⟩
  exact (hm₁.trans (hm₂.trans (hm₃.trans (hm₄.trans (hm₅.trans (hm₆.trans hm₇)))))).mono
    (by simp [matBlock, Nat.mul_comm])

end Proposal.Polar
