import proposals.polar.Initial
import proposals.polar.Stage
import proposals.polar.Access

/-! Assemble the full stored-entry proof for the proposed polar target. -/

open NLAlib NLAlib.Computation NLAlib.Computation.Builder

namespace Proposal.Polar

private def workShape (m n d k : ℕ) : Array (Unit × ℕ) :=
  #[((),m*n),((),k*(d+2)),((),m*n),((),n*n),((),n*n),((),n*n)]

private def scratch (m n d k : ℕ) : Stmt Unit Unit ℕ ℕ :=
  let mn := (IExp.const m : IExp ℕ) * IExp.const n
  let nn := (IExp.const n : IExp ℕ) * IExp.const n
  .alloc () mn fun adj => .alloc () nn fun gram => .alloc () nn fun poly => .alloc () nn fun tmp =>
    .seq (.loop (.const k) fun i =>
      (stage (.const m) (.const n) (.const d) (.var i) 0 1 adj gram poly tmp).run) .skip

private theorem exists_exec_stages {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜]
    (I : Interp Unit Unit 𝕜 (OpCount Unit Unit)) (hs : I.sem = exactSem)
    (hmm : IsMatMulKernel I () realLayout (exactMM (𝕜 := 𝕜))) (m n d k : ℕ)
    (A : Matrix (Fin m) (Fin n) 𝕜) (c : ℕ → ℕ → ℝ)
    (st₀ : St Unit 𝕜 (OpCount Unit Unit)) (hsh : st₀.store.shape = workShape m n d k)
    (hA : realLayout.Holds st₀.store () 0 0 A)
    (hc : ∀ s < k, ∀ j ≤ d+1, st₀.store.read () 1 (s*(d+2)+j) = some (c s j : 𝕜)) :
    ∃ out, exec I (.loop (.const k) (fun i =>
      (stage (.const m) (.const n) (.const d) (.var i) 0 1 2 3 4 5).run)) st₀ = some out ∧
      out.store.shape = workShape m n d k ∧
      realLayout.Holds out.store () 0 0 (oddMatrixIterate (d+1) c A k) := by
  let Inv (s : ℕ) (st : St Unit 𝕜 (OpCount Unit Unit)) :=
    st.store.shape = workShape m n d k ∧
      (∀ i < k, ∀ j ≤ d+1, st.store.read () 1 (i*(d+2)+j) = some (c i j : 𝕜)) ∧
      realLayout.Holds st.store () 0 0 (oddMatrixIterate (d+1) c A s)
  have hi : Inv 0 st₀ := ⟨hsh,hc,hA⟩
  have hstep (i : ℕ) (hik : i < k) (st : St Unit 𝕜 (OpCount Unit Unit)) (h : Inv i st) :
      ∃ out, exec I (stage (.const m) (.const n) (.const d) (.var i) 0 1 2 3 4 5).run st =
        some out ∧ Inv (i+1) out := by
    obtain ⟨sh, hc', hcur⟩ := h
    apply (spec_stage I hs hmm m n d i (oddMatrixIterate (d+1) c A i) (c i)).wp_run
    · refine ⟨hcur, hc' i hik, ?_, ?_, ?_, ?_, ?_⟩ <;>
        exact writable_of_shape_eq sh rfl (by simp)
    · intro out hm hnew
      refine ⟨hm.1.trans sh, ?_, hnew⟩
      intro z hz j hj
      exact (hm.2 () 1 _ (fun b hb => blockDisjoint_of_fst_ne (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl|rfl|rfl|rfl|rfl <;> norm_num [matBlock]))).trans (hc' z hz j hj)
  obtain ⟨out, run, ho, _, hval⟩ :=
    exists_exec_loop_eq_some_of_forall (n := IExp.const k) (body := fun i =>
      (stage (.const m) (.const n) (.const d) (.var i) 0 1 2 3 4 5).run) I Inv hi hstep
  exact ⟨out,run,ho,hval⟩

private theorem exists_exec_scratch {𝕜 : Type} [RCLike 𝕜] [Inhabited 𝕜]
    (I : Interp Unit Unit 𝕜 (OpCount Unit Unit)) (hs : I.sem = exactSem)
    (hmm : IsMatMulKernel I () realLayout (exactMM (𝕜 := 𝕜))) (m n d k : ℕ)
    (A : Matrix (Fin m) (Fin n) 𝕜) (c : ℕ → ℕ → ℝ)
    (st : St Unit 𝕜 (OpCount Unit Unit)) (hsh : st.store.shape = #[((),m*n),((),k*(d+2))])
    (hA : realLayout.Holds st.store () 0 0 A)
    (hc : ∀ s < k, ∀ j ≤ d+1, st.store.read () 1 (s*(d+2)+j) = some (c s j : 𝕜)) :
    ∃ out, exec I (scratch m n d k) st = some out ∧
      realLayout.Holds out.store () 0 0 (oddMatrixIterate (d+1) c A k) := by
  let hold := fun (s : Store Unit 𝕜) => realLayout.Holds s () 0 0 (oddMatrixIterate (d+1) c A k)
  let mn := (IExp.const m : IExp ℕ) * IExp.const n
  let nn := (IExp.const n : IExp ℕ) * IExp.const n
  have hsize : st.store.size = 2 := by rw [← Store.size_shape, hsh]; simp
  refine exists_exec_alloc I () mn _ st hold fun a ha =>
    exists_exec_alloc I () nn _ a (fun y => hold y.pop) fun b hb =>
    exists_exec_alloc I () nn _ b (fun y => hold y.pop.pop) fun c₀ hc₀ =>
    exists_exec_alloc I () nn _ c₀ (fun y => hold y.pop.pop.pop) fun e he => ?_
  have haS : a.store.size = 3 := by simp [ha,hsize]
  have hbS : b.store.size = 4 := by simp [hb,haS]
  have hcS : c₀.store.size = 5 := by simp [hc₀,hbS]
  have hef : e.store.shape = workShape m n d k := by
    simp only [he,hc₀,hb,ha,Store.shape,Array.map_push,Array.size_replicate]
    change ((((st.store.shape.push ((),m*n)).push ((),n*n)).push ((),n*n)).push ((),n*n)) = _
    rw [hsh]
    rfl
  have hrd (q : ℕ) (hq : q < 2) (i : ℕ) : e.store.read () q i = st.store.read () q i := by
    rw [he, Store.read_push_of_ne (by omega), hc₀, Store.read_push_of_ne (by omega),
      hb, Store.read_push_of_ne (by omega), ha, Store.read_push_of_ne (by omega)]
  have heA : realLayout.Holds e.store () 0 0 A := hA.of_forall_read_eq fun i _ _ => hrd 0 (by decide) i
  obtain ⟨out, run, hout, hval⟩ := exists_exec_stages I hs hmm m n d k A c e hef heA
    fun s hs j hj => (hrd 1 (by decide) _).trans (hc s hs j hj)
  have hsize' : out.store.size = 6 := by
    rw [← Store.size_shape, hout]; simp [workShape]
  refine ⟨out, ?_, ?_⟩
  · rw [hsize,haS,hbS,hcS,exec_seq_skip]
    exact run
  · apply hval.of_forall_read_eq
    intro i _ _
    rw [Store.read_pop_of_lt (by simp [Array.size_pop,hsize']),
      Store.read_pop_of_lt (by simp [Array.size_pop,hsize']),
      Store.read_pop_of_lt (by simp [Array.size_pop,hsize']), Store.read_pop_of_lt (by omega)]

/-- All runs of the reviewed candidate exist, return the atlas iterate, and have the
declared operation and workspace bounds. -/
theorem storedEntriesHornerWithExactMM : StoredEntriesHornerWithExactMM := by
  apply storedEntriesHornerWithExactMM_of_value
  intro 𝕜 _ m n d k c vals ξ
  let : Inhabited 𝕜 := ⟨0⟩
  let I := polarInterp m n vals ξ
  let A := Matrix.of fun (i : Fin m) (j : Fin n) => vals (i+m*j)
  obtain ⟨load, hl, hsh, hA, hc⟩ := exists_exec_polarLoad m n d k c vals ξ
  obtain ⟨out, hr, hv⟩ := exists_exec_scratch I rfl
    (isMatMulKernel_withKernel _ () realLayout (exactMM (𝕜 := 𝕜))) m n d k A c load hsh hA hc
  refine ⟨out, ?_, hv⟩
  rw [Prog.exec_eq_exec_toStmt, horner.toStmt_compiled]
  change (exec I (.loop (.const m * .const n) (fun i =>
    .seq (.rom () ⟨0, .var i⟩ (.var i)) .skip)) (polarInput m n d k c)).bind
    (exec I (.seq (scratch m n d k) .skip)) = _
  rw [hl, Option.bind_some, exec_seq_skip, hr]

/-- The registry-shaped presentation of the verified stored-entry Horner target. -/
theorem storedEntriesHorner : StoredEntriesHorner :=
  storedEntriesHorner_iff.mpr storedEntriesHornerWithExactMM

end Proposal.Polar
