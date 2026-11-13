import proposals.polar.Horner

/-! Workspace accounting for the proposed stored-entry polar algorithm. -/

open NLAlib NLAlib.Computation

namespace Proposal.Polar

/-- The four scoped arrays use one rectangular temporary and three square temporaries.
This is the program's workspace in addition to input buffers and ROM. -/
theorem horner.cells_staticCost (m n d k : ℕ) (charge : OpKind Unit Unit → OpCount Unit Unit)
    (width : Unit → ℕ) : (horner.compiled.staticCost charge width m ![n, d, k]).cells () =
      m*n + 3*(n*n) := by
  change (StaticCost.seq _ _).cells () = _
  simp [FStmt.staticCost, StaticCost.seq, StaticCost.alloc, StaticCost.step, StaticCost.zero,
    IExp.evalIn, Matrix.cons_val,
    Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty, Matrix.Fin.cons_vecCons]
  ring

/-- The exact stored-entry interpreter used by the proposed polar target. -/
noncomputable def polarInterp {𝕜 : Type} [RCLike 𝕜] (m n : ℕ) (vals : ℕ → 𝕜)
    (ξ : Dist → ℕ → ℝ) : Interp Unit Unit 𝕜 (OpCount Unit Unit) :=
  letI : Inhabited 𝕜 := ⟨0⟩
  (storedInterp (m * n) vals ξ ()).withKernel ()
    (liftMM realLayout (exactMM (𝕜 := 𝕜))) (mmShape (realLayout (K := 𝕜)))

/-- The first handle is writable scratch for the initial input; the second holds the
supplied coefficients in ascending powers, grouped by stage. -/
def polarInput {𝕜 : Type} [RCLike 𝕜] (m n d k : ℕ) (c : ℕ → ℕ → ℝ) :
    St Unit 𝕜 (OpCount Unit Unit) :=
  inputState () [Array.replicate (m * n) none,
    Array.ofFn fun t : Fin (k * (d+2)) => some ((c (t / (d+2)) (t % (d+2)) : ℝ) : 𝕜)]

/-- A successful value-correct run of this exact interpreter automatically satisfies every
resource clause of the proposed target, including the read-only copy of the input. -/
theorem storedEntriesHornerWithExactMM_of_value
    (value : ∀ (𝕜 : Type) [RCLike 𝕜] (m n d k : ℕ) (c : ℕ → ℕ → ℝ) (vals : ℕ → 𝕜)
      (ξ : Dist → ℕ → ℝ), ∃ out,
      horner.compiled.exec (polarInterp m n vals ξ) m ![n,d,k] (polarInput m n d k c) =
        some out ∧ realLayout.Holds out.store () 0 0
        (oddMatrixIterate (d+1) c (Matrix.of fun (i : Fin m) (j : Fin n) => vals (i+m*j)) k)) :
    StoredEntriesHornerWithExactMM := by
  intro 𝕜 _ m n d k c vals ξ
  let I := polarInterp m n vals ξ
  let st := polarInput (𝕜 := 𝕜) m n d k c
  obtain ⟨out, hr, hval⟩ := value 𝕜 m n d k c vals ξ
  have run : horner.compiled.exec I m ![n,d,k] st = some out := hr
  have hc := horner.compiled.bounds_staticCost_of_exec_eq_some I m ![n,d,k] run
  refine ⟨by simp, out, run, hc.count, ?_, hval, ?_⟩
  · intro p
    cases p
    have hp := hc.peak ()
    rw [horner.cells_staticCost] at hp
    have hpeak : st.peak () = m*n + k*(d+2) := by simp [st, polarInput, inputState]
    have hcur : st.cur () = m*n + k*(d+2) := by simp [st, polarInput, inputState]
    rw [hpeak, hcur, max_eq_right (Nat.le_add_right _ _)] at hp
    change out.peak () + m*n ≤ 3*m*n + 3*n*n + k*(d+2)
    calc
      _ ≤ (m*n + k*(d+2) + (m*n + 3*(n*n))) + m*n := Nat.add_le_add_right hp _
      _ = _ := by ring
  · have h := horner.kernelWeight_cnt_of_exec_eq_some I rfl m n d k run
    simpa only [show st.cnt = 0 from rfl, map_zero, Nat.zero_add] using h

end Proposal.Polar
