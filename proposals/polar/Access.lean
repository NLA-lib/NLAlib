import proposals.polar.Horner

/-! A proposed registry-facing exact access model. The executable Horner tree requires
one matrix multiplication kernel in addition to its stored input entries. -/

open NLAlib NLAlib.Computation

namespace Proposal.Polar

/-- The stored-entries model with one designated exact matrix multiplication kernel
on one-word entries over the scalar field. Tree, cost and memory are fixed before data. -/
def StoredEntriesExactMatMul {K P ι : Type} [RCLike K] [DecidableEq P] [DecidableEq ι]
    {r b : ℕ} (p : P) (mm : ι) (prog : Prog P ι r b)
    (valid : ℕ → (Fin r → ℕ) → Prop) (X : ℕ → (Fin r → ℕ) → Type)
    (inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option K))
    (len : ℕ → (Fin r → ℕ) → ℕ) (cost : ℕ → (Fin r → ℕ) → OpCount P ι)
    (mem : ℕ → (Fin r → ℕ) → P → ℕ)
    (post : (N : ℕ) → (n : Fin r → ℕ) → X N n → (ℕ → K) → (Dist → ℕ → ℝ) →
      St P K (OpCount P ι) → Prop) : Prop :=
  letI : Inhabited K := ⟨0⟩
  ∀ N n, valid N n → ∀ x vals ξ,
    prog.RunsWithin ((storedInterp (len N n) vals ξ p).withKernel mm
      (liftMM realLayout (exactMM (𝕜 := K))) (mmShape (realLayout (K := K)))) N n
      (inputState p (List.ofFn (inputs N n x))) (cost N n) (mem N n) (post N n x vals ξ)

/-- The existing stored-entry nonvacuity check applies verbatim to the same inputs.
The choice of multiplication-kernel name has no effect on feasibility of the size conditions. -/
@[nolint unusedArguments]
def StoredEntriesExactMatMul.NonVacuous {K P ι : Type} [RCLike K] [DecidableEq P] [DecidableEq ι]
    {r b : ℕ} (p : P) (_mm : ι) (prog : Prog P ι r b)
    (valid : ℕ → (Fin r → ℕ) → Prop) (X : ℕ → (Fin r → ℕ) → Type)
    (inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option K))
    (len : ℕ → (Fin r → ℕ) → ℕ) (cost : ℕ → (Fin r → ℕ) → OpCount P ι)
    (mem : ℕ → (Fin r → ℕ) → P → ℕ)
    (post : (N : ℕ) → (n : Fin r → ℕ) → X N n → (ℕ → K) → (Dist → ℕ → ℝ) →
      St P K (OpCount P ι) → Prop) (N₀ : ℕ) : Prop :=
  StoredEntries.NonVacuous p prog valid X inputs len cost mem post N₀

private def inputs (K : Type) [RCLike K] (m : ℕ) (sizes : Fin 3 → ℕ) (c : ℕ → ℕ → ℝ) :
    Fin 2 → Array (Option K) :=
  ![Array.replicate (m * sizes 0) none,
    Array.ofFn fun i : Fin (sizes 2 * (sizes 1+2)) =>
      some ((c (i / (sizes 1+2)) (i % (sizes 1+2)) : ℝ) : K)]

/-- The registry-facing target with the same input and output as the expanded proposition. -/
def StoredEntriesHorner : Prop :=
  ∀ (K : Type) [RCLike K],
    StoredEntriesExactMatMul () () horner.compiled (fun _ _ => True)
      (fun _ _ => ℕ → ℕ → ℝ) (inputs K) (fun m sizes => m * sizes 0)
      (fun m sizes => (horner.compiled.staticCost (fun op => Finsupp.single op 1)
        (fun _ => 0) m sizes).count)
      (fun m sizes _ => 3*m*sizes 0 + 3*sizes 0*sizes 0 + sizes 2*(sizes 1+2))
      (fun m sizes c vals _ out => realLayout.Holds out.store () 0 0
        (oddMatrixIterate (sizes 1+1) c
          (Matrix.of fun (i : Fin m) (j : Fin (sizes 0)) => vals (i + m*j)) (sizes 2)) ∧
        Finsupp.weight (OpKind.kernelWeight fun _ => 1) out.cnt = (sizes 1+2)*sizes 2)

/-- Both presentations of the proposed claim have the same witness and postcondition. -/
theorem storedEntriesHorner_iff : StoredEntriesHorner ↔ StoredEntriesHornerWithExactMM := by
  constructor
  · intro h K _ m n d k c vals ξ
    have hr := h K m ![n,d,k] trivial c vals ξ
    simp [inputs, List.ofFn_succ, Matrix.cons_val] at hr ⊢
    convert! hr using 3
  · intro h K _ m sizes _ c vals ξ
    have eq : sizes = ![sizes 0, sizes 1, sizes 2] := by funext i; fin_cases i <;> rfl
    rw [eq]
    have hr := h K m (sizes 0) (sizes 1) (sizes 2) c vals ξ
    simp [inputs, List.ofFn_succ, Matrix.cons_val] at hr ⊢
    convert! hr using 3

/-- The target's valid sizes and coefficient inputs are inhabited arbitrarily far out. -/
theorem storedEntriesHorner_nonVacuous (N₀ : ℕ) :
    ∃ (K : Type) (_ : RCLike K), StoredEntriesExactMatMul.NonVacuous () () horner.compiled
      (fun _ _ => True) (fun _ _ => ℕ → ℕ → ℝ) (inputs K) (fun m sizes => m * sizes 0)
      (fun m sizes => (horner.compiled.staticCost (fun op => Finsupp.single op 1)
        (fun _ => 0) m sizes).count)
      (fun m sizes _ => 3*m*sizes 0 + 3*sizes 0*sizes 0 + sizes 2*(sizes 1+2))
      (fun m sizes c vals _ out => realLayout.Holds out.store () 0 0
        (oddMatrixIterate (sizes 1+1) c
          (Matrix.of fun (i : Fin m) (j : Fin (sizes 0)) => vals (i + m*j)) (sizes 2)) ∧
        Finsupp.weight (OpKind.kernelWeight fun _ => 1) out.cnt = (sizes 1+2)*sizes 2) N₀ :=
  ⟨ℝ, inferInstance, N₀, ![N₀, 0, 1], le_rfl, trivial, ⟨fun _ _ => 0⟩⟩

end Proposal.Polar
