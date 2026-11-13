import proposals.polar.Memory
import NLAlib.Computation.ScalarFrames

/-! Correctness of the first concrete step: copy column-major ROM into the output buffer. -/
open NLAlib NLAlib.Computation
open Builder

namespace Proposal.Polar

/-- The coefficient cell for a stage and a power. -/
theorem read_polarInput_coeff {𝕜 : Type} [RCLike 𝕜] (m n d k : ℕ) (c : ℕ → ℕ → ℝ)
    {s j : ℕ} (hs : s < k) (hj : j ≤ d+1) :
    (polarInput (𝕜 := 𝕜) m n d k c).store.read () 1 (s*(d+2)+j) = some (c s j : 𝕜) := by
  have hj' : j < d+2 := by omega
  have hi : s*(d+2)+j < k*(d+2) := by
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.add_mul_lt_mul_of_lt_of_lt hj' hs
  simp only [polarInput, inputState, Store.read, List.map_cons, List.map_nil]
  change (Array.ofFn (fun t : Fin (k*(d+2)) =>
    some ((c (t / (d+2)) (t % (d+2)) : ℝ) : 𝕜)))[s*(d+2)+j]?.join = _
  rw [Array.getElem?_eq_getElem (by simpa only [Array.size_ofFn] using hi)]
  have hdiv : (s*(d+2)+j)/(d+2) = s := by
    rw [Nat.mul_comm s, Nat.mul_add_div (by omega : 0 < d+2), Nat.div_eq_of_lt hj', Nat.add_zero]
  have hmod : (s*(d+2)+j)%(d+2) = j := by simp [Nat.mod_eq_of_lt hj']
  simp [hdiv, hmod]


/-- Running the ROM loop establishes the input layout, preserves the coefficient buffer
and retains both declared buffer sizes (also for zero-row and zero-column matrices). -/
theorem exists_exec_polarLoad {𝕜 : Type} [RCLike 𝕜] (m n d k : ℕ) (c : ℕ → ℕ → ℝ)
    (vals : ℕ → 𝕜) (ξ : Dist → ℕ → ℝ) :
    ∃ out, exec (polarInterp m n vals ξ)
      (.loop (.const m * .const n) (fun i => (Stmt.rom () ⟨0, .var i⟩ (.var i)).seq .skip))
      (polarInput m n d k c) = some out ∧
      out.store.shape = #[((),m*n),((),k*(d+2))] ∧
      realLayout.Holds out.store () 0 0
        (Matrix.of fun (i : Fin m) (j : Fin n) => vals (i+m*j)) ∧
      ∀ s < k, ∀ j ≤ d+1, out.store.read () 1 (s*(d+2)+j) = some (c s j : 𝕜) := by
  let I := polarInterp m n vals ξ
  let st₀ := polarInput (𝕜 := 𝕜) m n d k c
  let len : IExp ℕ := IExp.const m * IExp.const n
  have hl : len.eval = m*n := rfl
  have hshape : st₀.store.shape = #[((),m*n),((),k*(d+2))] := by
    simp [st₀, polarInput, inputState, Store.shape]
  obtain ⟨buf, hr, hsh, hread, hframe⟩ := exec_forRange_rom I () st₀ len 0 vals
    (by simp [hshape, hl]) (fun i hi => by
      change (if i < m*n then some (vals i) else none) = _
      exact if_pos (hl ▸ hi))
  refine ⟨_, hr, hsh.trans hshape, ?_, fun s hs j hj =>
    (hframe () 1 _ (by decide)).trans (read_polarInput_coeff m n d k c hs hj)⟩
  intro i j t
  change Fin 1 at t
  have ht : t = 0 := Subsingleton.elim _ _
  simpa [realLayout, ht] using hread (i+m*j) (hl.symm ▸ Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)


end Proposal.Polar
