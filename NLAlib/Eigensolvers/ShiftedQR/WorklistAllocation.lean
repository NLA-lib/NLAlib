/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.WorklistExecute
public import NLAlib.Ops.Logic.Allocation

/-!
# Scoped storage for exact shifted-QR deflation

The stack, dense workspace and five-word scan view are actual scoped allocations. The raw
matrix, five parameter words and persistent output are the only supplied buffers. The shared
allocation rules transport the completed root column through scratch cleanup.

## Main results

* `NLAlib.ShiftedQR.solveAllocated`: the allocating fixed implementation.
* `NLAlib.ShiftedQR.solveAllocated_writes`: total output and backward error with scoped scratch.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- Standard initial geometry extends to the six views of the allocated worklist.
Only the shared allocation facts, room, apartness and subview permutation are used. -/
private theorem geometry_allocated {N : ℕ} {μ : Mem ℝ} {a p out : ℕ × ℕ} {s : Store ℝ}
    (hl : μ.Live [a, p, out])
    (hr : μ.Room [a, p, out] [2 * (N * N), 5, 2 * N])
    (ha : Fp.Apart [a, p, out] [2 * (N * N), 5, 2 * N])
    (hs : s.length = μ.store.length + 3)
    (hlens : ∀ i (hi : i < ([1 + 2 * N, 2 * (N * N), 5] : List ℕ).length),
      s.len (μ.store.length + i) = ([1 + 2 * N, 2 * (N * N), 5] : List ℕ)[i])
    (hBelow : Store.Below μ.store.length μ.store s) :
    WorklistGeometry N a p (μ.store.length, 0) out
      (μ.store.length + 1, 0) (μ.store.length + 2, 0) ⟨s, μ.pos⟩ := by
  let L := μ.store.length
  let ns := [1 + 2 * N, 2 * (N * N), 5]
  have hRaw : (⟨s, μ.pos⟩ : Mem ℝ).Room [a, p, out] [2 * (N * N), 5, 2 * N] := by
    rw [Mem.room_eq_of_below hBelow (fun z hz => hl z hz)]
    exact hr
  have hFresh : (⟨s, μ.pos⟩ : Mem ℝ).Room [(L, 0), (L + 1, 0), (L + 2, 0)] ns := by
    simpa [ns, List.range_succ, Nat.add_assoc] using Mem.room_allocs ⟨s, μ.pos⟩ L ns hlens
  have hFreshApart : Fp.Apart [(L, 0), (L + 1, 0), (L + 2, 0)] ns := by
    simpa [ns, List.range_succ, Nat.add_assoc] using Fp.apart_allocs L ns
  have hCross : Fp.Disj (Fp.blocks [a, p, out] [2 * (N * N), 5, 2 * N])
      (Fp.blocks [(L, 0), (L + 1, 0), (L + 2, 0)] ns) := by
    refine (Fp.blocks_disj_above (fun z hz => hl z hz)).mono le_rfl ?_
    exact Fp.blocks_le_above (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> omega)
  have hAll := ha.append hFreshApart rfl hCross
  let e : Fin 6 ≃ Fin 6 := Equiv.swap 2 3
  have hReorder := hAll.subviews (fun i : Fin 6 => e i) (fun _ => 0)
    (fun i => ([2 * (N * N), 5, 2 * N, 1 + 2 * N, 2 * (N * N), 5] : List ℕ).getD (e i) 0)
    (by intro i; simpa only [ns, List.cons_append, List.nil_append, Nat.zero_add] using
      (le_refl
        (([2 * (N * N), 5, 2 * N, 1 + 2 * N, 2 * (N * N), 5] : List ℕ).getD (e i) 0)))
    (by intro i j hne he; exact False.elim (hne (e.injective he)))
  refine ⟨?_, ?_, ?_⟩
  · have hla := hl a (by simp)
    have hlp := hl p (by simp)
    have hlo := hl out (by simp)
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [hs]; omega)
  · exact ⟨hRaw.1, hRaw.2.1, hFresh.1, hRaw.2.2.1, hFresh.2.1, hFresh.2.2.1, trivial⟩
  · simpa [e, ns, L, List.ofFn_succ, Equiv.swap_apply_def] using hReorder

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- The full worklist allocates and releases its stack, work matrix and scan registers. -/
def solveAllocated (D : Impl O Q) : Impl O Q := opsImpl% [N, m, k, F, M] (A, Params) → (Out) {
  let St ← alloc (1 + 2 * N);
  let W ← alloc (2 * (N * N));
  let R ← alloc 5;
  run (worklistSolve D).body [N, m, k, F, M] (A, Params, St, Out, W, R)
}

/-- The actual allocating exact algorithm returns a packed listing of a perturbation of the
raw input, with error at most $n\tau$ for order $n+1$. Scratch and output need no initialized
contents; the raw spectral and numerical parameter hypotheses guarantee total execution. -/
theorem solveAllocated_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I)
    (hQ : IsToNat id I) (hC : IsCmp id I)
    {θ : ℝ} {K : KernelRoutines θ} (hK : IsEigenvalueKernels K I)
    (D : Impl O Q) (hD : DecouplingContract θ D I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m F M : ℕ} {a p out : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ B α γ δ g : ℝ}
    (hl : μ.Live [a, p, out])
    (hr : μ.Room [a, p, out] [2 * ((n + 1) * (n + 1)), 5, 2 * (n + 1)])
    (ha : Fp.Apart [a, p, out] [2 * ((n + 1) * (n + 1)), 5, 2 * (n + 1)])
    (hHess : IsUpperHessenberg H) (hA : HoldsMatrix a H μ.store)
    (hGlobal : ShiftedQRHyps H B θ α γ δ g m F) (hτ : τ = δ * frobNorm H)
    (hM : M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hParams : μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ]) :
    Writes .total I tape (solveAllocated D).body
      (Env.frame [n + 1, m, 2 ^ m, F, M] [a, p, out])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)))
      (fun μ' => μ'.pos = μ.pos ∧
        ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
          HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
          specNorm E ≤ (n : ℝ) * τ ∧
          (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)) μ := by
  unfold solveAllocated
  refine writes_allocs_preserving_post
    (lens := [.const 1 + .const 2 * .var 0, .const 2 * (.var 0 * .var 0), .const 5])
    (ns := [1 + 2 * (n + 1), 2 * ((n + 1) * (n + 1)), 5]) rfl ?_ ?_
  · intro s s' pos hBelow ⟨hp, roots, E, hOut, hNorm, hRoots⟩
    exact ⟨hp, roots, E, hOut.of_below hBelow (hl out (by simp)), hNorm, hRoots⟩
  · intro s hs hlens hBelow
    let L := μ.store.length
    have hG := geometry_allocated hl hr ha hs hlens hBelow
    have hA' := hA.of_below hBelow (hl a (by simp))
    have hP' := (hBelow.readBlock (hl p (by simp)) p.2 5).trans hParams
    have hw := worklistSolve_writes (tape := tape) hS hE hL hQ hC hK D hD hG
      hHess hA' hGlobal hτ hM hP'
    refine (hw.in_frame rfl rfl hG.live).mono ?_ (fun _ _ hp => hp)
    intro b x hx
    simp only [worklistFp, Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq, Pi.sup_apply] at hx
    rcases hx with hx | hx | hx | hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (show μ.store.length ≤ b from by
        have he : b = μ.store.length := hx.1
        omega)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (show μ.store.length ≤ b from by
        have he : b = μ.store.length + 1 := hx.1
        omega)
    · exact Or.inr (show μ.store.length ≤ b from by
        have he : b = μ.store.length + 2 := hx.1
        omega)

end NLAlib.ShiftedQR
