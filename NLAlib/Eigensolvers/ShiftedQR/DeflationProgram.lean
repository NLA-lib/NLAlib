/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Constants
public import NLAlib.Eigensolvers.ShiftedQR.WorklistAllocation

/-!
# Exact deflation from raw parameter words

The program computes the actual absolute threshold from the raw tolerance and Frobenius
norm, stores its prepared parameters in scoped storage, and executes the allocating worklist.
The supplied inputs are the raw matrix and `[B,theta,alpha,gamma,delta]` words; output slots
and all internal work arrays need no initialized contents.

## Main results

* `NLAlib.ShiftedQR.solve`: raw-parameter exact deflation with explicit scalar initialization.
* `NLAlib.ShiftedQR.solve_writes`: total actual stored roots and backward error.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- An allocated parameter view is separate from the original matrix and output views. -/
private theorem prepared_geometry {N : ℕ} {μ μ' μ'' : Mem ℝ} {a raw out : ℕ × ℕ}
    (hl : μ.Live [a, raw, out])
    (hr : μ.Room [a, raw, out] [2 * (N * N), 5, 2 * N])
    (ha : Fp.Apart [a, raw, out] [2 * (N * N), 5, 2 * N])
    (hs : μ'.store.length = μ.store.length + 1)
    (hP : μ'.store.len μ.store.length = 5)
    (hBelow : Store.Below μ.store.length μ.store μ'.store)
    (hfr : μ'.store.EqOff (Store.inBlock μ.store.length 0 5) μ''.store) :
    μ''.Live [a, (μ.store.length, 0), out] ∧
      μ''.Room [a, (μ.store.length, 0), out] [2 * (N * N), 5, 2 * N] ∧
      Fp.Apart [a, (μ.store.length, 0), out] [2 * (N * N), 5, 2 * N] := by
  have hla := hl a (by simp)
  have hlo := hl out (by simp)
  have hRawRoom : μ'.Room [a, raw, out] [2 * (N * N), 5, 2 * N] := by
    rw [Mem.room_eq_of_below hBelow (fun z hz => hl z hz)]
    exact hr
  have hAP : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N)))
      (Store.inBlock μ.store.length 0 5) := Fp.disj_inBlock_of_ne (by omega)
  have hPO : Fp.Disj (Store.inBlock μ.store.length 0 5)
      (Store.inBlock out.1 out.2 (2 * N)) := Fp.disj_inBlock_of_ne (by omega)
  have hAO : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N)))
      (Store.inBlock out.1 out.2 (2 * N)) := by
    simpa using ha.disj_getD (i := 0) (j := 2) (by simp) (by simp) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [hfr.length_eq, hs]
    exact ⟨hla.trans_le (by omega), by omega, hlo.trans_le (by omega)⟩
  · exact (show μ'.Room [a, (μ.store.length, 0), out] [2 * (N * N), 5, 2 * N] from
      ⟨hRawRoom.1, by simpa only [Nat.zero_add, hP] using le_rfl,
        hRawRoom.2.2.1, trivial⟩).congr hfr.len_eq
  · refine ⟨?_, ?_, Fp.disj_bot_right _, trivial⟩
    · simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using
        (Fp.disj_sup_right.mpr ⟨hAP, hAO⟩)
    · simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using hPO

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- Compute all prepared parameters from raw words before mutating the global matrix.
The decoupling body is one fixed scalar implementation supplied at construction time. -/
def solve (D : Impl O Q) : Impl O Q := opsImpl% [N, m, k, F, M] (A, Raw) → (Out) {
  let Params ← alloc 5;
  run (initializeParameters (Op := O) (Tst := Q)).body [N] (A, Raw, Params);
  run (solveAllocated D).body [N, m, k, F, M] (A, Params, Out)
}

/-- The actual raw-parameter program returns all roots of a perturbation satisfying
$\|\mathbf{E}\|_2\le n\delta\|\mathbf{H}\|_{\mathsf F}$ for order $n+1$.
The threshold is computed by the scalar initializer; it is not an assumed prepared input.
All scratch is scoped and no initialized output words are required. -/
theorem solve_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I)
    (hQ : IsToNat id I) (hC : IsCmp id I)
    {θ : ℝ} {K : KernelRoutines θ} (hK : IsEigenvalueKernels K I)
    (D : Impl O Q) (hD : DecouplingContract θ D I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m F M : ℕ} {a raw out : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {B α γ δ g : ℝ}
    (hl : μ.Live [a, raw, out])
    (hr : μ.Room [a, raw, out] [2 * ((n + 1) * (n + 1)), 5, 2 * (n + 1)])
    (ha : Fp.Apart [a, raw, out] [2 * ((n + 1) * (n + 1)), 5, 2 * (n + 1)])
    (hHess : IsUpperHessenberg H) (hA : HoldsMatrix a H μ.store)
    (hGlobal : ShiftedQRHyps H B θ α γ δ g m F)
    (hM : M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hRaw : μ.store.readBlock raw.1 raw.2 5 = some [B, θ, α, γ, δ]) :
    Writes .total I tape (solve D).body
      (Env.frame [n + 1, m, 2 ^ m, F, M] [a, raw, out])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)))
      (fun μ' => μ'.pos = μ.pos ∧
        ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
          HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
          specNorm E ≤ (n : ℝ) * (δ * frobNorm H) ∧
          (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)) μ := by
  have hla := hl a (by simp)
  have hlRaw := hl raw (by simp)
  have hlo := hl out (by simp)
  unfold solve
  refine writes_allocs_preserving_post (lens := [.const 5]) (ns := [5]) rfl ?_ ?_
  · intro s s' pos hBelow ⟨hp, roots, E, hOut, hNorm, hRoots⟩
    exact ⟨hp, roots, E, hOut.of_below hBelow hlo, hNorm, hRoots⟩
  · intro s hs hlens hBelow
    let p : ℕ × ℕ := (μ.store.length, 0)
    let μ₁ : Mem ℝ := ⟨s, μ.pos⟩
    have hP : s.len p.1 = 5 := by simpa [p] using hlens 0 (by simp)
    have hPA : Fp.Disj (Store.inBlock p.1 p.2 5)
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) :=
      Fp.disj_inBlock_of_ne (by dsimp [p]; omega)
    have hRawP : Fp.Disj (Store.inBlock raw.1 raw.2 5) (Store.inBlock p.1 p.2 5) :=
      Fp.disj_inBlock_of_ne (by dsimp [p]; omega)
    have hA₁ := hA.of_below hBelow hla
    have hRaw₁ := (hBelow.readBlock hlRaw raw.2 5).trans hRaw
    have hLiveInit : μ₁.Live [a, raw, p] := by
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      change a.1 < s.length ∧ raw.1 < s.length ∧ μ.store.length < s.length
      simp only [List.length_cons, List.length_nil] at hs
      exact ⟨by omega, by omega, by omega⟩
    have hInit := initializeParameters_writes (τ := tape) hS hE
      hLiveInit hA₁ hRaw₁ hRawP (by change 0 + 5 ≤ s.len p.1; omega)
    refine hInit.frame_seq_le rfl rfl hLiveInit
      (Fp.inBlock_le_sup_above (by dsimp [p]; omega)) ?_
    intro μ₂ hfr₂ ⟨hp₂, hParams⟩
    have hg := prepared_geometry hl hr ha hs hP hBelow hfr₂
    have hw := solveAllocated_writes (tape := tape) hS hE hL hQ hC hK D hD
      hg.1 hg.2.1 hg.2.2 hHess (hA₁.of_eqOff hfr₂ hPA) hGlobal rfl hM hParams
    refine (hw.in_frame rfl rfl hg.1).mono le_sup_left ?_
    intro _ _ ⟨hp₃, hOut⟩
    exact ⟨hp₃.trans hp₂, hOut⟩

end NLAlib.ShiftedQR
