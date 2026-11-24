/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.DeflationProgram
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# The routine of exact shifted QR with deflation

`NLAlib.ShiftedQR.deflationRoutine` is
`[n, m, k, F, M] (A : update 2 (n + 1)², p : read 5) → (out : write 2 (n + 1))`: the solver
`NLAlib.ShiftedQR.solve` at the order `n + 1`. The matrix is working storage: it is read and
left with unspecified contents, so the routine meets its specification in the sense of
`NLAlib.Ops.Routine.Meets`; the matrix is an unreported operand, so only the output block is
reported. It draws nothing.

## Main definitions

* `NLAlib.ShiftedQR.deflationRoutine`, `NLAlib.ShiftedQR.deflationSpec`.

## Main results

* `NLAlib.ShiftedQR.deflationRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- Exact shifted QR with deflation at the order `n + 1`:
`[n, m, k, F, M] (A : update 2 (n + 1)², p : read 5) → (out : write 2 (n + 1))`. The dimension
`n` is one less than the order, so that every dimension is the order of a nonempty matrix; the
tree is `solve D` at `n + 1`. The matrix is destroyed, so its final contents are not reported.
The tree `solve D` has one buffer variable for each operand (the matrix is updated through one
variable), which the clause `one variable` states; the routine then has no layout, and its
program is this tree with no frame around it. -/
def deflationRoutine (D : Stmt O Q) : Routine O Q :=
  routine% [n, m, k, F, M] (unreported A : 2 * ((n + 1) * (n + 1)), p : 5) →
      (A, out : 2 * (n + 1))
    one variable {
    run (solve D) [n + 1, m, k, F, M] (A, p, out)
  }

/-- For an upper Hessenberg matrix $\mathbf{H}$ of order $n + 1$ and parameters satisfying the
hypotheses of the analysis, the output block holds all roots of a perturbation
$\mathbf{H} + \mathbf{E}$ with $\|\mathbf{E}\|_2 \le n \delta \|\mathbf{H}\|_{\mathsf F}$. -/
noncomputable def deflationSpec {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B θ α γ δ g : ℝ) : Routine.Spec ℝ where
  pre d _ X := d.headD 0 = n ∧ d.getD 2 0 = 2 ^ d.getD 1 0 ∧ IsUpperHessenberg H ∧
    X = [matrixWords H, [B, θ, α, γ, δ]] ∧
    ShiftedQRHyps H B θ α γ δ g (d.getD 1 0) (d.getD 3 0) ∧
    d.getD 4 0 = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ d.getD 1 0) B θ α ((1 - γ) ^ 2)⌉₊
  post _ _ _ Y := ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    Y = [matrixWords (Matrix.of fun i (_ : Fin 1) => roots i)] ∧
    specNorm E ≤ (n : ℝ) * (δ * frobNorm H) ∧
    (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)

/-- Exact shifted QR with deflation meets its specification for every exact interpretation with
the spectral kernels at $\theta$ and every decoupling implementation satisfying its contract. -/
theorem deflationRoutine_meets {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I)
    (hQ : IsToNat id I) (hC : IsCmp id I)
    {θ : ℝ} {K : KernelRoutines θ} (hK : IsEigenvalueKernels K I)
    (D : Stmt O Q) (hD : DecouplingContract θ D I) {n : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {B α γ δ g : ℝ} :
    (deflationRoutine D).Meets I (deflationSpec H B θ α γ δ g) := by
  routine_intro [n', mm, k, F, M] (a, raw, out) reads (ws, ps)
  obtain ⟨hn, hk, hHess, heq, hGlobal, hM⟩ := hpre
  obtain rfl : n' = n := hn
  obtain rfl : k = 2 ^ mm := hk
  obtain ⟨rfl, rfl⟩ : ws = matrixWords H ∧ ps = [B, θ, α, γ, δ] := by simpa using heq
  have hRoom : m.Room [a, raw, out] [2 * ((n' + 1) * (n' + 1)), 5, 2 * (n' + 1)] := by
    simp only [Mem.room_cons, Mem.room_nil, and_true]
    exact ⟨hroom.1, Store.le_len_of_readBlock hps (by omega), hroom.2⟩
  have hApart : Fp.Apart [a, raw, out] [2 * ((n' + 1) * (n' + 1)), 5, 2 * (n' + 1)] := by
    disjoint
  -- the raw parameters are turned into prepared ones in a scoped buffer, then the solver runs
  have hA : HoldsMatrix a H m.store := hws
  have hw : Writes .total I τ (solve D)
      (Env.frame [n' + 1, mm, 2 ^ mm, F, M] [a, raw, out])
      (Store.inBlock a.1 a.2 (2 * ((n' + 1) * (n' + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n' + 1)))
      (fun μ' => μ'.pos = m.pos ∧
        ∃ (roots : Fin (n' + 1) → ℂ) (E : Matrix (Fin (n' + 1)) (Fin (n' + 1)) ℂ),
          HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
          specNorm E ≤ (n' : ℝ) * (δ * frobNorm H) ∧
          (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)) m := by
      have hla := hlive a (by simp)
      have hlRaw := hlive raw (by simp)
      have hlo := hlive out (by simp)
      unfold solve
      refine writes_allocs_preserving_post (lens := [.const 5]) (ns := [5]) rfl ?_ ?_
      · intro s s' pos hBelow ⟨hp, roots, E, hOut, hNorm, hRoots⟩
        exact ⟨hp, roots, E, hOut.of_below hBelow hlo, hNorm, hRoots⟩
      · intro s hs hlens hBelow
        let p : ℕ × ℕ := (m.store.length, 0)
        let μ₁ : Mem ℝ := ⟨s, m.pos⟩
        have hP : s.len p.1 = 5 := by simpa [p] using hlens 0 (by simp)
        have hPA : Fp.Disj (Store.inBlock p.1 p.2 5)
            (Store.inBlock a.1 a.2 (2 * ((n' + 1) * (n' + 1)))) :=
          Fp.disj_inBlock_of_ne (by dsimp [p]; omega)
        have hRawP : Fp.Disj (Store.inBlock raw.1 raw.2 5) (Store.inBlock p.1 p.2 5) :=
          Fp.disj_inBlock_of_ne (by dsimp [p]; omega)
        have hA₁ := hA.of_below hBelow hla
        have hRaw₁ := (hBelow.readBlock hlRaw raw.2 5).trans hps
        have hLiveInit : μ₁.Live [a, raw, p] := by
          simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
            forall_eq]
          change a.1 < s.length ∧ raw.1 < s.length ∧ m.store.length < s.length
          simp only [List.length_cons, List.length_nil] at hs
          exact ⟨by omega, by omega, by omega⟩
        have hInit := initializeParameters_writes (τ := τ) hS hE
          hLiveInit hA₁ hRaw₁ hRawP (by change 0 + 5 ≤ s.len p.1; omega)
        refine hInit.frame_seq_le rfl rfl hLiveInit
          (Fp.inBlock_le_sup_above (by dsimp [p]; omega)) ?_
        intro μ₂ hfr₂ ⟨hp₂, hParams⟩
        have hg := prepared_geometry hlive hRoom hApart hs hP hBelow hfr₂
        have hw := solveAllocated_writes (tape := τ) hS hE hL hQ hC hK D hD
          hg.1 hg.2.1 hg.2.2 hHess (hA₁.of_eqOff hfr₂ hPA) hGlobal rfl hM hParams
        refine (hw.in_frame rfl rfl hg.1).mono le_sup_left ?_
        intro _ _ ⟨hp₃, hOut⟩
        exact ⟨hp₃.trans hp₂, hOut⟩
  refine (hw.in_frame (ρ := Env.frame [n', mm, 2 ^ mm, F, M] [a, raw, out]) rfl rfl (by room)).mono
    (by fp_sub) ?_
  rintro m' - ⟨hpos, roots, E, hOut, hNorm, hRoots⟩
  refine ⟨hpos, [_], Mem.readBlocks_of_cons ?_ rfl, roots, E, rfl, hNorm, hRoots⟩
  have h : m'.store.readBlock out.1 out.2 (2 * (1 * (n' + 1))) = some _ := hOut
  rwa [Nat.one_mul] at h

end NLAlib.ShiftedQR
