/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.RandomHessenbergWeights
public import NLAlib.Eigensolvers.HessenbergReduction
public import NLAlib.Eigensolvers.SmallEig.Draws
public import NLAlib.Matrix.Perturbation.EigenvalueBackward
public import NLAlib.Matrix.QRIteration.EigenvectorWeights
public import NLAlib.Ops.Logic.Probabilistic
public import NLAlib.RandomMatrix.Gaussian.Complex.LeastSingularValue
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlib.RandomMatrix.Gaussian.Tape

/-!
# The random Hessenberg form

`RHess` ([BanksGarzaVargasSrivastava2025, §5]) makes the last-row weights of an eigenvector
matrix large: a unitary similarity whose last column is a random direction, followed by the
bottom-up Hessenberg reduction, which fixes the last coordinate vector. The direction here is a
complex Gaussian vector $\mathbf{g}$ of $2N$ draws, rotated to $\mathbf{e}_N$ by $N - 1$ rounded
Givens rotations, instead of the paper's uniform vector on the sphere applied by a reflector: the
phase of the last column is explicit (the paper's erratum P3), anti-concentration in a fixed
direction is that of a Gaussian
(`NLAlib.measureReal_norm_dotProduct_le_le_of_hasLaw_complexGaussianVector`),
and the weights are taken for the eigenvectors of the input, fixed before the draw, then
transferred to the output (`NLAlib.exists_lastRowWeights_ge_of_norm_sub_le`, the erratum P4).

## Main definitions

* `NLAlib.SmallEig.rhess`: the program `[N] (A) → (A)`.

## Main results

* `NLAlib.SmallEig.rhess_writes_word`, `NLAlib.SmallEig.rhess_isPerturbedUnitarySimilar`,
  `NLAlib.SmallEig.rhess_pwrites`, `NLAlib.SmallEig.rhess_terminates`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR
open Matrix (replicateCol replicateCol_apply)

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has CmpTst Q]

/-- **The random Hessenberg form** ([BanksGarzaVargasSrivastava2025, Proposition 5.3], with a
Gaussian direction and rotations): draw $2N$ words of the stream `sG` as a complex vector
$\mathbf{g}$; for $j < N - 1$, the Givens coefficients of $(\bar g_{j+1}, -\bar g_j)$, the rotation
of the entries $j, j + 1$ of $\mathbf{g}$ (which zeros entry $j$), and the same rotation of the
rows and the columns $j, j + 1$ of `A`; then `NLAlib.hessenbergReduceLast`. The rotations are
recorded in the slotted log `Lg` (slot width $w \ge N - 1$): the $N - 1$ rotations of the vector
as the entries of slot $j_0$ (validated), the reduction's rounds in the slots
$j_0 + 1, \dots, j_0 + N - 2$. The interface is `[N, w, j0] (A) → (A, Lg)`; the vector, the
coefficients and the scratch are scoped.
Algorithm: small-eig -/
def rhess (sG : ℕ) : Impl O Q := opsImpl% [N, w, j0] (A) → (A, Lg) {
  let G ← alloc (2 * N);
  let Cf ← alloc 4;
  let Uv ← alloc 4;
  let Tm ← alloc 10;
  run (gaussDraws (O := O) (Q := Q) sG).body [2 * N] (G);
  for j < N - 1 {
    call (Has.inj ScalarOp.copy) [] (G[2 * j + 2]) → (Uv);
    call (Has.inj ScalarOp.neg) [] (G[2 * j + 3]) → (Uv[1]);
    call (Has.inj ScalarOp.neg) [] (G[2 * j]) → (Uv[2]);
    call (Has.inj ScalarOp.copy) [] (G[2 * j + 1]) → (Uv[3]);
    run (slottedLogWrite (O := O) (Q := Q)).body [w, j0, j, j] (Uv, Uv[2], Lg);
    run (coefficients (Op := O) (Tst := Q)).body [] (Uv, Uv[2], Cf, Cf[2]);
    run (rotateLeftWithScratch (Op := O) (Tst := Q)).body []
      (Cf, Cf[2], G[2 * j], G[2 * j + 2], Tm, G[2 * j], G[2 * j + 2]);
    run (rotateRows (Op := O) (Tst := Q)).body [N, j] (A, Cf, Cf[2], A);
    run (rotateColumns (Op := O) (Tst := Q)).body [N, j] (A, Cf, Cf[2], A)
  };
  run (slottedLogValidate (O := O) (Q := Q)).body [w, j0] (Lg);
  run (hessenbergReduceLast (O := O) (Q := Q)).body [N, w, j0 + 1] (A, A, Lg)
}

end Program

/-- `omega` after reducing the projections of literal pairs. -/
local macro "pomega" : tactic => `(tactic| ((try dsimp only) <;> omega))

section Steps

variable {O Q : Type} [Has ScalarOp O] [Has CmpTst Q]

/-- The words of a stored vector. -/
private theorem get_colVec {N L : ℕ} {s : Store ℝ} {v : Fin N → ℂ}
    (h : HoldsMatrix (L, 0) (replicateCol (Fin 1) v) s) (i : Fin N) :
    s.get L (2 * i) = some (v i).re ∧ s.get L (2 * i + 1) = some (v i).im := by
  have h0 := h.get_re i 0
  have h1 := h.get_im i 0
  simp only [replicateCol_apply, Fin.val_zero, zero_mul, zero_add] at h0 h1
  exact ⟨h0, h1⟩

/-- A stored vector from its words. -/
private theorem holdsMatrix_colVec {N L : ℕ} {s : Store ℝ} {v : Fin N → ℂ}
    (h : ∀ i : Fin N, s.get L (2 * i) = some (v i).re ∧ s.get L (2 * i + 1) = some (v i).im) :
    HoldsMatrix (L, 0) (replicateCol (Fin 1) v) s := by
  refine HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)
  · have : (j : ℕ) = 0 := Nat.lt_one_iff.mp j.isLt
    simpa [this] using (h i).1
  · have : (j : ℕ) = 0 := Nat.lt_one_iff.mp j.isLt
    simpa [this] using (h i).2

/-- **The coefficients of one rotation of `RHess`**: the four words
$(\Re g_{j+1}, -\Im g_{j+1}, -\Re g_j, \Im g_j)$ into `Uv`, then their rounded Givens
coefficients into `Cf`; only `Cf` and `Uv` are written. -/
private theorem writes_rhessCoeffs {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {F : Fp} {P : Mem ℝ → Prop}
    {L t : ℕ} {x₀ x₁ y₀ y₁ : ℝ} {i₁ u₁ i₂ u₂ i₃ u₃ i₄ u₄ : List Operand} {ds : List IExp}
    {as : List Operand} {next : Stmt O Q}
    (h₁ : Operand.evalList ρ i₁ = some [(L, t + 2)])
    (h₁' : Operand.evalList ρ u₁ = some [(L + 2, 0)])
    (h₂ : Operand.evalList ρ i₂ = some [(L, t + 3)])
    (h₂' : Operand.evalList ρ u₂ = some [(L + 2, 1)])
    (h₃ : Operand.evalList ρ i₃ = some [(L, t)])
    (h₃' : Operand.evalList ρ u₃ = some [(L + 2, 2)])
    (h₄ : Operand.evalList ρ i₄ = some [(L, t + 1)])
    (h₄' : Operand.evalList ρ u₄ = some [(L + 2, 3)])
    (hd : IExp.evalList ρ.idx ds = some [])
    (ha : Operand.evalList ρ as = some [(L + 2, 0), (L + 2, 2), (L + 1, 0), (L + 1, 2)])
    (hx₀ : m.store.get L t = some x₀) (hx₁ : m.store.get L (t + 1) = some x₁)
    (hy₀ : m.store.get L (t + 2) = some y₀) (hy₁ : m.store.get L (t + 3) = some y₁)
    (hlen : L + 2 < m.store.length) (hCf : m.store.len (L + 1) = 4)
    (hUv : m.store.len (L + 2) = 4)
    (hF : Store.inBlock (L + 1) 0 4 ⊔ Store.inBlock (L + 2) 0 4 ≤ F)
    (hnext : ∀ m' : Mem ℝ,
      m.store.EqOff (Store.inBlock (L + 1) 0 4 ⊔ Store.inBlock (L + 2) 0 4) m'.store →
      m'.pos = m.pos →
      m'.store.readBlock (L + 1) 0 2 = some
        [(roundedGivensCoeffs M ⟨y₀, M.neg y₁⟩ ⟨M.neg x₀, x₁⟩).1.re,
          (roundedGivensCoeffs M ⟨y₀, M.neg y₁⟩ ⟨M.neg x₀, x₁⟩).1.im] →
      m'.store.readBlock (L + 1) 2 2 = some
        [(roundedGivensCoeffs M ⟨y₀, M.neg y₁⟩ ⟨M.neg x₀, x₁⟩).2.re,
          (roundedGivensCoeffs M ⟨y₀, M.neg y₁⟩ ⟨M.neg x₀, x₁⟩).2.im] →
      Writes .total I τ next ρ F P m') :
    Writes .total I τ
      (.seq (.call (Has.inj ScalarOp.copy) [] i₁ u₁) (.seq (.call (Has.inj ScalarOp.neg) [] i₂ u₂)
        (.seq (.call (Has.inj ScalarOp.neg) [] i₃ u₃) (.seq (.call (Has.inj ScalarOp.copy) [] i₄ u₄)
          (.seq (.frame ds as (coefficients (Op := O) (Tst := Q)).body) next))))) ρ F P m := by
  set G := Store.inBlock (L + 1) 0 4 ⊔ Store.inBlock (L + 2) 0 4
  have hU : ∀ k < 4, Store.inBlock (L + 2) k 1 ≤ G := fun k hk =>
    le_sup_of_le_right (Fp.inBlock_le_inBlock (by pomega) (by pomega))
  have K : ∀ {s s' : Store ℝ} {b o b' i : ℕ} {v : ℝ}, s.EqOff (Store.inBlock b o 1) s' →
      (b' ≠ b ∨ i ≠ o) → s.get b' i = some v → s'.get b' i = some v :=
    fun hf hne hv => (hf.2 _ _ (Store.not_inBlock_of (by pomega))).trans hv
  refine (writes_call_un (hS .copy) h₁ h₁' trivial hy₀ rfl (by pomega)).seq_le
    ((hU 0 (by pomega)).trans hF) ?_
  rintro m₁ hf₁ ⟨hp₁, hv₁⟩
  refine (writes_call_un (hS .neg) h₂ h₂' trivial (K hf₁ (by pomega) hy₁) rfl
    (by rw [hf₁.len_eq]; pomega)).seq_le ((hU 1 (by pomega)).trans hF) ?_
  rintro m₂ hf₂ ⟨hp₂, hv₂⟩
  refine (writes_call_un (hS .neg) h₃ h₃' trivial (K hf₂ (by pomega) (K hf₁ (by pomega) hx₀)) rfl
    (by rw [hf₂.len_eq, hf₁.len_eq]; pomega)).seq_le ((hU 2 (by pomega)).trans hF) ?_
  rintro m₃ hf₃ ⟨hp₃, hv₃⟩
  refine (writes_call_un (hS .copy) h₄ h₄' trivial
    (K hf₃ (by pomega) (K hf₂ (by pomega) (K hf₁ (by pomega) hx₁))) rfl
    (by rw [hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; pomega)).seq_le ((hU 3 (by pomega)).trans hF) ?_
  rintro m₄ hf₄ ⟨hp₄, hv₄⟩
  have hlen₄ : m₄.store.length = m.store.length :=
    hf₄.length_eq.trans (hf₃.length_eq.trans (hf₂.length_eq.trans hf₁.length_eq))
  have hCf₄ : m₄.store.len (L + 1) = 4 := by
    rw [hf₄.len_eq, hf₃.len_eq, hf₂.len_eq, hf₁.len_eq, hCf]
  have hcf : Fp.blocks [(L + 1, 0), (L + 1, 2)] [2, 2] ≤ Store.inBlock (L + 1) 0 4 := by
    intro b i hi
    simp [Fp.blocks, Store.inBlock] at hi ⊢
    omega
  refine (coefficients_writes_word (τ := τ) (m := m₄) (a := (L + 2, 0)) (b := (L + 2, 2))
    (c := (L + 1, 0)) (s := (L + 1, 2)) (u := ⟨y₀, M.neg y₁⟩) (v := ⟨M.neg x₀, x₁⟩) hS hC
    (Fp.disj_inBlock_of_le le_rfl) (K hf₄ (by pomega) (K hf₃ (by pomega) (K hf₂ (by pomega) hv₁)))
    (K hf₄ (by pomega) (K hf₃ (by pomega) hv₂)) (K hf₄ (by pomega) hv₃) hv₄ (by pomega)
    (by pomega)).frame_seq_le hd ha
    (by simp only [Mem.live_cons, Mem.live_nil, and_true, and_self, and_self_left]; pomega)
    ((hcf.trans le_sup_left).trans hF) ?_
  rintro m₅ hf₅ ⟨hp₅, hcs⟩
  refine hnext m₅ ?_ (by rw [hp₅, hp₄, hp₃, hp₂, hp₁])
    (Mem.readBlocks_cons_iff.mp hcs).1
    (Mem.readBlocks_cons_iff.mp (Mem.readBlocks_cons_iff.mp hcs).2).1
  exact ((((hf₁.mono (hU 0 (by pomega))).trans (hf₂.mono (hU 1 (by pomega)))).trans
    (hf₃.mono (hU 2 (by pomega)))).trans (hf₄.mono (hU 3 (by pomega)))).trans
    (hf₅.mono (hcf.trans le_sup_left))

end Steps

section Rotate

variable {O Q : Type} [Has ScalarOp O] [Has CmpTst Q]

omit [Has CmpTst Q] in
/-- **The rotations of one step of `RHess`**: with the coefficients in `Cf`, the rotation of the
entries $j, j + 1$ of the vector at `G`, then of the rows and the columns $j, j + 1$ of the matrix
at `a`; only `a`, `G` and the scratch `Tm` are written. -/
private theorem writes_rhessRotate {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {N L j : ℕ} (hj : j + 1 < N) {a : ℕ × ℕ}
    {B : Matrix (Fin N) (Fin N) ℂ} {v : Fin N → ℂ} {cs : ℂ × ℂ} {ds₆ ds₇ ds₈ : List IExp}
    {as₆ as₇ as₈ : List Operand} (hd₆ : IExp.evalList ρ.idx ds₆ = some [])
    (ha₆ : Operand.evalList ρ as₆ = some [(L + 1, 0), (L + 1, 2), (L, 2 * j), (L, 2 * j + 2),
      (L + 3, 0), (L, 2 * j), (L, 2 * j + 2)])
    (hd₇ : IExp.evalList ρ.idx ds₇ = some [N, j])
    (ha₇ : Operand.evalList ρ as₇ = some [a, (L + 1, 0), (L + 1, 2), a])
    (hd₈ : IExp.evalList ρ.idx ds₈ = some [N, j])
    (ha₈ : Operand.evalList ρ as₈ = some [a, (L + 1, 0), (L + 1, 2), a])
    (haL : a.1 < L) (hlen : m.store.length = L + 4) (hG : m.store.len L = 2 * N)
    (hTm : m.store.len (L + 3) = 10)
    (hc : m.store.readBlock (L + 1) 0 2 = some [cs.1.re, cs.1.im])
    (hs : m.store.readBlock (L + 1) 2 2 = some [cs.2.re, cs.2.im])
    (hB : HoldsMatrix a B m.store) (hV : HoldsMatrix (L, 0) (replicateCol (Fin 1) v) m.store) :
    Writes .total I τ
      (.seq (.frame ds₆ as₆ (rotateLeftWithScratch (Op := O) (Tst := Q)).body)
        (.seq (.frame ds₇ as₇ (rotateRows (Op := O) (Tst := Q)).body)
          (.frame ds₈ as₈ (rotateColumns (Op := O) (Tst := Q)).body))) ρ
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Fp.above L)
      (fun m' => m'.pos = m.pos ∧
        HoldsMatrix a (machineColRotation M ⟨j, by omega⟩ ⟨j + 1, hj⟩ cs.1 cs.2
          (machineRowRotation M ⟨j, by omega⟩ ⟨j + 1, hj⟩ cs.1 cs.2 B)) m'.store ∧
        HoldsMatrix (L, 0) (replicateCol (Fin 1) (vecRot M ⟨j, by omega⟩ ⟨j + 1, hj⟩ cs v))
          m'.store) m := by
  have hc0 := Store.get_of_readBlock hc (j := 0) (by norm_num) (0 : ℝ)
  have hc1 := Store.get_of_readBlock hc (j := 1) (by norm_num) (0 : ℝ)
  have hs0 := Store.get_of_readBlock hs (j := 0) (by norm_num) (0 : ℝ)
  have hs1 := Store.get_of_readBlock hs (j := 1) (by norm_num) (0 : ℝ)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, zero_add] at hc0 hc1 hs0 hs1
  obtain ⟨hx0, hx1⟩ := get_colVec hV ⟨j, by omega⟩
  obtain ⟨hy0, hy1⟩ := get_colVec hV ⟨j + 1, hj⟩
  simp only at hx0 hx1 hy0 hy1
  have habove : Fp.blocks [(L + 3, 0), (L, 2 * j), (L, 2 * j + 2)] [10, 2, 2] ≤
      Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Fp.above L := by
    intro b i hi
    simp [Fp.blocks, Store.inBlock] at hi
    exact Or.inr (show L ≤ b by omega)
  refine (writes_rotateLeftWithScratch_word (τ := τ) (m := m) (c := (L + 1, 0)) (s := (L + 1, 2))
    (x := (L, 2 * j)) (y := (L, 2 * j + 2)) (t := (L + 3, 0)) (cv := cs.1) (sv := cs.2)
    (xv := v ⟨j, by omega⟩) (yv := v ⟨j + 1, hj⟩) hS (by simp) (by simp) (by simp) (by simp)
    (Fp.disj_inBlock_of_le (by omega)) hc0 hc1 (by simpa using hs0) (by simpa using hs1) hx0
    (by simpa [Nat.add_assoc] using hx1)
    (by simpa [show 2 * (j + 1) = 2 * j + 2 by omega] using hy0)
    (by simpa [show 2 * (j + 1) + 1 = 2 * j + 2 + 1 by omega] using hy1) (by simp [hTm])
    (by simp [hG]; omega) (by simp [hG]; omega)).frame_seq_le hd₆ ha₆
    (by simp [Mem.Live, hlen]) habove ?_
  rintro m₁ hf₁ ⟨hp₁, hr₁⟩
  have hdA : Fp.Disj (Fp.blocks [(L + 3, 0), (L, 2 * j), (L, 2 * j + 2)] [10, 2, 2])
      (Store.inBlock a.1 a.2 (2 * (N * N))) := fun b i h1 h2 => by
    simp [Fp.blocks, Store.inBlock] at h1 h2; omega
  have hdC : ∀ o, Fp.Disj (Fp.blocks [(L + 3, 0), (L, 2 * j), (L, 2 * j + 2)] [10, 2, 2])
      (Store.inBlock (L + 1) o 2) := fun o b i h1 h2 => by
    simp [Fp.blocks, Store.inBlock] at h1 h2; omega
  have hB₁ := hB.of_eqOff hf₁ hdA
  have hc₁ := hf₁.keep (Store.readsOnly_readBlock _ _ _ _) (hdC 0) hc
  have hs₁ := hf₁.keep (Store.readsOnly_readBlock _ _ _ _) (hdC 2) hs
  have hx' := (Mem.readBlocks_cons_iff.mp hr₁).1
  have hy' := (Mem.readBlocks_cons_iff.mp (Mem.readBlocks_cons_iff.mp hr₁).2).1
  have hV₁ : HoldsMatrix (L, 0)
      (replicateCol (Fin 1) (vecRot M ⟨j, by omega⟩ ⟨j + 1, hj⟩ cs v)) m₁.store := by
    refine holdsMatrix_colVec fun r => ?_
    by_cases hri : (r : ℕ) = j
    · obtain rfl : r = ⟨j, Nat.lt_of_succ_lt hj⟩ := Fin.ext hri
      simp only [vecRot, if_true]
      exact ⟨by simpa using Store.get_of_readBlock hx' (j := 0) (by norm_num) (0 : ℝ),
        by simpa using Store.get_of_readBlock hx' (j := 1) (by norm_num) (0 : ℝ)⟩
    by_cases hrk : (r : ℕ) = j + 1
    · obtain rfl : r = ⟨j + 1, hj⟩ := Fin.ext hrk
      have hne : (⟨j + 1, hj⟩ : Fin N) ≠ ⟨j, by omega⟩ := Fin.ne_of_val_ne (by simp)
      simp only [vecRot, hne, if_false, if_true]
      refine ⟨?_, ?_⟩
      · simpa [show 2 * (j + 1) = 2 * j + 2 by ring] using
          Store.get_of_readBlock hy' (j := 0) (by norm_num) (0 : ℝ)
      · simpa [show 2 * (j + 1) + 1 = 2 * j + 2 + 1 by ring] using
          Store.get_of_readBlock hy' (j := 1) (by norm_num) (0 : ℝ)
    · have h1 : r ≠ ⟨j, by omega⟩ := fun h => hri (by rw [h])
      have h2 : r ≠ ⟨j + 1, hj⟩ := fun h => hrk (by rw [h])
      simp only [vecRot, h1, h2, if_false]
      obtain ⟨hr0, hr1⟩ := get_colVec hV r
      have hk : ∀ i : ℕ, (i = 2 * (r : ℕ) ∨ i = 2 * (r : ℕ) + 1) →
          m₁.store.get L i = m.store.get L i :=
        fun i hi => hf₁.2 _ _ (fun h => by
          simp [Fp.blocks, Store.inBlock] at h; pomega)
      exact ⟨(hk _ (Or.inl rfl)).trans hr0, (hk _ (Or.inr rfl)).trans hr1⟩
  have hdV : ∀ {F' : Fp}, F' = Store.inBlock a.1 a.2 (2 * (N * N)) →
      Fp.Disj F' (Store.inBlock L 0 (2 * (1 * N))) := fun hF' => by
    subst hF'; exact Fp.disj_inBlock_of_ne (by omega)
  have hcs : ∀ o, Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock (L + 1) o 2) :=
    fun _ => Fp.disj_inBlock_of_ne (by omega)
  have hlen₁ : m₁.store.length = L + 4 := hf₁.length_eq.trans hlen
  refine (rotateRows_writes_word (τ := τ) (k := j) hS hj hB₁ hc₁ hs₁ (hcs 0) (hcs 2)).frame_seq_le
    hd₇ ha₇ (by simp only [Mem.live_cons, Mem.live_nil, and_true, and_self_left]; pomega)
    le_sup_left ?_
  rintro m₂ hf₂ ⟨hp₂, hB₂⟩
  have hc₂ := hf₂.keep (Store.readsOnly_readBlock _ _ _ _) (hcs 0) hc₁
  have hs₂ := hf₂.keep (Store.readsOnly_readBlock _ _ _ _) (hcs 2) hs₁
  refine ((rotateColumns_writes_word (τ := τ) (k := j) hS hj hB₂ hc₂ hs₂ (hcs 0) (hcs 2)).in_frame
    hd₈ ha₈ (by simp only [Mem.live_cons, Mem.live_nil, and_true, and_self_left,
        hf₂.length_eq]; pomega)).mono
    le_sup_left ?_
  rintro m₃ hf₃ ⟨hp₃, hB₃⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hB₃,
    (hV₁.of_eqOff hf₂ (hdV rfl)).of_eqOff hf₃ (hdV rfl)⟩

end Rotate

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has CmpTst Q]

/-- `NLAlib.SmallEig.rhess` on a scalar machine with exact comparisons and draws that store the
tape entry: from $\mathbf{A}$ of order $N$ at `a`, it writes only the matrix, advances the position
by $2N$, and stores `NLAlib.SmallEig.rhessWord` of $\mathbf{A}$ and the $2N$ entries of the
stream `sG` at the start position. -/
theorem rhess_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) (hSmp : IsSample I) {sG N : ℕ} {τ : Tape ℝ} {μ : Mem ℝ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hl : μ.Live [a]) (hA : HoldsMatrix a A μ.store)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax) (h1 : 1 ≤ nmax)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] μ.store) (hj : LL.length + (N - 1) ≤ ns) (hw : N - 1 ≤ w)
    (hlgl : μ.Live [lg]) (hlga : lg.1 ≠ a.1) :
    Writes .total I τ (rhess (O := O) (Q := Q) sG).body (Env.frame [N, w, LL.length] [a, a, lg])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => μ'.pos = μ.pos + 2 * N ∧
        HoldsMatrix a (rhessWord M A fun j => τ (μ.pos + j) sG) μ'.store ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = N - 1 ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 2 < N) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] μ'.store) μ :=
  sorry

/-- **`RHess` is a backward-stable unitary similarity to a random direction**
([BanksGarzaVargasSrivastava2025, Proposition 5.3], deterministic part): on a machine with the
standard model at the unit roundoff $\boldsymbol{u}$, $M.\mathrm{lit}(0) = 0$ and
$100(n + 1)^2\boldsymbol{u} \le 1$, for $\mathbf{A}$ of order $n + 1$ and words $x$ whose vector
$\mathbf{g} = (x_{2i} + i x_{2i+1})_i$ is not zero, the stored $\widehat{\mathbf{H}}$
(`NLAlib.SmallEig.rhessWord`) is upper Hessenberg and there are a unitary $\mathbf{Q}$ and
$\lvert c\rvert = 1$ with
$$\|\mathbf{Q}\mathbf{e}_{n+1} - c\,\mathbf{g}/\|\mathbf{g}\|\| \le 60(n + 1)\boldsymbol{u},
  \qquad \|\widehat{\mathbf{H}} - \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}\|_2 \le
  200(n + 1)^2\boldsymbol{u}\,\|\mathbf{A}\|_2\,.$$ -/
theorem rhess_isPerturbedUnitarySimilar {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hzero : M.lit 0 = 0) {n : ℕ} (hnu : 100 * ((n : ℝ) + 1) ^ 2 * u ≤ 1)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (x : ℕ → ℝ) (hg : pairVector x (n + 1) ≠ 0) :
    IsUpperHessenberg (rhessWord M A x) ∧
      ∃ (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c : ℂ), HasOrthonormalCols Q ∧ ‖c‖ = 1 ∧
        ‖WithLp.toLp 2 ((fun k => Q k (Fin.last n)) -
          (c * ((‖WithLp.toLp 2 (pairVector x (n + 1))‖⁻¹ : ℝ) : ℂ)) • pairVector x (n + 1))‖ ≤
          60 * ((n : ℝ) + 1) * u ∧
        specNorm (rhessWord M A x - Qᴴ * A * Q) ≤ 200 * ((n : ℝ) + 1) ^ 2 * u * specNorm A := by
  have hu : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  set g := pairVector x (n + 1)
  set BV := (List.range n).foldl (fun Ag j => rotateToStepWord M j Ag) (A, g)
  have hrw : rhessWord M A x = hessenbergReduceLastWord M BV.1 := rfl
  have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hNu : ((n : ℝ) + 1) * u ≤ 1 / 100 := by
    nlinarith [mul_le_mul_of_nonneg_right (show (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 by nlinarith) hu]
  have hnu' : (n : ℝ) * u ≤ 1 / 100 := by nlinarith
  obtain ⟨hH, Q', hQ', hlast, hE⟩ :=
    hessenbergReduceLast_isPerturbedUnitarySimilar hM hzero hnu BV.1
  obtain ⟨U, hU, hB, hv, hz⟩ := rotInv_fold (M := M) hM hu (fun h2 => by
    have : (2 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h2
    nlinarith [mul_le_mul_of_nonneg_right (show (4 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 by nlinarith) hu])
    A g n (by omega)
  rw [hrw]
  obtain ⟨c, hc, hcv⟩ := rhess_phase hU hg hv hz hu hNu hnu'
  refine ⟨hH, Uᴴ * Q', c, hasOrthonormalCols_iff.mpr
    ((hU.conjTranspose.conjTranspose_mul_mul _ _).trans (hasOrthonormalCols_iff.mp hQ')), hc, ?_,
    rhess_matrix_bound hU hQ' hB hE hu hNu⟩
  have hcol : (fun k => (Uᴴ * Q') k (Fin.last n)) = Uᴴ *ᵥ Pi.single (Fin.last n) 1 := by
    ext r
    simp [Matrix.mul_apply, hlast, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hcol]
  exact hcv

/-- **`RHess` makes the last-row weights large** ([BanksGarzaVargasSrivastava2025,
Proposition 5.3], corrected: the anti-concentration is applied to the eigenvectors of the input,
fixed before the draw, its erratum P4): on a scalar machine with the standard model at the unit
roundoff $\boldsymbol{u}$, $M.\mathrm{lit}(0) = 0$ and exact comparisons, a measurable
interpretation reading the tape only in its windows whose draws store the tape entry, and a
stream `sG` with the standard real Gaussian law: let $\mathbf{A}$ of order $n + 1$ have
$\mathbf{A}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$, eigenvalues separated by $g > 0$ and
$\|\mathbf{A}\|_2 \le \Sigma$; let $s > 0$, $0 < \varphi' \le 1$,
$R \ge 2(\sqrt{n + 1} + 1) + \sqrt{2\log(1/\varphi')}$, and the precision conditions
$100(n + 1)^2\boldsymbol{u} \le 1$, $60(n + 1)\boldsymbol{u} \le s/(2R)$ and
$200(n + 1)^2\boldsymbol{u}\Sigma \le \min(g/(32(n + 1)B), sg/(1024(n + 1)B^2R))$. Then from
$\mathbf{A}$ at `a`, except with probability at most $(n + 1)s^2 + \varphi'$, the run writes only
the matrix and stores an upper Hessenberg perturbed unitary similarity $\widehat{\mathbf{H}}$ of
$\mathbf{A}$ with backward error $200(n + 1)^2\boldsymbol{u}\Sigma$ that has a diagonalization
$\mathbf{V}'$, $\mathbf{d}'$ with $\|\mathbf{V}'\|_2\|\mathbf{V}'^{-1}\|_2 \le 2B$, eigenvalues
separated by $g/2$, and every last-row weight at least $s^2/(64R^2B^2)$. -/
theorem rhess_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hzero : M.lit 0 = 0) (hC : IsCmp id I) (hSmp : IsSample I)
    {law : ℕ → Measure ℝ} {sG : ℕ} (hG : law sG = gaussianReal 0 1) {n : ℕ}
    {A V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {B g S s R φ' : ℝ}
    (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B)
    (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖) (hAS : specNorm A ≤ S) (hs : 0 < s)
    (hφ' : 0 < φ') (hφ'1 : φ' ≤ 1)
    (hR : 2 * (√((n : ℝ) + 1) + 1) + √(2 * Real.log φ'⁻¹) ≤ R)
    (hnu : 100 * ((n : ℝ) + 1) ^ 2 * u ≤ 1) (hus : 60 * ((n : ℝ) + 1) * u ≤ s / (2 * R))
    (huc : 200 * ((n : ℝ) + 1) ^ 2 * u * S ≤
      min (g / (32 * (n + 1) * B)) (s * g / (1024 * (n + 1) * B ^ 2 * R))) {a : ℕ × ℕ}
    (hL : IsIndexLit M I) (h1 : 1 ≤ n)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))} (hj : LL.length + n ≤ ns)
    (hw : n ≤ w) :
    PWrites law I (rhess (O := O) (Q := Q) sG).body (Env.frame [n + 1, w, LL.length] [a, a, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ => HoldsMatrix a A μ.store ∧ μ.Live [a] ∧
        HoldsSlottedLog lg ns w LL [] μ.store ∧ μ.Live [lg] ∧ lg.1 ≠ a.1)
      (fun μ' => ∃ (H V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d' : Fin (n + 1) → ℂ),
        HoldsMatrix a H μ'.store ∧ IsUpperHessenberg H ∧
        IsPerturbedUnitarySimilar A H (200 * ((n : ℝ) + 1) ^ 2 * u * S) ∧ IsUnit V' ∧
        H * V' = V' * Matrix.diagonal d' ∧ pseudoConditionNumber V' ≤ 2 * B ∧
        (∀ i j, i ≠ j → g / 2 ≤ ‖d' i - d' j‖) ∧
        ∀ i, s ^ 2 / (64 * R ^ 2 * B ^ 2) ≤ lastRowWeights V' i)
      ((n + 1) * s ^ 2 + φ') := sorry

/-- `NLAlib.SmallEig.rhess` terminates on every tape and every stored matrix. -/
theorem rhess_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) (hSmp : IsSample I) {sG N : ℕ} {τ : Tape ℝ} {μ : Mem ℝ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hl : μ.Live [a]) (hA : HoldsMatrix a A μ.store)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax) (h1 : 1 ≤ nmax)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] μ.store) (hj : LL.length + (N - 1) ≤ ns) (hw : N - 1 ≤ w)
    (hlgl : μ.Live [lg]) (hlga : lg.1 ≠ a.1) :
    Writes .total I τ (rhess (O := O) (Q := Q) sG).body (Env.frame [N, w, LL.length] [a, a, lg])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => ∃ H : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix a H μ'.store ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = N - 1 ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 2 < N) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] μ'.store) μ :=
  sorry

end Theorems

end NLAlib.SmallEig
