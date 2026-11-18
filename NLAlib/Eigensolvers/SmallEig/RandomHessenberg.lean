/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.RandomHessenbergWeights
public import NLAlib.Eigensolvers.HessenbergReduction
public import NLAlib.Matrix.FinitePrecision.GivensLogValidate
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

variable {O Q : Type} [Has ScalarOp O]

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

/-- **The words of one rotation of `RHess`**: the four words
$(\Re g_{j+1}, -\Im g_{j+1}, -\Re g_j, \Im g_j)$ into `Uv`; only `Uv` is written. -/
private theorem writes_rhessUv {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {F : Fp} {P : Mem ℝ → Prop}
    {L t : ℕ} {x₀ x₁ y₀ y₁ : ℝ} {i₁ u₁ i₂ u₂ i₃ u₃ i₄ u₄ : List Operand} {next : Stmt O Q}
    (h₁ : Operand.evalList ρ i₁ = some [(L, t + 2)])
    (h₁' : Operand.evalList ρ u₁ = some [(L + 2, 0)])
    (h₂ : Operand.evalList ρ i₂ = some [(L, t + 3)])
    (h₂' : Operand.evalList ρ u₂ = some [(L + 2, 1)])
    (h₃ : Operand.evalList ρ i₃ = some [(L, t)])
    (h₃' : Operand.evalList ρ u₃ = some [(L + 2, 2)])
    (h₄ : Operand.evalList ρ i₄ = some [(L, t + 1)])
    (h₄' : Operand.evalList ρ u₄ = some [(L + 2, 3)])
    (hx₀ : m.store.get L t = some x₀) (hx₁ : m.store.get L (t + 1) = some x₁)
    (hy₀ : m.store.get L (t + 2) = some y₀) (hy₁ : m.store.get L (t + 3) = some y₁)
    (hUv : m.store.len (L + 2) = 4) (hF : Store.inBlock (L + 2) 0 4 ≤ F)
    (hnext : ∀ m' : Mem ℝ, m.store.EqOff (Store.inBlock (L + 2) 0 4) m'.store →
      m'.pos = m.pos → m'.store.get (L + 2) 0 = some y₀ →
      m'.store.get (L + 2) 1 = some (M.neg y₁) → m'.store.get (L + 2) 2 = some (M.neg x₀) →
      m'.store.get (L + 2) 3 = some x₁ → Writes .total I τ next ρ F P m') :
    Writes .total I τ
      (.seq (.call (Has.inj ScalarOp.copy) [] i₁ u₁) (.seq (.call (Has.inj ScalarOp.neg) [] i₂ u₂)
        (.seq (.call (Has.inj ScalarOp.neg) [] i₃ u₃) (.seq (.call (Has.inj ScalarOp.copy) [] i₄ u₄)
          next)))) ρ F P m := by
  have hU : ∀ k < 4, Store.inBlock (L + 2) k 1 ≤ Store.inBlock (L + 2) 0 4 := fun k hk =>
    Fp.inBlock_le_inBlock (by pomega) (by pomega)
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
  exact hnext m₄ ((((hf₁.mono (hU 0 (by pomega))).trans (hf₂.mono (hU 1 (by pomega)))).trans
      (hf₃.mono (hU 2 (by pomega)))).trans (hf₄.mono (hU 3 (by pomega))))
    (by rw [hp₄, hp₃, hp₂, hp₁])
    (K hf₄ (by pomega) (K hf₃ (by pomega) (K hf₂ (by pomega) hv₁)))
    (K hf₄ (by pomega) (K hf₃ (by pomega) hv₂)) (K hf₄ (by pomega) hv₃) hv₄

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

section Loop

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

omit [Has IndexOp O] in
/-- **The rotation of one step of `RHess`** after its words: from the four words in `Uv`, the
rounded coefficients into `Cf`, then the rotation of the vector and of the matrix; the stored log
is kept. -/
private theorem rhess_rotate_step {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {N L j : ℕ} (hjN : j + 1 < N)
    {a lg : ℕ × ℕ} {B : Matrix (Fin N) (Fin N) ℂ} {v : Fin N → ℂ} {ns w : ℕ}
    {LL : List (Option (List GivensEntry))} {P : List GivensEntry}
    {as₅ as₆ as₇ as₈ : List Operand} {ds₅ ds₆ ds₇ ds₈ : List IExp}
    (hd₅ : IExp.evalList ρ.idx ds₅ = some [])
    (ha₅ : Operand.evalList ρ as₅ = some [(L + 2, 0), (L + 2, 2), (L + 1, 0), (L + 1, 2)])
    (hd₆ : IExp.evalList ρ.idx ds₆ = some [])
    (ha₆ : Operand.evalList ρ as₆ = some [(L + 1, 0), (L + 1, 2), (L, 2 * j),
      (L, 2 * j + 2), (L + 3, 0), (L, 2 * j), (L, 2 * j + 2)])
    (hd₇ : IExp.evalList ρ.idx ds₇ = some [N, j])
    (ha₇ : Operand.evalList ρ as₇ = some [a, (L + 1, 0), (L + 1, 2), a])
    (hd₈ : IExp.evalList ρ.idx ds₈ = some [N, j])
    (ha₈ : Operand.evalList ρ as₈ = some [a, (L + 1, 0), (L + 1, 2), a])
    (haL : a.1 < L) (hlgL : lg.1 < L) (hlga : lg.1 ≠ a.1) (hlen : m.store.length = L + 4)
    (hG : m.store.len L = 2 * N) (hCf : m.store.len (L + 1) = 4)
    (hTm : m.store.len (L + 3) = 10)
    (g₀ : m.store.get (L + 2) 0 = some (v ⟨j + 1, hjN⟩).re)
    (g₁ : m.store.get (L + 2) 1 = some (M.neg (v ⟨j + 1, hjN⟩).im))
    (g₂ : m.store.get (L + 2) 2 = some (M.neg (v ⟨j, by omega⟩).re))
    (g₃ : m.store.get (L + 2) 3 = some (v ⟨j, by omega⟩).im)
    (hB : HoldsMatrix a B m.store) (hW : HoldsMatrix (L, 0) (replicateCol (Fin 1) v) m.store)
    (hlg : HoldsSlottedLog lg ns w LL P m.store) :
    Writes .total I τ
      (.seq (.frame ds₅ as₅ (coefficients (Op := O) (Tst := Q)).body)
        (.seq (.frame ds₆ as₆ (rotateLeftWithScratch (Op := O) (Tst := Q)).body)
          (.seq (.frame ds₇ as₇ (rotateRows (Op := O) (Tst := Q)).body)
            (.frame ds₈ as₈ (rotateColumns (Op := O) (Tst := Q)).body)))) ρ
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) ⊔
        Fp.above L)
      (fun m' => m'.pos = m.pos ∧ m'.store.length = L + 4 ∧ m'.store.len L = 2 * N ∧
        m'.store.len (L + 1) = 4 ∧ m'.store.len (L + 2) = m.store.len (L + 2) ∧
        m'.store.len (L + 3) = 10 ∧ HoldsMatrix a (rotateToStepWord M j (B, v)).1 m'.store ∧
        HoldsMatrix (L, 0) (replicateCol (Fin 1) (rotateToStepWord M j (B, v)).2) m'.store ∧
        HoldsSlottedLog lg ns w LL P m'.store) m := by
  have hcf : Fp.blocks [(L + 1, 0), (L + 1, 2)] [2, 2] ≤ Store.inBlock (L + 1) 0 4 := by
    intro b i hi
    simp [Fp.blocks, Store.inBlock] at hi ⊢
    omega
  have hcF : Fp.blocks [(L + 1, 0), (L + 1, 2)] [2, 2] ≤ Store.inBlock a.1 a.2 (2 * (N * N)) ⊔
      Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) ⊔ Fp.above L :=
    hcf.trans fun b i hi => Or.inr (show L ≤ b by have := hi.1; omega)
  refine (coefficients_writes_word (τ := τ) (m := m) (a := (L + 2, 0)) (b := (L + 2, 2))
    (c := (L + 1, 0)) (s := (L + 1, 2))
    (u := ⟨(v ⟨j + 1, hjN⟩).re, M.neg (v ⟨j + 1, hjN⟩).im⟩)
    (v := ⟨M.neg (v ⟨j, by omega⟩).re, (v ⟨j, by omega⟩).im⟩) hS hC
    (Fp.disj_inBlock_of_le le_rfl) g₀ g₁ g₂ g₃ (by rw [hCf]; pomega)
    (by rw [hCf])).frame_seq_le hd₅ ha₅
    (by simp only [Mem.live_cons, Mem.live_nil, and_true]; refine ⟨?_, ?_, ?_, ?_⟩ <;> pomega)
    hcF ?_
  rintro m₃ hf₃ ⟨hp₃, hcs⟩
  have hdC : Fp.Disj (Store.inBlock (L + 1) 0 4) (Store.inBlock a.1 a.2 (2 * (N * N))) :=
    Fp.disj_inBlock_of_ne (by omega)
  have hB₃ := hB.of_eqOff hf₃ (hdC.mono hcf le_rfl)
  have hW₃ := hW.of_eqOff hf₃ ((Fp.disj_inBlock_of_ne (b := L + 1) (b' := L) (by omega)).mono
    hcf le_rfl)
  have hlg₃ : HoldsSlottedLog lg ns w LL P m₃.store :=
    hf₃.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _)
      ((Fp.disj_inBlock_of_ne (b := L + 1) (by omega)).mono hcf le_rfl) hlg
  refine (writes_rhessRotate hS hjN hd₆ ha₆ hd₇ ha₇ hd₈ ha₈ haL
    (hf₃.length_eq.trans hlen) (by rw [hf₃.len_eq, hG]) (by rw [hf₃.len_eq, hTm])
    (Mem.readBlocks_cons_iff.mp hcs).1
    (Mem.readBlocks_cons_iff.mp (Mem.readBlocks_cons_iff.mp hcs).2).1 hB₃ hW₃).mono
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right) ?_
  rintro m₄ hf₄ ⟨hp₄, hB₄, hW₄⟩
  have hAbove : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Fp.above L)
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) := by
    refine Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (Ne.symm hlga), fun b i hb hr => ?_⟩
    have := hr.1
    change L ≤ b at hb
    omega
  refine ⟨hp₄.trans hp₃, hf₄.length_eq.trans (hf₃.length_eq.trans hlen),
    by rw [hf₄.len_eq, hf₃.len_eq, hG], by rw [hf₄.len_eq, hf₃.len_eq, hCf],
    by rw [hf₄.len_eq, hf₃.len_eq], by rw [hf₄.len_eq, hf₃.len_eq, hTm], ?_, ?_,
    hf₄.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _) hAbove hlg₃⟩
  · simpa only [rotateToStepWord, dif_pos hjN] using hB₄
  · simp only [rotateToStepWord, dif_pos hjN]
    exact hW₄

/-- **One step of `RHess`**: the four words of the rotation into `Uv`, their entry
$(j, p, q)$ appended to the pending slot of the log, then the coefficients and the rotation of the
vector and of the matrix (`NLAlib.SmallEig.rotateToStepWord`). -/
private theorem rhess_step_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {N L j : ℕ} (hjN : j + 1 < N) (hjn : j ≤ nmax)
    {a lg : ℕ × ℕ} {B : Matrix (Fin N) (Fin N) ℂ} {v : Fin N → ℂ} {ns w : ℕ}
    {LL : List (Option (List GivensEntry))} {P : List GivensEntry}
    {i₁ u₁ i₂ u₂ i₃ u₃ i₄ u₄ asW as₅ as₆ as₇ as₈ : List Operand}
    {dsW ds₅ ds₆ ds₇ ds₈ : List IExp}
    (h₁ : Operand.evalList ρ i₁ = some [(L, 2 * j + 2)])
    (h₁' : Operand.evalList ρ u₁ = some [(L + 2, 0)])
    (h₂ : Operand.evalList ρ i₂ = some [(L, 2 * j + 3)])
    (h₂' : Operand.evalList ρ u₂ = some [(L + 2, 1)])
    (h₃ : Operand.evalList ρ i₃ = some [(L, 2 * j)])
    (h₃' : Operand.evalList ρ u₃ = some [(L + 2, 2)])
    (h₄ : Operand.evalList ρ i₄ = some [(L, 2 * j + 1)])
    (h₄' : Operand.evalList ρ u₄ = some [(L + 2, 3)])
    (hdW : IExp.evalList ρ.idx dsW = some [w, LL.length, P.length, j])
    (haW : Operand.evalList ρ asW = some [(L + 2, 0), (L + 2, 2), lg])
    (hd₅ : IExp.evalList ρ.idx ds₅ = some [])
    (ha₅ : Operand.evalList ρ as₅ = some [(L + 2, 0), (L + 2, 2), (L + 1, 0), (L + 1, 2)])
    (hd₆ : IExp.evalList ρ.idx ds₆ = some [])
    (ha₆ : Operand.evalList ρ as₆ = some [(L + 1, 0), (L + 1, 2), (L, 2 * j),
      (L, 2 * j + 2), (L + 3, 0), (L, 2 * j), (L, 2 * j + 2)])
    (hd₇ : IExp.evalList ρ.idx ds₇ = some [N, j])
    (ha₇ : Operand.evalList ρ as₇ = some [a, (L + 1, 0), (L + 1, 2), a])
    (hd₈ : IExp.evalList ρ.idx ds₈ = some [N, j])
    (ha₈ : Operand.evalList ρ as₈ = some [a, (L + 1, 0), (L + 1, 2), a])
    (haL : a.1 < L) (hlgL : lg.1 < L) (hlga : lg.1 ≠ a.1) (hlen : m.store.length = L + 4)
    (hG : m.store.len L = 2 * N) (hCf : m.store.len (L + 1) = 4) (hUv : m.store.len (L + 2) = 4)
    (hTm : m.store.len (L + 3) = 10) (hB : HoldsMatrix a B m.store)
    (hW : HoldsMatrix (L, 0) (replicateCol (Fin 1) v) m.store)
    (hlg : HoldsSlottedLog lg ns w LL P m.store) (hLn : LL.length < ns) (hPw : P.length < w) :
    Writes .total I τ
      (.seq (.call (Has.inj ScalarOp.copy) [] i₁ u₁)
        (.seq (.call (Has.inj ScalarOp.neg) [] i₂ u₂) (.seq (.call (Has.inj ScalarOp.neg) [] i₃ u₃)
          (.seq (.call (Has.inj ScalarOp.copy) [] i₄ u₄)
            (.seq (.frame dsW asW (slottedLogWrite (O := O) (Q := Q)).body)
              (.seq (.frame ds₅ as₅ (coefficients (Op := O) (Tst := Q)).body)
                (.seq (.frame ds₆ as₆ (rotateLeftWithScratch (Op := O) (Tst := Q)).body)
                  (.seq (.frame ds₇ as₇ (rotateRows (Op := O) (Tst := Q)).body)
                    (.frame ds₈ as₈ (rotateColumns (Op := O) (Tst := Q)).body))))))))) ρ
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) ⊔
        Fp.above L)
      (fun m' => m'.pos = m.pos ∧ m'.store.length = L + 4 ∧ m'.store.len L = 2 * N ∧
        m'.store.len (L + 1) = 4 ∧ m'.store.len (L + 2) = 4 ∧
        m'.store.len (L + 3) = 10 ∧ HoldsMatrix a (rotateToStepWord M j (B, v)).1 m'.store ∧
        HoldsMatrix (L, 0) (replicateCol (Fin 1) (rotateToStepWord M j (B, v)).2) m'.store ∧
        HoldsSlottedLog lg ns w LL (P ++ [rotateToStepEntry M j (B, v)]) m'.store) m := by
  set R := Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) with hRdef
  have hRA : ∀ {b o k : ℕ}, b ≠ lg.1 → Fp.Disj (Store.inBlock b o k) R :=
    fun hb => Fp.disj_inBlock_of_ne hb
  obtain ⟨hx0, hx1⟩ := get_colVec hW ⟨j, by omega⟩
  obtain ⟨hy0, hy1⟩ := get_colVec hW ⟨j + 1, hjN⟩
  refine writes_rhessUv hS (t := 2 * j) h₁ h₁' h₂ h₂' h₃ h₃' h₄ h₄' hx0 hx1
    (by simpa [show 2 * (j + 1) = 2 * j + 2 by ring] using hy0)
    (by simpa [show 2 * (j + 1) + 1 = 2 * j + 3 by ring] using hy1) hUv
    (fun b i hi => Or.inr (show L ≤ b by have := hi.1; omega)) ?_
  intro μ₁ hf₁ hp₁ g₀ g₁ g₂ g₃
  have hl₁ : μ₁.store.length = L + 4 := hf₁.length_eq.trans hlen
  have hlg₁ := hf₁.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _) (hRA (by omega)) hlg
  have hpb : μ₁.store.readBlock (L + 2) 0 2 = some [(⟨(v ⟨j + 1, hjN⟩).re,
      M.neg (v ⟨j + 1, hjN⟩).im⟩ : ℂ).re, (⟨(v ⟨j + 1, hjN⟩).re,
      M.neg (v ⟨j + 1, hjN⟩).im⟩ : ℂ).im] :=
    Store.readBlock_succ_of (Store.readBlock_one_of_get g₀) g₁
  have hqb : μ₁.store.readBlock (L + 2) 2 2 = some [(⟨M.neg (v ⟨j, by omega⟩).re,
      (v ⟨j, by omega⟩).im⟩ : ℂ).re, (⟨M.neg (v ⟨j, by omega⟩).re,
      (v ⟨j, by omega⟩).im⟩ : ℂ).im] :=
    Store.readBlock_succ_of (Store.readBlock_one_of_get g₂) g₃
  have hdUv : Fp.Disj R (Store.inBlock (L + 2) 0 2 ⊔ Store.inBlock (L + 2) 2 2) :=
    Fp.disj_sup_right.mpr ⟨(hRA (by omega)).symm, (hRA (by omega)).symm⟩
  have hlive : μ₁.Live [(L + 2, 0), (L + 2, 2), lg] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true]; refine ⟨?_, ?_, ?_⟩ <;> pomega
  refine ((slottedLogWrite_writes hS hL hNat (r := j) hjn hlg₁ hLn hPw hpb hqb hlive
    hdUv).and (slottedLogWrite_pos hS hL (r := j) hlg₁ hLn hPw hpb hqb hdUv)).frame_seq_le
    hdW haW hlive (le_sup_right.trans le_sup_left) ?_
  rintro μ₂ hf₂ ⟨⟨-, hlg₂⟩, hp₂⟩
  have K₂ : ∀ {i : ℕ} {x : ℝ}, μ₁.store.get (L + 2) i = some x →
      μ₂.store.get (L + 2) i = some x := fun hv =>
    hf₂.keep (Store.readsOnly_get _ _ _) (hRA (by omega)).symm hv
  have hdA : Fp.Disj (Store.inBlock (L + 2) 0 4 ⊔ R) (Store.inBlock a.1 a.2 (2 * (N * N))) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (by omega), Fp.disj_inBlock_of_ne hlga⟩
  have hdV : Fp.Disj (Store.inBlock (L + 2) 0 4 ⊔ R) (Store.inBlock L 0 (2 * (1 * N))) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (by omega), Fp.disj_inBlock_of_ne (by omega)⟩
  refine (rhess_rotate_step hS hC hjN hd₅ ha₅ hd₆ ha₆ hd₇ ha₇ hd₈ ha₈ haL hlgL hlga
    (hf₂.length_eq.trans hl₁) (by rw [hf₂.len_eq, hf₁.len_eq, hG])
    (by rw [hf₂.len_eq, hf₁.len_eq, hCf]) (by rw [hf₂.len_eq, hf₁.len_eq, hTm])
    (K₂ g₀) (K₂ g₁) (K₂ g₂) (K₂ g₃)
    ((hB.of_eqOff hf₁ (hdA.mono le_sup_left le_rfl)).of_eqOff hf₂ (hdA.mono le_sup_right le_rfl))
    ((hW.of_eqOff hf₁ (hdV.mono le_sup_left le_rfl)).of_eqOff hf₂ (hdV.mono le_sup_right le_rfl))
    hlg₂).mono le_rfl ?_
  rintro μ₄ - ⟨hp₄, hl₄, hG₄, hCf₄, hUv₄, hTm₄, hB₄, hW₄, hlg₄⟩
  exact ⟨hp₄.trans (hp₂.trans hp₁), hl₄, hG₄, hCf₄, by rw [hUv₄, hf₂.len_eq, hf₁.len_eq, hUv],
    hTm₄, hB₄, hW₄, by rw [rotateToStepEntry, dif_pos hjN]; exact hlg₄⟩

/-- **The loop, the validation and the reduction of `RHess`**: from $\mathbf{A}$ at `a`, the
vector $\mathbf{g}$ of the words $x$ at `G` and a log with closed slots `LL`, the $N - 1$
rotations (recorded as the pending entries), the validation of their slot and
`NLAlib.hessenbergReduceLast` store `NLAlib.SmallEig.rhessWord` at `a` and close $N - 1$ slots. -/
private theorem rhess_loop_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    (h1 : 1 ≤ nmax) {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {N L p : ℕ} (h2 : 2 ≤ N)
    (hN : N ≤ nmax + 1) {a lg : ℕ × ℕ} {A : Matrix (Fin N) (Fin N) ℂ} {x : ℕ → ℝ} {n : IExp}
    {ns w : ℕ} {LL : List (Option (List GivensEntry))}
    {i₁ u₁ i₂ u₂ i₃ u₃ i₄ u₄ asW as₅ as₆ as₇ as₈ asV asH : List Operand}
    {dsW ds₅ ds₆ ds₇ ds₈ dsV dsH : List IExp} (hn : n.eval ρ.idx = some (N - 1))
    (h₁ : ∀ j, Operand.evalList (ρ.pushIdx j) i₁ = some [(L, 2 * j + 2)])
    (h₁' : ∀ j, Operand.evalList (ρ.pushIdx j) u₁ = some [(L + 2, 0)])
    (h₂ : ∀ j, Operand.evalList (ρ.pushIdx j) i₂ = some [(L, 2 * j + 3)])
    (h₂' : ∀ j, Operand.evalList (ρ.pushIdx j) u₂ = some [(L + 2, 1)])
    (h₃ : ∀ j, Operand.evalList (ρ.pushIdx j) i₃ = some [(L, 2 * j)])
    (h₃' : ∀ j, Operand.evalList (ρ.pushIdx j) u₃ = some [(L + 2, 2)])
    (h₄ : ∀ j, Operand.evalList (ρ.pushIdx j) i₄ = some [(L, 2 * j + 1)])
    (h₄' : ∀ j, Operand.evalList (ρ.pushIdx j) u₄ = some [(L + 2, 3)])
    (hdW : ∀ j, IExp.evalList (ρ.pushIdx j).idx dsW = some [w, LL.length, j, j])
    (haW : ∀ j, Operand.evalList (ρ.pushIdx j) asW = some [(L + 2, 0), (L + 2, 2), lg])
    (hd₅ : ∀ j, IExp.evalList (ρ.pushIdx j).idx ds₅ = some [])
    (ha₅ : ∀ j, Operand.evalList (ρ.pushIdx j) as₅ =
      some [(L + 2, 0), (L + 2, 2), (L + 1, 0), (L + 1, 2)])
    (hd₆ : ∀ j, IExp.evalList (ρ.pushIdx j).idx ds₆ = some [])
    (ha₆ : ∀ j, Operand.evalList (ρ.pushIdx j) as₆ = some [(L + 1, 0), (L + 1, 2), (L, 2 * j),
      (L, 2 * j + 2), (L + 3, 0), (L, 2 * j), (L, 2 * j + 2)])
    (hd₇ : ∀ j, IExp.evalList (ρ.pushIdx j).idx ds₇ = some [N, j])
    (ha₇ : ∀ j, Operand.evalList (ρ.pushIdx j) as₇ = some [a, (L + 1, 0), (L + 1, 2), a])
    (hd₈ : ∀ j, IExp.evalList (ρ.pushIdx j).idx ds₈ = some [N, j])
    (ha₈ : ∀ j, Operand.evalList (ρ.pushIdx j) as₈ = some [a, (L + 1, 0), (L + 1, 2), a])
    (hdV : IExp.evalList ρ.idx dsV = some [w, LL.length])
    (haV : Operand.evalList ρ asV = some [lg])
    (hdH : IExp.evalList ρ.idx dsH = some [N, w, LL.length + 1])
    (haH : Operand.evalList ρ asH = some [a, a, lg])
    (haL : a.1 < L) (hlgL : lg.1 < L) (hlga : lg.1 ≠ a.1) (hlen : m.store.length = L + 4)
    (hG : m.store.len L = 2 * N) (hCf : m.store.len (L + 1) = 4) (hUv : m.store.len (L + 2) = 4)
    (hTm : m.store.len (L + 3) = 10) (hA : HoldsMatrix a A m.store)
    (hV : HoldsMatrix (L, 0) (replicateCol (Fin 1) (pairVector x N)) m.store) (hp : m.pos = p)
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + (N - 1) ≤ ns)
    (hw : N - 1 ≤ w) :
    Writes .total I τ
      (.seq (.loop n (.seq (.call (Has.inj ScalarOp.copy) [] i₁ u₁)
        (.seq (.call (Has.inj ScalarOp.neg) [] i₂ u₂) (.seq (.call (Has.inj ScalarOp.neg) [] i₃ u₃)
          (.seq (.call (Has.inj ScalarOp.copy) [] i₄ u₄)
            (.seq (.frame dsW asW (slottedLogWrite (O := O) (Q := Q)).body)
              (.seq (.frame ds₅ as₅ (coefficients (Op := O) (Tst := Q)).body)
                (.seq (.frame ds₆ as₆ (rotateLeftWithScratch (Op := O) (Tst := Q)).body)
                  (.seq (.frame ds₇ as₇ (rotateRows (Op := O) (Tst := Q)).body)
                    (.frame ds₈ as₈ (rotateColumns (Op := O) (Tst := Q)).body))))))))))
        (.seq (.frame dsV asV (slottedLogValidate (O := O) (Q := Q)).body)
          (.frame dsH asH (hessenbergReduceLast (O := O) (Q := Q)).body))) ρ
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) ⊔
        Fp.above L)
      (fun m' => m'.pos = p ∧ HoldsMatrix a (rhessWord M A x) m'.store ∧
        HoldsSlottedLog lg ns w (LL ++ (rhessSlots M A x).map some) [] m'.store)
      m := by
  set F := Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) ⊔
    Fp.above L with hFdef
  set R := Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) with hRdef
  have hRF : R ≤ F := le_sup_right.trans le_sup_left
  have hAF : Store.inBlock a.1 a.2 (2 * (N * N)) ≤ F := le_sup_left.trans le_sup_left
  have hRA : ∀ {b o k : ℕ}, b ≠ lg.1 → Fp.Disj (Store.inBlock b o k) R :=
    fun hb => Fp.disj_inBlock_of_ne hb
  set X : ℕ → Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) := fun k =>
    (List.range k).foldl (fun Ag j => rotateToStepWord M j Ag) (A, pairVector x N)
  set Inv : ℕ → Mem ℝ → Prop := fun k μ => μ.pos = p ∧ μ.store.length = L + 4 ∧
    μ.store.len L = 2 * N ∧ μ.store.len (L + 1) = 4 ∧ μ.store.len (L + 2) = 4 ∧
    μ.store.len (L + 3) = 10 ∧ HoldsMatrix a (X k).1 μ.store ∧
    HoldsMatrix (L, 0) (replicateCol (Fin 1) (X k).2) μ.store ∧
    HoldsSlottedLog lg ns w LL (rotateToEntries M A (pairVector x N) k) μ.store
  have hPl : ∀ k, (rotateToEntries M A (pairVector x N) k).length = k := fun k => by
    simp [rotateToEntries]
  refine (writes_loop (N := N - 1) hn (fun _ => F) (fun _ _ => le_rfl) Inv
    ⟨hp, hlen, hG, hCf, hUv, hTm, hA, hV, hlog⟩ ?_).seq_le le_rfl ?_
  · rintro j hj μ - ⟨hp', hl', hG', hCf', hUv', hTm', hB, hW, hlg⟩
    have hjN : j + 1 < N := by omega
    refine (rhess_step_writes hS hC hL hNat hjN (by omega) (h₁ j) (h₁' j) (h₂ j) (h₂' j)
      (h₃ j) (h₃' j) (h₄ j) (h₄' j) (by rw [hdW j, hPl]) (haW j) (hd₅ j) (ha₅ j) (hd₆ j)
      (ha₆ j) (hd₇ j) (ha₇ j) (hd₈ j) (ha₈ j) haL hlgL hlga hl' hG' hCf' hUv' hTm' hB hW hlg
      (by omega) (by rw [hPl]; omega)).mono le_rfl ?_
    rintro μ' - ⟨hp₄, hl₄, hG₄, hCf₄, hUv₄, hTm₄, hB₄, hW₄, hlg₄⟩
    have hX : X (j + 1) = rotateToStepWord M j (X j) := by
      simp only [X, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨hp₄.trans hp', hl₄, hG₄, hCf₄, hUv₄, hTm₄, by rw [hX]; exact hB₄,
      by rw [hX]; exact hW₄, ?_⟩
    rw [rotateToEntries_succ]
    exact hlg₄
  · rintro μ - ⟨hp', hl', -, -, -, -, hB, -, hlg⟩
    have hLn : LL.length < ns := by omega
    refine ((slottedLogValidate_writes_of_exactNat (O := O) (Q := Q) (τ := τ) hL
      (hNat.mono h1) hlg hLn).in_frame hdV haV
      (by simp only [Mem.live_cons, Mem.live_nil, and_true]; pomega)).seq_le hRF ?_
    rintro μ₁ hf₁ ⟨hp₁, hlg₁⟩
    have hB₁ := hB.of_eqOff hf₁ (hRA (Ne.symm hlga)).symm
    refine ((hessenbergReduceLast_writes_word
      (L := LL ++ [some (rotateToEntries M A (pairVector x N) (N - 1))]) hS hC hL hNat h1 hN hlg₁
      (by simp; omega) (by omega)
      (by simp only [Mem.live_cons, Mem.live_nil, and_true, hf₁.length_eq]; constructor <;> pomega)
      hB₁ (hRA (Ne.symm hlga))).in_frame (by simpa using hdH) haH
      (by simp only [Mem.live_cons, Mem.live_nil, and_true, hf₁.length_eq]
          refine ⟨?_, ?_, ?_⟩ <;> pomega)).mono (sup_le hAF hRF) ?_
    rintro μ₂ - ⟨hp₂, hW₂, hlg₂⟩
    exact ⟨hp₂.trans (hp₁.trans hp'), hW₂, by simpa [rhessSlots] using hlg₂⟩

end Loop

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has CmpTst Q]

/-- `NLAlib.SmallEig.rhess` on a scalar machine with exact comparisons, index literals, exact
natural literals up to $n_{\max} \ge N - 1$ and draws that store the tape entry: from
$\mathbf{A}$ of order $2 \le N$ at `a` and a log with closed slots `LL` and room for $N - 1$ more,
it writes only the matrix and the log, advances the position by $2N$, stores
`NLAlib.SmallEig.rhessWord` of $\mathbf{A}$ and the $2N$ entries of the stream `sG` at the start
position, and closes the $N - 1$ accepted slots `NLAlib.SmallEig.rhessSlots` of $\mathbf{A}$ and
those entries. -/
theorem rhess_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) (hSmp : IsSample I) {sG N : ℕ} {τ : Tape ℝ} {μ : Mem ℝ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hl : μ.Live [a]) (hA : HoldsMatrix a A μ.store)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax) (h1 : 1 ≤ nmax)
    (h2 : 2 ≤ N) (hN : N ≤ nmax + 1)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] μ.store) (hj : LL.length + (N - 1) ≤ ns) (hw : N - 1 ≤ w)
    (hlgl : μ.Live [lg]) (hlga : lg.1 ≠ a.1) :
    Writes .total I τ (rhess (O := O) (Q := Q) sG).body (Env.frame [N, w, LL.length] [a, a, lg])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => μ'.pos = μ.pos + 2 * N ∧
        HoldsMatrix a (rhessWord M A fun j => τ (μ.pos + j) sG) μ'.store ∧
        HoldsSlottedLog lg ns w (LL ++ (rhessSlots M A fun j => τ (μ.pos + j) sG).map some) []
          μ'.store) μ := by
  have hal : a.1 < μ.store.length := hl a (by simp)
  have hlgl' : lg.1 < μ.store.length := hlgl lg (by simp)
  unfold rhess
  change Writes .total I τ (Stmt.allocs [.const 2 * .var 0, .const 4, .const 4, .const 10] _)
    _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2 * N, 4, 4, 10]) rfl
    (fun hBelow ⟨hp, hW, hlog'⟩ => ⟨hp, hW.of_below hBelow hal,
      hBelow.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _)
        (fun b i g => by rw [g.1]; exact hlgl') hlog'⟩) ?_
  intro s₁ hlen hlens hBelow
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  have hG : s₁.len L = 2 * N := by simpa using hlens 0 (by simp)
  have hCf : s₁.len (L + 1) = 4 := by simpa using hlens 1 (by simp)
  have hUv : s₁.len (L + 2) = 4 := by simpa using hlens 2 (by simp)
  have hTm : s₁.len (L + 3) = 10 := by simpa using hlens 3 (by simp)
  refine (gaussDraws_writes (O := O) (Q := Q) hSmp (sG := sG) (m := 2 * N) (τ := τ)
    (μ := ⟨s₁, μ.pos⟩) (g := (L, 0)) (by simp [Mem.Live]; omega) (by simp [hG])).frame_seq_le
    rfl rfl (by simp [Mem.Live]; omega) (fun b i hi => Or.inr (hi.1 ▸ le_rfl)) ?_
  rintro m₁ hf₁ ⟨hp₁, hr₁⟩
  have hV₁ : HoldsMatrix (L, 0)
      (replicateCol (Fin 1) (pairVector (fun j => τ (μ.pos + j) sG) N)) m₁.store :=
    holdsMatrix_colVec fun i => ⟨by
      simpa [pairVector, Tape.window, show 2 * (i : ℕ) < 2 * N by omega] using
        Store.get_of_readBlock hr₁ (j := 2 * i) (by omega) (0 : ℝ), by
      simpa [pairVector, Tape.window, show 2 * (i : ℕ) + 1 < 2 * N by omega] using
        Store.get_of_readBlock hr₁ (j := 2 * i + 1) (by omega) (0 : ℝ)⟩
  have hA₁ : HoldsMatrix a A m₁.store :=
    (hA.of_below hBelow hal).of_eqOff hf₁ (Fp.disj_inBlock_of_ne (by omega))
  have hlog₁ : HoldsSlottedLog lg ns w LL [] m₁.store :=
    hf₁.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _) (Fp.disj_inBlock_of_ne (by omega))
      (hBelow.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _)
        (fun b i g => by rw [g.1]; exact hlgl') hlog)
  exact rhess_loop_writes hS hC hL hNat h1 h2 hN rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl (by omega)
    (by omega) hlga (by rw [hf₁.length_eq]; exact hlen) (by rw [hf₁.len_eq]; exact hG)
    (by rw [hf₁.len_eq]; exact hCf) (by rw [hf₁.len_eq]; exact hUv)
    (by rw [hf₁.len_eq]; exact hTm) hA₁ hV₁ hp₁ hlog₁ hj hw

/-- **`RHess` is a backward-stable unitary similarity to a random direction, by the unitary of
its log** ([BanksGarzaVargasSrivastava2025, Proposition 5.3], deterministic part): on a machine
with the standard model at the unit roundoff $\boldsymbol{u}$, $M.\mathrm{lit}(0) = 0$ and
$100(n + 1)^2\boldsymbol{u} \le 1$, for $\mathbf{A}$ of order $n + 1$ and words $x$ whose vector
$\mathbf{g} = (x_{2i} + i x_{2i+1})_i$ is not zero, the stored $\widehat{\mathbf{H}}$
(`NLAlib.SmallEig.rhessWord`) is upper Hessenberg, and the unitary $\mathbf{Q}$ of the recorded
entries (`NLAlib.givensLog` of `NLAlib.SmallEig.rhessSlots`) has, for some $\lvert c\rvert = 1$,
$$\|\mathbf{Q}\mathbf{e}_{n+1} - c\,\mathbf{g}/\|\mathbf{g}\|\| \le 60(n + 1)\boldsymbol{u},
  \qquad \|\widehat{\mathbf{H}} - \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}\|_2 \le
  200(n + 1)^2\boldsymbol{u}\,\|\mathbf{A}\|_2\,.$$ -/
theorem rhess_isPerturbedUnitarySimilar {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hzero : M.lit 0 = 0) {n : ℕ} (hnu : 100 * ((n : ℝ) + 1) ^ 2 * u ≤ 1)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (x : ℕ → ℝ) (hg : pairVector x (n + 1) ≠ 0) :
    IsUpperHessenberg (rhessWord M A x) ∧
      HasOrthonormalCols (givensLog (n + 1) (rhessSlots M A x).flatten) ∧
      ∃ c : ℂ, ‖c‖ = 1 ∧
        ‖WithLp.toLp 2 ((fun k => givensLog (n + 1) (rhessSlots M A x).flatten k (Fin.last n)) -
          (c * ((‖WithLp.toLp 2 (pairVector x (n + 1))‖⁻¹ : ℝ) : ℂ)) • pairVector x (n + 1))‖ ≤
          60 * ((n : ℝ) + 1) * u ∧
        specNorm (rhessWord M A x - (givensLog (n + 1) (rhessSlots M A x).flatten)ᴴ * A *
          givensLog (n + 1) (rhessSlots M A x).flatten) ≤
          200 * ((n : ℝ) + 1) ^ 2 * u * specNorm A := by
  have hu : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  set g := pairVector x (n + 1)
  set BV := (List.range n).foldl (fun Ag j => rotateToStepWord M j Ag) (A, g)
  have hrw : rhessWord M A x = hessenbergReduceLastWord M BV.1 := rfl
  have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hNu : ((n : ℝ) + 1) * u ≤ 1 / 100 := by
    nlinarith [mul_le_mul_of_nonneg_right (show (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 by nlinarith) hu]
  have hnu' : (n : ℝ) * u ≤ 1 / 100 := by nlinarith
  obtain ⟨hH, hlast, hQ', E, hE₀, he⟩ :=
    hessenbergReduceLast_isPerturbedUnitarySimilarBy hM hzero hnu BV.1
  set Q' := givensLog (n + 1) (hessenbergReduceLastSlots M BV.1).flatten
  have hE : specNorm (hessenbergReduceLastWord M BV.1 - Q'ᴴ * BV.1 * Q') ≤
      50 * ((n : ℝ) + 1) ^ 2 * u * specNorm BV.1 := by
    rw [he, Matrix.mul_add, Matrix.add_mul, add_sub_cancel_left,
      hQ'.specNorm_conjTranspose_mul_mul]
    exact hE₀
  set U := (givensLog (n + 1) (rotateToEntries M A g n))ᴴ
  obtain ⟨hU, hB, hv, hz⟩ := rotInv_fold (M := M) hM hu (fun h2 => by
    have : (2 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h2
    nlinarith [mul_le_mul_of_nonneg_right (show (4 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 by nlinarith) hu])
    A g n (by omega)
  have hQ : givensLog (n + 1) (rhessSlots M A x).flatten = Uᴴ * Q' := by
    simp only [U, Matrix.conjTranspose_conjTranspose, Q', rhessSlots, List.flatten_cons,
      givensLog_append]
    rfl
  rw [hrw, hQ]
  obtain ⟨c, hc, hcv⟩ := rhess_phase hU hg hv hz hu hNu hnu'
  refine ⟨hH, hasOrthonormalCols_iff.mpr
    ((hU.conjTranspose.conjTranspose_mul_mul _ _).trans (hasOrthonormalCols_iff.mp hQ')), c, hc,
    ?_, rhess_matrix_bound hU hQ' hB hE hu hNu⟩
  have hcol : (fun k => (Uᴴ * Q') k (Fin.last n)) = Uᴴ *ᵥ Pi.single (Fin.last n) 1 := by
    ext r
    simp [Matrix.mul_apply, hlast, Q', Matrix.mulVec, dotProduct, Pi.single_apply]
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
the matrix and the log, closes $n$ accepted slots of the log (planes below $n$), and stores an
upper Hessenberg perturbed unitary similarity $\widehat{\mathbf{H}}$ of $\mathbf{A}$ **by the
exact unitary of the slots' entries** (`NLAlib.givensLog`) with backward error
$200(n + 1)^2\boldsymbol{u}\Sigma$ that has a diagonalization
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
    (hL : IsIndexLit M I) (h1 : 1 ≤ n) {nmax : ℕ} (hNat : IsExactNatLit id M nmax) (hn : n ≤ nmax)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))} (hj : LL.length + n ≤ ns)
    (hw : n ≤ w) :
    PWrites law I (rhess (O := O) (Q := Q) sG).body (Env.frame [n + 1, w, LL.length] [a, a, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ => HoldsMatrix a A μ.store ∧ μ.Live [a] ∧
        HoldsSlottedLog lg ns w LL [] μ.store ∧ μ.Live [lg] ∧ lg.1 ≠ a.1)
      (fun μ' => ∃ (H V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d' : Fin (n + 1) → ℂ)
        (Ls : List (Option (List GivensEntry))),
        HoldsMatrix a H μ'.store ∧ Ls.length = n ∧ (∀ e ∈ slotEntries w Ls, e.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns w (LL ++ Ls) [] μ'.store ∧ IsUpperHessenberg H ∧
        IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries w Ls)) A H
          (200 * ((n : ℝ) + 1) ^ 2 * u * S) ∧ IsUnit V' ∧
        H * V' = V' * Matrix.diagonal d' ∧ pseudoConditionNumber V' ≤ 2 * B ∧
        (∀ i j, i ≠ j → g / 2 ≤ ‖d' i - d' j‖) ∧
        ∀ i, s ^ 2 / (64 * R ^ 2 * B ^ 2) ≤ lastRowWeights V' i)
      ((n + 1) * s ^ 2 + φ') := by
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hu : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  refine PWrites.of_window (s := sG) (W := (n + 1) * 2) (Bad := fun _ => rhessBad V s R)
    (measurable_snd (measurableSet_rhessBad V s R))
    (fun _ _ => by rw [hG]; exact measureReal_rhessBad_le hV hs hφ' hφ'1 hR) ?_
  rintro μ τ ⟨hAμ, hl, hlog, hlgl, hlga⟩ hgood
  refine (rhess_writes_word hS hC hSmp hl hAμ hL hNat (by omega) (by omega) (by omega) hlog
    (by simpa using hj) (by simpa using hw) hlgl hlga).mono le_rfl ?_
  rintro μ' - ⟨-, hW', hlg'⟩
  set x := Tape.windowFn τ sG μ.pos ((n + 1) * 2)
  set gv := pairVector (fun j => τ (μ.pos + j) sG) (n + 1)
  have hgv : winVec (n + 1) x = gv := winVec_windowFn (n + 1) τ sG μ.pos
  simp only [rhessBad, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
    not_le] at hgood
  obtain ⟨hdir, hnorm⟩ := hgood
  rw [← norm_winVec, hgv] at hnorm
  -- the overlaps with the drawn direction
  have hgi : ∀ i, s * ‖WithLp.toLp 2 (fun k => V k i)‖ < ‖star gv ⬝ᵥ (fun k => V k i)‖ := by
    intro i
    have h := hdir i
    have e : ‖star (fun k => V k i) ⬝ᵥ gv‖ = ‖star gv ⬝ᵥ (fun k => V k i)‖ := by
      rw [← norm_star (star (fun k => V k i) ⬝ᵥ gv)]
      congr 1
      exact (Matrix.star_dotProduct gv (fun k => V k i)).symm
    rw [hgv, unitCol, star_smul, smul_dotProduct, smul_eq_mul, norm_mul, norm_star,
      Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), e,
      inv_mul_eq_div, lt_div_iff₀ (norm_col_pos hV i)] at h
    exact h
  have hg0 : gv ≠ 0 := by
    rintro h0
    have h := hgi 0
    rw [h0, star_zero, zero_dotProduct, norm_zero] at h
    nlinarith [norm_col_pos hV 0]
  have hgpos : 0 < ‖WithLp.toLp 2 gv‖ :=
    norm_pos_iff.mpr fun h => hg0 (by simpa using congrArg WithLp.ofLp h)
  obtain ⟨hH, hQ, c, hc, hq, hE⟩ := rhess_isPerturbedUnitarySimilar hM hzero hnu A _ hg0
  set Ls := rhessSlots M A fun j => τ (μ.pos + j) sG
  set Qm := givensLog (n + 1) Ls.flatten
  have hqv : ∀ i, s / (2 * R) * ‖WithLp.toLp 2 (fun k => V k i)‖ ≤
      ‖star (fun k => Qm k (Fin.last n)) ⬝ᵥ (fun k => V k i)‖ := fun i =>
    le_norm_star_dotProduct_of_near hc hs.le hR0 hgpos hnorm.le (hgi i).le (hq.trans hus)
  have hEs : specNorm (rhessWord M A (fun j => τ (μ.pos + j) sG) - Qmᴴ * A * Qm) ≤
      200 * ((n : ℝ) + 1) ^ 2 * u * S :=
    hE.trans (mul_le_mul_of_nonneg_left hAS (by positivity))
  obtain ⟨V', d', hV', hHV', hκ', hgap', hw'⟩ :=
    rhess_class hV hAV hκ hg hgap hs hR0 hQ hqv hEs huc
  obtain ⟨hLs, hpl⟩ := rhessSlots_spec M (show 2 ≤ n + 1 by omega) A
    (fun j => τ (μ.pos + j) sG) w
  refine ⟨_, V', d', Ls.map some, hW', by simpa using hLs, hpl, hlg', hH, ?_, hV', hHV', hκ',
    hgap', hw'⟩
  rw [givensLog_slotEntries_map_some]
  exact IsPerturbedUnitarySimilarBy.of_specNorm_sub_le hQ hEs

/-- `NLAlib.SmallEig.rhess` terminates on every tape and every stored matrix. -/
theorem rhess_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) (hSmp : IsSample I) {sG N : ℕ} {τ : Tape ℝ} {μ : Mem ℝ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hl : μ.Live [a]) (hA : HoldsMatrix a A μ.store)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax) (h1 : 1 ≤ nmax)
    (h2 : 2 ≤ N) (hN : N ≤ nmax + 1)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] μ.store) (hj : LL.length + (N - 1) ≤ ns) (hw : N - 1 ≤ w)
    (hlgl : μ.Live [lg]) (hlga : lg.1 ≠ a.1) :
    Writes .total I τ (rhess (O := O) (Q := Q) sG).body (Env.frame [N, w, LL.length] [a, a, lg])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => ∃ H : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix a H μ'.store ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = N - 1 ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < N) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] μ'.store)
              μ :=
  (rhess_writes_word hS hC hSmp hl hA hL hNat h1 h2 hN hlog hj hw hlgl hlga).mono le_rfl
    fun _ _ h => ⟨_, h.2.1, _, by simpa using (rhessSlots_spec M h2 A _ w).1,
      (rhessSlots_spec M h2 A _ w).2, h.2.2⟩

end Theorems

end NLAlib.SmallEig
