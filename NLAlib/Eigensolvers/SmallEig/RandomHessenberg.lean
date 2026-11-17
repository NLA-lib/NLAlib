/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.HessenbergReduction
public import NLAlib.Eigensolvers.SmallEig.Draws
public import NLAlib.Matrix.Perturbation.EigenvalueBackward
public import NLAlib.Matrix.QRIteration.EigenvectorWeights
public import NLAlib.Ops.Logic.Probabilistic
public import NLAlib.RandomMatrix.Gaussian.Complex.LeastSingularValue

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
* `NLAlib.SmallEig.rhessWord`: the matrix it stores on a machine.

## Main results

* `NLAlib.SmallEig.rhess_writes_word`, `NLAlib.SmallEig.rhess_isPerturbedUnitarySimilar`,
  `NLAlib.SmallEig.rhess_pwrites`, `NLAlib.SmallEig.rhess_terminates`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has SampleOp O] [Has CmpTst Q]

/-- **The random Hessenberg form** ([BanksGarzaVargasSrivastava2025, Proposition 5.3], with a
Gaussian direction and rotations): draw $2N$ words of the stream `sG` as a complex vector
$\mathbf{g}$; for $j < N - 1$, the Givens coefficients of $(\bar g_{j+1}, -\bar g_j)$, the rotation
of the entries $j, j + 1$ of $\mathbf{g}$ (which zeros entry $j$), and the same rotation of the
rows and the columns $j, j + 1$ of `A`; then `NLAlib.hessenbergReduceLast`. The interface is
`[N] (A) → (A)`; the vector, the coefficients and the scratch are scoped.
Algorithm: small-eig -/
def rhess (sG : ℕ) : Impl O Q := opsImpl% [N] (A) → (A) {
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
    run (coefficients (Op := O) (Tst := Q)).body [] (Uv, Uv[2], Cf, Cf[2]);
    run (rotateLeftWithScratch (Op := O) (Tst := Q)).body []
      (Cf, Cf[2], G[2 * j], G[2 * j + 2], Tm, G[2 * j], G[2 * j + 2]);
    run (rotateRows (Op := O) (Tst := Q)).body [N, j] (A, Cf, Cf[2], A);
    run (rotateColumns (Op := O) (Tst := Q)).body [N, j] (A, Cf, Cf[2], A)
  };
  run (hessenbergReduceLast (O := O) (Q := Q)).body [N] (A, A)
}

end Program

/-- The complex vector of $2N$ real words, $(x_{2i} + i x_{2i+1})_{i < N}$. -/
def pairVector (x : ℕ → ℝ) (N : ℕ) : Fin N → ℂ := fun i => ⟨x (2 * i), x (2 * i + 1)⟩

/-- One rotation of `NLAlib.SmallEig.rhess` on a machine: the rounded coefficients of
$(\bar g_{j+1}, -\bar g_j)$, the rounded rotation of the entries $j, j + 1$ of $\mathbf{g}$, and of
the rows, then the columns, $j, j + 1$ of $\mathbf{A}$; the identity when $j + 1 \ge N$. -/
noncomputable def rotateToStepWord (M : Machine ℝ) {N : ℕ} (j : ℕ)
    (Ag : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ)) : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) :=
  if h : j + 1 < N then
    let i : Fin N := ⟨j, by omega⟩
    let k : Fin N := ⟨j + 1, h⟩
    let cs := roundedGivensCoeffs M ⟨(Ag.2 k).re, M.neg (Ag.2 k).im⟩
      ⟨M.neg (Ag.2 i).re, (Ag.2 i).im⟩
    (machineColRotation M i k cs.1 cs.2 (machineRowRotation M i k cs.1 cs.2 Ag.1),
      fun r => if r = i then linearComplex M cs.1 cs.2 (Ag.2 i) (Ag.2 k)
        else if r = k then
          linearComplex M ⟨M.neg cs.2.re, cs.2.im⟩ ⟨cs.1.re, M.neg cs.1.im⟩ (Ag.2 i) (Ag.2 k)
        else Ag.2 r)
  else Ag

/-- The matrix stored by `NLAlib.SmallEig.rhess` on the machine `M` from the matrix $\mathbf{A}$
and the $2N$ drawn words $x$: the $N - 1$ steps `NLAlib.SmallEig.rotateToStepWord` from
$(\mathbf{A}, \mathbf{g})$, then `NLAlib.hessenbergReduceLastWord`. -/
noncomputable def rhessWord (M : Machine ℝ) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (x : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  hessenbergReduceLastWord M
    ((List.range (N - 1)).foldl (fun Ag j => rotateToStepWord M j Ag) (A, pairVector x N)).1

/-- `omega` after reducing the projections of literal pairs. -/
local macro "pomega" : tactic => `(tactic| ((try dsimp only) <;> omega))

section Steps

variable {O Q : Type} [Has ScalarOp O] [Has CmpTst Q]


/-- A complex vector stored as a one-column matrix. -/
private def colVec {N : ℕ} (v : Fin N → ℂ) : Matrix (Fin N) (Fin 1) ℂ := Matrix.of fun i _ => v i

/-- The words of a stored vector. -/
private theorem get_colVec {N L : ℕ} {s : Store ℝ} {v : Fin N → ℂ}
    (h : HoldsMatrix (L, 0) (colVec v) s) (i : Fin N) :
    s.get L (2 * i) = some (v i).re ∧ s.get L (2 * i + 1) = some (v i).im := by
  have h0 := h.get_re i 0
  have h1 := h.get_im i 0
  simp only [colVec, Matrix.of_apply, Fin.val_zero, zero_mul, zero_add] at h0 h1
  exact ⟨h0, h1⟩

/-- A stored vector from its words. -/
private theorem holdsMatrix_colVec {N L : ℕ} {s : Store ℝ} {v : Fin N → ℂ}
    (h : ∀ i : Fin N, s.get L (2 * i) = some (v i).re ∧ s.get L (2 * i + 1) = some (v i).im) :
    HoldsMatrix (L, 0) (colVec v) s := by
  refine HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)
  · have : (j : ℕ) = 0 := Nat.lt_one_iff.mp j.isLt
    simpa [colVec, this] using (h i).1
  · have : (j : ℕ) = 0 := Nat.lt_one_iff.mp j.isLt
    simpa [colVec, this] using (h i).2

/-- A cell outside a block of another buffer, or before or after it, is not in the block. -/
private theorem not_inBlock_of {b o n b' i : ℕ} (h : b' ≠ b ∨ i < o ∨ o + n ≤ i) :
    ¬ Store.inBlock b o n b' i := fun hi => by
  obtain ⟨h1, h2, h3⟩ := hi
  omega

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
    fun hf hne hv => (hf.2 _ _ (not_inBlock_of (by pomega))).trans hv
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
    (by pomega)).frame_seq_le hd ha (by simp [Mem.Live, hlen₄]; pomega)
    ((hcf.trans le_sup_left).trans hF) ?_
  rintro m₅ hf₅ ⟨hp₅, hcs⟩
  refine hnext m₅ ?_ (by rw [hp₅, hp₄, hp₃, hp₂, hp₁])
    (Mem.readBlocks_cons_iff.mp hcs).1
    (Mem.readBlocks_cons_iff.mp (Mem.readBlocks_cons_iff.mp hcs).2).1
  exact ((((hf₁.mono (hU 0 (by pomega))).trans (hf₂.mono (hU 1 (by pomega)))).trans
    (hf₃.mono (hU 2 (by pomega)))).trans (hf₄.mono (hU 3 (by pomega)))).trans
    (hf₅.mono (hcf.trans le_sup_left))

end Steps

section BackwardError

variable {M : Machine ℝ} {u : ℝ}

/-- $(1 + x)^n - 1 \le 2nx$ for $x \ge 0$ and $nx \le 1/2$. -/
private theorem one_add_pow_sub_one_le_two_mul {x : ℝ} {n : ℕ} (hx : 0 ≤ x)
    (hnx : n * x ≤ 1 / 2) : (1 + x) ^ n - 1 ≤ 2 * n * x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx1 : x ≤ 1 / 2 := le_trans (le_mul_of_one_le_left hx hn1) hnx
  have hB : 1 + n * (-x) ≤ (1 + -x) ^ n := one_add_mul_le_pow (by linarith) n
  have hAB : (1 + x) ^ n * (1 + -x) ^ n ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hA : 0 ≤ (1 + x) ^ n := by positivity
  have h1 : (1 + x) ^ n * (1 - n * x) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hB hA]
  have hy : 0 ≤ (n : ℝ) * x := by positivity
  have hP : (1 + x) ^ n ≤ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hP hy]

/-- One rounded round, rows then columns, within $50\boldsymbol{u}\|\mathbf{Z}\|_2$ of the exact
conjugation, for $0 \le \boldsymbol{u} \le 1/288$. -/
private theorem specNorm_rowCol_sub_le (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 288)
    {N : ℕ} {i j : Fin N} (hij : i ≠ j) (p q : ℂ) (Z : Matrix (Fin N) (Fin N) ℂ) :
    specNorm (machineColRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2
        (machineRowRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2 Z) -
      givens i j (givensCoeffs p q).1 (givensCoeffs p q).2 * Z *
        (givens i j (givensCoeffs p q).1 (givensCoeffs p q).2)ᴴ) ≤ 50 * u * specNorm Z := by
  have hu100 : u ≤ 1 / 100 := by linarith
  set G := givens i j (givensCoeffs p q).1 (givensCoeffs p q).2
  have hG : HasOrthonormalCols G :=
    hasOrthonormalCols_givens hij (norm_givensCoeffs_fst_sq_add p q)
  set Z₁ := machineRowRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2 Z
  set Z₂ := machineColRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2 Z₁
  have h1 := (isRoundedRowRotation_machineRowRotation hM hu hu100 hij p q Z).specNorm_sub_le
    (by positivity)
  have h2 := (isRoundedColRotation_machineColRotation hM hu hu100 hij p q Z₁).specNorm_sub_le
    (by positivity)
  have hZ₁ : specNorm Z₁ ≤ (1 + 24 * u) * specNorm Z := by
    have e : Z₁ = G * Z + (Z₁ - G * Z) := by abel
    have := specNorm_add_le (G * Z) (Z₁ - G * Z)
    rw [← e, hG.specNorm_mul_left] at this
    linarith
  have e : Z₂ - G * Z * Gᴴ = (Z₂ - Z₁ * Gᴴ) + (Z₁ - G * Z) * Gᴴ := by
    rw [Matrix.sub_mul]
    abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [hG.specNorm_mul_conjTranspose_right]
  have hZ : 0 ≤ specNorm Z := specNorm_nonneg Z
  nlinarith [mul_le_mul_of_nonneg_left hZ₁ (by positivity : (0 : ℝ) ≤ 2 * (12 * u)),
    mul_nonneg (mul_nonneg hu hZ) (by linarith : (0 : ℝ) ≤ 2 - 576 * u)]

/-- The rounded rotation of the entries $i, k$ of a vector, as `NLAlib.SmallEig.rhess` computes
it. -/
private noncomputable def vecRot (M : Machine ℝ) {N : ℕ} (i k : Fin N) (cs : ℂ × ℂ)
    (v : Fin N → ℂ) : Fin N → ℂ :=
  fun r => if r = i then linearComplex M cs.1 cs.2 (v i) (v k)
    else if r = k then linearComplex M ⟨M.neg cs.2.re, cs.2.im⟩ ⟨cs.1.re, M.neg cs.1.im⟩ (v i) (v k)
    else v r

/-- The rounded rotation of two entries of a vector is within $12\boldsymbol{u}$ of the exact
one, on those entries, and keeps the others. -/
private theorem vecRot_sub_le (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) {N : ℕ}
    {i k : Fin N} (hik : i ≠ k) (p q : ℂ) (v : Fin N → ℂ) :
    √(‖vecRot M i k (roundedGivensCoeffs M p q) v i -
        (givens i k (givensCoeffs p q).1 (givensCoeffs p q).2 *ᵥ v) i‖ ^ 2 +
      ‖vecRot M i k (roundedGivensCoeffs M p q) v k -
        (givens i k (givensCoeffs p q).1 (givensCoeffs p q).2 *ᵥ v) k‖ ^ 2) ≤
      12 * u * √(‖v i‖ ^ 2 + ‖v k‖ ^ 2) := by
  let X : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun r _ => v r
  have h := (isRoundedRowRotation_machineRowRotation hM hu hu' hik p q X).2 i
  have e1 : ∀ r, (givens i k (givensCoeffs p q).1 (givensCoeffs p q).2 * X) r i =
      (givens i k (givensCoeffs p q).1 (givensCoeffs p q).2 *ᵥ v) r := fun r => by
    simp [X, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [e1, e1] at h
  simpa [X, machineRowRotation, vecRot, Ne.symm hik] using h

/-- The Euclidean norm of a vector supported on two entries. -/
private theorem norm_toLp_eq_of_support {N : ℕ} {i k : Fin N} (hik : i ≠ k) {w : Fin N → ℂ}
    (hw : ∀ r, r ≠ i → r ≠ k → w r = 0) :
    ‖WithLp.toLp 2 w‖ = √(‖w i‖ ^ 2 + ‖w k‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_eq_add i k hik fun r hr => by simp [hw r hr.1 hr.2]]

/-- Two entries have joint norm at most the Euclidean norm. -/
private theorem sqrt_norm_sq_add_le_norm_toLp {N : ℕ} {i k : Fin N} (hik : i ≠ k)
    (w : Fin N → ℂ) : √(‖w i‖ ^ 2 + ‖w k‖ ^ 2) ≤ ‖WithLp.toLp 2 w‖ := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i, k})
    (f := fun r => ‖w r‖ ^ 2) fun _ _ _ => sq_nonneg _
  simpa [Finset.sum_pair hik] using h

/-- The invariant of the rotations of `RHess` after $k$ steps from $(\mathbf{A}, \mathbf{g})$:
a unitary $\mathbf{U}$ with $\mathbf{B}$ within $((1 + 50\boldsymbol{u})^k - 1)\|\mathbf{A}\|_2$ of
$\mathbf{U}\mathbf{A}\mathbf{U}^{\mathsf{H}}$, $\mathbf{v}$ within
$((1 + 12\boldsymbol{u})^k - 1)\|\mathbf{g}\|$ of $\mathbf{U}\mathbf{g}$, and the first $k$ entries
of $\mathbf{v}$ at most $12\boldsymbol{u}(1 + 12\boldsymbol{u})^k\|\mathbf{g}\|$. -/
private def RotInv (u : ℝ) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (g : Fin N → ℂ) (k : ℕ)
    (Bv : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ)) : Prop :=
  ∃ U : Matrix (Fin N) (Fin N) ℂ, HasOrthonormalCols U ∧
    specNorm (Bv.1 - U * A * Uᴴ) ≤ ((1 + 50 * u) ^ k - 1) * specNorm A ∧
    ‖WithLp.toLp 2 (Bv.2 - U *ᵥ g)‖ ≤ ((1 + 12 * u) ^ k - 1) * ‖WithLp.toLp 2 g‖ ∧
    ∀ r : Fin N, (r : ℕ) < k → ‖Bv.2 r‖ ≤ 12 * u * (1 + 12 * u) ^ k * ‖WithLp.toLp 2 g‖

/-- The step of `NLAlib.SmallEig.rotateToStepWord` on a machine with the standard model. -/
private theorem rotateToStepWord_eq (hM : StdModel u id M) {N j : ℕ} (hj : j + 1 < N)
    (B : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    rotateToStepWord M j (B, v) =
      (machineColRotation M ⟨j, by omega⟩ ⟨j + 1, hj⟩
        (roundedGivensCoeffs M (star (v ⟨j + 1, hj⟩)) (-star (v ⟨j, by omega⟩))).1
        (roundedGivensCoeffs M (star (v ⟨j + 1, hj⟩)) (-star (v ⟨j, by omega⟩))).2
        (machineRowRotation M ⟨j, by omega⟩ ⟨j + 1, hj⟩
          (roundedGivensCoeffs M (star (v ⟨j + 1, hj⟩)) (-star (v ⟨j, by omega⟩))).1
          (roundedGivensCoeffs M (star (v ⟨j + 1, hj⟩)) (-star (v ⟨j, by omega⟩))).2 B),
        vecRot M ⟨j, by omega⟩ ⟨j + 1, hj⟩
          (roundedGivensCoeffs M (star (v ⟨j + 1, hj⟩)) (-star (v ⟨j, by omega⟩))) v) := by
  have hn (x : ℝ) : M.neg x = -x := hM.neg x
  have e1 : (⟨(v ⟨j + 1, hj⟩).re, M.neg (v ⟨j + 1, hj⟩).im⟩ : ℂ) = star (v ⟨j + 1, hj⟩) := by
    apply Complex.ext <;> simp [hn]
  have e2 : (⟨M.neg (v ⟨j, by omega⟩).re, (v ⟨j, by omega⟩).im⟩ : ℂ) =
      -star (v ⟨j, by omega⟩) := by
    apply Complex.ext <;> simp [hn]
  simp only [rotateToStepWord, dif_pos hj, e1, e2]
  rfl

/-- The matrix half of a rotation step of `RHess`: a step within $50\boldsymbol{u}\|\mathbf{B}\|_2$
of $\mathbf{G}\mathbf{B}\mathbf{G}^{\mathsf{H}}$ adds one factor $1 + 50\boldsymbol{u}$. -/
private theorem rotInv_matrix_step {N j : ℕ} {A B B' U G : Matrix (Fin N) (Fin N) ℂ}
    (hU : HasOrthonormalCols U) (hG : HasOrthonormalCols G)
    (hB : specNorm (B - U * A * Uᴴ) ≤ ((1 + 50 * u) ^ j - 1) * specNorm A) (hu : 0 ≤ u)
    (hrc : specNorm (B' - G * B * Gᴴ) ≤ 50 * u * specNorm B) :
    specNorm (B' - G * U * A * (G * U)ᴴ) ≤ ((1 + 50 * u) ^ (j + 1) - 1) * specNorm A := by
  have hAU : specNorm (U * A * Uᴴ) = specNorm A := by
    have := hU.conjTranspose.specNorm_conjTranspose_mul_mul A
    rwa [Matrix.conjTranspose_conjTranspose] at this
  have hBn : specNorm B ≤ (1 + 50 * u) ^ j * specNorm A := by
    have e : B = (B - U * A * Uᴴ) + U * A * Uᴴ := by abel
    have := specNorm_add_le (B - U * A * Uᴴ) (U * A * Uᴴ)
    rw [← e, hAU] at this
    linarith
  have e : B' - G * U * A * (G * U)ᴴ = (B' - G * B * Gᴴ) + G * (B - U * A * Uᴴ) * Gᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [hG.specNorm_mul_conjTranspose_right, hG.specNorm_mul_left, pow_succ]
  nlinarith [mul_le_mul_of_nonneg_left hBn (by positivity : (0 : ℝ) ≤ 50 * u)]

/-- One rotation of `RHess` keeps the invariant, with one more step. -/
private theorem rotInv_step (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 288) {N j : ℕ}
    (hj : j + 1 < N) {A : Matrix (Fin N) (Fin N) ℂ} {g : Fin N → ℂ}
    {X : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ)} (h : RotInv u A g j X) :
    RotInv u A g (j + 1) (rotateToStepWord M j X) := by
  obtain ⟨B, v⟩ := X
  obtain ⟨U, hU, hB, hv, hz⟩ := h
  dsimp only at hB hv hz
  rw [rotateToStepWord_eq hM hj]
  set i : Fin N := ⟨j, by omega⟩
  set k : Fin N := ⟨j + 1, hj⟩
  have hik : i ≠ k := Fin.ne_of_val_ne (by simp [i, k])
  set p := star (v k)
  set q := -star (v i)
  set G := givens i k (givensCoeffs p q).1 (givensCoeffs p q).2
  have hG : HasOrthonormalCols G := hasOrthonormalCols_givens hik (norm_givensCoeffs_fst_sq_add _ _)
  have hgn : ‖WithLp.toLp 2 (U *ᵥ g)‖ = ‖WithLp.toLp 2 g‖ := hU.norm_toLp_mulVec g
  have hvn : ‖WithLp.toLp 2 v‖ ≤ (1 + 12 * u) ^ j * ‖WithLp.toLp 2 g‖ := by
    have e : v = (v - U *ᵥ g) + U *ᵥ g := by abel
    have := norm_add_le (WithLp.toLp 2 (v - U *ᵥ g)) (WithLp.toLp 2 (U *ᵥ g))
    rw [← WithLp.toLp_add, ← e, hgn] at this
    linarith
  have hpair := vecRot_sub_le hM hu (by linarith) hik p q v
  set v' := vecRot M i k (roundedGivensCoeffs M p q) v
  have hsupp : ∀ r, r ≠ i → r ≠ k → (v' - G *ᵥ v) r = 0 := fun r h1 h2 => by
    simp [v', vecRot, h1, h2, G, givens_mulVec_apply_of_ne h1 h2]
  have hvv : ‖WithLp.toLp 2 (v' - G *ᵥ v)‖ ≤ 12 * u * ((1 + 12 * u) ^ j * ‖WithLp.toLp 2 g‖) := by
    rw [norm_toLp_eq_of_support hik hsupp]
    have hp' : √(‖(v' - G *ᵥ v) i‖ ^ 2 + ‖(v' - G *ᵥ v) k‖ ^ 2) ≤
        12 * u * √(‖v i‖ ^ 2 + ‖v k‖ ^ 2) := by simpa using hpair
    exact hp'.trans (mul_le_mul_of_nonneg_left
      ((sqrt_norm_sq_add_le_norm_toLp hik v).trans hvn) (by positivity))
  refine ⟨G * U, hasOrthonormalCols_iff.mpr ((hG.conjTranspose_mul_mul U U).trans
    (hasOrthonormalCols_iff.mp hU)), ?_, ?_, fun r hr => ?_⟩
  · dsimp only
    exact rotInv_matrix_step hU hG hB hu (specNorm_rowCol_sub_le hM hu hu' hik p q B)
  · dsimp only
    have e : v' - (G * U) *ᵥ g = (v' - G *ᵥ v) + G *ᵥ (v - U *ᵥ g) := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      abel
    rw [e, WithLp.toLp_add]
    refine (norm_add_le _ _).trans ?_
    rw [hG.norm_toLp_mulVec, pow_succ]
    nlinarith [hvv, hv, norm_nonneg (WithLp.toLp 2 g)]
  · dsimp only
    have hg0 : 0 ≤ ‖WithLp.toLp 2 g‖ := norm_nonneg _
    have hmono : 12 * u * (1 + 12 * u) ^ j * ‖WithLp.toLp 2 g‖ ≤
        12 * u * (1 + 12 * u) ^ (j + 1) * ‖WithLp.toLp 2 g‖ := by
      rw [pow_succ]
      have : 0 ≤ 12 * u * (1 + 12 * u) ^ j * ‖WithLp.toLp 2 g‖ := by positivity
      nlinarith
    by_cases hri : r = i
    · subst hri
      have h0 : (G *ᵥ v) i = 0 := by
        have hz0 := congrArg star (neg_star_givensCoeffs_snd_mul_add p q)
        simp only [p, q, star_add, star_mul', star_neg, star_star, star_zero] at hz0
        rw [givens_mulVec_apply_left hik]
        linear_combination -hz0
      have hle : ‖v' i‖ ≤ ‖WithLp.toLp 2 (v' - G *ᵥ v)‖ := by
        have := PiLp.norm_apply_le (WithLp.toLp 2 (v' - G *ᵥ v)) i
        simpa [h0] using this
      exact (hle.trans hvv).trans (le_of_eq_of_le (by ring) hmono)
    · have hrj : (r : ℕ) < j := by
        have : (r : ℕ) ≠ j := fun h => hri (Fin.ext h)
        omega
      have hrk : r ≠ k := Fin.ne_of_val_ne (by simp [k]; pomega)
      have : v' r = v r := by simp [v', vecRot, hri, hrk]
      rw [this]
      exact (hz r hrj).trans hmono

/-- The rotations of `RHess` keep the invariant. -/
private theorem rotInv_fold (hM : StdModel u id M) (hu : 0 ≤ u) {N : ℕ}
    (hu' : 2 ≤ N → u ≤ 1 / 288) (A : Matrix (Fin N) (Fin N) ℂ) (g : Fin N → ℂ) :
    ∀ k ≤ N - 1, RotInv u A g k
      ((List.range k).foldl (fun Ag j => rotateToStepWord M j Ag) (A, g))
  | 0, _ => ⟨1, hasOrthonormalCols_one, by simp, by simp, fun r hr => absurd hr (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact rotInv_step hM hu (hu' (by omega)) (by omega)
      (rotInv_fold hM hu hu' A g k (by omega))

/-- **A phase for the last coordinate vector**: if $\|\mathbf{w}\| = R > 0$ and the entries of
$\mathbf{w}$ other than the last have joint norm at most $\delta R$ with $0 \le \delta < 1$, there
is $\lvert c\rvert = 1$ with $\|\mathbf{e}_{n+1} - (c/R)\mathbf{w}\| \le \sqrt2\,\delta$. -/
private theorem exists_phase_norm_sub_le {n : ℕ} (w : Fin (n + 1) → ℂ) {R δ : ℝ} (hR : 0 < R)
    (hw : ‖WithLp.toLp 2 w‖ = R) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (hoff : ∑ i : Fin n, ‖w i.castSucc‖ ^ 2 ≤ (δ * R) ^ 2) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ‖WithLp.toLp 2 (Pi.single (Fin.last n) 1 - (c * ((R⁻¹ : ℝ) : ℂ)) • w)‖ ≤ √2 * δ := by
  set a := w (Fin.last n)
  have hsum : ∑ i : Fin n, ‖w i.castSucc‖ ^ 2 + ‖a‖ ^ 2 = R ^ 2 := by
    rw [← hw, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  have ha2 : (1 - δ ^ 2) * R ^ 2 ≤ ‖a‖ ^ 2 := by nlinarith
  have ha : 0 < ‖a‖ := by
    have h0 : 0 < (1 - δ ^ 2) * R ^ 2 := by
      have : δ ^ 2 < 1 := by nlinarith
      have : 0 < 1 - δ ^ 2 := by linarith
      positivity
    by_contra hle
    have : ‖a‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
    rw [this] at ha2
    linarith
  set c := star a / (‖a‖ : ℂ)
  refine ⟨c, ?_, ?_⟩
  · rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self ha.ne']
  have hca : c * a = (‖a‖ : ℂ) := by
    simp only [c]
    rw [div_mul_eq_mul_div, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
      pow_two, Complex.ofReal_mul, mul_div_assoc, div_self (by exact_mod_cast ha.ne'), mul_one]
  set ρ := ‖a‖ / R
  have hρ1 : ρ ≤ 1 := by
    rw [div_le_one hR]
    have : 0 ≤ ∑ i : Fin n, ‖w i.castSucc‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [norm_nonneg a]
  set z : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1 - (c * ((R⁻¹ : ℝ) : ℂ)) • w
  have hc1 : ‖c‖ = 1 := by
    rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self ha.ne']
  have h1 : ∀ i : Fin n, ‖z i.castSucc‖ = ‖w i.castSucc‖ / R := fun i => by
    simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne (Fin.castSucc_ne_last i), zero_sub, norm_neg, norm_mul, hc1,
      Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), one_mul]
    rw [div_eq_inv_mul]
  have h2 : z (Fin.last n) = ((1 - ρ : ℝ) : ℂ) := by
    simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]
    rw [mul_comm c, mul_assoc, hca]
    push_cast
    simp only [ρ]
    push_cast
    ring
  have hzsq : ‖WithLp.toLp 2 z‖ ^ 2 = (∑ i : Fin n, ‖w i.castSucc‖ ^ 2) / R ^ 2 + (1 - ρ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
    simp only [PiLp.toLp_apply, h1, h2, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
      Finset.sum_div]
  have hoffR : (∑ i : Fin n, ‖w i.castSucc‖ ^ 2) / R ^ 2 = 1 - ρ ^ 2 := by
    simp only [ρ]
    field_simp
    linarith
  have hδR : (∑ i : Fin n, ‖w i.castSucc‖ ^ 2) / R ^ 2 ≤ δ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [hzsq, mul_pow, Real.sq_sqrt (by norm_num)]
  have hρ0 : 0 ≤ ρ := by positivity
  nlinarith

/-- The matrix bound of `RHess`: the reduction's error on top of the rotations' error. -/
private theorem rhess_matrix_bound {n : ℕ} {A B U Q' H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q')
    (hB : specNorm (B - U * A * Uᴴ) ≤ ((1 + 50 * u) ^ n - 1) * specNorm A)
    (hE : specNorm (H - Q'ᴴ * B * Q') ≤ 50 * ((n : ℝ) + 1) ^ 2 * u * specNorm B)
    (hu : 0 ≤ u) (hNu : ((n : ℝ) + 1) * u ≤ 1 / 100) (hnu : (n : ℝ) * u ≤ 1 / 100) :
    specNorm (H - (Uᴴ * Q')ᴴ * A * (Uᴴ * Q')) ≤ 200 * ((n : ℝ) + 1) ^ 2 * u * specNorm A := by
  have hgrow := one_add_pow_sub_one_le_two_mul (x := 50 * u) (n := n) (by positivity)
    (by nlinarith)
  have hAU : specNorm (U * A * Uᴴ) = specNorm A := by
    have := hU.conjTranspose.specNorm_conjTranspose_mul_mul A
    rwa [Matrix.conjTranspose_conjTranspose] at this
  have hA0 := specNorm_nonneg A
  have hB' : specNorm (B - U * A * Uᴴ) ≤ 100 * n * u * specNorm A := by
    refine hB.trans ?_
    nlinarith [mul_le_mul_of_nonneg_right hgrow hA0]
  have hBn : specNorm B ≤ 2 * specNorm A := by
    have e : B = (B - U * A * Uᴴ) + U * A * Uᴴ := by abel
    have := specNorm_add_le (B - U * A * Uᴴ) (U * A * Uᴴ)
    rw [← e, hAU] at this
    nlinarith
  have e : H - (Uᴴ * Q')ᴴ * A * (Uᴴ * Q') = (H - Q'ᴴ * B * Q') + Q'ᴴ * (B - U * A * Uᴴ) * Q' := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc]
    abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [hQ'.specNorm_conjTranspose_mul_mul]
  have hn2 : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hBn (by positivity : (0 : ℝ) ≤ 50 * ((n : ℝ) + 1) ^ 2 * u),
    mul_le_mul_of_nonneg_right hn2 (mul_nonneg hu hA0)]

/-- The direction bound of `RHess`: the last column of $\mathbf{U}^{\mathsf{H}}$ is within
$60(n + 1)\boldsymbol{u}$ of a phase of $\mathbf{g}/\|\mathbf{g}\|$. -/
private theorem rhess_phase {n : ℕ} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {g v : Fin (n + 1) → ℂ} (hU : HasOrthonormalCols U) (hg : g ≠ 0)
    (hv : ‖WithLp.toLp 2 (v - U *ᵥ g)‖ ≤ ((1 + 12 * u) ^ n - 1) * ‖WithLp.toLp 2 g‖)
    (hz : ∀ r : Fin (n + 1), (r : ℕ) < n → ‖v r‖ ≤ 12 * u * (1 + 12 * u) ^ n * ‖WithLp.toLp 2 g‖)
    (hu : 0 ≤ u) (hNu : ((n : ℝ) + 1) * u ≤ 1 / 100) (hnu : (n : ℝ) * u ≤ 1 / 100) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖WithLp.toLp 2 (Uᴴ *ᵥ Pi.single (Fin.last n) 1 -
      (c * ((‖WithLp.toLp 2 g‖⁻¹ : ℝ) : ℂ)) • g)‖ ≤ 60 * ((n : ℝ) + 1) * u := by
  set R := ‖WithLp.toLp 2 g‖
  have hR : 0 < R := norm_pos_iff.mpr (fun h => hg (by simpa using congrArg WithLp.ofLp h))
  set w := U *ᵥ g
  have hw : ‖WithLp.toLp 2 w‖ = R := hU.norm_toLp_mulVec g
  have hgrow := one_add_pow_sub_one_le_two_mul (x := 12 * u) (n := n) (by positivity)
    (by nlinarith)
  have hP : (1 + 12 * u) ^ n ≤ 1 + 24 * n * u := by linarith
  have hδ : (39 * ((n : ℝ) + 1) * u) < 1 := by nlinarith
  -- the entries of `w` other than the last
  have hoff : ∑ i : Fin n, ‖w i.castSucc‖ ^ 2 ≤ (39 * ((n : ℝ) + 1) * u * R) ^ 2 := by
    set e : Fin (n + 1) → ℂ := Pi.single (Fin.last n) (v (Fin.last n))
    have h1 : ‖WithLp.toLp 2 (v - e)‖ ≤ 15 * ((n : ℝ) + 1) * u * R := by
      have hvi : ∀ i : Fin n, ‖v i.castSucc‖ ≤ 15 * u * R := fun i => by
        refine (hz i.castSucc (by simp)).trans ?_
        nlinarith [mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 12 * u * R),
          mul_le_mul_of_nonneg_left hnu (by positivity : (0 : ℝ) ≤ u * R)]
      refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
      have hl : (v - e) (Fin.last n) = 0 := by simp [e]
      have hc : ∀ i : Fin n, (v - e) i.castSucc = v i.castSucc := fun i => by
        simp [e, Pi.single_eq_of_ne (Fin.castSucc_ne_last i)]
      simp only [PiLp.toLp_apply, WithLp.ofLp_toLp, hl, hc, norm_zero]
      have hs : ∑ i : Fin n, ‖v i.castSucc‖ ^ 2 ≤ n * (15 * u * R) ^ 2 := by
        calc ∑ i : Fin n, ‖v i.castSucc‖ ^ 2 ≤ ∑ _i : Fin n, (15 * u * R) ^ 2 :=
              Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hvi i) 2
          _ = n * (15 * u * R) ^ 2 := by simp
      have hn2 : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      have e1 : (15 * ((n : ℝ) + 1) * u * R) ^ 2 = ((n : ℝ) + 1) ^ 2 * (15 * u * R) ^ 2 := by ring
      rw [e1]
      nlinarith [mul_le_mul_of_nonneg_right hn2 (sq_nonneg (15 * u * R))]
    have h2 : ‖WithLp.toLp 2 (w - e)‖ ≤ 39 * ((n : ℝ) + 1) * u * R := by
      have e2 : w - e = (v - e) - (v - w) := by abel
      rw [e2, WithLp.toLp_sub]
      refine (norm_sub_le _ _).trans ?_
      nlinarith [hv, mul_le_mul_of_nonneg_right hgrow hR.le]
    have h3 : ∑ i : Fin n, ‖w i.castSucc‖ ^ 2 ≤ ‖WithLp.toLp 2 (w - e)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
      have : ∀ i : Fin n, (w - e) i.castSucc = w i.castSucc := fun i => by
        simp [e, Pi.single_eq_of_ne (Fin.castSucc_ne_last i)]
      simp only [PiLp.toLp_apply, WithLp.ofLp_toLp, this]
      exact le_add_of_nonneg_right (by positivity)
    exact h3.trans (pow_le_pow_left₀ (norm_nonneg _) h2 2)
  obtain ⟨c, hc, hcz⟩ := exists_phase_norm_sub_le w hR hw (by positivity) hδ hoff
  refine ⟨c, hc, ?_⟩
  have hgw : g = Uᴴ *ᵥ w := by
    rw [show w = U *ᵥ g from rfl, Matrix.mulVec_mulVec, hasOrthonormalCols_iff.mp hU,
      Matrix.one_mulVec]
  have e3 : Uᴴ *ᵥ Pi.single (Fin.last n) 1 - (c * ((R⁻¹ : ℝ) : ℂ)) • g =
      Uᴴ *ᵥ (Pi.single (Fin.last n) 1 - (c * ((R⁻¹ : ℝ) : ℂ)) • w) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ← hgw]
  rw [e3, hU.conjTranspose.norm_toLp_mulVec]
  refine hcz.trans ?_
  have hs2 : √2 ≤ 1.42 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  nlinarith [mul_le_mul_of_nonneg_right hs2 (by positivity : (0 : ℝ) ≤ 39 * ((n : ℝ) + 1) * u)]

end BackwardError

section Rotate

variable {O Q : Type} [Has ScalarOp O] [Has CmpTst Q]

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
    (hB : HoldsMatrix a B m.store) (hV : HoldsMatrix (L, 0) (colVec v) m.store) :
    Writes .total I τ
      (.seq (.frame ds₆ as₆ (rotateLeftWithScratch (Op := O) (Tst := Q)).body)
        (.seq (.frame ds₇ as₇ (rotateRows (Op := O) (Tst := Q)).body)
          (.frame ds₈ as₈ (rotateColumns (Op := O) (Tst := Q)).body))) ρ
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Fp.above L)
      (fun m' => m'.pos = m.pos ∧
        HoldsMatrix a (machineColRotation M ⟨j, by omega⟩ ⟨j + 1, hj⟩ cs.1 cs.2
          (machineRowRotation M ⟨j, by omega⟩ ⟨j + 1, hj⟩ cs.1 cs.2 B)) m'.store ∧
        HoldsMatrix (L, 0) (colVec (vecRot M ⟨j, by omega⟩ ⟨j + 1, hj⟩ cs v)) m'.store) m := by
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
    right
    show L ≤ b
    omega
  refine (writes_rotateLeftWithScratch_word (τ := τ) (m := m) (c := (L + 1, 0)) (s := (L + 1, 2))
    (x := (L, 2 * j)) (y := (L, 2 * j + 2)) (t := (L + 3, 0)) (cv := cs.1) (sv := cs.2)
    (xv := v ⟨j, by omega⟩) (yv := v ⟨j + 1, hj⟩) hS (by simp) (by simp) (by simp) (by simp)
    (Fp.disj_inBlock_of_le (by omega)) hc0 hc1 (by simpa using hs0) (by simpa using hs1) hx0
    (by simpa [Nat.add_assoc] using hx1)
    (by simpa [show 2 * (j + 1) = 2 * j + 2 by omega] using hy0)
    (by simpa [show 2 * (j + 1) + 1 = 2 * j + 2 + 1 by omega] using hy1) (by simp [hTm])
    (by simp [hG] <;> omega) (by simp [hG] <;> omega)).frame_seq_le hd₆ ha₆
    (by simp [Mem.Live, hlen] <;> omega) habove ?_
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
  have hV₁ : HoldsMatrix (L, 0) (colVec (vecRot M ⟨j, by omega⟩ ⟨j + 1, hj⟩ cs v)) m₁.store := by
    refine holdsMatrix_colVec fun r => ?_
    by_cases hri : (r : ℕ) = j
    · have hr : r = ⟨j, Nat.lt_of_succ_lt hj⟩ := Fin.ext hri
      subst hr
      simp only [vecRot, if_true]
      exact ⟨by simpa using Store.get_of_readBlock hx' (j := 0) (by norm_num) (0 : ℝ),
        by simpa using Store.get_of_readBlock hx' (j := 1) (by norm_num) (0 : ℝ)⟩
    by_cases hrk : (r : ℕ) = j + 1
    · have hr : r = ⟨j + 1, hj⟩ := Fin.ext hrk
      subst hr
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
    hd₇ ha₇ (by simp [Mem.Live, hlen₁]; pomega) le_sup_left ?_
  rintro m₂ hf₂ ⟨hp₂, hB₂⟩
  have hc₂ := hf₂.keep (Store.readsOnly_readBlock _ _ _ _) (hcs 0) hc₁
  have hs₂ := hf₂.keep (Store.readsOnly_readBlock _ _ _ _) (hcs 2) hs₁
  refine ((rotateColumns_writes_word (τ := τ) (k := j) hS hj hB₂ hc₂ hs₂ (hcs 0) (hcs 2)).in_frame
    hd₈ ha₈ (by simp [Mem.Live, hf₂.length_eq, hlen₁]; pomega)).mono le_sup_left ?_
  rintro m₃ hf₃ ⟨hp₃, hB₃⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hB₃,
    (hV₁.of_eqOff hf₂ (hdV rfl)).of_eqOff hf₃ (hdV rfl)⟩

/-- **The loop and the reduction of `RHess`**: from $\mathbf{A}$ at `a` and the vector
$\mathbf{g}$ of the words $x$ at `G`, the $N - 1$ rotations and `NLAlib.hessenbergReduceLast`
store `NLAlib.SmallEig.rhessWord` at `a`. -/
private theorem rhess_loop_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {N L p : ℕ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} {x : ℕ → ℝ} {n : IExp}
    {i₁ u₁ i₂ u₂ i₃ u₃ i₄ u₄ as₅ as₆ as₇ as₈ asH : List Operand}
    {ds₅ ds₆ ds₇ ds₈ dsH : List IExp} (hn : n.eval ρ.idx = some (N - 1))
    (h₁ : ∀ j, Operand.evalList (ρ.pushIdx j) i₁ = some [(L, 2 * j + 2)])
    (h₁' : ∀ j, Operand.evalList (ρ.pushIdx j) u₁ = some [(L + 2, 0)])
    (h₂ : ∀ j, Operand.evalList (ρ.pushIdx j) i₂ = some [(L, 2 * j + 3)])
    (h₂' : ∀ j, Operand.evalList (ρ.pushIdx j) u₂ = some [(L + 2, 1)])
    (h₃ : ∀ j, Operand.evalList (ρ.pushIdx j) i₃ = some [(L, 2 * j)])
    (h₃' : ∀ j, Operand.evalList (ρ.pushIdx j) u₃ = some [(L + 2, 2)])
    (h₄ : ∀ j, Operand.evalList (ρ.pushIdx j) i₄ = some [(L, 2 * j + 1)])
    (h₄' : ∀ j, Operand.evalList (ρ.pushIdx j) u₄ = some [(L + 2, 3)])
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
    (hdH : IExp.evalList ρ.idx dsH = some [N]) (haH : Operand.evalList ρ asH = some [a, a])
    (haL : a.1 < L) (hlen : m.store.length = L + 4) (hG : m.store.len L = 2 * N)
    (hCf : m.store.len (L + 1) = 4) (hUv : m.store.len (L + 2) = 4)
    (hTm : m.store.len (L + 3) = 10) (hA : HoldsMatrix a A m.store)
    (hV : HoldsMatrix (L, 0) (colVec (pairVector x N)) m.store) (hp : m.pos = p) :
    Writes .total I τ
      (.seq (.loop n (.seq (.call (Has.inj ScalarOp.copy) [] i₁ u₁)
        (.seq (.call (Has.inj ScalarOp.neg) [] i₂ u₂) (.seq (.call (Has.inj ScalarOp.neg) [] i₃ u₃)
          (.seq (.call (Has.inj ScalarOp.copy) [] i₄ u₄)
            (.seq (.frame ds₅ as₅ (coefficients (Op := O) (Tst := Q)).body)
              (.seq (.frame ds₆ as₆ (rotateLeftWithScratch (Op := O) (Tst := Q)).body)
                (.seq (.frame ds₇ as₇ (rotateRows (Op := O) (Tst := Q)).body)
                  (.frame ds₈ as₈ (rotateColumns (Op := O) (Tst := Q)).body)))))))))
        (.frame dsH asH (hessenbergReduceLast (O := O) (Q := Q)).body)) ρ
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Fp.above L)
      (fun m' => m'.pos = p ∧ HoldsMatrix a (rhessWord M A x) m'.store) m := by
  set F := Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Fp.above L
  set X : ℕ → Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) := fun k =>
    (List.range k).foldl (fun Ag j => rotateToStepWord M j Ag) (A, pairVector x N)
  set Inv : ℕ → Mem ℝ → Prop := fun k μ => μ.pos = p ∧ μ.store.length = L + 4 ∧
    μ.store.len L = 2 * N ∧ μ.store.len (L + 1) = 4 ∧ μ.store.len (L + 2) = 4 ∧
    μ.store.len (L + 3) = 10 ∧ HoldsMatrix a (X k).1 μ.store ∧
    HoldsMatrix (L, 0) (colVec (X k).2) μ.store
  refine (writes_loop (N := N - 1) hn (fun _ => F) (fun _ _ => le_rfl) Inv
    ⟨hp, hlen, hG, hCf, hUv, hTm, hA, hV⟩ ?_).seq_le le_rfl ?_
  · rintro j hj μ - ⟨hp', hl', hG', hCf', hUv', hTm', hB, hW⟩
    have hjN : j + 1 < N := by omega
    obtain ⟨hx0, hx1⟩ := get_colVec hW ⟨j, by omega⟩
    obtain ⟨hy0, hy1⟩ := get_colVec hW ⟨j + 1, hjN⟩
    refine writes_rhessCoeffs hS hC (t := 2 * j) (h₁ j) (h₁' j) (h₂ j) (h₂' j) (h₃ j) (h₃' j)
      (h₄ j) (h₄' j) (hd₅ j) (ha₅ j) hx0 hx1 (by simpa [show 2 * (j + 1) = 2 * j + 2 by ring]
        using hy0) (by simpa [show 2 * (j + 1) + 1 = 2 * j + 3 by ring] using hy1)
      (by omega) hCf' hUv' (sup_le (fun b i hi => Or.inr (show L ≤ b by have := hi.1; pomega))
        (fun b i hi => Or.inr (show L ≤ b by have := hi.1; pomega))) ?_
    intro μ₂ hf₂ hp₂ hc₂ hs₂
    have hdA : Fp.Disj (Store.inBlock (L + 1) 0 4 ⊔ Store.inBlock (L + 2) 0 4)
        (Store.inBlock a.1 a.2 (2 * (N * N))) := fun b i h1 h2 => by
      simp [Store.inBlock] at h1 h2; omega
    have hdV : Fp.Disj (Store.inBlock (L + 1) 0 4 ⊔ Store.inBlock (L + 2) 0 4)
        (Store.inBlock L 0 (2 * (1 * N))) := fun b i h1 h2 => by
      simp [Store.inBlock] at h1 h2; omega
    have hB₂ := hB.of_eqOff hf₂ hdA
    have hW₂ := hW.of_eqOff hf₂ hdV
    refine (writes_rhessRotate hS hjN (hd₆ j) (ha₆ j) (hd₇ j) (ha₇ j) (hd₈ j) (ha₈ j) haL
      (by rw [hf₂.length_eq]; exact hl') (by rw [hf₂.len_eq]; exact hG')
      (by rw [hf₂.len_eq]; exact hTm') hc₂ hs₂ hB₂ hW₂).mono le_rfl ?_
    rintro μ₃ hf₃ ⟨hp₃, hB₃, hW₃⟩
    have hX : X (j + 1) = rotateToStepWord M j (X j) := by
      simp only [X, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨hp₃.trans (hp₂.trans hp'), hf₃.length_eq.trans (hf₂.length_eq.trans hl'),
      by rw [hf₃.len_eq, hf₂.len_eq, hG'], by rw [hf₃.len_eq, hf₂.len_eq, hCf'],
      by rw [hf₃.len_eq, hf₂.len_eq, hUv'], by rw [hf₃.len_eq, hf₂.len_eq, hTm'], ?_, ?_⟩
    · rw [hX]
      simpa only [rotateToStepWord, dif_pos hjN] using hB₃
    · rw [hX]
      simp only [rotateToStepWord, dif_pos hjN]
      exact hW₃
  · rintro μ - ⟨hp', hl', -, -, -, -, hB, -⟩
    refine ((hessenbergReduceLast_writes_word hS hC (by simp [Mem.Live, hl']; pomega) hB).in_frame
      hdH haH (by simp [Mem.Live, hl']; pomega)).mono le_sup_left ?_
    rintro μ' - ⟨hp'', hW'⟩
    exact ⟨hp''.trans hp', hW'⟩

end Rotate

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has SampleOp O] [Has CmpTst Q]

/-- `NLAlib.SmallEig.rhess` on a scalar machine with exact comparisons and draws that store the
tape entry: from $\mathbf{A}$ of order $N$ at `a`, it writes only the matrix, advances the position
by $2N$, and stores `NLAlib.SmallEig.rhessWord` of $\mathbf{A}$ and the $2N$ entries of the
stream `sG` at the start position. -/
theorem rhess_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) (hSmp : IsSample I) {sG N : ℕ} {τ : Tape ℝ} {μ : Mem ℝ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hl : μ.Live [a]) (hA : HoldsMatrix a A μ.store) :
    Writes .total I τ (rhess (O := O) (Q := Q) sG).body (Env.frame [N] [a, a])
      (Store.inBlock a.1 a.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos + 2 * N ∧
        HoldsMatrix a (rhessWord M A fun j => τ (μ.pos + j) sG) μ'.store) μ := by
  have hal : a.1 < μ.store.length := hl a (by simp)
  unfold rhess
  change Writes .total I τ (Stmt.allocs [.const 2 * .var 0, .const 4, .const 4, .const 10] _)
    _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2 * N, 4, 4, 10]) rfl
    (fun hBelow ⟨hp, hW⟩ => ⟨hp, hW.of_below hBelow hal⟩) ?_
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
  have hV₁ : HoldsMatrix (L, 0) (colVec (pairVector (fun j => τ (μ.pos + j) sG) N)) m₁.store :=
    holdsMatrix_colVec fun i => ⟨by
      simpa [pairVector, Tape.window, show 2 * (i : ℕ) < 2 * N by omega] using
        Store.get_of_readBlock hr₁ (j := 2 * i) (by omega) (0 : ℝ), by
      simpa [pairVector, Tape.window, show 2 * (i : ℕ) + 1 < 2 * N by omega] using
        Store.get_of_readBlock hr₁ (j := 2 * i + 1) (by omega) (0 : ℝ)⟩
  have hA₁ : HoldsMatrix a A m₁.store :=
    (hA.of_below hBelow hal).of_eqOff hf₁ (Fp.disj_inBlock_of_ne (by omega))
  exact rhess_loop_writes hS hC rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    rfl rfl (by omega) (by rw [hf₁.length_eq]; exact hlen)
    (by rw [hf₁.len_eq]; exact hG) (by rw [hf₁.len_eq]; exact hCf) (by rw [hf₁.len_eq]; exact hUv)
    (by rw [hf₁.len_eq]; exact hTm) hA₁ hV₁ hp₁

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
    rhess_matrix_bound hU hQ' hB hE hu hNu hnu'⟩
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
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sG : ℕ} (hG : law sG = gaussianReal 0 1) {n : ℕ}
    {A V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {B g S s R φ' : ℝ}
    (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B)
    (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖) (hAS : specNorm A ≤ S) (hs : 0 < s)
    (hφ' : 0 < φ') (hφ'1 : φ' ≤ 1)
    (hR : 2 * (√((n : ℝ) + 1) + 1) + √(2 * Real.log φ'⁻¹) ≤ R)
    (hnu : 100 * ((n : ℝ) + 1) ^ 2 * u ≤ 1) (hus : 60 * ((n : ℝ) + 1) * u ≤ s / (2 * R))
    (huc : 200 * ((n : ℝ) + 1) ^ 2 * u * S ≤
      min (g / (32 * (n + 1) * B)) (s * g / (1024 * (n + 1) * B ^ 2 * R))) {a : ℕ × ℕ} :
    PWrites law I (rhess (O := O) (Q := Q) sG).body (Env.frame [n + 1] [a, a])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (fun μ => HoldsMatrix a A μ.store ∧ μ.Live [a])
      (fun μ' => ∃ (H V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d' : Fin (n + 1) → ℂ),
        HoldsMatrix a H μ'.store ∧ IsUpperHessenberg H ∧
        IsPerturbedUnitarySimilar A H (200 * ((n : ℝ) + 1) ^ 2 * u * S) ∧ IsUnit V' ∧
        H * V' = V' * Matrix.diagonal d' ∧ pseudoConditionNumber V' ≤ 2 * B ∧
        (∀ i j, i ≠ j → g / 2 ≤ ‖d' i - d' j‖) ∧
        ∀ i, s ^ 2 / (64 * R ^ 2 * B ^ 2) ≤ lastRowWeights V' i)
      ((n + 1) * s ^ 2 + φ') := by
  sorry

/-- `NLAlib.SmallEig.rhess` terminates on every tape and every stored matrix. -/
theorem rhess_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hC : IsCmp id I) (hSmp : IsSample I) {sG N : ℕ} {τ : Tape ℝ} {μ : Mem ℝ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hl : μ.Live [a]) (hA : HoldsMatrix a A μ.store) :
    Writes .total I τ (rhess (O := O) (Q := Q) sG).body (Env.frame [N] [a, a])
      (Store.inBlock a.1 a.2 (2 * (N * N)))
      (fun μ' => ∃ H : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix a H μ'.store) μ :=
  (rhess_writes_word hS hC hSmp hl hA).mono le_rfl fun _ _ h => ⟨_, h.2⟩

end Theorems

end NLAlib.SmallEig
