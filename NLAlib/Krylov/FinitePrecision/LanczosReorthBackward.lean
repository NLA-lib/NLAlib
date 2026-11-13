/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosReorthResidual
public import NLAlib.Matrix.Perturbation.SymmetricBackward
public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# The symmetric backward model of a reorthogonalized Lanczos run

For a run `NLAlib.LanczosReorthRun` with $\mathbf{U}$ the polar factor of the computed
$\mathbf{V}_{k+1}$, there is a symmetric $n \times n$ perturbation $\mathbf{E}$ of size
`NLAlib.LanczosReorthRun.backwardRadius` $= 100(k+1)(\mu + \varepsilon + \varepsilon_2)
\|\mathbf{H}\|_2$ for which the computed tridiagonal is exactly the Lanczos tridiagonal of
$(\mathbf{H} + \mathbf{E}, \mathbf{u}_1)$, and, after an orthogonal similarity close to the
identity, of $(\mathbf{H}', \mathbf{b})$ for the exact start vector. No dilation is needed
(compare `NLAlib/Krylov/FinitePrecision/Backward.lean` for plain Lanczos). Historical background on
reorthogonalization and Krylov decompositions:
[Paige1970]; [Simon1984b]; [Stewart2002]. The polar-factor construction, pure backward
model and explicit constant above are the formulation proved here. Design:
`docs/design/Krylov-LanczosReorth.md` §3.2–3.3.

Common hypotheses: $\eta_0 \le 1/100$, the fixed-point condition
$\sqrt{3(k+1)}\,\mu \le \eta_0$ on the orthogonality level $\mu$
(`NLAlib.LanczosReorthRun.orthLevel`), and for the bounds $\mu + \varepsilon + \varepsilon_2 \le
1/100$ (`NLAlib.LanczosReorthRun.recLevel`) and $\tau \le 1$.

## Main results

* `NLAlib.LanczosReorthRun.hasOrthonormalCols_polarFactor_basisOf`: the polar factor of the
  computed basis has orthonormal columns.
* `NLAlib.LanczosReorthRun.exists_backward`: the backward identity and its bound.
* `NLAlib.LanczosReorthRun.exists_lanczosState_backward`: exact Lanczos on the backward model
  computes the run.
* `NLAlib.LanczosReorthRun.exists_pure_backward`: the backward model with the exact start vector.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace LanczosReorthRun

variable {n k : ℕ} (L : LanczosReorthRun n k)

/-- Under $\eta_0 \le 1/100$ and the fixed-point condition $\sqrt{3(k+1)}\,\mu \le \eta_0$,
the polar factor of the computed basis $\mathbf{V}_{k+1}$ has orthonormal columns; it is the
basis of the backward model. -/
theorem hasOrthonormalCols_polarFactor_basisOf (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀) :
    HasOrthonormalCols (polarFactor (basisOf L.v (k + 1))) :=
  hasOrthonormalCols_polarFactor ((L.specNorm_transpose_mul_self_sub_one_le hη hsmall le_rfl).trans
    hη) (by norm_num)

/-- The Frobenius norm of a residual that reappears on the right of its own decomposition
$\mathbf{R} = \mathbf{H}\mathbf{X}_k - \mathbf{X}\mathbf{U}^{\mathsf{T}}\mathbf{H}\mathbf{U}_k +
\mathbf{X}\mathbf{U}^{\mathsf{T}}\mathbf{R} + \mathbf{F}$, with $\|\mathbf{U}\|_2 \le 1$ and
$\|\mathbf{U}_k\|_2 \le 1$. -/
private theorem frobNorm_le_of_eq_sub_add_add {n k : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    {U X : Matrix (Fin n) (Fin (k + 1)) ℝ} {Uk R F : Matrix (Fin n) (Fin k) ℝ}
    (hU : specNorm Uᵀ ≤ 1) (hUk : specNorm Uk ≤ 1)
    (h : R = H * X.submatrix id Fin.castSucc - (X * Uᵀ) * (H * Uk) + (X * Uᵀ) * R + F) :
    frobNorm R ≤ specNorm H * frobNorm X + frobNorm X * specNorm H +
      frobNorm X * frobNorm R + frobNorm F := by
  have hXU : frobNorm (X * Uᵀ) ≤ frobNorm X :=
    (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
      (mul_le_of_le_one_right (frobNorm_nonneg _) hU)
  have hHUk : specNorm (H * Uk) ≤ specNorm H :=
    (specNorm_mul_le _ _).trans (mul_le_of_le_one_right (specNorm_nonneg _) hUk)
  have hA : frobNorm (H * X.submatrix id Fin.castSucc) ≤ specNorm H * frobNorm X :=
    (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans <| by
      gcongr; exact frobNorm_submatrix_le X Function.injective_id (Fin.castSucc_injective k)
  have hB : frobNorm ((X * Uᵀ) * (H * Uk)) ≤ frobNorm X * specNorm H :=
    (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans <| by gcongr
  have hC : frobNorm ((X * Uᵀ) * R) ≤ frobNorm X * frobNorm R :=
    (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans <| by
      gcongr; exact (specNorm_le_frobNorm _).trans hXU
  calc frobNorm R = frobNorm (H * X.submatrix id Fin.castSucc - (X * Uᵀ) * (H * Uk) +
        (X * Uᵀ) * R + F) := congrArg frobNorm h
    _ ≤ _ := (frobNorm_add_le _ _).trans (add_le_add_left ((frobNorm_add_le _ _).trans
        (add_le_add ((frobNorm_sub_le _ _).trans (add_le_add hA hB)) hC)) _)

/-- **The symmetric backward model**: under $\eta_0 \le 1/100$, the fixed-point condition
$\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$ and $\tau \le 1$,
with $\mathbf{U} = $ `NLAlib.polarFactor` $\mathbf{V}_{k+1}$ and $\mathbf{U}_k$ its first $k$
columns, some symmetric $\mathbf{E}$ with $\|\mathbf{E}\|_{\mathsf F} \le$
`NLAlib.LanczosReorthRun.backwardRadius` satisfies
$$(\mathbf{H} + \mathbf{E})\mathbf{U}_k = \mathbf{U}_k\mathbf{T}_k +
(\beta_k\mathbf{u}_{k+1})\mathbf{e}_{k-1}^{\mathsf{T}}$$
exactly. [Paige1971, §6.1] (the backward form $(\mathbf{A} + \delta\mathbf{P})\mathbf{V} =
\mathbf{V}\mathbf{T}$ there); the completion is that of Kahan, Parlett and Jiang (1982).
Result: lanczos-reorth-backward-model -/
theorem exists_backward (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, Eᵀ = E ∧ frobNorm E ≤ L.backwardRadius ∧
      (L.H + E) * (polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc =
        (polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc *
          L.toLanczosData.tridiagonal +
        Matrix.vecMulVec (L.β k • fun i => polarFactor (basisOf L.v (k + 1)) i (Fin.last k))
          (Pi.single L.toLanczosData.lastIndex 1) := by
  set D := L.toLanczosData
  set V := basisOf L.v (k + 1)
  set U := polarFactor V
  set Uk := U.submatrix id Fin.castSucc
  set T := D.tridiagonalSucc
  have hG : frobNorm (Vᵀ * V - 1) ≤ Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel := by
    simpa using L.frobNorm_transpose_mul_self_sub_one_le hη hsmall (k + 1) le_rfl
  have hGs : specNorm (Vᵀ * V - 1) ≤ 1 / 100 :=
    (L.specNorm_transpose_mul_self_sub_one_le hη hsmall le_rfl).trans hη
  have hU : HasOrthonormalCols U := L.hasOrthonormalCols_polarFactor_basisOf hη hsmall
  have hUk : HasOrthonormalCols Uk := hU.submatrix (Equiv.refl _) (Fin.castSucc_injective k)
  have hUU : Uᵀ * U = 1 := by
    have h := hU.conjTranspose_mul_self
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hUT : Ukᵀ * (U * T) = D.tridiagonal := by
    have h : Ukᵀ * (U * T) = (Uᵀ * (U * T)).submatrix Fin.castSucc id := by
      rw [Matrix.transpose_submatrix, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
      rfl
    rw [h, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    ext i j
    exact D.tridiagonalSucc_castSucc i j
  set R := L.H * Uk - U * T with hR
  have hsym : (Ukᵀ * R)ᵀ = Ukᵀ * R := by
    rw [hR, Matrix.mul_sub, hUT, Matrix.transpose_sub, D.transpose_tridiagonal,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, L.transpose_H,
      Matrix.mul_assoc]
  obtain ⟨E, hEt, hEU, hEF, -⟩ := HasOrthonormalCols.exists_transpose_eq_mul_eq_neg hUk hsym
  refine ⟨E, hEt, ?_, ?_⟩
  · set X := U - V
    -- `R = H Xₖ - X T + F`, and `T = Uᵀ (H Uₖ - R)`
    have hdec : R = L.H * X.submatrix id Fin.castSucc - (X * Uᵀ) * (L.H * Uk) +
        (X * Uᵀ) * R + D.residual := by
      have hT : T = Uᵀ * (L.H * Uk - R) := by
        rw [hR, sub_sub_cancel, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
      have hF : L.H * V.submatrix id Fin.castSucc = V * T + D.residual :=
        D.mul_basis_eq_basisSucc_mul
      calc R = L.H * X.submatrix id Fin.castSucc - X * T + D.residual := by
            rw [show X.submatrix id Fin.castSucc = Uk - V.submatrix id Fin.castSucc from rfl,
              hR, Matrix.mul_sub, hF, Matrix.sub_mul]; abel
        _ = _ := by
            rw [hT]; simp only [Matrix.mul_sub, Matrix.mul_assoc]; abel
    have hRle := frobNorm_le_of_eq_sub_add_add
      ((specNorm_transpose U).le.trans hU.specNorm_le_one) hUk.specNorm_le_one hdec
    have hX : frobNorm X ≤ Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel := by
      refine (frobNorm_polarFactor_sub_le hGs (by norm_num)).trans
        ((div_le_self (frobNorm_nonneg _) ?_).trans hG)
      have : (1 / 2 : ℝ) ≤ Real.sqrt (1 - 1 / 100) :=
        Real.le_sqrt_of_sq_le (by norm_num)
      linarith
    have hμ := L.orthLevel_nonneg
    have hμrec := L.orthLevel_le_recLevel
    have hs : Real.sqrt (3 * ((k : ℝ) + 1)) ≤ 2 * ((k : ℝ) + 1) :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
    have hx2 : frobNorm X ≤ 2 * ((k : ℝ) + 1) * L.recLevel :=
      hX.trans (mul_le_mul hs hμrec hμ (by positivity))
    have hx1 : frobNorm X ≤ 1 / 100 := hX.trans (hsmall.trans hη)
    have hF := L.frobNorm_residual_le hη hsmall hrec hτ
    have h2 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hH := specNorm_nonneg L.H
    have hr0 := frobNorm_nonneg R
    have hK : 0 ≤ ((k : ℝ) + 1) * L.recLevel * specNorm L.H :=
      mul_nonneg (mul_nonneg (by positivity) (hμ.trans hμrec)) hH
    have hr : 99 / 100 * frobNorm R ≤ 34 * (((k : ℝ) + 1) * L.recLevel * specNorm L.H) := by
      nlinarith [mul_le_mul_of_nonneg_right hx1 hr0, mul_le_mul_of_nonneg_left hx2 hH]
    unfold backwardRadius
    nlinarith [mul_le_mul_of_nonneg_right h2 hr0]
  · rw [Matrix.add_mul, hEU, hR, neg_sub, add_sub_cancel]
    exact D.mul_tridiagonalSucc U

/-- The first column of the polar factor of $\mathbf{V}_{k+1}$ is within
$2\sqrt{3(k+1)}\,\mu$ of $\mathbf{v}_1$. -/
private theorem norm_colSeq_polarFactor_one_sub_v_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀) :
    ‖WithLp.toLp 2 (colSeq (polarFactor (basisOf L.v (k + 1))) 1 - L.v 1)‖ ≤
      2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel := by
  set V := basisOf L.v (k + 1)
  have hgram : frobNorm (Vᵀ * V - 1) ≤ Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel := by
    simpa using L.frobNorm_transpose_mul_self_sub_one_le hη hsmall (k + 1) le_rfl
  have hsqrt1 : (1 : ℝ) ≤ 2 * Real.sqrt (1 - 1 / 100) := by
    have : (1 / 2 : ℝ) ≤ Real.sqrt (1 - 1 / 100) := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  have hfro : frobNorm (polarFactor V - V) ≤ Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel :=
    ((frobNorm_polarFactor_sub_le ((L.specNorm_transpose_mul_self_sub_one_le hη hsmall
      le_rfl).trans hη) (by norm_num)).trans (div_le_self (frobNorm_nonneg _) hsqrt1)).trans hgram
  have hcolV : colSeq (polarFactor V) 1 - L.v 1 =
      (polarFactor V - V) *ᵥ Pi.single (0 : Fin (k + 1)) (1 : ℝ) := by
    funext r
    simp [V, colSeq, basisOf]
  have hnorm := norm_toLp_mulVec_le_frobNorm_mul (polarFactor V - V)
    (Pi.single (0 : Fin (k + 1)) (1 : ℝ))
  have hone : ‖WithLp.toLp 2 (Pi.single (0 : Fin (k + 1)) (1 : ℝ) : Fin (k + 1) → ℝ)‖ = 1 := by
    simp
  rw [← hcolV, hone, mul_one] at hnorm
  nlinarith [mul_nonneg (Real.sqrt_nonneg (3 * ((k : ℝ) + 1))) L.orthLevel_nonneg]

/-- The columns of an $n \times (k+1)$ matrix $\mathbf{P}$ with orthonormal columns are
orthonormal as the sequence `NLAlib.LanczosReorthRun.colSeq`. -/
private theorem colSeq_dotProduct_colSeq {P : Matrix (Fin n) (Fin (k + 1)) ℝ}
    (hP : HasOrthonormalCols P) (i j : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ k + 1) (hj1 : 1 ≤ j)
    (hj2 : j ≤ k + 1) : colSeq P i ⬝ᵥ colSeq P j = if i = j then 1 else 0 := by
  have hdot : colSeq P i ⬝ᵥ colSeq P j = (Pᴴ * P) ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ := by
    simp [colSeq, hi1, hi2, hj1, hj2, Matrix.mul_apply, dotProduct]
  rw [hdot, hP.conjTranspose_mul_self, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have hne : (⟨i - 1, by omega⟩ : Fin (k + 1)) ≠ ⟨j - 1, by omega⟩ := by
      intro e; apply h; have := congrArg Fin.val e; simp at this; omega
    simp [h, hne]

/-- If $(\mathbf{H} + \mathbf{E})\mathbf{P}_k = \mathbf{P}\mathbf{T}_{k+1,k}$ for the extended
tridiagonal, the columns of $\mathbf{P}$ satisfy the three-term recurrence of the run. -/
private theorem mulVec_colSeq_eq {E : Matrix (Fin n) (Fin n) ℝ}
    {P : Matrix (Fin n) (Fin (k + 1)) ℝ}
    (hid : (L.H + E) * P.submatrix id Fin.castSucc = P * L.toLanczosData.tridiagonalSucc)
    {j : ℕ} (hj : j < k) :
    (L.H + E) *ᵥ colSeq P (j + 1) =
      L.β j • colSeq P j + L.toLanczosData.α (j + 1) • colSeq P (j + 1) +
        L.β (j + 1) • colSeq P (j + 2) := by
  have hu : ∀ (m : ℕ) (hm : m < k + 1) (p : Fin n), P p ⟨m, hm⟩ = colSeq P (m + 1) p := by
    intro m hm p
    simp only [colSeq]
    rw [dif_pos ⟨by omega, by omega⟩]
    rfl
  funext r
  have h1 := congrFun (congrFun hid r) ⟨j, hj⟩
  have h2 := L.toLanczosData.mul_tridiagonalSucc_apply P (colSeq P) hu r ⟨j, hj⟩
  have h3 : ((L.H + E) *ᵥ colSeq P (j + 1)) r =
      ((L.H + E) * P.submatrix id Fin.castSucc) r ⟨j, hj⟩ := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, colSeq, hj.le]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  exact h3.trans (h1.trans h2)

/-- **Exact Lanczos on the backward model computes the run**: under $\eta_0 \le 1/100$, the
fixed-point condition $\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$
and $\tau \le 1$, some symmetric $\mathbf{E}$ with $\|\mathbf{E}\|_{\mathsf F} \le$
`NLAlib.LanczosReorthRun.backwardRadius` has the following property. With $\mathbf{u}_j$ the columns
of the polar factor of $\mathbf{V}_{k+1}$ (`NLAlib.LanczosReorthRun.colSeq`), the exact Lanczos
recurrence on $(\mathbf{H} + \mathbf{E}, \mathbf{u}_1)$ has states $(\mathbf{u}_j, \mathbf{u}_{j+1},
\beta_j)$ for $j < k$ and tridiagonal $\mathbf{T}_k$; the start vector is within
$2\sqrt{3(k+1)}\,\mu$ of $\mathbf{v}_1$. [Paige1971, §6.1] in substance.
Result: lanczos-reorth-backward-model -/
theorem exists_lanczosState_backward (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, Eᵀ = E ∧ frobNorm E ≤ L.backwardRadius ∧
      (∀ j < k, lanczosState (L.H + E) (colSeq (polarFactor (basisOf L.v (k + 1))) 1) j =
        ⟨colSeq (polarFactor (basisOf L.v (k + 1))) j,
          colSeq (polarFactor (basisOf L.v (k + 1))) (j + 1), L.β j⟩) ∧
      lanczosTridiagonal (L.H + E) (colSeq (polarFactor (basisOf L.v (k + 1))) 1) k =
        L.toLanczosData.tridiagonal ∧
      ‖WithLp.toLp 2 (colSeq (polarFactor (basisOf L.v (k + 1))) 1 - L.v 1)‖ ≤
        2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel := by
  obtain ⟨E, hEs, hE, hid⟩ := L.exists_backward hη hsmall hrec hτ
  have hPo := L.hasOrthonormalCols_polarFactor_basisOf hη hsmall
  set P := polarFactor (basisOf L.v (k + 1)) with hPdef
  have hu0 : colSeq P 0 = 0 := by
    funext i; simp [colSeq]
  have horth := colSeq_dotProduct_colSeq hPo
  have hβ : ∀ j ≤ k, 0 ≤ L.β j := fun j hj => L.β_nonneg hj
  have hβpos : ∀ j, 1 ≤ j → j < k → 0 < L.β j := fun j h1 h2 => by
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    exact L.β_succ_pos (by omega)
  have hrec : ∀ j < k, (L.H + E) *ᵥ colSeq P (j + 1) =
      L.β j • colSeq P j + L.toLanczosData.α (j + 1) • colSeq P (j + 1) +
        L.β (j + 1) • colSeq P (j + 2) := fun j hj =>
    L.mulVec_colSeq_eq (by rw [hid, L.toLanczosData.mul_tridiagonalSucc]; rfl) hj
  have hstate := lanczosState_eq_of_orthonormal_recurrence hu0 horth hrec L.β_zero hβ hβpos
  refine ⟨E, hEs, hE, fun j hj => hstate j hj, ?_, ?_⟩
  · have hdiag : ∀ i : Fin k, lanczosAlpha (L.H + E) (lanczosState (L.H + E) (colSeq P 1) i) =
        L.toLanczosData.α (i + 1) := fun i => by
      rw [hstate i i.isLt]; exact (lanczosStep_of_orthonormal_recurrence horth hrec hβ i.isLt).1
    have hbeta : ∀ i : Fin k, (lanczosState (L.H + E) (colSeq P 1) i).beta = L.β i :=
      fun i => by rw [hstate i i.isLt]
    ext i j
    simp only [lanczosTridiagonal, LanczosData.tridiagonal, Matrix.of_apply, hdiag, hbeta]
    split_ifs <;> rfl
  · exact L.norm_colSeq_polarFactor_one_sub_v_le hη hsmall

/-- One exact Lanczos step commutes with an orthogonal similarity. -/
private theorem lanczosStep_mul_mul_transpose {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Zᵀ * Z = 1)
    (M : Matrix (Fin n) (Fin n) ℝ) (s : LanczosState ℝ (Fin n)) :
    lanczosAlpha (Z * M * Zᵀ) ⟨Z *ᵥ s.prev, Z *ᵥ s.cur, s.beta⟩ = lanczosAlpha M s ∧
    lanczosStep (Z * M * Zᵀ) ⟨Z *ᵥ s.prev, Z *ᵥ s.cur, s.beta⟩ =
      ⟨Z *ᵥ (lanczosStep M s).prev, Z *ᵥ (lanczosStep M s).cur, (lanczosStep M s).beta⟩ := by
  have hZ' : HasOrthonormalCols Z := by
    rw [hasOrthonormalCols_iff, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hZ
  have hM : ∀ c, (Z * M * Zᵀ) *ᵥ (Z *ᵥ c) = Z *ᵥ (M *ᵥ c) := fun c => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (Z * M), hZ, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
  have hα : lanczosAlpha (Z * M * Zᵀ) ⟨Z *ᵥ s.prev, Z *ᵥ s.cur, s.beta⟩ = lanczosAlpha M s := by
    simp only [lanczosAlpha, star_trivial, RCLike.re_to_real, hM]
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
    simpa only [star_trivial] using hZ'.star_mulVec_dotProduct_mulVec _ _
  refine ⟨hα, ?_⟩
  simp only [lanczosStep, hα, hM]
  simp only [← Matrix.mulVec_smul, ← Matrix.mulVec_sub, hZ'.norm_toLp_mulVec]

/-- Exact Lanczos is equivariant under an orthogonal similarity: the states map by
$\mathbf{Z}$. -/
private theorem lanczosState_mul_mul_transpose {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Zᵀ * Z = 1)
    (M : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (j : ℕ) :
    lanczosState (Z * M * Zᵀ) (Z *ᵥ u) j =
      ⟨Z *ᵥ (lanczosState M u j).prev, Z *ᵥ (lanczosState M u j).cur,
        (lanczosState M u j).beta⟩ := by
  induction j with
  | zero =>
    have hZ' : HasOrthonormalCols Z := by
      rw [hasOrthonormalCols_iff, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hZ
    simp only [lanczosState, Matrix.mulVec_zero, Matrix.mulVec_smul, hZ'.norm_toLp_mulVec]
  | succ j ih => rw [lanczosState, ih, (lanczosStep_mul_mul_transpose hZ M _).2]; rfl

/-- The exact Lanczos tridiagonal is invariant under an orthogonal similarity. -/
private theorem lanczosTridiagonal_mul_mul_transpose {Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : Zᵀ * Z = 1) (M : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (q : ℕ) :
    lanczosTridiagonal (Z * M * Zᵀ) (Z *ᵥ u) q = lanczosTridiagonal M u q := by
  ext i j
  simp only [lanczosTridiagonal, Matrix.of_apply, lanczosState_mul_mul_transpose hZ,
    (lanczosStep_mul_mul_transpose hZ M _).1]

/-- **The backward model with the exact start vector**: under $\eta_0 \le 1/100$, the fixed-point
condition $\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$ and $\tau
\le 1$, if $\mathbf{b} \ne \mathbf{0}$ and the computed $\mathbf{v}_1$ is within $\delta_b$ of
$\mathbf{b}/\|\mathbf{b}\|$, some symmetric $\mathbf{H}'$ with
$$\|\mathbf{H}' - \mathbf{H}\|_{\mathsf F} \le e + 3\|\mathbf{H}\|_2\,
(\delta_b + 2\sqrt{3(k+1)}\,\mu)$$
($e$ = `NLAlib.LanczosReorthRun.backwardRadius`) has Lanczos tridiagonal $\mathbf{T}_k$ from
$\mathbf{b}$ itself. No printed source.
Result: lanczos-reorth-backward-model -/
theorem exists_pure_backward (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {b : Fin n → ℝ} (hb : b ≠ 0) {δb : ℝ}
    (hδ : ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - L.v 1)‖ ≤ δb) :
    ∃ H' : Matrix (Fin n) (Fin n) ℝ, H'ᵀ = H' ∧
      frobNorm (H' - L.H) ≤ L.backwardRadius +
        3 * specNorm L.H * (δb + 2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel) ∧
      lanczosTridiagonal H' b k = L.toLanczosData.tridiagonal := by
  obtain ⟨E, hEt, hEf, hst, hT, hu⟩ := L.exists_lanczosState_backward hη hsmall hrec hτ
  set u := colSeq (polarFactor (basisOf L.v (k + 1))) 1 with hu_def
  set bh := ‖WithLp.toLp 2 b‖⁻¹ • b with hbh
  have hb0 : 0 < ‖WithLp.toLp 2 b‖ := by
    rw [norm_pos_iff]; exact fun h => hb (by simpa using congrArg WithLp.ofLp h)
  have hbh1 : ‖WithLp.toLp 2 bh‖ = 1 := by
    rw [hbh, WithLp.toLp_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hb0.ne']
  -- `u` is a unit vector: it is normalized by the first Lanczos state and close to `v 1`
  have hu1 : ‖WithLp.toLp 2 u‖ = 1 := by
    have hcur := congrArg LanczosState.cur (hst 0 L.k_pos)
    simp only [lanczosState, zero_add, ← hu_def] at hcur
    have hv1 := L.abs_norm_v_sq_sub_one_le 1 le_rfl (by omega)
    have htri := norm_sub_norm_le (WithLp.toLp 2 (L.v 1)) (WithLp.toLp 2 u)
    rw [norm_sub_rev, ← WithLp.toLp_sub] at htri
    have hupos : 0 < ‖WithLp.toLp 2 u‖ := by
      nlinarith [abs_le.mp hv1, L.ε_le, norm_nonneg (WithLp.toLp 2 (L.v 1))]
    have h := congrArg (fun x => ‖WithLp.toLp 2 x‖) hcur
    simp only [WithLp.toLp_smul, norm_smul, norm_inv, norm_algebraMap', norm_norm,
      inv_mul_cancel₀ hupos.ne'] at h
    exact h.symm
  obtain ⟨Z, hZ, hZu, -, hZf⟩ := exists_orthogonal_mulVec_eq_specNorm_sub_one_le hu1 hbh1
  have hZ' : HasOrthonormalCols Z := by
    rw [hasOrthonormalCols_iff, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hZ
  have hd : ‖WithLp.toLp 2 (u - bh)‖ ≤ δb + 2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel := by
    have := norm_sub_le (WithLp.toLp 2 (u - L.v 1)) (WithLp.toLp 2 (bh - L.v 1))
    rw [← WithLp.toLp_sub, sub_sub_sub_cancel_right] at this
    linarith
  refine ⟨Z * (L.H + E) * Zᵀ, ?_, ?_, ?_⟩
  · simp only [Matrix.transpose_mul, Matrix.transpose_add, L.transpose_H, hEt,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  · have hf : frobNorm (Z - 1) ≤ 3 / 2 * (δb + 2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel) :=
      hZf.trans (mul_le_mul (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) hd
        (norm_nonneg _) (by norm_num))
    have hZt : Zᵀ = Zᴴ := (Matrix.conjTranspose_eq_transpose_of_trivial Z).symm
    calc frobNorm (Z * (L.H + E) * Zᵀ - L.H)
        = frobNorm (Z * E * Zᵀ + ((Z - 1) * L.H * Zᵀ + L.H * (Z - 1)ᵀ)) := by
          rw [Matrix.transpose_sub, Matrix.transpose_one]; congr 1; noncomm_ring
      _ ≤ frobNorm (Z * E * Zᵀ) + (frobNorm ((Z - 1) * L.H * Zᵀ) + frobNorm (L.H * (Z - 1)ᵀ)) :=
          (frobNorm_add_le _ _).trans (add_le_add le_rfl (frobNorm_add_le _ _))
      _ ≤ L.backwardRadius +
            (frobNorm (Z - 1) * specNorm L.H + specNorm L.H * frobNorm (Z - 1)) := by
          rw [hZt, hZ'.frobNorm_mul_conjTranspose_right, hZ'.frobNorm_mul_conjTranspose_right,
            hZ'.frobNorm_mul_left]
          gcongr
          · exact frobNorm_mul_le_frobNorm_mul_specNorm _ _
          · rw [← frobNorm_transpose (Z - 1)]
            exact frobNorm_mul_le_specNorm_mul_frobNorm _ _
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hf (specNorm_nonneg L.H)]
  · have hstate : lanczosState (Z * (L.H + E) * Zᵀ) b =
        lanczosState (Z * (L.H + E) * Zᵀ) (Z *ᵥ u) := by
      funext j
      induction j with
      | zero =>
        simp only [lanczosState, hZu, hbh1, RCLike.ofReal_real_eq_id, id, inv_one, one_smul]
        rfl
      | succ j ih => simp only [lanczosState, ih]
    simp only [lanczosTridiagonal, hstate]
    rw [← lanczosTridiagonal, lanczosTridiagonal_mul_mul_transpose hZ, hT]

end LanczosReorthRun

end NLAlib
