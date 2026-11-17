/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Norms.Frobenius

/-!
# Perturbation of the QR factorization

For an invertible $\mathbf{M}$ with QR factorization $\mathbf{M} = \mathbf{Q}\mathbf{R}$
(positive diagonal) and a perturbation with $\eta = \|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_2 \le 1/4$,
the factors of $\mathbf{M} + \mathbf{E} = \widehat{\mathbf{Q}}\widehat{\mathbf{R}}$ satisfy
$\|\widehat{\mathbf{Q}} - \mathbf{Q}\|_{\mathsf F} \le
8\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_{\mathsf F}$ and
$\|\widehat{\mathbf{R}} - \mathbf{R}\|_{\mathsf F} \le 8\|\mathbf{M}^{-1}\|_2
\|\mathbf{R}\|_2\|\mathbf{E}\|_{\mathsf F}$ [Sun1991, Theorem 1.6], [ChangPaigeStewart1997].
[BanksGarzaVargasSrivastava2022, Lemma 3.7] states the bound on $\mathbf{R}$ with
$\|\mathbf{E}\|_2$; that form fails for large $n$ (the first-order term is an upper triangular
truncation, whose operator norm grows like $\log n$), so the Frobenius norm of $\mathbf{E}$ is
used here. The constants $8$ at $\eta \le 1/4$ are deliberately loose.

The last diagonal entry has an elementary bound with the factor $1 \pm \eta$ that needs no factor
perturbation: $\mathbf{R}_{nn} = \|\mathbf{e}_n^{\mathsf T}\mathbf{M}^{-1}\|_2^{-1}$, so
$\lvert\widehat{\mathbf{R}}_{nn}\rvert / \mathbf{R}_{nn} \in [1 - \eta, 1 + \eta]$ (the lower end
cannot be $(1 + \eta)^{-1}$: take $n = 0$, $\mathbf{M} = 1$, $\mathbf{E} = -1/2$).

## Main results

* `NLAlib.IsQR.frobNorm_sub_le_of_add`: the bound on the unitary factors.
* `NLAlib.IsQR.frobNorm_sub_triangular_le_of_add`: the bound on the triangular factors.
* `NLAlib.IsQR.frobNorm_mul_inv_sub_one_le_of_add`: the relative triangular factor
  $\widehat{\mathbf{R}}\mathbf{R}^{-1}$ is within
  $3\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_{\mathsf F}$ of $\mathbf{I}$; both factor bounds follow
  from it.
* `NLAlib.IsQR.last_le_of_add`, `NLAlib.IsQR.le_last_of_add`: the last diagonal entry.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {n : ℕ} {M E Q R Q' R' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}

/-- For a positive real $d$, $\lvert d - 1\rvert \le \lvert d - \bar d^{-1}\rvert$. -/
private theorem norm_sub_one_le_norm_sub_star_inv {d : ℂ} (hd : 0 < d) :
    ‖d - 1‖ ≤ ‖d - star d⁻¹‖ := by
  obtain ⟨r, hr, rfl⟩ := RCLike.pos_iff_exists_ofReal.mp hd
  rw [← RCLike.ofReal_inv, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_sub,
    ← RCLike.ofReal_one, ← RCLike.ofReal_sub, RCLike.norm_ofReal, RCLike.norm_ofReal]
  rw [show r - r⁻¹ = (r - 1) * (1 + r⁻¹) by field_simp; ring, abs_mul,
    abs_of_pos (by positivity : 0 < 1 + r⁻¹)]
  exact le_mul_of_one_le_right (abs_nonneg _) (le_add_of_nonneg_right (by positivity))

/-- An upper triangular $\mathbf{T}$ with positive diagonal satisfies $\|\mathbf{T} -
\mathbf{I}\|_{\mathsf F} \le \|\mathbf{T} - \mathbf{T}^{-\mathsf H}\|_{\mathsf F}$. -/
private theorem frobNorm_sub_one_le_of_isUpperTriangular {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hT : T.IsUpperTriangular) (hd : ∀ i, 0 < T i i) :
    frobNorm (T - 1) ≤ frobNorm (T - T⁻¹ᴴ) := by
  refine frobNorm_le_of_norm_apply_le fun i j => ?_
  simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [if_neg hij.ne, hT.inv hij, star_zero]
  · rw [if_pos rfl, hT.inv_apply_self (fun k => (hd k).ne') i]
    exact norm_sub_one_le_norm_sub_star_inv (hd i)
  · rw [if_neg hij.ne', hT hij, sub_self, norm_zero]
    exact norm_nonneg _

/-- A lower bound $c\|\mathbf{y}\| \le \|\mathbf{T}\mathbf{y}\|$, $c > 0$, bounds the inverse:
$\|\mathbf{T}^{-1}\|_2 \le c^{-1}$. -/
private theorem specNorm_inv_le_of_mul_norm_le {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hT : IsUnit T) {c : ℝ} (hc : 0 < c)
    (h : ∀ y, c * ‖WithLp.toLp 2 y‖ ≤ ‖WithLp.toLp 2 (T *ᵥ y)‖) : specNorm T⁻¹ ≤ c⁻¹ := by
  refine (specNorm_le_iff (inv_nonneg.2 hc.le)).2 fun x => ?_
  have hx := h (T⁻¹ *ᵥ x)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det T).mp hT),
    Matrix.one_mulVec] at hx
  rw [inv_mul_eq_div, le_div_iff₀ hc]
  linarith

/-- The factor $\mathbf{T} = \widehat{\mathbf{R}}\mathbf{R}^{-1}$ relating the QR factorizations
of $\mathbf{M}$ and $\mathbf{M} + \mathbf{E}$: it is upper triangular with positive diagonal,
$\widehat{\mathbf{Q}}\mathbf{T} = (\mathbf{I} + \mathbf{E}\mathbf{M}^{-1})\mathbf{Q}$, and
$\|\mathbf{T}^{-1}\|_2 \le (1 - \eta)^{-1}$. -/
private theorem IsQR.mul_inv_of_add (h : IsQR M Q R) (h' : IsQR (M + E) Q' R')
    (hR : ∀ i, 0 < R i i) (hR' : ∀ i, 0 < R' i i) (hη : specNorm M⁻¹ * specNorm E < 1) :
    (R' * R⁻¹).IsUpperTriangular ∧ (∀ i, 0 < (R' * R⁻¹) i i) ∧ R' * R⁻¹ * R = R' ∧
      IsUnit (R' * R⁻¹) ∧ Q' * (R' * R⁻¹) = (1 + E * M⁻¹) * Q ∧
      specNorm (R' * R⁻¹)⁻¹ ≤ (1 - specNorm M⁻¹ * specNorm E)⁻¹ := by
  have hQ := h.hasOrthonormalCols
  have hQ' := h'.hasOrthonormalCols
  have hRu : IsUnit R := h.isUnit fun i => (hR i).ne'
  have hRd := (Matrix.isUnit_iff_isUnit_det R).mp hRu
  set K := E * M⁻¹ with hK
  set T := R' * R⁻¹ with hTdef
  have hTU : T.IsUpperTriangular := h'.isUpperTriangular.mul h.isUpperTriangular.inv
  have hTR : T * R = R' := by
    rw [hTdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRd, Matrix.mul_one]
  have hTd : ∀ i, 0 < T i i := fun i => by
    have e := hTU.mul_apply_self h.isUpperTriangular i
    rw [hTR] at e
    rw [eq_div_of_mul_eq (hR i).ne' e.symm]
    exact div_pos (hR' i) (hR i)
  have hTu : IsUnit T :=
    (h'.isUnit fun i => (hR' i).ne').mul (Matrix.isUnit_nonsing_inv_iff.mpr hRu)
  have hQT : Q' * T = (1 + K) * Q := by
    have hMinv : M⁻¹ * Q = R⁻¹ := by
      rw [h.eq_mul, Matrix.mul_inv_rev, hQ.inv_eq, Matrix.mul_assoc, hQ.conjTranspose_mul_self,
        Matrix.mul_one]
    rw [hTdef, ← Matrix.mul_assoc, ← h'.eq_mul, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul,
      h.mul_inv_eq hRu, hK, Matrix.mul_assoc, hMinv]
  have hKs : specNorm K ≤ specNorm M⁻¹ * specNorm E :=
    (specNorm_mul_le E M⁻¹).trans_eq (mul_comm _ _)
  have hlow : ∀ y, (1 - specNorm M⁻¹ * specNorm E) * ‖WithLp.toLp 2 y‖ ≤
      ‖WithLp.toLp 2 (T *ᵥ y)‖ := fun y => by
    rw [← hQ'.norm_toLp_mulVec (T *ᵥ y), Matrix.mulVec_mulVec, hQT, ← Matrix.mulVec_mulVec,
      Matrix.add_mulVec, Matrix.one_mulVec, WithLp.toLp_add]
    have h1 := norm_toLp_mulVec_le K (Q *ᵥ y)
    have h2 := norm_sub_le (WithLp.toLp 2 (Q *ᵥ y) + WithLp.toLp 2 (K *ᵥ (Q *ᵥ y)))
      (WithLp.toLp 2 (K *ᵥ (Q *ᵥ y)))
    rw [add_sub_cancel_right, hQ.norm_toLp_mulVec] at h2
    rw [hQ.norm_toLp_mulVec] at h1
    nlinarith [mul_le_mul_of_nonneg_right hKs (norm_nonneg (WithLp.toLp 2 y))]
  exact ⟨hTU, hTd, hTR, hTu, hQT, specNorm_inv_le_of_mul_norm_le hTu (by linarith) hlow⟩

/-- The relative triangular factor under perturbation: for QR factorizations with positive
diagonals of $\mathbf{M}$ and $\mathbf{M} + \mathbf{E}$ and
$\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_2 \le 1/4$,
$\|\widehat{\mathbf{R}}\mathbf{R}^{-1} - \mathbf{I}\|_{\mathsf F} \le
3\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_{\mathsf F}$. -/
theorem IsQR.frobNorm_mul_inv_sub_one_le_of_add (h : IsQR M Q R) (h' : IsQR (M + E) Q' R')
    (hR : ∀ i, 0 < R i i) (hR' : ∀ i, 0 < R' i i) (hη : specNorm M⁻¹ * specNorm E ≤ 1 / 4) :
    frobNorm (R' * R⁻¹ - 1) ≤ 3 * (specNorm M⁻¹ * frobNorm E) := by
  obtain ⟨hTU, hTd, -, hTu, hQT, hTinv⟩ := h.mul_inv_of_add h' hR hR' (by linarith)
  have hQ := h.hasOrthonormalCols
  have hQ' := h'.hasOrthonormalCols
  have hKs : specNorm (E * M⁻¹) ≤ specNorm M⁻¹ * specNorm E :=
    (specNorm_mul_le E M⁻¹).trans_eq (mul_comm _ _)
  have hKf : frobNorm (E * M⁻¹) ≤ specNorm M⁻¹ * frobNorm E :=
    (frobNorm_mul_le_frobNorm_mul_specNorm E M⁻¹).trans_eq (mul_comm _ _)
  generalize E * M⁻¹ = K at hKs hKf hQT
  generalize R' * R⁻¹ = T at *
  have hTT : Tᴴ * T - 1 = Qᴴ * (Kᴴ + K + Kᴴ * K) * Q := by
    have e1 : Tᴴ * T = (Q' * T)ᴴ * (Q' * T) := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Q'ᴴ,
        hQ'.conjTranspose_mul_self, Matrix.one_mul]
    have e2 : Qᴴ * (Kᴴ + K + Kᴴ * K) * Q = Qᴴ * ((1 + Kᴴ) * (1 + K)) * Q - Qᴴ * Q := by
      noncomm_ring
    rw [e1, hQT, e2, hQ.conjTranspose_mul_self, Matrix.conjTranspose_mul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one]
    simp only [Matrix.mul_assoc]
  have hW : T - T⁻¹ᴴ = T⁻¹ᴴ * (Tᴴ * T - 1) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det T).mp hTu),
      Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hS : frobNorm (Tᴴ * T - 1) ≤ (2 + specNorm M⁻¹ * specNorm E) *
      (specNorm M⁻¹ * frobNorm E) := by
    rw [hTT, hQ.frobNorm_mul_right, hQ.conjTranspose.frobNorm_mul_left]
    calc frobNorm (Kᴴ + K + Kᴴ * K) ≤ frobNorm K + frobNorm K + specNorm K * frobNorm K := by
          refine (frobNorm_add_le _ _).trans (add_le_add ((frobNorm_add_le _ _).trans_eq ?_) ?_)
          · rw [frobNorm_conjTranspose]
          · simpa [specNorm_conjTranspose] using frobNorm_mul_le_specNorm_mul_frobNorm Kᴴ K
      _ ≤ _ := by nlinarith [frobNorm_nonneg K, specNorm_nonneg K]
  refine (frobNorm_sub_one_le_of_isUpperTriangular hTU hTd).trans ?_
  rw [hW]
  refine (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans ?_
  rw [specNorm_conjTranspose]
  have hφ := mul_nonneg (specNorm_nonneg M⁻¹) (frobNorm_nonneg E)
  calc specNorm T⁻¹ * frobNorm (Tᴴ * T - 1)
      ≤ (1 - specNorm M⁻¹ * specNorm E)⁻¹ *
        ((2 + specNorm M⁻¹ * specNorm E) * (specNorm M⁻¹ * frobNorm E)) := by
        gcongr
        exact inv_nonneg.2 (by linarith)
    _ ≤ _ := by
        rw [inv_mul_le_iff₀ (by linarith)]
        nlinarith

/-- **Perturbation of the triangular QR factor**, in the Frobenius norm of the perturbation:
$\|\widehat{\mathbf{R}} - \mathbf{R}\|_{\mathsf F} \le 8\|\mathbf{M}^{-1}\|_2\|\mathbf{R}\|_2
\|\mathbf{E}\|_{\mathsf F}$. [Sun1991, Theorem 1.6]; [BanksGarzaVargasSrivastava2022, Lemma 3.7]
(stated there with $\|\mathbf{E}\|_2$, which fails for large $n$). -/
theorem IsQR.frobNorm_sub_triangular_le_of_add (h : IsQR M Q R)
    (h' : IsQR (M + E) Q' R') (hR : ∀ i, 0 < R i i) (hR' : ∀ i, 0 < R' i i)
    (hη : specNorm M⁻¹ * specNorm E ≤ 1 / 4) :
    frobNorm (R' - R) ≤ 8 * specNorm M⁻¹ * specNorm R * frobNorm E := by
  obtain ⟨-, -, hTR, -⟩ := h.mul_inv_of_add h' hR hR' (by linarith)
  have hT1 := h.frobNorm_mul_inv_sub_one_le_of_add h' hR hR' hη
  calc frobNorm (R' - R) = frobNorm ((R' * R⁻¹ - 1) * R) := by
        rw [Matrix.sub_mul, hTR, Matrix.one_mul]
    _ ≤ frobNorm (R' * R⁻¹ - 1) * specNorm R := frobNorm_mul_le_frobNorm_mul_specNorm _ _
    _ ≤ 3 * (specNorm M⁻¹ * frobNorm E) * specNorm R := by gcongr
    _ ≤ _ := by nlinarith [specNorm_nonneg M⁻¹, frobNorm_nonneg E, specNorm_nonneg R,
          mul_nonneg (mul_nonneg (specNorm_nonneg M⁻¹) (frobNorm_nonneg E)) (specNorm_nonneg R)]

/-- **Perturbation of the unitary QR factor**: for QR factorizations with positive diagonals of
$\mathbf{M}$ and $\mathbf{M} + \mathbf{E}$, $\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_2 \le 1/4$ gives
$\|\widehat{\mathbf{Q}} - \mathbf{Q}\|_{\mathsf F} \le
8\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_{\mathsf F}$.
[Sun1991, Theorem 1.6]; [BanksGarzaVargasSrivastava2022, Lemma 3.7]. -/
theorem IsQR.frobNorm_sub_le_of_add (h : IsQR M Q R) (h' : IsQR (M + E) Q' R')
    (hR : ∀ i, 0 < R i i) (hR' : ∀ i, 0 < R' i i) (hη : specNorm M⁻¹ * specNorm E ≤ 1 / 4) :
    frobNorm (Q' - Q) ≤ 8 * specNorm M⁻¹ * frobNorm E := by
  obtain ⟨-, -, -, hTu, hQT, hTinv⟩ := h.mul_inv_of_add h' hR hR' (by linarith)
  have hT1 := h.frobNorm_mul_inv_sub_one_le_of_add h' hR hR' hη
  generalize R' * R⁻¹ = T at *
  have hTd := (Matrix.isUnit_iff_isUnit_det T).mp hTu
  -- `(Q' - Q) T = E M⁻¹ Q - Q (T - 1)`.
  have hD : Q' - Q = (E * M⁻¹ * Q - Q * (T - 1)) * T⁻¹ := by
    have e : (Q' - Q) * T = E * M⁻¹ * Q - Q * (T - 1) := by
      rw [Matrix.sub_mul, hQT]; noncomm_ring
    rw [← e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTd, Matrix.mul_one]
  have hφ := mul_nonneg (specNorm_nonneg M⁻¹) (frobNorm_nonneg E)
  have hK : frobNorm (E * M⁻¹ * Q) ≤ specNorm M⁻¹ * frobNorm E := by
    rw [h.hasOrthonormalCols.frobNorm_mul_right]
    exact (frobNorm_mul_le_frobNorm_mul_specNorm E M⁻¹).trans_eq (mul_comm _ _)
  have hinv : specNorm T⁻¹ ≤ 4 / 3 :=
    hTinv.trans ((inv_le_comm₀ (by linarith) (by norm_num)).2 (by linarith))
  rw [hD]
  calc frobNorm ((E * M⁻¹ * Q - Q * (T - 1)) * T⁻¹)
      ≤ frobNorm (E * M⁻¹ * Q - Q * (T - 1)) * specNorm T⁻¹ :=
        frobNorm_mul_le_frobNorm_mul_specNorm _ _
    _ ≤ (specNorm M⁻¹ * frobNorm E + 3 * (specNorm M⁻¹ * frobNorm E)) * (4 / 3) := by
        gcongr
        refine (frobNorm_sub_le _ _).trans (add_le_add hK ?_)
        rw [h.hasOrthonormalCols.frobNorm_mul_left]
        exact hT1
    _ ≤ _ := by nlinarith


/-- The factor
$\mathbf{X} = \widehat{\mathbf{Q}}^{\mathsf H}(\mathbf{I} + \mathbf{E}\mathbf{M}^{-1})\mathbf{Q}$
equals $\widehat{\mathbf{R}}\mathbf{R}^{-1}$, so it is upper triangular and
$\widehat{\mathbf{R}}_{nn} = \mathbf{X}_{nn}\mathbf{R}_{nn}$. -/
private theorem IsQR.last_eq_of_add (hM : IsUnit M) (h : IsQR M Q R) (h' : IsQR (M + E) Q' R')
    (hR : ∀ i, 0 < R i i) :
    (Q'ᴴ * (1 + E * M⁻¹) * Q).IsUpperTriangular ∧ R' (Fin.last n) (Fin.last n) =
      (Q'ᴴ * (1 + E * M⁻¹) * Q) (Fin.last n) (Fin.last n) * R (Fin.last n) (Fin.last n) := by
  have hRR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det R).mp (h.isUnit fun i => (hR i).ne'))
  have hX : Q'ᴴ * (1 + E * M⁻¹) * Q = R' * R⁻¹ := by
    have hQ : (1 + E * M⁻¹) * Q = (M + E) * R⁻¹ := by
      calc (1 + E * M⁻¹) * Q = (1 + E * M⁻¹) * M * R⁻¹ := by
            rw [Matrix.mul_assoc, h.mul_inv_eq (h.isUnit fun i => (hR i).ne')]
        _ = (M + E) * R⁻¹ := by
            rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc E,
              Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det M).mp hM),
              Matrix.mul_one]
    rw [Matrix.mul_assoc, hQ, ← Matrix.mul_assoc, h'.conjTranspose_mul_eq]
  have hlast : ∀ A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, A.IsUpperTriangular →
      (A * B) (Fin.last n) (Fin.last n) =
        A (Fin.last n) (Fin.last n) * B (Fin.last n) (Fin.last n) := by
    intro A B hA
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
    · intro k _ hk
      have h0 : A (Fin.last n) k = 0 := hA (lt_of_le_of_ne (Fin.le_last k) hk)
      rw [h0, zero_mul]
    · simp
  refine ⟨hX ▸ h'.isUpperTriangular.mul h.isUpperTriangular.inv, ?_⟩
  have h1 := hlast R R⁻¹ h.isUpperTriangular
  rw [hRR, Matrix.one_apply_eq] at h1
  rw [hX, hlast R' R⁻¹ h'.isUpperTriangular, mul_assoc, mul_comm _ (R _ _), ← h1, mul_one]

/-- The last diagonal entry under perturbation, upper bound: with
$\eta = \|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_2 < 1$, $\lvert\widehat{\mathbf{R}}_{nn}\rvert \le
(1 - \eta)^{-1}\mathbf{R}_{nn}$, for any QR factorization of $\mathbf{M} + \mathbf{E}$ (no sign
normalization). The proof also gives the smaller factor $1 + \eta$. -/
theorem IsQR.last_le_of_add (hM : IsUnit M) (h : IsQR M Q R) (h' : IsQR (M + E) Q' R')
    (hR : ∀ i, 0 < R i i) (hη : specNorm M⁻¹ * specNorm E < 1) :
    ‖R' (Fin.last n) (Fin.last n)‖ ≤
      (1 - specNorm M⁻¹ * specNorm E)⁻¹ * ‖R (Fin.last n) (Fin.last n)‖ := by
  have hη0 : 0 ≤ specNorm M⁻¹ * specNorm E := by positivity
  have hent := (h.last_eq_of_add hM h' hR).2
  have hspec : specNorm (Q'ᴴ * (1 + E * M⁻¹) * Q) ≤ 1 + specNorm M⁻¹ * specNorm E := by
    calc specNorm (Q'ᴴ * (1 + E * M⁻¹) * Q)
        ≤ specNorm Q'ᴴ * specNorm (1 + E * M⁻¹) * specNorm Q :=
          (specNorm_mul_le _ _).trans (by gcongr; exact specNorm_mul_le _ _)
      _ ≤ 1 * (1 + specNorm M⁻¹ * specNorm E) * 1 := by
          rw [specNorm_conjTranspose]
          gcongr
          · exact h'.hasOrthonormalCols.specNorm_le_one
          · refine (specNorm_add_le _ _).trans (add_le_add specNorm_one_le ?_)
            rw [mul_comm]
            exact specNorm_mul_le _ _
          · exact h.hasOrthonormalCols.specNorm_le_one
      _ = _ := by ring
  have hinv : 1 + specNorm M⁻¹ * specNorm E ≤ (1 - specNorm M⁻¹ * specNorm E)⁻¹ := by
    rw [inv_eq_one_div (1 - specNorm M⁻¹ * specNorm E), le_div_iff₀ (by linarith)]
    nlinarith
  rw [hent, norm_mul]
  gcongr
  exact ((norm_apply_le_specNorm _ _ _).trans hspec).trans hinv

/-- The last diagonal entry under perturbation, lower bound:
$(1 - \eta)\mathbf{R}_{nn} \le \lvert\widehat{\mathbf{R}}_{nn}\rvert$, for any QR factorization of
$\mathbf{M} + \mathbf{E}$. The last row of the upper triangular
$\mathbf{X} = \widehat{\mathbf{Q}}^{\mathsf H}(\mathbf{I} + \mathbf{E}\mathbf{M}^{-1})\mathbf{Q}$ is
$\mathbf{X}_{nn}\mathbf{e}_n^{\mathsf T}$, of norm at least $1 - \eta$. The factor $1 - \eta$ cannot
be raised to $(1 + \eta)^{-1}$: take $n = 0$, $\mathbf{M} = 1$, $\mathbf{E} = -1/2$. -/
theorem IsQR.le_last_of_add (hM : IsUnit M) (h : IsQR M Q R) (h' : IsQR (M + E) Q' R')
    (hR : ∀ i, 0 < R i i) :
    (1 - specNorm M⁻¹ * specNorm E) * ‖R (Fin.last n) (Fin.last n)‖ ≤
      ‖R' (Fin.last n) (Fin.last n)‖ := by
  obtain ⟨hXU, hent⟩ := h.last_eq_of_add hM h' hR
  have hKs : specNorm (E * M⁻¹)ᴴ ≤ specNorm M⁻¹ * specNorm E := by
    rw [specNorm_conjTranspose]; exact (specNorm_mul_le E M⁻¹).trans_eq (mul_comm _ _)
  generalize E * M⁻¹ = K at hXU hent hKs
  set X := Q'ᴴ * (1 + K) * Q
  set e : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1
  -- The last row of `X` is `X_nn eₙᵀ`.
  have hv : Xᴴ *ᵥ e = Pi.single (Fin.last n) (star (X (Fin.last n) (Fin.last n))) := by
    funext i
    simp only [e, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
      Matrix.conjTranspose_apply]
    rcases (Fin.le_last i).lt_or_eq with hi | rfl
    · rw [show X (Fin.last n) i = 0 from hXU hi, star_zero, Pi.single_eq_of_ne hi.ne]
    · rw [Pi.single_eq_same]
  have hXe : Xᴴ *ᵥ e = Qᴴ *ᵥ ((Q' *ᵥ e) + Kᴴ *ᵥ (Q' *ᵥ e)) := by
    simp only [X, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_add, Matrix.conjTranspose_one, ← Matrix.mulVec_mulVec,
      Matrix.add_mulVec, Matrix.one_mulVec]
  have hw : ‖WithLp.toLp 2 (Q' *ᵥ e)‖ = 1 := by
    rw [h'.hasOrthonormalCols.norm_toLp_mulVec]
    rw [PiLp.toLp_single, PiLp.norm_single, norm_one]
  have hnorm : ‖X (Fin.last n) (Fin.last n)‖ = ‖WithLp.toLp 2 (Xᴴ *ᵥ e)‖ := by
    rw [hv, PiLp.toLp_single, PiLp.norm_single, norm_star]
  have hX : 1 - specNorm M⁻¹ * specNorm E ≤ ‖X (Fin.last n) (Fin.last n)‖ := by
    rw [hnorm, hXe, h.hasOrthonormalCols.conjTranspose.norm_toLp_mulVec, WithLp.toLp_add]
    have h1 := norm_toLp_mulVec_le Kᴴ (Q' *ᵥ e)
    have h2 := norm_sub_le (WithLp.toLp 2 (Q' *ᵥ e) + WithLp.toLp 2 (Kᴴ *ᵥ (Q' *ᵥ e)))
      (WithLp.toLp 2 (Kᴴ *ᵥ (Q' *ᵥ e)))
    rw [add_sub_cancel_right, hw] at h2
    rw [hw] at h1
    nlinarith
  rw [hent, norm_mul]
  exact mul_le_mul_of_nonneg_right hX (norm_nonneg _)

end NLAlib
