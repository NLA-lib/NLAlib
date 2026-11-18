/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.GivensRounded

/-!
# Chains of Givens rotations taking a coordinate vector to a computed vector

Errors along a chain of unitary steps add up (`NLAlib.norm_toLp_sub_mulVec_le_sum`,
`NLAlib.specNorm_sub_mul_mul_conjTranspose_le_sum`). Applied to $N - 1$ Givens rotations of
adjacent coordinates, each computed within a relative error $\eta$, this gives a unitary matrix
whose last column is a unit multiple of the normalized computed vector up to $O(N\eta)$, and a
spectral-norm error $O(N\eta)\|\mathbf{A}\|_2$ for the similarity it applies: the rotations of
the random Hessenberg form of [BanksGarzaVargasSrivastava2025].

## Main results

* `NLAlib.exists_hasOrthonormalCols_rotateTo`: rotations taking $\mathbf{e}_N$ to a computed
  vector.
* `NLAlib.norm_toLp_sub_mulVec_le_sum`, `NLAlib.specNorm_sub_mul_mul_conjTranspose_le_sum`: errors
  along a chain of unitary steps add up.
* `NLAlib.exists_norm_conjTranspose_col_sub_le`, `NLAlib.specNorm_sub_rotateTo_le`: its vector and
  matrix parts.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Ops

variable {n : ℕ}

/-- $(1 + x)^n - 1 \le nx + (nx)^2$ for $x \ge 0$ and $nx \le 1$. -/
theorem one_add_pow_sub_one_le {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hnx : n * x ≤ 1) :
    (1 + x) ^ n - 1 ≤ n * x + (n * x) ^ 2 := by
  have h1 : (1 + x) ^ n ≤ Real.exp (n * x) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n
  have h2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := n * x)
    (by rw [abs_of_nonneg (by positivity)]; exact hnx))).2
  linarith

/-- The geometric accumulation: $\sum_{j < n} x(1 + x)^j = (1 + x)^n - 1$. -/
theorem sum_mul_one_add_pow (x : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, x * (1 + x) ^ j = (1 + x) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- Errors along a chain of isometries add up: if $x_{j+1}$ is within $\varepsilon_j$ of
$\mathbf{U}_j x_j$ for unitary $\mathbf{U}_j$ and $\mathbf{P}_{j+1} = \mathbf{U}_j\mathbf{P}_j$,
$\mathbf{P}_0 = \mathbf{I}$, then $x_k$ is within $\sum_{j<k}\varepsilon_j$ of
$\mathbf{P}_k x_0$. -/
theorem norm_toLp_sub_mulVec_le_sum {m : Type*} [Fintype m] [DecidableEq m]
    {U P : ℕ → Matrix m m ℂ} (hU : ∀ j, HasOrthonormalCols (U j)) (hP0 : P 0 = 1)
    (hP : ∀ j, P (j + 1) = U j * P j) (x : ℕ → m → ℂ) (k : ℕ) :
    ‖WithLp.toLp 2 (x k - P k *ᵥ x 0)‖ ≤
      ∑ j ∈ Finset.range k, ‖WithLp.toLp 2 (x (j + 1) - U j *ᵥ x j)‖ := by
  induction k with
  | zero => simp [hP0]
  | succ k ih =>
    have he : x (k + 1) - P (k + 1) *ᵥ x 0 =
        (x (k + 1) - U k *ᵥ x k) + U k *ᵥ (x k - P k *ᵥ x 0) := by
      rw [hP, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]; abel
    rw [he, WithLp.toLp_add, Finset.sum_range_succ]
    refine (norm_add_le _ _).trans ?_
    rw [(hU k).norm_toLp_mulVec]
    linarith

/-- Errors along a chain of unitary similarities add up: if $\mathbf{A}_{j+1}$ is within
$\varepsilon_j$ of $\mathbf{U}_j\mathbf{A}_j\mathbf{U}_j^{\mathsf H}$ for unitary
$\mathbf{U}_j$, then $\mathbf{A}_k$ is within $\sum_{j<k}\varepsilon_j$ of
$\mathbf{P}_k\mathbf{A}_0\mathbf{P}_k^{\mathsf H}$. -/
theorem specNorm_sub_mul_mul_conjTranspose_le_sum {m : Type*} [Fintype m] [DecidableEq m]
    {U P : ℕ → Matrix m m ℂ} (hU : ∀ j, HasOrthonormalCols (U j)) (hP0 : P 0 = 1)
    (hP : ∀ j, P (j + 1) = U j * P j) (A : ℕ → Matrix m m ℂ) (k : ℕ) :
    specNorm (A k - P k * A 0 * (P k)ᴴ) ≤
      ∑ j ∈ Finset.range k, specNorm (A (j + 1) - U j * A j * (U j)ᴴ) := by
  induction k with
  | zero => simp [hP0]
  | succ k ih =>
    have he : A (k + 1) - P (k + 1) * A 0 * (P (k + 1))ᴴ =
        (A (k + 1) - U k * A k * (U k)ᴴ) + U k * (A k - P k * A 0 * (P k)ᴴ) * (U k)ᴴ := by
      rw [hP, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      abel
    rw [he, Finset.sum_range_succ]
    refine (specNorm_add_le _ _).trans ?_
    rw [(hU k).conjTranspose.specNorm_mul_right, (hU k).specNorm_mul_left]
    linarith

/-- Truncating a vector to its first $k$ coordinates does not increase its norm. -/
theorem norm_toLp_truncate_le {m : ℕ} (x : Fin m → ℂ) (k : ℕ) :
    ‖WithLp.toLp 2 (fun i : Fin m => if (i : ℕ) < k then x i else 0)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  dsimp only
  split_ifs <;> simp

/-- A rotation that zeros coordinate $j$ of $x$ moves the truncation point by one: the first
$j + 1$ coordinates of $\mathbf{G}_j x$ are the first $j$ coordinates of $x$ and a zero. -/
theorem truncate_givens_mulVec {n : ℕ} (j : Fin n) (x : Fin (n + 1) → ℂ) :
    (fun i : Fin (n + 1) => if (i : ℕ) < (j : ℕ) + 1 then
        (givens j.castSucc j.succ (givensCoeffs (star (x j.succ)) (-star (x j.castSucc))).1
          (givensCoeffs (star (x j.succ)) (-star (x j.castSucc))).2 *ᵥ x) i else 0) =
      fun i : Fin (n + 1) => if (i : ℕ) < (j : ℕ) then x i else 0 := by
  have hne : j.castSucc ≠ j.succ := Fin.ne_of_val_ne (by simp)
  funext i
  by_cases hij : (i : ℕ) < j
  · rw [if_pos (by omega), if_pos hij, givens_mulVec_apply_of_ne (Fin.ne_of_val_ne (by simp; omega))
      (Fin.ne_of_val_ne (by simp; omega))]
  · rw [if_neg hij]
    by_cases hi : (i : ℕ) = j
    · rw [if_pos (by omega), show i = j.castSucc from Fin.ext (by simp [hi]),
        givens_mulVec_apply_left hne]
      have h := neg_star_givensCoeffs_snd_mul_add (star (x j.succ)) (-star (x j.castSucc))
      have h' := congrArg star h
      simp only [star_add, star_mul, star_neg, star_star, star_zero] at h'
      linear_combination -h'
    · rw [if_neg (by omega)]

/-- The scalar step of `NLAlib.exists_hasOrthonormalCols_rotateTo`: a vector $v$ of norm
$\gamma > 0$ whose first $n$ coordinates have norm $t$ is, after a phase, within
$\sqrt2\,t/\gamma$ of $\gamma\mathbf{e}_{n+1}$, relatively. -/
theorem exists_norm_single_sub_smul_le {n : ℕ} (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖WithLp.toLp 2 (Pi.single (Fin.last n) 1 -
      (c * ((‖WithLp.toLp 2 v‖⁻¹ : ℝ) : ℂ)) • v)‖ ≤ √2 * (‖WithLp.toLp 2 (fun i : Fin (n + 1) =>
        if (i : ℕ) < n then v i else 0)‖ / ‖WithLp.toLp 2 v‖) := by
  set γ := ‖WithLp.toLp 2 v‖ with hγ
  have hγ0 : 0 < γ := norm_pos_iff.mpr (by simpa using hv)
  set w := ‖v (Fin.last n)‖
  set t := ‖WithLp.toLp 2 (fun i : Fin (n + 1) => if (i : ℕ) < n then v i else 0)‖
  have hsq : γ ^ 2 = t ^ 2 + w ^ 2 := by
    simp only [γ, t, w, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc, Fin.val_castSucc,
      Fin.val_last, lt_irrefl, if_false, Fin.is_lt, if_true, norm_zero]
    simp
  refine ⟨if v (Fin.last n) = 0 then 1 else star (v (Fin.last n)) / (w : ℂ), ?_, ?_⟩
  · split_ifs with h
    · simp
    · rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr h)]
  set c : ℂ := if v (Fin.last n) = 0 then 1 else star (v (Fin.last n)) / (w : ℂ) with hc
  have hc' : ‖c * ((γ⁻¹ : ℝ) : ℂ)‖ = γ⁻¹ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hc]
    split_ifs with h
    · simp
    · rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr h), one_mul]
  have hlast : c * ((γ⁻¹ : ℝ) : ℂ) * v (Fin.last n) = ((w / γ : ℝ) : ℂ) := by
    simp only [hc]
    split_ifs with h
    · simp [w, h]
    · have hw : (w : ℂ) ≠ 0 := by simpa [w] using h
      calc star (v (Fin.last n)) / (w : ℂ) * ((γ⁻¹ : ℝ) : ℂ) * v (Fin.last n)
          = v (Fin.last n) * star (v (Fin.last n)) * ((γ⁻¹ : ℝ) : ℂ) / w := by ring
        _ = ((w / γ : ℝ) : ℂ) := by
          rw [Complex.star_def, Complex.mul_conj']
          push_cast
          field_simp
          rfl
  have hw : w ≤ γ := by nlinarith [norm_nonneg (WithLp.toLp 2 (fun i : Fin (n + 1) =>
    if (i : ℕ) < n then v i else 0)), norm_nonneg (v (Fin.last n))]
  have ht2 : t ^ 2 = ∑ i : Fin n, ‖v i.castSucc‖ ^ 2 := by
    simp [t, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  have h2 : ‖WithLp.toLp 2 (Pi.single (Fin.last n) 1 - (c * ((γ⁻¹ : ℝ) : ℂ)) • v)‖ ^ 2 =
      γ⁻¹ ^ 2 * t ^ 2 + (1 - w / γ) ^ 2 := by
    rw [ht2, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc, Finset.mul_sum]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]
    rw [hlast]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne, zero_sub, norm_neg, norm_mul, hc',
        mul_pow]
    · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        sq_abs]
  have h3 : (1 - w / γ) ^ 2 ≤ γ⁻¹ ^ 2 * t ^ 2 := by
    rw [show 1 - w / γ = γ⁻¹ * (γ - w) by field_simp, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith [norm_nonneg (v (Fin.last n))]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [h2, mul_pow, Real.sq_sqrt zero_le_two, div_pow]
  have e : γ⁻¹ ^ 2 * t ^ 2 = t ^ 2 / γ ^ 2 := by rw [inv_pow, mul_comm, div_eq_mul_inv]
  linarith

/-- The vector part of `NLAlib.exists_hasOrthonormalCols_rotateTo`: along the rotations
$\mathbf{U}_j$ that zero the computed vectors one coordinate at a time, the last column of
$\mathbf{P}_n^{\mathsf H}$, $\mathbf{P}_n = \mathbf{U}_{n-1}\cdots\mathbf{U}_0$, is within $5n\eta$
of the direction of $\mathbf{g}^{(0)}$, up to a phase. -/
theorem exists_norm_conjTranspose_col_sub_le {n : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (hnη : n * η ≤ 1 / 8) {cs : ℕ → ℂ × ℂ} {g : ℕ → Fin (n + 1) → ℂ}
    {U P : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hU : ∀ j, HasOrthonormalCols (U j))
    (hP0 : P 0 = 1) (hP : ∀ j, P (j + 1) = U j * P j)
    (hUj : ∀ j : Fin n, U j = givens j.castSucc j.succ (cs j).1 (cs j).2)
    (hcs : ∀ j : Fin n, cs j = givensCoeffs (star (g j j.succ)) (-star (g j j.castSucc)))
    (hg : ∀ j : Fin n, ‖WithLp.toLp 2 (g ((j : ℕ) + 1) - U j *ᵥ g j)‖ ≤
      η * ‖WithLp.toLp 2 (g j)‖) (hg0 : g 0 ≠ 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖WithLp.toLp 2 ((fun k => (P n)ᴴ k (Fin.last n)) -
      (c * ((‖WithLp.toLp 2 (g 0)‖⁻¹ : ℝ) : ℂ)) • g 0)‖ ≤ 5 * n * η := by
  set γ := ‖WithLp.toLp 2 (g 0)‖
  have hγ : 0 < γ := norm_pos_iff.mpr (by simpa using hg0)
  set tr : ℕ → (Fin (n + 1) → ℂ) → Fin (n + 1) → ℂ := fun k x i => if (i : ℕ) < k then x i else 0
  have htr_sub : ∀ k x y, tr k (x - y) = tr k x - tr k y := fun k x y => by
    funext i; simp only [tr, Pi.sub_apply]; split_ifs <;> simp
  set E := ∑ j ∈ Finset.range n, ‖WithLp.toLp 2 (g (j + 1) - U j *ᵥ g j)‖
  have hPu : ∀ k, HasOrthonormalCols (P k) := fun k => by
    induction k with
    | zero => rw [hP0]; exact hasOrthonormalCols_one
    | succ k ih => rw [hP]; exact (hU k).mul ih
  have hgrow : ∀ j ≤ n, ‖WithLp.toLp 2 (g j)‖ ≤ (1 + η) ^ j * γ := fun j => by
    induction j with
    | zero => simp [γ]
    | succ j ih =>
      intro hj
      have h := hg ⟨j, by omega⟩
      have h1 := norm_sub_norm_le (WithLp.toLp 2 (g (j + 1))) (WithLp.toLp 2 (U j *ᵥ g j))
      rw [← WithLp.toLp_sub, (hU j).norm_toLp_mulVec] at h1
      rw [pow_succ]
      nlinarith [ih (by omega)]
  have hE : E ≤ 9 / 8 * (n * η) * γ := by
    calc E ≤ ∑ j ∈ Finset.range n, η * (1 + η) ^ j * γ := Finset.sum_le_sum fun j hj => by
          have hj' := Finset.mem_range.mp hj
          have := hg ⟨j, hj'⟩
          nlinarith [hgrow j hj'.le]
      _ = ((1 + η) ^ n - 1) * γ := by rw [← Finset.sum_mul, sum_mul_one_add_pow]
      _ ≤ (n * η + (n * η) ^ 2) * γ := by
          gcongr; exact one_add_pow_sub_one_le hη (by linarith)
      _ ≤ 9 / 8 * (n * η) * γ := by gcongr; nlinarith [mul_nonneg n.cast_nonneg hη]
  have htail : ∀ k ≤ n, ‖WithLp.toLp 2 (tr k (g k))‖ ≤
      ∑ j ∈ Finset.range k, ‖WithLp.toLp 2 (g (j + 1) - U j *ᵥ g j)‖ := fun k => by
    induction k with
    | zero => simp [tr]; rfl
    | succ k ih =>
      intro hk
      have he : tr (k + 1) (g (k + 1)) = tr (k + 1) (g (k + 1) - U k *ᵥ g k) + tr k (g k) := by
        have h := truncate_givens_mulVec (⟨k, by omega⟩ : Fin n) (g k)
        rw [← hcs ⟨k, by omega⟩, ← hUj ⟨k, by omega⟩] at h
        rw [htr_sub, show tr (k + 1) (U k *ᵥ g k) = tr k (g k) from h]
        abel
      rw [he, WithLp.toLp_add, Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 := norm_toLp_truncate_le (g (k + 1) - U k *ᵥ g k) (k + 1)
      exact (norm_add_le _ _).trans (by linarith)
  set v := P n *ᵥ g 0
  have hv : ‖WithLp.toLp 2 v‖ = γ := (hPu n).norm_toLp_mulVec _
  have hv0 : v ≠ 0 := fun h => by rw [h] at hv; simp at hv; linarith
  have hprop := norm_toLp_sub_mulVec_le_sum hU hP0 hP g n
  have htv : ‖WithLp.toLp 2 (tr n v)‖ ≤ 2 * E := by
    have h : tr n v = tr n (g n) - tr n (g n - v) := by rw [htr_sub]; abel
    rw [h, WithLp.toLp_sub]
    refine (norm_sub_le _ _).trans ?_
    linarith [htail n le_rfl, norm_toLp_truncate_le (g n - v) n]
  obtain ⟨c, hc1, hc⟩ := exists_norm_single_sub_smul_le v hv0
  refine ⟨c, hc1, ?_⟩
  rw [hv] at hc
  have hcol : (fun k => (P n)ᴴ k (Fin.last n)) - (c * ((γ⁻¹ : ℝ) : ℂ)) • g 0 =
      (P n)ᴴ *ᵥ (Pi.single (Fin.last n) 1 - (c * ((γ⁻¹ : ℝ) : ℂ)) • v) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      (hPu n).conjTranspose_mul_self, Matrix.one_mulVec]
    congr 1
    funext k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hcol, (hPu n).conjTranspose.norm_toLp_mulVec]
  refine hc.trans ?_
  have hs : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc √2 * (‖WithLp.toLp 2 (tr n v)‖ / γ) ≤ 3 / 2 * (2 * E / γ) := by gcongr
    _ ≤ 3 / 2 * (2 * (9 / 8 * (n * η) * γ) / γ) := by gcongr
    _ ≤ 5 * n * η := by
        field_simp
        nlinarith [mul_nonneg n.cast_nonneg hη]

/-- The matrix part of `NLAlib.exists_hasOrthonormalCols_rotateTo`: rounded rotations of the
rows and then the columns $j, j + 1$ by $\mathbf{U}_j$, each with relative error $\eta$ per pair,
keep $\mathbf{A}_n$ within $8n\eta\|\mathbf{A}_0\|_2$ of
$\mathbf{P}_n\mathbf{A}_0\mathbf{P}_n^{\mathsf H}$ for $n\eta \le 1/8$. -/
theorem specNorm_sub_rotateTo_le {n : ℕ} {η : ℝ} (hη : 0 ≤ η) (hnη : n * η ≤ 1 / 8)
    {cs : ℕ → ℂ × ℂ} {A : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {U P : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hU : ∀ j, HasOrthonormalCols (U j))
    (hP0 : P 0 = 1) (hP : ∀ j, P (j + 1) = U j * P j)
    (hUj : ∀ j : Fin n, U j = givens j.castSucc j.succ (cs j).1 (cs j).2)
    (hA : ∀ j : Fin n, ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsRoundedRowRotation η j.castSucc j.succ (cs j).1 (cs j).2 (A j) A' ∧
        IsRoundedColRotation η j.castSucc j.succ (cs j).1 (cs j).2 A' (A ((j : ℕ) + 1))) :
    specNorm (A n - P n * A 0 * (P n)ᴴ) ≤ 8 * n * η * specNorm (A 0) := by
  set β := 4 * η + 4 * η ^ 2
  have hβ : 0 ≤ β := by positivity
  have hD : ∀ j < n, specNorm (A (j + 1) - U j * A j * (U j)ᴴ) ≤ β * specNorm (A j) := by
    intro j hj
    obtain ⟨A', hr, hc⟩ := hA ⟨j, hj⟩
    have h1 := hr.specNorm_sub_le hη
    have h2 := hc.specNorm_sub_le hη
    rw [← hUj ⟨j, hj⟩] at h1 h2
    have h3 : specNorm A' ≤ (1 + 2 * η) * specNorm (A j) := by
      have := (abs_le.mp (abs_specNorm_sub_specNorm_le A' (U j * A j))).2
      rw [(hU j).specNorm_mul_left] at this
      linarith
    have he : A (j + 1) - U j * A j * (U j)ᴴ =
        (A (j + 1) - A' * (U j)ᴴ) + (A' - U j * A j) * (U j)ᴴ := by
      simp only [Matrix.sub_mul]; abel
    rw [he]
    refine (specNorm_add_le _ _).trans ?_
    rw [(hU j).conjTranspose.specNorm_mul_right]
    nlinarith [specNorm_nonneg (A j)]
  have hgrow : ∀ j ≤ n, specNorm (A j) ≤ (1 + β) ^ j * specNorm (A 0) := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have h := (abs_le.mp (abs_specNorm_sub_specNorm_le (A (j + 1)) (U j * A j * (U j)ᴴ))).2
      rw [(hU j).conjTranspose.specNorm_mul_right, (hU j).specNorm_mul_left] at h
      rw [pow_succ]
      nlinarith [hD j (by omega), ih (by omega), specNorm_nonneg (A j)]
  refine (specNorm_sub_mul_mul_conjTranspose_le_sum hU hP0 hP A n).trans ?_
  calc ∑ j ∈ Finset.range n, specNorm (A (j + 1) - U j * A j * (U j)ᴴ)
      ≤ ∑ j ∈ Finset.range n, β * (1 + β) ^ j * specNorm (A 0) :=
        Finset.sum_le_sum fun j hj => by
          have hj' := Finset.mem_range.mp hj
          nlinarith [hD j hj', hgrow j hj'.le]
    _ = ((1 + β) ^ n - 1) * specNorm (A 0) := by rw [← Finset.sum_mul, sum_mul_one_add_pow]
    _ ≤ 8 * n * η * specNorm (A 0) := by
        refine mul_le_mul_of_nonneg_right ?_ (specNorm_nonneg _)
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        have hη8 : η ≤ 1 / 8 := le_trans (le_mul_of_one_le_left hη
          (by exact_mod_cast hn)) hnη
        have hnβ : n * β ≤ 9 / 2 * (n * η) := by
          simp only [β]; nlinarith [mul_nonneg n.cast_nonneg hη]
        refine (one_add_pow_sub_one_le hβ (by linarith)).trans ?_
        nlinarith [mul_nonneg n.cast_nonneg hβ]

/-- Rotating $\mathbf{e}_N$ to a computed vector: let $n$ adjacent rotations, step $j$ by the
exact Givens rotation $\mathbf{G}_j$ of the coefficients $(c_j, s_j)$ that
`NLAlib.givensCoeffs` computes from $(\bar g^{(j)}_{j+1}, -\bar g^{(j)}_j)$ (so that
$\mathbf{G}_j$ zeros entry $j$ of $\mathbf{g}^{(j)}$), take the vectors
$\mathbf{g}^{(j+1)}$ within $\eta\|\mathbf{g}^{(j)}\|$ of $\mathbf{G}_j\mathbf{g}^{(j)}$, and the
matrices $\mathbf{A}_{j+1}$ by a rounded rotation of the rows $j, j + 1$ and then of the columns
$j, j + 1$ of $\mathbf{A}_j$ (`NLAlib.IsRoundedRowRotation`, `NLAlib.IsRoundedColRotation`, relative
error $\eta \ge 0$), with $n\eta \le 1/8$ and $\mathbf{g}^{(0)} \ne 0$. Then there are a unitary
$\mathbf{Q}$ and $\lvert c\rvert = 1$ with
$$\|\mathbf{Q}\mathbf{e}_N - c\,\mathbf{g}^{(0)}/\|\mathbf{g}^{(0)}\|\| \le 5n\eta, \qquad
  \|\mathbf{A}_n - \mathbf{Q}^{\mathsf{H}}\mathbf{A}_0\mathbf{Q}\|_2 \le
  8n\eta\|\mathbf{A}_0\|_2\,.$$
The rounded coefficients and their application meet the hypotheses with $\eta = 12\boldsymbol{u}$
(`NLAlib.Ops.StdModel.norm_rotatePair_sub_le`). The last column is close to the direction of
$\mathbf{g}^{(0)}$, not equal to it: the computed rotations do not zero their entries exactly.
No printed source. -/
theorem exists_hasOrthonormalCols_rotateTo {η : ℝ} (hη : 0 ≤ η) (hnη : n * η ≤ 1 / 8)
    {cs : ℕ → ℂ × ℂ} {g : ℕ → Fin (n + 1) → ℂ} {A : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hcs : ∀ j : Fin n, cs j = givensCoeffs (star (g j j.succ)) (-star (g j j.castSucc)))
    (hg : ∀ j : Fin n, ‖WithLp.toLp 2 (g ((j : ℕ) + 1) -
      givens j.castSucc j.succ (cs j).1 (cs j).2 *ᵥ g j)‖ ≤ η * ‖WithLp.toLp 2 (g j)‖)
    (hA : ∀ j : Fin n, ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsRoundedRowRotation η j.castSucc j.succ (cs j).1 (cs j).2 (A j) A' ∧
        IsRoundedColRotation η j.castSucc j.succ (cs j).1 (cs j).2 A' (A ((j : ℕ) + 1)))
    (hg0 : g 0 ≠ 0) :
    ∃ (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c : ℂ), HasOrthonormalCols Q ∧ ‖c‖ = 1 ∧
      ‖WithLp.toLp 2 ((fun k => Q k (Fin.last n)) -
          (c * ((‖WithLp.toLp 2 (g 0)‖⁻¹ : ℝ) : ℂ)) • g 0)‖ ≤ 5 * n * η ∧
      specNorm (A n - Qᴴ * A 0 * Q) ≤ 8 * n * η * specNorm (A 0) := by
  set U : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun j => if h : j < n then
    givens (⟨j, by omega⟩ : Fin (n + 1)) ⟨j + 1, by omega⟩ (cs j).1 (cs j).2 else 1 with hUdef
  have hUj : ∀ j : Fin n, U j = givens j.castSucc j.succ (cs j).1 (cs j).2 := fun j => by
    simp only [hUdef, dif_pos j.isLt]; rfl
  have hU : ∀ j, HasOrthonormalCols (U j) := fun j => by
    by_cases h : j < n
    · rw [show U j = U (⟨j, h⟩ : Fin n) from rfl, hUj]
      exact hasOrthonormalCols_givens (Fin.ne_of_val_ne (by simp))
        (by rw [hcs]; exact norm_givensCoeffs_fst_sq_add _ _)
    · simp only [hUdef, dif_neg h]; exact hasOrthonormalCols_one
  set P : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun k => Nat.rec 1 (fun j Pj => U j * Pj) k
  have hPu : ∀ k, HasOrthonormalCols (P k) := fun k => by
    induction k with
    | zero => exact hasOrthonormalCols_one
    | succ k ih => exact (hU k).mul ih
  obtain ⟨c, hc1, hcol⟩ := exists_norm_conjTranspose_col_sub_le hη hnη hU (P := P) rfl
    (fun _ => rfl) hUj hcs (fun j => by rw [hUj]; exact hg j) hg0
  refine ⟨(P n)ᴴ, c, (hPu n).conjTranspose, hc1, hcol, ?_⟩
  rw [Matrix.conjTranspose_conjTranspose]
  exact specNorm_sub_rotateTo_le hη hnη hU rfl (fun _ => rfl) hUj hA

/-- **One-sided chain, right multiplications**: if $\mathbf{X}_{j+1}$ is within
$e_j$ of $\mathbf{X}_j\mathbf{U}_j$ for unitaries $\mathbf{U}_j$, then $\mathbf{X}_k$ is within
$\sum_j e_j$ of $\mathbf{X}_0\mathbf{P}_k$, $\mathbf{P}_k = \mathbf{U}_0\cdots\mathbf{U}_{k-1}$. -/
theorem specNorm_sub_mul_le_sum {m : Type*} [Fintype m] [DecidableEq m]
    {U P : ℕ → Matrix m m ℂ} (hU : ∀ j, HasOrthonormalCols (U j)) (hP0 : P 0 = 1)
    (hP : ∀ j, P (j + 1) = P j * U j) (X : ℕ → Matrix m m ℂ) (k : ℕ) :
    specNorm (X k - X 0 * P k) ≤
      ∑ j ∈ Finset.range k, specNorm (X (j + 1) - X j * U j) := by
  induction k with
  | zero => simp [hP0]
  | succ k ih =>
    have he : X (k + 1) - X 0 * P (k + 1) =
        (X (k + 1) - X k * U k) + (X k - X 0 * P k) * U k := by
      rw [hP, Matrix.sub_mul, Matrix.mul_assoc]; abel
    rw [he, Finset.sum_range_succ]
    refine (specNorm_add_le _ _).trans ?_
    rw [(hU k).specNorm_mul_right]
    linarith

/-- **One-sided chain, left multiplications**: the mirror of `NLAlib.specNorm_sub_mul_le_sum`,
with $\mathbf{P}_{j+1} = \mathbf{U}_j\mathbf{P}_j$. -/
theorem specNorm_sub_mul_left_le_sum {m : Type*} [Fintype m] [DecidableEq m]
    {U P : ℕ → Matrix m m ℂ} (hU : ∀ j, HasOrthonormalCols (U j)ᴴ) (hP0 : P 0 = 1)
    (hP : ∀ j, P (j + 1) = U j * P j) (X : ℕ → Matrix m m ℂ) (k : ℕ) :
    specNorm (X k - P k * X 0) ≤
      ∑ j ∈ Finset.range k, specNorm (X (j + 1) - U j * X j) := by
  induction k with
  | zero => simp [hP0]
  | succ k ih =>
    have he : X (k + 1) - P (k + 1) * X 0 =
        (X (k + 1) - U k * X k) + U k * (X k - P k * X 0) := by
      rw [hP, Matrix.mul_sub, Matrix.mul_assoc]; abel
    rw [he, Finset.sum_range_succ]
    refine (specNorm_add_le _ _).trans ?_
    have hUk := (hU k).conjTranspose
    rw [Matrix.conjTranspose_conjTranspose] at hUk
    rw [hUk.specNorm_mul_left]
    linarith

end NLAlib
