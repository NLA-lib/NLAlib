/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedExc
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedRitz
public import NLAlibScaffold.Matrix.QRIteration.Ritz

/-!
# The rounded `Regularize`

`Regularize` ([BanksGarzaVargasSrivastava2022, §4.2], called $\mathsf{RitzOrDecouple}$ there)
computes forward-approximate Ritz values with `SmallEig`, perturbs each by an independent uniform
sample of a small disk, and tests the perturbed values with `Optimal`. If they are optimal it
returns them; otherwise the dichotomy
(`NLAlib.exists_mem_le_norm_inv_pow_of_not_isOptimalRitzValues`) gives one among them whose
degree $k$ step decouples, and the program tries them in turn. The random perturbation keeps
every shift away from the spectrum, which the forward error of the rounded steps needs.

## Main results

* `NLAlib.ShiftedQR.regularize_bad_window_le`: one perturbation comes within
  $\eta = R\sqrt{\varphi/(2k)}$ of an eigenvalue with probability at most $\varphi/(2k)$.
* `NLAlib.exists_norm_subdiag_le_hessenbergPotential`: some bottom subdiagonal entry is at most
  the potential.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- **Some bottom subdiagonal entry is at most the potential**: for $1 \le k \le n$ one of the
last $k$ subdiagonal entries has $\lvert\mathbf{H}_{i+1,i}\rvert \le \psi_k(\mathbf{H})$, the
geometric mean of their moduli. -/
theorem exists_norm_subdiag_le_hessenbergPotential {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H i.succ i.castSucc‖ ≤ hessenbergPotential k H := by
  set S := Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)
  have hmem : (⟨n - k, by omega⟩ : Fin n) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hne : S.Nonempty := ⟨_, hmem⟩
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ (fun i : Fin n => ‖H i.succ i.castSucc‖) hne
  have hcard : S.card = k := by
    rw [← Finset.card_map Fin.valEmbedding,
      show S.map Fin.valEmbedding = Finset.Ico (n - k) n by
        ext x
        simp only [S, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply, Finset.mem_Ico]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact ⟨by omega, i.isLt⟩
        · intro hx; exact ⟨⟨x, hx.2⟩, by simp only; omega, rfl⟩]
    simp only [Nat.card_Ico]; omega
  refine ⟨i0, (Finset.mem_filter.mp hi0).2, ?_⟩
  have hprod : ‖H i0.succ i0.castSucc‖ ^ k ≤ hessenbergPotential k H ^ k := by
    rw [hessenbergPotential_pow hk]
    calc ‖H i0.succ i0.castSucc‖ ^ k = ∏ _i ∈ S, ‖H i0.succ i0.castSucc‖ := by
          rw [Finset.prod_const, hcard]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hmin
  exact le_of_pow_le_pow_left₀ hk.ne' (hessenbergPotential_nonneg k H) hprod

/-- **Optimality does not depend on the order of the shifts**: the shift polynomial of a
permuted list is the same. -/
theorem isOptimalRitzValues_iff_of_perm {θ : ℝ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss ts : List ℂ} (h : ss.Perm ts) :
    IsOptimalRitzValues θ H ss ↔ IsOptimalRitzValues θ H ts := by
  have hp : shiftPoly ss = shiftPoly ts := (h.map _).prod_eq
  simp only [IsOptimalRitzValues, hp, h.length_eq]

/-- **A rounded step with a good shift decouples** ([BanksGarzaVargasSrivastava2022, proof of
Lemma 4.6]): let $\mathbf{H} \ne 0$ be upper Hessenberg, $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{e})$ with $\kappa(\mathbf{V}) \le B$,
$\|\mathbf{H}\|_2 \le \Sigma$, $1 \le k \le n$, $\omega > 0$, and $r$ a shift with
$\lvert r\rvert \le C\|\mathbf{H}\|_2$ ($C \ge 0$), at distance at least $d > 0$ from every
$e_i$, and $\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - r)^{-k}\| \ge (2/\omega)^k$. If
$\widehat{\mathbf{H}}$ is the result of a backward-stable chain of $k$ steps with the shift $r$
and relative error $x \ge 0$,
$$x \le (16B)^{-1}\Bigl(\frac{d}{(2 + 2C)\Sigma}\Bigr)^k, \qquad
(66 + 2C)B\Sigma\Bigl(\frac{(2 + 2C)\Sigma}{d}\Bigr)^k\sqrt{n + 1}\,x \le \frac{\omega}{2},$$
then one of the last $k$ subdiagonal entries of $\widehat{\mathbf{H}}$ has modulus at most
$\omega$: the exact step has its potential at most $\omega/2$, and the computed step is within
$\omega/2$ of it up to a diagonal unitary similarity. -/
theorem IsStableQRChain.exists_norm_subdiag_le_of_le_norm_inv_pow {x C B S d ω : ℝ} {k : ℕ}
    {H H' V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {r : ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x H (List.replicate k r) H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hd : 0 < d) (hω : 0 < ω) (hk : 0 < k) (hkn : k ≤ n) (hH0 : H ≠ 0)
    (hH : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e)
    (hκ : pseudoConditionNumber V ≤ B) (hS : specNorm H ≤ S) (hr : ‖r‖ ≤ C * specNorm H)
    (hdist : ∀ i, d ≤ ‖e i - r‖)
    (hτ : (2 / ω) ^ k ≤ ‖WithLp.toLp 2
      ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖)
    (hxu : x ≤ (16 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) * x ≤ ω / 2) :
    ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω := by
  have hHp : 0 < specNorm H :=
    (specNorm_nonneg H).lt_of_ne fun h0 => hH0 (specNorm_eq_zero_iff.mp h0.symm)
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num)
    ((one_le_pseudoConditionNumber hV.ne_zero).trans hκ)
  have hS0 : 0 < S := hHp.trans_le hS
  have hne : ∀ i, e i ≠ r := fun i he => by have := hdist i; rw [he, sub_self, norm_zero] at this; linarith
  set X := multiShiftedQRStep H (List.replicate k r)
  -- the exact step has its potential at most `ω / 2`
  have hpot := hH.hessenbergPotential_multiShiftedQRStep_replicate_pow_mul_le hk hkn
    (det_sub_smul_one_ne_zero_of_forall_ne hV hHV (fun i => hne i))
  rw [aeval_shiftPoly_replicate, ← Matrix.inv_pow'] at hτ
  have hψ : hessenbergPotential k X ≤ ω / 2 := by
    have h2 : 0 < (2 / ω) ^ k := by positivity
    have hle : hessenbergPotential k X ^ k * (2 / ω) ^ k ≤ 1 :=
      (mul_le_mul_of_nonneg_left hτ (pow_nonneg (hessenbergPotential_nonneg k X) k)).trans hpot
    have : hessenbergPotential k X ^ k ≤ (ω / 2) ^ k := by
      have h3 := (le_div_iff₀ h2).mpr hle
      rwa [one_div, ← inv_pow, inv_div] at h3
    exact le_of_pow_le_pow_left₀ hk.ne' (by positivity) this
  obtain ⟨i, hik, hi⟩ := exists_norm_subdiag_le_hessenbergPotential hk hkn X
  refine ⟨i, hik, ?_⟩
  -- the computed step is within `ω / 2` of the exact one, up to a diagonal unitary
  have hs : ∀ s ∈ List.replicate k r, ‖s‖ ≤ C * specNorm H := fun s hs => by
    rw [List.eq_of_mem_replicate hs]; exact hr
  have hdist' : ∀ s ∈ List.replicate k r, ∀ i, d ≤ ‖e i - s‖ := fun s hs i => by
    rw [List.eq_of_mem_replicate hs]; exact hdist i
  have hmono : (d / ((2 + 2 * C) * S)) ^ k ≤ (d / ((2 + 2 * C) * specNorm H)) ^ k := by
    gcongr
  obtain ⟨D, hD, hF⟩ := h.exists_frobNorm_conj_sub_le hx hC hd hH0 hH hV hHV hκ hs hdist'
    (by rw [List.length_replicate]; exact hxu.trans (by gcongr))
  rw [List.length_replicate] at hF
  have hF' : frobNorm ((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D - X) ≤ ω / 2 := by
    refine hF.trans (le_trans ?_ hbound)
    gcongr
  have he := (norm_apply_le_frobNorm _ i.succ i.castSucc).trans hF'
  have hconj : ((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D) i.succ i.castSucc =
      star (D i.succ) * H' i.succ i.castSucc * D i.castSucc := by
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  have hn : ‖((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D) i.succ i.castSucc‖ =
      ‖H' i.succ i.castSucc‖ := by
    rw [hconj, norm_mul, norm_mul, norm_star, hD, hD, one_mul, mul_one]
  rw [Matrix.sub_apply] at he
  have := norm_sub_norm_le (((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D) i.succ i.castSucc)
    (X i.succ i.castSucc)
  rw [hn] at this
  linarith

end NLAlib

namespace NLAlib.ShiftedQR

/-- **The bad draws of one random shift regularization** ([BanksGarzaVargasSrivastava2022,
Lemma 3.10], one sample, as `Regularize` uses it): for a centre $c$, complex numbers
$\lambda_1, \dots, \lambda_N$ whose distinct values are at distance at least $4R$, $R > 0$,
$k \ge 1$ and $0 \le \varphi \le 1$, the window $x \in \mathbb{R}^2$ of two uniform draws on
$[0, 1]$ lies off the unit square or makes the polar sample $w$ of radius $R$ bring $c + w$
within $\eta = R\sqrt{\varphi/(2k)}$ of some $\lambda_i$ with probability at most
$\varphi/(2k)$. Over the $k$ draws of `Regularize` this is the paper's $\varphi/2$. -/
theorem regularize_bad_window_le (c : ℂ) {N : ℕ} (e : Fin N → ℂ) {k : ℕ} {R φ : ℝ}
    (hk : 0 < k) (hR : 0 < R) (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hsep : ∀ i j, e i ≠ e j → 4 * R ≤ ‖e i - e j‖) :
    (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)).real
      {x | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1) ∨
        ∃ i, ‖c + polarDisk 0 R x - e i‖ < R * √(φ / (2 * k))} ≤ φ / (2 * k) := by
  classical
  set η := R * √(φ / (2 * k)) with hη_def
  set Λ : Finset ℂ := Finset.univ.image e
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq0 : 0 ≤ φ / (2 * k) := by positivity
  have hq1 : φ / (2 * k) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hη0 : 0 ≤ η := by positivity
  have hηR : η ≤ R := mul_le_of_le_one_right hR.le (Real.sqrt_le_one.mpr hq1)
  have hΛ : ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → 2 * (η + R) ≤ ‖a - b‖ := by
    intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    linarith [hsep i j hab]
  have hD3 := measureReal_exists_norm_add_sub_lt_le (fun _ : Fin 1 => c) Λ hR hη0 hΛ
  set U : Set ℂ := {w | ∃ a ∈ Λ, ‖c + w - a‖ < η}
  have hU : MeasurableSet U := by
    have : U = ⋃ a ∈ Λ, {w | ‖c + w - a‖ < η} := by ext; simp [U]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun a _ => measurableSet_lt (by fun_prop)
      measurable_const
  have h1 : (diskUniform 0 R).real U ≤ (η / R) ^ 2 := by
    have hmp := measurePreserving_funUnique (diskUniform 0 R) (Fin 1)
    rw [← hmp.measureReal_preimage hU.nullMeasurableSet]
    refine le_trans (le_of_eq ?_) (by simpa using hD3)
    congr 1
  set μ := Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)
  set A : Set (Fin 2 → ℝ) := ⋃ j, (fun x : Fin 2 → ℝ => x j) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ
  have hmeas : Measurable (polarDisk 0 R) := by unfold polarDisk; fun_prop
  have hset : {x : Fin 2 → ℝ | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ i, ‖c + polarDisk 0 R x - e i‖ < η} = A ∪ polarDisk 0 R ⁻¹' U := by
    ext x; simp [A, U, Λ]
  have hA0 : μ A = 0 := by
    refine measure_iUnion_null fun j => Measure.pi_eval_preimage_null _ ?_
    rw [Measure.restrict_apply' measurableSet_Icc, Set.compl_inter_self, measure_empty]
  rw [hset]
  calc μ.real (A ∪ polarDisk 0 R ⁻¹' U) ≤ μ.real A + μ.real (polarDisk 0 R ⁻¹' U) :=
        measureReal_union_le _ _
    _ = (diskUniform 0 R).real U := by
        rw [measureReal_def, hA0, ENNReal.toReal_zero, zero_add,
          ← map_measureReal_apply hmeas hU, map_polarDisk_eq_diskUniform 0 hR]
    _ ≤ (η / R) ^ 2 := h1
    _ = φ / (2 * k) := by rw [hη_def, mul_div_cancel_left₀ _ hR.ne', Real.sq_sqrt hq0]

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

/-- A list of complex numbers stored as interleaved pairs, read pair by pair. -/
theorem readBlock_flatMap_pair_of_forall {s : Store ℝ} {b o : ℕ} {zs : List ℂ}
    (h : ∀ j < zs.length,
      s.readBlock b (o + 2 * j) 2 = some [(zs.getD j 0).re, (zs.getD j 0).im]) :
    s.readBlock b o (2 * zs.length) = some (zs.flatMap fun z => [z.re, z.im]) := by
  induction zs generalizing o with
  | nil => simp
  | cons z zs ih =>
    have h0 := h 0 (by simp)
    have ht := ih (o := o + 2) fun j hj => by
      have := h (j + 1) (by simpa using hj)
      rwa [show o + 2 * (j + 1) = o + 2 + 2 * j by ring, List.getD_cons_succ] at this
    rw [List.length_cons, show 2 * (zs.length + 1) = 2 + 2 * zs.length by ring, List.flatMap_cons]
    exact Store.readBlock_add (by simpa using h0) ht

/-- A pair read from its two cells. -/
theorem readBlock_pair_of_get {s : Store ℝ} {b o : ℕ} {x y : ℝ} (hx : s.get b o = some x)
    (hy : s.get b (o + 1) = some y) : s.readBlock b o 2 = some [x, y] := by
  rw [Store.readBlock_eq_some_iff]
  refine ⟨rfl, fun j hj => ?_⟩
  have hj' : j < 2 := hj
  interval_cases j
  · simpa using hx
  · simpa using hy

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **One random perturbation of a shift**: a polar sample $w$ of the radius word `Rd` into the
pair `Z`, then the pair `S` becomes $\mathrm{fl}(S + w)$ componentwise. The interface is
`[] (Rd, S) → (Z, S)`. -/
def regularizeDraw : Impl O Q := opsImpl% [] (Rd, S) → (Z, S) {
  call (Has.inj DiskSampleOp.polar) [] (Rd) → (Z);
  call (Has.inj ScalarOp.add) [] (S, Z) → (S);
  call (Has.inj ScalarOp.add) [] (S[1], Z[1]) → (S[1])
}

/-- **The $k$ random perturbations**: `NLAlib.ShiftedQR.regularizeDraw` on each of the $k$ pairs
of `S`, with the radius word `Rd` and the scratch pair `Z`. The interface is
`[k] (Rd) → (Z, S)`. -/
def regularizeDraws : Impl O Q := opsImpl% [k] (Rd) → (Z, S) {
  for i < k {
    run regularizeDraw.body [] (Rd, S[2 * i], Z, S[2 * i])
  }
}

/-- The pair `S` copied $k$ times into `SR`: the shifts of a degree $k$ step with one repeated
shift. The interface is `[k] (S) → (SR)`. -/
def replicatePair : Impl O Q := opsImpl% [k] (S) → (SR) {
  for l < k {
    run (unaryMap (Has.inj ScalarOp.copy)).body [2] (S, SR[2 * l])
  }
}

/-- The computation of one trial of `Regularize`: the degree $k$ rounded step with the shift `S`
repeated $k$ times on a copy `T` of `A` (`SR` the repeated shifts, `Ds` the diagonal outputs),
and the scan of its bottom $k$ subdiagonal entries against the threshold word `Thr` into the
registers `Rg`. The interface is `[N, k] (A, S, Thr) → (T, SR, Ds, Rg)`. -/
def trialStep : Impl O Q := opsImpl% [N, k] (A, S, Thr) → (T, SR, Ds, Rg) {
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (N * N)] (A, T);
  run replicatePair.body [k] (S, SR);
  run multiStepStable.body [N, k] (T, SR, T, Ds);
  run bottomScan.body [N, k] (T, Thr, Rg)
}

/-- The acceptance of a trial: copy the step `T` back to `A`, set the search word `G` to $0$ and
the flag `Fl` to $1$. The interface is `[N] (T) → (A, G, Fl)`. -/
def trialAccept : Impl O Q := opsImpl% [N] (T) → (A, G, Fl) {
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (N * N)] (T, A);
  call (Has.inj (ScalarOp.lit 0)) [] () → (G);
  call (Has.inj (ScalarOp.lit 1)) [] () → (Fl)
}

/-- **One trial of `Regularize`**: if the search word `G` is positive, run
`NLAlib.ShiftedQR.trialStep`; if its scan found a small entry (`Rg[3]` positive), accept it
(`NLAlib.ShiftedQR.trialAccept`). The interface is
`[N, k] (A, S, Thr, T, SR, Ds, Rg) → (A, G, Fl)`. -/
def regularizeTrial : Impl O Q :=
  opsImpl% [N, k] (A, S, Thr, T, SR, Ds, Rg) → (A, G, Fl) {
    if (Has.inj CmpTst.isPos) [] (G) {
      run trialStep.body [N, k] (A, S, Thr, T, SR, Ds, Rg);
      if (Has.inj CmpTst.isPos) [] (Rg[3]) {
        run trialAccept.body [N] (T, A, G, Fl)
      } else {
        skip
      }
    } else {
      skip
    }
  }

/-- The $k$ trials of `Regularize`, with the shifts `S[2j]` in turn. The interface is
`[N, k] (A, S, Thr, T, SR, Ds, Rg) → (A, G, Fl)`. -/
def regularizeTrials : Impl O Q :=
  opsImpl% [N, k] (A, S, Thr, T, SR, Ds, Rg) → (A, G, Fl) {
    for j < k {
      run regularizeTrial.body [N, k] (A, S[2 * j], Thr, T, SR, Ds, Rg, A, G, Fl)
    }
  }

/-- The decision of `Regularize`: `Optimal` of the $k$ shifts `S` with the word `C` into `G`; if
optimal, the flag `Fl` is $0$; otherwise `Fl` is $2$, `G` is $1$, and the trials run. The
interface is `[N, k] (A, S, C, Thr, T, SR, Ds, Rg) → (A, G, Fl)`. -/
def regularizeDecide : Impl O Q :=
  opsImpl% [N, k] (A, S, C, Thr, T, SR, Ds, Rg) → (A, G, Fl) {
    run optimalTest.body [N, k] (A, S, C, G);
    if (Has.inj CmpTst.isPos) [] (G) {
      call (Has.inj (ScalarOp.lit 0)) [] () → (Fl)
    } else {
      call (Has.inj (ScalarOp.lit 2)) [] () → (Fl);
      call (Has.inj (ScalarOp.lit 1)) [] () → (G);
      run regularizeTrials.body [N, k] (A, S, Thr, T, SR, Ds, Rg, A, G, Fl)
    }
  }

/-- `Regularize` with caller-owned scratch: the trailing $k \times k$ block of the order-$N$
matrix `A` into `B`, `SmallEig` of it into the $k$ pairs `S`, one random perturbation of each
pair (radius word `Rd`), `Optimal` with the word `C` into `G`; if optimal, the flag `Fl` is $0$;
otherwise `Fl` is $2$ and the $k$ trials run until one decouples (then `Fl` is $1$). The
interface is `[N, k] (A, Rd, C, Thr, B, Z, G, T, SR, Ds, Rg) → (A, S, Fl)`. -/
def regularizeWithScratch : Impl O Q :=
  opsImpl% [N, k] (A, Rd, C, Thr, B, Z, G, T, SR, Ds, Rg) → (A, S, Fl) {
    run copyToWork.body [N, N - k, k] (A, B);
    run smallEigLeaf.body [k] (B, S);
    run regularizeDraws.body [k] (Rd, Z, S);
    run regularizeDecide.body [N, k] (A, S, C, Thr, T, SR, Ds, Rg, A, G, Fl)
  }

/-- **`Regularize`** ([BanksGarzaVargasSrivastava2022, §4.2], $\mathsf{RitzOrDecouple}$): from
the order-$N$ matrix `A`, the radius word `Rd` of the perturbations, the word `C` of `Optimal`
($0.999\theta^k$) and the threshold word `Thr` of the decoupling scan, store $k$ perturbed
approximate Ritz values at `S` and set the flag `Fl` to $0$ (they are optimal, `A` unchanged) or
$1$ (`A` holds a decoupled degree $k$ step); `Fl` is $2$ only if no trial decoupled. All scratch is
scoped. The interface is `[N, k] (A, Rd, C, Thr) → (A, S, Fl)`. -/
def regularize : Impl O Q := opsImpl% [N, k] (A, Rd, C, Thr) → (A, S, Fl) {
  let B ← alloc (2 * (k * k));
  let Z ← alloc 2;
  let G ← alloc 1;
  let T ← alloc (2 * (N * N));
  let SR ← alloc (2 * k);
  let Ds ← alloc (2 * k);
  let Rg ← alloc 5;
  run regularizeWithScratch.body [N, k] (A, Rd, C, Thr, B, Z, G, T, SR, Ds, Rg, A, S, Fl)
}

end Program

section Proofs

variable {O Q : Type} [Has ScalarOp O] [Has DiskSampleOp O]

/-- **One random perturbation on any scalar machine** with an exact polar sampler on the stream
`s`: from the radius word $R$ at `Rd` and the pair $r$ at `S`, `NLAlib.ShiftedQR.regularizeDraw`
stores at `S` the rounded $\mathrm{fl}(r + w)$ (`NLAlib.ShiftedQR.excCentreWord`) of the polar
sample $w$ of radius $R$ read at the start position, writes only `S` and the scratch pair `Z`,
and advances the position by two. -/
theorem regularizeDraw_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) {s : ℕ}
    (hD : IsPolarDiskSampler s I) {τ : Tape ℝ} {m : Mem ℝ} {rd sp z : ℕ × ℕ} {r : ℂ} {R : ℝ}
    (hrd : m.store.get rd.1 rd.2 = some R)
    (hs : m.store.readBlock sp.1 sp.2 2 = some [r.re, r.im])
    (hz : z.2 + 2 ≤ m.store.len z.1)
    (hzs : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock sp.1 sp.2 2)) :
    Writes .total I τ (regularizeDraw (O := O) (Q := Q)).body (Env.frame [] [rd, sp, z, sp])
      (Store.inBlock sp.1 sp.2 2 ⊔ Store.inBlock z.1 z.2 2)
      (fun m' => m'.pos = m.pos + 2 ∧ m'.store.readBlock sp.1 sp.2 2 =
        some [(excCentreWord M r (excSample τ s m.pos R)).1,
          (excCentreWord M r (excSample τ s m.pos R)).2]) m := by
  have hrl := Store.lt_length_of_get hrd
  have hre := Store.get_of_readBlock hs (j := 0) (by norm_num) 0
  have him := Store.get_of_readBlock hs (j := 1) (by norm_num) 0
  simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at hre him
  have hsl := Store.lt_length_of_get hre
  have hzl := Store.lt_length_of_lt_len (show z.2 < m.store.len z.1 by omega)
  set W := excSample τ s m.pos R with hW_def
  unfold regularizeDraw
  have hread : m.readBlocks [rd] [1] = some [[R]] := by
    simp [Mem.readBlocks, Store.readBlock, hrd]
  refine (writes_call (R := polarDiskRel s) hD (d := []) (a := [rd]) (b := [z])
    (k := 2) (ls := [2]) rfl rfl rfl rfl rfl rfl trivial (by simp [Fp.Apart])
    (fun _ => ⟨by simp [Mem.Live]; omega, ⟨_, hread, trivial⟩, by
      simp [Mem.Room]; omega⟩)).seq_le (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨hp₁, xs, ys, hr, hys, hrel⟩
  have hxs : xs = [[R]] := Option.some.inj (hr.symm.trans hread)
  have hwin : (fun j : Fin 2 => (τ.window s m.pos 2).getD j 0) = Tape.windowFn τ s m.pos 2 := by
    funext j
    fin_cases j <;> simp [Tape.window, Tape.windowFn, List.getD_eq_getElem?_getD]
  have hys' := hrel R hxs
  simp only [polarDiskRel] at hys'
  rw [hwin] at hys'
  have hWb : m₁.store.readBlock z.1 z.2 2 = some [W.re, W.im] := by
    subst hys'
    obtain ⟨y, hy, hyy⟩ := Option.bind_eq_some_iff.mp (by simpa [Mem.readBlocks] using hys)
    simp only [Option.some.injEq, List.cons.injEq, and_true] at hyy
    rw [hy, hyy]; rfl
  have hW1 := Store.get_of_readBlock hWb (j := 0) (by norm_num) 0
  have hW2 := Store.get_of_readBlock hWb (j := 1) (by norm_num) 0
  simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at hW1 hW2
  have hz2 : Fp.Disj (Fp.blocks [z] [2]) (Store.inBlock sp.1 sp.2 2) := by
    simpa [Fp.blocks] using hzs
  have hre₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hz2.mono le_rfl (by fp_sub)) hre
  have him₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hz2.mono le_rfl (by fp_sub)) him
  refine (writes_call_bin (hS .add) rfl rfl trivial hre₁ hW1 rfl
    (fun _ => ⟨by simp [Mem.Live, hfr₁.length_eq]; omega, by
      rw [hfr₁.len_eq]; exact Store.lt_len_of_get hre⟩)).seq_le (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hX₂⟩
  have him₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) him₁
  have hW2₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hzs.symm.mono (by fp_sub) (by fp_sub)) hW2
  refine (writes_call_bin (hS .add) rfl rfl trivial him₂ hW2₂ rfl
    (fun _ => ⟨by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq]; omega, by
      rw [hfr₂.len_eq, hfr₁.len_eq]; exact Store.lt_len_of_get him⟩)).mono (by fp_sub) ?_
  intro m₃ hfr₃ ⟨hp₃, hY₃⟩
  have hX₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (by disjoint) hX₂
  exact ⟨by rw [hp₃, hp₂, hp₁], readBlock_pair_of_get hX₃ hY₃⟩

/-- **The rounding of a perturbed shift**: under the standard model,
$\lvert\mathrm{fl}(r + w) - (r + w)\rvert \le 2\boldsymbol{u}\lvert r + w\rvert$ for the
componentwise rounded sum `NLAlib.ShiftedQR.excCentreWord`. -/
theorem norm_excCentreWord_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (r w : ℂ) :
    ‖(⟨(excCentreWord M r w).1, (excCentreWord M r w).2⟩ : ℂ) - (r + w)‖ ≤
      2 * u * ‖r + w‖ := by
  have hu0 := hM.roundoff_nonneg
  have h1 := hM.add r.re w.re
  have h2 := hM.add r.im w.im
  simp only [id] at h1 h2
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e : ((⟨(excCentreWord M r w).1, (excCentreWord M r w).2⟩ : ℂ) - (r + w)).re =
      M.add r.re w.re - (r.re + w.re) := by simp [excCentreWord]
  have e' : ((⟨(excCentreWord M r w).1, (excCentreWord M r w).2⟩ : ℂ) - (r + w)).im =
      M.add r.im w.im - (r.im + w.im) := by simp [excCentreWord]
  rw [e, e']
  have h3 : |r.re + w.re| ≤ ‖r + w‖ := by simpa using Complex.abs_re_le_norm (r + w)
  have h4 : |r.im + w.im| ≤ ‖r + w‖ := by simpa using Complex.abs_im_le_norm (r + w)
  nlinarith

end Proofs

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops MeasureTheory

section Draws

variable {O Q : Type} [Has ScalarOp O] [Has DiskSampleOp O]

/-- The pair at `b` read as a complex number, an uninitialised word read as $0$. -/
def storedPair (b : ℕ × ℕ) (m : Mem ℝ) : ℂ := storedMatrix b 1 1 m.store 0 0

/-- A stored pair is the pair read from its block. -/
theorem storedPair_eq {b : ℕ × ℕ} {m : Mem ℝ} {z : ℂ}
    (h : m.store.readBlock b.1 b.2 2 = some [z.re, z.im]) : storedPair b m = z := by
  have hre := Store.get_of_readBlock h (j := 0) (by norm_num) 0
  have him := Store.get_of_readBlock h (j := 1) (by norm_num) 0
  simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at hre him
  apply Complex.ext <;> simp [storedPair, storedMatrix, hre, him]

/-- The bad windows of the perturbation of the pair at `b`: off the unit square, or bringing the
stored centre within $\eta$ of some $\lambda_l$. Jointly measurable in the memory and the
window. -/
theorem measurableSet_drawBad (b : ℕ × ℕ) {N : ℕ} (e : Fin N → ℂ) (R η : ℝ) :
    MeasurableSet {x : Mem ℝ × (Fin 2 → ℝ) | (∃ j, x.2 j ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ l, ‖storedPair b x.1 + polarDisk 0 R x.2 - e l‖ < η} := by
  have hc : Measurable fun m : Mem ℝ => storedPair b m :=
    (measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp (measurable_storedMatrix b 1 1))
  have hp : Measurable (polarDisk 0 R) := by unfold polarDisk; fun_prop
  have e1 : {x : Mem ℝ × (Fin 2 → ℝ) | (∃ j, x.2 j ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ l, ‖storedPair b x.1 + polarDisk 0 R x.2 - e l‖ < η} =
      (⋃ j, (fun x : Mem ℝ × (Fin 2 → ℝ) => x.2 j) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ) ∪
        ⋃ l, {x | ‖storedPair b x.1 + polarDisk 0 R x.2 - e l‖ < η} := by
    ext x; simp
  rw [e1]
  refine (MeasurableSet.iUnion fun j => measurableSet_Icc.compl.preimage
    ((measurable_pi_apply j).comp measurable_snd)).union (MeasurableSet.iUnion fun l => ?_)
  exact measurableSet_lt (((hc.comp measurable_fst).add (hp.comp measurable_snd)).sub_const _
    |>.norm) measurable_const

/-- The state after `i` of the `k` perturbations of `NLAlib.ShiftedQR.regularizeDraws`: the
radius word $R$ at `rd`, room for the scratch pair `z`, targets $\lambda$ with the property
`Lam`, and $k$ pairs $c_j$ at `s` with
$\lvert c_j - \lambda_j\rvert \le \beta$ for $j \ge i$ (not yet perturbed) and, for
$j < i$, $\lvert c_j - \lambda_j\rvert \le \beta + R + \delta_j$ and every
$\lvert c_j - e_l\rvert + \delta_j \ge \eta$, where
$\delta_j = 2\boldsymbol{u}(\lvert\lambda_j\rvert + \beta + R)$. -/
def DrawsInv (u β R η : ℝ) {k N : ℕ} (Lam : (Fin k → ℂ) → Prop) (e : Fin N → ℂ)
    (rd z s : ℕ × ℕ) (i : ℕ) (m : Mem ℝ) : Prop :=
  m.store.get rd.1 rd.2 = some R ∧ z.2 + 2 ≤ m.store.len z.1 ∧ ∃ lam, Lam lam ∧ ∃ c : Fin k → ℂ,
    (∀ j : Fin k, m.store.readBlock s.1 (s.2 + 2 * j) 2 = some [(c j).re, (c j).im]) ∧
    ∀ j : Fin k, ((i ≤ j → ‖c j - lam j‖ ≤ β) ∧ ((j : ℕ) < i →
      ‖c j - lam j‖ ≤ β + R + 2 * u * (‖lam j‖ + β + R) ∧
        ∀ l, η ≤ ‖c j - e l‖ + 2 * u * (‖lam j‖ + β + R)))

/-- **One perturbation as a probabilistic block**: under an exact polar sampler on a stream `s₀`
uniform on $[0, 1]$, the perturbation of pair $i$ keeps `NLAlib.ShiftedQR.DrawsInv` from $i$ to
$i + 1$, except with probability at most $\varphi/(2k)$ (`regularize_bad_window_le`), for
$\eta = R\sqrt{\varphi/(2k)}$ and $\lambda$'s whose distinct values are $4R$ apart. -/
theorem regularizeDraw_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) {law : ℕ → Measure ℝ} {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k N : ℕ} (hk : 0 < k)
    (Lam : (Fin k → ℂ) → Prop) (e : Fin N → ℂ) {β R φ : ℝ} (hR : 0 < R) (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hsep : ∀ i j, e i ≠ e j → 4 * R ≤ ‖e i - e j‖) {rd z s : ℕ × ℕ}
    (hzs : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock s.1 s.2 (2 * k)))
    (hzr : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock rd.1 rd.2 1))
    (hsr : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock rd.1 rd.2 1)) (i : Fin k) :
    PWrites law I (regularizeDraw (O := O) (Q := Q)).body
      (Env.frame [] [rd, (s.1, s.2 + 2 * i), z, (s.1, s.2 + 2 * i)])
      (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock z.1 z.2 2)
      (DrawsInv u β R (R * √(φ / (2 * k))) Lam e rd z s i)
      (DrawsInv u β R (R * √(φ / (2 * k))) Lam e rd z s (i + 1)) (φ / (2 * k)) := by
  set η := R * √(φ / (2 * k))
  have hu0 := hM.roundoff_nonneg
  have hpair : ∀ j : Fin k, Store.inBlock s.1 (s.2 + 2 * j) 2 ≤ Store.inBlock s.1 s.2 (2 * k) :=
    fun j => Fp.inBlock_le_inBlock (by omega) (by omega)
  refine PWrites.of_window (s := s₀) (W := 2) (Bad := fun m => {x | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1)
    ∨ ∃ l, ‖storedPair (s.1, s.2 + 2 * i) m + polarDisk 0 R x - e l‖ < η})
    (measurableSet_drawBad _ e R η) ?_ ?_
  · rintro m ⟨-, -, -, -, c, hc, -⟩
    rw [storedPair_eq (b := (s.1, s.2 + 2 * i)) (hc i), hU]
    exact regularize_bad_window_le (c i) e hk hR hφ hφ1 hsep
  rintro m τ ⟨hrd, hz, lam, hlam, c, hc, hgood⟩ hwin
  simp only [Set.mem_ofPred_eq, not_or, not_exists, not_lt, storedPair_eq (b := (s.1, s.2 + 2 * i)) (hc i)] at hwin
  obtain ⟨hsq, hfar⟩ := hwin
  have hw := regularizeDraw_writes (τ := τ) (sp := (s.1, s.2 + 2 * i)) hS hD hrd (hc i) hz (hzs.mono le_rfl (hpair i))
  refine hw.mono (sup_le ((hpair i).trans le_sup_left) le_sup_right) ?_
  rintro m' hfr ⟨-, hnew⟩
  set W := excSample τ s₀ m.pos R
  have hW : ‖W‖ ≤ R := norm_polarDisk_le hR.le fun j => not_not.mp (hsq j)
  have hfar' : ∀ l, η ≤ ‖c i + W - e l‖ := hfar
  set c' := Function.update c i ⟨(excCentreWord M (c i) W).1, (excCentreWord M (c i) W).2⟩
  have hround := norm_excCentreWord_sub_le hM (c i) W
  have hci := (hgood i).1 le_rfl
  have hcw : ‖c i + W‖ ≤ ‖lam i‖ + β + R := by
    have := norm_add_le (c i - lam i + lam i) W
    have := norm_add_le (c i - lam i) (lam i)
    simp only [sub_add_cancel] at *
    linarith
  have hδ : 2 * u * ‖c i + W‖ ≤ 2 * u * (‖lam i‖ + β + R) := by gcongr
  refine ⟨hfr.keep (Store.readsOnly_get _ _ _) (Fp.disj_sup_left.mpr ⟨hsr.mono (hpair i) le_rfl, hzr⟩) hrd,
    by rw [hfr.len_eq]; exact hz, lam, hlam, c', fun j => ?_, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
  · by_cases hji : j = i
    · subst hji; simpa [c'] using hnew
    · have hne : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
      have hd : Fp.Disj (Store.inBlock s.1 (s.2 + 2 * i) 2 ⊔ Store.inBlock z.1 z.2 2)
          (Store.inBlock s.1 (s.2 + 2 * j) 2) := by
        refine Fp.disj_sup_left.mpr ⟨?_, hzs.mono le_rfl (hpair j)⟩
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · exact (Fp.disj_inBlock_of_le (by omega)).symm
        · exact Fp.disj_inBlock_of_le (by omega)
      simpa [c', Function.update_of_ne hji] using
        hfr.keep (Store.readsOnly_readBlock _ _ _ _) hd (hc j)
  · have hji : j ≠ i := fun h => by subst h; simp at hj
    simpa [c', Function.update_of_ne hji] using (hgood j).1 (by simp at hj ⊢; omega)
  · by_cases hji : j = i
    · subst hji
      simp only [c', Function.update_self]
      refine ⟨?_, fun l => ?_⟩
      · have := norm_sub_le_norm_sub_add_norm_sub (⟨(excCentreWord M (c j) W).1,
          (excCentreWord M (c j) W).2⟩ : ℂ) (c j + W) (lam j)
        have h2 : ‖c j + W - lam j‖ ≤ ‖c j - lam j‖ + ‖W‖ := by
          rw [show c j + W - lam j = (c j - lam j) + W by ring]; exact norm_add_le _ _
        linarith
      · have := norm_sub_le_norm_sub_add_norm_sub (c j + W) (⟨(excCentreWord M (c j) W).1,
          (excCentreWord M (c j) W).2⟩ : ℂ) (e l)
        rw [norm_sub_rev (c j + W) (⟨(excCentreWord M (c j) W).1,
          (excCentreWord M (c j) W).2⟩ : ℂ)] at this
        linarith [hfar' l]
    · have hj' : (j : ℕ) < i := by
        have : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
        simp at hj; omega
      simpa [c', Function.update_of_ne hji] using (hgood j).2 hj'

/-- **The $k$ perturbations as a probabilistic block**: under a measurable, tape-local
interpretation with an exact polar sampler on a stream `s₀` uniform on $[0, 1]$, from $k \ge 1$
pairs $c_j$ at `s` within $\beta$ of targets $\lambda_j$ and the radius word $R > 0$ at `rd`,
`NLAlib.ShiftedQR.regularizeDraws` writes only the pairs and the scratch pair `z` and, except
with probability at most $\varphi/2$, $0 \le \varphi \le 1$, stores pairs within
$\beta + R + \delta_j$ of the $\lambda_j$ and at distance at least
$R\sqrt{\varphi/(2k)} - \delta_j$ from every $e_l$, $\delta_j =
2\boldsymbol{u}(\lvert\lambda_j\rvert + \beta + R)$, provided the distinct $e_l$ are $4R$
apart ([BanksGarzaVargasSrivastava2022, Lemma 3.10], one draw at a time). -/
theorem regularizeDraws_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) {law : ℕ → Measure ℝ} {s₀ : ℕ}
    (hD : IsPolarDiskSampler s₀ I) (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k N : ℕ}
    (hk : 0 < k) (Lam : (Fin k → ℂ) → Prop) (e : Fin N → ℂ) {β R φ : ℝ} (hR : 0 < R) (hφ : 0 ≤ φ)
    (hφ1 : φ ≤ 1) (hsep : ∀ i j, e i ≠ e j → 4 * R ≤ ‖e i - e j‖) {rd z s : ℕ × ℕ}
    (hzs : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock s.1 s.2 (2 * k)))
    (hzr : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock rd.1 rd.2 1))
    (hsr : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock rd.1 rd.2 1)) :
    PWrites law I (regularizeDraws (O := O) (Q := Q)).body (Env.frame [k] [rd, z, s])
      (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock z.1 z.2 2)
      (DrawsInv u β R (R * √(φ / (2 * k))) Lam e rd z s 0)
      (DrawsInv u β R (R * √(φ / (2 * k))) Lam e rd z s k) (φ / 2) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold regularizeDraws
  refine (PWrites.loop hI hloc (N := k) rfl _ (fun _ => φ / (2 * k))
    (fun _ _ => by positivity) (fun _ h => h) (fun i hi => ?_) (fun _ h => h)).mono
    (fun _ h => h) le_rfl (fun _ h => h) (by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      rfl)
  refine (regularizeDraw_pwrites hS hM hD hU hk Lam e hR hφ hφ1 hsep hzs hzr hsr ⟨i, hi⟩).in_frame
    rfl rfl ?_
  rintro m ⟨hrd, hz, -, -, c, hc, -⟩
  have h0 := Store.get_of_readBlock (hc ⟨i, hi⟩) (j := 0) (by norm_num) 0
  simp [Mem.Live, Store.lt_length_of_get hrd, Store.lt_length_of_get h0,
    Store.lt_length_of_lt_len (show z.2 < m.store.len z.1 by omega)]

end Draws

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

section Trials

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- `NLAlib.ShiftedQR.replicatePair` on any scalar machine stores the pair $r$ of `S` $k$ times
at `SR`, writing only `SR`. -/
theorem replicatePair_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ} {sp sr : ℕ × ℕ} {r : ℂ}
    (hs : m.store.readBlock sp.1 sp.2 2 = some [r.re, r.im])
    (hsr : sr.2 + 2 * k ≤ m.store.len sr.1)
    (hd : Fp.Disj (Store.inBlock sp.1 sp.2 2) (Store.inBlock sr.1 sr.2 (2 * k))) :
    Writes .total I τ (replicatePair (O := O) (Q := Q)).body (Env.frame [k] [sp, sr])
      (Store.inBlock sr.1 sr.2 (2 * k))
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock sr.1 sr.2 (2 * (List.replicate k r).length) =
          some ((List.replicate k r).flatMap fun z => [z.re, z.im])) m := by
  have hsl := Store.lt_length_of_get (Store.get_of_readBlock hs (j := 0) (by norm_num) 0)
  unfold replicatePair
  refine (writes_loop (N := k) rfl (fun _ => Store.inBlock sr.1 sr.2 (2 * k))
    (fun _ _ => le_rfl) (fun l μ => μ.pos = m.pos ∧ μ.store.readBlock sr.1 sr.2 (2 * l) =
      some ((List.replicate l r).flatMap fun z => [z.re, z.im])) ⟨rfl, by simp⟩ ?_).mono
    le_rfl ?_
  · intro l hl μ hfr ⟨hp, hpre⟩
    have hsμ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) hd.symm hs
    have hsub : Store.inBlock sr.1 (sr.2 + 2 * l) 2 ≤ Store.inBlock sr.1 sr.2 (2 * k) :=
      Fp.inBlock_le_inBlock (by omega) (by omega)
    have hc := writes_unaryMap_of_disj_or_eq (md := .total) (τ := τ) (f := id) (x := sp)
      (y := (sr.1, sr.2 + 2 * l)) (hS .copy) (Or.inl (hd.mono le_rfl hsub)) hsμ
      (by rw [hfr.len_eq]; dsimp only; omega)
    refine (hc.in_frame rfl rfl ?_).mono hsub ?_
    · have h0 : sr.2 < m.store.len sr.1 := by omega
      simp [Mem.Live, hfr.length_eq, hsl, Store.lt_length_of_lt_len h0]
    rintro μ' hfr' ⟨hp', hnew⟩
    refine ⟨hp'.trans hp, ?_⟩
    have hold := hfr'.keep (Store.readsOnly_readBlock _ _ _ _)
      (Fp.disj_inBlock_of_le le_rfl).symm hpre
    rw [show 2 * (l + 1) = 2 * l + 2 by ring, List.replicate_succ', List.flatMap_append]
    exact Store.readBlock_add hold (by simpa using hnew)
  · rintro μ - ⟨hp, h⟩
    exact ⟨hp, by simpa using h⟩

omit [Has IdxTst Q] in
/-- **The computation of one trial** on a scalar machine with the standard model at
$(n + 1)\boldsymbol{u} \le 1/2500$, exact comparisons, index literals and exact natural literals
up to $n + 1$: from an upper Hessenberg $\mathbf{H}$ of order $n + 1$ at `A`, the shift $r$ at `S`
and the threshold word $t$ at `Thr`, `NLAlib.ShiftedQR.trialStep` writes only its four outputs
and stores at `T` a backward-stable degree $k$ step $\widehat{\mathbf{H}}$ with the shift $r$
repeated (relative error $300(n+1)^2\boldsymbol{u}$), upper Hessenberg, and in `Rg` the scan
of its bottom $k$ subdiagonal entries (`NLAlib.ShiftedQR.bottomScan_writes`). -/
theorem trialStep_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a sp thr t sr ds rg : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {r : ℂ} {tv : ℝ} (hH : IsUpperHessenberg H) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hA : HoldsMatrix a H m.store) (hs : m.store.readBlock sp.1 sp.2 2 = some [r.re, r.im])
    (hthr : m.store.get thr.1 thr.2 = some tv)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock sp.1 sp.2 2 ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I τ (trialStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, sp, thr, t, sr, ds, rg])
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5)
      (fun m' => ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
        IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k r) H' Rs ∧
          IsUpperHessenberg H' ∧ HoldsMatrix t H' m'.store ∧
          ((m'.store.get rg.1 (rg.2 + 3) = some 1 ∧ ∃ i : Fin n, n ≤ (i : ℕ) + k ∧
              (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
            (m'.store.get rg.1 (rg.2 + 3) = some 0 ∧ ∀ i : Fin n, n ≤ (i : ℕ) + k →
              tv < (1 + u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2))) m := by
  have hu0 := hM.roundoff_nonneg
  have hal := Store.lt_length_of_get (Store.get_of_readBlock hA (j := 0) (by positivity) 0)
  have hsl := Store.lt_length_of_get (Store.get_of_readBlock hs (j := 0) (by norm_num) 0)
  have htl := Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by nlinarith)
  have hsrl := Store.lt_length_of_lt_len (show sr.2 < m.store.len sr.1 by omega)
  have hdsl := Store.lt_length_of_lt_len (show ds.2 < m.store.len ds.1 by omega)
  have hrgl := Store.lt_length_of_lt_len (show rg.2 < m.store.len rg.1 by omega)
  have hthl := Store.lt_length_of_get hthr
  unfold trialStep
  refine (copyMatrix_writes (τ := τ) hS hA hrt (hW.symm.mono (by fp_sub) (by fp_sub))).frame_seq_le
    rfl rfl (by simp [Mem.Live, hal, htl]) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, hT₁⟩
  have hs₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hW.mono (by fp_sub) (by fp_sub)) hs
  have hthr₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hW.mono (by fp_sub) (by fp_sub)) hthr
  have hrep := replicatePair_writes (τ := τ) (sr := sr) hS hs₁ (by rw [hfr₁.len_eq]; exact hrsr)
    (hW.symm.mono (by fp_sub) (by fp_sub))
  refine hrep.frame_seq_le rfl rfl (by simp [Mem.Live, hfr₁.length_eq, hsl, hsrl]) (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨-, hSR₂⟩
  have hT₂ := hT₁.of_eqOff hfr₂ hts.symm
  have hthr₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hW.mono (by fp_sub) (by fp_sub)) hthr₁
  have hl₂ : ∀ b, m₂.store.len b = m.store.len b := fun b => by rw [hfr₂.len_eq, hfr₁.len_eq]
  have hL₂ : m₂.store.length = m.store.length := by rw [hfr₂.length_eq, hfr₁.length_eq]
  have hms := multiStepStable_isStableQRChain (τ := τ) (m := m₂) (a := t) (s := sr) (ds := ds)
    (ss := List.replicate k r) hS hM hu0 hC hH hnu (by simp [Mem.Live, hL₂, htl, hsrl, hdsl])
    hT₂ hSR₂ (by rw [hl₂, List.length_replicate]; exact hrds)
    (by simpa using hts) (by simpa using htd) (by simpa using hsd)
  rw [List.length_replicate] at hms
  refine hms.frame_seq_le rfl rfl (by simp [Mem.Live, hL₂, htl, hsrl, hdsl]) (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨-, H', Rs, hch, hH', hT₃, -⟩
  have hthr₃ := hfr₃.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_sup_left.mpr ⟨hW.mono (by fp_sub) (by fp_sub), hW.mono (by fp_sub) (by fp_sub)⟩)
    hthr₂
  have hL₃ : m₃.store.length = m.store.length := by rw [hfr₃.length_eq, hL₂]
  have hb := bottomScan_writes (τ := τ) (m := m₃) (a := t) (t := thr) (r := rg) hS hM hu0 hu1
    hL hNat hC hk hT₃ hthr₃ (by simp [Mem.Live, hL₃, htl, hthl, hrgl])
    (by rw [hfr₃.len_eq, hl₂]; exact hrrg) hrg (hW.mono (by fp_sub) (by fp_sub))
  refine (hb.in_frame rfl rfl (by simp [Mem.Live, hL₃, htl, hthl, hrgl])).mono (by fp_sub) ?_
  rintro m₄ hfr₄ ⟨-, hscan⟩
  refine ⟨H', Rs, hch, hH', hT₃.of_eqOff hfr₄ hrg, ?_⟩
  rcases hscan with ⟨h1, i, hi, -, hle⟩ | h0
  · exact Or.inl ⟨h1, i, hi, hle⟩
  · exact Or.inr h0

omit [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The acceptance of a trial on a scalar machine with the standard model and exact natural
literals up to $1$: `NLAlib.ShiftedQR.trialAccept` copies the matrix at `T` to `A`, stores $0$
in `G` and $1$ in `Fl`, and writes only these. -/
theorem trialAccept_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hNat : IsExactNatLit id M 1) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ}
    {t a g f : ℕ × ℕ} {H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hT : HoldsMatrix t H' m.store) (hra : a.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len a.1)
    (hrg : g.2 < m.store.len g.1) (hrf : f.2 < m.store.len f.1)
    (hta : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hga : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1)) :
    Writes .total I τ (trialAccept (O := O) (Q := Q)).body (Env.frame [n + 1] [t, a, g, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1)
      (fun m' => HoldsMatrix a H' m'.store ∧ m'.store.get g.1 g.2 = some 0 ∧
        m'.store.get f.1 f.2 = some 1) m := by
  have h0 : M.lit 0 = 0 := by simpa using hM.lit 0
  have h1 : M.lit 1 = 1 := by simpa using hNat 1 le_rfl
  have htl := Store.lt_length_of_get (Store.get_of_readBlock hT (j := 0) (by positivity) 0)
  have hal := Store.lt_length_of_lt_len (show a.2 < m.store.len a.1 by nlinarith)
  unfold trialAccept
  refine (copyMatrix_writes (τ := τ) hS hT hra hta).frame_seq_le rfl rfl
    (by simp [Mem.Live, htl, hal]) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, hA₁⟩
  refine (writes_call_const (hS (.lit 0)) (z := g) rfl trivial
    (by rw [hfr₁.len_eq]; exact hrg)).seq_le (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨-, hG₂⟩
  refine (writes_call_const (hS (.lit 1)) (z := f) rfl trivial
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hrf)).mono (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨-, hF₃⟩
  refine ⟨(hA₁.of_eqOff hfr₂ (hga.mono (by fp_sub) le_rfl)).of_eqOff hfr₃
    (hga.mono (by fp_sub) le_rfl), ?_, by rw [hF₃, h1]⟩
  rw [hfr₃.keep (Store.readsOnly_get _ _ _) hgf.symm hG₂, h0]

/-- The outcome of one trial of `Regularize` from the search word $g$, the flag word $f$ and
the matrix $\mathbf{H}$ at `a`, with the shift $r$ and the threshold $t$: either nothing visible
changed (and, if $g > 0$, the computed step had no small bottom entry), or $g > 0$ and a
decoupled step was accepted: `G` is $0$, `Fl` is $1$ and `a` holds a backward-stable degree $k$
step with a bottom entry passing the scan. -/
def TrialPost (u : ℝ) {n : ℕ} (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r : ℂ)
    (tv gv fv : ℝ) (a g f : ℕ × ℕ) (m' : Mem ℝ) : Prop :=
  (m'.store.get g.1 g.2 = some gv ∧ m'.store.get f.1 f.2 = some fv ∧ HoldsMatrix a H m'.store ∧
    (0 < gv → ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
      IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k r) H' Rs ∧
        ∀ i : Fin n, n ≤ (i : ℕ) + k → tv < (1 + u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2)) ∨
  (0 < gv ∧ m'.store.get g.1 g.2 = some 0 ∧ m'.store.get f.1 f.2 = some 1 ∧
    ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
      IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k r) H' Rs ∧
        IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
        ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv)

omit [Has IdxTst Q] in
/-- **One trial of `Regularize`** on a scalar machine with the standard model at
$(n + 1)\boldsymbol{u} \le 1/2500$, exact comparisons, index literals and exact natural literals
up to $n + 1$: `NLAlib.ShiftedQR.regularizeTrial` writes only the matrix `A`, the words `G`,
`Fl` and its scratch, and ends in `NLAlib.ShiftedQR.TrialPost`. -/
theorem regularizeTrial_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a sp thr t sr ds rg g f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {r : ℂ} {tv gv fv : ℝ}
    (hH : IsUpperHessenberg H) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hA : HoldsMatrix a H m.store) (hs : m.store.readBlock sp.1 sp.2 2 = some [r.re, r.im])
    (hthr : m.store.get thr.1 thr.2 = some tv) (hg : m.store.get g.1 g.2 = some gv)
    (hf : m.store.get f.1 f.2 = some fv)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock sp.1 sp.2 2 ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hGF : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1)) :
    Writes .total I τ (regularizeTrial (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, sp, thr, t, sr, ds, rg, a, g, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
          Store.inBlock rg.1 rg.2 5))
      (TrialPost u k H r tv gv fv a g f) m := by
  have h1 : M.lit 1 = 1 := by simpa using hNat 1 (by omega)
  unfold regularizeTrial
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := g) hg) ?_
  by_cases hgp : 0 < gv
  · rw [show decide (0 < id gv) = true by simpa using hgp, if_pos rfl]
    have hstep := trialStep_writes (τ := τ) hS hM hu1 hL hNat hC hk0 hk hH hnu hA hs hthr hrt hrsr
      hrds hrrg hW hts htd hsd hrg
    have hal := Store.lt_length_of_get (Store.get_of_readBlock hA (j := 0) (by positivity) 0)
    refine hstep.frame_seq_le rfl rfl (by
        simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq]
        refine ⟨hal, Store.lt_length_of_get (Store.get_of_readBlock hs (j := 0) (by norm_num) 0),
          Store.lt_length_of_get hthr,
          Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by nlinarith),
          Store.lt_length_of_lt_len (show sr.2 < m.store.len sr.1 by omega),
          Store.lt_length_of_lt_len (show ds.2 < m.store.len ds.1 by omega),
          Store.lt_length_of_lt_len (show rg.2 < m.store.len rg.1 by omega)⟩) (le_sup_right) ?_
    rintro m₁ hfr₁ ⟨H', Rs, hch, hH', hT₁, hscan⟩
    have hA₁ := hA.of_eqOff hfr₁ (hW.mono le_rfl (by fp_sub))
    have hg₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hGF.symm.mono (by fp_sub) (by fp_sub)) hg
    have hf₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hGF.symm.mono (by fp_sub) (by fp_sub)) hf
    rcases hscan with ⟨hR1, hdec⟩ | ⟨hR0, hall⟩
    · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (rg.1, rg.2 + 3)) hR1) ?_
      rw [show decide (0 < id (1 : ℝ)) = true by simp, if_pos rfl]
      have hacc := trialAccept_writes (τ := τ) (a := a) (g := g) (f := f) hS hM
        (hNat.mono (by omega)) hT₁
        (by rw [hfr₁.len_eq]; exact Store.le_len_of_readBlock hA (by positivity))
        (by rw [hfr₁.len_eq]; exact Store.lt_len_of_get hg)
        (by rw [hfr₁.len_eq]; exact Store.lt_len_of_get hf)
        (hW.mono (by fp_sub) (by fp_sub)) (hGF.mono le_rfl (by fp_sub)) hgf
      refine (hacc.in_frame rfl rfl (by
        simp [Mem.Live, hfr₁.length_eq, Store.lt_length_of_get hg, Store.lt_length_of_get hf, hal,
          Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by nlinarith)])).mono
        (by fp_sub) ?_
      rintro m₂ - ⟨hA₂, hG₂, hF₂⟩
      exact Or.inr ⟨hgp, hG₂, hF₂, H', Rs, hch, hH', hA₂, hdec⟩
    · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (rg.1, rg.2 + 3)) hR0) ?_
      rw [show decide (0 < id (0 : ℝ)) = false by simp, if_neg (by simp)]
      exact (Writes.skip (Or.inl ⟨hg₁, hf₁, hA₁, fun _ => ⟨H', Rs, hch, hall⟩⟩)).mono bot_le
        fun _ _ h => h
  · rw [show decide (0 < id gv) = false by simpa using hgp, if_neg (by simp)]
    exact (Writes.skip (Or.inl ⟨hg, hf, hA, fun h => absurd h hgp⟩)).mono bot_le fun _ _ h => h

omit [Has IdxTst Q] in
/-- **The trials of `Regularize`** on a scalar machine with the standard model at
$(n + 1)\boldsymbol{u} \le 1/2500$, exact comparisons, index literals and exact natural literals
up to $n + 1$: from an upper Hessenberg $\mathbf{H}$ at `A`, $k \ge 1$ shifts $z_j$ stored as
pairs at `S`, the threshold word $t$ at `Thr`, the search word $1$ at `G`, and a shift $z_{j^*}$
every backward-stable degree $k$ step of which has a bottom subdiagonal entry of modulus at most
$\omega$, $(1 + \boldsymbol{u})^2\omega^2 \le t$, `NLAlib.ShiftedQR.regularizeTrials` sets the
flag to $1$ and stores at `A` an accepted step: a backward-stable degree $k$ step with some
shift $z_j$ repeated, upper Hessenberg, with a bottom entry passing the scan. -/
theorem regularizeTrials_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a s thr t sr ds rg g f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {zs : Fin k → ℂ} {tv fv ω : ℝ}
    (hH : IsUpperHessenberg H) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hA : HoldsMatrix a H m.store)
    (hs : ∀ j : Fin k, m.store.readBlock s.1 (s.2 + 2 * j) 2 = some [(zs j).re, (zs j).im])
    (hthr : m.store.get thr.1 thr.2 = some tv) (hg : m.store.get g.1 g.2 = some 1)
    (hf : m.store.get f.1 f.2 = some fv)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hGF : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1))
    (hAS : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
      Store.inBlock f.1 f.2 1) (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1))
    (jstar : Fin k) (hgood : ∀ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) Rs,
      IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k (zs jstar)) H' Rs →
        ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) :
    Writes .total I τ (regularizeTrials (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, s, thr, t, sr, ds, rg, a, g, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
          Store.inBlock rg.1 rg.2 5))
      (fun m' => m'.store.get f.1 f.2 = some 1 ∧ ∃ (j : Fin k)
        (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
        IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k (zs j)) H' Rs ∧
          IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
          ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv) m := by
  set F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
    Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5)
  have hFS : Fp.Disj F (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1) :=
    Fp.disj_sup_left.mpr ⟨hAS, hW.mono le_rfl (by fp_sub)⟩
  have hpair : ∀ j : Fin k, Store.inBlock s.1 (s.2 + 2 * j) 2 ≤ Store.inBlock s.1 s.2 (2 * k) :=
    fun j => Fp.inBlock_le_inBlock (by omega) (by omega)
  let Done : Mem ℝ → Prop := fun μ => μ.store.get g.1 g.2 = some 0 ∧
    μ.store.get f.1 f.2 = some 1 ∧ ∃ (j : Fin k) (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
      IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k (zs j)) H' Rs ∧
        IsUpperHessenberg H' ∧ HoldsMatrix a H' μ.store ∧
        ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv
  have hLive : ∀ (j : ℕ) (μ : Mem ℝ), μ.store.length = m.store.length →
      μ.Live [a, (s.1, s.2 + 2 * j), thr, t, sr, ds, rg, a, g, f] := by
    intro j μ hμ
    have hal := Store.lt_length_of_get (Store.get_of_readBlock hA (j := 0) (by positivity) 0)
    have hsl := Store.lt_length_of_get (Store.get_of_readBlock (hs ⟨0, hk0⟩) (j := 0)
      (by norm_num) 0)
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hμ]
    exact ⟨hal, hsl, Store.lt_length_of_get hthr,
      Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by nlinarith),
      Store.lt_length_of_lt_len (show sr.2 < m.store.len sr.1 by omega),
      Store.lt_length_of_lt_len (show ds.2 < m.store.len ds.1 by omega),
      Store.lt_length_of_lt_len (show rg.2 < m.store.len rg.1 by omega), hal,
      Store.lt_length_of_get hg, Store.lt_length_of_get hf⟩
  unfold regularizeTrials
  refine (writes_loop (N := k) rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun j μ => (μ.store.get g.1 g.2 = some 1 ∧ μ.store.get f.1 f.2 = some fv ∧
      HoldsMatrix a H μ.store ∧ j ≤ jstar) ∨ Done μ) (Or.inl ⟨hg, hf, hA, Nat.zero_le _⟩)
    ?_).mono le_rfl ?_
  · intro j hj μ hfr hinv
    have hl : ∀ b, μ.store.len b = m.store.len b := fun b => hfr.len_eq b
    have hsj := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hFS.mono le_rfl
      ((hpair ⟨j, hj⟩).trans le_sup_left)) (hs ⟨j, hj⟩)
    have hthrμ := hfr.keep (Store.readsOnly_get _ _ _) (hFS.mono le_rfl le_sup_right) hthr
    rcases hinv with ⟨hgμ, hfμ, hAμ, hjs⟩ | hdone
    · have htr := regularizeTrial_writes (τ := τ) (sp := (s.1, s.2 + 2 * j)) hS hM hu1 hL hNat hC
        hk0 hk hH hnu hAμ hsj hthrμ hgμ hfμ (by rw [hl]; exact hrt) (by rw [hl]; exact hrsr)
        (by rw [hl]; exact hrds) (by rw [hl]; exact hrrg)
        (hW.mono le_rfl (sup_le_sup_right (sup_le_sup_left (hpair ⟨j, hj⟩) _) _)) hts htd hsd hrg
        hGF hgf
      refine (htr.in_frame rfl rfl (hLive j μ hfr.length_eq)).mono le_rfl ?_
      rintro μ' - (⟨hg', hf', hA', hch⟩ | ⟨-, hg', hf', H', Rs, hc, hH', hA', hdec⟩)
      · refine Or.inl ⟨hg', hf', hA', ?_⟩
        by_contra hlt
        have hjeq : (⟨j, hj⟩ : Fin k) = jstar := Fin.ext (by simp at hlt ⊢; omega)
        obtain ⟨H', Rs, hc, hall⟩ := hch one_pos
        obtain ⟨i, hik, hi⟩ := hgood H' Rs (by rw [← hjeq]; exact hc)
        have h1 := hall i hik
        have h2 : ‖H' i.succ i.castSucc‖ ^ 2 ≤ ω ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
        nlinarith [sq_nonneg (1 + u)]
      · exact Or.inr ⟨hg', hf', ⟨j, hj⟩, H', Rs, hc, hH', hA', hdec⟩
    · obtain ⟨hg0, hf1, j', H', Rs, hc, hH', hA', hdec⟩ := hdone
      have htr := regularizeTrial_writes (τ := τ) (sp := (s.1, s.2 + 2 * j)) hS hM hu1 hL hNat hC
        hk0 hk hH' hnu hA' hsj hthrμ hg0 hf1 (by rw [hl]; exact hrt) (by rw [hl]; exact hrsr)
        (by rw [hl]; exact hrds) (by rw [hl]; exact hrrg)
        (hW.mono le_rfl (sup_le_sup_right (sup_le_sup_left (hpair ⟨j, hj⟩) _) _)) hts htd hsd hrg
        hGF hgf
      refine (htr.in_frame rfl rfl (hLive j μ hfr.length_eq)).mono le_rfl ?_
      rintro μ' - (⟨hg', hf', hA'', -⟩ | ⟨h0, -⟩)
      · exact Or.inr ⟨hg', hf', j', H', Rs, hc, hH', hA'', hdec⟩
      · exact absurd h0 (lt_irrefl 0)
  · rintro μ - (⟨-, -, -, hjs⟩ | ⟨-, hF, hrest⟩)
    · exact absurd jstar.isLt (by omega)
    · exact ⟨hF, hrest⟩

omit [Has IdxTst Q] in
/-- **The decision of `Regularize`** on a scalar machine with the standard model, exact
comparisons, index literals and exact natural literals up to $n + 1$: with the $k$ shifts $z_j$
at `S`, the word $0.999\theta^k$ at `C` and the hypotheses of `NLAlib.ShiftedQR.optimalTest_writes`,
`NLAlib.ShiftedQR.regularizeDecide` either sets the flag to $0$, leaves $\mathbf{H}$ at `A` and
the shifts are $\theta$-optimal, or sets the flag to $1$ and stores at `A` an accepted step
(`NLAlib.ShiftedQR.regularizeTrials_writes`), given that, when the shifts are not
$0.998^{1/k}\theta$-optimal, some shift decouples every backward-stable step with it. -/
theorem regularizeDecide_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a s c thr t sr ds rg g f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {zs : Fin k → ℂ} {tv ω θ C : ℝ}
    (hH : IsUpperHessenberg H) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hθ : 0 < θ)
    (hψ : 0 < hessenbergPotential k H) (hzs : ∀ j, ‖zs j‖ ≤ C * specNorm H)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) *
      ((2 + 2 * C) * specNorm H) ^ k ≤ (θ * hessenbergPotential k H) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hA : HoldsMatrix a H m.store)
    (hs : ∀ j : Fin k, m.store.readBlock s.1 (s.2 + 2 * j) 2 = some [(zs j).re, (zs j).im])
    (hc : m.store.get c.1 c.2 = some (0.999 * θ ^ k))
    (hthr : m.store.get thr.1 thr.2 = some tv) (hrg' : g.2 < m.store.len g.1)
    (hrf : f.2 < m.store.len f.1)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hGF : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1))
    (hAS : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
      Store.inBlock f.1 f.2 1) (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1 ⊔
        Store.inBlock c.1 c.2 1))
    (hdich : ¬IsOptimalRitzValues ((0.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ) H (List.ofFn zs) →
      ∃ jstar : Fin k, ∀ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) Rs,
        IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k (zs jstar)) H' Rs →
          ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) :
    Writes .total I τ (regularizeDecide (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, s, c, thr, t, sr, ds, rg, a, g, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
          Store.inBlock rg.1 rg.2 5))
      (fun m' => (m'.store.get f.1 f.2 = some 0 ∧ HoldsMatrix a H m'.store ∧
          IsOptimalRitzValues θ H (List.ofFn zs)) ∨
        (m'.store.get f.1 f.2 = some 1 ∧ ∃ (j : Fin k)
          (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
          (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
          IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k (zs j)) H' Rs ∧
            IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
            ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv)) m := by
  have h0 : M.lit 0 = 0 := by simpa using hM.lit 0
  have h1 : M.lit 1 = 1 := by simpa using hNat 1 (by omega)
  have h2 : M.lit 2 = 2 := by simpa using hNat 2 (by omega)
  have hlen : (List.ofFn zs).length = k := List.length_ofFn
  have hsS : m.store.readBlock s.1 s.2 (2 * (List.ofFn zs).length) =
      some ((List.ofFn zs).flatMap fun z => [z.re, z.im]) :=
    readBlock_flatMap_pair_of_forall fun j hj => by
      have := hs ⟨j, by simpa using hj⟩
      simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlen ▸ hj] using this
  have hal := Store.lt_length_of_get (Store.get_of_readBlock hA (j := 0) (by positivity) 0)
  have hsl := Store.lt_length_of_get (Store.get_of_readBlock (hs ⟨0, hk0⟩) (j := 0)
    (by norm_num) 0)
  have hgl := Store.lt_length_of_lt_len hrg'
  have hopt := optimalTest_writes (τ := τ) (ss := List.ofFn zs) (a := a) (s := s) (c := c)
    (f := g) hS hM (hNat.mono (by omega)) hC (by simp; omega) (by simp; omega) hθ
    (by simpa using hψ) (by simpa using fun j => hzs j) (by simpa using huo)
    (by simpa using huo1) hA hsS (by simpa using hc) hrg'
    (by simp [Mem.Live, hal, hsl, Store.lt_length_of_get hc, hgl])
    (by
      rw [hlen]
      exact Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨hGF.mono le_sup_left le_sup_right,
        hAS.mono (by fp_sub) (by fp_sub)⟩, hAS.mono (by fp_sub) (by fp_sub)⟩)
  rw [hlen] at hopt
  unfold regularizeDecide
  refine hopt.frame_seq_le rfl rfl (by simp [Mem.Live, hal, hsl, Store.lt_length_of_get hc, hgl])
    (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, b, hb, hb01, hb1, hb0⟩
  have hA₁ := hA.of_eqOff hfr₁ (hGF.mono le_sup_left le_sup_right)
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := g) hb) ?_
  rcases hb01 with rfl | rfl
  · rw [show decide (0 < id (0 : ℝ)) = false by simp, if_neg (by simp)]
    obtain ⟨jstar, hgood⟩ := hdich (hb0 rfl)
    refine (writes_call_const (hS (.lit 2)) (z := f) rfl trivial
      (by rw [hfr₁.len_eq]; exact hrf)).seq_le (by fp_sub) ?_
    rintro m₂ hfr₂ ⟨-, hF₂⟩
    refine (writes_call_const (hS (.lit 1)) (z := g) rfl trivial
      (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hrg')).seq_le (by fp_sub) ?_
    rintro m₃ hfr₃ ⟨-, hG₃⟩
    have hfr := (hfr₁.trans' hfr₂).trans' hfr₃
    have hl : ∀ b, m₃.store.len b = m.store.len b := fun b => by
      rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]
    have hkeep : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock g.1 g.2 1) (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1) :=
      hAS.mono (by fp_sub) (by fp_sub)
    have hs₃ : ∀ j : Fin k, m₃.store.readBlock s.1 (s.2 + 2 * j) 2 =
        some [(zs j).re, (zs j).im] := fun j => hfr.keep (Store.readsOnly_readBlock _ _ _ _)
      (hkeep.mono le_rfl ((Fp.inBlock_le_inBlock (by omega) (by omega)).trans le_sup_left))
      (hs j)
    have hthr₃ := hfr.keep (Store.readsOnly_get _ _ _) (hkeep.mono le_rfl le_sup_right) hthr
    have hA₃ := hA.of_eqOff hfr (hGF.mono (by fp_sub) le_sup_right)
    have hF₃ := hfr₃.keep (Store.readsOnly_get _ _ _) hgf hF₂
    have htr := regularizeTrials_writes (τ := τ) hS hM hu1 hL hNat hC hk0 hk hH hnu hA₃ hs₃
      hthr₃ (by rw [hG₃, h1]) hF₃ (by rw [hl]; exact hrt) (by rw [hl]; exact hrsr)
      (by rw [hl]; exact hrds) (by rw [hl]; exact hrrg) hW hts htd hsd hrg hGF hgf
      (hAS.mono le_rfl (by fp_sub)) jstar hgood hthrω
    have hL₃ : m₃.store.length = m.store.length := hfr.length_eq
    refine (htr.in_frame rfl rfl ?_).mono (by fp_sub) fun _ _ h => Or.inr h
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hL₃]
    exact ⟨hal, hsl, Store.lt_length_of_get hthr,
      Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by nlinarith),
      Store.lt_length_of_lt_len (show sr.2 < m.store.len sr.1 by omega),
      Store.lt_length_of_lt_len (show ds.2 < m.store.len ds.1 by omega),
      Store.lt_length_of_lt_len (show rg.2 < m.store.len rg.1 by omega), hal, hgl,
      Store.lt_length_of_lt_len hrf⟩
  · rw [show decide (0 < id (1 : ℝ)) = true by simp, if_pos rfl]
    refine (writes_call_const (hS (.lit 0)) (z := f) rfl trivial
      (by rw [hfr₁.len_eq]; exact hrf)).mono (by fp_sub) ?_
    rintro m₂ hfr₂ ⟨-, hF₂⟩
    exact Or.inl ⟨by rw [hF₂, h0], hA₁.of_eqOff hfr₂ (hGF.mono le_sup_right le_sup_right),
      hb1 rfl⟩

end Trials

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

/-- **The dichotomy of `Regularize`, with rounded steps** ([BanksGarzaVargasSrivastava2022,
proof of Lemma 4.6], with the corrections G10, G11 of the errata): let $\mathbf{H}$ be upper
Hessenberg of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$
with $\kappa(\mathbf{V}) \le B$, $B^{2/k} \le 2$, $1 \le k \le n$, eigenvalues separated by
$2\omega^2/\Sigma$, $\|\mathbf{H}\|_2 \le \Sigma$, $0 < \omega \le \psi_k(\mathbf{H})$, and
shifts $z_1, \dots, z_k$ within $\omega^2/(2020\Sigma)$ of a listing of the eigenvalues of the
trailing $k \times k$ block, with $\lvert z_j\rvert \le 1.1\|\mathbf{H}\|_2$ and at distance at
least $d > 0$ from every $e_i$. If the shifts are not $0.998^{1/k}\theta$-optimal,
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, then some $z_{j^*}$ has the property that
every backward-stable chain of $k$ steps with the shift $z_{j^*}$ and relative error $x \ge 0$,
$$x \le (16B)^{-1}\Bigl(\frac{d}{4.2\Sigma}\Bigr)^k, \qquad
68.2B\Sigma\Bigl(\frac{4.2\Sigma}{d}\Bigr)^k\sqrt{n + 1}\,x \le \frac{\omega}{2},$$
ends in a matrix with a bottom subdiagonal entry of modulus at most $\omega$. -/
theorem exists_forall_isStableQRChain_exists_norm_subdiag_le {n k : ℕ} {B S ω d x : ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {zs lam : Fin k → ℂ}
    (hH : IsUpperHessenberg H) (hk : 0 < k) (hkn : k ≤ n) (hBk : B ^ ((2 : ℝ) / k) ≤ 2)
    (hω : 0 < ω) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e)
    (hκ : pseudoConditionNumber V ≤ B) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hS : specNorm H ≤ S) (hψ : ω ≤ hessenbergPotential k H)
    (hlam : IsEigenvalueListing (trailingBlock k H) lam)
    (hzl : ∀ j, ‖zs j - lam j‖ ≤ ω ^ 2 / (20 * 101 * S))
    (hz : ∀ j, ‖zs j‖ ≤ 1.1 * specNorm H) (hd : 0 < d) (hdist : ∀ j i, d ≤ ‖e i - zs j‖)
    (hopt : ¬IsOptimalRitzValues ((0.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹))) H (List.ofFn zs))
    (hx : 0 ≤ x) (hxu : x ≤ (16 * B)⁻¹ * (d / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / d) ^ k * √(n + 1) * x ≤ ω / 2) :
    ∃ jstar : Fin k, ∀ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) Rs,
      IsStableQRChain x H (List.replicate k (zs jstar)) H' Rs →
        ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω := by
  have hB : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hψH := hessenbergPotential_le_specNorm hk hkn H
  have hH0 : H ≠ 0 := fun h0 => by
    rw [h0, specNorm_zero] at hψH
    rw [h0] at hψ
    linarith
  obtain ⟨ss, hperm, hss⟩ := exists_perm_forall₂_ritzValues hlam hzl
  have hne : ∀ r ∈ ss, ∀ i, e i ≠ r := by
    intro r hr i he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (hperm.subset hr)
    have := hdist j i
    rw [he, sub_self, norm_zero] at this
    linarith
  obtain ⟨r, hr, hτ⟩ := exists_mem_le_norm_inv_pow_of_not_isOptimalRitzValues hH hk hkn hB hBk hω
    hV hHV hκ hgap hS hψ hss hne (by rwa [isOptimalRitzValues_iff_of_perm hperm])
  obtain ⟨jstar, rfl⟩ := List.mem_ofFn.mp (hperm.subset hr)
  refine ⟨jstar, fun H' Rs hch => ?_⟩
  exact hch.exists_norm_subdiag_le_of_le_norm_inv_pow hx (by norm_num) hd hω hk hkn hH0 hH hV hHV
    hκ hS (hz jstar) (fun i => hdist jstar i) hτ hxu hbound

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops MeasureTheory

section SmallEig

variable {O Q : Type} [Has EigenvalueKernelOp O]

/-- **A randomized small-eigenvalue kernel with its forward error** ([BanksGarzaVargasSrivastava2022,
Definition 1.2]): if the interpretation's `smallEig` is a randomized kernel with forward error
$\beta$ and failure probability $\varphi$ on the stream `s` (`NLAlib.ShiftedQR.IsRandomSmallEig`),
the leaf routine that calls it on an upper Hessenberg $\mathbf{B}$ of order $d$ writes only its
output and, except with probability at most $\varphi$, stores values within $\beta$ of a listing
of the eigenvalues of $\mathbf{B}$ with multiplicity. -/
theorem IsRandomSmallEig.smallEigLeaf_pwrites {law : ℕ → Measure ℝ} {s : ℕ} {β φ : ℝ}
    {I : Interp O Q ℝ} (h : IsRandomSmallEig law s β φ I) {d : ℕ} {w o : ℕ × ℕ}
    (B : Matrix (Fin d) (Fin d) ℂ) (hB : IsUpperHessenberg B) :
    PWrites law I (smallEigLeaf (O := O) (Q := Q)).body (Env.frame [d] [w, o])
      (Store.inBlock o.1 o.2 (2 * d))
      (fun μ => HoldsMatrix w B μ.store ∧ μ.Live [w, o] ∧ o.2 + 2 * d ≤ μ.store.len o.1 ∧
        Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)))
      (fun μ' => ∃ roots ev : Fin d → ℂ, IsEigenvalueListing B ev ∧
        (∀ i, ‖roots i - ev i‖ ≤ β) ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) φ := by
  obtain ⟨W, Bad, hBad, hφ, hI⟩ := h
  refine PWrites.of_window (s := s) (W := W d) (Bad := fun _ => Bad d B)
    (measurable_snd (hBad d B)) (fun _ _ => hφ d B hB) ?_
  rintro μ τ ⟨hH, hl, hroom, hdisj⟩ hgood
  unfold smallEigLeaf
  have hread : μ.readBlocks [w] [2 * (d * d)] = some [matrixWords B] := by
    simp [Mem.readBlocks, show μ.store.readBlock w.1 w.2 (2 * (d * d)) =
      some (matrixWords B) from hH]
  refine (writes_call (R := randomSmallEigRel s W Bad β) hI (d := [d]) (a := [w]) (b := [o])
    (k := W d) (ls := [2 * d]) rfl rfl rfl rfl rfl rfl trivial (by simp [Fp.Apart])
    (fun _ => ⟨by simpa [Mem.Live] using hl, ⟨[matrixWords B], hread, trivial⟩,
      by simpa [Mem.Room] using hroom⟩)).mono (by simp [Fp.blocks]) ?_
  rintro μ' - ⟨-, xs, ys, hr, hys, hrel⟩
  have hxs : xs = [matrixWords B] := Option.some.inj (hr.symm.trans hread)
  have hwin : (fun j : Fin (W d) => (τ.window s μ.pos (W d)).getD j 0) =
      Tape.windowFn τ s μ.pos (W d) := by
    funext j
    simp [Tape.window, Tape.windowFn, List.getD_eq_getElem?_getD]
  obtain ⟨roots, ev, hev, hfw, rfl⟩ := hrel d (matrixWords B) rfl hxs
    (by simpa using hB) (by
      change (fun j : Fin (W d) => (τ.window s μ.pos (W d)).getD j 0) ∉ _
      rw [hwin]
      simpa using hgood)
  rw [matrixOfWords_matrixWords] at hev
  refine ⟨roots, ev, hev, hfw, ?_⟩
  obtain ⟨y, hy, hyy⟩ := Option.bind_eq_some_iff.mp
    (by simpa [Mem.readBlocks, randomSmallEigRel] using hys)
  simp only [Option.some.injEq, List.cons.injEq, and_true] at hyy
  simpa [HoldsMatrix] using hyy ▸ hy

end SmallEig

end NLAlib.ShiftedQR

namespace NLAlib

variable {n : ℕ}

/-- An eigenvalue of the trailing $k \times k$ block, $k \le n + 1$, is at most
$\|\mathbf{H}\|_2$. -/
theorem IsEigenvalueListing.norm_le_specNorm_of_trailingBlock {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {lam : Fin k → ℂ}
    (hlam : IsEigenvalueListing (trailingBlock k H) lam) (hkn : k ≤ n + 1) (j : Fin k) :
    ‖lam j‖ ≤ specNorm H := by
  have hroots : (trailingBlock k H).charpoly.roots = (List.ofFn lam : Multiset ℂ) := by
    rw [isEigenvalueListing_iff.mp hlam]
    simpa only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
      List.prod_ofFn, Function.comp_def] using
      Polynomial.roots_multiset_prod_X_sub_C (List.ofFn lam : Multiset ℂ)
  refine norm_le_specNorm_of_mem_ritzValues hkn ?_
  rw [ritzValues, Multiset.mem_toList, hroots, Multiset.mem_coe]
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

end NLAlib

namespace NLAlib.ShiftedQR

open Ops

/-- The words `Regularize` with scratch at `L, …, L + 6` reads, and the room it writes into: the
matrix $\mathbf{H}$ at `a`, the radius word $R$ at `rd`, the word $c_w$ at `c`, the threshold
word $t$ at `thr`, room for the $k$ output pairs at `s` and the flag at `f`, and seven scratch
buffers of the lengths of `NLAlib.ShiftedQR.regularize` above the $L$ buffers of the caller. -/
def RegularizeCtx (L : ℕ) {n : ℕ} (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (R cw tv : ℝ) (a rd c thr s f : ℕ × ℕ) (m : Mem ℝ) : Prop :=
  HoldsMatrix a H m.store ∧ m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some cw ∧
    m.store.get thr.1 thr.2 = some tv ∧ s.2 + 2 * k ≤ m.store.len s.1 ∧
    f.2 < m.store.len f.1 ∧ m.store.length = L + 7 ∧ m.store.len L = 2 * (k * k) ∧
    m.store.len (L + 1) = 2 ∧ m.store.len (L + 2) = 1 ∧
    m.store.len (L + 3) = 2 * ((n + 1) * (n + 1)) ∧ m.store.len (L + 4) = 2 * k ∧
    m.store.len (L + 5) = 2 * k ∧ m.store.len (L + 6) = 5

/-- The context survives a write apart from the matrix and the three input words. -/
theorem RegularizeCtx.of_eqOff {L n k : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {R cw tv : ℝ} {a rd c thr s f : ℕ × ℕ} {m m' : Mem ℝ} {F : Fp}
    (h : RegularizeCtx L k H R cw tv a rd c thr s f m) (hfr : m.store.EqOff F m'.store)
    (hF : Fp.Disj F (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1)) :
    RegularizeCtx L k H R cw tv a rd c thr s f m' := by
  obtain ⟨hA, hrd, hc, ht, hs, hf, hlen, h0, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hA.of_eqOff hfr (hF.mono le_rfl (by fp_sub)),
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) hrd,
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) hc,
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) ht, ?_⟩
  simp only [hfr.len_eq, hfr.length_eq]
  exact ⟨hs, hf, hlen, h0, h1, h2, h3, h4, h5, h6⟩

/-- **The outcome of `Regularize`**, with the optimality parameter $\theta$, the distance $d$ to
the spectrum, the threshold word $t$ and the backward error $\varepsilon$: either the flag is $0$,
`a` still holds $\mathbf{H}$, and `s` holds $k$ shifts that are $\theta$-optimal, at distance at
least $d$ from every $e_i$ and in $\mathbb{D}(0, 1.1\|\mathbf{H}\|_2)$; or the flag is $1$ and
`a` holds an upper Hessenberg perturbed unitary similarity of $\mathbf{H}$ with error
$\varepsilon$ one of whose bottom $k$ subdiagonal entries passes the scan. -/
def RegularizeOutcome {n : ℕ} (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (e : Fin (n + 1) → ℂ) (u θ d tv ε : ℝ) (a s f : ℕ × ℕ) (m' : Mem ℝ) : Prop :=
  (m'.store.get f.1 f.2 = some 0 ∧ HoldsMatrix a H m'.store ∧ ∃ zs : Fin k → ℂ,
      m'.store.readBlock s.1 s.2 (2 * k) = some ((List.ofFn zs).flatMap fun z => [z.re, z.im]) ∧
      IsOptimalRitzValues θ H (List.ofFn zs) ∧ (∀ j i, d ≤ ‖e i - zs j‖) ∧
      ∀ j, ‖zs j‖ ≤ 1.1 * specNorm H) ∨
    (m'.store.get f.1 f.2 = some 1 ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsPerturbedUnitarySimilar H H' ε ∧ IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
      ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv)

/-- The bounds on the perturbed shifts that `Regularize` needs: from shifts $z_j$ within
$\beta + R + \delta_j$ of a listing $\lambda$ of the eigenvalues of the trailing block, with
$\lvert z_j - e_l\rvert + \delta_j \ge \eta$, $\delta_j = 2\boldsymbol{u}(\lvert\lambda_j\rvert
+ \beta + R)$, under $\beta + R + 2\boldsymbol{u}(\Sigma + \beta + R) \le \omega^2/(2020\Sigma)$,
$4\boldsymbol{u}(\Sigma + \beta + R) \le \eta$ and $0 < \omega \le \psi_k(\mathbf{H})$,
$\|\mathbf{H}\|_2 \le \Sigma$: the shifts are within $\omega^2/(2020\Sigma)$ of $\lambda$, in
$\mathbb{D}(0, 1.1\|\mathbf{H}\|_2)$ and at distance at least $\eta/2$ from every $e_l$. -/
theorem regularize_shift_bounds {n k N : ℕ} {u β R η ω S : ℝ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {lam zs : Fin k → ℂ} {e : Fin N → ℂ}
    (hu0 : 0 ≤ u) (hk : 0 < k) (hkn : k ≤ n) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hS : specNorm H ≤ S) (hlam : IsEigenvalueListing (trailingBlock k H) lam)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ η)
    (hz : ∀ j : Fin k, ‖zs j - lam j‖ ≤ β + R + 2 * u * (‖lam j‖ + β + R) ∧
      ∀ l, η ≤ ‖zs j - e l‖ + 2 * u * (‖lam j‖ + β + R)) :
    (∀ j, ‖zs j - lam j‖ ≤ ω ^ 2 / (20 * 101 * S)) ∧ (∀ j, ‖zs j‖ ≤ 1.1 * specNorm H) ∧
      ∀ j l, η / 2 ≤ ‖e l - zs j‖ := by
  have hψH := hessenbergPotential_le_specNorm hk hkn H
  have hS0 : 0 < S := by linarith
  have hlH : ∀ j, ‖lam j‖ ≤ specNorm H := fun j => hlam.norm_le_specNorm_of_trailingBlock (by omega) j
  have hδ : ∀ j, 2 * u * (‖lam j‖ + β + R) ≤ 2 * u * (S + β + R) := fun j => by
    have := hlH j; gcongr; linarith
  have hsmall : ω ^ 2 / (20 * 101 * S) ≤ 0.1 * specNorm H := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨fun j => ?_, fun j => ?_, fun j l => ?_⟩
  · linarith [(hz j).1, hδ j]
  · have h1 := norm_le_norm_add_norm_sub' (zs j) (lam j)
    linarith [(hz j).1, hδ j, hlH j]
  · have := (hz j).2 l
    rw [norm_sub_rev] at this
    nlinarith [hδ j]

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

section Tail

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- The views of `Regularize` are apart: the matrix, the output pairs and the flag from each other
and from the three input words, all below the scratch handle $L$. -/
structure RegularizeViews (L : ℕ) (n k : ℕ) (a rd c thr s f : ℕ × ℕ) : Prop where
  lt : a.1 < L ∧ rd.1 < L ∧ c.1 < L ∧ thr.1 < L ∧ s.1 < L ∧ f.1 < L
  as : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock s.1 s.2 (2 * k))
  af : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1)
  sf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1)
  io : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
    Store.inBlock f.1 f.2 1) (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔
      Store.inBlock thr.1 thr.2 1)

/-- **The deterministic tail of `Regularize`**: from the context
`NLAlib.ShiftedQR.RegularizeCtx` and $k \ge 1$ perturbed shifts at `s` as
`NLAlib.ShiftedQR.DrawsInv` leaves them (within $\beta + R + \delta_j$ of a listing of the
eigenvalues of the trailing block, $\eta - \delta_j$ from every eigenvalue), under the precision
conditions of `Optimal`, of the rounded steps and of the scan, the decision of `Regularize` ends
in `NLAlib.ShiftedQR.RegularizeOutcome` with $d = \eta/2$, the optimality parameter
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$ and the backward error
$2.1\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$. -/
theorem regularizeDecide_outcome {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k L : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (hv : RegularizeViews L n k a rd c thr s f)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω β R η tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖) (hη : 0 < η)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ η) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (16 * B)⁻¹ * (η / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (η / 2)) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    (hctx : RegularizeCtx L k H R
      (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) tv
      a rd c thr s f m)
    (hinv : DrawsInv u β R η (fun lam : Fin k → ℂ => IsEigenvalueListing (trailingBlock k H) lam)
      e rd (L + 1, 0) s k m) :
    Writes .total I τ (regularizeDecide (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, s, c, thr, (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), a,
        (L + 2, 0), f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 2) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 3) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 4) 0 (2 * k) ⊔ Store.inBlock (L + 5) 0 (2 * k) ⊔
          Store.inBlock (L + 6) 0 5))
      (RegularizeOutcome k H e u (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) *
        (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) (η / 2) tv
        ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f) m := by
  set θ := 1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) with hθdef
  obtain ⟨⟨ha, hrd, hcl, htl, hsl, hfl⟩, has, haf, hsf, hio⟩ := hv
  obtain ⟨hA, -, hc, hthr, -, hrf, hlen, -, -, h2, h3, h4, h5, h6⟩ := hctx
  obtain ⟨-, -, lam, hlam, zs, hpairs, hzk⟩ := hinv
  have hu0 := hM.roundoff_nonneg
  have hψH := hessenbergPotential_le_specNorm hk0 hk H
  have hψ0 : 0 < hessenbergPotential k H := lt_of_lt_of_le hω hψ
  have hS0 : 0 < S := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le one_pos ((one_le_pseudoConditionNumber hV.ne_zero).trans hκ)
  have hθ : 0 < θ := by positivity
  obtain ⟨hzl, hz, hdist⟩ := regularize_shift_bounds hu0 hk0 hk hω hψ hSH hlam hβ hdη
    (fun j => (hzk j).2 j.isLt)
  have hx : (0 : ℝ) ≤ 300 * (n + 1) ^ 2 * u := by positivity
  have huo' : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) *
      ((2 + 2 * 1.1) * specNorm H) ^ k ≤ (θ * hessenbergPotential k H) ^ k := by
    refine le_trans ?_ (huo.trans (by gcongr))
    gcongr
  have hdich := fun hopt => exists_forall_isStableQRChain_exists_norm_subdiag_le (d := η / 2)
    hH hk0 hk hBk hω hV hHV hκ hgap hSH hψ hlam hzl hz (by positivity)
    (fun j i => hdist j i) hopt hx hxu hbound
  have hdec := regularizeDecide_writes (τ := τ) (m := m) (a := a) (s := s) (c := c) (thr := thr)
    (t := (L + 3, 0)) (sr := (L + 4, 0)) (ds := (L + 5, 0)) (rg := (L + 6, 0)) (g := (L + 2, 0))
    (f := f) (C := 1.1) hS hM hu1 hL hNat hC hk0 hk hH hnu hθ hψ0 hz huo' huo1 hA hpairs hc hthr
    (by simp [h2]) hrf (by simp [h3]) (by simp [h4]) (by simp [h5]) (by simp [h6])
    (by disjoint) (by disjoint) (by disjoint) (by disjoint) (by disjoint)
    (Fp.disj_sup_left.mpr ⟨by disjoint, Fp.disj_sup_right.mpr ⟨by disjoint, haf.symm⟩⟩)
    (by disjoint) (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_right.mpr
      ⟨Fp.disj_sup_right.mpr ⟨has, hio.mono (by fp_sub) (by fp_sub)⟩,
        hio.mono (by fp_sub) (by fp_sub)⟩, by disjoint⟩, Fp.disj_sup_right.mpr
      ⟨Fp.disj_sup_right.mpr ⟨hsf.symm, hio.mono (by fp_sub) (by fp_sub)⟩,
        hio.mono (by fp_sub) (by fp_sub)⟩⟩) hdich hthrω
  refine hdec.mono le_rfl ?_
  rintro m' hfr (⟨hF, hA', hopt⟩ | ⟨hF, j, H', Rs, hch, hH', hA', hdec'⟩)
  · refine Or.inl ⟨hF, hA', zs, ?_, hopt, fun j i => hdist j i, hz⟩
    have := readBlock_flatMap_pair_of_forall (s := m'.store) (b := s.1) (o := s.2)
      (zs := List.ofFn zs) fun j hj => by
        have hj' : j < k := by simpa using hj
        have hkeep := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_sup_left.mpr
          ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨has.symm.mono
            (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl |>.symm, by disjoint⟩,
            hsf.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl |>.symm⟩,
            by disjoint⟩) (hpairs ⟨j, hj'⟩)
        simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj'] using hkeep
    simpa using this
  · refine Or.inr ⟨hF, H', ?_, hH', hA', hdec'⟩
    have hsim := hch.isPerturbedUnitarySimilar hx (C := 1.1) (by norm_num) (fun s hs => by
      rw [List.eq_of_mem_replicate hs]; exact hz j)
    simpa using hsim

end Tail

end NLAlib.ShiftedQR
