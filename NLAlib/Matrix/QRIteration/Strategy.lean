/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.Matrix.QRIteration.Ritz

/-!
# The shifting strategy $\mathrm{Sh}_{k,B}$ and its global convergence in exact arithmetic

The shifting strategy of [BanksGarzaVargasSrivastava2021, §4.2] as a mathematical rule on the
current Hessenberg iterate $\mathbf{H}$ and a list of $k = 2^m$ approximate Ritz values: if a
Ritz value is an eigenvalue, shift by it (the step then decouples exactly); otherwise try the
promising Ritz value $r$ of `NLAlib.findRitz`, then the exceptional shifts, a square grid on the
disk of radius $(2B)^{1/k}\theta\alpha\,\psi_k(\mathbf{H})$ about $r$, and take a shift
$s$ whose degree $k$ step $(z - s)^k$ decouples exactly or reduces the potential by $1 - \gamma$.
The iteration `NLAlib.shqrIterate` repeats this with a Ritz-value oracle.

This is the exact iteration the convergence theorem is about, written as a definition so that
the theorem names one sequence. It is a specification, not an implementation: it compares exact
real numbers, decides equality of complex determinants by classical choice and carries no cost.
The finite-precision algorithm of [BanksGarzaVargasSrivastava2022] is to refine it (design note
`docs/design/Eigensolvers-ShiftedQR.md`, §9).

The results: stagnation of a promising shift implies last-row weight near it (Lemma 4.6 there);
some point of the square grid succeeds (Lemma 4.7 there); one iteration decouples or reduces the
potential; the iteration decouples within $\lceil\log(1/\delta)/\log(1/(1 - \gamma))\rceil$ steps
(Theorem 1.6 there), with the count of shifts tried per iteration and the paper's parameter
instance; and the normal case (Theorem 1.2 there).

## Main definitions

* `NLAlib.squareGrid`: the exceptional shifts, a square grid covering a disk.
* `NLAlib.exceptionalRadius`, `NLAlib.exceptionalSpacing`: the radius and relative spacing.
* `NLAlib.IsShiftSuccess`: a shift whose degree $k$ step decouples or reduces the potential.
* `NLAlib.shqrCandidates`, `NLAlib.shqrShift`, `NLAlib.shqrStep`, `NLAlib.shqrIterate`.

## Main results

* `NLAlib.IsOptimalRitzValues.sq_mul_pow_le_mul_sum_lastRowWeights_filter`: stagnation implies
  support.
* `NLAlib.exists_mem_squareGrid_norm_sub_le`, `NLAlib.length_squareGrid_le`,
  `NLAlib.norm_sub_le_of_mem_squareGrid`: the grid.
* `NLAlib.IsOptimalRitzValues.exists_mem_squareGrid_det_eq_zero_or_one_le`: an exceptional shift
  succeeds.
* `NLAlib.IsUpperHessenberg.isDecoupled_zero_shqrStep_or_hessenbergPotential_le`: one
  iteration.
* `NLAlib.IsUpperHessenberg.exists_le_isDecoupled_shqrIterate`: rapid decoupling.
* `NLAlib.length_shqrCandidates_le`, `NLAlib.exceptionalSpacing_ge`: shifts per iteration.
* `IsStarNormal.exists_le_isDecoupled_shqrIterate_ritzValues`: the normal case.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- The **square grid** of $(m + 1)^2$ points $c + R\,(2i/m - 1) + R\,(2j/m - 1)\,\mathrm{i}$,
$0 \le i, j \le m$, with $m = \lceil\sqrt2/\varepsilon\rceil$: it covers the square of half-side
$R$ about $c$, so every point of the disk of radius $R$ about $c$ is within $\varepsilon R$ of a
grid point. An explicit $\varepsilon R$-net, in place of the maximal separated set of
[BanksGarzaVargasSrivastava2021, proof of Lemma 4.7]. -/
noncomputable def squareGrid (c : ℂ) (R ε : ℝ) : List ℂ :=
  (List.range (⌈Real.sqrt 2 / ε⌉₊ + 1)).flatMap fun i =>
    (List.range (⌈Real.sqrt 2 / ε⌉₊ + 1)).map fun j =>
      c + (R : ℂ) * ⟨2 * (i : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) - 1,
        2 * (j : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) - 1⟩

/-- The **radius of the exceptional disk**, $(2B)^{1/k}\theta\alpha\psi$, for degree $k$,
condition bound $B$, optimality $\theta$, promising parameter $\alpha$ and potential $\psi$.
[BanksGarzaVargasSrivastava2021, Lemma 4.7], line 1 of $\mathrm{Exc}$ there. -/
noncomputable def exceptionalRadius (k : ℕ) (B θ α ψ : ℝ) : ℝ :=
  (2 * B) ^ ((k : ℝ)⁻¹) * θ * α * ψ

/-- The **relative spacing of the exceptional shifts**,
$$\varepsilon = \Bigl(\frac{\rho}{(14B^4)^{1/k}\alpha^2\theta^2}\Bigr)^{k/(k-1)}\,,$$
with $\rho = (1 - \gamma)^2$ in exact arithmetic ($\rho = \xi(1 - \gamma)$ for a stagnation ratio
$\xi$ in finite precision). [BanksGarzaVargasSrivastava2021, Lemma 4.7], line 2 of
$\mathrm{Exc}$ there, with $12$ in place of $14$ for a net of $9/\varepsilon^2$ points; the
square grid has up to $12/\varepsilon^2$. -/
noncomputable def exceptionalSpacing (k : ℕ) (B θ α ρ : ℝ) : ℝ :=
  (ρ / ((14 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^ ((k : ℝ) / (k - 1))

/-- A shift $s$ is a **success** for the degree $k$ and rate $\gamma$ at $\mathbf{H}$ if the
degree $k$ step with shift polynomial $(z - s)^k$ gives a reduced matrix or reduces the
potential: $\psi_k(\widehat{\mathbf{H}}) \le (1 - \gamma)\psi_k(\mathbf{H})$. -/
def IsShiftSuccess (γ : ℝ) (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ) : Prop :=
  IsDecoupled 0 (multiShiftedQRStep H (List.replicate k s)) ∨
    hessenbergPotential k (multiShiftedQRStep H (List.replicate k s)) ≤
      (1 - γ) * hessenbergPotential k H

/-- The **candidate shifts** of $\mathrm{Sh}_{k,B}$ at $\mathbf{H}$ for a list `ss` of $k = 2^m$
Ritz values: the promising Ritz value $r$ of `NLAlib.findRitz`, then the square grid of spacing
`NLAlib.exceptionalSpacing` $(\rho = (1 - \gamma)^2)$ on the disk of radius
`NLAlib.exceptionalRadius` about $r$. [BanksGarzaVargasSrivastava2021, §4.2], lines 1–4 of
$\mathrm{Sh}_{k,B}$ there. -/
noncomputable def shqrCandidates (B θ α γ : ℝ) (m : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) : List ℂ :=
  findRitz H m 1 ss ::
    squareGrid (findRitz H m 1 ss)
      (exceptionalRadius (2 ^ m) B θ α (hessenbergPotential (2 ^ m) H))
      (exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2))

open Classical in
/-- The **shift chosen by $\mathrm{Sh}_{k,B}$**, $k = 2^m$: a Ritz value in `ss` that is an
eigenvalue of $\mathbf{H}$ if there is one; otherwise a success among `NLAlib.shqrCandidates`
(the promising Ritz value $r$ or an exceptional shift) if there is one, and $r$ if none succeeds
(which the convergence theorem excludes). Which eigenvalue or success is taken is a classical
choice; no statement depends on it (the paper tries the candidates in order and stops at the
first success). The first clause covers the case the paper sets aside, where the shift
polynomial is singular. [BanksGarzaVargasSrivastava2021, §4.2]. -/
noncomputable def shqrShift (B θ α γ : ℝ) (m : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) : ℂ :=
  if h : ∃ r ∈ ss, (H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0 then h.choose
  else if h' : ∃ s ∈ shqrCandidates B θ α γ m H ss, IsShiftSuccess γ (2 ^ m) H s then h'.choose
  else findRitz H m 1 ss

/-- One **iteration of $\mathrm{Sh}_{k,B}$**, $k = 2^m$: the degree $k$ QR step with shift
polynomial $(z - s)^k$, $s$ the shift `NLAlib.shqrShift`.
[BanksGarzaVargasSrivastava2021, §4.2].
Algorithm: shifted-qr (specification) -/
noncomputable def shqrStep (B θ α γ : ℝ) (m : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  multiShiftedQRStep H (List.replicate (2 ^ m) (shqrShift B θ α γ m H ss))

/-- The **shifted QR iteration with strategy $\mathrm{Sh}_{k,B}$**: $\mathbf{H}_0$ given and
$\mathbf{H}_{t+1}$ the iteration `NLAlib.shqrStep` at $\mathbf{H}_t$ with the Ritz values
`ritz` $\mathbf{H}_t$ of an oracle (exact Ritz values, or any $\theta$-optimal ones).
[BanksGarzaVargasSrivastava2021, Theorem 1.6].
Algorithm: shifted-qr (specification) -/
noncomputable def shqrIterate (B θ α γ : ℝ) (m : ℕ)
    (ritz : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ)
    (H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  | 0 => H₀
  | t + 1 => shqrStep B θ α γ m (shqrIterate B θ α γ m ritz H₀ t)
      (ritz (shqrIterate B θ α γ m ritz H₀ t))

/-! ### Stagnation implies support -/

/-- A weighted Paley–Zygmund bound, with the second moment and the event bound supplied. -/
private theorem paley_zygmund_chain {κ M E F G Wsub W t : ℝ} (hsq1 : 1 ≤ (κ * M * E) ^ 2)
    (hPZ : (1 - t) ^ 2 * E ^ 2 ≤ F * Wsub) (hFG : F * G ^ 2 ≤ κ ^ 2) (hWsub : Wsub ≤ W)
    (hWsub0 : 0 ≤ Wsub) : (1 - t) ^ 2 * G ^ 2 ≤ κ ^ 4 * M ^ 2 * W := by
  calc (1 - t) ^ 2 * G ^ 2 ≤ (1 - t) ^ 2 * G ^ 2 * (κ * M * E) ^ 2 :=
        le_mul_of_one_le_right (by positivity) hsq1
    _ = (κ ^ 2 * M ^ 2 * G ^ 2) * ((1 - t) ^ 2 * E ^ 2) := by ring
    _ ≤ (κ ^ 2 * M ^ 2 * G ^ 2) * (F * Wsub) := mul_le_mul_of_nonneg_left hPZ (by positivity)
    _ = (κ ^ 2 * M ^ 2) * (F * G ^ 2) * Wsub := by ring
    _ ≤ (κ ^ 2 * M ^ 2) * κ ^ 2 * Wsub :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFG (by positivity)) hWsub0
    _ ≤ (κ ^ 2 * M ^ 2) * κ ^ 2 * W := mul_le_mul_of_nonneg_left hWsub (by positivity)
    _ = κ ^ 4 * M ^ 2 * W := by ring

/-- An event $tE < 1/a^k$ for a moment $E$ with $1 \le \kappa(\alpha\theta\psi)^kE$ lies in the
disk of radius $\alpha\theta(\kappa/t)^{1/k}\psi$: $a \le \alpha\theta(\kappa/t)^{1/k}\psi$. -/
private theorem le_radius_of_lt_inv_pow {a E t κ α θ ψ : ℝ} {k : ℕ} (hk : 0 < k) (ha : 0 < a)
    (ht0 : 0 < t) (hκ0 : 0 ≤ κ) (hα : 0 ≤ α) (hθ : 0 ≤ θ) (hψ : 0 ≤ ψ)
    (hone : 1 ≤ κ * (α * θ * ψ) ^ k * E) (hi : t * E < 1 / a ^ k) :
    a ≤ α * θ * (κ / t) ^ ((k : ℝ)⁻¹) * ψ := by
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hM0 : 0 ≤ (α * θ * ψ) ^ k := pow_nonneg (mul_nonneg (mul_nonneg hα hθ) hψ) _
  have hκM : 0 < κ * (α * θ * ψ) ^ k := by
    rcases (mul_nonneg hκ0 hM0).eq_or_lt with h | h
    · rw [← h, zero_mul] at hone; linarith
    · exact h
  have h1 : t < κ * (α * θ * ψ) ^ k * (1 / a ^ k) := by
    have h2 : t ≤ t * (κ * (α * θ * ψ) ^ k * E) := le_mul_of_one_le_right ht0.le hone
    have h3 : t * (κ * (α * θ * ψ) ^ k * E) = κ * (α * θ * ψ) ^ k * (t * E) := by ring
    have h4 : κ * (α * θ * ψ) ^ k * (t * E) < κ * (α * θ * ψ) ^ k * (1 / a ^ k) :=
      mul_lt_mul_of_pos_left hi hκM
    linarith
  have hak : 0 < a ^ k := pow_pos ha k
  have h6 : t * a ^ k < κ * (α * θ * ψ) ^ k := by
    have h7 := mul_lt_mul_of_pos_right h1 hak
    have h8 : κ * (α * θ * ψ) ^ k * (1 / a ^ k) * a ^ k = κ * (α * θ * ψ) ^ k := by
      field_simp
    linarith
  have h5 : a ^ k ≤ (α * θ * ψ) ^ k * (κ / t) := by
    have h8 : a ^ k < κ * (α * θ * ψ) ^ k / t := (lt_div_iff₀ ht0).mpr (by rw [mul_comm]; exact h6)
    rw [show (α * θ * ψ) ^ k * (κ / t) = κ * (α * θ * ψ) ^ k / t by ring]
    exact h8.le
  have hR0 : 0 ≤ α * θ * (κ / t) ^ ((k : ℝ)⁻¹) * ψ :=
    mul_nonneg (mul_nonneg (mul_nonneg hα hθ) (Real.rpow_nonneg (div_nonneg hκ0 ht0.le) _)) hψ
  have hpowR : (α * θ * (κ / t) ^ ((k : ℝ)⁻¹) * ψ) ^ k = (α * θ * ψ) ^ k * (κ / t) := by
    have hc : ((κ / t) ^ ((k : ℝ)⁻¹)) ^ k = κ / t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hκ0 ht0.le), inv_mul_cancel₀ hkR,
        Real.rpow_one]
    rw [show α * θ * (κ / t) ^ ((k : ℝ)⁻¹) * ψ = (α * θ * ψ) * (κ / t) ^ ((k : ℝ)⁻¹) by ring,
      mul_pow, hc]
  rw [← pow_le_pow_iff_left₀ ha.le hR0 hk.ne', hpowR]
  exact h5

/-- **Stagnation implies support**: let $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(
\mathbf{d})$ with $\mathbf{V}$ invertible, $\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$ and
last-row weights $w$; let the $k$ shifts `ss` be $\theta$-optimal Ritz values of $\mathbf{H}$,
none an eigenvalue, $r$ an $\alpha$-promising member, $\alpha, \theta \ge 0$, and
$\psi = \psi_k(\mathbf{H}) > 0$. If the shift $(z - r)^k$ stagnates with ratio $\xi > 0$,
$\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|\,(\xi\psi)^k \le 1$ (that is
$\tau_{(z-r)^k}(\mathbf{H}) \ge \xi\psi$), then for $0 < t < 1$
$$(1 - t)^2\xi^{2k} \le \kappa^4(\alpha\theta)^{2k}\sum_{i\,:\,\lvert\mathbf{d}_i - r\rvert \le
\alpha\theta(\kappa/t)^{1/k}\psi} w_i\,.$$
[BanksGarzaVargasSrivastava2021, Lemma 4.6], with the weaker stagnation hypothesis of
[BanksGarzaVargasSrivastava2022, (2.2)] in place of $\psi_k(\widehat{\mathbf{H}}) \ge
(1 - \gamma)\psi$ (which implies it by
`NLAlib.IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_pow_mul_le`). -/
theorem IsOptimalRitzValues.sq_mul_pow_le_mul_sum_lastRowWeights_filter {θ α ξ t : ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {ss : List ℂ} {r : ℂ}
    (hss : IsOptimalRitzValues θ H ss) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hd : ∀ i, ∀ s ∈ ss, d i ≠ s) (hr : IsPromisingRitzValue α V d ss r) (hα : 0 ≤ α)
    (hθ : 0 ≤ θ) (hξ : 0 < ξ) (ht0 : 0 < t) (ht1 : t < 1)
    (hψ : 0 < hessenbergPotential ss.length H)
    (hstag : ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^
        ss.length) (Fin.last n))‖ * (ξ * hessenbergPotential ss.length H) ^ ss.length ≤ 1) :
    (1 - t) ^ 2 * ξ ^ (2 * ss.length) ≤
      pseudoConditionNumber V ^ 4 * (α * θ) ^ (2 * ss.length) *
        ∑ i ∈ Finset.univ.filter (fun i => ‖d i - r‖ ≤ α * θ *
          (pseudoConditionNumber V / t) ^ ((ss.length : ℝ)⁻¹) *
            hessenbergPotential ss.length H), lastRowWeights V i := by
  set k := ss.length
  set κ := pseudoConditionNumber V
  set ψ := hessenbergPotential k H
  have hkpos : 0 < k := List.length_pos_of_mem hr.1
  have hκ0 : 0 ≤ κ := pseudoConditionNumber_nonneg V
  have hdr : ∀ i, d i ≠ r := fun i => hd i r hr.1
  set N := ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k)
    (Fin.last n))‖
  have hN0 : 0 ≤ N := norm_nonneg _
  set x : Fin (n + 1) → ℝ := fun i => 1 / ‖d i - r‖ ^ k with hxdef
  have hx0 : ∀ i, 0 ≤ x i := fun i => by simp only [hxdef]; positivity
  have hS : ∑ i, lastRowWeights V i / ‖d i - r‖ ^ k = ∑ i, lastRowWeights V i * x i :=
    Finset.sum_congr rfl fun i _ => by simp only [hxdef]; ring
  have hFN : ∑ i, lastRowWeights V i * (x i) ^ 2 ≤ κ ^ 2 * N ^ 2 :=
    le_of_eq_of_le (Finset.sum_congr rfl fun i _ => by
      simp only [hxdef, div_pow, one_pow, ← pow_mul, mul_comm k 2, mul_one_div])
      (sum_lastRowWeights_div_pow_two_mul_le hV hHV hdr k)
  set F := ∑ i, lastRowWeights V i * (x i) ^ 2 with hFdef
  have hone := IsOptimalRitzValues.one_le_mul_sum_lastRowWeights_div hss hV hHV hd hr hθ
  rw [hS] at hone
  set E := ∑ i, lastRowWeights V i * x i with hEdef
  set M := (α * θ * ψ) ^ k with hMdef
  have hM0 : 0 ≤ M := pow_nonneg (mul_nonneg (mul_nonneg hα hθ) hψ.le) _
  have hκM : 0 < κ * M := by
    refine lt_of_le_of_ne (mul_nonneg hκ0 hM0) fun h0 => ?_
    rw [← h0, zero_mul] at hone; norm_num at hone
  have hE : 0 < E := by
    by_contra! h; nlinarith [hone, hκM]
  have hsub : Finset.univ.filter (fun i => t * E < x i) ⊆
      Finset.univ.filter (fun i => ‖d i - r‖ ≤ α * θ * (κ / t) ^ ((k : ℝ)⁻¹) * ψ) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_radius_of_lt_inv_pow hkpos (norm_pos_iff.mpr (sub_ne_zero.mpr (hdr i))) ht0
      hκ0 hα hθ hψ.le hone hi
  have hWsub : ∑ i ∈ Finset.univ.filter (fun i => t * E < x i), lastRowWeights V i ≤
      ∑ i ∈ Finset.univ.filter (fun i => ‖d i - r‖ ≤ α * θ * (κ / t) ^ ((k : ℝ)⁻¹) * ψ),
        lastRowWeights V i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => lastRowWeights_nonneg V i)
  have hWsub0 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => t * E < x i), lastRowWeights V i :=
    Finset.sum_nonneg fun i _ => lastRowWeights_nonneg V i
  have hPZ : (1 - t) ^ 2 * E ^ 2 ≤ F * ∑ i ∈ Finset.univ.filter (fun i => t * E < x i),
      lastRowWeights V i :=
    Finset.sq_mul_sq_sum_le_sum_mul_sq_mul_sum_filter Finset.univ (w := lastRowWeights V) (x := x)
      (fun i _ => lastRowWeights_nonneg V i) (sum_lastRowWeights hV) (fun i _ => hx0 i)
      ht0.le ht1.le
  have hFG : F * ((ξ * ψ) ^ k) ^ 2 ≤ κ ^ 2 := by
    have hNG : (N * (ξ * ψ) ^ k) ^ 2 ≤ 1 :=
      pow_le_one₀ (mul_nonneg hN0 (pow_nonneg (mul_nonneg hξ.le hψ.le) _)) hstag
    calc F * ((ξ * ψ) ^ k) ^ 2 ≤ κ ^ 2 * N ^ 2 * ((ξ * ψ) ^ k) ^ 2 :=
          mul_le_mul_of_nonneg_right hFN (sq_nonneg _)
      _ = κ ^ 2 * (N * (ξ * ψ) ^ k) ^ 2 := by ring
      _ ≤ κ ^ 2 * 1 := mul_le_mul_of_nonneg_left hNG (sq_nonneg _)
      _ = κ ^ 2 := mul_one _
  have hmain := paley_zygmund_chain (one_le_pow₀ hone) hPZ hFG hWsub hWsub0
  rw [hMdef] at hmain
  refine le_of_mul_le_mul_right ?_ (pow_pos hψ (2 * k))
  linear_combination hmain

/-! ### The grid of exceptional shifts -/

/-- The square grid covers the disk: for $R \ge 0$, $\varepsilon > 0$ and
$\lvert z - c\rvert \le R$, some point $s$ of `NLAlib.squareGrid` $c$ $R$ $\varepsilon$ has
$\lvert z - s\rvert \le \varepsilon R$. -/
theorem exists_mem_squareGrid_norm_sub_le {c z : ℂ} {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hz : ‖z - c‖ ≤ R) : ∃ s ∈ squareGrid c R ε, ‖z - s‖ ≤ ε * R := by
  rcases hR.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨c, ?_, by simpa using hz⟩
    unfold squareGrid
    simp only [List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨0, Nat.succ_pos _, 0, Nat.succ_pos _, by simp⟩
  set m : ℕ := ⌈Real.sqrt 2 / ε⌉₊ with hm_def
  have hs0 : 0 < Real.sqrt 2 / ε := by positivity
  have hmR : Real.sqrt 2 / ε ≤ (m : ℝ) := Nat.le_ceil _
  have hm_pos : (0 : ℝ) < m := lt_of_lt_of_le hs0 hmR
  have hsε : Real.sqrt 2 ≤ (m : ℝ) * ε := by rwa [div_le_iff₀ hε] at hmR
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- rounding one coordinate of a point of the disk to the grid
  have hround : ∀ x : ℝ, -1 ≤ x → x ≤ 1 →
      ∃ i : ℕ, i < m + 1 ∧ |2 * (i : ℝ) / m - 1 - x| ≤ 1 / m := by
    intro x hx1 hx2
    have hnn : 0 ≤ (x + 1) * m / 2 + 1 / 2 := by nlinarith
    have h1 := Nat.floor_le hnn
    have h2 := Nat.lt_floor_add_one ((x + 1) * m / 2 + 1 / 2)
    refine ⟨⌊(x + 1) * m / 2 + 1 / 2⌋₊, ?_, ?_⟩
    · have h3 : ((⌊(x + 1) * m / 2 + 1 / 2⌋₊ : ℕ) : ℝ) < m + 1 := by nlinarith
      exact_mod_cast h3
    · set i : ℝ := (⌊(x + 1) * m / 2 + 1 / 2⌋₊ : ℝ)
      have e : 2 * i / m - 1 - x = (2 * i - (x + 1) * m) / m := by field_simp; ring
      rw [e, abs_div, abs_of_pos hm_pos, div_le_div_iff_of_pos_right hm_pos, abs_le]
      constructor <;> linarith
  -- the normalised point and its coordinates lie in the square
  set w : ℂ := (z - c) / R with hw_def
  have hwn : ‖w‖ ≤ 1 := by
    rw [hw_def, norm_div, Complex.norm_real, Real.norm_of_nonneg hR, div_le_one hpos]
    exact hz
  have hwre := abs_le.mp ((Complex.abs_re_le_norm w).trans hwn)
  have hwim := abs_le.mp ((Complex.abs_im_le_norm w).trans hwn)
  obtain ⟨i, hi, hia⟩ := hround w.re hwre.1 hwre.2
  obtain ⟨j, hj, hjb⟩ := hround w.im hwim.1 hwim.2
  refine ⟨c + (R : ℂ) * ⟨2 * (i : ℝ) / m - 1, 2 * (j : ℝ) / m - 1⟩, ?_, ?_⟩
  · unfold squareGrid
    simp only [List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨i, hi, j, hj, rfl⟩
  have hdiff : z - (c + (R : ℂ) * ⟨2 * (i : ℝ) / m - 1, 2 * (j : ℝ) / m - 1⟩) =
      (R : ℂ) * (w - ⟨2 * (i : ℝ) / m - 1, 2 * (j : ℝ) / m - 1⟩) := by
    rw [hw_def]; field_simp; ring
  have hu : ‖w - ⟨2 * (i : ℝ) / m - 1, 2 * (j : ℝ) / m - 1⟩‖ ≤ Real.sqrt 2 * (1 / m) := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    have hA := abs_le.mp hia
    have hB := abs_le.mp hjb
    have ha2 : (w.re - (2 * (i : ℝ) / m - 1)) ^ 2 ≤ (1 / (m : ℝ)) ^ 2 :=
      sq_le_sq' (by linarith [hA.1, hA.2]) (by linarith [hA.1, hA.2])
    have hb2 : (w.im - (2 * (j : ℝ) / m - 1)) ^ 2 ≤ (1 / (m : ℝ)) ^ 2 :=
      sq_le_sq' (by linarith [hB.1, hB.2]) (by linarith [hB.1, hB.2])
    have hR2 : (Real.sqrt 2 * (1 / m)) ^ 2 = 2 * (1 / m) ^ 2 := by rw [mul_pow, hsq]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith [ha2, hb2, hR2]
  have hεm : Real.sqrt 2 * (1 / m) ≤ ε := by
    rw [mul_one_div, div_le_iff₀ hm_pos]; linarith
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR]
  nlinarith [mul_le_mul_of_nonneg_left hu hR, mul_le_mul_of_nonneg_left hεm hR]

/-- The size of the square grid: for $0 < \varepsilon \le 1$, `NLAlib.squareGrid` $c$ $R$
$\varepsilon$ has at most $12/\varepsilon^2$ points. -/
theorem length_squareGrid_le (c : ℂ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((squareGrid c R ε).length : ℝ) ≤ 12 / ε ^ 2 := by
  have hlen :
      (squareGrid c R ε).length = (⌈Real.sqrt 2 / ε⌉₊ + 1) * (⌈Real.sqrt 2 / ε⌉₊ + 1) := by
    simp [squareGrid, List.length_flatMap, List.length_map, List.length_range]
  rw [hlen]
  push_cast
  have hs0 : 0 ≤ Real.sqrt 2 / ε := by positivity
  have hmlt : (⌈Real.sqrt 2 / ε⌉₊ : ℝ) < Real.sqrt 2 / ε + 1 := Nat.ceil_lt_add_one hs0
  have hmε : (⌈Real.sqrt 2 / ε⌉₊ : ℝ) * ε < Real.sqrt 2 + ε := by
    have := mul_lt_mul_of_pos_right hmlt hε
    rwa [add_mul, div_mul_cancel₀ _ hε.ne', one_mul] at this
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs15 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hu : ((⌈Real.sqrt 2 / ε⌉₊ : ℝ) + 1) * ε ≤ Real.sqrt 2 + 2 * ε := by linarith
  have hu0 : 0 ≤ ((⌈Real.sqrt 2 / ε⌉₊ : ℝ) + 1) * ε := by positivity
  have hsq2 := pow_le_pow_left₀ hu0 hu 2
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hε1 (Real.sqrt_nonneg 2),
    mul_le_mul_of_nonneg_left hε1 hε.le]

/-- The grid stays near its centre: every point $s$ of `NLAlib.squareGrid` $c$ $R$
$\varepsilon$, $R \ge 0$, $\varepsilon > 0$, has $\lvert s - c\rvert \le \sqrt2R$. -/
theorem norm_sub_le_of_mem_squareGrid {c s : ℂ} {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hs : s ∈ squareGrid c R ε) : ‖s - c‖ ≤ Real.sqrt 2 * R := by
  have hbd : ∀ i : ℕ, i < ⌈Real.sqrt 2 / ε⌉₊ + 1 →
      -1 ≤ 2 * (i : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) - 1 ∧
        2 * (i : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) - 1 ≤ 1 := by
    intro i hi
    rcases Nat.eq_zero_or_pos ⌈Real.sqrt 2 / ε⌉₊ with h0 | hpos
    · have : i = 0 := by omega
      subst this
      simp [h0]
    · have hm : (0 : ℝ) < (⌈Real.sqrt 2 / ε⌉₊ : ℝ) := by exact_mod_cast hpos
      have hi' : (i : ℝ) ≤ (⌈Real.sqrt 2 / ε⌉₊ : ℝ) := by exact_mod_cast (by omega : i ≤ _)
      have h0' : 0 ≤ 2 * (i : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) := by positivity
      have h1' : 2 * (i : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hm]; linarith
      constructor <;> linarith
  unfold squareGrid at hs
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hs
  obtain ⟨i, hi, j, hj, rfl⟩ := hs
  obtain ⟨ha1, ha2⟩ := hbd i hi
  obtain ⟨hb1, hb2⟩ := hbd j hj
  have hnorm : ‖(⟨2 * (i : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) - 1,
      2 * (j : ℝ) / (⌈Real.sqrt 2 / ε⌉₊ : ℝ) - 1⟩ : ℂ)‖ ≤ Real.sqrt 2 := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [Complex.sq_norm, Complex.normSq_mk]
    nlinarith
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR]
  nlinarith [mul_le_mul_of_nonneg_left hnorm hR]

/-- Averaging over a finite set $G$ of shifts covering the eigenvalues indexed by $S$ within
$\rho$: some $s \in G$ has
$\sum_{i \in S} w_i/\rho^k \le \lvert G\rvert\sum_i w_i/\lvert\mathbf{d}_i - s\rvert^k$. -/
theorem exists_mem_sum_div_pow_le_card_mul_sum {G : Finset ℂ}
    {S : Finset (Fin (n + 1))} {w : Fin (n + 1) → ℝ} {d : Fin (n + 1) → ℂ} {ρ : ℝ} {k : ℕ}
    (hw : ∀ i, 0 ≤ w i) (hG : G.Nonempty) (hd : ∀ i, ∀ s ∈ G, d i ≠ s)
    (hcov : ∀ i ∈ S, ∃ s ∈ G, ‖d i - s‖ ≤ ρ) :
    ∃ s ∈ G, (∑ i ∈ S, w i) / ρ ^ k ≤ G.card * ∑ i, w i / ‖d i - s‖ ^ k := by
  have h1 : (∑ i ∈ S, w i) / ρ ^ k ≤ ∑ s ∈ G, ∑ i, w i / ‖d i - s‖ ^ k := by
    rw [Finset.sum_div, Finset.sum_comm]
    calc ∑ i ∈ S, w i / ρ ^ k ≤ ∑ i ∈ S, ∑ s ∈ G, w i / ‖d i - s‖ ^ k :=
          Finset.sum_le_sum fun i hi => by
            obtain ⟨s, hs, hle⟩ := hcov i hi
            calc w i / ρ ^ k ≤ w i / ‖d i - s‖ ^ k :=
                  div_le_div_of_nonneg_left (hw i)
                    (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hd i s hs))) _)
                    (pow_le_pow_left₀ (norm_nonneg _) hle _)
              _ ≤ _ := Finset.single_le_sum (f := fun s => w i / ‖d i - s‖ ^ k)
                  (fun s _ => div_nonneg (hw i) (by positivity)) hs
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun i _ _ => Finset.sum_nonneg fun s _ => div_nonneg (hw i) (by positivity)
  have hc : (0 : ℝ) < G.card := Nat.cast_pos.mpr hG.card_pos
  obtain ⟨s, hs, hle⟩ := Finset.exists_le_of_sum_le hG
    (f := fun _ => (∑ i ∈ S, w i) / ρ ^ k / G.card)
    (g := fun s => ∑ i, w i / ‖d i - s‖ ^ k) (by
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hc.ne']
      exact h1)
  exact ⟨s, hs, (div_le_iff₀' hc).mp hle⟩

/-- The exceptional spacing $\varepsilon$ lies in $(0, 1]$ and satisfies
$\varepsilon^{2k} = \varepsilon^2\bigl((\xi(1-\gamma))^k/(14B^4(\alpha\theta)^{2k})\bigr)^2$. -/
private theorem exceptionalSpacing_pos_and_le_one_and_pow {k : ℕ} {B θ α γ ξ : ℝ}
    (hk : 2 ≤ k) (hB1 : 1 ≤ B) (hθ : 1 ≤ θ) (hα : 1 ≤ α) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1) :
    0 < exceptionalSpacing k B θ α (ξ * (1 - γ)) ∧ exceptionalSpacing k B θ α (ξ * (1 - γ)) ≤ 1 ∧
      exceptionalSpacing k B θ α (ξ * (1 - γ)) ^ (2 * k) =
        exceptionalSpacing k B θ α (ξ * (1 - γ)) ^ 2 *
          ((ξ * (1 - γ)) ^ k / (14 * B ^ 4 * (α * θ) ^ (2 * k))) ^ 2 := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hc : ((14 * B ^ 4) ^ ((k : ℝ)⁻¹)) ^ k = 14 * B ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), inv_mul_cancel₀ hk0.ne',
      Real.rpow_one]
  set b := ξ * (1 - γ) / ((14 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2) with hb_def
  have hγ' : 0 < 1 - γ := by linarith
  have hb0 : 0 < b := by positivity
  have hb1 : b ≤ 1 := by
    rw [hb_def, div_le_one (by positivity)]
    have : 1 ≤ (14 * B ^ 4) ^ ((k : ℝ)⁻¹) :=
      Real.one_le_rpow (by nlinarith [one_le_pow₀ (n := 4) hB1]) (by positivity)
    calc ξ * (1 - γ) ≤ 1 * 1 * 1 := by nlinarith
      _ ≤ _ := by gcongr <;> nlinarith
  have hεk : exceptionalSpacing k B θ α (ξ * (1 - γ)) ^ (k - 1) = b ^ k := by
    rw [exceptionalSpacing, ← hb_def, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le,
      Nat.cast_sub (by omega), Nat.cast_one, div_mul_cancel₀ _ (by linarith), Real.rpow_natCast]
  refine ⟨Real.rpow_pos_of_pos hb0 _, Real.rpow_le_one hb0.le hb1 (div_nonneg hk0.le
    (by linarith)), ?_⟩
  have hbk : b ^ k = (ξ * (1 - γ)) ^ k / (14 * B ^ 4 * (α * θ) ^ (2 * k)) := by
    simp only [hb_def, div_pow, mul_pow, hc]
    ring
  rw [← hbk, ← hεk, ← pow_mul, ← pow_add]
  congr 1
  omega

/-- The arithmetic of the averaging step of the exceptional shifts: the weight bound, the
averaging over at most $12/\varepsilon^2$ grid points and the moment bound at the chosen
point give $1 \le ((1 - \gamma)\psi)^k x$. -/
private theorem one_le_pow_mul_of_le_card_mul_sum {k : ℕ} {B θ α ξ γ ψ ε x P N f : ℝ}
    (hk : 0 < k) (hB : 0 < B) (hθ : 0 < θ) (hα : 0 < α) (hξ : 0 < ξ) (hγ1 : γ < 1)
    (hψ : 0 < ψ) (hx : 0 ≤ x) (hε0 : 0 < ε)
    (hε : ε ^ (2 * k) = ε ^ 2 * ((ξ * (1 - γ)) ^ k / (14 * B ^ 4 * (α * θ) ^ (2 * k))) ^ 2)
    (hP : (1 / 2) ^ 2 * ξ ^ (2 * k) ≤ B ^ 4 * (α * θ) ^ (2 * k) * P)
    (hsle : P / (ε * exceptionalRadius k B θ α ψ) ^ (2 * k) ≤ N * f) (hN : N ≤ 12 / ε ^ 2)
    (hf0 : 0 ≤ f) (hf : f ≤ B ^ 2 * x ^ 2) :
    1 ≤ ((1 - γ) * ψ) ^ k * x := by
  set R := exceptionalRadius k B θ α ψ with hR_def
  have hR0 : 0 < R := by rw [hR_def, exceptionalRadius]; positivity
  have h1 : P ≤ (12 / ε ^ 2) * (B ^ 2 * x ^ 2) * (ε * R) ^ (2 * k) := by
    calc P ≤ _ := (div_le_iff₀ (by positivity)).mp hsle
      _ ≤ _ := by gcongr
  have hRk : R ^ k = 2 * B * (θ * α * ψ) ^ k := by
    rw [hR_def, exceptionalRadius, mul_pow, mul_pow, mul_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), inv_mul_cancel₀ (by exact_mod_cast hk.ne'), Real.rpow_one]
    ring
  have h2 : ξ ^ (2 * k) ≤ 48 / 49 * ξ ^ (2 * k) * (((1 - γ) * ψ) ^ k * x) ^ 2 := by
    calc ξ ^ (2 * k) ≤ 4 * (B ^ 4 * (α * θ) ^ (2 * k) * P) := by linarith
      _ ≤ 4 * (B ^ 4 * (α * θ) ^ (2 * k) *
          ((12 / ε ^ 2) * (B ^ 2 * x ^ 2) * (ε * R) ^ (2 * k))) := by gcongr
      _ = _ := by
          rw [mul_pow ε R, hε, mul_comm 2 k, pow_mul R, hRk]
          simp only [mul_pow]
          field_simp
          ring
  have hy : 0 ≤ ((1 - γ) * ψ) ^ k * x := mul_nonneg (pow_nonneg (by nlinarith) _) hx
  have h3 : 1 ≤ 48 / 49 * (((1 - γ) * ψ) ^ k * x) ^ 2 :=
    le_of_mul_le_mul_left (by rw [mul_one, ← mul_assoc, mul_comm _ (48 / 49)]; exact h2)
      (by positivity : 0 < ξ ^ (2 * k))
  by_contra h
  have := pow_lt_one₀ hy (not_le.mp h) two_ne_zero
  linarith

/-- **An exceptional shift succeeds**: let $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(
\mathbf{d})$ with $\mathbf{V}$ invertible and $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$; let
the $k \ge 2$ shifts `ss` be $\theta$-optimal Ritz values of $\mathbf{H}$, $\theta \ge 1$, none
an eigenvalue, $r$ an $\alpha$-promising member, $\alpha \ge 1$, $0 < \gamma < 1$,
$0 < \xi \le 1$, $\psi = \psi_k(\mathbf{H}) > 0$, and let $(z - r)^k$ stagnate with ratio $\xi$:
$\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|\,(\xi\psi)^k \le 1$. Then some point
$s$ of the grid of spacing $\varepsilon = \bigl(\xi(1 - \gamma)/((14B^4)^{1/k}\alpha^2\theta^2)
\bigr)^{k/(k-1)}$ on the disk of radius $(2B)^{1/k}\theta\alpha\psi$ about $r$ is an eigenvalue
or has
$$1 \le ((1 - \gamma)\psi)^k\,\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - s\mathbf{I})^{-k}\|\,,$$
so that $\tau_{(z-s)^k}(\mathbf{H}) \le (1 - \gamma)\psi$.
[BanksGarzaVargasSrivastava2021, Lemma 4.7] (Exc), there with $\xi = 1 - \gamma$, constant
$12$ and a maximal net; the grid has up to $12/\varepsilon^2$ points, whence $14 \ge \sqrt{192}$. -/
theorem IsOptimalRitzValues.exists_mem_squareGrid_det_eq_zero_or_one_le {θ α ξ γ B : ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {ss : List ℂ} {r : ℂ}
    (hss : IsOptimalRitzValues θ H ss) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hB : pseudoConditionNumber V ≤ B) (hd : ∀ i, ∀ s ∈ ss, d i ≠ s)
    (hr : IsPromisingRitzValue α V d ss r) (hk : 2 ≤ ss.length) (hθ : 1 ≤ θ) (hα : 1 ≤ α)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hψ : 0 < hessenbergPotential ss.length H)
    (hstag : ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^
        ss.length) (Fin.last n))‖ * (ξ * hessenbergPotential ss.length H) ^ ss.length ≤ 1) :
    ∃ s ∈ squareGrid r (exceptionalRadius ss.length B θ α (hessenbergPotential ss.length H))
        (exceptionalSpacing ss.length B θ α (ξ * (1 - γ))),
      (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0 ∨
        1 ≤ ((1 - γ) * hessenbergPotential ss.length H) ^ ss.length *
          ‖WithLp.toLp 2 (((H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^
            ss.length) (Fin.last n))‖ := by
  set k := ss.length with hk_def
  set ψ := hessenbergPotential k H with hψ_def
  set R := exceptionalRadius k B θ α ψ with hR_def
  set ε := exceptionalSpacing k B θ α (ξ * (1 - γ)) with hε_def
  by_cases hG : ∃ s ∈ squareGrid r R ε,
      (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0
  · obtain ⟨s, hs, h⟩ := hG
    exact ⟨s, hs, Or.inl h⟩
  have hdG : ∀ i, ∀ s ∈ squareGrid r R ε, d i ≠ s := by
    rintro i s hs rfl
    exact hG ⟨d i, hs, det_sub_smul_one_eq_zero_of_mul_eq_mul_diagonal hV hHV i⟩
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hB
  obtain ⟨hε0, hε1, hε2k⟩ := exceptionalSpacing_pos_and_le_one_and_pow hk hB1 hθ hα hγ0 hγ1 hξ0 hξ1
  have hR0 : 0 < R := by rw [hR_def, exceptionalRadius]; positivity
  -- weight on the disk
  set S := Finset.univ.filter (fun i => ‖d i - r‖ ≤ R) with hS_def
  have hP : (1 / 2) ^ 2 * ξ ^ (2 * k) ≤
      B ^ 4 * (α * θ) ^ (2 * k) * ∑ i ∈ S, lastRowWeights V i := by
    have h := hss.sq_mul_pow_le_mul_sum_lastRowWeights_filter hV hHV hd hr (by linarith)
      (by linarith) hξ0 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hψ hstag
    norm_num only at h ⊢
    refine h.trans ?_
    gcongr ?_ * _ * ?_
    · exact Finset.sum_nonneg fun i _ => lastRowWeights_nonneg V i
    · exact pow_le_pow_left₀ (pseudoConditionNumber_nonneg V) hB 4
    · refine Finset.sum_le_sum_of_subset_of_nonneg (fun i => ?_)
        fun i _ _ => lastRowWeights_nonneg V i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS_def]
      intro hi
      refine hi.trans ?_
      rw [hR_def, exceptionalRadius, show α * θ * (pseudoConditionNumber V / (1 / 2)) ^
        (k : ℝ)⁻¹ * ψ = (2 * pseudoConditionNumber V) ^ (k : ℝ)⁻¹ * θ * α * ψ by ring_nf]
      gcongr
  -- average over the grid
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, mul_zero] at hP
    have : 0 < (1 / 2 : ℝ) ^ 2 * ξ ^ (2 * k) := by positivity
    linarith
  have hcov : ∀ i ∈ S, ∃ s ∈ (squareGrid r R ε).toFinset, ‖d i - s‖ ≤ ε * R := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS_def] at hi
    obtain ⟨s, hs, h⟩ := exists_mem_squareGrid_norm_sub_le hR0.le hε0 hi
    exact ⟨s, List.mem_toFinset.mpr hs, h⟩
  obtain ⟨i₀, hi₀⟩ := hSne
  obtain ⟨s, hs, hsle⟩ := exists_mem_sum_div_pow_le_card_mul_sum (k := 2 * k)
    (lastRowWeights_nonneg V) ⟨_, (hcov i₀ hi₀).choose_spec.1⟩
    (fun i s hs => hdG i s (List.mem_toFinset.mp hs)) hcov
  rw [List.mem_toFinset] at hs
  have hN : ((squareGrid r R ε).toFinset.card : ℝ) ≤ 12 / ε ^ 2 :=
    (Nat.cast_le.mpr (List.toFinset_card_le _)).trans (length_squareGrid_le r R hε0 hε1)
  -- the moment at `s`
  refine ⟨s, hs, Or.inr ?_⟩
  set x := ‖WithLp.toLp 2 (((H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k)
    (Fin.last n))‖ with hx_def
  set P := ∑ i ∈ S, lastRowWeights V i with hP_def
  have hf0 : 0 ≤ ∑ i, lastRowWeights V i / ‖d i - s‖ ^ (2 * k) :=
    Finset.sum_nonneg fun i _ => div_nonneg (lastRowWeights_nonneg V i) (by positivity)
  have hf : ∑ i, lastRowWeights V i / ‖d i - s‖ ^ (2 * k) ≤ B ^ 2 * x ^ 2 :=
    (sum_lastRowWeights_div_pow_two_mul_le hV hHV (fun i => hdG i s hs) k).trans (by gcongr)
  exact one_le_pow_mul_of_le_card_mul_sum (by omega) (by positivity) (by positivity)
    (by positivity) hξ0 hγ1 hψ (norm_nonneg _) hε0 hε2k hP hsle hN hf0 hf

/-! ### One iteration and the decoupling theorem -/

/-- **One iteration of $\mathrm{Sh}_{k,B}$ decouples or reduces the potential**: let
$\mathbf{H}$ be upper Hessenberg with $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(
\mathbf{d})$, $\mathbf{V}$ invertible and $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$; let
$k = 2^m$ with $m \ge 1$ and $k \le n$, `ss` a list of $k$ $\theta$-optimal Ritz values,
$\theta \ge 1$, $\alpha \ge 1$ with $B^{4m} \le \alpha^k$, and $0 < \gamma < 1$. Then
$\widehat{\mathbf{H}} = \mathsf{shqrStep}(\mathbf{H}, \mathrm{ss})$ has a zero subdiagonal entry
or $\psi_k(\widehat{\mathbf{H}}) \le (1 - \gamma)\psi_k(\mathbf{H})$.
[BanksGarzaVargasSrivastava2021, Theorem 1.6, proof of rapid convergence], with the singular
cases made explicit. -/
theorem IsUpperHessenberg.isDecoupled_zero_shqrStep_or_hessenbergPotential_le
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {d : Fin (n + 1) → ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {B θ α γ : ℝ}
    (hB : pseudoConditionNumber V ≤ B) {m : ℕ} (hm : 1 ≤ m) (hmn : 2 ^ m ≤ n) {ss : List ℂ}
    (hlen : ss.length = 2 ^ m) (hss : IsOptimalRitzValues θ H ss) (hθ : 1 ≤ θ) (hα1 : 1 ≤ α)
    (hα : B ^ (4 * m) ≤ α ^ 2 ^ m) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsDecoupled 0 (shqrStep B θ α γ m H ss) ∨
      hessenbergPotential (2 ^ m) (shqrStep B θ α γ m H ss) ≤
        (1 - γ) * hessenbergPotential (2 ^ m) H := by
  have hk0 : 0 < 2 ^ m := by positivity
  have hn : 0 < n := hk0.trans_le hmn
  change IsShiftSuccess γ (2 ^ m) H (shqrShift B θ α γ m H ss)
  by_cases hdec : IsDecoupled 0 H
  · exact Or.inl (hH.isDecoupled_zero_multiShiftedQRStep hdec _)
  have hψ : 0 < hessenbergPotential (2 ^ m) H := by
    by_contra h
    exact hdec (isDecoupled_of_hessenbergPotential_le hk0 hmn le_rfl (by simpa using not_lt.mp h))
  -- the potential after the step with shift `s` is at most `τ`
  have hτ := fun (s : ℂ) (hs : (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det ≠ 0) =>
    hH.hessenbergPotential_multiShiftedQRStep_replicate_pow_mul_le hk0 hmn hs
  have hsucc : ∀ s : ℂ, ((H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0 ∨
      1 ≤ ((1 - γ) * hessenbergPotential (2 ^ m) H) ^ (2 ^ m) *
        ‖WithLp.toLp 2 (((H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ (2 ^ m))
          (Fin.last n))‖) → IsShiftSuccess γ (2 ^ m) H s := by
    intro s hs
    by_cases hdet : (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0
    · left
      apply hH.isDecoupled_zero_multiShiftedQRStep_of_det_eq_zero hn
      rw [aeval_shiftPoly_replicate, Matrix.det_pow, hdet, zero_pow hk0.ne']
    right
    have h1 := hs.resolve_left hdet
    have hx : 0 < ‖WithLp.toLp 2 (((H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^
        (2 ^ m)) (Fin.last n))‖ :=
      (norm_nonneg _).lt_of_ne fun h => by rw [← h, mul_zero] at h1; linarith
    have h0 : 0 ≤ hessenbergPotential (2 ^ m) (multiShiftedQRStep H (List.replicate (2 ^ m) s)) :=
    hessenbergPotential_nonneg _ _
    exact (pow_le_pow_iff_left₀ h0 (mul_nonneg (by linarith) hψ.le) hk0.ne').mp
      (le_of_mul_le_mul_right ((hτ s hdet).trans h1) hx)
  by_cases hdet : ∃ r ∈ ss, (H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0
  · rw [shqrShift, dif_pos hdet]
    exact hsucc _ (Or.inl hdet.choose_spec.2)
  have hd : ∀ i, ∀ s ∈ ss, d i ≠ s := fun i s hs he =>
    hdet ⟨s, hs, he ▸ det_sub_smul_one_eq_zero_of_mul_eq_mul_diagonal hV hHV i⟩
  have hrss := findRitz_mem H (e := 1) hlen
  have hr := isPromisingRitzValue_findRitz hV hHV hlen hd
    ((pow_le_pow_left₀ (pseudoConditionNumber_nonneg V) hB _).trans hα)
  have h' : ∃ s ∈ shqrCandidates B θ α γ m H ss, IsShiftSuccess γ (2 ^ m) H s := by
    by_cases hr' : IsShiftSuccess γ (2 ^ m) H (findRitz H m 1 ss)
    · exact ⟨_, List.mem_cons_self, hr'⟩
    have hlt := lt_of_not_ge fun h => hr' (Or.inr h)
    have hdr : (H - findRitz H m 1 ss • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det ≠ 0 :=
      fun h => hdet ⟨_, hrss, h⟩
    have hstag : ‖WithLp.toLp 2 (((H - findRitz H m 1 ss •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ ss.length) (Fin.last n))‖ *
          ((1 - γ) * hessenbergPotential ss.length H) ^ ss.length ≤ 1 := by
      rw [hlen, mul_comm]
      refine le_trans ?_ (hτ _ hdr)
      gcongr
    obtain ⟨s, hs, hs'⟩ := hss.exists_mem_squareGrid_det_eq_zero_or_one_le hV hHV hB hd hr
      (by rw [hlen]; exact le_self_pow₀ one_le_two (by omega)) hθ hα1 hγ0 hγ1 (by linarith)
      (by linarith) (hlen ▸ hψ) hstag
    rw [hlen, ← sq] at hs
    rw [hlen] at hs'
    exact ⟨s, List.mem_cons_of_mem _ hs, hsucc s hs'⟩
  rw [shqrShift, dif_neg hdet, dif_pos h']
  exact h'.choose_spec.2

/-- The iterates of $\mathrm{Sh}_{k,B}$ are upper Hessenberg: if $\mathbf{H}_0$ is, so is
every `NLAlib.shqrIterate` $\mathbf{H}_t$, for every Ritz-value oracle. -/
theorem IsUpperHessenberg.isUpperHessenberg_shqrIterate {H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H₀) (B θ α γ : ℝ) (m : ℕ)
    (ritz : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ) (t : ℕ) :
    IsUpperHessenberg (shqrIterate B θ α γ m ritz H₀ t) := by
  induction t with
  | zero => exact hH
  | succ t ih => exact isUpperHessenberg_multiShiftedQRStep ih _

/-- The iterates of $\mathrm{Sh}_{k,B}$ have the norm of $\mathbf{H}_0$:
$\|\mathbf{H}_t\|_2 = \|\mathbf{H}_0\|_2$ for every $t$ and every Ritz-value oracle. -/
theorem specNorm_shqrIterate (B θ α γ : ℝ) (m : ℕ)
    (ritz : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ)
    (H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (t : ℕ) :
    specNorm (shqrIterate B θ α γ m ritz H₀ t) = specNorm H₀ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [shqrIterate, shqrStep, specNorm_multiShiftedQRStep, ih]

/-- The iterates of $\mathrm{Sh}_{k,B}$ keep the eigenvector condition number: if
$\mathbf{H}_0\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$
invertible, every $\mathbf{H}_t$ has $\mathbf{H}_t\mathbf{V}' = \mathbf{V}'\operatorname{diag}(
\mathbf{d})$ for an invertible $\mathbf{V}'$ with $\|\mathbf{V}'\|_2\|\mathbf{V}'^{-1}\|_2 =
\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$. -/
theorem exists_isUnit_mul_eq_mul_diagonal_shqrIterate
    {H₀ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H₀ * V = V * Matrix.diagonal d) (B θ α γ : ℝ) (m : ℕ)
    (ritz : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ) (t : ℕ) :
    ∃ V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsUnit V' ∧
      shqrIterate B θ α γ m ritz H₀ t * V' = V' * Matrix.diagonal d ∧
      pseudoConditionNumber V' = pseudoConditionNumber V := by
  induction t with
  | zero => exact ⟨V, hV, by simpa only [shqrIterate] using hHV, rfl⟩
  | succ t ih =>
    obtain ⟨V₁, hV₁, hHV₁, hκ₁⟩ := ih
    obtain ⟨V₂, hV₂, hHV₂, hκ₂⟩ := exists_isUnit_mul_eq_mul_diagonal_multiShiftedQRStep hV₁ hHV₁
      (List.replicate (2 ^ m) (shqrShift B θ α γ m (shqrIterate B θ α γ m ritz H₀ t)
        (ritz (shqrIterate B θ α γ m ritz H₀ t))))
    exact ⟨V₂, hV₂, by simpa only [shqrIterate, shqrStep] using hHV₂, hκ₂.trans hκ₁⟩

/-- **Rapid decoupling of the Hessenberg shifted QR algorithm** with the strategy
$\mathrm{Sh}_{k,B}$: let $\mathbf{H}_0$ be upper Hessenberg and diagonalizable,
$\mathbf{H}_0\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible
and $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$ (so $\kappa_V(\mathbf{H}_0) \le B$); let
$k = 2^m$, $m \ge 1$, $k \le n$; $\theta \ge 1$; $\alpha \ge 1$ with $B^{4m} \le \alpha^k$ (e.g.
$\alpha = B^{4\log_2 k/k}$); $0 < \gamma < 1$; and let the Ritz-value oracle return, on every
upper Hessenberg matrix with $\psi_k > 0$, $k$ $\theta$-optimal Ritz values (as
[BanksGarzaVargasSrivastava2021, Definition 1.5] requires only when the minimum is nonzero).
Then for every $\delta > 0$ some
$$t \le \Bigl\lceil\frac{\log(1/\delta)}{\log(1/(1 - \gamma))}\Bigr\rceil$$
has $\mathsf{shqrIterate}(\mathbf{H}_0)_t$ $\delta$-decoupled: a subdiagonal entry of modulus at
most $\delta\|\mathbf{H}_t\|_2$. Adapted from [BanksGarzaVargasSrivastava2021, Theorem 1.6,
item 1]; the ceiling makes the bound hold for every $\delta > 0$, and it is at most
$4\log_2(1/\delta) + 1$ at $\gamma = 0.2$.
Result: shifted-qr-rapid-decoupling -/
theorem IsUpperHessenberg.exists_le_isDecoupled_shqrIterate
    {H₀ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H₀)
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H₀ * V = V * Matrix.diagonal d)
    {B θ α γ : ℝ} (hB : pseudoConditionNumber V ≤ B) {m : ℕ} (hm : 1 ≤ m) (hmn : 2 ^ m ≤ n)
    (hθ : 1 ≤ θ) (hα1 : 1 ≤ α) (hα : B ^ (4 * m) ≤ α ^ 2 ^ m) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {ritz : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → List ℂ}
    (hritz : ∀ H', IsUpperHessenberg H' → 0 < hessenbergPotential (2 ^ m) H' →
      (ritz H').length = 2 ^ m ∧ IsOptimalRitzValues θ H' (ritz H'))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t ≤ ⌈Real.log (1 / δ) / Real.log (1 / (1 - γ))⌉₊,
      IsDecoupled δ (shqrIterate B θ α γ m ritz H₀ t) := by
  have hk0 : 0 < 2 ^ m := by positivity
  have hψ0 : 0 ≤ hessenbergPotential (2 ^ m) H₀ :=
    hessenbergPotential_nonneg _ _
  -- until an iterate is reduced, the potential decays geometrically
  have key : ∀ t, (∃ t' ≤ t, IsDecoupled 0 (shqrIterate B θ α γ m ritz H₀ t')) ∨
      hessenbergPotential (2 ^ m) (shqrIterate B θ α γ m ritz H₀ t) ≤
        (1 - γ) ^ t * hessenbergPotential (2 ^ m) H₀ := by
    intro t
    induction t with
    | zero => exact Or.inr (by simp [shqrIterate])
    | succ t ih =>
      rcases ih with ⟨t', ht', h⟩ | ih
      · exact Or.inl ⟨t', by omega, h⟩
      by_cases hdec : IsDecoupled 0 (shqrIterate B θ α γ m ritz H₀ t)
      · exact Or.inl ⟨t, by omega, hdec⟩
      have hHt := hH.isUpperHessenberg_shqrIterate B θ α γ m ritz t
      have hψ : 0 < hessenbergPotential (2 ^ m) (shqrIterate B θ α γ m ritz H₀ t) := by
        by_contra h
        exact hdec (isDecoupled_of_hessenbergPotential_le hk0 hmn le_rfl
          (by simpa using not_lt.mp h))
      obtain ⟨hlen, hss⟩ := hritz _ hHt hψ
      obtain ⟨V', hV', hHV', hκ⟩ := exists_isUnit_mul_eq_mul_diagonal_shqrIterate hV hHV B θ α γ m
        ritz t
      rcases hHt.isDecoupled_zero_shqrStep_or_hessenbergPotential_le hV' hHV' (hκ ▸ hB) hm hmn
        hlen hss hθ hα1 hα hγ0 hγ1 with h | h
      · exact Or.inl ⟨t + 1, le_rfl, h⟩
      right
      refine h.trans ?_
      rw [pow_succ, mul_comm _ (1 - γ), mul_assoc]
      gcongr
  set T := ⌈Real.log (1 / δ) / Real.log (1 / (1 - γ))⌉₊
  have hL : 0 < Real.log (1 / (1 - γ)) :=
    Real.log_pos (by rw [one_div, one_lt_inv₀ (by linarith)]; linarith)
  have hT : (1 - γ) ^ T ≤ δ := by
    have h : Real.log (1 / δ) ≤ (T : ℝ) * Real.log (1 / (1 - γ)) :=
      (div_le_iff₀ hL).mp (Nat.le_ceil _)
    rw [one_div, one_div, Real.log_inv, Real.log_inv] at h
    rw [← Real.log_le_log_iff (pow_pos (by linarith) _) hδ, Real.log_pow]
    linarith
  rcases key T with ⟨t, ht, h⟩ | h
  · obtain ⟨i, hi⟩ := h
    exact ⟨t, ht, i, hi.trans (by gcongr)⟩
  refine ⟨T, le_rfl, isDecoupled_of_hessenbergPotential_le hk0 hmn hδ.le ?_⟩
  rw [specNorm_shqrIterate]
  calc _ ≤ (1 - γ) ^ T * hessenbergPotential (2 ^ m) H₀ := h
    _ ≤ δ * specNorm H₀ := by
      gcongr
      exact hessenbergPotential_le_specNorm hk0 hmn H₀

/-- **The number of shifts tried per iteration**: for $B, \theta, \alpha \ge 1$,
$0 < \gamma < 1$ and $m \ge 1$, the candidate list `NLAlib.shqrCandidates` has at most
$1 + 12/\varepsilon^2$ entries, $\varepsilon$ = `NLAlib.exceptionalSpacing` $2^m$ $B$ $\theta$
$\alpha$ $(1 - \gamma)^2$; each candidate is tested by one degree $k$ QR step
(`NLAlib.IsShiftSuccess`). [BanksGarzaVargasSrivastava2021, Theorem 1.6, item 2], as a count of
candidate shifts instead of arithmetic operations. -/
theorem length_shqrCandidates_le {B θ α γ : ℝ} (hB : 1 ≤ B) (hθ : 1 ≤ θ) (hα : 1 ≤ α)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) {m : ℕ} (hm : 1 ≤ m)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) :
    ((shqrCandidates B θ α γ m H ss).length : ℝ) ≤
      1 + 12 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2) ^ 2 := by
  have hB0 : 0 < B := by linarith
  have hθ0 : 0 < θ := by linarith
  have hα0 : 0 < α := by linarith
  have hγ' : 0 < 1 - γ := by linarith
  have hρ0 : 0 < (1 - γ) ^ 2 := pow_pos hγ' 2
  have hρ1 : (1 - γ) ^ 2 ≤ 1 := pow_le_one₀ hγ'.le (by linarith)
  have hB4 : 1 ≤ 14 * B ^ 4 := by have := one_le_pow₀ (n := 4) hB; linarith
  have hden : 1 ≤ (14 * B ^ 4) ^ (((2 ^ m : ℕ) : ℝ)⁻¹) * α ^ 2 * θ ^ 2 :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hB4 (by positivity))
        (one_le_pow₀ hα))
      (one_le_pow₀ hθ)
  have hden0 : 0 < (14 * B ^ 4) ^ (((2 ^ m : ℕ) : ℝ)⁻¹) * α ^ 2 * θ ^ 2 := by linarith
  have hk2 : (2 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    have : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    exact_mod_cast this
  have hexp : (0 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) / (((2 ^ m : ℕ) : ℝ) - 1) :=
    div_nonneg (by linarith) (by linarith)
  have hbase1 : (1 - γ) ^ 2 / ((14 * B ^ 4) ^ (((2 ^ m : ℕ) : ℝ)⁻¹) * α ^ 2 * θ ^ 2) ≤ 1 :=
    div_le_one_of_le₀ (by linarith) hden0.le
  have hε0 : 0 < exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2) := by
    unfold exceptionalSpacing
    exact Real.rpow_pos_of_pos (div_pos hρ0 hden0) _
  have hε1 : exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2) ≤ 1 := by
    unfold exceptionalSpacing
    exact Real.rpow_le_one (div_nonneg hρ0.le hden0.le) hbase1 hexp
  have hgrid := length_squareGrid_le (findRitz H m 1 ss)
    (exceptionalRadius (2 ^ m) B θ α (hessenbergPotential (2 ^ m) H)) hε0 hε1
  unfold shqrCandidates
  rw [List.length_cons]
  push_cast
  linarith

/-- **The spacing at the paper's parameters**: for $m \ge 1$, $B \ge 1$, $\theta = 2$,
$\gamma = 0.2$ and $\alpha = B^{4m/2^m}$,
$$\varepsilon \ge 0.0018\,B^{-(8m + 4)/(2^m - 1)}\,,$$
so the number of shifts per iteration is $O(B^{(16\log_2 k + 8)/(k-1)})$, which is $O(1)$ for
$k \ge C\log B\log\log B$. [BanksGarzaVargasSrivastava2021, Lemma 4.7, proof], there
$0.002B^{-(8\log k + 4)/(k-1)}$ for the constant $12$. -/
theorem exceptionalSpacing_ge {B : ℝ} (hB : 1 ≤ B) {m : ℕ} (hm : 1 ≤ m) :
    0.0018 * B ^ (-(8 * m + 4 : ℝ) / ((2 : ℝ) ^ m - 1)) ≤
      exceptionalSpacing (2 ^ m) B 2 (B ^ ((4 * m : ℝ) / (2 : ℝ) ^ m)) ((1 - 0.2) ^ 2) := by
  unfold exceptionalSpacing
  push_cast
  set k : ℝ := (2 : ℝ) ^ m with hk_def
  have hk : 2 ≤ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ k := pow_le_pow_right₀ (by norm_num) hm
  have hk1 : 0 < k - 1 := by linarith
  have hB0 : 0 < B := by linarith
  set c : ℝ := 0.16 / (14 : ℝ) ^ k⁻¹ with hc_def
  have h14 : (14 : ℝ) ^ k⁻¹ ≤ 3.75 := by
    have hk2 : k⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) hk2).trans ?_
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]
    norm_num
  have hc0 : 0.0425 ≤ c := by
    rw [hc_def, le_div_iff₀ (by positivity)]; nlinarith
  have hc1 : c ≤ 1 := by
    rw [hc_def, div_le_one (by positivity)]
    linarith [Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 14) (inv_nonneg.mpr (by linarith : 0 ≤ k))]
  have hbase : (1 - 0.2 : ℝ) ^ 2 / ((14 * B ^ 4) ^ k⁻¹ * (B ^ ((4 * m : ℝ) / k)) ^ 2 * 2 ^ 2) =
      c * B ^ (-(8 * m + 4 : ℝ) / k) := by
    have e : (8 * m + 4 : ℝ) / k = (4 : ℕ) * k⁻¹ + 4 * m / k * (2 : ℕ) := by push_cast; ring
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast B 4,
      ← Real.rpow_mul hB0.le, ← Real.rpow_natCast (B ^ _) 2, ← Real.rpow_mul hB0.le, neg_div,
      Real.rpow_neg hB0.le, hc_def, e, Real.rpow_add hB0]
    field_simp
    norm_num
  have hexp : (-(8 * m + 4 : ℝ) / k) * (k / (k - 1)) = -(8 * m + 4 : ℝ) / (k - 1) := by
    field_simp
  rw [hbase, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hB0.le, hexp]
  gcongr
  calc (0.0018 : ℝ) ≤ c ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
    _ ≤ c ^ (k / (k - 1)) := Real.rpow_le_rpow_of_exponent_ge (by linarith) hc1
        (by rw [div_le_iff₀ hk1]; linarith)

/-- **Rapid decoupling for normal Hessenberg matrices**: let $\mathbf{H}_0$ be normal and upper
Hessenberg, $k = 2^m$ with $m \ge 1$ and $k \le n$, and $0 < \gamma < 1$. With the exact Ritz
values and $B = \theta = \alpha = 1$, the iteration $\mathrm{Sh}_{k,1}$ is $\delta$-decoupled
at some
$$t \le \Bigl\lceil\frac{\log(1/\delta)}{\log(1/(1 - \gamma))}\Bigr\rceil$$
for every $\delta > 0$; by `NLAlib.length_shqrCandidates_le` each iteration tries at most
$1 + 12/\varepsilon^2$ shifts, $\varepsilon = ((1 - \gamma)^2/14^{1/k})^{k/(k-1)}$.
Adapted from [BanksGarzaVargasSrivastava2021, Theorem 1.2] (Theorem 3.3 there for $k = 2$), which
uses a separate strategy $\mathrm{Sh}_{2,1}$ with a quadratic shift $(z - r)^2$; here as the case
$B = 1$ of the general strategy.
Result: shifted-qr-normal-decoupling -/
theorem _root_.IsStarNormal.exists_le_isDecoupled_shqrIterate_ritzValues
    {H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hN : IsStarNormal H₀)
    (hH : IsUpperHessenberg H₀) {m : ℕ} (hm : 1 ≤ m) (hmn : 2 ^ m ≤ n) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t ≤ ⌈Real.log (1 / δ) / Real.log (1 / (1 - γ))⌉₊,
      IsDecoupled δ (shqrIterate 1 1 1 γ m (ritzValues (2 ^ m)) H₀ t) := by
  obtain ⟨V, d, hV, hHV, hcond⟩ :=
    hN.exists_isUnit_mul_eq_mul_diagonal_and_pseudoConditionNumber_eq_one
  have hk : 0 < 2 ^ m := by positivity
  have hritz : ∀ H', IsUpperHessenberg H' → 0 < hessenbergPotential (2 ^ m) H' →
      (ritzValues (2 ^ m) H').length = 2 ^ m ∧
        IsOptimalRitzValues 1 H' (ritzValues (2 ^ m) H') :=
    fun H' hH' _ =>
      ⟨length_ritzValues _ _, IsUpperHessenberg.isOptimalRitzValues_one_ritzValues hH' hk hmn⟩
  exact IsUpperHessenberg.exists_le_isDecoupled_shqrIterate hH hV hHV hcond.le hm hmn le_rfl le_rfl
    (by simp) hγ0 hγ1 hritz hδ

end NLAlib
