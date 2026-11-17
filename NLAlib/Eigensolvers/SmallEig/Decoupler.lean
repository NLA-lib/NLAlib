/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveTermination
public import NLAlib.Eigensolvers.SmallEig.Decouple
public import NLAlib.Eigensolvers.SmallEig.OneEig
public import NLAlib.Eigensolvers.SmallEig.Precision
public import NLAlib.Eigensolvers.SmallEig.RandomHessenberg

/-!
# The decoupler of the small-eigenvalue solver

One node of the deflation of [BanksGarzaVargasSrivastava2025, §6] (the paper's `Eig` on a block,
with `RHess` at every node, decision D7 of the design): `RHess` makes the last-row weights large,
`OneEig` finds a shift within $\beta' = \omega/20$ of an eigenvalue and at least $\eta_1$ away from
the spectrum, and `Decouple` makes the last subdiagonal entry at most $\omega$. As the decoupler of
the rounded worklist at the bottom width $k = 1$ it meets the randomized decoupling contract on the
class of the blocks; Lemma 6.2's preservation of the class is carried by the composition of the
three contracts, and the class inside the node by one doubling
(`NLAlib.SmallEig.class_of_rhess`).

## Main definitions

* `NLAlib.SmallEig.smallEigDecoupler`: the program `[N, k, np, F, T] (W, P) → (W, Fl)`.
* `NLAlib.SmallEig.smallEigDecoupleError`: its backward error.

## Main results

* `NLAlib.SmallEig.class_of_rhess`,
  `NLAlib.SmallEig.smallEigDecoupler_randomDecouplingRoutineContract`,
  `NLAlib.SmallEig.smallEigDecoupler_terminatingDecouplerRoutine`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The decoupler of the small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025, §6], one
node): read the cap words $m$ (bound $T$), $q$ (bound $m$), $t$ and $m_2$ (bound $T$) from
`P[8..11]`; `NLAlib.SmallEig.rhess` on the block `W` in place; `NLAlib.SmallEig.oneEig` with the
words `P` into the shift `Lam` and the flag; if the flag is $0$,
`NLAlib.SmallEig.decoupleLast` with the shift. The interface is
`[N, k, np, F, T] (W, P) → (W, Fl)`, that of the decoupling routine of
`NLAlib.ShiftedQR.solveRoundedWith`; the bottom width and the iteration cap are not read.
Algorithm: small-eig -/
def smallEigDecoupler (sG : ℕ) : Impl O Q := opsImpl% [N, k, np, F, T] (W, P) → (W, Fl) {
  let m ← index (Has.inj IdxTst.toNat) (P[8]) ≤ T;
  let q ← index (Has.inj IdxTst.toNat) (P[9]) ≤ m;
  let t ← index (Has.inj IdxTst.toNat) (P[10]) ≤ T;
  let m2 ← index (Has.inj IdxTst.toNat) (P[11]) ≤ T;
  let Lam ← alloc 2;
  run (rhess (O := O) (Q := Q) sG).body [N] (W, W);
  run (oneEig (O := O) (Q := Q)).body [N, m, q, t] (W, P, Lam, Fl);
  if (Has.inj CmpTst.isZero) [] (Fl) {
    run (decoupleLast (O := O) (Q := Q)).body [N, m2] (W, Lam, P, W, Fl)
  } else { skip }
}

end Program

/-- The backward error of the decoupler on a block of norm at most $N$ at the unit roundoff
$\boldsymbol{u}$: `RHess`, $200(n_{\max} + 1)^2\boldsymbol{u}N$, and `Decouple` from a block of norm
at most $2N$ with the shift reach $10$,
$11 \cdot 2N((1 + 300(n_{\max} + 1)^2\boldsymbol{u})^{m_2} - 1)$. -/
noncomputable def smallEigDecoupleError (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) (u N : ℝ) :
    ℝ :=
  200 * ((nmax : ℝ) + 1) ^ 2 * u * N +
    11 * (2 * N) * ((1 + 300 * ((nmax : ℝ) + 1) ^ 2 * u) ^ smallEigDecoupleSteps nmax S δ φ c₂ - 1)

/-- A unitary similarity carries a diagonalization: $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is
diagonalized by $\mathbf{Q}^{\mathsf{H}}\mathbf{V}$, with the same eigenvalues and condition. -/
private theorem exists_diagonalization_conjTranspose_mul_mul {n : ℕ}
    {A Q V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hAV : A * V = V * Matrix.diagonal d) (hQ : HasOrthonormalCols Q) :
    IsUnit (Qᴴ * V) ∧ (Qᴴ * A * Q) * (Qᴴ * V) = (Qᴴ * V) * Matrix.diagonal d ∧
      pseudoConditionNumber (Qᴴ * V) = pseudoConditionNumber V := by
  have hQQ : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQ.conjTranspose_mul_self
  have hU : HasOrthonormalCols Qᴴ := by
    unfold HasOrthonormalCols; rwa [Matrix.conjTranspose_conjTranspose]
  have hQu : IsUnit Qᴴ := ⟨⟨Qᴴ, Q, hQ.conjTranspose_mul_self, hQQ⟩, rfl⟩
  refine ⟨hQu.mul hV, ?_,
    hU.pseudoConditionNumber_mul_left V⟩
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQQ, Matrix.one_mul, hAV]

/-- **The class after `RHess`** ([BanksGarzaVargasSrivastava2025, Lemma 6.2], the class part, as
the merged deflation's class doubling): if $\mathbf{A}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le 2B$,
eigenvalues separated by $g/2$, $g > 0$, $\mathbf{Q}$ unitary and
$\|\mathbf{H} - \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}\|_2 \le g/(64(n + 1)B)$, then
$\mathbf{H}$ has a diagonalization with condition at most $4B$ and eigenvalues separated by
$g/4$. -/
theorem class_of_rhess {n : ℕ} {A H Q V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} {B g : ℝ} (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ 2 * B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g / 2 ≤ ‖d i - d j‖) (hQ : HasOrthonormalCols Q)
    (hH : specNorm (H - Qᴴ * A * Q) ≤ g / (64 * (n + 1) * B)) :
    ∃ (V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d' : Fin (n + 1) → ℂ), IsUnit V' ∧
      H * V' = V' * Matrix.diagonal d' ∧ pseudoConditionNumber V' ≤ 4 * B ∧
      ∀ i j, i ≠ j → g / 4 ≤ ‖d' i - d' j‖ := by
  have hB : 0 < B := by
    have := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ; linarith
  obtain ⟨hV₀, hAV₀, hκ₀⟩ := exists_diagonalization_conjTranspose_mul_mul hV hAV hQ
  have hE : specNorm (H - Qᴴ * A * Q) ≤ g / 2 / (16 * (n + 1) * (2 * B)) := by
    convert hH using 1; field_simp; ring
  obtain ⟨V', d', hV', hHV', hκ', hgap'⟩ := exists_pseudoConditionNumber_le_and_le_norm_sub hV₀
    hAV₀ (hκ₀.trans_le hκ) (by positivity) hgap hE
  rw [add_sub_cancel] at hHV'
  refine ⟨V', d', hV', hHV', by linarith, fun i j hij => le_trans ?_ (hgap' i j hij)⟩
  have hn : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h1 : 2 * (2 * B) * specNorm (H - Qᴴ * A * Q) ≤ g / 16 := by
    calc 2 * (2 * B) * specNorm (H - Qᴴ * A * Q) ≤ 4 * B * (g / (64 * (n + 1) * B)) := by
          rw [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num]; gcongr
      _ = g / (16 * (n + 1)) := by field_simp; ring
      _ ≤ g / 16 := div_le_div_of_nonneg_left hg.le (by norm_num) (by linarith)
  linarith

/-! ### The precision bookkeeping of the decoupler -/

/-- $(1 + x)^m \le 2$ for $x \ge 0$ with $mx \le 1/2$. -/
theorem one_add_pow_le_two {x : ℝ} {m : ℕ} (hx : 0 ≤ x) (h : m * x ≤ 1 / 2) :
    (1 + x) ^ m ≤ 2 := by
  have he : Real.exp (1 / 2) ^ 2 < 4 := by
    rw [← Real.exp_nat_mul]; norm_num
    linarith [Real.exp_one_lt_d9]
  calc (1 + x) ^ m ≤ Real.exp x ^ m := by
        gcongr; linarith [Real.add_one_le_exp x]
    _ = Real.exp (m * x) := (Real.exp_nat_mul x m).symm
    _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr h
    _ ≤ 2 := by nlinarith [Real.exp_pos (1 / 2)]

/-- $(m + 1)r^m \le 1$ for $0 \le r \le 1/2$. -/
theorem succ_mul_pow_le_one {r : ℝ} (h0 : 0 ≤ r) (h : r ≤ 1 / 2) (m : ℕ) :
    ((m : ℝ) + 1) * r ^ m ≤ 1 := by
  have h2 : ((m : ℝ) + 1) ≤ 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
  calc ((m : ℝ) + 1) * r ^ m ≤ 2 ^ m * (1 / 2) ^ m := by gcongr
    _ = 1 := by rw [← mul_pow]; norm_num

/-- The terms of the precision threshold that the decoupler uses, unfolded: for tail records
with $b_1, b_2 > 0$, $n_{\max} \ge 1$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and
$\boldsymbol{u} \le$ `NLAlib.SmallEig.uSmallEig`, the counts, `RHess`, `DistSpec` and `Decouple`
terms. -/
theorem smallEigDecoupler_precision {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : 1 ≤ nmax) {S δ φ u : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) :
    100000 * ((nmax : ℝ) + 1) ^ 2 * u ≤ 1 ∧
    1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) * u ≤ smallEigSeparation nmax S δ φ c₁ / 2 /
      (64 * ((nmax : ℝ) + 1) * (2 * smallEigCondition nmax S δ φ c₂)) ∧
    1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) * u ≤
      √(smallEigWeight nmax S δ φ c₂) * (smallEigSeparation nmax S δ φ c₁ / 2) /
        (1024 * ((nmax : ℝ) + 1) * (2 * smallEigCondition nmax S δ φ c₂) ^ 2) ∧
    30000 * ((2 : ℝ) ^ smallEigDegreeLog nmax S δ φ c₂ + 1) * u ≤ 1 ∧
    300 * ((nmax : ℝ) + 1) ^ 2 * u ≤ (8004 * (8 * smallEigCondition nmax S δ φ c₂))⁻¹ *
      (smallEigInnerRadius nmax S δ φ c₁ c₂ / (22 * (2 * S))) ^
        (2 ^ smallEigDegreeLog nmax S δ φ c₂) ∧
    300 * ((nmax : ℝ) + 1) ^ 2 * u ≤ (16 * (8 * smallEigCondition nmax S δ φ c₂))⁻¹ *
      (smallEigInnerRadius nmax S δ φ c₁ c₂ / (22 * (2 * S))) ^
        smallEigDecoupleSteps nmax S δ φ c₂ ∧
    300 * ((nmax : ℝ) + 1) ^ 2 * u ≤ smallEigOmega nmax S δ φ c₁ c₂ / 2 /
      (86 * (8 * smallEigCondition nmax S δ φ c₂) * (2 * S) *
        (22 * (2 * S) / smallEigInnerRadius nmax S δ φ c₁ c₂) ^
          smallEigDecoupleSteps nmax S δ φ c₂ * √((nmax : ℝ) + 1)) := by
  obtain ⟨-, h1, -, h3, h4, h5, -⟩ := uSmallEig_spec hb₁ hb₂ hn hδ hδS hφ hφ1
  have hS : 0 < S := hδ.trans_le hδS
  have hN : (0 : ℝ) < ((nmax : ℝ) + 1) ^ 2 := by positivity
  have a := hu.trans h1
  have b := hu.trans h3
  have c := hu.trans h4
  have d := hu.trans h5
  unfold uSmallEigBasic at a
  unfold uSmallEigRHess at b
  unfold uSmallEigDistSpec at c
  unfold uSmallEigDecouple at d
  rw [le_div_iff₀ (by positivity)] at b d
  have a2 := a.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at a2
  have c1 := c.trans (min_le_left _ _)
  have c2 := c.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at c1
  rw [le_div_iff₀ (by positivity)] at c2
  have b1 := b.trans (min_le_left _ _)
  have b2 := b.trans (min_le_right _ _)
  have d1 := d.trans (min_le_left _ _)
  have d2 := d.trans (min_le_right _ _)
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-- The precision conditions of `RHess` inside the decoupler: on a block of order
$n + 1 \le n_{\max} + 1$ and norm $N \le 2\Sigma$, in the class $(2B_c, g_c/2)$ with $B_c \ge 4$
and $0 < g_c \le \Sigma$, with the direction bound $s > 0$, the radius $R > 0$ and
$\sqrt p = s/(16RB_c)$, the `RHess` terms of the threshold give the precision conditions of
`NLAlib.SmallEig.rhess_pwrites` at the norm $N$. -/
theorem smallEigDecoupler_rhess_precision {nmax n : ℕ} (hn : n ≤ nmax) {u N S gc Bc s R p : ℝ}
    (hu0 : 0 ≤ u) (hN0 : 0 ≤ N) (hNS : N ≤ 2 * S) (hgc : 0 < gc) (hgcS : gc ≤ S)
    (hBc : 4 ≤ Bc) (hs : 0 < s) (hR : 0 < R) (hp : √p = s / (16 * R * Bc))
    (ha : 100000 * ((nmax : ℝ) + 1) ^ 2 * u ≤ 1)
    (hb : 1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) * u ≤
      gc / 2 / (64 * ((nmax : ℝ) + 1) * (2 * Bc)))
    (hc : 1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) * u ≤
      √p * (gc / 2) / (1024 * ((nmax : ℝ) + 1) * (2 * Bc) ^ 2)) :
    100 * ((n : ℝ) + 1) ^ 2 * u ≤ 1 ∧ 60 * ((n : ℝ) + 1) * u ≤ s / (2 * R) ∧
      200 * ((n : ℝ) + 1) ^ 2 * u * N ≤ min (gc / 2 / (32 * (n + 1) * (2 * Bc)))
        (s * (gc / 2) / (1024 * (n + 1) * (2 * Bc) ^ 2 * R)) := by
  have hn' : (n : ℝ) + 1 ≤ nmax + 1 := by exact_mod_cast Nat.succ_le_succ hn
  have hn1 : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((nmax : ℝ) + 1) ^ 2 := by gcongr
  have hS : 0 < S := hgc.trans_le hgcS
  have hK : 200 * ((n : ℝ) + 1) ^ 2 * u * N ≤ 1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) * u := by
    have h1 : ((n : ℝ) + 1) ^ 2 * u * N ≤ ((nmax : ℝ) + 1) ^ 2 * u * (2 * S) := by
      gcongr
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ((nmax : ℝ) + 1)) hu0) hS.le]
  set Y := s / R with hY
  have hY0 : 0 < Y := div_pos hs hR
  have hA : √p ≤ Y / 64 := by
    rw [hp, hY, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hs hR]
  have hD : (1 : ℝ) ≤ 1024 * ((nmax : ℝ) + 1) * (2 * Bc) ^ 2 := by nlinarith
  have hc' : 1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) * u ≤ Y / 64 * (S / 2) := by
    refine hc.trans ((div_le_self (by positivity) hD).trans ?_)
    exact mul_le_mul hA (by linarith) (by positivity) (by positivity)
  have hu1 : 2000 * ((nmax : ℝ) + 1) ^ 2 * u ≤ Y / 128 := by
    have : S * (2000 * ((nmax : ℝ) + 1) ^ 2 * u) ≤ S * (Y / 128) := by nlinarith
    exact le_of_mul_le_mul_left this hS
  refine ⟨by nlinarith, ?_, le_min (hK.trans (hb.trans ?_)) (hK.trans (hc.trans ?_))⟩
  · have e : s / (2 * R) = Y / 2 := by rw [hY]; field_simp
    rw [e]
    have : ((n : ℝ) + 1) ≤ ((nmax : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  · rw [hp]
    have e1 : s / (16 * R * Bc) * (gc / 2) / (1024 * ((nmax : ℝ) + 1) * (2 * Bc) ^ 2) =
        s * gc / (2048 * (2 * Bc) ^ 2 * R) / (16 * Bc * ((nmax : ℝ) + 1)) := by
      field_simp; norm_num
    have e2 : s * (gc / 2) / (1024 * ((n : ℝ) + 1) * (2 * Bc) ^ 2 * R) =
        s * gc / (2048 * (2 * Bc) ^ 2 * R) / ((n : ℝ) + 1) := by
      field_simp; norm_num
    rw [e1, e2]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

/-- The parameters of `RHess` inside the decoupler: with the direction bound
$s = \sqrt{\varphi_D/(8n_{\max})}$ and the radius $R' = \sqrt2\,R$ ($R$ =
`NLAlib.SmallEig.smallEigVectorRadius`), for $n \le n_{\max}$, $n_{\max} \ge 1$ and
$0 < \varphi \le 1$: the weight bound $p$ = `NLAlib.SmallEig.smallEigWeight` is the bound
$s^2/(64R'^2(2B_c)^2)$ of `NLAlib.SmallEig.rhess_pwrites` at the condition $2B_c$, so
$\sqrt p = s/(16R'B_c)$; $R'$ is a valid radius at the failure $\varphi_D/4$; and the failure
$(n + 1)s^2 + \varphi_D/4$ is at most $\varphi_D/2$. -/
theorem smallEigDecoupler_rhess_params {nmax n : ℕ} (hn1 : 1 ≤ nmax) (hn : n ≤ nmax)
    {φ Bc : ℝ} (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hBc : 0 < Bc) (S δ : ℝ) (c₂ : PolyLogTail)
    (hB : Bc = smallEigCondition nmax S δ φ c₂) :
    let s := √(smallEigDecouplerFailure nmax φ / (8 * nmax))
    let R := √2 * smallEigVectorRadius nmax φ
    0 < s ∧ 0 < R ∧
    smallEigWeight nmax S δ φ c₂ = s ^ 2 / (64 * R ^ 2 * (2 * Bc) ^ 2) ∧
    √(smallEigWeight nmax S δ φ c₂) = s / (16 * R * Bc) ∧
    2 * (√((n : ℝ) + 1) + 1) + √(2 * Real.log (smallEigDecouplerFailure nmax φ / 4)⁻¹) ≤ R ∧
    (n + 1) * s ^ 2 + smallEigDecouplerFailure nmax φ / 4 ≤
      smallEigDecouplerFailure nmax φ / 2 := by
  intro s R
  have hn' : (1 : ℝ) ≤ nmax := by exact_mod_cast hn1
  have hnn : (n : ℝ) ≤ nmax := by exact_mod_cast hn
  set φD := smallEigDecouplerFailure nmax φ with hφD
  have hD : 0 < φD := by rw [hφD]; unfold smallEigDecouplerFailure; positivity
  have hD16 : φD ≤ 1 / 16 := by
    rw [hφD]; unfold smallEigDecouplerFailure
    rw [div_le_iff₀ (by positivity)]; nlinarith
  set L := √(2 * Real.log (4 / φD)) with hL
  have hL2 : 2 ≤ L := by
    have h64 : 64 ≤ 4 / φD := by rw [le_div_iff₀ hD]; linarith
    have he : Real.exp 2 ≤ 64 := by
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
    have hlog : 2 ≤ Real.log (4 / φD) :=
      (Real.le_log_iff_exp_le (by positivity)).mpr (he.trans h64)
    rw [hL, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hRv : smallEigVectorRadius nmax φ = 3 * √(nmax : ℝ) + L := by
    rw [hL, hφD]; rfl
  have hsn : 1 ≤ √(nmax : ℝ) := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hn'
  have h2 : 1.41 ≤ √(2 : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hRv0 : 0 < smallEigVectorRadius nmax φ := by rw [hRv]; positivity
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hR : 0 < R := by positivity
  have hs2 : s ^ 2 = φD / (8 * nmax) := Real.sq_sqrt (by positivity)
  have hR2 : R ^ 2 = 2 * smallEigVectorRadius nmax φ ^ 2 := by
    simp only [R, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hp : smallEigWeight nmax S δ φ c₂ = s ^ 2 / (64 * R ^ 2 * (2 * Bc) ^ 2) := by
    rw [hs2, hR2, smallEigWeight, ← hB, ← hφD]
    field_simp; ring
  refine ⟨hs, hR, hp, ?_, ?_, ?_⟩
  · rw [hp, show 64 * R ^ 2 * (2 * Bc) ^ 2 = (16 * R * Bc) ^ 2 by ring, ← div_pow,
      Real.sqrt_sq (by positivity)]
  · rw [inv_div, ← hL]
    have hnn2 : √((n : ℝ) + 1) ≤ √2 * √(nmax : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt (by linarith)
    simp only [R, hRv]
    nlinarith [mul_le_mul h2 hsn (by norm_num) (Real.sqrt_nonneg 2),
      mul_le_mul_of_nonneg_left hL2 (by linarith : (0 : ℝ) ≤ √2 - 1)]
  · rw [hs2]
    have : ((n : ℝ) + 1) * (φD / (8 * nmax)) ≤ φD / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith

/-- A power of a ratio loses at most a factor $2$ when the denominator grows by $1 + x$ with
$mx \le 1/2$: for $0 < a \le b(1 + x)$, $x \ge 0$, $c \ge 0$,
$(c/b)^m \le 2(c/a)^m$. -/
theorem div_pow_le_two_mul {a b c x : ℝ} {m : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hab : a ≤ b * (1 + x)) (hmx : m * x ≤ 1 / 2) :
    (c / b) ^ m ≤ 2 * (c / a) ^ m := by
  have h2 := one_add_pow_le_two hx hmx
  have h1 : c / b = (c / (b * (1 + x))) * (1 + x) := by field_simp
  have h3 : c / (b * (1 + x)) ≤ c / a := div_le_div_of_nonneg_left hc ha hab
  rw [h1, mul_pow]
  calc (c / (b * (1 + x))) ^ m * (1 + x) ^ m ≤ (c / a) ^ m * 2 := by gcongr
    _ = 2 * (c / a) ^ m := mul_comm _ _

/-- The precision conditions of `OneEig` inside the decoupler: on a block of order
$n + 1 \le n_{\max} + 1$ after `RHess`, of norm $\|\mathbf{H}\|_2 \le 2\Sigma(1 + x)$ with
$x = 200(n_{\max} + 1)^2\boldsymbol{u}$, the norm $\Sigma'' = 2\Sigma(1 + x)$ is within $1\%$ of
$2\Sigma$, and the `DistSpec` term of the threshold at the condition $8B_c$ gives the precision
condition of `NLAlib.SmallEig.oneEig_pwrites_of_norm_le` at the condition $4B_c$. -/
theorem smallEigDecoupler_oneEig_precision {nmax n m : ℕ} (hn : n ≤ nmax) {u S Hn η₁ Bc : ℝ}
    (hu0 : 0 ≤ u) (hS : 0 < S) (hη₁ : 0 < η₁) (hη₁S : η₁ ≤ S) (hBc : 4 ≤ Bc) (hN0 : 0 ≤ Hn)
    (hN : Hn ≤ 2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u))
    (ha : 100000 * ((nmax : ℝ) + 1) ^ 2 * u ≤ 1)
    (he : 300 * ((nmax : ℝ) + 1) ^ 2 * u ≤ (8004 * (8 * Bc))⁻¹ * (η₁ / (22 * (2 * S))) ^ m) :
    2 * S ≤ 2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u) ∧
      2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u) ≤ 1.01 * (2 * S) ∧
      300 * ((n : ℝ) + 1) ^ 2 * u ≤ (8004 * (4 * Bc))⁻¹ *
        (η₁ / (2 * Hn + 20 * (2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u)))) ^ m := by
  set x := 200 * ((nmax : ℝ) + 1) ^ 2 * u with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 0.01 := by linarith
  have hn' : (n : ℝ) + 1 ≤ nmax + 1 := by exact_mod_cast Nat.succ_le_succ hn
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((nmax : ℝ) + 1) ^ 2 := by gcongr
  set r := η₁ / (22 * (2 * S)) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 / 2 := by rw [hr, div_le_iff₀ (by positivity)]; linarith
  set K := (8004 * (8 * Bc))⁻¹ with hK
  have hK0 : 0 < K := by positivity
  have hK1 : K ≤ 1 / 2 := by rw [hK]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have hmr := succ_mul_pow_le_one hr0.le hr1 m
  have hmx : m * x ≤ 1 / 2 := by
    have : x ≤ K * r ^ m := by linarith
    have h1 : (m : ℝ) * x ≤ m * (K * r ^ m) := by gcongr
    have h2 : (m : ℝ) * r ^ m ≤ 1 := by nlinarith [pow_nonneg hr0.le m]
    nlinarith
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have hden : 0 < 2 * Hn + 20 * (2 * S * (1 + x)) := by positivity
  have hpow := div_pow_le_two_mul (c := η₁) (m := m) hden (by positivity : (0 : ℝ) < 22 * (2 * S))
    hη₁.le hx0 (by nlinarith) hmx
  rw [← hr] at hpow
  have e : (8004 * (4 * Bc))⁻¹ = 2 * K := by rw [hK]; field_simp; ring
  rw [e]
  have : 300 * ((n : ℝ) + 1) ^ 2 * u ≤ 300 * ((nmax : ℝ) + 1) ^ 2 * u := by gcongr
  nlinarith

/-- The precision conditions of `Decouple` inside the decoupler: on a block of order
$k + 2 \le n_{\max} + 1$ after `RHess`, with $\eta_1 \le \|\mathbf{H}\|_2 \le 2\Sigma(1 + x)$,
$x = 200(n_{\max} + 1)^2\boldsymbol{u}$, the `Decouple` terms of the threshold at the condition
$8B_c$ give the precision conditions of `NLAlib.SmallEig.decoupleLast_spec` at the condition $4B_c$
and the shift reach $C = 10$, for every step count $\ell \le m_2$. -/
theorem smallEigDecoupler_decouple_precision {nmax k m₂ : ℕ} (hk : k + 1 ≤ nmax)
    {u S Hn η₁ Bc ω : ℝ} (hu0 : 0 ≤ u) (hS : 0 < S) (hη₁ : 0 < η₁) (hη₁S : η₁ ≤ S)
    (hBc : 4 ≤ Bc) (hη₁H : η₁ ≤ Hn) (hN : Hn ≤ 2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u))
    (hf : 300 * ((nmax : ℝ) + 1) ^ 2 * u ≤ (16 * (8 * Bc))⁻¹ * (η₁ / (22 * (2 * S))) ^ m₂)
    (hg : 300 * ((nmax : ℝ) + 1) ^ 2 * u ≤ ω / 2 / (86 * (8 * Bc) * (2 * S) *
      (22 * (2 * S) / η₁) ^ m₂ * √((nmax : ℝ) + 1))) :
    (∀ ℓ ≤ m₂, 300 * ((k : ℝ) + 2) ^ 2 * u ≤
      (16 * (4 * Bc))⁻¹ * (η₁ / ((2 + 2 * 10) * Hn)) ^ ℓ) ∧
    ∀ ℓ ≤ m₂, (66 + 2 * 10) * (4 * Bc) * Hn * ((2 + 2 * 10) * Hn / η₁) ^ ℓ *
      √((k : ℝ) + 2) * (300 * ((k : ℝ) + 2) ^ 2 * u) ≤ ω / 2 := by
  set x := 200 * ((nmax : ℝ) + 1) ^ 2 * u with hx
  have hx0 : 0 ≤ x := by positivity
  have hk' : (k : ℝ) + 2 ≤ nmax + 1 := by
    have : ((k + 1 : ℕ) : ℝ) ≤ nmax := by exact_mod_cast hk
    push_cast at this; linarith
  have hsq : ((k : ℝ) + 2) ^ 2 ≤ ((nmax : ℝ) + 1) ^ 2 := by gcongr
  set V := 300 * ((nmax : ℝ) + 1) ^ 2 * u with hV
  have hV0 : 0 ≤ V := by positivity
  have hkV : 300 * ((k : ℝ) + 2) ^ 2 * u ≤ V := by rw [hV]; gcongr
  set r := η₁ / (22 * (2 * S)) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 / 2 := by rw [hr, div_le_iff₀ (by positivity)]; linarith
  have hmr := succ_mul_pow_le_one hr0.le hr1 m₂
  have hK1 : (16 * (8 * Bc))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have hmx : ((m₂ + 1 : ℕ) : ℝ) * x ≤ 1 / 2 := by
    have h1 : x ≤ r ^ m₂ / 2 := by nlinarith [pow_nonneg hr0.le m₂]
    push_cast
    nlinarith [pow_nonneg hr0.le m₂]
  have hmx' : (m₂ : ℝ) * x ≤ 1 / 2 := by push_cast at hmx; nlinarith
  have hH0 : 0 < Hn := hη₁.trans_le hη₁H
  refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
  · have ha1 : η₁ / ((2 + 2 * 10) * Hn) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hpow := div_pow_le_two_mul (c := η₁) (m := m₂)
      (by positivity : (0 : ℝ) < (2 + 2 * 10) * Hn) (by positivity : (0 : ℝ) < 22 * (2 * S))
      hη₁.le hx0 (by nlinarith) hmx'
    rw [← hr] at hpow
    have hℓ' : (η₁ / ((2 + 2 * 10) * Hn)) ^ m₂ ≤ (η₁ / ((2 + 2 * 10) * Hn)) ^ ℓ :=
      pow_le_pow_of_le_one (by positivity) ha1 hℓ
    have e : (16 * (4 * Bc))⁻¹ = 2 * (16 * (8 * Bc))⁻¹ := by field_simp; ring
    rw [e]
    nlinarith [inv_pos.mpr (by positivity : (0 : ℝ) < 16 * (8 * Bc))]
  · set Z := (22 * (2 * S) / η₁) ^ m₂ with hZ
    have hb1 : 1 ≤ (2 + 2 * 10) * Hn / η₁ := by rw [le_div_iff₀ hη₁]; linarith
    have hb : ((2 + 2 * 10) * Hn / η₁) ^ ℓ ≤ Z * (1 + x) ^ m₂ := by
      calc ((2 + 2 * 10) * Hn / η₁) ^ ℓ ≤ ((2 + 2 * 10) * Hn / η₁) ^ m₂ :=
            pow_le_pow_right₀ hb1 hℓ
        _ ≤ (22 * (2 * S) / η₁ * (1 + x)) ^ m₂ := by
            gcongr
            rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hη₁]; nlinarith
        _ = Z * (1 + x) ^ m₂ := by rw [mul_pow]
    have h2 := one_add_pow_le_two hx0 hmx
    have hD : 0 < 86 * (8 * Bc) * (2 * S) * Z * √((nmax : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hD] at hg
    have hsk : √((k : ℝ) + 2) ≤ √((nmax : ℝ) + 1) := Real.sqrt_le_sqrt hk'
    calc (66 + 2 * 10) * (4 * Bc) * Hn * ((2 + 2 * 10) * Hn / η₁) ^ ℓ *
          √((k : ℝ) + 2) * (300 * ((k : ℝ) + 2) ^ 2 * u)
        ≤ (66 + 2 * 10) * (4 * Bc) * (2 * S * (1 + x)) * (Z * (1 + x) ^ m₂) *
          √((nmax : ℝ) + 1) * V := by gcongr
      _ = V * (86 * (8 * Bc) * (2 * S) * Z * √((nmax : ℝ) + 1)) * ((1 + x) ^ (m₂ + 1) / 2) := by
          ring
      _ ≤ V * (86 * (8 * Bc) * (2 * S) * Z * √((nmax : ℝ) + 1)) * 1 := by
          gcongr; linarith
      _ ≤ ω / 2 := by linarith

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- The outcomes of a decoupling call on a fixed block $\mathbf{H}$, as pairs of a memory before
and after: the frame `F`, the flag $0$, an initialised work matrix, and the matrix read after is an
upper Hessenberg perturbed unitary similarity of $\mathbf{H}$ with error $\varepsilon$ whose last
subdiagonal entry has modulus at most $\omega$. They form a measurable set. -/
theorem measurableSet_decoupleOutcome_of {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ε ω : ℝ) (w f : ℕ × ℕ) (F : Fp) :
    MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧
      x.2.store.get f.1 f.2 = some 0 ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (x.2.store.get w.1 (w.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilar H (storedMatrix w (n + 1) (n + 1) x.2.store) ε ∧
      IsUpperHessenberg (storedMatrix w (n + 1) (n + 1) x.2.store) ∧
      ∃ i : Fin n, n ≤ (i : ℕ) + 1 ∧
        ‖storedMatrix w (n + 1) (n + 1) x.2.store i.succ i.castSucc‖ ≤ ω} := by
  have hm : Measurable fun x : Mem ℝ × Mem ℝ => storedMatrix w (n + 1) (n + 1) x.2.store :=
    (measurable_storedMatrix w (n + 1) (n + 1)).comp measurable_snd
  have hent (i j : Fin (n + 1)) : Measurable fun x : Mem ℝ × Mem ℝ =>
      storedMatrix w (n + 1) (n + 1) x.2.store i j :=
    (Matrix.measurable_apply i j).comp hm
  simp only [Set.ofPred_and]
  refine (Mem.measurableSet_eqOff F).inter ((measurable_snd (Mem.measurableSet_get_eq f 0)).inter
    ((measurable_snd (measurableSet_forall_isSome w _)).inter
      (((isClosed_setOf_isPerturbedUnitarySimilar ε).measurableSet.preimage
        (measurable_const.prodMk hm)).inter ((?_ : MeasurableSet _).inter ?_))))
  · simp only [IsUpperHessenberg, Set.ofPred_forall]
    refine .iInter fun i => .iInter fun j => ?_
    by_cases hij : (j : ℕ) + 1 < i
    · simpa [hij] using measurableSet_eq_fun (hent i j) measurable_const
    · simp [hij]
  · simp only [Set.ofPred_exists, Set.ofPred_and]
    exact .iUnion fun i => (MeasurableSet.const _).inter
      (measurableSet_le (hent _ _).norm measurable_const)

/-- The input of `OneEig` survives a write of the matrix: after a run that writes only the block
of the matrix and stores $\mathbf{H}'$ there, `NLAlib.SmallEig.OneEigInput` holds with
$\mathbf{H}'$. -/
theorem OneEigInput.of_eqOff_matrix {n : ℕ} {H H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} {h qw lam f : ℕ × ℕ} {μ μ' : Mem ℝ} (hin : OneEigInput H qs h qw lam f μ)
    (hfr : μ.store.EqOff (Store.inBlock h.1 h.2 (2 * ((n + 1) * (n + 1)))) μ'.store)
    (hH' : HoldsMatrix h H' μ'.store) : OneEigInput H' qs h qw lam f μ' := by
  obtain ⟨hl, hr, hA, -, hq⟩ := hin
  have hA' := hA
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true] at hA'
  refine ⟨fun x hx => hfr.length_eq ▸ hl x hx, ?_, hA, hH', ?_⟩
  · simpa only [Mem.Room, hfr.len_eq] using hr
  · exact hfr.keep (Store.readsOnly_readBlock _ _ _ _) hA'.1.1 hq

/-- From the input of `OneEig` to the input of `Decouple`: after a run that writes only the pair
`lam` and the flag and stores the point $z$ in the pair, `NLAlib.SmallEig.DecoupleInput` holds with
the shift $z$. -/
theorem OneEigInput.decoupleInput_of_eqOff {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} {h qw lam f : ℕ × ℕ} {μ μ' : Mem ℝ} {z : ℂ}
    (hin : OneEigInput H qs h qw lam f μ)
    (hfr : μ.store.EqOff (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1) μ'.store)
    (hz : μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im]) :
    DecoupleInput H z qs h lam qw f μ' := by
  obtain ⟨d1, d2, -⟩ := hin.disj
  obtain ⟨hl, hr, hA, hH, hq⟩ := hin
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true] at hA
  obtain ⟨⟨hhq, hhl, hhf⟩, ⟨hql, hqf⟩, hlf⟩ := hA
  refine ⟨fun x hx => ?_, ?_, ?_, hH.of_eqOff hfr d1, hz,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) d2 hq⟩
  · have := hl x (by simp only [List.mem_cons] at hx ⊢; tauto)
    exact hfr.length_eq ▸ this
  · simp only [Mem.Room, ← hfr.len_eq] at hr ⊢
    exact ⟨hr.1, hr.2.2.1, hr.2.1, hr.2.2.2⟩
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨hhl, hhq, hhf⟩, ⟨hql.symm, hlf⟩, hqf⟩

omit [Has SampleOp O] [Has IdxTst Q] in
/-- **`OneEig` inside the decoupler** ([BanksGarzaVargasSrivastava2025, Proposition 3.5] at the
parameters of `NLAlib.SmallEig.smallEigParams`): on a block of order $n + 1$,
$1 \le n \le n_{\max}$, after `RHess` (upper Hessenberg, condition at most $4B_c$, separation
$g_c/4$, last-row weights at least $p$, norm at most
$2\Sigma(1 + 200(n_{\max} + 1)^2\boldsymbol{u})$), `OneEig` with the cap words $m = 2^q$, $q$,
$t$ sets the flag to $0$ and stores a point at distance between $\eta_1$ and
$\beta'$ from the spectrum, except with probability at most $\varphi_D/2$. -/
theorem smallEigDecoupler_oneEig_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M 1) (hC : IsCmp id I) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn1 : 1 ≤ nmax)
    {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {n : ℕ} (hn : 1 ≤ n) (hnn : n ≤ nmax)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    (hH : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ 4 * smallEigCondition nmax S δ φ c₂)
    (hgap : ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ / 4 ≤ ‖d i - d j‖)
    (hw : ∀ i, smallEigWeight nmax S δ φ c₂ ≤ lastRowWeights V i)
    (hHS : specNorm H ≤ 2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u)) {h qw lam f : ℕ × ℕ} :
    PWrites law I (oneEig (O := O) (Q := Q)).body
      (Env.frame [n + 1, 2 ^ smallEigDegreeLog nmax S δ φ c₂, smallEigDegreeLog nmax S δ φ c₂,
        smallEigRounds nmax S δ φ c₁ c₂] [h, qw, lam, f])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1)
      (OneEigInput H (smallEigParams nmax S δ φ c₁ c₂) h qw lam f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ z : ℂ,
        μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im] ∧
        smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ ⨅ i, ‖z - d i‖ ∧
        ⨅ i, ‖z - d i‖ ≤ smallEigAccuracy nmax S δ φ c₁ c₂)
      (smallEigDecouplerFailure nmax φ / 2) := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hS0 : 0 < S := hδ.trans_le hδS
  have hn' : (1 : ℝ) ≤ nmax := by exact_mod_cast hn1
  have hnn' : (n : ℝ) ≤ nmax := by exact_mod_cast hnn
  obtain ⟨ha, -, -, hd, he, -, -⟩ := smallEigDecoupler_precision hb₁ hb₂ hn1 hδ hδS hφ hφ1 hu
  obtain ⟨hβ, hβS⟩ := smallEigAccuracy_le hb₁ hb₂ hn1 hδ hδS hφ hφ1
  have hsep := smallEigSeparation_pos hb₁ hn1 hS0.le hδ hφ hφ1
  have hBc := smallEigCondition_ge hb₂ hn1 hS0.le hδ hφ hφ1
  obtain ⟨hp0, -⟩ := smallEigWeight_pos_le hb₂ hn1 hS0.le hδ hφ hφ1
  have hη₁ := smallEigInnerRadius_pos hb₁ hb₂ hn1 hδ hδS hφ hφ1
  have hD : 0 < smallEigDecouplerFailure nmax φ / 2 := by
    unfold smallEigDecouplerFailure; positivity
  have hD1 : smallEigDecouplerFailure nmax φ / 2 ≤ 1 := by
    unfold smallEigDecouplerFailure
    rw [div_div, div_le_one (by positivity)]; nlinarith
  have hη₁6 := oneEigInnerRadius_le hβ hβS
    (by positivity : 0 < smallEigSeparation nmax S δ φ c₁ / 4) hD1
  have hη₂β : smallEigOuterRadius nmax S δ φ c₁ c₂ ≤ smallEigAccuracy nmax S δ φ c₁ c₂ / 40 :=
    min_le_left _ _
  have hη₁S : smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ S := by
    change oneEigInnerRadius _ _ _ _ ≤ S at *
    unfold smallEigOuterRadius at hη₂β
    linarith
  obtain ⟨h1, h2, h3⟩ := smallEigDecoupler_oneEig_precision
    (m := 2 ^ smallEigDegreeLog nmax S δ φ c₂) hnn hu0 hS0 hη₁ hη₁S (by linarith)
    (specNorm_nonneg H) hHS ha he
  have hm : distSpecDegree (4 * smallEigCondition nmax S δ φ c₂) (smallEigWeight nmax S δ φ c₂)
      ≤ 2 ^ smallEigDegreeLog nmax S δ φ c₂ := by
    refine le_trans ?_ (distSpecDegree_le_two_pow_smallEigDegreeLog nmax S δ φ c₂)
    unfold distSpecDegree
    exact Nat.ceil_mono (by
      linarith [Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity)
        (by linarith : 4 * smallEigCondition nmax S δ φ c₂ ≤ 8 * smallEigCondition nmax S δ φ c₂)])
  have hnu : ((n : ℝ) + 1) * u ≤ 1 / 2500 := by nlinarith
  have hum : 30000 * (((2 ^ smallEigDegreeLog nmax S δ φ c₂ : ℕ) : ℝ) + 1) * u ≤ 1 := by
    push_cast; exact hd
  exact oneEig_pwrites_of_norm_le hS hM hL hNat hC hI hloc hDisk hU hn hH hV hHV hκ hp0 hw
    (by positivity) hgap hHS h1 h2 hβ hβS hD hD1 rfl hm rfl rfl rfl hnu hum h3
    (by simp [smallEigParams, smallEigOuterRadius]) (by simp [smallEigParams])
    (by simp [smallEigParams])

/-- The backward errors of `RHess` and `Decouple` add up to
`NLAlib.SmallEig.smallEigDecoupleError`: for a block of order $k + 2 \le n_{\max} + 1$ and norm at
most $N$, an error $\varepsilon_1 \le 200(n_{\max} + 1)^2\boldsymbol{u}N$ and a block after
`RHess` of norm at most $2N$. -/
theorem smallEigDecoupleError_le {nmax k : ℕ} (hk : k + 1 ≤ nmax) {S δ φ : ℝ}
    {c₂ : PolyLogTail} {u N ε₁ Hn : ℝ} (hu0 : 0 ≤ u) (hN0 : 0 ≤ N)
    (hH : Hn ≤ 2 * N) (hε₁ : ε₁ ≤ 200 * ((nmax : ℝ) + 1) ^ 2 * u * N) :
    ε₁ + (1 + 10) * Hn * ((1 + 300 * ((k : ℝ) + 2) ^ 2 * u) ^
      smallEigDecoupleSteps nmax S δ φ c₂ - 1) ≤ smallEigDecoupleError nmax S δ φ c₂ u N := by
  unfold smallEigDecoupleError
  set m := smallEigDecoupleSteps nmax S δ φ c₂
  have hk' : (k : ℝ) + 2 ≤ nmax + 1 := by
    have : ((k + 1 : ℕ) : ℝ) ≤ nmax := by exact_mod_cast hk
    push_cast at this; linarith
  have hpow : (1 + 300 * ((k : ℝ) + 2) ^ 2 * u) ^ m ≤ (1 + 300 * ((nmax : ℝ) + 1) ^ 2 * u) ^ m := by
    gcongr
  have h1 : 1 ≤ (1 + 300 * ((k : ℝ) + 2) ^ 2 * u) ^ m :=
    one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  have h2 : (1 + 10) * Hn * ((1 + 300 * ((k : ℝ) + 2) ^ 2 * u) ^ m - 1) ≤
      11 * (2 * N) * ((1 + 300 * ((nmax : ℝ) + 1) ^ 2 * u) ^ m - 1) := by
    norm_num
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

/-- The level of `Decouple`: from $(1 - \boldsymbol{u})a \le \sqrt{2\omega^2}$ with
$\omega > 0$ and $\boldsymbol{u} \le 1/100$, $a \le 1.5\,\omega$. -/
theorem le_of_sub_mul_le_sqrt {ω u a : ℝ} (hω : 0 < ω) (hu : u ≤ 1 / 100)
    (h : (1 - u) * a ≤ √(2 * ω ^ 2)) : a ≤ 1.5 * ω := by
  have hsq : √(2 * ω ^ 2) ≤ 1.42 * ω := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  by_contra hlt
  push Not at hlt
  have : 0.99 * (1.5 * ω) ≤ (1 - u) * a :=
    mul_le_mul (by linarith) hlt.le (by positivity) (by linarith)
  linarith

/-- The side conditions of `NLAlib.SmallEig.decoupleLast_spec` inside the decoupler, at the
condition $4B_c$ and the shift reach $C = 10$: let $\mathbf{H}_1$ of order $k + 2 \le n_{\max} + 1$
be a perturbed unitary similarity with error at most $200(n_{\max} + 1)^2\boldsymbol{u}N$ of a
block of norm at most $N \le 2\Sigma$, with a diagonalization of separation $g_c/4$, and let $z$ be
at distance between $\eta_1$ and $\beta'$ from its eigenvalues. Then $\mathbf{H}_1 \ne 0$,
$\|\mathbf{H}_1\|_2 \le 2N$, $\lvert z\rvert \le 10\|\mathbf{H}_1\|_2$, $z$ is at distance at least
$\eta_1$ from every eigenvalue and within $\beta'$ of one, and the precision conditions hold for
every step count $\ell \le m_2$. -/
theorem smallEigDecoupler_decouple_conditions {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b)
    (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn1 : 1 ≤ nmax) {S δ φ u : ℝ} (hu0 : 0 ≤ u) (hδ : 0 < δ)
    (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {k : ℕ}
    (hk : k + 1 ≤ nmax) {N ε₁ : ℝ} {H H₁ V : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ}
    {d : Fin (k + 1 + 1) → ℂ} (hHN : specNorm H ≤ N) (hN : N ≤ 2 * S)
    (hH₁ : IsPerturbedUnitarySimilar H H₁ ε₁) (hε₁ : ε₁ ≤ 200 * ((nmax : ℝ) + 1) ^ 2 * u * N)
    (hV : IsUnit V) (hHV : H₁ * V = V * Matrix.diagonal d)
    (hgap : ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ / 4 ≤ ‖d i - d j‖) {z : ℂ}
    (hz1 : smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ ⨅ i, ‖z - d i‖)
    (hz2 : ⨅ i, ‖z - d i‖ ≤ smallEigAccuracy nmax S δ φ c₁ c₂) :
    H₁ ≠ 0 ∧ specNorm H₁ ≤ 2 * N ∧ ‖z‖ ≤ 10 * specNorm H₁ ∧
      (∀ j, smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ ‖d j - z‖) ∧
      (∃ i, ‖z - d i‖ ≤ smallEigAccuracy nmax S δ φ c₁ c₂) ∧
      (∀ ℓ ≤ smallEigDecoupleSteps nmax S δ φ c₂, 300 * ((k : ℝ) + 2) ^ 2 * u ≤
        (16 * (4 * smallEigCondition nmax S δ φ c₂))⁻¹ *
          (smallEigInnerRadius nmax S δ φ c₁ c₂ / ((2 + 2 * 10) * specNorm H₁)) ^ ℓ) ∧
      ∀ ℓ ≤ smallEigDecoupleSteps nmax S δ φ c₂, (66 + 2 * 10) *
        (4 * smallEigCondition nmax S δ φ c₂) * specNorm H₁ *
        ((2 + 2 * 10) * specNorm H₁ / smallEigInnerRadius nmax S δ φ c₁ c₂) ^ ℓ *
        √((k : ℝ) + 2) * (300 * ((k : ℝ) + 2) ^ 2 * u) ≤ smallEigOmega nmax S δ φ c₁ c₂ / 2 := by
  have hS0 : 0 < S := hδ.trans_le hδS
  have hn' : (1 : ℝ) ≤ nmax := by exact_mod_cast hn1
  obtain ⟨ha, -, -, -, -, hf, hg⟩ := smallEigDecoupler_precision hb₁ hb₂ hn1 hδ hδS hφ hφ1 hu
  obtain ⟨-, -, -, -, -, -, hω, -, hωB, hβS, -⟩ := smallEigParams_spec hb₁ hb₂ hn1 hδ hδS hφ hφ1
  have hβ : smallEigAccuracy nmax S δ φ c₁ c₂ = smallEigOmega nmax S δ φ c₁ c₂ / 20 := rfl
  have hsep := smallEigSeparation_pos hb₁ hn1 hS0.le hδ hφ hφ1
  have hBc := smallEigCondition_ge hb₂ hn1 hS0.le hδ hφ hφ1
  have hη₁ := smallEigInnerRadius_pos hb₁ hb₂ hn1 hδ hδS hφ hφ1
  have hD1 : smallEigDecouplerFailure nmax φ / 2 ≤ 1 := by
    unfold smallEigDecouplerFailure
    rw [div_div, div_le_one (by positivity)]; nlinarith
  have hη₁6 := oneEigInnerRadius_le (by linarith) hβS
    (by positivity : 0 < smallEigSeparation nmax S δ φ c₁ / 4) hD1
  have hη₂g : smallEigOuterRadius nmax S δ φ c₁ c₂ ≤ smallEigSeparation nmax S δ φ c₁ / 4 / 3 :=
    min_le_right _ _
  have hη₂β : smallEigOuterRadius nmax S δ φ c₁ c₂ ≤ smallEigAccuracy nmax S δ φ c₁ c₂ / 40 :=
    min_le_left _ _
  change oneEigInnerRadius _ _ _ _ ≤ _ at hη₁6
  unfold smallEigOuterRadius at hη₂g hη₂β
  change smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ _ at hη₁6
  have hN0 : 0 ≤ N := (specNorm_nonneg H).trans hHN
  have hx : 200 * ((nmax : ℝ) + 1) ^ 2 * u ≤ 1 := by linarith
  have hH₁N : specNorm H₁ ≤ N * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u) := by
    have := hH₁.specNorm_le; nlinarith
  have hlast : (0 : Fin (k + 1 + 1)) ≠ Fin.last (k + 1) := fun h => by
    have := congrArg Fin.val h; simp at this
  have hdH : ∀ i, ‖d i‖ ≤ specNorm H₁ := norm_le_specNorm_of_mul_eq_mul_diagonal hV hHV
  have hlow : smallEigSeparation nmax S δ φ c₁ / 8 ≤ specNorm H₁ := by
    have h1 := hgap 0 (Fin.last (k + 1)) hlast
    have h2 := norm_sub_le (d 0) (d (Fin.last (k + 1)))
    linarith [hdH 0, hdH (Fin.last (k + 1))]
  obtain ⟨hxu, hfwd⟩ := smallEigDecoupler_decouple_precision hk hu0 hS0 hη₁ (by linarith)
    hBc (by linarith) (hH₁N.trans (by gcongr)) hf hg
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => ‖z - d i‖)
  have hzi : ‖z - d i‖ ≤ smallEigAccuracy nmax S δ φ c₁ c₂ := hi ▸ hz2
  refine ⟨fun h0 => by rw [h0, specNorm_zero] at hlow; linarith,
    by have := mul_le_mul_of_nonneg_left hx hN0; linarith, ?_,
    fun j => by rw [norm_sub_rev]; exact hz1.trans (ciInf_le (Finite.bddBelow_range _) j),
    ⟨i, hzi⟩, hxu, hfwd⟩
  have := norm_le_insert' z (d i)
  have h3 : 2 * (2.25 * smallEigOmega nmax S δ φ c₁ c₂) ≤ smallEigSeparation nmax S δ φ c₁ := by
    have : smallEigSeparation nmax S δ φ c₁ /
        (16 * nmax * smallEigCondition nmax S δ φ c₂) ≤ smallEigSeparation nmax S δ φ c₁ :=
      div_le_self hsep.le (by nlinarith)
    have := mul_le_mul_of_nonneg_right hn'
      (by positivity : (0 : ℝ) ≤ 2 * (2.25 * smallEigOmega nmax S δ φ c₁ c₂))
    linarith
  linarith [hdH i, specNorm_nonneg H₁]

omit [Has SampleOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- **`Decouple` inside the decoupler** ([BanksGarzaVargasSrivastava2025, Proposition 4.3] at the
parameters of `NLAlib.SmallEig.smallEigParams`; deterministic): let $\mathbf{H}_1$ of order
$k + 2 \le n_{\max} + 1$ be the block after `RHess`, a perturbed unitary similarity with error at
most $200(n_{\max} + 1)^2\boldsymbol{u}N$ of a block $\mathbf{H}$ of norm at most $N \le 2\Sigma$,
upper Hessenberg with condition at most $4B_c$, separation $g_c/4$ and last-row weights at least
$p$, and let the shift $z$ of `OneEig` be at distance between $\eta_1$ and $\beta'$ from the
spectrum. Then on every tape `Decouple` sets the flag to $0$ and stores an upper Hessenberg
perturbed unitary similarity of $\mathbf{H}$ with the error `NLAlib.SmallEig.smallEigDecoupleError`
at $N$ whose last subdiagonal entry is at most $1.5\,\omega$. -/
theorem smallEigDecoupler_decouple_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn1 : 1 ≤ nmax)
    (hNat : IsExactNatLit id M (nmax + 1)) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {k : ℕ} (hk : k + 1 ≤ nmax) {N ε₁ : ℝ}
    {H H₁ V : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ} {d : Fin (k + 1 + 1) → ℂ}
    (hHN : specNorm H ≤ N) (hN : N ≤ 2 * S) (hH₁ : IsPerturbedUnitarySimilar H H₁ ε₁)
    (hε₁ : ε₁ ≤ 200 * ((nmax : ℝ) + 1) ^ 2 * u * N)
    (hHess : IsUpperHessenberg H₁) (hV : IsUnit V) (hHV : H₁ * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ 4 * smallEigCondition nmax S δ φ c₂)
    (hgap : ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ / 4 ≤ ‖d i - d j‖)
    (hw : ∀ i, smallEigWeight nmax S δ φ c₂ ≤ lastRowWeights V i) {z : ℂ}
    (hz1 : smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ ⨅ i, ‖z - d i‖)
    (hz2 : ⨅ i, ‖z - d i‖ ≤ smallEigAccuracy nmax S δ φ c₁ c₂) {τ : Tape ℝ} {μ : Mem ℝ}
    {h lam qw f : ℕ × ℕ}
    (hin : DecoupleInput H₁ z (smallEigParams nmax S δ φ c₁ c₂) h lam qw f μ) :
    Writes .total I τ (decoupleLast (O := O) (Q := Q)).body
      (Env.frame [k + 1 + 1, smallEigDecoupleSteps nmax S δ φ c₂] [h, lam, qw, h, f])
      (Store.inBlock h.1 h.2 (2 * ((k + 1 + 1) * (k + 1 + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ H' : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ,
        IsPerturbedUnitarySimilar H H' (smallEigDecoupleError nmax S δ φ c₂ u N) ∧
        IsUpperHessenberg H' ∧
        (∃ i : Fin (k + 1), k + 1 ≤ (i : ℕ) + 1 ∧
          ‖H' i.succ i.castSucc‖ ≤ 1.5 * smallEigOmega nmax S δ φ c₁ c₂) ∧
        HoldsMatrix h H' μ'.store) μ := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  obtain ⟨hH0, hH₁2, hζ, hdist, ⟨i, hzi⟩, hxu, hfwd⟩ := smallEigDecoupler_decouple_conditions
    hb₁ hb₂ hn1 hu0 hδ hδS hφ hφ1 hu hk hHN hN hH₁ hε₁ hV hHV hgap hz1 hz2
  obtain ⟨ha, -⟩ := smallEigDecoupler_precision hb₁ hb₂ hn1 hδ hδS hφ hφ1 hu
  obtain ⟨-, -, -, -, -, -, hω, -, -, -, hp0, -, -, hm₂B⟩ :=
    smallEigParams_spec hb₁ hb₂ hn1 hδ hδS hφ hφ1
  have hnsq : (1 : ℝ) ≤ ((nmax : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ nmax := nmax.cast_nonneg; nlinarith
  have hu' : u ≤ 1 / 100 := by
    have := le_mul_of_one_le_left hu0 hnsq; linarith
  have hN0 : 0 ≤ N := (specNorm_nonneg H).trans hHN
  have hm₂ : 1 ≤ smallEigDecoupleSteps nmax S δ φ c₂ := by
    unfold smallEigDecoupleSteps decoupleSteps; omega
  have hβ : smallEigAccuracy nmax S δ φ c₁ c₂ = smallEigOmega nmax S δ φ c₁ c₂ / 20 := rfl
  have hBc := smallEigCondition_ge hb₂ hn1 (hδ.le.trans hδS) hδ hφ hφ1
  have h7 : (smallEigParams nmax S δ φ c₁ c₂).getD 7 0 = 2 * smallEigOmega nmax S δ φ c₁ c₂ ^ 2 :=
    by simp [smallEigParams]
  have htL : (1 + u) ^ 2 * smallEigOmega nmax S δ φ c₁ c₂ ^ 2 ≤
      (smallEigParams nmax S δ φ c₁ c₂).getD 7 0 := by
    rw [h7]
    have : (1 + u) ^ 2 ≤ 2 := by
      have := mul_le_mul hu' hu' hu0 (by norm_num : (0 : ℝ) ≤ 1 / 100)
      ring_nf; linarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hres := decoupleLast_spec (n := k) (C := 10) (B := 4 * smallEigCondition nmax S δ φ c₂)
    (O := O) (Q := Q) (τ := τ) hS hM (by linarith) hL hC (hNat.mono (by omega)) hHess hH0 hV
    hHV hκ (by norm_num) hζ (smallEigInnerRadius_pos hb₁ hb₂ hn1 hδ hδS hφ hφ1) hdist hzi hp0
    (hw i) (by rw [hβ]; linarith) hm₂ (by linarith) hxu hfwd (by simp [smallEigParams]) htL hin
  have e : Env.frame [k + 2, smallEigDecoupleSteps nmax S δ φ c₂] [h, lam, qw, h, f] =
      Env.frame [k + 1 + 1, smallEigDecoupleSteps nmax S δ φ c₂] [h, lam, qw, h, f] :=
    congrArg (fun x => Env.frame [x, smallEigDecoupleSteps nmax S δ φ c₂] [h, lam, qw, h, f])
      (by omega)
  have eF : Store.inBlock h.1 h.2 (2 * ((k + 2) * (k + 2))) =
      Store.inBlock h.1 h.2 (2 * ((k + 1 + 1) * (k + 1 + 1))) :=
    congrArg (fun x => Store.inBlock h.1 h.2 (2 * (x * x))) (by omega)
  rw [e, eF] at hres
  refine hres.mono le_rfl ?_
  rintro μ' - ⟨hf0, H', hPUS, hHess', hW, hsub⟩
  refine ⟨hf0, H', (hH₁.trans hPUS).mono (smallEigDecoupleError_le hk hu0 hN0 hH₁2 hε₁),
    hHess', ⟨Fin.last k, by simp, ?_⟩, hW⟩
  rw [h7] at hsub
  rw [Fin.succ_last]
  exact le_of_sub_mul_le_sqrt hω hu' hsub

omit [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q] in
/-- The index binder at a known value: if from every memory of the precondition the index
query returns the same number $v \le B$, the binder fails with the probability of its body at
$v$. -/
theorem pwrites_bindIdx_of_index_eq {K : Type} [Inhabited K] [MeasurableSpace K]
    {law : ℕ → Measure K} {I : Interp O Q K} (hI : I.IsMeasurable) {ρ : Env} {F : Fp}
    {Pre Post : Mem K → Prop} {φ : ℝ} {q : Q} {ins : List Operand} {bound : IExp}
    {body : Stmt O Q} {a : List (ℕ × ℕ)} {B v : ℕ} (ha : Operand.evalList ρ ins = some a)
    (hB : bound.eval ρ.idx = some B) (hvB : v ≤ B) (hidx : ∀ m, Pre m → I.index q a m = some v)
    (hφ : 0 ≤ φ) (h : PWrites law I body (ρ.pushIdx v) F Pre Post φ) :
    PWrites law I (.bindIdx q ins bound body) ρ F Pre Post φ := by
  refine PWrites.bindIdx hI ha hB (fun m hm => ⟨v, hvB, hidx m hm⟩) fun v' _ => ?_
  by_cases hv : v' = v
  · subst hv; exact h.mono (fun m hm => hm.1) le_rfl (fun _ h => h) le_rfl
  · exact PWrites.of_writes hφ fun m τ hm => by
      have := hm.2.symm.trans (hidx m hm.1); simp at this; omega

/-- The blocks after `RHess` inside the decoupler: $\mathbf{H}_1$ is upper Hessenberg, a perturbed
unitary similarity of the block $\mathbf{H}$ with the error $\varepsilon$, and has a diagonalization
with condition at most $4B_c$, separation $g_c/4$ and last-row weights at least $p$. -/
def SmallEigRHessClass (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ε : ℝ) (H₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Prop :=
  IsUpperHessenberg H₁ ∧ IsPerturbedUnitarySimilar H H₁ ε ∧
    ∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
      IsUnit V ∧ H₁ * V = V * Matrix.diagonal d ∧
      pseudoConditionNumber V ≤ 4 * smallEigCondition nmax S δ φ c₂ ∧
      (∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ / 4 ≤ ‖d i - d j‖) ∧
      ∀ i, smallEigWeight nmax S δ φ c₂ ≤ lastRowWeights V i

omit [Has IndexOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- **`RHess` inside the decoupler** ([BanksGarzaVargasSrivastava2025, Proposition 5.3] at the
parameters of `NLAlib.SmallEig.smallEigParams`): on a block of order $n + 1 \le n_{\max} + 1$ and
norm at most $N \le 2\Sigma$ in the class $(2B_c, g_c/2)$, `RHess` stores a block in
`NLAlib.SmallEig.SmallEigRHessClass` with the error $200(n + 1)^2\boldsymbol{u}N$, except with
probability at most $\varphi_D/2$. -/
theorem smallEigDecoupler_rhess_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hzero : M.lit 0 = 0) (hC : IsCmp id I)
    (hSmp : IsSample I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {sG : ℕ}
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {n : ℕ} (hnn : n ≤ nmax) {N : ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hN : N ≤ 2 * S)
    (hHN : specNorm H ≤ N) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ 2 * smallEigCondition nmax S δ φ c₂)
    (hgap : ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ / 2 ≤ ‖d i - d j‖) {w : ℕ × ℕ} :
    PWrites law I (rhess (O := O) (Q := Q) sG).body (Env.frame [n + 1] [w, w])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (fun μ => HoldsMatrix w H μ.store ∧ μ.Live [w])
      (fun μ' => ∃ H₁, HoldsMatrix w H₁ μ'.store ∧
        SmallEigRHessClass nmax S δ φ c₁ c₂ H (200 * ((n : ℝ) + 1) ^ 2 * u * N) H₁)
      (smallEigDecouplerFailure nmax φ / 2) := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hS0 : 0 < S := hδ.trans_le hδS
  have hN0 : 0 ≤ N := (specNorm_nonneg H).trans hHN
  have hBc := smallEigCondition_ge hb₂ hn hS0.le hδ hφ hφ1
  have hsep := smallEigSeparation_pos hb₁ hn hS0.le hδ hφ hφ1
  have hgcS : smallEigSeparation nmax S δ φ c₁ ≤ S := by
    obtain ⟨-, hg⟩ := smallEigGap_pos_le hb₁ hn hS0.le hδ hφ hφ1
    have hW : 3 ≤ smallEigNoiseLevel φ := by
      unfold smallEigNoiseLevel; linarith [Real.sqrt_nonneg (Real.log (4 / φ))]
    have hγ := smallEigScale_mul_noiseLevel δ φ
    have hγ0 := (smallEigScale_pos (φ := φ) hδ).le
    have := mul_le_mul_of_nonneg_left hW hγ0
    unfold smallEigSeparation; linarith
  obtain ⟨ha, hb, hc, -, -, -, -⟩ := smallEigDecoupler_precision hb₁ hb₂ hn hδ hδS hφ hφ1 hu
  obtain ⟨hs, hR, hpw, hsp, hRr, hfail⟩ := smallEigDecoupler_rhess_params hn hnn
    hφ hφ1 (by linarith) S δ c₂ rfl
  obtain ⟨hnu, hus, huc⟩ := smallEigDecoupler_rhess_precision hnn hu0 hN0 hN hsep hgcS hBc hs hR
    hsp ha hb hc
  have hφD : 0 < smallEigDecouplerFailure nmax φ := by unfold smallEigDecouplerFailure; positivity
  have hφD1 : smallEigDecouplerFailure nmax φ ≤ 1 := by
    unfold smallEigDecouplerFailure; rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
    nlinarith
  exact (rhess_pwrites (a := w) hS hM hzero hC hSmp hI hloc hG hV hHV hκ (by positivity)
    hgap hHN hs (φ' := smallEigDecouplerFailure nmax φ / 4) (by positivity) (by linarith) hRr
    hnu hus huc).mono (fun _ h => h) le_rfl
    (fun μ' ⟨H₁, V', d', hW₁, hHess₁, hPUS₁, hV', hHV', hκ', hgap', hw'⟩ =>
      ⟨H₁, hW₁, hHess₁, hPUS₁, V', d', hV', hHV', by linarith,
        fun i j hij => by linarith [hgap' i j hij], fun i => hpw ▸ hw' i⟩) hfail

omit [Has SampleOp O] [Has IdxTst Q] in
/-- The tail of the decoupler (`OneEig`, then `Decouple` on the flag $0$): from a block
$\mathbf{H}_1$ in `NLAlib.SmallEig.SmallEigRHessClass` of a block $\mathbf{H}$ of order
$k + 2 \le n_{\max} + 1$ and norm at most $N \le 2\Sigma$, with the pair at `(L, 0)`, the tail of
`NLAlib.SmallEig.smallEigDecoupler` reaches the outcome of the decoupling contract, except with
probability at most $\varphi_D/2$. The frames are given by their evaluations. -/
theorem smallEigDecoupler_tail_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    (hU : law sU = volume.restrict (Set.Icc 0 1)) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b)
    (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : 1 ≤ nmax) (hNat : IsExactNatLit id M (nmax + 1))
    {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {k : ℕ} (hnn : k + 1 ≤ nmax) {N : ℝ}
    {H H₁ : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ} (hHN : specNorm H ≤ N) (hN : N ≤ 2 * S)
    (hx : SmallEigRHessClass nmax S δ φ c₁ c₂ H (200 * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 * u * N) H₁)
    {ρ : Env} {ds₁ ds₂ : List IExp} {args₁ tins args₂ : List Operand} {w q f : ℕ × ℕ} {L : ℕ}
    (hd₁ : IExp.evalList ρ.idx ds₁ = some [k + 1 + 1, 2 ^ smallEigDegreeLog nmax S δ φ c₂,
      smallEigDegreeLog nmax S δ φ c₂, smallEigRounds nmax S δ φ c₁ c₂])
    (ha₁ : Operand.evalList ρ args₁ = some [w, q, (L, 0), f])
    (ht : Operand.evalList ρ tins = some [f])
    (hd₂ : IExp.evalList ρ.idx ds₂ = some [k + 1 + 1, smallEigDecoupleSteps nmax S δ φ c₂])
    (ha₂ : Operand.evalList ρ args₂ = some [w, (L, 0), q, w, f]) :
    PWrites law I ((Stmt.frame ds₁ args₁ (oneEig (O := O) (Q := Q)).body).seq
        (Stmt.ite (Has.inj CmpTst.isZero) [] tins
          (Stmt.frame ds₂ args₂ (decoupleLast (O := O) (Q := Q)).body) Stmt.skip)) ρ
      (Store.inBlock L 0 2 ⊔ Store.inBlock f.1 f.2 1 ⊔
        (Store.inBlock w.1 w.2 (2 * ((k + 1 + 1) * (k + 1 + 1))) ⊔ Store.inBlock f.1 f.2 1))
      (OneEigInput H₁ (smallEigParams nmax S δ φ c₁ c₂) w q (L, 0) f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ H' : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ,
        IsPerturbedUnitarySimilar H H' (smallEigDecoupleError nmax S δ φ c₂ u N) ∧
        IsUpperHessenberg H' ∧
        (∃ i : Fin (k + 1), k + 1 ≤ (i : ℕ) + 1 ∧
          ‖H' i.succ i.castSucc‖ ≤ 1.5 * smallEigOmega nmax S δ φ c₁ c₂) ∧
        HoldsMatrix w H' μ'.store) (smallEigDecouplerFailure nmax φ / 2) := by
  obtain ⟨hHess₁, hPUS₁, V', d', hV', hHV', hκ', hgap', hw'⟩ := hx
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hsq : (((k + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ ((nmax : ℝ) + 1) ^ 2 := by
    have : ((k + 1 : ℕ) : ℝ) ≤ nmax := by exact_mod_cast hnn
    gcongr
  have hε₁ : 200 * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 * u * N ≤ 200 * ((nmax : ℝ) + 1) ^ 2 * u * N := by
    have := (specNorm_nonneg H).trans hHN
    gcongr
  have hH₁S : specNorm H₁ ≤ 2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u) := by
    have h1 := hPUS₁.specNorm_le
    have h2 : 200 * ((nmax : ℝ) + 1) ^ 2 * u * N ≤ 200 * ((nmax : ℝ) + 1) ^ 2 * u * (2 * S) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    nlinarith
  have hA := smallEigDecoupler_oneEig_pwrites (O := O) (Q := Q) hS hM hL
    (hNat.mono (by omega)) hC hI hloc hDisk hU hb₁ hb₂ hn hδ hδS hφ hφ1 hu (n := k + 1)
    (by omega) hnn hHess₁ hV' hHV' hκ' hgap' hw' hH₁S (h := w) (qw := q) (lam := (L, 0)) (f := f)
  refine (PWrites.seq (Mid := fun μ₂ => μ₂.store.get f.1 f.2 = some 0 ∧ ∃ z : ℂ,
      DecoupleInput H₁ z (smallEigParams nmax S δ φ c₁ c₂) w (L, 0) q f μ₂ ∧
      smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ ⨅ i, ‖z - d' i‖ ∧
      ⨅ i, ‖z - d' i‖ ≤ smallEigAccuracy nmax S δ φ c₁ c₂)
    hI hloc le_rfl ((hA.mono_eqOff (fun _ h => h)
      (fun μ μ' hμ hfr ⟨hf0, z, hz, hz1, hz2⟩ =>
        ⟨hf0, z, hμ.decoupleInput_of_eqOff hfr hz, hz1, hz2⟩)).in_frame hd₁ ha₁
        (fun μ hμ => hμ.1))
    (PWrites.of_writes (F := Store.inBlock w.1 w.2 (2 * ((k + 1 + 1) * (k + 1 + 1))) ⊔
      Store.inBlock f.1 f.2 1) le_rfl fun μ₂ τ ⟨hf0, z, hdin, hz1, hz2⟩ => ?_)).mono
    (fun _ h => h) le_rfl (fun _ h => h) (by simp)
  refine writes_ite (a := [f]) rfl ht (hC.test_isZero hf0) ?_
  simp only [id, decide_true, if_true]
  exact (smallEigDecoupler_decouple_writes (O := O) (Q := Q) hS hM hL hC hb₁ hb₂ hn hNat hδ
    hδS hφ hφ1 hu hnn hHN hN hPUS₁ hε₁ hHess₁ hV' hHV' hκ' hgap' hw' hz1 hz2 hdin).in_frame
    hd₂ ha₂ (fun x hx => hdin.1 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto))

/-- The input of `OneEig` after the allocation of the pair: from the memory of the decoupling
contract (`NLAlib.ShiftedQR.RandomDecouplingRoutineContract`) and a store with one fresh buffer of
two words at the handle $L$ = the old buffer count, `NLAlib.SmallEig.OneEigInput` holds with the
pair at `(L, 0)`. -/
theorem OneEigInput.of_alloc {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {qs : List ℝ}
    (hqs : 0 < qs.length) {w q f : ℕ × ℕ} {μ : Mem ℝ} {s₁ : Store ℝ}
    (hW : HoldsMatrix w H μ.store) (hq : μ.store.readBlock q.1 q.2 qs.length = some qs)
    (hl : μ.Live [w, q, w, f]) (hwr : w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1)
    (hfr : f.2 + 1 ≤ μ.store.len f.1)
    (hwf : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hqwf : Fp.Disj (Store.inBlock q.1 q.2 qs.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1))
    (hlen : s₁.length = μ.store.length + 1) (hL2 : s₁.len μ.store.length = 2)
    (hBelow : Store.Below μ.store.length μ.store s₁) :
    OneEigInput H qs w q (μ.store.length, 0) f ⟨s₁, μ.pos⟩ := by
  simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hl
  obtain ⟨hlw, hlq, -, hlf⟩ := hl
  have hq₁ := hBelow.readBlock_of hlq hq
  have hD : ∀ {b o k : ℕ}, b < μ.store.length →
      Fp.Disj (Store.inBlock μ.store.length 0 2) (Store.inBlock b o k) :=
    fun hb => Fp.disj_inBlock_of_ne (by omega)
  have hqw := (hqwf.mono le_rfl le_sup_left).symm
  have hqf := hqwf.mono le_rfl le_sup_right
  refine ⟨by simp [Mem.Live, hlen]; omega, ?_, ?_, hW.of_below hBelow hlw, hq₁⟩
  · simp only [Mem.Room]
    exact ⟨(hBelow w.1 hlw).1 ▸ hwr, Store.le_len_of_readBlock hq₁ hqs, by simp [hL2],
      (hBelow f.1 hlf).1 ▸ hfr, trivial⟩
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨hqw, (hD hlw).symm, hwf⟩, ⟨(hD hlq).symm, hqf⟩, hD hlf⟩

/-- **The decoupler meets the randomized decoupling contract** ([BanksGarzaVargasSrivastava2025,
Theorem 6.1], one node; [BanksGarzaVargasSrivastava2025, Lemma 6.2] carried by the composition):
on a scalar machine with the standard model at $\boldsymbol{u} \le$
`NLAlib.SmallEig.uSmallEig`, $M.\mathrm{lit}(0) = 0$, index literals, exact natural literals up to
$n_{\max} + 1$, exact comparisons and conversion, a measurable interpretation reading the tape
only in its windows whose draws store the tape entry, a stream `sG` with the standard real
Gaussian law and an exact polar sampler on a stream `sU` uniform on $[0, 1]$: for tail records
with $b_1, b_2 > 0$, $1 \le n_{\max}$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$,
`NLAlib.SmallEig.smallEigDecoupler` with the words `NLAlib.SmallEig.smallEigParams` and the cap
`NLAlib.SmallEig.smallEigCap` meets `NLAlib.ShiftedQR.RandomDecouplingRoutineContract` at the
bottom width $1$, any iteration cap, orders up to $n_{\max}$ and norms up to $2\Sigma$, on the
class $(2B_c, g_c/2)$ of the blocks ($B_c, g_c$ = `NLAlib.SmallEig.smallEigCondition`,
`NLAlib.SmallEig.smallEigSeparation`), with failure probability $\varphi_D$ =
`NLAlib.SmallEig.smallEigDecouplerFailure`, the level $1.5\,\omega$ and the backward error
`NLAlib.SmallEig.smallEigDecoupleError`. -/
theorem smallEigDecoupler_randomDecouplingRoutineContract {M : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} (hS : IsScalar M I) (hM : StdModel u id M) (hzero : M.lit 0 = 0)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M (nmax + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) (F : ℕ) :
    RandomDecouplingRoutineContract law (2 * smallEigCondition nmax S δ φ c₂)
      (smallEigSeparation nmax S δ φ c₁ / 2) (smallEigDecouplerFailure nmax φ) 1 F
      (smallEigCap nmax S δ φ c₁ c₂) nmax (2 * S) (smallEigParams nmax S δ φ c₁ c₂)
      (1.5 * smallEigOmega nmax S δ φ c₁ c₂) (smallEigDecoupleError nmax S δ φ c₂ u)
      (smallEigDecoupler (O := O) (Q := Q) sG) I := by
  intro n N w q f H V d hk hnn hN hH hHN hV hHV hκ hgap
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hφD : 0 < smallEigDecouplerFailure nmax φ := by unfold smallEigDecouplerFailure; positivity
  have hRH := smallEigDecoupler_rhess_pwrites (O := O) (Q := Q) (w := w) hS hM hzero hC hSmp hI
    hloc hG hb₁ hb₂ hn hδ hδS hφ hφ1 hu hnn hN hHN hV hHV hκ hgap
  have hget : ∀ μ : Mem ℝ, μ.store.readBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length =
      some (smallEigParams nmax S δ φ c₁ c₂) → ∀ i < 12,
        μ.store.get q.1 (q.2 + i) = some ((smallEigParams nmax S δ φ c₁ c₂).getD i 0) :=
    fun μ hq i hi => Store.get_of_readBlock hq (by simp [smallEigParams]; omega) 0
  unfold smallEigDecoupler
  refine pwrites_bindIdx_of_index_eq hI rfl rfl (le_max_left _ _) (fun μ hμ =>
    hQ.index_eq_of_decode_nat (hget μ hμ.2.1 8 (by omega)) (by simp [smallEigParams])) hφD.le ?_
  refine pwrites_bindIdx_of_index_eq hI rfl rfl Nat.lt_two_pow_self.le (fun μ hμ =>
    hQ.index_eq_of_decode_nat (hget μ hμ.2.1 9 (by omega)) (by simp [smallEigParams])) hφD.le ?_
  refine pwrites_bindIdx_of_index_eq hI rfl rfl ((le_max_left _ _).trans (le_max_right _ _))
    (fun μ hμ => hQ.index_eq_of_decode_nat (hget μ hμ.2.1 10 (by omega))
      (by simp [smallEigParams])) hφD.le ?_
  refine pwrites_bindIdx_of_index_eq hI rfl rfl ((le_max_right _ _).trans (le_max_right _ _))
    (fun μ hμ => hQ.index_eq_of_decode_nat (hget μ hμ.2.1 11 (by omega))
      (by simp [smallEigParams])) hφD.le ?_
  change PWrites law I (Stmt.allocs [.const 2] _) _ _ _ _ _
  refine PWrites.allocs (ns := [2]) rfl
    (Pre₁ := fun L μ => OneEigInput H (smallEigParams nmax S δ φ c₁ c₂) w q (L, 0) f μ)
    (fun μ s₁ ⟨hW, hq, hl, hwr, hfr, hwf, hqwf⟩ hlen hlens hBelow =>
      OneEigInput.of_alloc (by simp [smallEigParams]) hW hq hl hwr hfr hwf hqwf
        (by simpa using hlen) (by simpa using hlens 0 (by simp)) hBelow) ?_ fun L => ?_
  · rintro μ ⟨-, -, hl, -⟩ s s' p hBelow ⟨hf0, H', h1, h2, h3, hW'⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl
    exact ⟨hBelow.get_of hl.2.2.2 hf0, H', h1, h2, h3, hW'.of_below hBelow hl.1⟩
  let ι := {H₁ : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ //
    SmallEigRHessClass nmax S δ φ c₁ c₂ H (200 * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 * u * N) H₁}
  let F₂ : Fp := Store.inBlock L 0 2 ⊔ Store.inBlock f.1 f.2 1 ⊔
    (Store.inBlock w.1 w.2 (2 * ((k + 1 + 1) * (k + 1 + 1))) ⊔ Store.inBlock f.1 f.2 1)
  refine (PWrites.seq (Mid := fun μ => ∃ x : ι,
      OneEigInput x.1 (smallEigParams nmax S δ φ c₁ c₂) w q (L, 0) f μ) (F₂ := F₂)
    (φ₂ := smallEigDecouplerFailure nmax φ / 2) hI hloc (by positivity) ((hRH.mono_eqOff
      (fun μ hμ => ⟨hμ.2.2.2.1, fun x hx => hμ.1 x (by simp at hx ⊢; tauto)⟩)
      (fun μ μ' hμ hfr ⟨H₁, hW₁, hx⟩ => ⟨⟨H₁, hx⟩, hμ.of_eqOff_matrix hfr hW₁⟩)).in_frame rfl rfl
      (fun μ hμ x hx => hμ.1 x (by simp at hx ⊢; tauto))) ?_).mono (fun _ h => h) (by fp_sub)
    (fun _ h => h) (by linarith)
  refine PStep.mono (PWrites.pstep_of_forall hI hloc (F := F₂)
    (P := fun (x : ι) μ => OneEigInput x.1 (smallEigParams nmax S δ φ c₁ c₂) w q (L, 0) f μ)
    (fun x => smallEigDecoupler_tail_pwrites (O := O) (Q := Q) hS hM hL hC hI hloc hDisk hU hb₁
      hb₂ hn hNat hδ hδS hφ hφ1 hu hnn hHN hN x.2 rfl rfl rfl rfl rfl)
    (measurableSet_decoupleOutcome_of H (smallEigDecoupleError nmax S δ φ c₂ u N)
      (1.5 * smallEigOmega nmax S δ φ c₁ c₂) w f F₂) ?_) (fun μ h => h) ?_ le_rfl
  · rintro x μ μ' - hfr ⟨hf0, H', hPUS, hHess, hsm, hW'⟩
    rw [hW'.eq_storedMatrix] at hPUS hHess hsm
    exact ⟨hfr, hf0, fun i hi => by rw [Store.get_of_readBlock hW' hi 0]; rfl, hPUS, hHess, hsm⟩
  · rintro μ μ' - ⟨hfr, hf0, hinit, hPUS, hHess, hsm⟩
    exact ⟨hfr, hf0, _, hPUS, hHess, hsm, holdsMatrix_storedMatrix hinit⟩

/-- The decoupler terminates: on a scalar machine with index literals, exact natural literals
up to $n_{\max} + 1$, exact comparisons and conversion, draws that store the tape entry and an
exact polar sampler, for words `qs` with valid cap words for the cap $T$
(`NLAlib.SmallEig.SmallEigCaps`) and at least twelve words, `NLAlib.SmallEig.smallEigDecoupler`
is a terminating decoupling routine (`NLAlib.ShiftedQR.TerminatingDecouplerRoutine`) at the
bottom width $1$, any iteration cap and orders up to $n_{\max} + 1$. -/
theorem smallEigDecoupler_terminatingDecouplerRoutine {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M (nmax + 1))
    (hC : IsCmp id I) (hQ : IsToNat id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {T F : ℕ} {qs : List ℝ} (hqs : SmallEigCaps T qs)
    (hlen : 12 ≤ qs.length) :
    TerminatingDecouplerRoutine nmax 1 F T qs (smallEigDecoupler (O := O) (Q := Q) sG) I := by
  intro n w q f tape μ H hk hn hW hq hl hwr hfr hwf hqwf
  obtain ⟨m, qq, t, m₂, h8, h9, h10, h11, hmq, hmT, htT, hm2T⟩ := hqs
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hget : ∀ i < qs.length, μ.store.get q.1 (q.2 + i) = some (qs.getD i 0) :=
    fun i hi => Store.get_of_readBlock hq hi 0
  have hlive : w.1 < μ.store.length ∧ q.1 < μ.store.length ∧ f.1 < μ.store.length := by
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl
    exact ⟨hl.1, hl.2.1, hl.2.2.2⟩
  have hqm : qq ≤ m := hmq ▸ Nat.lt_two_pow_self.le
  have hzero : M.lit 0 = 0 := by simpa using hNat 0 (by omega)
  unfold smallEigDecoupler
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 8 (by omega)) (by simpa using h8) hmT ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 9 (by omega)) (by simpa using h9) hqm ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 10 (by omega)) (by simpa using h10) htT ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 11 (by omega)) (by simpa using h11) hm2T ?_
  change Writes .total I tape (Stmt.allocs [.const 2] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2]) rfl (fun hBelow ⟨⟨x, hx⟩, H', hH'⟩ =>
    ⟨⟨x, hBelow.get_of hlive.2.2 hx⟩, H', hH'.of_below hBelow hlive.1⟩) ?_
  intro s₁ hlen hlens hBelow
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  have hL2 : s₁.len L = 2 := by simpa using hlens 0 (by simp)
  have hq₁ := hBelow.readBlock_of hlive.2.1 hq
  have hqr : q.2 + qs.length ≤ s₁.len q.1 := Store.le_len_of_readBlock hq₁ (by omega)
  have hwr₁ : w.2 + 2 * ((n' + 1 + 1) * (n' + 1 + 1)) ≤ s₁.len w.1 := by
    rw [(hBelow w.1 hlive.1).1]; exact hwr
  have hfr₁ : f.2 + 1 ≤ s₁.len f.1 := by rw [(hBelow f.1 hlive.2.2).1]; exact hfr
  have hD : ∀ {b o k : ℕ}, b < L → Fp.Disj (Store.inBlock L 0 2) (Store.inBlock b o k) :=
    fun hb => Fp.disj_inBlock_of_ne (by omega)
  refine (rhess_terminates (τ := tape) (μ := ⟨s₁, μ.pos⟩) hS hC hSmp
    (by simp [Mem.Live, hlen]; omega) (hW.of_below hBelow hlive.1)).frame_seq_le rfl rfl
    (by simp [Mem.Live, hlen]; omega) (by fp_sub) ?_
  rintro μ₁ hfr₁' ⟨H₁, hH₁⟩
  have hqw : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n' + 1 + 1) * (n' + 1 + 1))))
      (Store.inBlock q.1 q.2 qs.length) := (hqwf.mono le_rfl le_sup_left).symm
  have hqf : Fp.Disj (Store.inBlock q.1 q.2 qs.length) (Store.inBlock f.1 f.2 1) :=
    hqwf.mono le_rfl le_sup_right
  have hq₂ := hfr₁'.keep (Store.readsOnly_readBlock _ _ _ _) hqw hq₁
  have hin : OneEigInput H₁ qs w q (L, 0) f μ₁ := by
    refine ⟨by simp [Mem.Live, hfr₁'.length_eq, hlen]; omega, ?_, ?_, hH₁, hq₂⟩
    · simp only [Mem.Room, hfr₁'.len_eq]
      exact ⟨hwr₁, hqr, by rw [hL2], by omega, trivial⟩
    · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
        and_true]
      exact ⟨⟨hqw, (hD hlive.1).symm, hwf⟩, ⟨(hD hlive.2.1).symm, hqf⟩, hD hlive.2.2⟩
  refine (oneEig_terminates (m := m) (q := qq) (t := t) hS hzero hL hC hDisk (by omega)
    hin).frame_seq_le rfl rfl (by simp [Mem.Live, hfr₁'.length_eq, hlen]; omega)
    (by fp_sub) ?_
  rintro μ₂ hfr₂ ⟨⟨z, hz⟩, x, hx⟩
  have hH₂ : HoldsMatrix w H₁ μ₂.store :=
    hH₁.of_eqOff hfr₂ (Fp.disj_sup_left.mpr ⟨hD hlive.1, hwf.symm⟩)
  refine writes_ite (a := [f]) rfl rfl (hC.test_isZero hx) ?_
  split_ifs
  · have hin₂ : DecoupleInput H₁ z qs w (L, 0) q f μ₂ := by
      refine ⟨by simp [Mem.Live, hfr₂.length_eq, hfr₁'.length_eq, hlen]; omega, ?_, ?_, hH₂, hz,
        hfr₂.keep (Store.readsOnly_readBlock _ _ _ _)
          (Fp.disj_sup_left.mpr ⟨hD hlive.2.1, hqf.symm⟩) hq₂⟩
      · simp only [Mem.Room, hfr₂.len_eq, hfr₁'.len_eq]
        exact ⟨hwr₁, by rw [hL2], hqr, by omega, trivial⟩
      · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right,
          Fp.disj_bot_right, and_true]
        exact ⟨⟨(hD hlive.1).symm, hqw, hwf⟩, ⟨hD hlive.2.1, hD hlive.2.2⟩, hqf⟩
    exact ((decoupleLast_terminates (m₂ := m₂) hS hL hC (hNat.mono (by omega)) (by omega)
      hin₂).in_frame rfl rfl
      (by simp [Mem.Live, hfr₂.length_eq, hfr₁'.length_eq, hlen]; omega)).mono (by fp_sub)
      fun _ _ ⟨⟨H₃, hH₃⟩, y, hy⟩ => ⟨⟨y, hy⟩, H₃, hH₃⟩
  · exact (Writes.skip ⟨⟨x, hx⟩, H₁, hH₂⟩).mono bot_le fun _ _ h => h

end Theorems

end NLAlib.SmallEig
