/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.Parameters
public import NLAlib.Eigensolvers.ShiftedQR.RoundedTheoremsBits

/-!
# The precision of the small-eigenvalue solver

The unit roundoff $\boldsymbol{u}_{\mathrm{SmallEig}}$ of [BanksGarzaVargasSrivastava2025,
Theorem 1.1], defined once as the minimum of named terms, one per block of the program: the
counts, the perturbation and the Hessenberg reduction, `RHess`, `DistSpec` and `Decouple`; the
`Decouple` term also keeps the backward error of the decoupler calls of the worklist within
$\delta/8$. Each block's theorem takes its own term; the
headline takes the minimum. Its logarithm is $O(\log^2(n_{\max}\Sigma/(\delta\varphi)))$ for
fixed tail records (Theorem 1.1's $O(\log^2)$ bits). The forward form of Corollary 1.3 runs the
backward form at the accuracy $\delta_b = \Sigma(\beta/(4(2k_{\max} + 1)\Sigma))^{k_{\max}}$, which
the Ostrowski–Elsner matching turns into the forward error $\beta$.

## Main definitions

* `NLAlib.SmallEig.uSmallEig` and its terms.
* `NLAlib.SmallEig.forwardBackwardError`, `NLAlib.SmallEig.uSmallEigForward`,
  `NLAlib.SmallEig.smallEigForwardParams`, `NLAlib.SmallEig.smallEigForwardCap`: the forward form.

## Main results

* `NLAlib.SmallEig.uSmallEig_spec`: positivity and the terms.
* `NLAlib.SmallEig.logb_inv_uSmallEig_le`: the bits.
* `NLAlib.SmallEig.forwardBackwardError_spec`: the backward accuracy gives the forward one.
-/

@[expose] public section

namespace NLAlib.SmallEig

open Real

/-- The precision term of the counts:
$\boldsymbol{u} \le 1/20$ and $10^5(n_{\max} + 1)^2\boldsymbol{u} \le 1$. -/
noncomputable def uSmallEigBasic (nmax : ℕ) : ℝ :=
  min (1 / 20) (1 / (100000 * ((nmax : ℝ) + 1) ^ 2))

/-- The precision term of the perturbation and the Hessenberg reduction: their rounding, at most
$1000(n_{\max} + 1)^2\boldsymbol{u}\cdot 2\Sigma$, is within $\delta/8$ and keeps the class of the
perturbation (condition $2/t_2$, separation $t_1$) up to one doubling. -/
noncomputable def uSmallEigReduce (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (δ / 8)
      (smallEigGap nmax S δ φ c₁ / (64 * ((nmax : ℝ) + 1) * (2 / smallEigCond nmax S δ φ c₂))) /
    (1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S))

/-- The precision term of `RHess` on a block of the core (condition $2B_c$, separation $g_c/2$):
its backward error keeps the class up to one doubling and the weights up to the factor of
`NLAlib.exists_lastRowWeights_ge_of_norm_sub_le`. -/
noncomputable def uSmallEigRHess (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (smallEigSeparation nmax S δ φ c₁ / 2 /
      (64 * ((nmax : ℝ) + 1) * (2 * smallEigCondition nmax S δ φ c₂)))
    (√(smallEigWeight nmax S δ φ c₂) * (smallEigSeparation nmax S δ φ c₁ / 2) /
      (1024 * ((nmax : ℝ) + 1) * (2 * smallEigCondition nmax S δ φ c₂) ^ 2)) /
    (1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S))

/-- The precision term of `DistSpec` (`NLAlib.SmallEig.distSpec_accuracy`) at the condition
$8B_c$, the shift reach $10$, the norm $2\Sigma$ and the distance $\eta_1$. -/
noncomputable def uSmallEigDistSpec (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (1 / (30000 * ((2 : ℝ) ^ smallEigDegreeLog nmax S δ φ c₂ + 1)))
    ((8004 * (8 * smallEigCondition nmax S δ φ c₂))⁻¹ *
      (smallEigInnerRadius nmax S δ φ c₁ c₂ / (22 * (2 * S))) ^
        (2 ^ smallEigDegreeLog nmax S δ φ c₂)
      / (300 * ((nmax : ℝ) + 1) ^ 2))

/-- The precision term of `Decouple` (`NLAlib.SmallEig.decoupleLast_spec`): the forward error of
$m_2$ rounded steps at the distance $\eta_1$ within $\omega/2$. -/
noncomputable def uSmallEigDecouple (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min ((16 * (8 * smallEigCondition nmax S δ φ c₂))⁻¹ *
      (smallEigInnerRadius nmax S δ φ c₁ c₂ / (22 * (2 * S))) ^ smallEigDecoupleSteps nmax S δ φ c₂)
    (smallEigOmega nmax S δ φ c₁ c₂ / 2 / (86 * (8 * smallEigCondition nmax S δ φ c₂) * (2 * S) *
      (22 * (2 * S) / smallEigInnerRadius nmax S δ φ c₁ c₂) ^ smallEigDecoupleSteps nmax S δ φ c₂ *
        √((nmax : ℝ) + 1))) / (300 * ((nmax : ℝ) + 1) ^ 2)

/-- **The precision threshold of the small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], recomputed for the corrected constants of the blocks): the minimum of the terms
`NLAlib.SmallEig.uSmallEigBasic`, `NLAlib.SmallEig.uSmallEigReduce`,
`NLAlib.SmallEig.uSmallEigRHess`, `NLAlib.SmallEig.uSmallEigDistSpec` and
`NLAlib.SmallEig.uSmallEigDecouple`, at the outer order bound $n_{\max}$. The backward error of
the core (its decoupler calls) is within $\delta/8$ by the `Decouple` term
(`NLAlib.SmallEig.smallEigDecoupleError_le_omega`). -/
noncomputable def uSmallEig (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (uSmallEigBasic nmax) <| min (uSmallEigReduce nmax S δ φ c₁ c₂) <|
    min (uSmallEigRHess nmax S δ φ c₁ c₂) <| min (uSmallEigDistSpec nmax S δ φ c₁ c₂) <|
      uSmallEigDecouple nmax S δ φ c₁ c₂

/-- **The precision threshold is positive and below every term**: for tail records with
$b_1, b_2 > 0$, $n_{\max} \ge 1$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$,
$0 < \boldsymbol{u}_{\mathrm{SmallEig}}$ and $\boldsymbol{u}_{\mathrm{SmallEig}}$ is at most each of
its five terms. Without positivity the headline would be vacuous through
$0 \le \boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$. -/
theorem uSmallEig_spec {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < uSmallEig nmax S δ φ c₁ c₂ ∧ uSmallEig nmax S δ φ c₁ c₂ ≤ uSmallEigBasic nmax ∧
      uSmallEig nmax S δ φ c₁ c₂ ≤ uSmallEigReduce nmax S δ φ c₁ c₂ ∧
      uSmallEig nmax S δ φ c₁ c₂ ≤ uSmallEigRHess nmax S δ φ c₁ c₂ ∧
      uSmallEig nmax S δ φ c₁ c₂ ≤ uSmallEigDistSpec nmax S δ φ c₁ c₂ ∧
      uSmallEig nmax S δ φ c₁ c₂ ≤ uSmallEigDecouple nmax S δ φ c₁ c₂ := by
  have hS : 0 < S := hδ.trans_le hδS
  have hg := (smallEigGap_pos_le hb₁ hn hS.le hδ hφ hφ1).1
  have hc := (smallEigCond_pos_le hb₂ hn hS.le hδ hφ hφ1).1
  have hB : 0 < smallEigCondition nmax S δ φ c₂ := by
    linarith [smallEigCondition_ge hb₂ hn hS.le hδ hφ hφ1]
  have hsep := smallEigSeparation_pos hb₁ hn hS.le hδ hφ hφ1
  have hp := (smallEigWeight_pos_le hb₂ hn hS.le hδ hφ hφ1).1
  have hη := smallEigInnerRadius_pos hb₁ hb₂ hn hδ hδS hφ hφ1
  have hω := smallEigOmega_pos hb₁ hb₂ hn hS.le hδ hφ hφ1
  have h1 : 0 < uSmallEigBasic nmax := by unfold uSmallEigBasic; positivity
  have h2 : 0 < uSmallEigReduce nmax S δ φ c₁ c₂ := by
    unfold uSmallEigReduce; exact div_pos (lt_min (by positivity) (by positivity)) (by positivity)
  have h3 : 0 < uSmallEigRHess nmax S δ φ c₁ c₂ := by
    unfold uSmallEigRHess
    have := sqrt_pos.mpr hp
    exact div_pos (lt_min (by positivity) (by positivity)) (by positivity)
  have h4 : 0 < uSmallEigDistSpec nmax S δ φ c₁ c₂ := by
    unfold uSmallEigDistSpec; exact lt_min (by positivity) (by positivity)
  have h5 : 0 < uSmallEigDecouple nmax S δ φ c₁ c₂ := by
    unfold uSmallEigDecouple; exact div_pos (lt_min (by positivity) (by positivity)) (by positivity)
  unfold uSmallEig
  refine ⟨lt_min h1 (lt_min h2 (lt_min h3 (lt_min h4 h5))), min_le_left _ _, ?_, ?_,
    ?_, ?_⟩ <;> simp only [min_le_iff, le_refl, true_or, or_true]

/-! ### The bits -/

section Bits

open NLAlib.ShiftedQR


section General

variable {ι : Type*} {P : ι → Prop} {Y : ι → ℝ}

/-- The inverted tail is uniformly polynomial: for a record with $b > 0$, if the order $N \ge 1$,
the ratio $K + 1$ ($K \ge 0$) are at most polynomial in $Y$ and the failure $\varphi \le 1$ at least
an inverse polynomial, so is the parameter $\tau$ of `NLAlib.polyLogTailInverse`. -/
theorem unifLo_polyLogTailInverse {c : PolyLogTail} (hb : 0 < c.b) (hY : ∀ i, P i → 4 ≤ Y i)
    {N K φ : ι → ℝ} (hN : UnifHi P Y N) (hN1 : ∀ i, P i → 1 ≤ N i)
    (hK : UnifHi P Y (fun i => K i + 1))
    (hK0 : ∀ i, P i → 0 ≤ K i) (hφ : UnifLo P Y φ) (hφ1 : ∀ i, P i → φ i ≤ 1) :
    UnifLo P Y (fun i => polyLogTailInverse c.normalize (N i) (K i) (φ i)) := by
  set d := c.normalize with hd
  have hC : 1 ≤ d.C := le_max_right _ _
  have ha : 0 ≤ d.a := le_max_right _ _
  have hc : 0 ≤ d.c := le_max_right _ _
  have hbn : d.b = c.b := rfl
  have hX : 1 ≤ (1 + 2 * d.c / c.b) ^ d.c := one_le_rpow (by
    have : 0 ≤ 2 * d.c / c.b := by positivity
    linarith) hc
  have hE : 1 ≤ exp (c.b / 2) := one_le_exp (by positivity)
  have hs1 : ∀ i, P i → 1 ≤ polyLogTailScale d (N i) (K i) := by
    intro i hi
    have h1 : 1 ≤ N i ^ d.a := one_le_rpow (hN1 i hi) ha
    have h2 : 1 ≤ (K i + 1) ^ d.c := one_le_rpow (by linarith [hK0 i hi]) hc
    unfold polyLogTailScale
    rw [hbn]
    have h3 : 1 ≤ (1 + 2 * d.c / c.b) ^ d.c * exp (c.b / 2) := one_le_mul_of_one_le_of_one_le hX hE
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC h1) h2) h3
  have hs : UnifHi P Y (fun i => polyLogTailScale d (N i) (K i)) := by
    have := ((((UnifHi.const hY (by linarith : (0 : ℝ) < d.C)).mul (hN.rpow hN1 d.a)).mul
      (hK.rpow (fun i hi => by linarith [hK0 i hi]) d.c)).mul
      (UnifHi.const hY (by positivity : (0 : ℝ) < (1 + 2 * d.c / c.b) ^ d.c * exp (c.b / 2))))
    refine this.congr fun i _ => ?_
    simp only [polyLogTailScale, hbn]
  have hq : UnifLo P Y (fun i => φ i / polyLogTailScale d (N i) (K i)) := hφ.div hs
  have hq1 : ∀ i, P i → φ i / polyLogTailScale d (N i) (K i) ≤ 1 := fun i hi => by
    rw [div_le_one (by linarith [hs1 i hi])]; linarith [hφ1 i hi, hs1 i hi]
  refine ((UnifLo.const hY one_pos).min (fun i hi => by linarith [hY i hi])
    (hq.rpow hq1 (2 / d.b))).congr fun i _ => ?_
  simp only [polyLogTailInverse]


end General

/-! ### The arguments of the bits -/

/-- The arguments $(n_{\max}, \Sigma, \delta, \varphi)$ of the bits with $n_{\max} \ge 1$,
$0 < \delta \le \Sigma$ and $0 < \varphi \le 1$. -/
private def Adm (i : ℕ × ℝ × ℝ × ℝ) : Prop :=
  1 ≤ i.1 ∧ 0 < i.2.2.1 ∧ i.2.2.1 ≤ i.2.1 ∧ 0 < i.2.2.2 ∧ i.2.2.2 ≤ 1

/-- The argument $Y = 4n_{\max}\Sigma/(\delta\varphi)$ of the bits. -/
private noncomputable def arg (i : ℕ × ℝ × ℝ × ℝ) : ℝ := 4 * i.1 * i.2.1 / (i.2.2.1 * i.2.2.2)

private theorem arg_bounds {i : ℕ × ℝ × ℝ × ℝ} (h : Adm i) :
    4 ≤ arg i ∧ HiBd (arg i) 1 (i.1 : ℝ) ∧ LoBd (arg i) 1 (i.2.2.1 / i.2.1) ∧
      LoBd (arg i) 1 i.2.2.2 := by
  obtain ⟨n, S, δ, φ⟩ := i
  obtain ⟨hn, hδ, hδS, hφ, hφ1⟩ := h
  simp only [arg] at *
  have hS : 0 < S := hδ.trans_le hδS
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hP : 0 < δ * φ := by positivity
  have hP1 : δ * φ ≤ S := by nlinarith
  refine ⟨?_, ⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩, ⟨hφ, ?_⟩⟩
  · rw [le_div_iff₀ hP]; nlinarith
  · rw [pow_one, le_div_iff₀ hP]; nlinarith
  · rw [pow_one, div_mul_div_comm, le_div_iff₀ (by positivity)]
    have : S * δ * φ ≤ S * δ * (4 * n) := by gcongr; linarith
    nlinarith
  · rw [pow_one, mul_div_assoc', le_div_iff₀ hP]
    have : δ * φ * 1 ≤ S * φ * (4 * n) := by gcongr; linarith
    nlinarith

private theorem arg_four : ∀ i, Adm i → 4 ≤ arg i := fun _ h => (arg_bounds h).1
private theorem arg_one : ∀ i, Adm i → 1 ≤ arg i := fun _ h => by linarith [(arg_bounds h).1]
private theorem arg_two : ∀ i, Adm i → 2 ≤ arg i := fun _ h => by linarith [(arg_bounds h).1]

private theorem unifHi_order : UnifHi Adm arg (fun i => (i.1 : ℝ)) :=
  ⟨1, fun _ h => (arg_bounds h).2.1⟩

private theorem unifLo_delta : UnifLo Adm arg (fun i => i.2.2.1 / i.2.1) :=
  ⟨1, fun _ h => (arg_bounds h).2.2.1⟩

private theorem unifLo_failure : UnifLo Adm arg (fun i => i.2.2.2) :=
  ⟨1, fun _ h => (arg_bounds h).2.2.2⟩

/-- The scale: $\gamma/(2\Sigma)$ and $K + 1 = 2\Sigma/\gamma + 5$ are polynomial. -/
private theorem unifLo_scale :
    UnifLo Adm arg (fun i => smallEigScale i.2.2.1 i.2.2.2 / 2 / i.2.1) ∧
      UnifHi Adm arg (fun i => (i.2.1 + 4 * (smallEigScale i.2.2.1 i.2.2.2 / 2)) /
        (smallEigScale i.2.2.1 i.2.2.2 / 2) + 1) := by
  have hW : UnifHi Adm arg (fun i => smallEigNoiseLevel i.2.2.2) := by
    refine ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 3)).add arg_two
      ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 4)).mul (UnifHi.inv unifLo_failure))).of_le
      (fun i _ => smallEigNoiseLevel_pos _) fun i h => ?_
    obtain ⟨-, -, -, hφ, hφ1⟩ := h
    have h4 : 1 ≤ 4 * i.2.2.2⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hφ]; linarith
    have hl : log (4 / i.2.2.2) ≤ 4 * i.2.2.2⁻¹ := by
      rw [div_eq_mul_inv]; linarith [log_le_sub_one_of_pos (by linarith : 0 < 4 * i.2.2.2⁻¹)]
    have hs : √(log (4 / i.2.2.2)) ≤ 4 * i.2.2.2⁻¹ := by
      rw [sqrt_le_left (by linarith)]; nlinarith
    simp only [smallEigNoiseLevel]; linarith
  have hγ : UnifLo Adm arg (fun i => smallEigScale i.2.2.1 i.2.2.2 / 2 / i.2.1) :=
    ((unifLo_delta.div ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 4)).mul hW)).div
      (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 2))).congr fun i h => by
        have := (smallEigNoiseLevel_pos i.2.2.2).ne'
        have : i.2.1 ≠ 0 := (h.2.1.trans_le h.2.2.1).ne'
        simp only [smallEigScale]; field_simp
  refine ⟨hγ, ((UnifHi.inv hγ).add arg_two
    (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 5))).congr
    fun i h => ?_⟩
  have := (smallEigNoiseLevel_pos i.2.2.2).ne'
  have := h.2.1.ne'
  have : i.2.1 ≠ 0 := (h.2.1.trans_le h.2.2.1).ne'
  simp only [smallEigScale]; field_simp; ring


section Chain

variable {c₁ c₂ : PolyLogTail}

private theorem unifLo_cond (hb₂ : 0 < c₂.b) :
    UnifLo Adm arg (fun i => smallEigCond i.1 i.2.1 i.2.2.1 i.2.2.2 c₂) ∧
    UnifHi Adm arg (fun i => smallEigCondition i.1 i.2.1 i.2.2.1 i.2.2.2 c₂) := by
  have hK0 : ∀ i, Adm i → 0 ≤ (i.2.1 + 4 * (smallEigScale i.2.2.1 i.2.2.2 / 2)) /
      (smallEigScale i.2.2.1 i.2.2.2 / 2) := fun i h => by
    have := smallEigScale_pos (φ := i.2.2.2) h.2.1
    have := h.2.1.trans_le h.2.2.1
    positivity
  have h := unifLo_polyLogTailInverse hb₂ arg_four unifHi_order
    (fun i h => by exact_mod_cast h.1) unifLo_scale.2 hK0
    (unifLo_failure.div (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 4)))
    (fun i h => by linarith [h.2.2.2.2])
  refine ⟨h, ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 4)).mul (UnifHi.inv h)).congr
    fun i _ => ?_⟩
  simp only [smallEigCondition, smallEigCond, ginibreConditionThreshold, div_eq_mul_inv]

private theorem unifLo_sep (hb₁ : 0 < c₁.b) :
    UnifLo Adm arg (fun i => smallEigSeparation i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ / i.2.1) := by
  have hK0 : ∀ i, Adm i → 0 ≤ (i.2.1 + 4 * (smallEigScale i.2.2.1 i.2.2.2 / 2)) /
      (smallEigScale i.2.2.1 i.2.2.2 / 2) := fun i h => by
    have := smallEigScale_pos (φ := i.2.2.2) h.2.1
    have := h.2.1.trans_le h.2.2.1
    positivity
  have h2c : (0 : ℝ) < 4 * 2 ^ c₁.normalize.c := by positivity
  have h2c1 : (1 : ℝ) ≤ 4 * 2 ^ c₁.normalize.c := by
    have : (1 : ℝ) ≤ 2 ^ c₁.normalize.c := one_le_rpow (by norm_num) (le_max_right _ _)
    linarith
  have h := unifLo_polyLogTailInverse hb₁ arg_four unifHi_order
    (fun i h => by exact_mod_cast h.1) unifLo_scale.2 hK0
    (unifLo_failure.div (UnifHi.const arg_four h2c))
    (fun i h => by rw [div_le_one h2c]; linarith [h.2.2.2.2])
  refine ((unifLo_scale.1.mul h).div (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 4))).congr
    fun i _ => ?_
  simp only [smallEigSeparation, smallEigGap, ginibreGapThreshold]
  ring

private theorem pos_of_adm {i : ℕ × ℝ × ℝ × ℝ} (h : Adm i) :
    0 < i.2.1 ∧ (0 : ℝ) < i.1 := ⟨h.2.1.trans_le h.2.2.1, by have := h.1; positivity⟩

private theorem unifLo_omega (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    UnifLo Adm arg (fun i => smallEigOmega i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ c₂ / i.2.1) := by
  refine (((unifLo_delta.div (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 4))).min arg_one
    ((unifLo_sep hb₁).div (((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 16)).mul
      unifHi_order).mul (unifLo_cond hb₂).2))).div
    ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 12)).mul unifHi_order)).congr fun i h => ?_
  have hS := (pos_of_adm h).1
  simp only [smallEigOmega]
  rw [div_right_comm i.2.2.1 i.2.1, div_right_comm (smallEigSeparation _ _ _ _ _) i.2.1,
    min_div_div_right hS.le, div_right_comm]

private theorem unifLo_accuracy (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    UnifLo Adm arg (fun i => smallEigAccuracy i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ c₂ / i.2.1) :=
  ((unifLo_omega hb₁ hb₂).div (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 20))).congr
    fun i _ => by simp only [smallEigAccuracy]; rw [div_right_comm]

private theorem unifLo_outer (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    UnifLo Adm arg (fun i => smallEigOuterRadius i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ c₂ / i.2.1) := by
  refine (((unifLo_accuracy hb₁ hb₂).div (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 40))).min
    arg_one (((unifLo_sep hb₁).div (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 4))).div
      (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 3)))).congr fun i h => ?_
  have hS := (pos_of_adm h).1
  simp only [smallEigOuterRadius, oneEigOuterRadius]
  rw [div_right_comm (smallEigAccuracy _ _ _ _ _ _) i.2.1, div_right_comm _ i.2.1 (4 : ℝ),
    div_right_comm _ i.2.1 (3 : ℝ), min_div_div_right hS.le]

private theorem unifLo_inner (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    UnifLo Adm arg (fun i => smallEigInnerRadius i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ c₂ / i.2.1) := by
  have hβ := unifLo_accuracy hb₁ hb₂
  have hlog : UnifHi Adm arg (fun i => logb 2 (8 * (2 * i.2.1) /
      smallEigAccuracy i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ c₂)) := by
    refine ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 32)).mul (UnifHi.inv hβ)).of_le
      (fun i h => ?_) fun i h => ?_
    all_goals obtain ⟨hn, hδ, hδS, hφ, hφ1⟩ := h
    all_goals obtain ⟨h0, h1⟩ := smallEigAccuracy_le hb₁ hb₂ hn hδ hδS hφ hφ1
    · apply logb_pos (by norm_num); rw [one_lt_div h0]; nlinarith
    · have hS : 0 < i.2.1 := hδ.trans_le hδS
      refine (logb_two_le_two_mul (by positivity)).trans (le_of_eq ?_)
      field_simp; ring
  refine ((unifLo_outer hb₁ hb₂).mul ((((unifLo_failure.div ((UnifHi.const arg_four
    (by norm_num : (0 : ℝ) < 16)).mul unifHi_order)).div (UnifHi.const arg_four
      (by norm_num : (0 : ℝ) < 2))).div ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 12)).mul
        hlog)).sqrt arg_one)).congr fun i h => ?_
  simp only [smallEigInnerRadius, oneEigInnerRadius, smallEigOuterRadius,
    smallEigDecouplerFailure]
  rw [div_mul_eq_mul_div]

private theorem unifLo_weight (hb₂ : 0 < c₂.b) :
    UnifLo Adm arg (fun i => smallEigWeight i.1 i.2.1 i.2.2.1 i.2.2.2 c₂) := by
  have hR0 : UnifHi Adm arg (fun i => 3 * √(i.1 : ℝ) +
      √(2 * log (4 / smallEigDecouplerFailure i.1 i.2.2.2))) := by
    refine (((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 3)).mul unifHi_order).add arg_two
      ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 128)).mul (unifHi_order.mul
        (UnifHi.inv unifLo_failure)))).of_le (fun i h => ?_) fun i h => ?_
    all_goals obtain ⟨hn, hδ, hδS, hφ, hφ1⟩ := h
    all_goals have hn1 : (1 : ℝ) ≤ i.1 := by exact_mod_cast hn
    · have : 0 < √(i.1 : ℝ) := sqrt_pos.mpr (by linarith)
      positivity
    · have hD : 4 / smallEigDecouplerFailure i.1 i.2.2.2 = 64 * i.1 * i.2.2.2⁻¹ := by
        unfold smallEigDecouplerFailure; field_simp; ring
      have hφi : 1 ≤ i.2.2.2⁻¹ := one_le_inv₀ hφ |>.mpr hφ1
      have hq : 1 ≤ 64 * (i.1 : ℝ) * i.2.2.2⁻¹ := by nlinarith
      have hl : log (64 * i.1 * i.2.2.2⁻¹) ≤ 64 * i.1 * i.2.2.2⁻¹ := by
        linarith [log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 64 * i.1 * i.2.2.2⁻¹)]
      have h1 : √(i.1 : ℝ) ≤ i.1 := by rw [sqrt_le_left (by linarith)]; nlinarith
      have h2 : √(2 * log (64 * i.1 * i.2.2.2⁻¹)) ≤ 128 * (i.1 * i.2.2.2⁻¹) := by
        rw [sqrt_le_left (by positivity)]; nlinarith
      rw [hD]; linarith
  have hR : UnifHi Adm arg (fun i => smallEigVectorRadius i.1 i.2.2.2) :=
    ((UnifHi.const arg_four (by positivity : (0 : ℝ) < √2)).mul hR0).congr fun i _ => by
      simp only [smallEigVectorRadius]
  refine ((unifLo_failure.div ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 16)).mul
    unifHi_order)).div ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 8)).mul unifHi_order)).div
    (((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 64)).mul (hR.pow 2)).mul
      (((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 2)).mul (unifLo_cond hb₂).2).pow 2))
    |>.congr fun i h => ?_
  simp only [smallEigWeight, smallEigDecouplerFailure]

private theorem unifHi_succ : UnifHi Adm arg (fun i => (i.1 : ℝ) + 1) :=
  unifHi_order.add arg_two (UnifHi.const arg_four one_pos)

private theorem unifLo_basic :
    UnifLo Adm arg (fun i => uSmallEigBasic i.1) :=
  ((UnifLo.const arg_four (by norm_num : (0 : ℝ) < 1 / 20)).min arg_one
    ((UnifLo.const arg_four one_pos).div ((UnifHi.const arg_four
      (by norm_num : (0 : ℝ) < 100000)).mul (unifHi_succ.pow 2)))).congr fun i _ => by
    simp only [uSmallEigBasic]

private theorem unifLo_reduce (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    UnifLo Adm arg (fun i => uSmallEigReduce i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ c₂) := by
  refine (((unifLo_delta.div (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 8))).min arg_one
    (((UnifLo.const arg_four (by norm_num : (0 : ℝ) < 4)).mul (unifLo_sep hb₁)).div
      (((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 64)).mul unifHi_succ).mul
        ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 2)).mul
          (UnifHi.inv (unifLo_cond hb₂).1))))).div
    (((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 1000)).mul (unifHi_succ.pow 2)).mul
      (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 2)))).congr fun i h => ?_
  have hS := (pos_of_adm h).1
  simp only [uSmallEigReduce, smallEigSeparation]
  rw [show 4 * (smallEigGap i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ / 4 / i.2.1) =
    smallEigGap i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ / i.2.1 by ring, ← div_eq_mul_inv,
    div_right_comm i.2.2.1 i.2.1, div_right_comm (smallEigGap _ _ _ _ _) i.2.1,
    min_div_div_right hS.le, div_div]
  congr 1; ring

private theorem unifLo_rhess (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    UnifLo Adm arg (fun i => uSmallEigRHess i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ c₂) := by
  have hB := (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 2)).mul (unifLo_cond hb₂).2
  refine (((((unifLo_sep hb₁).div (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 2))).div
    (((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 64)).mul unifHi_succ).mul hB)).min arg_one
    ((((unifLo_weight hb₂).sqrt arg_one).mul ((unifLo_sep hb₁).div (UnifHi.const arg_four
      (by norm_num : (0 : ℝ) < 2)))).div (((UnifHi.const arg_four
        (by norm_num : (0 : ℝ) < 1024)).mul unifHi_succ).mul (hB.pow 2)))).div
    (((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 1000)).mul (unifHi_succ.pow 2)).mul
      (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 2)))).congr fun i h => ?_
  have hS := (pos_of_adm h).1
  simp only [uSmallEigRHess]
  rw [div_right_comm (smallEigSeparation _ _ _ _ _) i.2.1 (2 : ℝ),
    div_right_comm (smallEigSeparation _ _ _ _ _ / 2) i.2.1, mul_div_assoc', 
    div_right_comm (√(smallEigWeight _ _ _ _ _) * (smallEigSeparation _ _ _ _ _ / 2)) i.2.1,
    min_div_div_right hS.le, div_div]
  congr 1; ring

/-- The base $\eta_1/(44\Sigma)$ of the powers of `DistSpec` and `Decouple`. -/
private theorem unifLo_innerRatio (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    UnifLo Adm arg
      (fun i => smallEigInnerRadius i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ c₂ / (22 * (2 * i.2.1))) :=
  ((unifLo_inner hb₁ hb₂).div (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 44))).congr
    fun i h => by
      have := (pos_of_adm h).1.ne'
      field_simp; ring

private theorem unifLo_distSpecRest (hb₂ : 0 < c₂.b) :
    UnifLo Adm arg (fun i => (8004 * (8 * smallEigCondition i.1 i.2.1 i.2.2.1 i.2.2.2 c₂))⁻¹ /
      (300 * ((i.1 : ℝ) + 1) ^ 2)) :=
  (UnifLo.inv ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 8004)).mul
    ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 8)).mul (unifLo_cond hb₂).2))).div
    ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 300)).mul (unifHi_succ.pow 2))

private theorem unifLo_decoupleRest (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    UnifLo Adm arg (fun i => (16 * (8 * smallEigCondition i.1 i.2.1 i.2.2.1 i.2.2.2 c₂))⁻¹ /
      (300 * ((i.1 : ℝ) + 1) ^ 2)) ∧
    UnifLo Adm arg (fun i => smallEigOmega i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ c₂ / i.2.1 / 2 /
      (86 * (8 * smallEigCondition i.1 i.2.1 i.2.2.1 i.2.2.2 c₂) * 2 * √((i.1 : ℝ) + 1)) /
      (300 * ((i.1 : ℝ) + 1) ^ 2)) := by
  have hB := (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 8)).mul (unifLo_cond hb₂).2
  have hN := (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 300)).mul (unifHi_succ.pow 2)
  exact ⟨(UnifLo.inv ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 16)).mul hB)).div hN,
    ((((unifLo_omega hb₁ hb₂).div (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 2))).div
      (((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 86)).mul hB).mul
        (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 2)) |>.mul (unifHi_succ.sqrt arg_one))).div
      hN)⟩

private theorem uSmallEigDecouple_eq (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) :
    uSmallEigDecouple nmax S δ φ c₁ c₂ =
      min ((16 * (8 * smallEigCondition nmax S δ φ c₂))⁻¹ / (300 * ((nmax : ℝ) + 1) ^ 2) *
          (smallEigInnerRadius nmax S δ φ c₁ c₂ / (22 * (2 * S))) ^
            smallEigDecoupleSteps nmax S δ φ c₂)
        (smallEigOmega nmax S δ φ c₁ c₂ / S / 2 /
          (86 * (8 * smallEigCondition nmax S δ φ c₂) * 2 * √((nmax : ℝ) + 1)) /
          (300 * ((nmax : ℝ) + 1) ^ 2) *
          (smallEigInnerRadius nmax S δ φ c₁ c₂ / (22 * (2 * S))) ^
            smallEigDecoupleSteps nmax S δ φ c₂) := by
  have hN : 0 < 300 * ((nmax : ℝ) + 1) ^ 2 := by positivity
  rw [uSmallEigDecouple, ← min_div_div_right hN.le,
    show 22 * (2 * S) / smallEigInnerRadius nmax S δ φ c₁ c₂ =
    (smallEigInnerRadius nmax S δ φ c₁ c₂ / (22 * (2 * S)))⁻¹ by rw [inv_div], inv_pow]
  congr 1 <;> simp only [div_eq_mul_inv, mul_inv, inv_inv] <;> ring

/-- The precision threshold is at least $Y^{-(K_0 + K_1(m + m_2))}$, $m = 2^q$ and $m_2$ the
degree and the step cap. -/
private theorem loBd_uSmallEig (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) : ∃ K₀ K₁ : ℕ, ∀ i, Adm i →
    LoBd (arg i) (K₀ + K₁ * (2 ^ smallEigDegreeLog i.1 i.2.1 i.2.2.1 i.2.2.2 c₂ +
      smallEigDecoupleSteps i.1 i.2.1 i.2.2.1 i.2.2.2 c₂))
      (uSmallEig i.1 i.2.1 i.2.2.1 i.2.2.2 c₁ c₂) := by
  obtain ⟨a1, h1⟩ := unifLo_basic
  obtain ⟨a2, h2⟩ := unifLo_reduce hb₁ hb₂
  obtain ⟨a3, h3⟩ := unifLo_rhess hb₁ hb₂
  obtain ⟨a4, h4⟩ := unifLo_distSpecRest hb₂
  obtain ⟨x, hx⟩ := unifLo_innerRatio hb₁ hb₂
  obtain ⟨⟨a5, h5⟩, ⟨a6, h6⟩⟩ := unifLo_decoupleRest hb₁ hb₂
  refine ⟨a1 + a2 + a3 + 8 + a4 + a5 + a6, 2 * x + 1, fun i hi => ?_⟩
  obtain ⟨n, S, δ, φ⟩ := i
  have hY := arg_four _ hi
  have hY1 : 1 ≤ arg (n, S, δ, φ) := by linarith
  obtain ⟨hS, hn⟩ := pos_of_adm hi
  simp only at hS hn h1 h2 h3 h4 h5 h6 hx ⊢
  set Q := 2 ^ smallEigDegreeLog n S δ φ c₂
  set m := smallEigDecoupleSteps n S δ φ c₂
  have hD : LoBd (arg (n, S, δ, φ)) (8 + Q + (a4 + x * Q)) (uSmallEigDistSpec n S δ φ c₁ c₂) := by
    refine (LoBd.min' hY1 ?_ (((h4 _ hi).mul ((hx _ hi).pow Q)).of_le (le_of_eq ?_)))
    · have := LoBd.one_div_mul_succ hY (by norm_num : (0 : ℝ) < 30000) (e := 8) (by norm_num) Q
      simp only [Q, Nat.cast_pow, Nat.cast_ofNat, one_div] at this ⊢
      exact this
    · simp only [Q]; ring
  have hDec : LoBd (arg (n, S, δ, φ)) (a5 + x * m + (a6 + x * m))
      (uSmallEigDecouple n S δ φ c₁ c₂) := by
    rw [uSmallEigDecouple_eq]
    exact ((h5 _ hi).mul ((hx _ hi).pow m)).min' hY1 ((h6 _ hi).mul ((hx _ hi).pow m))
  refine ((h1 _ hi).min' hY1 ((h2 _ hi).min' hY1 ((h3 _ hi).min' hY1
    (hD.min' hY1 hDec)))).mono hY1 ?_
  nlinarith [Nat.zero_le (x * Q), Nat.zero_le (x * m)]

private theorem natCeil_le_add_one {y z : ℝ} (hz : 0 ≤ z) (h : y ≤ z) : (⌈y⌉₊ : ℝ) ≤ z + 1 :=
  (Nat.cast_le.mpr (Nat.ceil_mono h)).trans (Nat.ceil_lt_add_one hz).le

/-- The degree $m = 2^q$ and the step cap $m_2$ are $O(\log_2 Y)$. -/
private theorem degree_add_steps_le (hb₂ : 0 < c₂.b) : ∃ c : ℝ, 0 ≤ c ∧ ∀ i, Adm i →
    ((2 ^ smallEigDegreeLog i.1 i.2.1 i.2.2.1 i.2.2.2 c₂ +
      smallEigDecoupleSteps i.1 i.2.1 i.2.2.1 i.2.2.2 c₂ : ℕ) : ℝ) ≤
      c * logb 2 (arg i) + 5 := by
  have h8B := (UnifHi.const arg_four (by norm_num : (0 : ℝ) < 8)).mul (unifLo_cond hb₂).2
  obtain ⟨e1, he1⟩ := h8B
  obtain ⟨e2, he2⟩ := UnifHi.inv (unifLo_weight hb₂)
  obtain ⟨e3, he3⟩ := ((UnifHi.const arg_four (by norm_num : (0 : ℝ) < 8)).mul
    (unifLo_cond hb₂).2).div ((unifLo_weight hb₂).sqrt arg_one)
  refine ⟨24 * e1 + 12 * e2 + e3, by positivity, fun i hi => ?_⟩
  have hL : 0 ≤ logb 2 (arg i) := logb_nonneg (by norm_num) (arg_one i hi)
  have l1 := (he1 i hi).logb_le
  have l2 := (he2 i hi).logb_le
  have l3 := (he3 i hi).logb_le
  set κ := 8 * smallEigCondition i.1 i.2.1 i.2.2.1 i.2.2.2 c₂
  set p := smallEigWeight i.1 i.2.1 i.2.2.1 i.2.2.2 c₂
  have hκ : 0 < κ := (he1 i hi).1
  have hp : 0 < p := (unifLo_weight hb₂).elim fun _ h => (h i hi).1
  have hm1 : (distSpecDegree κ p : ℝ) ≤ 12 * (e1 * logb 2 (arg i)) +
      6 * (e2 * logb 2 (arg i)) + 1 := by
    unfold distSpecDegree
    refine natCeil_le_add_one (by positivity) ?_
    have := l1; have := l2; nlinarith
  have hQ : 2 ^ smallEigDegreeLog i.1 i.2.1 i.2.2.1 i.2.2.2 c₂ ≤ 2 * distSpecDegree κ p + 1 := by
    unfold smallEigDegreeLog
    rcases Nat.lt_or_ge 1 (distSpecDegree κ p) with h | h
    · have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
      have h0 : 0 < Nat.clog 2 (distSpecDegree κ p) := Nat.clog_pos (by norm_num) h
      rw [← Nat.succ_pred_eq_of_pos h0, pow_succ]; omega
    · rw [Nat.clog_of_right_le_one h]; omega
  have hm : (smallEigDecoupleSteps i.1 i.2.1 i.2.2.1 i.2.2.2 c₂ : ℝ) ≤
      e3 * logb 2 (arg i) + 2 := by
    unfold smallEigDecoupleSteps decoupleSteps
    push_cast
    have := natCeil_le_add_one (by positivity) l3
    linarith
  have hQ' : ((2 ^ smallEigDegreeLog i.1 i.2.1 i.2.2.1 i.2.2.2 c₂ : ℕ) : ℝ) ≤
      2 * distSpecDegree κ p + 1 := by exact_mod_cast hQ
  push_cast at hQ' ⊢
  nlinarith

end Chain

end Bits

/-- **The bits of precision of the small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], $O(\log^2)$ bits): for tail records with $b_1, b_2 > 0$ there are constants
$e_1, e_2$ (depending on the records) such that for every $n_{\max} \ge 1$,
$0 < \delta \le \Sigma$ and $0 < \varphi \le 1$,
$$\log_2\frac{1}{\boldsymbol{u}_{\mathrm{SmallEig}}} \le e_1\log_2^2 Y + e_2, \qquad
  Y = \frac{4n_{\max}\Sigma}{\delta\varphi}\,.$$ -/
theorem logb_inv_uSmallEig_le (c₁ c₂ : PolyLogTail) (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    ∃ e₁ e₂ : ℝ, ∀ {nmax : ℕ} {S δ φ : ℝ}, 1 ≤ nmax → 0 < δ → δ ≤ S → 0 < φ → φ ≤ 1 →
      logb 2 (uSmallEig nmax S δ φ c₁ c₂)⁻¹ ≤
        e₁ * logb 2 (4 * nmax * S / (δ * φ)) ^ 2 + e₂ := by
  obtain ⟨K₀, K₁, hK⟩ := loBd_uSmallEig hb₁ hb₂
  obtain ⟨c, hc, hM⟩ := degree_add_steps_le (c₂ := c₂) hb₂
  refine ⟨K₁ * c + K₀ + 5 * K₁, 0, fun {nmax S δ φ} hn hδ hδS hφ hφ1 => ?_⟩
  have hi : Adm (nmax, S, δ, φ) := ⟨hn, hδ, hδS, hφ, hφ1⟩
  have hL1 : 1 ≤ logb 2 (arg (nmax, S, δ, φ)) := by
    rw [le_logb_iff_rpow_le (by norm_num) (by linarith [arg_four _ hi]), rpow_one]
    linarith [arg_four _ hi]
  have h := (hK _ hi).logb_inv_le
  have hm := hM _ hi
  simp only [arg] at h hm hL1 ⊢
  set L := logb 2 (4 * nmax * S / (δ * φ))
  push_cast at h hm
  have hK1 : (0 : ℝ) ≤ K₁ := K₁.cast_nonneg
  have hK0 : (0 : ℝ) ≤ K₀ := K₀.cast_nonneg
  calc logb 2 (uSmallEig nmax S δ φ c₁ c₂)⁻¹ ≤ (K₀ + K₁ * (c * L + 5)) * L := by
        refine h.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
        gcongr
    _ ≤ (K₁ * c + K₀ + 5 * K₁) * L ^ 2 + 0 := by
        have : 0 ≤ ((K₀ : ℝ) + 5 * K₁) * (L * (L - 1)) :=
          mul_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
        nlinarith

/-! ### The forward form -/

/-- The backward accuracy $\delta_b = \Sigma(\beta/(4(2k_{\max} + 1)\Sigma))^{k_{\max}}$ that gives
the forward error $\beta$ on orders at most $k_{\max}$ and norms at most $\Sigma$. -/
noncomputable def forwardBackwardError (kmax : ℕ) (S β : ℝ) : ℝ :=
  S * (β / (4 * (2 * kmax + 1) * S)) ^ kmax

/-- **The backward accuracy gives the forward error** ([BanksGarzaVargasSrivastava2025,
Corollary 1.3], the arithmetic): for $0 < \beta \le \Sigma$ and
$\delta_b$ = `NLAlib.SmallEig.forwardBackwardError` $k_{\max}$ $\Sigma$ $\beta$:
$0 < \delta_b \le \Sigma$ and, for every order $d + 1 \le k_{\max}$,
$(2d + 1)(3\Sigma)^{1 - 1/(d + 1)}\delta_b^{1/(d + 1)} \le \beta$, the Ostrowski–Elsner bound of a
perturbation of norm $\delta_b$ of a matrix of norm at most $\Sigma$ and order $d + 1$. -/
theorem forwardBackwardError_spec {kmax : ℕ} {S β : ℝ} (hβ : 0 < β) (hβS : β ≤ S) :
    0 < forwardBackwardError kmax S β ∧ forwardBackwardError kmax S β ≤ S ∧
      ∀ d : ℕ, d + 1 ≤ kmax → (2 * d + 1) * (3 * S) ^ (1 - 1 / ((d : ℝ) + 1)) *
        forwardBackwardError kmax S β ^ (1 / ((d : ℝ) + 1)) ≤ β := by
  have hS : 0 < S := hβ.trans_le hβS
  set r := β / (4 * (2 * kmax + 1) * S) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 / 4 := by
    rw [hr, div_le_iff₀ (by positivity)]
    have : (1:ℝ) ≤ 2 * kmax + 1 := by have := kmax.cast_nonneg (α := ℝ); linarith
    nlinarith
  have hrk : r ^ kmax ≤ 1 := pow_le_one₀ hr0.le (by linarith)
  refine ⟨by unfold forwardBackwardError; positivity, ?_, fun d hd => ?_⟩
  · unfold forwardBackwardError; nlinarith [pow_pos hr0 kmax]
  have hd1 : (0:ℝ) < d + 1 := by positivity
  have hdk : ((d:ℝ) + 1) ≤ kmax := by exact_mod_cast hd
  set e := 1 / ((d : ℝ) + 1) with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := by rw [he, div_le_one hd1]; linarith
  -- δ_b^e = S^e r^(kmax e) ≤ S^e r
  have hpow : (forwardBackwardError kmax S β) ^ e ≤ S ^ e * r := by
    unfold forwardBackwardError
    rw [mul_rpow hS.le (by positivity), ← rpow_natCast, ← rpow_mul hr0.le]
    gcongr
    calc r ^ ((kmax : ℝ) * e) ≤ r ^ (1:ℝ) := by
          apply rpow_le_rpow_of_exponent_ge hr0 (by linarith)
          rw [he, mul_one_div, le_div_iff₀ hd1]; linarith
      _ = r := rpow_one r
  have h3 : (3 * S) ^ (1 - e) * S ^ e ≤ 3 * S := by
    rw [mul_rpow (by norm_num) hS.le, mul_assoc, ← rpow_add hS, sub_add_cancel, rpow_one]
    gcongr
    calc (3:ℝ) ^ (1 - e) ≤ 3 ^ (1:ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 3 := rpow_one 3
  have h2d : (2 * (d:ℝ) + 1) ≤ 2 * kmax + 1 := by linarith
  calc (2 * d + 1) * (3 * S) ^ (1 - e) * (forwardBackwardError kmax S β) ^ e
      ≤ (2 * d + 1) * (3 * S) ^ (1 - e) * (S ^ e * r) := by gcongr
    _ = (2 * d + 1) * ((3 * S) ^ (1 - e) * S ^ e) * r := by ring
    _ ≤ (2 * kmax + 1) * (3 * S) * r := by gcongr
    _ = 3 / 4 * β := by rw [hr]; field_simp
    _ ≤ β := by linarith

/-- The precision threshold of the forward form: `NLAlib.SmallEig.uSmallEig` at the backward
accuracy `NLAlib.SmallEig.forwardBackwardError` and $n_{\max} = k_{\max}$. -/
noncomputable def uSmallEigForward (kmax : ℕ) (S β φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  uSmallEig kmax S (forwardBackwardError kmax S β) φ c₁ c₂

/-- The parameter words of the forward form: `NLAlib.SmallEig.smallEigParams` at the backward
accuracy `NLAlib.SmallEig.forwardBackwardError` and $n_{\max} = k_{\max}$. -/
noncomputable def smallEigForwardParams (kmax : ℕ) (S β φ : ℝ) (c₁ c₂ : PolyLogTail) : List ℝ :=
  smallEigParams kmax S (forwardBackwardError kmax S β) φ c₁ c₂

/-- The cap of the forward form: `NLAlib.SmallEig.smallEigCap` at the backward accuracy
`NLAlib.SmallEig.forwardBackwardError` and $n_{\max} = k_{\max}$. -/
noncomputable def smallEigForwardCap (kmax : ℕ) (S β φ : ℝ) (c₁ c₂ : PolyLogTail) : ℕ :=
  smallEigCap kmax S (forwardBackwardError kmax S β) φ c₁ c₂

end NLAlib.SmallEig
