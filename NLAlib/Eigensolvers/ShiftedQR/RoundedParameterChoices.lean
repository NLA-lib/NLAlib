/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedParameters

/-!
# Parameter choices of the rounded shifted QR algorithm

[BanksGarzaVargasSrivastava2022, Theorem 6.3]: the parameter choices of the headline in the order
of the paper, with no circularity: the decoupling threshold $\omega$ from the error budget, the
iteration cap $F$, the failure split, the radius $R$ and the separation $d$ of the shifts, then one
closed-form unit roundoff `NLAlib.ShiftedQR.uShQR`, a minimum of named per-block terms, and the
words that depend on it. Everything is written for the iterate class: condition $4B$ and
separation $\Gamma/4$, iterate norm $4\Sigma$, block norm $2\Sigma$. The shift degree and the
global constants are in `NLAlib.Eigensolvers.ShiftedQR.RoundedParameters`.

## Main definitions

* `NLAlib.ShiftedQR.shqrOmega`, `NLAlib.ShiftedQR.shqrCap`,
  `NLAlib.ShiftedQR.shqrSmallEigFailure`, `NLAlib.ShiftedQR.shqrSmallEigAccuracy`,
  `NLAlib.ShiftedQR.shqrDist`: the parameter choices.
* `NLAlib.ShiftedQR.uShQR`: the precision threshold.
* `NLAlib.ShiftedQR.shqrScanThreshold`, `NLAlib.ShiftedQR.shqrLoopThreshold`,
  `NLAlib.ShiftedQR.shqrDecoupled`: the words that depend on it.

## Main results

* `NLAlib.ShiftedQR.uShQR_pos`, `NLAlib.ShiftedQR.shqrSmallEigAccuracy_pos`,
  `NLAlib.ShiftedQR.shqrSmallEigFailure_pos`: the thresholds are positive.
* `NLAlib.ShiftedQR.shqrDecoupleError_le`, `NLAlib.ShiftedQR.shqrContraction_pow_shqrCap_mul_lt`:
  the loop's error budget and cap.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Real Filter Topology

/-! ### The parameter choices

Inputs: the order $n + 1$, the shift degree $k$, the condition bound $B$, the separation
$\Gamma$, the norm bound $\Sigma$ (`S`), the backward error $\delta$ and the failure probability
$\varphi$. The choices, in order: the error budget and $\omega$; the cap $F$; the failure split;
the radius $R$ and the forward accuracy of `SmallEig`; Regularize's distance $\eta/2$ and Sh's
separation $d$; the precision threshold; and only then the words that depend on it (the
thresholds). The blocks run at condition $4B$, separation $\Gamma/4$, iterate norm $4\Sigma$. -/

/-- The backward error budget $\min(\delta, \Gamma/(16(n + 1)B))$ of the worklist: at most $\delta$
(the headline) and at most the class-preservation bound of the worklist. -/
noncomputable def shqrBudget (n : ℕ) (B Γ δ : ℝ) : ℝ := min δ (Γ / (16 * (n + 1) * B))

/-- The decoupling threshold $\omega = \mathrm{budget}/(12(n + 1))$ of the iteration. -/
noncomputable def shqrOmega (n : ℕ) (B Γ δ : ℝ) : ℝ := shqrBudget n B Γ δ / (12 * (n + 1))

/-- The contraction $1.002(1 - \gamma) = 0.8016$ of $\psi_k$ per Sh step at $\gamma = 0.2$. -/
noncomputable def shqrContraction : ℝ := 1.002 * (1 - 0.2)

/-- The iteration cap $F = \lceil \log(4\Sigma/\omega)/\log(1/0.8016) \rceil + 1$: $\psi_k \le
4\Sigma$ cannot stay above $\omega$ through $F$ contractions. The $+1$ is an iteration more than
the count of [BanksGarzaVargasSrivastava2022, Lemma 6.4], whose loop also exits at a
subdiagonal equal to $\omega$. -/
noncomputable def shqrCap (n : ℕ) (B Γ S δ : ℝ) : ℕ :=
  ⌈log (4 * S / shqrOmega n B Γ δ) / log (1 / shqrContraction)⌉₊ + 1

/-- The failure unit $\varphi/(12F(n + 1))$; also the failure allowed to `SmallEig`. -/
noncomputable def shqrSmallEigFailure (n : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  φ / (12 * shqrCap n B Γ S δ * (n + 1))

/-- The failure probability given to Regularize's disk draws, twice the unit (Regularize fails
with `SmallEig`'s failure plus half of it). -/
noncomputable def shqrRegularizeFailure (n : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  2 * shqrSmallEigFailure n B Γ S δ φ

/-- Regularize's radius $R = \omega^2/(8080 \cdot 4\Sigma)$. -/
noncomputable def shqrRadius (n : ℕ) (B Γ S δ : ℝ) : ℝ :=
  shqrOmega n B Γ δ ^ 2 / (8080 * (4 * S))

/-- The forward accuracy required of `SmallEig`, equal to the radius $R$ (Regularize needs
$\beta + R \le \omega^2/(4040 \cdot 4\Sigma)$ with room for rounding). -/
noncomputable def shqrSmallEigAccuracy (n : ℕ) (B Γ S δ : ℝ) : ℝ := shqrRadius n B Γ S δ

/-- Regularize's window $\eta = R\sqrt{\varphi_{\mathrm{reg}}/(2k)}$; the stored shifts are at
distance at least $\eta/2$ from the spectrum. -/
noncomputable def shqrEta (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  shqrRadius n B Γ S δ * √(shqrRegularizeFailure n B Γ S δ φ / (2 * k))

/-- Sh's shift separation
$d = \min(\eta/2, \varepsilon c_{\mathrm{lo}}\omega\sqrt{\varphi/(11(n + 1))}/4)$,
at condition $4B$ and with Sh's failure the unit $\varphi/(12F(n + 1))$. -/
noncomputable def shqrDist (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  min (shqrEta n k B Γ S δ φ / 2)
    (shqrEps k (4 * B) * (shqrRadiusLo k (4 * B) * shqrOmega n B Γ δ) *
      √(shqrSmallEigFailure n B Γ S δ φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4)

/-! ### The precision threshold -/

/-- The precision term of the counts: $\boldsymbol{u} \le 1/10$ and
$10^5(n + 1 + k)^2\boldsymbol{u} \le 1$. -/
noncomputable def uShQRBasic (n k : ℕ) : ℝ :=
  min (1 / 10) (1 / (100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2))

/-- The precision term of Regularize (`NLAlib.ShiftedQR.regularize_pwrites` at condition $4B$,
norm $4\Sigma$): the rounding of the translates (`hβ`, `hdη`), Optimal's test (`huo`, with the
factor $kn^{3/2}$ of its rounding analysis, where [BanksGarzaVargasSrivastava2022, Lemma 4.5]
writes $2n^2$, which holds only for $k \le 2\sqrt{n}$) and the forward error of the shifted
chains (`hxu`, `hbound`). -/
noncomputable def uShQRRegularize (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  min (shqrOmega n B Γ δ ^ 2 / (16160 * (4 * S) ^ 2)) <|
  min (shqrEta n k B Γ S δ φ / (8 * (4 * S))) <|
  min ((shqrTheta k (4 * B) * shqrOmega n B Γ δ) ^ k /
    (30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ)) * ((2 + 2 * 1.1) * (4 * S)) ^ k)) <|
  min ((16 * (4 * B))⁻¹ * (shqrEta n k B Γ S δ φ / 2 / ((2 + 2 * 1.1) * (4 * S))) ^ k /
    (300 * (n + 1) ^ 2))
  (shqrOmega n B Γ δ / 2 / ((66 + 2 * 1.1) * (4 * B) * (4 * S) *
    ((2 + 2 * 1.1) * (4 * S) / (shqrEta n k B Γ S δ φ / 2)) ^ k * √(n + 1) * (300 * (n + 1) ^ 2)))

/-- The precision term of Sh (`NLAlib.ShiftedQR.shStep_pwrites` at condition $4B$, norm
$4\Sigma$): Find's half products (`hxu`), the forward error of the chains (`hbound`) and Exc's
rounded net and translate (`hexc1`, `hexc2`, at $\omega \le \psi_k \le 4\Sigma$). -/
noncomputable def uShQRSh (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  min ((8004 * (4 * B))⁻¹ * (shqrDist n k B Γ S δ φ / ((2 + 2 * shqrC k (4 * B)) * (4 * S))) ^ k /
    (300 * (n + 1) ^ 2)) <|
  min (0.001 * shqrOmega n B Γ δ / ((66 + 2 * shqrC k (4 * B)) * (4 * B) * (4 * S) *
    ((2 + 2 * shqrC k (4 * B)) * (4 * S) / shqrDist n k B Γ S δ φ) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2))) <|
  min (0.005 * shqrEps k (4 * B) * shqrRadiusLo k (4 * B) * shqrOmega n B Γ δ /
    (6 * (1.1 * (4 * S) + 3 * shqrRadiusHi k (4 * B) * (4 * S))))
  (shqrEps k (4 * B) * shqrRadiusLo k (4 * B) * shqrOmega n B Γ δ *
    √(shqrSmallEigFailure n B Γ S δ φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8 /
      (6 * (1.1 * (4 * S) + 3 * shqrRadiusHi k (4 * B) * (4 * S))))

/-- The precision term of the iteration loop: $F$ iterations of Regularize and Sh, each with
backward error $(3.1 + C) \cdot 4\Sigma((1 + 300(n + 1)^2\boldsymbol{u})^k - 1)$, stay within a
sixth of the budget per round. -/
noncomputable def uShQRLoop (n k : ℕ) (B Γ S δ : ℝ) : ℝ :=
  min (1 / (2 * k * (300 * (n + 1) ^ 2)))
    (shqrBudget n B Γ δ / (6 * (n + 1)) / (shqrCap n B Γ S δ * ((3.1 + shqrC k (4 * B)) *
      (4 * S)) * (2 * k * (300 * (n + 1) ^ 2))))

/-- **The precision threshold of the rounded shifted QR algorithm**
[BanksGarzaVargasSrivastava2022, Theorem 6.3], recomputed for the corrected constants of the
blocks (the shift reach $C$, Optimal's rounding factor $kn^{3/2}$, the cap $F$): the minimum of
the named per-block terms `NLAlib.ShiftedQR.uShQRBasic`, `NLAlib.ShiftedQR.uShQRRegularize`,
`NLAlib.ShiftedQR.uShQRSh` and `NLAlib.ShiftedQR.uShQRLoop`. -/
noncomputable def uShQR (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  min (uShQRBasic n k) <| min (uShQRRegularize n k B Γ S δ φ) <|
    min (uShQRSh n k B Γ S δ φ) (uShQRLoop n k B Γ S δ)

/-! ### The words that depend on the precision threshold -/

/-- The bottom-scan threshold word of the iteration,
$(1 + \boldsymbol{u}_{\mathrm{ShQR}})^2\omega^2$ (at least $(1 + \boldsymbol{u})^2\omega^2$ for
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$). -/
noncomputable def shqrScanThreshold (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  (1 + uShQR n k B Γ S δ φ) ^ 2 * shqrOmega n B Γ δ ^ 2

/-- The scan threshold word $t_L = (1 + \boldsymbol{u}_{\mathrm{ShQR}})^2 t/(1 -
\boldsymbol{u}_{\mathrm{ShQR}})^2$ of the decoupling loop, for the iteration's threshold word
$t$ (`NLAlib.ShiftedQR.shqrScanThreshold`): a rounded scan with $t_L$ cannot miss an entry the
iteration certified with $t$, $(1 + \boldsymbol{u})^2 t \le (1 - \boldsymbol{u})^2 t_L$. -/
noncomputable def shqrLoopThreshold (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  (1 + uShQR n k B Γ S δ φ) ^ 2 * shqrScanThreshold n k B Γ S δ φ /
    (1 - uShQR n k B Γ S δ φ) ^ 2

/-- The decoupling level
$\omega_D = \sqrt{t_L}/(1 - \boldsymbol{u}_{\mathrm{ShQR}})
= (1 + \boldsymbol{u}_{\mathrm{ShQR}})^2\omega/(1 - \boldsymbol{u}_{\mathrm{ShQR}})^2$
that a passing scan with the loop's threshold word $t_L$
(`NLAlib.ShiftedQR.shqrLoopThreshold`) certifies: $t_L \le (1 - \boldsymbol{u})^2\omega_D^2$. -/
noncomputable def shqrDecoupled (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  (1 + uShQR n k B Γ S δ φ) ^ 2 * shqrOmega n B Γ δ / (1 - uShQR n k B Γ S δ φ) ^ 2

/-- The worklist's deflation threshold word $(1 + \boldsymbol{u}_{\mathrm{ShQR}})^2\omega_D^2$. -/
noncomputable def shqrDeflationThreshold (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  (1 + uShQR n k B Γ S δ φ) ^ 2 * shqrDecoupled n k B Γ S δ φ ^ 2

/-- The worklist's cut level
$c = (1 + \boldsymbol{u}_{\mathrm{ShQR}})\omega_D/(1 - \boldsymbol{u}_{\mathrm{ShQR}})$. -/
noncomputable def shqrCut (n k : ℕ) (B Γ S δ φ : ℝ) : ℝ :=
  (1 + uShQR n k B Γ S δ φ) * shqrDecoupled n k B Γ S δ φ / (1 - uShQR n k B Γ S δ φ)

/-- The backward error of the decoupler on a block, $F(3.1 + C) \cdot 4\Sigma((1 +
300(n + 1)^2\boldsymbol{u})^k - 1)$: $F$ iterations of Regularize and Sh on iterates of norm at
most $4\Sigma$. -/
noncomputable def shqrDecoupleError (n k : ℕ) (B Γ S δ u : ℝ) : ℝ :=
  shqrCap n B Γ S δ * ((3.1 + shqrC k (4 * B)) * (4 * S) * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))

/-! ### Positivity

Without these the headline would be vacuous through $0 \le \boldsymbol{u} \le$ `uShQR` and the bit
count $\log_2(1/\boldsymbol{u}_{\mathrm{ShQR}})$ would be junk. -/

section Positivity

variable {n k : ℕ} {B Γ S δ φ : ℝ}

theorem shqrBudget_pos (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) : 0 < shqrBudget n B Γ δ := by
  have : 0 < B := by linarith
  unfold shqrBudget; positivity

theorem shqrOmega_pos (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) : 0 < shqrOmega n B Γ δ := by
  have := shqrBudget_pos (n := n) hB hΓ hδ
  unfold shqrOmega; positivity

theorem one_le_shqrCap : 1 ≤ shqrCap n B Γ S δ := by
  unfold shqrCap; omega

/-- The failure allowed to `SmallEig` is positive: for $\varphi > 0$,
$0 < \varphi/(12F(n + 1))$. -/
theorem shqrSmallEigFailure_pos (hφ : 0 < φ) : 0 < shqrSmallEigFailure n B Γ S δ φ := by
  have : (1 : ℝ) ≤ shqrCap n B Γ S δ := by exact_mod_cast one_le_shqrCap
  unfold shqrSmallEigFailure; positivity

theorem shqrRadius_pos (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hS : 0 < S) :
    0 < shqrRadius n B Γ S δ := by
  have := shqrOmega_pos (n := n) hB hΓ hδ
  unfold shqrRadius; positivity

/-- The forward accuracy required of `SmallEig` is positive: for $B \ge 1$, $\Gamma > 0$,
$\delta > 0$ and $\Sigma > 0$, $0 < \omega^2/(8080 \cdot 4\Sigma)$. -/
theorem shqrSmallEigAccuracy_pos (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hS : 0 < S) :
    0 < shqrSmallEigAccuracy n B Γ S δ :=
  shqrRadius_pos hB hΓ hδ hS

theorem shqrEta_pos (hk : 0 < k) (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hS : 0 < S)
    (hφ : 0 < φ) : 0 < shqrEta n k B Γ S δ φ := by
  have := shqrRadius_pos (n := n) hB hΓ hδ hS
  have := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have : (0 : ℝ) < k := by exact_mod_cast hk
  unfold shqrEta shqrRegularizeFailure; positivity

theorem shqrDist_pos (hk : 0 < k) (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hS : 0 < S)
    (hφ : 0 < φ) : 0 < shqrDist n k B Γ S δ φ := by
  have hB4 : 0 < 4 * B := by linarith
  have := shqrEta_pos (n := n) hk hB hΓ hδ hS hφ
  have := shqrOmega_pos (n := n) hB hΓ hδ
  have := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have := shqrEps_pos k hB4
  have := shqrRadiusLo_pos k hB4
  unfold shqrDist; positivity

theorem shqrC_pos (k : ℕ) (hB : 0 < B) : 0 < shqrC k B := by
  have := shqrRadiusHi_pos k hB
  unfold shqrC; positivity

/-- The precision threshold is positive: for $k \ge 1$, $B \ge 1$, $\Gamma > 0$,
$\delta > 0$, $\Sigma > 0$ and $\varphi > 0$, $0 < \boldsymbol{u}_{\mathrm{ShQR}}$. -/
theorem uShQR_pos (hk : 0 < k) (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hS : 0 < S)
    (hφ : 0 < φ) : 0 < uShQR n k B Γ S δ φ := by
  have hB4 : 0 < 4 * B := by linarith
  have hω := shqrOmega_pos (n := n) hB hΓ hδ
  have hb := shqrBudget_pos (n := n) hB hΓ hδ
  have hη := shqrEta_pos (n := n) hk hB hΓ hδ hS hφ
  have hd := shqrDist_pos (n := n) hk hB hΓ hδ hS hφ
  have hf := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have := shqrEps_pos k hB4
  have := shqrRadiusLo_pos k hB4
  have := shqrRadiusHi_pos k hB4
  have := shqrTheta_pos k hB4
  have := shqrC_pos k hB4
  have hF : (1 : ℝ) ≤ shqrCap n B Γ S δ := by exact_mod_cast one_le_shqrCap
  have : (0 : ℝ) < k := by exact_mod_cast hk
  unfold uShQR uShQRBasic uShQRRegularize uShQRSh uShQRLoop
  refine lt_min (by positivity) (lt_min ?_ (lt_min ?_ ?_))
  · exact lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity))))
  · exact lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (by positivity)))
  · exact lt_min (by positivity) (by positivity)

end Positivity

/-! ### Facts about the choices -/

section Facts

variable {n k : ℕ} {B Γ S δ φ u : ℝ}

theorem uShQR_le_uShQRBasic : uShQR n k B Γ S δ φ ≤ uShQRBasic n k := min_le_left _ _

theorem uShQR_le_uShQRRegularize : uShQR n k B Γ S δ φ ≤ uShQRRegularize n k B Γ S δ φ :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem uShQR_le_uShQRSh : uShQR n k B Γ S δ φ ≤ uShQRSh n k B Γ S δ φ :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem uShQR_le_uShQRLoop : uShQR n k B Γ S δ φ ≤ uShQRLoop n k B Γ S δ :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem uShQR_le_one_div_ten : uShQR n k B Γ S δ φ ≤ 1 / 10 :=
  uShQR_le_uShQRBasic.trans (min_le_left _ _)

/-- The counting conditions: $(n + 1)\boldsymbol{u} \le 1/2500$, $10^5k\boldsymbol{u} \le 1$ and
$10^5(n + 1 + k)^2\boldsymbol{u} \le 1$. -/
theorem counts_of_le_uShQR (hu0 : 0 ≤ u) (hu : u ≤ uShQR n k B Γ S δ φ) :
    (n + 1 : ℝ) * u ≤ 1 / 2500 ∧ 100000 * k * u ≤ 1 ∧
      100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1 := by
  have h := hu.trans (uShQR_le_uShQRBasic.trans (min_le_right _ _))
  have hN : (0 : ℝ) < ((n + 1 + k : ℕ) : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ (by positivity)] at h
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have h1 : (1 : ℝ) ≤ ((n + 1 + k : ℕ) : ℝ) := by push_cast; linarith
  have hsq : ((n + 1 + k : ℕ) : ℝ) ≤ ((n + 1 + k : ℕ) : ℝ) ^ 2 := by nlinarith
  have hn1 : (n + 1 : ℝ) ≤ ((n + 1 + k : ℕ) : ℝ) ^ 2 := by
    have : (n + 1 : ℝ) ≤ ((n + 1 + k : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hk1 : (k : ℝ) ≤ ((n + 1 + k : ℕ) : ℝ) ^ 2 := by
    have : (k : ℝ) ≤ ((n + 1 + k : ℕ) : ℝ) := by push_cast; linarith
    linarith
  refine ⟨?_, ?_, by linarith⟩ <;> nlinarith

theorem shqrBudget_le_left : shqrBudget n B Γ δ ≤ δ := min_le_left _ _

theorem shqrBudget_le_right : shqrBudget n B Γ δ ≤ Γ / (16 * (n + 1) * B) := min_le_right _ _

theorem shqrOmega_mul : shqrOmega n B Γ δ * (12 * (n + 1)) = shqrBudget n B Γ δ := by
  unfold shqrOmega; field_simp

theorem shqrOmega_le_div (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) :
    shqrOmega n B Γ δ ≤ shqrBudget n B Γ δ / 12 := by
  have := shqrBudget_pos (n := n) hB hΓ hδ
  unfold shqrOmega
  gcongr
  have : (0 : ℝ) ≤ n := by positivity
  linarith

theorem shqrOmega_le_S (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) :
    shqrOmega n B Γ δ ≤ S := by
  have := shqrOmega_le_div (n := n) hB hΓ hδ
  have := shqrBudget_pos (n := n) hB hΓ hδ
  linarith [shqrBudget_le_left (n := n) (B := B) (Γ := Γ) (δ := δ)]

/-- The cap outlasts the contraction: $0.8016^F \cdot 4\Sigma < \omega$. -/
theorem shqrContraction_pow_shqrCap_mul_lt (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ)
    (hS : 0 < S) : shqrContraction ^ shqrCap n B Γ S δ * (4 * S) < shqrOmega n B Γ δ := by
  have hω := shqrOmega_pos (n := n) hB hΓ hδ
  set ρ := shqrContraction with hρ
  have hρ0 : 0 < ρ := by rw [hρ, shqrContraction]; norm_num
  have hρ1 : ρ < 1 := by rw [hρ, shqrContraction]; norm_num
  have hl : 0 < log (1 / ρ) := log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hρ0, hρ1⟩)
  set x := log (4 * S / shqrOmega n B Γ δ) / log (1 / ρ)
  set m := ⌈x⌉₊
  have hm : x ≤ m := Nat.le_ceil x
  have hlogρ : log ρ = -log (1 / ρ) := by rw [one_div, log_inv, neg_neg]
  -- $\rho^m \cdot 4\Sigma \le \omega$
  have h1 : ρ ^ m * (4 * S) ≤ shqrOmega n B Γ δ := by
    rw [← log_le_log_iff (by positivity) hω, log_mul (by positivity) (by positivity), log_pow,
      hlogρ]
    have : log (4 * S / shqrOmega n B Γ δ) ≤ m * log (1 / ρ) := by
      rw [div_le_iff₀ hl] at hm; linarith
    rw [log_div (by positivity) hω.ne'] at this
    linarith
  calc ρ ^ shqrCap n B Γ S δ * (4 * S) = ρ * (ρ ^ m * (4 * S)) := by
        simp only [shqrCap, pow_succ, ρ, m, x]; ring
    _ ≤ ρ * shqrOmega n B Γ δ := by gcongr
    _ < shqrOmega n B Γ δ := by nlinarith

/-- The decoupler's backward error is at most a sixth of the budget per round:
$F(3.1 + C) \cdot 4\Sigma((1 + 300(n + 1)^2\boldsymbol{u})^k - 1)
\le \mathrm{budget}/(6(n + 1))$. -/
theorem shqrDecoupleError_le (hk : 0 < k) (hB : 1 ≤ B) (hS : 0 < S) (hu0 : 0 ≤ u)
    (hu : u ≤ uShQR n k B Γ S δ φ) :
    shqrDecoupleError n k B Γ S δ u ≤ shqrBudget n B Γ δ / (6 * (n + 1)) := by
  have hB4 : 0 < 4 * B := by linarith
  have hC := shqrC_pos k hB4
  have hF : (1 : ℝ) ≤ shqrCap n B Γ S δ := by exact_mod_cast one_le_shqrCap
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hL := hu.trans uShQR_le_uShQRLoop
  have h1 : u ≤ 1 / (2 * k * (300 * (n + 1) ^ 2)) := hL.trans (min_le_left _ _)
  have h2 := hL.trans (min_le_right _ _)
  set x := 300 * (n + 1) ^ 2 * u with hx
  have hx0 : 0 ≤ x := by positivity
  have hkx : k * x ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at h1
    rw [hx]; nlinarith
  -- $(1 + x)^k - 1 \le kx/(1 - kx) \le 2kx$
  have hγ : (1 + x) ^ k - 1 ≤ 2 * (k * x) := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkx0 : 0 ≤ (k : ℝ) * x := by positivity
    have e1 := Computation.one_add_pow_sub_one_le_roundingFactor (n := k) hx0 (by nlinarith)
    have e2 := Computation.roundingFactor_le (n := k) hx0 (by linarith)
    have e3 : k * x / (1 - k * x) ≤ 2 * (k * x) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg hkx0 (by linarith : (0 : ℝ) ≤ 1 - 2 * (k * x))]
    linarith
  have hpos : 0 < shqrCap n B Γ S δ * ((3.1 + shqrC k (4 * B)) * (4 * S)) *
      (2 * k * (300 * (n + 1) ^ 2)) := by positivity
  rw [le_div_iff₀ hpos] at h2
  unfold shqrDecoupleError
  rw [← hx]
  have hA : (0 : ℝ) ≤ shqrCap n B Γ S δ * ((3.1 + shqrC k (4 * B)) * (4 * S)) := by positivity
  calc (shqrCap n B Γ S δ : ℝ) * ((3.1 + shqrC k (4 * B)) * (4 * S) * ((1 + x) ^ k - 1))
      = shqrCap n B Γ S δ * ((3.1 + shqrC k (4 * B)) * (4 * S)) * ((1 + x) ^ k - 1) := by ring
    _ ≤ shqrCap n B Γ S δ * ((3.1 + shqrC k (4 * B)) * (4 * S)) * (2 * (k * x)) := by gcongr
    _ ≤ shqrBudget n B Γ δ / (6 * (n + 1)) := by rw [hx]; linarith

/-- Regularize's rounding budget for the translates:
$\beta + R + 2\boldsymbol{u}(4\Sigma + \beta + R) \le \omega^2/(2020 \cdot 4\Sigma)$ when
$4\Sigma + \beta + R \le 8\Sigma$, $\beta \le R$ and
$\boldsymbol{u} \le \omega^2/(16160(4\Sigma)^2)$. -/
theorem add_shqrRadius_add_le {β : ℝ} (hS : 0 < S)
    (hsum : 4 * S + β + shqrRadius n B Γ S δ ≤ 2 * (4 * S)) (hu0 : 0 ≤ u)
    (r1 : u ≤ shqrOmega n B Γ δ ^ 2 / (16160 * (4 * S) ^ 2)) (hβR : β ≤ shqrRadius n B Γ S δ) :
    β + shqrRadius n B Γ S δ + 2 * u * (4 * S + β + shqrRadius n B Γ S δ) ≤
      shqrOmega n B Γ δ ^ 2 / (20 * 101 * (4 * S)) := by
  have a1 : 2 * u * (4 * S + β + shqrRadius n B Γ S δ) ≤ 2 * u * (2 * (4 * S)) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have a2 : 4 * u * (4 * S) ≤ 4 * (shqrOmega n B Γ δ ^ 2 / (16160 * (4 * S) ^ 2)) * (4 * S) := by
    gcongr
  have e1 : 4 * (shqrOmega n B Γ δ ^ 2 / (16160 * (4 * S) ^ 2)) * (4 * S) =
      shqrOmega n B Γ δ ^ 2 / (4040 * (4 * S)) := by field_simp; ring
  have e2 : 2 * shqrRadius n B Γ S δ = shqrOmega n B Γ δ ^ 2 / (4040 * (4 * S)) := by
    unfold shqrRadius; field_simp; ring
  have e3 : shqrOmega n B Γ δ ^ 2 / (20 * 101 * (4 * S)) =
      2 * (shqrOmega n B Γ δ ^ 2 / (4040 * (4 * S))) := by field_simp; ring
  rw [e3]
  linarith

end Facts

end NLAlib.ShiftedQR
