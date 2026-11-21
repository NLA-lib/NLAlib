/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedShExc

/-!
# The trials of the exceptional branch of the rounded shifting strategy

The exceptional branch of `Sh` ([BanksGarzaVargasSrivastava2022, Lemma 5.3]) tries its random shifts
in turn and accepts the first that passes the potential test. Its outcome
`NLAlib.ShiftedQR.ShOutcome` is an upper Hessenberg step, recorded in the log, whose potential has
contracted; `NLAlib.ShiftedQR.shExc_pwrites` gives it except with the failure probability of the
random shifts.

## Main definitions

* `NLAlib.ShiftedQR.ShOutcome`, `NLAlib.ShiftedQR.ShExcPre`: the outcome of the branch and its
  precondition.

## Main results

* `NLAlib.ShiftedQR.shOutcome_of_accepted`: an accepted trial gives the outcome.
* `NLAlib.ShiftedQR.shExcTrials_writes`: the trials.
* `NLAlib.ShiftedQR.shExc_pwrites`: the exceptional branch as a probabilistic block.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

variable {n : ℕ}

/-- **The outcome of `Sh`**, with the decoupling rate $\gamma$, the scan threshold $t$ and the
backward error $\varepsilon$: the flag is $1$ and `a` holds an upper Hessenberg perturbed unitary
similarity $\widehat{\mathbf{H}}$ of $\mathbf{H}$ with error $\varepsilon$ that is decoupled at
the bottom (one of its last $k$ subdiagonal entries passes the scan) or has
$\psi_k(\widehat{\mathbf{H}}) \le 1.002(1 - \gamma)\psi_k(\mathbf{H})$. -/
def ShOutcome (u : ℝ) (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (γ tv ε : ℝ)
    (a f lg : ℕ × ℕ) (ns w : ℕ) (LL : List (Option (List GivensEntry))) (c : ℕ) (m' : Mem ℝ) :
    Prop :=
  m'.store.get f.1 f.2 = some 1 ∧ ∃ Ls : List (Option (List GivensEntry)), Ls.length = c ∧
    (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store ∧
  ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries w Ls)) H H' ε ∧
      IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
    ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
      hessenbergPotential k H' ≤ 1.002 * (1 - γ) * hessenbergPotential k H)

/-- An accepted trial is the outcome of `Sh`: a backward-stable step with the shift $s$ repeated,
$\lvert s\rvert \le C\|\mathbf{H}\|_2$, accepted against the potential threshold
$\mathrm{fl}(1.0015(1 - \gamma)p_H)$, $p_H$ within $20\boldsymbol{u}$, relatively, of
$\psi_k(\mathbf{H})$, $\gamma \le 1$, $2 \cdot 10^5\boldsymbol{u} \le 1$, with the error
$(1 + C)\|\mathbf{H}\|_2((1 + x)^k - 1)$, by the exact unitary of the closed slots `Ls`. -/
theorem shOutcome_of_accepted {M : Machine ℝ} {u x C γ tv pH : ℝ} (hM : StdModel u id M)
    (hu : 200000 * u ≤ 1) (hx : 0 ≤ x) (hγ1 : γ ≤ 1) {k : ℕ}
    {H H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s : ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)} {a f lg : ℕ × ℕ} {m' : Mem ℝ}
    {ns w : ℕ} {LL Ls : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store)
    (hpl : ∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1)
    (hpH : |pH - hessenbergPotential k H| ≤ 20 * u * hessenbergPotential k H)
    (hs : ‖s‖ ≤ C * specNorm H) (hch : IsStableQRChainBy x H (List.replicate k s) H' Rs
      (givensLog (n + 1) (slotEntries w Ls)))
    (hH' : IsUpperHessenberg H') (hA : HoldsMatrix a H' m'.store)
    (hf : m'.store.get f.1 f.2 = some 1)
    (hacc : ShAccepted u k tv (M.mul (1.0015 * (1 - γ)) pH) H') :
    ShOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + x) ^ k - 1)) a f lg ns w LL Ls.length
      m' := by
  have hsim := hch.isPerturbedUnitarySimilarBy hx (fun t ht => by
    rw [List.eq_of_mem_replicate ht]; exact hs)
  rw [List.length_replicate] at hsim
  refine ⟨hf, Ls, rfl, hpl, hlog, H', hsim, hH', hA, ?_⟩
  rcases hacc with h | ⟨p, hp, hlt⟩
  · exact Or.inl h
  · exact Or.inr (potential_contract_of_lt hM.roundoff_nonneg hu hγ1
      (hessenbergPotential_nonneg k H) hp hpH (hM.mul _ _) hlt)

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

variable {n : ℕ}

section Trials

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has IdxTst Q] in
/-- The trials of the exceptional branch: on a scalar machine with the standard model at
$(n + 1)\boldsymbol{u} \le 1/2500$ and $10^5k\boldsymbol{u} \le 1$, exact comparisons, index
literals and exact natural literals up to $n + 1$, for $2 \le k = 2^q \le n$, $\mathbf{H}$ upper
Hessenberg with $0 < \omega \le \psi_k(\mathbf{H})$, $\gamma < 1$, the threshold word
$t \ge (1 + \boldsymbol{u})^2\omega^2$, $c_p = 1.0015(1 - \gamma)$,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with $\kappa(\mathbf{V}) \le B$,
$\|\mathbf{H}\|_2 \le \Sigma$ and the forward-error conditions $\omega > 0$, $C \ge 0$, $d > 0$,
$x = 300(n+1)^2\boldsymbol{u} \le (16B)^{-1}(d/((2 + 2C)\Sigma))^k$ and
$(66 + 2C)B\Sigma((2 + 2C)\Sigma/d)^k\sqrt{n + 1}\,x \le 0.001\,\omega$, from the state
`NLAlib.ShiftedQR.ShExcMid2` the trials end in `NLAlib.ShiftedQR.ShOutcome` with the backward error
$(1 + C)\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$. -/
theorem shExcTrials_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {L k q : ℕ}
    (hk2 : 2 ≤ k) (hkn : k ≤ n) (hkq : k = 2 ^ q) (hku : 100000 * k * u ≤ 1) {ε : ℝ}
    {a s wg wr ww wp g thr f : ℕ × ℕ} (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    {B S ω γ d C cg cr cw cp tv : ℝ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hSH : specNorm H ≤ S) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hC0 : 0 ≤ C) (hd : 0 < d)
    (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H) (hγ1 : γ < 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (16 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) (hcp : cp = 1.0015 * (1 - γ))
    (hm : ShExcMid2 M u L k ε H e ss γ cg cr cw cp tv d C a s wg wr ww wp g thr f m)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hj : LL.length + (excNet ε).length ≤ ns)
    (hw : k * n ≤ w) (hlgL : lg.1 < L) (hlgv : ∀ b ∈ [a, s, wg, wr, ww, wp, g, thr, f],
      b.1 ≠ lg.1) :
    Writes .total I τ (shTrials (O := O) (Q := Q))
      (Env.frame [n + 1, k, q, (excNet ε).length, w, LL.length] [a, (L + 10, 0), thr, (L + 2, 0),
        (L + 5, 0),
        (L + 6, 0), (L + 7, 0), (L + 8, 0), (L + 9, 0), a, (L + 11, 0), f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 6) 0 (2 * k) ⊔ Store.inBlock (L + 7) 0 (2 * k) ⊔
          Store.inBlock (L + 8) 0 5 ⊔ Store.inBlock (L + 9) 0 1) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (ShOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a f lg
        ns w LL (excNet ε).length)
      m := by
  obtain ⟨⟨ha, hs, hwg, hwr, hww, hwp, hg, hthl, hfl⟩, haf, hio⟩ := hv
  obtain ⟨⟨hA, -, -, -, -, -, -, hthr, -, hlen, -, -, h2, -, -, h5, h6, h7, h8, h9, -, -⟩,
    ⟨zs, hzs, ⟨j, hj'⟩, hdist, hnear⟩, ⟨p, hp, hPt⟩, hGw, hF⟩ := hm
  subst hcp
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlgv
  obtain ⟨lga, -, -, -, -, -, -, lgthr, lgf⟩ := hlgv
  have hu0 := hM.roundoff_nonneg
  have hk0 : 0 < k := by omega
  have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hψ0 : 0 < hessenbergPotential k H := lt_of_lt_of_le hω hψ
  have hH0 : H ≠ 0 := fun h0 => by
    have h1 : specNorm H = 0 := by rw [h0, specNorm_zero]
    linarith [hessenbergPotential_le_specNorm hk0 hkn H]
  have hthrA : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock f.1 f.2 1) (Store.inBlock thr.1 thr.2 1) := hio.mono le_rfl (by fp_sub)
  refine (shTrials_writes (τ := τ) (s := (L + 10, 0)) (pt := (L + 2, 0)) (t := (L + 5, 0))
    (sr := (L + 6, 0)) (ds := (L + 7, 0)) (rg := (L + 8, 0)) (p2 := (L + 9, 0))
    (g := (L + 11, 0)) hS hM hu1 hL hNat hC hk0 hkn hkq (by nlinarith) hH hnu hA
    (fun j => by simpa using hzs j) hthr hPt hGw hF (by simp [h5]) (by simp [h6])
    (by simp [h7]) (by simp [h8]) (by simp [h9]) (by disjoint) (by disjoint) (by disjoint)
    (by disjoint) (by disjoint)
    (Fp.disj_sup_left.mpr ⟨by disjoint, Fp.disj_sup_right.mpr ⟨by disjoint, haf.symm⟩⟩)
    (by disjoint)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_right.mpr ⟨by disjoint,
      hthrA.mono le_sup_left le_rfl⟩, by disjoint⟩, Fp.disj_sup_right.mpr ⟨by disjoint,
        hthrA.mono le_sup_right le_rfl⟩⟩)
    (by disjoint) (by disjoint) j
    (shTrial_good hM (by nlinarith) hC0 hd hω hk0 hkn hH0 hH hV hHV hκ hSH (hnear j)
      (fun i => hdist j i) hxu hbound hγ1 hψ0 hp hj') hthrω hlog hj hw
    (by simp [Mem.Live, hlen]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        refine ⟨lga, ?_, lgthr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, lgf⟩ <;> omega)).mono le_rfl ?_
  rintro m' - ⟨hf1, j', Ls, es, hLs, hpl, hlog', hse, H', Rs, hch, hH', hA', hacc⟩
  rw [← hLs]
  rw [← givensLog_padEntries (n + 1) w es, ← hse] at hch
  exact shOutcome_of_accepted hM (by nlinarith) (by positivity) hγ1.le hlog' hpl hp (hnear j')
    hch hH' hA' hf1 hacc

end Trials

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops MeasureTheory

variable {n : ℕ}

/-- The state of `Sh` before the exceptional branch: the context, the promising centre $r$ at `L`
(a pair), stagnating with the ratio $0.998(1 - \gamma)$, and at `L + 1` a $p$ within
$20\boldsymbol{u}$, relatively, of $\psi_k(\mathbf{H})$. -/
def ShExcPre (u : ℝ) (L k : ℕ) (ε : ℝ) (H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (e : Fin (n + 1) → ℂ) (ss : List ℂ) (α γ cg cr cw cp tv : ℝ)
    (a s wg wr ww wp g thr f : ℕ × ℕ) (m : Mem ℝ) : Prop :=
  ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m ∧
    (∃ r : ℂ, m.store.readBlock L 0 2 = some [r.re, r.im] ∧ IsPromisingRitzValue α V e ss r ∧
      ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖ ≤
        (0.998 * (1 - γ) * hessenbergPotential k H)⁻¹ ^ k) ∧
    ∃ p : ℝ, |p - hessenbergPotential k H| ≤ 20 * u * hessenbergPotential k H ∧
      m.store.get (L + 1) 0 = some p

section Branch

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]

omit [Has IdxTst Q] in
/-- The exceptional branch of `Sh` as a probabilistic block: on a scalar machine with the standard
model at $(n + 1)\boldsymbol{u} \le 1/2500$ and $10^5k\boldsymbol{u} \le 1$, exact comparisons,
index literals and exact natural literals up to $n + 1$, a measurable tape-local interpretation with
an exact polar sampler on a stream `s₀` uniform on $[0, 1]$, let $k = 2^q$, $\mathbf{H}$ be upper
Hessenberg, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with
$\kappa(\mathbf{V}) \le B$, $\|\mathbf{H}\|_2 \le \Sigma$, $2 \le k \le n$, the $k$ shifts `ss`
$\theta$-optimal ($\theta \ge 1$), none an eigenvalue, in $\mathbb{D}(0, 1.1\|\mathbf{H}\|_2)$,
$\psi_k(\mathbf{H}) > 0$, $0 < \gamma < 1$, $\alpha \ge 1$,
$\varepsilon = (0.998(1 - \gamma)^2/((13B^4)^{1/k}\alpha^2\theta^2))^{k/(k-1)} \le 1/2$,
$0 < \varphi \le 1/5$, $0 < d \le \varepsilon R_{\mathrm{lo}}\sqrt{q}/4$ with
$q = \varphi/(11(n + 1))$ and the window
$[R_{\mathrm{lo}}, R_{\mathrm{hi}}] =
[1.998^{1/k}, 2.002^{1/k}]\,\theta\alpha B^{1/k}\psi_k(\mathbf{H})$
of the radius, $1.1 + 2.1 \cdot 2.002^{1/k}\theta\alpha B^{1/k} \le C$, the words
$c_r = 2^{1/k}\theta\alpha B^{1/k}$ and $c_w = \varepsilon/2$, and the rounding budget
$6\boldsymbol{u}(1.1\Sigma + 3R_{\mathrm{hi}}) \le
\min(0.005, \sqrt{q}/8)\,\varepsilon R_{\mathrm{lo}}$,
the word $c_p = 1.0015(1 - \gamma)$, $0 < \omega \le \psi_k(\mathbf{H})$, a scan threshold
$t \ge (1 + \boldsymbol{u})^2\omega^2$, and
$x = 300(n+1)^2\boldsymbol{u} \le (16B)^{-1}(d/((2 + 2C)\Sigma))^k$ and
$(66 + 2C)B\Sigma((2 + 2C)\Sigma/d)^k\sqrt{n + 1}\,x \le 0.001\,\omega$. From the state
`NLAlib.ShiftedQR.ShExcPre` the branch `NLAlib.ShiftedQR.shExc` writes only the matrix, the flag and
the scratch, and ends in `NLAlib.ShiftedQR.ShOutcome` except with probability at most $\varphi$ (the
random translate). -/
theorem shExc_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {law : ℕ → Measure ℝ} {s₀ : ℕ}
    (hD : IsPolarDiskSampler s₀ I) (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {L k q : ℕ}
    (hk : 2 ≤ k) (hkn : k ≤ n) (hkq : k = 2 ^ q) (hku : 100000 * k * u ≤ 1) {ε : ℝ}
    {a s wg wr ww wp g thr f : ℕ × ℕ} (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    {B S θ α γ φ d C ω cg cr cw cp tv : ℝ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} (hH : IsUpperHessenberg H) (hlen : ss.length = k)
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hSH : specNorm H ≤ S) (hopt : IsOptimalRitzValues θ H ss)
    (hd0 : ∀ i, ∀ s ∈ ss, e i ≠ s) (hsH : ∀ s ∈ ss, ‖s‖ ≤ 1.1 * specNorm H)
    (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H) (hγ : 0 < γ) (hγ1 : γ < 1) (hθ : 1 ≤ θ)
    (hα : 1 ≤ α)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^
      ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ) (hφ1 : φ ≤ 1 / 5)
    (hd : d ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4) (hd' : 0 < d)
    (hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹)) ≤ C)
    (hexc1 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H)) ≤ 0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
        B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H))
    (hexc2 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
        B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (16 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    (hcr : cr = (2 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹))) (hcw : cw = ε / 2)
    (hcp : cp = 1.0015 * (1 - γ))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))} (hj : LL.length + (excNet
      ε).length ≤ ns) (hw : k * n ≤ w)
    (hlgL : lg.1 < L) (hlgv : ∀ b ∈ [a, s, wg, wr, ww, wp, g, thr, f], b.1 ≠ lg.1) :
    PWrites law I (shExc (O := O) (Q := Q))
      (Env.frame [n + 1, k, q, (excNet ε).length, w, LL.length] [a, (L, 0), wr, ww, wp, g, thr,
        (L + 1, 0),
        (L + 2, 0), (L + 5, 0), (L + 6, 0), (L + 7, 0), (L + 8, 0), (L + 9, 0), (L + 10, 0), a,
        (L + 11, 0), f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => ShExcPre u L k ε H V e ss α γ cg cr cw cp tv a s wg wr ww wp g thr f m ∧
        HoldsSlottedLog lg ns w LL [] m.store)
      (ShOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a f lg
        ns w LL (excNet ε).length)
      φ := by
  have hv' := hv
  obtain ⟨⟨ha, hs, hwg, hwr, hww, hwp, hg, hthl, hfl⟩, haf, hio⟩ := hv'
  have hlgv' := hlgv
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlgv'
  obtain ⟨lga, lgs, lgwg, lgwr, lgww, lgwp, lgg, lgthr, lgf⟩ := hlgv'
  have hψ0 : 0 < hessenbergPotential k H := lt_of_lt_of_le hω hψ
  have hB0 : 0 ≤ B := le_trans zero_le_one ((one_le_pseudoConditionNumber hV.ne_zero).trans hκ)
  have hX : 0 ≤ (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) := by
    have : 0 ≤ θ := by linarith
    have : 0 ≤ α := by linarith
    positivity
  have hC0 : 0 ≤ C := by linarith
  have hfI : Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
        Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length) ⊔
        Store.inBlock thr.1 thr.2 1) :=
    (Fp.disj_sup_right.mpr ⟨haf.symm, hio.mono le_sup_right le_rfl⟩).mono le_rfl (by fp_sub)
  unfold shExc
  refine (PWrites.seq hI hloc (φ₁ := 0) (φ₂ := φ + 0)
    (F₁ := Store.inBlock (L + 1) 0 1 ⊔ Store.inBlock (L + 2) 0 1 ⊔ Store.inBlock (L + 11) 0 1 ⊔
      Store.inBlock f.1 f.2 1)
    (F₂ := Store.inBlock (L + 10) 0 (2 * (excNet ε).length) ⊔
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 6) 0 (2 * k) ⊔ Store.inBlock (L + 7) 0 (2 * k) ⊔
          Store.inBlock (L + 8) 0 5 ⊔ Store.inBlock (L + 9) 0 1) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))))
    (Mid := fun m => ShExcMid1 M u L k ε H V e ss α γ cg cr cw cp tv a s wg wr ww wp g thr f m ∧
      HoldsSlottedLog lg ns w LL [] m.store) (by positivity)
    ?_ (PWrites.seq hI hloc (φ₁ := φ) (φ₂ := 0)
      (F₁ := Store.inBlock (L + 10) 0 (2 * (excNet ε).length))
      (F₂ := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 6) 0 (2 * k) ⊔ Store.inBlock (L + 7) 0 (2 * k) ⊔
          Store.inBlock (L + 8) 0 5 ⊔ Store.inBlock (L + 9) 0 1) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Mid := fun m => ShExcMid2 M u L k ε H e ss γ cg cr cw cp tv d C a s wg wr ww wp g thr f m ∧
        HoldsSlottedLog lg ns w LL [] m.store) le_rfl ?_
      ?_)).mono (fun _ h => h) ?_ (fun _ h => h) (by simp)
  · -- the start of the branch
    refine PWrites.of_writes le_rfl fun m τ ⟨⟨hctx, ⟨r, hZ, hr⟩, ⟨p, hp, hRt⟩⟩, hlog⟩ => ?_
    obtain ⟨-, -, -, hcr', -, hcp', -, -, hf', hlen', -, h1, h2, -, -, -, -, -, -, -, -, h11⟩ :=
      id hctx
    have hfo : Fp.Disj (Store.inBlock (L + 1) 0 1 ⊔ Store.inBlock (L + 2) 0 1 ⊔
        Store.inBlock (L + 11) 0 1 ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
          Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
          Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length) ⊔
          Store.inBlock thr.1 thr.2 1) :=
      Fp.disj_sup_left.mpr ⟨by disjoint, hfI⟩
    refine ((shExcInit_writes (τ := τ) (rt := (L + 1, 0)) (pt := (L + 2, 0))
      (gw := (L + 11, 0)) (f := f) hS (hNat.mono (by omega)) hcr' hcp' hRt (by simp [h2])
      (by simp [h11]) hf' (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
        ⟨Fp.disj_sup_right.mpr ⟨hfI.mono le_rfl (by fp_sub), by disjoint⟩, by disjoint⟩,
          by disjoint⟩) (by disjoint) (by disjoint)).in_frame rfl rfl
      (by simp [Mem.Live, hlen']; omega)).mono (by fp_sub) ?_
    rintro m' hfr ⟨-, hR, hP, hG, hF⟩
    exact ⟨⟨hctx.of_eqOff hfr hfo, ⟨r, hfr.keep (Store.readsOnly_readBlock _ _ _ _)
      (by disjoint) hZ, hr⟩, ⟨p, hp, hR, hP⟩, hG, hF⟩,
      hfr.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (by disjoint) hlog⟩
  · -- the exceptional shifts
    refine ((shExcShifts_pwrites hI hloc hS hM hD hU hk hkn hv hlen hV hHV hκ hSH hopt hd0 hsH hψ0
      hγ hγ1 hθ hα hε hε2 hφ hφ1 hd hd' hC1 hku hexc1 hexc2 hcr hcw).in_frame rfl rfl
      ?_).mono_eqOff (fun _ h => h.1) fun m m' h hfr h' =>
        ⟨h', hfr.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
          (Fp.disj_inBlock_of_ne (by omega)) h.2⟩
    rintro m ⟨⟨-, -, -, -, -, -, -, -, -, hlen', -⟩, -⟩
    simp [Mem.Live, hlen']
    omega
  · -- the trials
    refine PWrites.of_writes le_rfl fun m τ hm => ?_
    refine (shExcTrials_writes hS hM hu1 hL hNat hC hk hkn hkq hku hv hH hV hHV hκ hSH hnu hC0 hd'
      hω hψ hγ1 hxu hbound hthrω hcp hm.1 hm.2 hj hw hlgL hlgv).in_frame rfl rfl ?_
    obtain ⟨⟨⟨-, -, -, -, -, -, -, -, -, hlen', -⟩, -⟩, -⟩ := hm
    simp [Mem.Live, hlen']
    omega
  · fp_sub

end Branch

end NLAlib.ShiftedQR
