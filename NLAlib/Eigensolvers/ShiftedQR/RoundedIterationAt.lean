/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedIteration

/-!
# One rounded iteration at the call site of the decoupling loop

One iteration of the loop of [BanksGarzaVargasSrivastava2022, Lemma 6.4] in floating point at the
frame the decoupling loop calls it with: the iteration (`NLAlib.ShiftedQR.shIterationWith`) opens
its own scratch log, apart from the views of the loop, and records its rotations in the slot of the
round, so the round's outcome is named by the unitary of the loop's log.

## Main results

* `NLAlib.ShiftedQR.shIterationWith_pwrites_at`, `NLAlib.ShiftedQR.shIteration_pwrites`: one
  iteration as a probabilistic block.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix
namespace NLAlib.ShiftedQR

open Ops
variable {n : ℕ}

section Assembly

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]
variable [Has EigenvalueKernelOp O]

/-- The scratch shift buffer of `NLAlib.ShiftedQR.shIterationWith`, a fresh buffer `L` above the
views, is apart from them. -/
private theorem shIterationWith_scratch_disj {L N k e q : ℕ}
    {a rd c thr wg wr ww wp g f qw : ℕ × ℕ}
    (h2 : rd.1 < L) (h3 : c.1 < L) (h4 : thr.1 < L) (h5 : wg.1 < L) (h6 : wr.1 < L)
    (h7 : ww.1 < L) (h8 : wp.1 < L) (h9 : g.1 < L) (h11 : qw.1 < L)
    (hio : Fp.Disj (Store.inBlock a.1 a.2 N ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1 ⊔
        Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
        Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 e))
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 N ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock qw.1 qw.2 q)) :
    Fp.Disj (Store.inBlock a.1 a.2 N ⊔ Store.inBlock (L, 0).1 (L, 0).2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1)
      (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1 ⊔
        Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
        Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 e) ∧
    Fp.Disj (Store.inBlock a.1 a.2 N ⊔ Store.inBlock (L, 0).1 (L, 0).2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1) (Store.inBlock qw.1 qw.2 q) := by
  have hne : ∀ {b : ℕ × ℕ} {o n' : ℕ}, b.1 < L →
      Fp.Disj (Store.inBlock b.1 b.2 o) (Store.inBlock (L, 0).1 (L, 0).2 n') :=
    fun hb => Fp.disj_inBlock_of_ne (by simp; omega)
  have := (hne h2 (o := 1) (n' := 2 * k)).symm; have := (hne h3 (o := 1) (n' := 2 * k)).symm
  have := (hne h4 (o := 1) (n' := 2 * k)).symm; have := (hne h5 (o := 1) (n' := 2 * k)).symm
  have := (hne h6 (o := 1) (n' := 2 * k)).symm; have := (hne h7 (o := 1) (n' := 2 * k)).symm
  have := (hne h8 (o := 1) (n' := 2 * k)).symm
  have := (hne h9 (o := e) (n' := 2 * k)).symm
  have := (hne h11 (o := q) (n' := 2 * k)).symm
  simp only [Fp.disj_sup_left, Fp.disj_sup_right] at hio hqw ⊢
  tauto

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The hypothesis lists of `Regularize` and `Sh` together, with their long real constants, make
-- the elaboration of the composition heavy.
omit [Has EigenvalueKernelOp O] in
/-- **One rounded iteration with a small-eigenvalue routine as a probabilistic block**, with the
word count `nq` apart from the words `qs` (`NLAlib.ShiftedQR.RandomSmallEigContractAt`), the
words stored at `qw` apart from the matrix and the flag: `NLAlib.ShiftedQR.shIteration_pwrites`
for `NLAlib.ShiftedQR.shIterationWith`. One rounded iteration of the decoupling loop as a
probabilistic block
([BanksGarzaVargasSrivastava2022, Lemma 6.4], one round, corrected: the dichotomy constant of
Theorem 4.1 is $\tfrac12 k^{-1/(2k)}$ for the printed $(2k)^{-1/(2k)}$, and the test in the proof
of Lemma 4.6 is $\psi_k \ge \varepsilon$; the net of `Exc`, Lemma 5.3, has rounding at most
$0.005\varepsilon\widetilde{R}$, covers $\mathbb{D}(r, (1 + \varepsilon)\widetilde{R})$ and has
at most $11$ points near an eigenvalue, and its radius keeps the factor $2^{1/k}$ the paper omits
($2.002^{1/k}$ for $1.001$, so the shift bound is $4.1\|\mathbf{H}\|_2$ for $3\|\mathbf{H}\|_2$);
`Sh`, Lemma 5.4, returns the computed step, assumes $\|\mathbf{H}\|_2 \le \Sigma$ and $k \ge 2$,
and reports with a flag that no shift was accepted; the precision of `Optimal`, Lemma 4.5,
carries $n + kn^{3/2}$ for the printed $2n^2$): on a scalar machine with the standard model, exact
comparisons, index literals, index conversion and exact natural literals up to $n + 1$, a
measurable tape-local interpretation whose `SmallEig` is a randomized kernel with forward error
$\beta \ge 0$ and failure probability $\varphi_{\mathrm{se}} \ge 0$ on a stream `s₀` uniform on
$[0, 1]$, and an exact polar disk sampler on the same stream: let $\mathbf{H}$ be upper Hessenberg
of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with
$\kappa(\mathbf{V}) \le B$, $B^{2/k} \le 2$, $2 \le k = 2^m \le n$, $\|\mathbf{H}\|_2 \le
\Sigma$, $0 < \omega \le \psi_k(\mathbf{H})$, eigenvalues separated by $2\omega^2/\Sigma$; the words
of `Regularize` (radius $R > 0$, $0.999\theta^k$ for
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, the threshold $t \ge (1 + \boldsymbol{u})^2
\omega^2$) with $0 < \varphi_R \le 1$, $\eta = R\sqrt{\varphi_R/(2k)}$ and $d = \eta/2$, and the
words of `Sh` ($(1 - \gamma)^k$, $2^{1/k}\theta\alpha B^{1/k}$, $\varepsilon/2$,
$1.0015(1 - \gamma)$,
the net `NLAlib.ShiftedQR.excNet ε`) with $\alpha = (1.01B)^{4m/2^m}$, $0 < \gamma < 1$,
$\varepsilon = (0.998(1 - \gamma)^2/((13B^4)^{1/k}\alpha^2\theta^2))^{k/(k-1)} \le 1/2$,
$0 < \varphi \le 1/5$, $1.1 + 2.1 \cdot 2.002^{1/k}\theta\alpha B^{1/k} \le C$,
$d \le \varepsilon \cdot 1.998^{1/k}\theta\alpha B^{1/k}\omega\sqrt{\varphi/(11(n + 1))}/4$; and the
precision conditions of `Regularize` and `Sh`, those of `Sh` that involve $\psi_k(\mathbf{H})$
asked at $\omega$ (below) and at $\Sigma$ (above). Then `NLAlib.ShiftedQR.shIteration` writes only
the matrix and the flag and, except with probability at most
$\varphi_{\mathrm{se}} + \varphi_R/2 + \varphi$, ends in `NLAlib.ShiftedQR.ShIterationOutcome`: an
upper Hessenberg perturbed unitary similarity of $\mathbf{H}$ with error
$(1 + C)\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$, decoupled at the bottom
or with $\psi_k \le 1.002(1 - \gamma)\psi_k(\mathbf{H})$.

Shared by the tree of `NLAlib.ShiftedQR.shqrSmallEigRoutine`, on its scratch. -/
theorem shIterationWith_pwrites_at {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ}
    (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse) (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k q : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    (hkn : k ≤ n) {ε : ℝ} {a rd c thr wg wr ww wp g f : ℕ × ℕ}
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1 ⊔
          Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
          Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length)))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω R φR α γ φ C tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hR : 0 < R) (hφR : 0 < φR) (hφR1 : φR ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φR / (2 * k))) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxuR : 300 * (n + 1) ^ 2 * u ≤
      (16 * B)⁻¹ * (R * √(φR / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hboundR : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hα : α = (1.01 * B) ^ ((4 * q : ℝ) / 2 ^ q)) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ 2)) ^
        ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ) (hφ1 : φ ≤ 1 / 5)
    (hd : R * √(φR / (2 * k)) / 2 ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4)
    (hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹)) ≤ C)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (8004 * B)⁻¹ * (R * √(φR / (2 * k)) / 2 / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hexc1 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * S)) ≤ 0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * ω))
    (hexc2 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * S)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) {nq T : ℕ} {qs : List ℝ} {SE : Stmt O Q}
    (hSE : RandomSmallEigContractAt law β φse k nq T S qs SE I) {qw : ℕ × ℕ}
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
        (hj : LL.length + (k + 1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ w)
    (hlgv : ∀ b ∈ [a, rd, c, thr, wg, wr, ww, wp, g, qw, f], b.1 ≠ lg.1) :
    PWrites law I (shIterationWith SE)
      (Env.frame [n + 1, q, k, (excNet ε).length, nq, T, w, LL.length]
        [a, rd, c, thr, wg, wr, ww, wp, g, qw, a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => m.Live [a, rd, c, thr, wg, wr, ww, wp, g, qw, f] ∧ HoldsMatrix a H m.store ∧
        m.store.readBlock qw.1 qw.2 qs.length = some qs ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ m.store.get wg.1 wg.2 = some ((1 - γ) ^ k) ∧
        m.store.get wr.1 wr.2 = some ((2 : ℝ) ^ ((k : ℝ)⁻¹) *
          ((1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
            B ^ ((k : ℝ)⁻¹))) ∧
        m.store.get ww.1 ww.2 = some (ε / 2) ∧ m.store.get wp.1 wp.2 = some (1.0015 * (1 - γ)) ∧
        m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧ f.2 < m.store.len f.1 ∧
        HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg])
      (ShIterationOutcomeBy u k H γ tv
          ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))
        a lg ns w LL (k + 1 + (excNet ε).length)) (φse + φR / 2 + φ) := by
  have hφ0 : 0 ≤ φse + φR / 2 + φ := by positivity
  have e : (shIterationWith SE) = Stmt.allocs [.const 2 * .var 2]
      (.frame [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7] [⟨0, .var 8⟩,
        ⟨1, .var 9⟩, ⟨2, .var 10⟩, ⟨3, .var 11⟩, ⟨4, .var 12⟩, ⟨5, .var 13⟩, ⟨6, .var 14⟩,
        ⟨7, .var 15⟩, ⟨8, .var 16⟩, ⟨9, .var 17⟩, ⟨13, .const 0⟩, ⟨0, .var 8⟩, ⟨11, .var 19⟩,
        ⟨12, .var 20⟩]
        (shIterationWithScratchWith SE)) :=
    rfl
  rw [e]
  refine PWrites.allocs (ns := [2 * k]) ?_ (Pre₁ := fun L μ => (a.1 < L ∧ rd.1 < L ∧ c.1 < L ∧
      thr.1 < L ∧ wg.1 < L ∧ wr.1 < L ∧ ww.1 < L ∧ wp.1 < L ∧ g.1 < L ∧ f.1 < L ∧ qw.1 < L ∧
      lg.1 < L) ∧
    μ.Live [a, rd, c, thr, wg, wr, ww, wp, g, qw, (L, 0), f] ∧ HoldsMatrix a H μ.store ∧
      μ.store.readBlock qw.1 qw.2 qs.length = some qs ∧
      μ.store.get rd.1 rd.2 = some R ∧ μ.store.get c.1 c.2 = some
        (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
      μ.store.get thr.1 thr.2 = some tv ∧ μ.store.get wg.1 wg.2 = some ((1 - γ) ^ k) ∧
      μ.store.get wr.1 wr.2 = some ((2 : ℝ) ^ ((k : ℝ)⁻¹) *
        ((1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
          B ^ ((k : ℝ)⁻¹))) ∧
      μ.store.get ww.1 ww.2 = some (ε / 2) ∧ μ.store.get wp.1 wp.2 = some (1.0015 * (1 - γ)) ∧
      μ.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
        some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧
      0 + 2 * k ≤ μ.store.len L ∧ f.2 < μ.store.len f.1 ∧
      HoldsSlottedLog lg ns w LL [] μ.store ∧ μ.Live [lg]) ?_ ?_ fun L => ?_
  · rfl
  · rintro m s₁ ⟨hl, hA, hq, hrd, hc, ht, hwg, hwr, hww, hwp, hg, hf, hlog, hlgl⟩ hlen hlens
      hBelow
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11, h10⟩ : a.1 < m.store.length ∧
        rd.1 < m.store.length ∧ c.1 < m.store.length ∧ thr.1 < m.store.length ∧
        wg.1 < m.store.length ∧ wr.1 < m.store.length ∧ ww.1 < m.store.length ∧
        wp.1 < m.store.length ∧ g.1 < m.store.length ∧ qw.1 < m.store.length ∧
        f.1 < m.store.length := by
      simpa [Mem.Live] using hl
    have hlg1 : lg.1 < m.store.length := hlgl lg (by simp)
    have hl0 := hlens 0 (by simp)
    simp only [List.length_cons, List.length_nil] at hlen
    refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hlg1⟩, ?_, hA.of_below hBelow h1,
      (hBelow.readBlock h11 qw.2 qs.length).trans hq, hBelow.get_of h2 hrd, hBelow.get_of h3 hc,
      hBelow.get_of h4 ht, hBelow.get_of h5 hwg,
      hBelow.get_of h6 hwr, hBelow.get_of h7 hww, hBelow.get_of h8 hwp,
      hBelow.readBlock_of h9 hg, by simpa using hl0.ge, by rw [(hBelow f.1 h10).1]; exact hf,
      hBelow.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
        (fun b i g => by rw [g.1]; exact hlg1) hlog, by simp [Mem.Live, hlen]; omega⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, hlen]
    omega
  · rintro m ⟨hl, -, -, -, -, -, -, -, -, -, -, -, -, hlgl⟩ st st' p hBelow
      ⟨Ls, hLs, hpl, hlog, H', hsim, hH', hA, hdec⟩
    have h1 : a.1 < m.store.length := hl a (by simp)
    exact ⟨Ls, hLs, hpl, hBelow.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
      (fun b i g => by rw [g.1]; exact hlgl lg (by simp)) hlog, H', hsim, hH',
      hA.of_below hBelow h1, hdec⟩
  · by_cases hvL : a.1 < L ∧ rd.1 < L ∧ c.1 < L ∧ thr.1 < L ∧ wg.1 < L ∧ wr.1 < L ∧
        ww.1 < L ∧ wp.1 < L ∧ g.1 < L ∧ f.1 < L ∧ qw.1 < L ∧ lg.1 < L
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hvL
      have hne : ∀ {b : ℕ × ℕ} {o n' : ℕ}, b.1 < L →
          Fp.Disj (Store.inBlock b.1 b.2 o) (Store.inBlock (L, 0).1 (L, 0).2 n') :=
        fun hb => Fp.disj_inBlock_of_ne (by simp; omega)
      obtain ⟨hio', hqw'⟩ := shIterationWith_scratch_disj (k := k) h2 h3 h4 h5 h6 h7 h8 h9 h11 hio
        hqw
      have hlgv' : ∀ b ∈ [a, rd, c, thr, wg, wr, ww, wp, g, qw, (L, 0), f], b.1 ≠ lg.1 :=
        fun b hb => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact (show L ≠ lg.1 by omega) | exact hlgv _ (by simp)
      refine ((shIterationWithScratchWith_pwrites (s := (L, 0)) hI hloc hS hM hu1 hL hNat hC hQ
        hβ0 hφse hD hU hkq hk hkn (hne h1) haf (hne h10).symm hio' hH hV hHV hκ hBk hω hψ hSH
        hgap hR hφR hφR1 hβ hdη hnu huo huo1 hxuR hboundR hα hγ hγ1 hε hε2 hφ hφ1 hd hC1 hxu
        hbound hexc1 hexc2 hthrω hSE hqw' hj hw hlgv').in_frame ?_ ?_ ?_).mono (fun _ h => h.2)
        (by fp_sub) (fun _ h => h) le_rfl
      · rfl
      · rfl
      · rintro μ ⟨hl, -, -, -, -, -, -, -, -, -, -, -, -, -, hlg⟩
        simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] at hl hlg ⊢
        tauto
    · exact PWrites.of_writes hφ0 fun _ _ h => absurd h.1 hvL

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The hypothesis lists of `Regularize` and `Sh` together, with their long real constants, make
-- the elaboration of the composition heavy.
/-- **One rounded iteration of the decoupling loop as a probabilistic block**
([BanksGarzaVargasSrivastava2022, Lemma 6.4], one round, corrected: the dichotomy constant of
Theorem 4.1 is $\tfrac12 k^{-1/(2k)}$ for the printed $(2k)^{-1/(2k)}$, and the test in the proof
of Lemma 4.6 is $\psi_k \ge \varepsilon$; the net of `Exc`, Lemma 5.3, has rounding at most
$0.005\varepsilon\widetilde{R}$, covers $\mathbb{D}(r, (1 + \varepsilon)\widetilde{R})$ and has
at most $11$ points near an eigenvalue, and its radius keeps the factor $2^{1/k}$ the paper omits
($2.002^{1/k}$ for $1.001$, so the shift bound is $4.1\|\mathbf{H}\|_2$ for $3\|\mathbf{H}\|_2$);
`Sh`, Lemma 5.4, returns the computed step, assumes $\|\mathbf{H}\|_2 \le \Sigma$ and $k \ge 2$,
and reports with a flag that no shift was accepted; the precision of `Optimal`, Lemma 4.5,
carries $n + kn^{3/2}$ for the printed $2n^2$): on a scalar machine with the standard model, exact
comparisons, index literals, index conversion and exact natural literals up to $n + 1$, a
measurable tape-local interpretation whose `SmallEig` is a randomized kernel with forward error
$\beta \ge 0$ and failure probability $\varphi_{\mathrm{se}} \ge 0$ on a stream `s₀` uniform on
$[0, 1]$, and an exact polar disk sampler on the same stream: let $\mathbf{H}$ be upper Hessenberg
of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with
$\kappa(\mathbf{V}) \le B$, $B^{2/k} \le 2$, $2 \le k = 2^m \le n$, $\|\mathbf{H}\|_2 \le
\Sigma$, $0 < \omega \le \psi_k(\mathbf{H})$, eigenvalues separated by $2\omega^2/\Sigma$; the words
of `Regularize` (radius $R > 0$, $0.999\theta^k$ for
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, the threshold $t \ge (1 + \boldsymbol{u})^2
\omega^2$) with $0 < \varphi_R \le 1$, $\eta = R\sqrt{\varphi_R/(2k)}$ and $d = \eta/2$, and the
words of `Sh` ($(1 - \gamma)^k$, $2^{1/k}\theta\alpha B^{1/k}$, $\varepsilon/2$,
$1.0015(1 - \gamma)$,
the net `NLAlib.ShiftedQR.excNet ε`) with $\alpha = (1.01B)^{4m/2^m}$, $0 < \gamma < 1$,
$\varepsilon = (0.998(1 - \gamma)^2/((13B^4)^{1/k}\alpha^2\theta^2))^{k/(k-1)} \le 1/2$,
$0 < \varphi \le 1/5$, $1.1 + 2.1 \cdot 2.002^{1/k}\theta\alpha B^{1/k} \le C$,
$d \le \varepsilon \cdot 1.998^{1/k}\theta\alpha B^{1/k}\omega\sqrt{\varphi/(11(n + 1))}/4$; and the
precision conditions of `Regularize` and `Sh`, those of `Sh` that involve $\psi_k(\mathbf{H})$
asked at $\omega$ (below) and at $\Sigma$ (above). Then `NLAlib.ShiftedQR.shIteration` writes only
the matrix and the flag and, except with probability at most
$\varphi_{\mathrm{se}} + \varphi_R/2 + \varphi$, ends in `NLAlib.ShiftedQR.ShIterationOutcome`: an
upper Hessenberg perturbed unitary similarity of $\mathbf{H}$ with error
$(1 + C)\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$, decoupled at the bottom
or with $\psi_k \le 1.002(1 - \gamma)\psi_k(\mathbf{H})$. -/
theorem shIteration_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ} (hSE : IsRandomSmallEig law s₀ β φse I)
    (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse) (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k q : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    (hkn : k ≤ n) {ε : ℝ} {a rd c thr wg wr ww wp g f : ℕ × ℕ}
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1 ⊔
          Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
          Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length)))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω R φR α γ φ C tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hR : 0 < R) (hφR : 0 < φR) (hφR1 : φR ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φR / (2 * k))) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxuR : 300 * (n + 1) ^ 2 * u ≤
      (16 * B)⁻¹ * (R * √(φR / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hboundR : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hα : α = (1.01 * B) ^ ((4 * q : ℝ) / 2 ^ q)) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ 2)) ^
        ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ) (hφ1 : φ ≤ 1 / 5)
    (hd : R * √(φR / (2 * k)) / 2 ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4)
    (hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹)) ≤ C)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (8004 * B)⁻¹ * (R * √(φR / (2 * k)) / 2 / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hexc1 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * S)) ≤ 0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * ω))
    (hexc2 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * S)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
        (hj : LL.length + (k + 1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ w)
    (hlgv : ∀ b ∈ [a, rd, c, thr, wg, wr, ww, wp, g, f], b.1 ≠ lg.1) :
    PWrites law I (shIteration (O := O) (Q := Q))
      (Env.frame [n + 1, q, k, (excNet ε).length, w, LL.length]
          [a, rd, c, thr, wg, wr, ww, wp, g, a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => m.Live [a, rd, c, thr, wg, wr, ww, wp, g, f] ∧ HoldsMatrix a H m.store ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ m.store.get wg.1 wg.2 = some ((1 - γ) ^ k) ∧
        m.store.get wr.1 wr.2 = some ((2 : ℝ) ^ ((k : ℝ)⁻¹) *
          ((1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
            B ^ ((k : ℝ)⁻¹))) ∧
        m.store.get ww.1 ww.2 = some (ε / 2) ∧ m.store.get wp.1 wp.2 = some (1.0015 * (1 - γ)) ∧
        m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧ f.2 < m.store.len f.1 ∧
        HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg])
      (ShIterationOutcomeBy u k H γ tv
          ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))
        a lg ns w LL (k + 1 + (excNet ε).length)) (φse + φR / 2 + φ) := by
  unfold shIteration
  refine ((shIterationWith_pwrites_at hI hloc hS hM hu1 hL hNat hC hQ hβ0 hφse hD hU hkq hk hkn
    haf hio hH hV hHV hκ hBk hω hψ hSH hgap hR hφR hφR1 hβ hdη hnu huo huo1 hxuR hboundR hα hγ
    hγ1 hε hε2 hφ hφ1 hd hC1 hxu hbound hexc1 hexc2 hthrω
    (hSE.randomSmallEigContractAt k 0 0 S []) (qw := rd)
    (fun _ _ _ h => by obtain ⟨-, h1, h2⟩ := h; simp at h2; omega) hj hw (fun b hb => hlgv b
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢; tauto))).in_frame
    (by simp) (by simp [Operand.evalList, Operand.eval]) ?_).mono ?_ le_rfl (fun _ h => h) le_rfl
  · rintro μ ⟨hl, -, -, -, -, -, -, -, -, -, -, -, -, hlg⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl hlg ⊢
    tauto
  · rintro μ ⟨hl, hA, hrest⟩
    refine ⟨?_, hA, by simp, hrest⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl ⊢
    tauto

end Assembly

end NLAlib.ShiftedQR
