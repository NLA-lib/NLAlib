/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedKernels
public import NLAlib.Eigensolvers.SmallEig.DistSpec
public import NLAlib.Eigensolvers.SmallEig.OneEigMath
public import NLAlib.Matrix.QRIteration.EigenvectorWeights

/-!
# `OneEig`: one approximate eigenvalue by a regularized search

`OneEig` ([BanksGarzaVargasSrivastava2025, §3.2]) finds a point within $\beta'$ of the spectrum of
an upper Hessenberg matrix whose eigenvalues all carry weight, and at least $\eta_1$ away from it:
from a disk sample $s_0$ of radius $\eta_2$ (not the paper's unperturbed start, its erratum B3),
each round estimates the distances of the six perturbed net points $s + \tau e^{i\pi j/3} + w$
with `DistSpec` and moves to the best one if its estimate is at most $0.66\,\tau$; the search stops
with the flag $0$ when the estimate is at most $0.9\beta'$, with the flag $1$ if a round makes no
progress or the round cap $t$ is reached. One attempt, no retry loop (the paper's erratum P13):
a failure is counted in the probability.

## Main definitions

* `NLAlib.SmallEig.oneEig`: the program `[N, m, q, t] (H, Q) → (Lam, Fl)`.

## Main results

* `NLAlib.SmallEig.oneEig_writes_word`, `NLAlib.SmallEig.oneEig_pwrites`,
  `NLAlib.SmallEig.oneEig_terminates`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]

/-- **`OneEig`** ([BanksGarzaVargasSrivastava2025, Proposition 3.5], corrected): the six
directions $e^{i\pi j/3}$ from the literals $1$, $1/2$ and $\sqrt3$; the start `Lam` a polar
sample of the radius $\eta_2$ = `Q[4]` and its estimate $\tau$ by `NLAlib.SmallEig.distSpec`; the
flag $0$; then, while $0.9\beta'$ = `Q[5]` $< \tau$ and for at most $t$ rounds: one polar sample
$w$, the estimates of the six points $s + \tau e^{i\pi j/3} + w$, and the move to the best one if
its estimate is at most $0.66\,\tau$, otherwise the flag $1$ and the estimate $0$ (which ends the
loop); at the cap with $0.9\beta' < \tau$, the flag $1$. The interface is
`[N, m, q, t] (H, Q) → (Lam, Fl)`; the scratch is scoped.
Algorithm: small-eig -/
def oneEig : Impl O Q := opsImpl% [N, m, q, t] (H, Qw) → (Lam, Fl) {
  let Tau ← alloc 1;
  let Z ← alloc 2;
  let Pt ← alloc 2;
  let Tc ← alloc 1;
  let Bt ← alloc 3;
  let D ← alloc 12;
  let K ← alloc 2;
  call (Has.inj (ScalarOp.lit (66 / 100))) [] () → (K);
  call (Has.inj (ScalarOp.lit 1)) [] () → (D);
  call (Has.inj (ScalarOp.lit 0)) [] () → (D[1]);
  call (Has.inj (ScalarOp.lit (1 / 2))) [] () → (D[2]);
  call (Has.inj (ScalarOp.lit 3)) [] () → (D[3]);
  call (Has.inj ScalarOp.sqrt) [] (D[3]) → (D[3]);
  call (Has.inj ScalarOp.mul) [] (D[3], D[2]) → (D[3]);
  call (Has.inj ScalarOp.neg) [] (D[2]) → (D[4]);
  call (Has.inj ScalarOp.copy) [] (D[3]) → (D[5]);
  call (Has.inj ScalarOp.neg) [] (D) → (D[6]);
  call (Has.inj (ScalarOp.lit 0)) [] () → (D[7]);
  call (Has.inj ScalarOp.copy) [] (D[4]) → (D[8]);
  call (Has.inj ScalarOp.neg) [] (D[3]) → (D[9]);
  call (Has.inj ScalarOp.copy) [] (D[2]) → (D[10]);
  call (Has.inj ScalarOp.copy) [] (D[9]) → (D[11]);
  call (Has.inj DiskSampleOp.polar) [] (Qw[4]) → (Lam);
  run (distSpec (O := O) (Q := Q)).body [N, m, q] (H, Lam, Tau);
  call (Has.inj IndexOp.lit) [0] () → (Fl);
  while i < t, (Has.inj CmpTst.lt) [] (Qw[5], Tau) {
    call (Has.inj DiskSampleOp.polar) [] (Qw[4]) → (Z);
    call (Has.inj ScalarOp.mul) [] (Tau, K) → (Bt[2]);
    call (Has.inj IndexOp.lit) [0] () → (K[1]);
    for j < 6 {
      call (Has.inj ScalarOp.mul) [] (Tau, D[2 * j]) → (Pt);
      call (Has.inj ScalarOp.add) [] (Pt, Lam) → (Pt);
      call (Has.inj ScalarOp.add) [] (Pt, Z) → (Pt);
      call (Has.inj ScalarOp.mul) [] (Tau, D[2 * j + 1]) → (Pt[1]);
      call (Has.inj ScalarOp.add) [] (Pt[1], Lam[1]) → (Pt[1]);
      call (Has.inj ScalarOp.add) [] (Pt[1], Z[1]) → (Pt[1]);
      run (distSpec (O := O) (Q := Q)).body [N, m, q] (H, Pt, Tc);
      if (Has.inj CmpTst.le) [] (Tc, Bt[2]) {
        call (Has.inj ScalarOp.copy) [] (Pt) → (Bt);
        call (Has.inj ScalarOp.copy) [] (Pt[1]) → (Bt[1]);
        call (Has.inj ScalarOp.copy) [] (Tc) → (Bt[2]);
        call (Has.inj IndexOp.lit) [1] () → (K[1])
      } else { skip }
    };
    if (Has.inj CmpTst.isPos) [] (K[1]) {
      call (Has.inj ScalarOp.copy) [] (Bt) → (Lam);
      call (Has.inj ScalarOp.copy) [] (Bt[1]) → (Lam[1]);
      call (Has.inj ScalarOp.copy) [] (Bt[2]) → (Tau)
    } else {
      call (Has.inj IndexOp.lit) [1] () → (Fl);
      call (Has.inj (ScalarOp.lit 0)) [] () → (Tau)
    }
  } then {
    if (Has.inj CmpTst.lt) [] (Qw[5], Tau) {
      call (Has.inj IndexOp.lit) [1] () → (Fl)
    } else { skip }
  }
}

end Program

/-- The memory of a call of `NLAlib.SmallEig.oneEig` on $\mathbf{H}$ of order $n + 1$: the
matrix at `h`, the words `qs` at `qw`, room for the pair `lam` and the flag `f`, all live and
apart. -/
def OneEigInput {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (qs : List ℝ)
    (h qw lam f : ℕ × ℕ) (μ : Mem ℝ) : Prop :=
  μ.Live [h, qw, lam, f] ∧ μ.Room [h, qw, lam, f] [2 * ((n + 1) * (n + 1)), qs.length, 2, 1] ∧
    Fp.Apart [h, qw, lam, f] [2 * ((n + 1) * (n + 1)), qs.length, 2, 1] ∧
    HoldsMatrix h H μ.store ∧ μ.store.readBlock qw.1 qw.2 qs.length = some qs

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]

/-- `NLAlib.SmallEig.oneEig` on a scalar machine with index literals, exact comparisons and an
exact polar sampler: from `NLAlib.SmallEig.OneEigInput` with at least six words, on every tape,
it writes only the pair `lam` and the flag `f`, and stores a pair and a flag $0$ or $1$. -/
theorem oneEig_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hCmp : IsCmp id I) {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {n m q t : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {qs : List ℝ} (hqs : 6 ≤ qs.length)
    {τ : Tape ℝ} {μ : Mem ℝ} {h qw lam f : ℕ × ℕ} (hin : OneEigInput H qs h qw lam f μ) :
    Writes .total I τ (oneEig (O := O) (Q := Q)).body (Env.frame [n + 1, m, q, t] [h, qw, lam, f])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ z : ℂ, μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im]) ∧
        (μ'.store.get f.1 f.2 = some (M.lit 0) ∨ μ'.store.get f.1 f.2 = some (M.lit 1))) μ := by
  sorry

/-- **`OneEig` finds a point near the spectrum** ([BanksGarzaVargasSrivastava2025,
Proposition 3.5], corrected: $\eta_2 = \min(\beta'/40, g/3)$ (P5), the round cap (P6), $\log_2$
(P7), a perturbed start (B3)): on a scalar machine with the standard model at
$\boldsymbol{u} \le 1/100$, index literals, exact natural literals up to $1$, exact comparisons,
a measurable interpretation reading the tape only in its windows and an exact polar sampler on a
stream `sU` uniform on $[0, 1]$: let $\mathbf{H}$ of order $n + 1 \ge 2$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le \kappa$, every last-row weight at least $p > 0$,
eigenvalues separated by $g > 0$, $\|\mathbf{H}\|_2 \le \Sigma'$, $0 < \beta' \le 0.8\,\Sigma'$,
$0 < \varphi \le 1$, $m = 2^q$ at least `NLAlib.SmallEig.distSpecDegree` $\kappa$ $p$, $t$ =
`NLAlib.SmallEig.oneEigRounds` $\Sigma'$ $\beta'$, $\eta_2, \eta_1$ =
`NLAlib.SmallEig.oneEigOuterRadius` $\beta'$ $g$, `NLAlib.SmallEig.oneEigInnerRadius`
$\Sigma'$ $\beta'$ $g$ $\varphi$, the words `qs` with $\eta_2$ at $4$ and $0.9\beta'$ at $5$, and
the
precision conditions of `DistSpec` at the distance $\eta_1$ and the shift reach $10\Sigma'$:
$(n + 1)\boldsymbol{u} \le 1/2500$, $30000(m + 1)\boldsymbol{u} \le 1$ and
$300(n + 1)^2\boldsymbol{u} \le (8004\kappa)^{-1}(\eta_1/(2\|\mathbf{H}\|_2 + 20\Sigma'))^m$. Then
from `NLAlib.SmallEig.OneEigInput`, except with probability at most $\varphi$, the run writes only
the pair and the flag, sets the flag to $0$ and stores a point $z$ with
$\eta_1 \le \min_i\lvert z - d_i\rvert \le \beta'$. -/
theorem oneEig_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu : u ≤ 1 / 100) (hL : IsIndexLit M I) (hNat : IsExactNatLit id M 1)
    (hCmp : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    {n m q t : ℕ} (hn : 1 ≤ n) {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {κ p g S' β' φ η₁ η₂ : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ κ) (hp : 0 < p)
    (hw : ∀ i, p ≤ lastRowWeights V i) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hHS : specNorm H ≤ S') (hβ' : 0 < β') (hβ'S : β' ≤ 0.8 * S') (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hmq : m = 2 ^ q) (hm : distSpecDegree κ p ≤ m) (ht : t = oneEigRounds S' β')
    (hη₂ : η₂ = oneEigOuterRadius β' g) (hη₁ : η₁ = oneEigInnerRadius S' β' g φ)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hum : 30000 * ((m : ℝ) + 1) * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * κ)⁻¹ * (η₁ / (2 * specNorm H + 20 * S')) ^ m)
    {qs : List ℝ} (hq4 : qs.getD 4 0 = η₂) (hq5 : qs.getD 5 0 = 0.9 * β') (hqs : 6 ≤ qs.length)
    {h qw lam f : ℕ × ℕ} :
    PWrites law I (oneEig (O := O) (Q := Q)).body (Env.frame [n + 1, m, q, t] [h, qw, lam, f])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1) (OneEigInput H qs h qw lam f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ z : ℂ,
        μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im] ∧
        η₁ ≤ ⨅ i, ‖z - d i‖ ∧ ⨅ i, ‖z - d i‖ ≤ β') φ := by
  sorry

/-- `NLAlib.SmallEig.oneEig` terminates on every tape: from `NLAlib.SmallEig.OneEigInput` with
any matrix and at least six words, it writes only the pair and the flag and stores both. -/
theorem oneEig_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hCmp : IsCmp id I) {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {n m q t : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {qs : List ℝ} (hqs : 6 ≤ qs.length)
    {τ : Tape ℝ} {μ : Mem ℝ} {h qw lam f : ℕ × ℕ} (hin : OneEigInput H qs h qw lam f μ) :
    Writes .total I τ (oneEig (O := O) (Q := Q)).body (Env.frame [n + 1, m, q, t] [h, qw, lam, f])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ z : ℂ, μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im]) ∧
        ∃ x, μ'.store.get f.1 f.2 = some x) μ := by
  sorry

end Theorems

end NLAlib.SmallEig
