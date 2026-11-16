/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolve
public import NLAlib.Eigensolvers.ShiftedQR.StableStep
public import NLAlib.Matrix.QRIteration.StableStepForward

/-!
# `Decouple`: decoupling the last eigenvalue by a repeated shift

`Decouple` ([BanksGarzaVargasSrivastava2025, §4]) runs rounded QR steps with one shift
$\tilde\lambda$ close to an eigenvalue of large weight until the last subdiagonal entry is small:
after each step the bottom entry is scanned against the threshold word $t_L$, and the run stops
with the flag $0$ when it passes, with the flag $1$ at the cap $m_2$ (the paper's loop is
uncapped, its erratum P13). By inverse iteration (`NLAlib.exists_le_norm_subdiag_shiftedQR_pow`)
and the forward error of the rounded steps
(`NLAlib.IsStableQRChain.exists_norm_subdiag_le_of_dist`), a shift within $\beta' = \omega/20$ of
an eigenvalue of weight at least $p$ decouples within $m_2$ steps. The scan threshold is that of
the merged decoupling loop: $(1 + \boldsymbol{u})^2\omega^2 \le t_L$.

## Main definitions

* `NLAlib.SmallEig.decoupleLast`: the program `[N, m2] (H, Lam, Q) → (H, Fl)`.

## Main results

* `NLAlib.SmallEig.decoupleLast_writes_word`, `NLAlib.SmallEig.decoupleLast_spec`,
  `NLAlib.SmallEig.decoupleLast_terminates`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **`Decouple`** ([BanksGarzaVargasSrivastava2025, Proposition 4.3], capped): scan the last
subdiagonal entry of the order-$N$ matrix `H` with the threshold $t_L$ = `Q[7]`
(`NLAlib.ShiftedQR.bottomScan` at $k = 1$); while it does not pass, for at most $m_2$ rounds, one
rounded QR step with the shift `Lam` (`NLAlib.ShiftedQR.multiStepStable` at degree $1$) and a scan;
then the flag $0$ if the last scan passed, $1$ otherwise. The interface is
`[N, m2] (H, Lam, Q) → (H, Fl)`; the registers are scoped.
Algorithm: small-eig -/
def decoupleLast : Impl O Q := opsImpl% [N, m2] (H, Lam, Qw) → (H, Fl) {
  let R ← alloc 5;
  let Ds ← alloc 2;
  run (bottomScan (O := O) (Q := Q)).body [N, 1] (H, Qw[7], R);
  while j < m2, (Has.inj CmpTst.isZero) [] (R[3]) {
    run (multiStepStable (Op := O) (Tst := Q)).body [N, 1] (H, Lam, H, Ds);
    run (bottomScan (O := O) (Q := Q)).body [N, 1] (H, Qw[7], R)
  } then {
    if (Has.inj CmpTst.isPos) [] (R[3]) {
      call (Has.inj IndexOp.lit) [0] () → (Fl)
    } else {
      call (Has.inj IndexOp.lit) [1] () → (Fl)
    }
  }
}

end Program

/-- The memory of a call of `NLAlib.SmallEig.decoupleLast` on $\mathbf{H}$ of order $n + 1$ with
the shift $\lambda$: the matrix at `h` (updated in place), the pair of $\lambda$ at `lam`, the words
`qs` at `qw` and room for the flag `f`, all live and apart. -/
def DecoupleInput {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ζ : ℂ) (qs : List ℝ)
    (h lam qw f : ℕ × ℕ) (μ : Mem ℝ) : Prop :=
  μ.Live [h, lam, qw, f] ∧ μ.Room [h, lam, qw, f] [2 * ((n + 1) * (n + 1)), 2, qs.length, 1] ∧
    Fp.Apart [h, lam, qw, f] [2 * ((n + 1) * (n + 1)), 2, qs.length, 1] ∧
    HoldsMatrix h H μ.store ∧ μ.store.readBlock lam.1 lam.2 2 = some [ζ.re, ζ.im] ∧
    μ.store.readBlock qw.1 qw.2 qs.length = some qs

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- `NLAlib.SmallEig.decoupleLast` on a scalar machine with the standard model at
$0 \le \boldsymbol{u}$, $(n + 1)\boldsymbol{u} \le 1/2500$, index literals, exact natural literals
up to $n + 1$, exact comparisons and conversion: from `NLAlib.SmallEig.DecoupleInput` with an
upper Hessenberg $\mathbf{H}$, the shift $\lambda$ and at least eight words, on every tape, it
writes only the matrix and the flag and stores the end $\widehat{\mathbf{H}}'$ of a
backward-stable chain (relative error $300(n + 1)^2\boldsymbol{u}$) of at most $m_2$ steps with the
shift $\lambda$, upper Hessenberg, and a flag $0$ or $1$; with the flag $0$ the last subdiagonal
entry $h$ of $\widehat{\mathbf{H}}'$ passed the scan,
$(1 - \boldsymbol{u})^2\lvert h\rvert^2 \le t_L$ for the word $t_L$ = `qs[7]`. -/
theorem decoupleLast_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu : 0 ≤ u) (hL : IsIndexLit M I) (hC : IsCmp id I)
    (hQ : IsToNat id I) {n m₂ : ℕ} (hNat : IsExactNatLit id M (n + 1))
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {ζ : ℂ}
    {qs : List ℝ} (hqs : 8 ≤ qs.length) (hH : IsUpperHessenberg H) {τ : Tape ℝ} {μ : Mem ℝ}
    {h lam qw f : ℕ × ℕ} (hin : DecoupleInput H ζ qs h lam qw f μ) :
    Writes .total I τ (decoupleLast (O := O) (Q := Q)).body
      (Env.frame [n + 2, m₂] [h, lam, qw, h, f])
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => ∃ (ℓ : ℕ) (H' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
        (Rs : List (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)), ℓ ≤ m₂ ∧
        IsStableQRChain (300 * (n + 2) ^ 2 * u) H (List.replicate ℓ ζ) H' Rs ∧
        IsUpperHessenberg H' ∧ HoldsMatrix h H' μ'.store ∧
        ((μ'.store.get f.1 f.2 = some 0 ∧
            (1 - u) ^ 2 * ‖H' (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2 ≤ qs.getD 7 0) ∨
          μ'.store.get f.1 f.2 = some 1)) μ := by
  sorry

/-- **`Decouple` decouples the last eigenvalue** ([BanksGarzaVargasSrivastava2025,
Proposition 4.3], capped; deterministic): on a scalar machine with the standard model at
$0 \le \boldsymbol{u} < 1$, index literals, exact natural literals up to $n + 2$, exact
comparisons and conversion: let $\mathbf{H} \ne 0$ of order $n + 2$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$, the shift $\lambda$ with
$\lvert\lambda\rvert \le C\|\mathbf{H}\|_2$ ($C \ge 0$), at distance at least $\eta_1 > 0$ from
every $d_j$ and within $\beta'$ of an eigenvalue $d_i$ of weight $w_i \ge p > 0$,
$4\beta' \le \omega$, $1 \le m_2$, $B \le 2^{m_2}\sqrt p$, the scan threshold $t_L$ = `qs[7]` with
$(1 + \boldsymbol{u})^2\omega^2 \le t_L$, and with $x = 300(n + 2)^2\boldsymbol{u}$, for every
$\ell \le m_2$, $x \le (16B)^{-1}(\eta_1/((2 + 2C)\|\mathbf{H}\|_2))^\ell$ and
$(66 + 2C)B\|\mathbf{H}\|_2((2 + 2C)\|\mathbf{H}\|_2/\eta_1)^\ell\sqrt{n + 2}\,x \le \omega/2$. Then
from `NLAlib.SmallEig.DecoupleInput`, on every tape, the run writes only the matrix and the flag,
sets the flag to $0$, and stores an upper Hessenberg perturbed unitary similarity
$\widehat{\mathbf{H}}'$ of $\mathbf{H}$ with backward error
$(1 + C)\|\mathbf{H}\|_2((1 + x)^{m_2} - 1)$ whose last subdiagonal entry is at most
$t_L^{1/2}/(1 - \boldsymbol{u})$. -/
theorem decoupleLast_spec {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u < 1) (hL : IsIndexLit M I) (hC : IsCmp id I)
    (hQ : IsToNat id I) {n m₂ : ℕ} (hNat : IsExactNatLit id M (n + 2))
    {H V : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {d : Fin (n + 2) → ℂ} {ζ : ℂ}
    {B C p η₁ β' ω tL : ℝ} (hH : IsUpperHessenberg H) (hH0 : H ≠ 0) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hC0 : 0 ≤ C)
    (hζ : ‖ζ‖ ≤ C * specNorm H) (hη₁ : 0 < η₁) (hdist : ∀ j, η₁ ≤ ‖d j - ζ‖)
    {i : Fin (n + 2)} (hi : ‖ζ - d i‖ ≤ β') (hp : 0 < p) (hpi : p ≤ lastRowWeights V i)
    (hω : 4 * β' ≤ ω) (hm₂ : 1 ≤ m₂) (hm₂B : B ≤ 2 ^ m₂ * √p)
    (hxu : ∀ ℓ ≤ m₂, 300 * ((n : ℝ) + 2) ^ 2 * u ≤
      (16 * B)⁻¹ * (η₁ / ((2 + 2 * C) * specNorm H)) ^ ℓ)
    (hfwd : ∀ ℓ ≤ m₂, (66 + 2 * C) * B * specNorm H * ((2 + 2 * C) * specNorm H / η₁) ^ ℓ *
      √((n : ℝ) + 2) * (300 * ((n : ℝ) + 2) ^ 2 * u) ≤ ω / 2)
    {qs : List ℝ} (hqs : 8 ≤ qs.length) (htL : (1 + u) ^ 2 * ω ^ 2 ≤ qs.getD 7 0)
    {τ : Tape ℝ} {μ : Mem ℝ} {h lam qw f : ℕ × ℕ} (hin : DecoupleInput H ζ qs h lam qw f μ) :
    Writes .total I τ (decoupleLast (O := O) (Q := Q)).body
      (Env.frame [n + 2, m₂] [h, lam, qw, h, f])
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ H' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ,
        IsPerturbedUnitarySimilar H H'
          ((1 + C) * specNorm H * ((1 + 300 * ((n : ℝ) + 2) ^ 2 * u) ^ m₂ - 1)) ∧
        IsUpperHessenberg H' ∧ HoldsMatrix h H' μ'.store ∧
        (1 - u) * ‖H' (Fin.last (n + 1)) (Fin.last n).castSucc‖ ≤ √(qs.getD 7 0)) μ := by
  sorry

/-- `NLAlib.SmallEig.decoupleLast` terminates on every tape: from `NLAlib.SmallEig.DecoupleInput`
with any matrix of order $n + 2$ and at least eight words, on a scalar machine with index
literals, exact natural literals up to $n + 2$, exact comparisons and conversion, it writes only
the matrix and the flag and stores both. -/
theorem decoupleLast_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) (hQ : IsToNat id I) {n m₂ : ℕ}
    (hNat : IsExactNatLit id M (n + 2)) {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {ζ : ℂ}
    {qs : List ℝ} (hqs : 8 ≤ qs.length) {τ : Tape ℝ} {μ : Mem ℝ} {h lam qw f : ℕ × ℕ}
    (hin : DecoupleInput H ζ qs h lam qw f μ) :
    Writes .total I τ (decoupleLast (O := O) (Q := Q)).body
      (Env.frame [n + 2, m₂] [h, lam, qw, h, f])
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ H' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ, HoldsMatrix h H' μ'.store) ∧
        ∃ x, μ'.store.get f.1 f.2 = some x) μ := by
  sorry

end Theorems

end NLAlib.SmallEig
