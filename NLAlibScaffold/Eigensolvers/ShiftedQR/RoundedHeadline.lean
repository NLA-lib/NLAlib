/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedSolve
public import NLAlibScaffold.Ops.Logic.Probabilistic

/-!
# The rounded deflation worklist with randomized routines

[BanksGarzaVargasSrivastava2022, Theorem 6.3] in floating point, at the level of the worklist:
the decoupler and the small-eigenvalue routine are randomized, each meeting its guarantee on a
good set of tapes (`NLAlib.Ops.PWrites`). The decoupler is guaranteed only on well-conditioned
blocks: upper Hessenberg, norm at most $N$, diagonalizable with condition at most $B$ and
eigenvalues separated by $g$. The worklist keeps every block it hands to the decoupler in that
class (norm at most $N_0$, condition at most $2B$, separation $g/2$) as long as the accumulated
backward error stays below $g/(16(n + 1)B)$, and the failure probabilities of the at most
$2(n + 1)$ rounds add (`NLAlib.Ops.PWrites.whileFuel`).

The deterministic backward error of the same program on every tape is
`NLAlib.ShiftedQR.solveRounded_backward`; this file adds the probability of success. The
decoupler that meets `NLAlib.ShiftedQR.RandomDecouplingContract` (Lemma 6.4's loop of
`Regularize` and $\mathrm{Sh}_{k,B}$) and the leaf that meets
`NLAlib.ShiftedQR.RandomLeafContract` (`SmallEig`, Definition 1.2) are separate.

## Main definitions

* `NLAlib.ShiftedQR.RandomDecouplingContract`, `NLAlib.ShiftedQR.RandomLeafContract`.

## Main results

* `NLAlib.ShiftedQR.solveRounded_pwrites`: the worklist as a probabilistic block specification.
* `NLAlib.ShiftedQR.solveRounded_measureReal_not_spectrum_le`: the probability that the run does
  not return the spectrum of a nearby matrix.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops MeasureTheory
open scoped Matrix

variable {O Q : Type}

/-- **The contract of a randomized decoupling implementation** with the stream laws `law`, the
class bounds `B` (condition) and `g` (separation), the failure probability `φ`, the bottom width
`k`, the parameter words `ps`, the coupling threshold `ω` and the backward error `ε N` for inputs
of norm at most `N`. From an upper Hessenberg matrix of order $n + 1 \ge k + 1$ stored in place,
of norm at most $N$, diagonalizable with condition at most $B$ and eigenvalues separated by $g$,
the run, except with probability at most $\varphi$, writes only the matrix and the one-word flag,
sets the flag to $0$ and stores an upper Hessenberg perturbed unitary similarity with backward
error $\varepsilon(N)$ having one of its bottom $k$ subdiagonal entries of modulus at most
$\omega$ (the success branch of `NLAlib.ShiftedQR.RoundedDecouplingContract`). The interface is
`[n, k, np] (W, P) → (W, Fl)`. -/
def RandomDecouplingContract (law : ℕ → Measure ℝ) (B g φ : ℝ) (k : ℕ) (ps : List ℝ) (ω : ℝ)
    (ε : ℝ → ℝ) (D : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {N : ℝ} {w q f : ℕ × ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
    k ≤ n → IsUpperHessenberg H → specNorm H ≤ N → IsUnit V → H * V = V * Matrix.diagonal d →
    pseudoConditionNumber V ≤ B → (∀ i j, i ≠ j → g ≤ ‖d i - d j‖) →
    PWrites law I D.body (Env.frame [n + 1, k, ps.length] [w, q, w, f])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ => HoldsMatrix w H μ.store ∧ μ.store.readBlock q.1 q.2 ps.length = some ps ∧
        μ.Live [w, q, w, f] ∧ w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 ∧
        f.2 + 1 ≤ μ.store.len f.1 ∧
        Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1) ∧
        Fp.Disj (Store.inBlock q.1 q.2 ps.length)
          (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1))
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsPerturbedUnitarySimilar H H' (ε N) ∧
          IsUpperHessenberg H' ∧ (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω) ∧
          HoldsMatrix w H' μ'.store) φ

/-- **The contract of a randomized leaf routine** with backward error `β` and failure
probability `φ`: from an upper Hessenberg matrix $\mathbf{B}$ of order $d$, except with
probability at most $\varphi$, the run writes only its $2d$ output words and stores a listing of
the eigenvalues, with multiplicity, of $\mathbf{B} + \mathbf{F}$ for some
$\|\mathbf{F}\|_2 \le \beta$ (the probabilistic form of `NLAlib.ShiftedQR.BackwardLeafContract`;
a forward-accurate `SmallEig` meets it through `NLAlib.IsEigenvalueListing.exists_specNorm_sub_le`).
The interface is `[d] (B) → (Ev)`. -/
def RandomLeafContract (law : ℕ → Measure ℝ) (β φ : ℝ) (L : Impl O Q) (I : Interp O Q ℝ) :
    Prop :=
  ∀ {d : ℕ} {w o : ℕ × ℕ} (B : Matrix (Fin d) (Fin d) ℂ), IsUpperHessenberg B →
    PWrites law I L.body (Env.frame [d] [w, o]) (Store.inBlock o.1 o.2 (2 * d))
      (fun μ => HoldsMatrix w B μ.store ∧ μ.Live [w, o] ∧ o.2 + 2 * d ≤ μ.store.len o.1 ∧
        Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)))
      (fun μ' => ∃ (roots : Fin d → ℂ) (F : Matrix (Fin d) (Fin d) ℂ), specNorm F ≤ β ∧
        IsEigenvalueListing (B + F) roots ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) φ

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The rounded worklist with randomized routines** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3], the worklist with the probability of success): on a machine with the standard model
at $0 \le \boldsymbol{u} < 1$ whose natural literals up to $n + 1$ are exact, with a measurable
interpretation that reads the tape only in its windows, let the decoupler `D` meet
`NLAlib.ShiftedQR.RandomDecouplingContract` on the class (condition $2B$, separation $g/2$) with
failure probability $\varphi_D$, and the leaf `L` meet `NLAlib.ShiftedQR.RandomLeafContract` with
error $\beta \ge 0$ and failure probability $\varphi_L$. Let $\mathbf{H}$ be upper Hessenberg of
order $n + 1$ with $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$,
$\kappa(\mathbf{V}) \le B$ and eigenvalues separated by $g > 0$; let the threshold word $t$
satisfy $(1 + \boldsymbol{u})^2\omega^2 \le t \le (1 - \boldsymbol{u})^2c^2$, $c \ge 0$, let
$\varepsilon(N_0) \ge 0$, $e = c + \varepsilon(N_0) + \beta$,
$\|\mathbf{H}\|_2 + 2(n+1)e \le N_0$ and $2(n + 1)e \le g/(16(n+1)B)$. Then from every memory
holding the input, except with probability at most $2(n + 1)(\varphi_D + \varphi_L)$, the run
writes only the matrix, the output and the failure word, sets the failure word to $0$ and stores
all eigenvalues, with multiplicity, of $\mathbf{H} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le 2(n + 1)e$. -/
theorem solveRounded_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD β φL : ℝ} {k : ℕ}
    {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    (hD : RandomDecouplingContract law (2 * B) (g / 2) φD k ps ω ε D I)
    (L : Impl O Q) (hLeaf : RandomLeafContract law β φL L I) {a t p out f : ℕ × ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {thr c N₀ : ℝ}
    (hHess : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀)
    (hN₀ : specNorm H + 2 * (n + 1) * (c + ε N₀ + β) ≤ N₀)
    (hsmall : 2 * (n + 1) * (c + ε N₀ + β) ≤ g / (16 * (n + 1) * B)) :
    PWrites law I (solveRounded D L).body (Env.frame [n + 1, k, ps.length] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ => μ.Live [a, t, p, out, f] ∧
        μ.Room [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * (n + 1), 1] ∧
        Fp.Apart [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * (n + 1), 1] ∧
        HoldsMatrix a H μ.store ∧ μ.store.get t.1 t.2 = some thr ∧
        μ.store.readBlock p.1 p.2 ps.length = some ps)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
          HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
          specNorm E ≤ 2 * (n + 1) * (c + ε N₀ + β) ∧
          (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ))
      (2 * (n + 1) * (φD + φL)) := by
  sorry

/-- **The probability of success of the rounded worklist** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3], at the level of the worklist): under the hypotheses of
`NLAlib.ShiftedQR.solveRounded_pwrites` and for a random tape `ξ` with the stream laws `law`, the
run from a memory holding the input fails to store the spectrum of some $\mathbf{H} + \mathbf{E}$
with $\|\mathbf{E}\|_2 \le 2(n + 1)(c + \varepsilon(N_0) + \beta)$ and the failure word $0$ with
probability at most $2(n + 1)(\varphi_D + \varphi_L)$. -/
theorem solveRounded_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD β φL : ℝ} {k : ℕ}
    {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    (hD : RandomDecouplingContract law (2 * B) (g / 2) φD k ps ω ε D I)
    (L : Impl O Q) (hLeaf : RandomLeafContract law β φL L I) {a t p out f : ℕ × ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {thr c N₀ : ℝ}
    (hHess : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀)
    (hN₀ : specNorm H + 2 * (n + 1) * (c + ε N₀ + β) ≤ N₀)
    (hsmall : 2 * (n + 1) * (c + ε N₀ + β) ≤ g / (16 * (n + 1) * B)) {μ : Mem ℝ}
    (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * (n + 1), 1])
    (ha : Fp.Apart [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * (n + 1), 1])
    (hA : HoldsMatrix a H μ.store) (ht : μ.store.get t.1 t.2 = some thr)
    (hp : μ.store.readBlock p.1 p.2 ps.length = some ps) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (solveRounded D L).body
      (Env.frame [n + 1, k, ps.length] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
          HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
          specNorm E ≤ 2 * (n + 1) * (c + ε N₀ + β) ∧
          (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)) μ} ≤
      2 * (n + 1) * (φD + φL) :=
  (solveRounded_pwrites hS hM hu hu1 hL hNat hQ hC hI hloc D hD L hLeaf hHess hV hHV hκ hg hgap
    hfind hcut hc hβ hε0 hN₀ hsmall).measureReal_not_writes_le ⟨hl, hr, ha, hA, ht, hp⟩ hξ

end Theorems

end NLAlib.ShiftedQR
