/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.DecoupleState
public import NLAlib.Eigensolvers.ShiftedQR.DeflationProgram
public import NLAlib.Eigensolvers.ShiftedQR.Step
public import NLAlib.Matrix.FinitePrecision.OpsUnitarySimilarity

/-!
# Backward-error contracts of shifted QR

The exact shifted QR program returns exact unitary similarities: `IterationContract` and
`DecouplingContract` end with $\mathbf{H}' = \mathbf{U}^{\mathsf H}\mathbf{H}\mathbf{U}$. In
floating point each layer returns a **perturbed** unitary similarity
(`NLAlib.IsPerturbedUnitarySimilar`) whose backward error is relative to a norm bound of its
input. This file states the weakened contracts, the bridges from the exact contracts (backward
error $0$, [BanksGarzaVargasSrivastava2022, Definition 3.4] at $\boldsymbol{u} = 0$), the rounded
single shifted QR step of the existing program as a perturbed similarity
([BanksGarzaVargasSrivastava2022, Lemma 3.5], with the error $O(n\boldsymbol{u})$ of a sweep
analysed round by round), and the deflation worklist driven by a backward decoupling
implementation (the backward half of [BanksGarzaVargasSrivastava2022, Theorem 6.3]).

The worklist and its program are the exact development's, unchanged: only the contract of the
decoupling implementation it is given is weaker. The final perturbation is the sum of the
discarded couplings and of the backward errors of the decoupling calls.

## Main definitions

* `NLAlib.ShiftedQR.BackwardIterationContract`, `NLAlib.ShiftedQR.BackwardDecouplingContract`.

## Main results

* `NLAlib.ShiftedQR.IterationContract.backward`, `NLAlib.ShiftedQR.DecouplingContract.backward`:
  exact contracts are backward contracts with error $0$.
* `NLAlib.ShiftedQR.shiftedStep_isPerturbedUnitarySimilar`: the rounded single step.
* `NLAlib.ShiftedQR.solve_backward`: the worklist with a backward decoupling implementation.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type}

/-- The backward contract of one shift-strategy iteration with the relative backward error `ν`:
from a Hessenberg matrix of norm at most `N`, the stored result is upper Hessenberg and a
perturbed unitary similarity of the input with backward error $\nu N$. Optimality of the Ritz
values and the acceptance test are not part of the backward contract (they are the convergence
half). -/
def BackwardIterationContract (ν : ℝ) (Iter : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n m M : ℕ} {τ B θ α γ N : ℝ} {w p c : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    IsUpperHessenberg H → specNorm H ≤ N → 2 ^ m ≤ n → 0 ≤ τ → 0 ≤ B →
    M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊ → 0 < M →
    HoldsMatrix w H μ.store → μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ] →
    μ.store.readBlock c.1 c.2 2 = some [τ ^ 2, (1 - γ) ^ (2 * (2 ^ m))] →
    μ.Live [w, p, c, w] → w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock p.1 p.2 5 ⊔ Store.inBlock c.1 c.2 2) →
    Writes .total I tape Iter.body (Env.frame [n + 1, m, 2 ^ m, M] [w, p, c, w])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsPerturbedUnitarySimilar H H' (ν * N) ∧ IsUpperHessenberg H' ∧
          HoldsMatrix w H' μ'.store) μ

/-- The backward contract of a decoupling implementation with the backward error `ε N` for
inputs of norm at most `N`: as `NLAlib.ShiftedQR.DecouplingContract`, with the exact unitary
similarity replaced by a perturbed one. -/
def BackwardDecouplingContract (θ : ℝ) (ε : ℝ → ℝ) (D : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n m F M : ℕ} {τ B α γ δ N : ℝ} {w p r : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    IsUpperHessenberg H → specNorm H ≤ N → RapidDecouplingHyps H τ B θ α γ δ m F → 2 ^ m ≤ n →
    0 ≤ τ → M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊ → 0 < M →
    HoldsMatrix w H μ.store → μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ] →
    μ.Live [w, p, w, r] → w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 →
    r.2 + 5 ≤ μ.store.len r.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock r.1 r.2 5) →
    Fp.Disj (Store.inBlock p.1 p.2 5)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5) →
    Writes .total I tape D.body (Env.frame [n + 1, m, 2 ^ m, F, M] [w, p, w, r])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5)
      (fun μ' => μ'.pos = μ.pos ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsPerturbedUnitarySimilar H H' (ε N) ∧
          IsUpperHessenberg H' ∧ IsDecoupledAbs τ H' ∧
          HoldsMatrix w H' μ'.store ∧ ScanHolds H' (τ ^ 2) n r μ'.store) μ

/-- An exact iteration contract is a backward iteration contract with backward error $0$
(`NLAlib.ShiftedQR.shqrAcceptStep` is a unitary similarity of its input). -/
theorem IterationContract.backward {θ : ℝ} {Iter : Impl O Q} {I : Interp O Q ℝ}
    (h : IterationContract θ Iter I) : BackwardIterationContract 0 Iter I := by
  sorry

/-- An exact decoupling contract is a backward decoupling contract with backward error $0$. -/
theorem DecouplingContract.backward {θ : ℝ} {D : Impl O Q} {I : Interp O Q ℝ}
    (h : DecouplingContract θ D I) : BackwardDecouplingContract θ (fun _ => 0) D I := by
  sorry

variable [Has ScalarOp O] [Has CmpTst Q]

/-- **The rounded single shifted QR step is backward stable** ([BanksGarzaVargasSrivastava2022,
Lemma 3.5], for the conjugating implementation): the existing scalar program `shiftedStep`, run on
a machine with the standard model at the unit roundoff $\boldsymbol{u}$ with
$(n + 1)\boldsymbol{u} \le 1/2500$, returns a perturbed unitary similarity of its input with
backward error $50(n + 1)\boldsymbol{u}\|\mathbf{H}\|_2$, for every shift. Each round rotates two
rows and two columns with rounded coefficients
(`NLAlib.IsRoundedRowRotation.specNorm_sub_le`, $49\boldsymbol{u}\|\mathbf{Z}\|_2$ per round); the
rounds compose by `NLAlib.Ops.BackwardStep.loop_rel`. The bound is $O(n)$, not the paper's
$32n^{3/2}$; it is relative to $\|\mathbf{H}\|_2$ because this implementation conjugates
$\mathbf{H}$ itself. The output is upper Hessenberg up to the rounding of entries that cancel in
exact arithmetic; the finite-precision program zeroes them (design note). -/
theorem shiftedStep_isPerturbedUnitarySimilar {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s z : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hl : m.Live [a, s, z]) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (haz : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hsz : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I τ shiftedStep.body (Env.frame [n + 1] [a, s, z])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (fun m' => m'.pos = m.pos ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsPerturbedUnitarySimilar H H' (50 * (n + 1) * u * specNorm H) ∧
          HoldsMatrix z H' m'.store) m := by
  sorry

variable [Has IndexOp O] [Has EigenvalueKernelOp O] [Has IdxTst Q]

/-- **Backward error of the deflation worklist with a backward decoupling implementation** (the
backward half of [BanksGarzaVargasSrivastava2022, Theorem 6.3]): the exact development's program
`solve D`, with `D` meeting the backward decoupling contract with a monotone error `ε`, returns
all roots of $\mathbf{H} + \mathbf{E}$ with
$\|\mathbf{E}\|_2 \le n(\delta\|\mathbf{H}\|_{\mathsf F} + \varepsilon(2\|\mathbf{H}\|_2))$,
provided that this total stays within the exact development's perturbation budget (the
conditioning and norm hypotheses of `NLAlib.ShiftedQRHyps`, with the backward errors added). The
scalar arithmetic of the worklist itself (the threshold, the scans) is exact here; its rounding is
the subject of the finite-precision program. -/
theorem solve_backward {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I)
    (hQ : IsToNat id I) (hC : IsCmp id I)
    {θ : ℝ} {K : KernelRoutines θ} (hK : IsEigenvalueKernels K I)
    (D : Impl O Q) {ε : ℝ → ℝ} (hεm : Monotone ε) (hε0 : ∀ N, 0 ≤ ε N)
    (hD : BackwardDecouplingContract θ ε D I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m F M : ℕ} {a raw out : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {B α γ δ g : ℝ}
    (hl : μ.Live [a, raw, out])
    (hr : μ.Room [a, raw, out] [2 * ((n + 1) * (n + 1)), 5, 2 * (n + 1)])
    (ha : Fp.Apart [a, raw, out] [2 * ((n + 1) * (n + 1)), 5, 2 * (n + 1)])
    (hHess : IsUpperHessenberg H) (hA : HoldsMatrix a H μ.store)
    (hGlobal : ShiftedQRHyps H B θ α γ δ g m F)
    (hεg : (n : ℝ) * (δ * frobNorm H + ε (2 * specNorm H)) ≤ g / (8 * (n + 1) * B))
    (hεn : (n : ℝ) * (δ * frobNorm H + ε (2 * specNorm H)) ≤ specNorm H)
    (hM : M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hRaw : μ.store.readBlock raw.1 raw.2 5 = some [B, θ, α, γ, δ]) :
    Writes .total I tape (solve D).body
      (Env.frame [n + 1, m, 2 ^ m, F, M] [a, raw, out])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)))
      (fun μ' => μ'.pos = μ.pos ∧
        ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
          HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
          specNorm E ≤ (n : ℝ) * (δ * frobNorm H + ε (2 * specNorm H)) ∧
          (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)) μ := by
  sorry

end NLAlib.ShiftedQR
