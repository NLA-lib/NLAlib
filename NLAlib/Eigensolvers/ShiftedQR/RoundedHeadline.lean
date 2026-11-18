/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import NLAlib.ForMathlib.MeasureTheory.Matrix
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolve
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveBackward
public import NLAlib.Matrix.Perturbation.BackwardClosed
public import NLAlib.Ops.Logic.ProbabilisticFamily
public import NLAlib.Eigensolvers.Schur.Contracts

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
* `NLAlib.ShiftedQR.measurable_storedMatrix`: the matrix read from a block
  (`NLAlib.storedMatrix`) is a measurable function of the memory.
* `NLAlib.ShiftedQR.RoundedReached`, `NLAlib.ShiftedQR.RoundedCopied`: the states of a round on
  the good tapes.

## Main results

* `NLAlib.ShiftedQR.measurableSet_decoupleOutcome`, `NLAlib.ShiftedQR.measurableSet_leafOutcome`:
  the outcomes of the randomized calls that the worklist uses are measurable, so each call's
  family of good sets becomes one (`NLAlib.Ops.PWrites.pstep_of_forall`).
* `NLAlib.ShiftedQR.roundedLeaf_pwrites`, `NLAlib.ShiftedQR.roundedDecouple_pwrites`,
  `NLAlib.ShiftedQR.roundedLarge_pwrites`, `NLAlib.ShiftedQR.roundedRange_pwrites`,
  `NLAlib.ShiftedQR.roundedWorklistRound_pwrites`, `NLAlib.ShiftedQR.roundedWorklist_pwrites`:
  the round of `NLAlib.ShiftedQR.roundedWorklistRound_backwardStep` and its loop on the good
  tapes.
* `NLAlib.ShiftedQR.solveRounded_pwrites`: the worklist as a probabilistic block specification.
* `NLAlib.ShiftedQR.solveRounded_measureReal_not_spectrum_le`: the probability that the run does
  not return the spectrum of a nearby matrix.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops MeasureTheory
open scoped Matrix

variable {O Q : Type}

/-! ### Measurable outcomes of the randomized calls -/

/-- The matrix read from a block is a measurable function of the memory. -/
theorem measurable_storedMatrix (b : ℕ × ℕ) (rows cols : ℕ) :
    Measurable fun m : Mem ℝ => storedMatrix b rows cols m.store := by
  have hw : ∀ z : ℕ × ℕ, Measurable fun m : Mem ℝ => (m.store.get z.1 z.2).getD 0 :=
    fun z => measurable_snd.comp (Mem.measurable_cell z)
  refine Matrix.measurable_iff.mpr fun i j => ?_
  have := (Complex.equivRealProdCLM.symm.continuous.measurable).comp
    ((hw (b.1, b.2 + 2 * (j * rows + i))).prodMk (hw (b.1, b.2 + 2 * (j * rows + i) + 1)))
  convert this using 1
  funext m
  apply Complex.ext <;> simp [storedMatrix]

/-- The memories whose first `N` words of the block at `b` are initialised. -/
theorem measurableSet_forall_isSome (b : ℕ × ℕ) (N : ℕ) :
    MeasurableSet {m : Mem ℝ | ∀ j < N, (m.store.get b.1 (b.2 + j)).isSome} := by
  have e : {m : Mem ℝ | ∀ j < N, (m.store.get b.1 (b.2 + j)).isSome} =
      ⋂ j : Fin N, {m | (m.store.get b.1 (b.2 + j)).isSome} := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h j => h j j.isLt, fun h j hj => h ⟨j, hj⟩⟩
  rw [e]
  exact .iInter fun j =>
    (measurable_fst.comp (Mem.measurable_cell (b.1, b.2 + j))) (measurableSet_singleton true)

/-- The outcomes of a decoupling call that the worklist uses, as pairs of a memory before and
after: the frame `F`, the flag $0$, an initialised work matrix, and the matrix read after is an
upper Hessenberg perturbed unitary similarity with error $\varepsilon$ of the matrix read before,
with a bottom-$k$ subdiagonal entry of modulus at most $\omega$. They form a measurable set. -/
theorem measurableSet_decoupleOutcome (d k : ℕ) (ε ω : ℝ) (w f : ℕ × ℕ) (F : Fp) :
    MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧
      x.2.store.get f.1 f.2 = some 0 ∧
      (∀ j < 2 * ((d + 1) * (d + 1)), (x.2.store.get w.1 (w.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilar (storedMatrix w (d + 1) (d + 1) x.1.store)
        (storedMatrix w (d + 1) (d + 1) x.2.store) ε ∧
      IsUpperHessenberg (storedMatrix w (d + 1) (d + 1) x.2.store) ∧
      ∃ i : Fin d, d ≤ (i : ℕ) + k ∧
        ‖storedMatrix w (d + 1) (d + 1) x.2.store i.succ i.castSucc‖ ≤ ω} := by
  have hm := measurable_storedMatrix w (d + 1) (d + 1)
  have hpair : Measurable fun x : Mem ℝ × Mem ℝ =>
      (storedMatrix w (d + 1) (d + 1) x.1.store, storedMatrix w (d + 1) (d + 1) x.2.store) :=
    (hm.comp measurable_fst).prodMk (hm.comp measurable_snd)
  have hent (i j : Fin (d + 1)) : Measurable fun x : Mem ℝ × Mem ℝ =>
      storedMatrix w (d + 1) (d + 1) x.2.store i j :=
    (Matrix.measurable_apply i j).comp (hm.comp measurable_snd)
  simp only [Set.ofPred_and]
  refine (Mem.measurableSet_eqOff F).inter ((measurable_snd (Mem.measurableSet_get_eq f 0)).inter
    ((measurable_snd (measurableSet_forall_isSome w _)).inter
      (((isClosed_setOf_isPerturbedUnitarySimilar ε).measurableSet.preimage hpair).inter
        ((?_ : MeasurableSet _).inter ?_))))
  · simp only [IsUpperHessenberg, Set.ofPred_forall]
    refine .iInter fun i => .iInter fun j => ?_
    by_cases hij : (j : ℕ) + 1 < i
    · simpa [hij] using measurableSet_eq_fun (hent i j) measurable_const
    · simp [hij]
  · simp only [Set.ofPred_exists, Set.ofPred_and]
    exact .iUnion fun i => (MeasurableSet.const _).inter
      (measurableSet_le (hent _ _).norm measurable_const)

/-- The outcomes of a leaf call that the worklist uses, as pairs of a memory before and after:
the frame `F`, an initialised output column of $d$ complex words at `o`, and the column read after
lists the eigenvalues of the matrix read at `w` before plus some $\|\mathbf{F}\|_2 \le \beta$.
They form a measurable set. -/
theorem measurableSet_leafOutcome (d : ℕ) (β : ℝ) (w o : ℕ × ℕ) (F : Fp) :
    MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧
      (∀ j < 2 * (1 * d), (x.2.store.get o.1 (o.2 + j)).isSome) ∧
      ∃ G : Matrix (Fin d) (Fin d) ℂ, specNorm G ≤ β ∧
        IsEigenvalueListing (storedMatrix w d d x.1.store + G)
          (fun i => storedMatrix o d 1 x.2.store i 0)} := by
  have hcol : Measurable fun x : Mem ℝ × Mem ℝ => fun i => storedMatrix o d 1 x.2.store i 0 :=
    measurable_pi_lambda _ fun i =>
      (Matrix.measurable_apply i (0 : Fin 1)).comp ((measurable_storedMatrix o d 1).comp
        measurable_snd)
  have hpair : Measurable fun x : Mem ℝ × Mem ℝ =>
      (storedMatrix w d d x.1.store, fun i => storedMatrix o d 1 x.2.store i 0) :=
    ((measurable_storedMatrix w d d).comp measurable_fst).prodMk hcol
  have hC : MeasurableSet {p : Matrix (Fin d) (Fin d) ℂ × (Fin d → ℂ) |
      ∃ G : Matrix (Fin d) (Fin d) ℂ, specNorm G ≤ β ∧ IsEigenvalueListing (p.1 + G) p.2} :=
    (isClosed_setOf_exists_specNorm_le_isEigenvalueListing β).measurableSet
  exact (Mem.measurableSet_eqOff F).inter ((measurable_snd (measurableSet_forall_isSome o _)).inter
    (hpair hC))

/-! ### Randomized routines with parameter words and a cap dimension -/

/-- **The contract of a randomized decoupling routine with a cap dimension and a log**, with the
class bounds `B`, `g`, the failure probability `φ`, the bottom width `k`, the iteration cap `F`, the
routine cap `T`, the outer bounds `nmax`, `Nmax`, the words `ps`, the log shape (`ns` slots of `w`
entries), the threshold `ω` and the error `ε`. For a decoupler with the interface
`[n, k, np, F, T, ns, w] (W, P) → (W, Fl, Lg)`: from an upper Hessenberg $\mathbf{H}$ of order
$n + 1$, $k \le n \le n_{\max}$, stored in place, of norm at most $N \le N_{\max}$,
diagonalizable with condition at most $B$ and eigenvalues separated by $g$, except with
probability at most $\varphi$ the run writes only the matrix, the flag and the log, sets the flag
to $0$, closes the `ns` slots of the log (planes below $n$) and stores an upper Hessenberg
perturbed similarity of $\mathbf{H}$ **by the exact unitary of the log's valid entries**, with
backward error $\varepsilon(N)$ and one of its bottom $k$ subdiagonal entries of modulus at most
$\omega$. -/
def RandomDecouplingRoutineContract (law : ℕ → Measure ℝ) (B g φ : ℝ) (k F T nmax : ℕ)
    (Nmax : ℝ) (ps : List ℝ) (ns w : ℕ) (ω : ℝ) (ε : ℝ → ℝ) (D : Impl O Q)
    (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {N : ℝ} {w₀ q f lg : ℕ × ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
    k ≤ n → n ≤ nmax → N ≤ Nmax → IsUpperHessenberg H → specNorm H ≤ N → IsUnit V →
    H * V = V * Matrix.diagonal d → pseudoConditionNumber V ≤ B → (∀ i j, i ≠ j → g ≤ ‖d i - d j‖) →
    PWrites law I D.body (Env.frame [n + 1, k, ps.length, F, T, ns, w] [w₀, q, w₀, f, lg])
      (Store.inBlock w₀.1 w₀.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ => HoldsMatrix w₀ H μ.store ∧ μ.store.readBlock q.1 q.2 ps.length = some ps ∧
        μ.Live [w₀, q, w₀, f, lg] ∧ w₀.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w₀.1 ∧
        f.2 + 1 ≤ μ.store.len f.1 ∧ lg.2 + ns * (1 + 5 * w) ≤ μ.store.len lg.1 ∧
        Fp.Apart [w₀, f, lg] [2 * ((n + 1) * (n + 1)), 1, ns * (1 + 5 * w)] ∧
        Fp.Disj (Store.inBlock q.1 q.2 ps.length)
          (Store.inBlock w₀.1 w₀.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
            Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))))
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (L : List (Option (List GivensEntry))),
          L.length = ns ∧ (∀ e ∈ slotEntries w L, e.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w L [] μ'.store ∧
          IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries w L)) H H' (ε N) ∧
          IsUpperHessenberg H' ∧ (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω) ∧
          HoldsMatrix w₀ H' μ'.store) φ

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The rounded worklist in Schur mode as a probabilistic block** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3] with the Schur form): on a scalar machine with the standard model, exact natural
literals up to $n + 1$, exact `toNat` and comparisons, and a measurable tape-local interpretation,
let the decoupler meet `NLAlib.ShiftedQR.RandomDecouplingRoutineContract` on the class
$(2B, g/2)$ with error $\varepsilon(N_0)$, and the leaf meet the Schur leaf contract
(`NLAlib.Schur.RandomSchurLeafContract`) with errors $(\varepsilon_L, \beta)$ on orders at most
$\min(k, n + 1)$. From an upper Hessenberg $\mathbf{H}$, diagonalizable with condition at most $B$
and eigenvalues separated by $g > 0$, and an accumulator $\mathbf{U}$, under the merged threshold
and precision conditions with the replay and product errors $\rho = 78\boldsymbol{u}\,n_s w N_0$
and $\rho_L = 8(n + 1)(k + 2)\boldsymbol{u}N_0$ in the budget, except with probability at most
$2(n + 1)(\varphi_D + \varphi_L)$ the flag is $0$, the stored matrix $\widehat{\mathbf{T}}$ is
upper triangular and $(\widehat{\mathbf{U}}, \widehat{\mathbf{T}})$ is tracked from
$(\mathbf{U}, \mathbf{H})$ (`NLAlib.IsTrackedUnitarySimilar`) with the backward error
$2(n + 1)(c + \varepsilon(N_0) + \beta + \rho + \rho_L)$ and the relative accumulator error
$(1 + 24\boldsymbol{u})^{2(n+1)(n_s w + 2k(k+2))}(1 + \varepsilon_L)^{n+1} - 1$. The constants of
$\rho$, $\rho_L$ and the accumulator error are design values (fixed when proved). -/
theorem solveRoundedWith_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD εL β φL : ℝ}
    {k F T ns w : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q) {N₀ : ℝ}
    (hD : RandomDecouplingRoutineContract law (2 * B) (g / 2) φD k F T n N₀ ps ns w ω ε D I)
    (L : Impl O Q)
    (hLeaf : Schur.RandomSchurLeafContract law εL β φL (min k (n + 1)) N₀ ps T L I)
    (hφD : 0 ≤ φD) (hφL : 0 ≤ φL) (hεL : 0 ≤ εL) {a t p uo f : ℕ × ℕ}
    {H U V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {thr c : ℝ}
    (hHess : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀)
    (hN₀ : specNorm H + 2 * (n + 1) * (c + ε N₀ + β + 78 * u * (ns * w) * N₀ +
      8 * (n + 1) * (k + 2) * u * N₀) ≤ N₀)
    (hsmall : 2 * (n + 1) * (c + ε N₀ + β + 78 * u * (ns * w) * N₀ +
      8 * (n + 1) * (k + 2) * u * N₀) ≤ g / (16 * (n + 1) * B)) :
    PWrites law I (solveRoundedWith D L).body
      (Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ => μ.Live [a, t, p, uo, f] ∧
        μ.Room [a, t, p, uo, f]
          [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * ((n + 1) * (n + 1)), 1] ∧
        Fp.Apart [a, t, p, uo, f]
          [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * ((n + 1) * (n + 1)), 1] ∧
        HoldsMatrix a H μ.store ∧ HoldsMatrix uo U μ.store ∧ μ.store.get t.1 t.2 = some thr ∧
        μ.store.readBlock p.1 p.2 ps.length = some ps)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ U' Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          HoldsMatrix a Tm μ'.store ∧ HoldsMatrix uo U' μ'.store ∧ Tm.IsUpperTriangular ∧
          IsTrackedUnitarySimilar
            ((1 + 24 * u) ^ (2 * (n + 1) * (ns * w + 2 * k * (k + 2))) * (1 + εL) ^ (n + 1) - 1)
            (2 * (n + 1) * (c + ε N₀ + β + 78 * u * (ns * w) * N₀ +
              8 * (n + 1) * (k + 2) * u * N₀)) U H U' Tm)
      (2 * (n + 1) * (φD + φL)) :=
  sorry

end Theorems

end NLAlib.ShiftedQR
