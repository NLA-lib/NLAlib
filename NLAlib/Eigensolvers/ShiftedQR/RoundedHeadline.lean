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
The worklist in Schur mode with these routines on the good tapes is
`NLAlib.ShiftedQR.solveRoundedWith_pwrites` (`NLAlib.Eigensolvers.ShiftedQR.RoundedSolveSchur`).
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
diagonalizable with condition at most $B$ and eigenvalues separated by $g$, with the log in a
buffer of its own (apart from those of the matrix, the words and the flag), except with
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
        μ.Live [w₀, q, w₀, f, lg] ∧ (∀ b ∈ [w₀, q, f], b.1 ≠ lg.1) ∧
        w₀.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w₀.1 ∧
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


end NLAlib.ShiftedQR
