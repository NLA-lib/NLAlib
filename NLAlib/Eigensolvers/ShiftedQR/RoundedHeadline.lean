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
* `NLAlib.ShiftedQR.storedMatrix`: the matrix read from a block, a measurable function of the
  memory.
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

/-- **The contract of a randomized decoupling implementation** with the stream laws `law`, the
class bounds `B` (condition) and `g` (separation), the failure probability `φ`, the bottom width
`k`, the iteration cap `F` (fixed outside the quantifiers, so that `φ` may depend on it), the
outer bounds `nmax` on the order and `Nmax` on the norm (fixed outside the quantifiers, so that a
precision and a cap chosen for them serve every block within them), the parameter words `ps`,
the coupling threshold `ω` and the backward error `ε N` for inputs of norm at most `N`. From an
upper Hessenberg matrix of order $n + 1$, $k \le n \le n_{\max}$, stored in place, of norm at most
$N \le N_{\max}$, diagonalizable with condition at most $B$ and eigenvalues separated by $g$,
the run, except with probability at most $\varphi$, writes only the matrix and the one-word flag,
sets the flag to $0$ and stores an upper Hessenberg perturbed unitary similarity with backward
error $\varepsilon(N)$ having one of its bottom $k$ subdiagonal entries of modulus at most
$\omega$ (the success branch of `NLAlib.ShiftedQR.RoundedDecouplingContract`). The interface is
`[n, k, np, F] (W, P) → (W, Fl)`. -/
def RandomDecouplingContract (law : ℕ → Measure ℝ) (B g φ : ℝ) (k F nmax : ℕ) (Nmax : ℝ)
    (ps : List ℝ) (ω : ℝ) (ε : ℝ → ℝ) (D : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {N : ℝ} {w q f : ℕ × ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
    k ≤ n → n ≤ nmax → N ≤ Nmax → IsUpperHessenberg H → specNorm H ≤ N → IsUnit V →
    H * V = V * Matrix.diagonal d → pseudoConditionNumber V ≤ B → (∀ i j, i ≠ j → g ≤ ‖d i - d j‖) →
    PWrites law I D.body (Env.frame [n + 1, k, ps.length, F] [w, q, w, f])
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

/-! ### Measurable outcomes of the randomized calls -/

/-- The complex matrix read entrywise from the pair-codec block at `b` (column-major, real and
imaginary parts in adjacent words), with an uninitialised word read as $0$. -/
def storedMatrix (b : ℕ × ℕ) (rows cols : ℕ) (s : Store ℝ) : Matrix (Fin rows) (Fin cols) ℂ :=
  Matrix.of fun i j => ⟨(s.get b.1 (b.2 + 2 * (j * rows + i))).getD 0,
    (s.get b.1 (b.2 + 2 * (j * rows + i) + 1)).getD 0⟩

/-- A stored matrix is the matrix read from its block. -/
theorem HoldsMatrix.eq_storedMatrix {rows cols : ℕ} {b : ℕ × ℕ}
    {A : Matrix (Fin rows) (Fin cols) ℂ} {s : Store ℝ} (h : HoldsMatrix b A s) :
    A = storedMatrix b rows cols s := by
  ext i j
  apply Complex.ext <;> simp [storedMatrix, h.get_re i j, h.get_im i j]

/-- A block whose words are all initialised holds the matrix read from it. -/
theorem holdsMatrix_storedMatrix {rows cols : ℕ} {b : ℕ × ℕ} {s : Store ℝ}
    (h : ∀ j < 2 * (cols * rows), (s.get b.1 (b.2 + j)).isSome) :
    HoldsMatrix b (storedMatrix b rows cols s) s := by
  let xs := List.ofFn fun j : Fin (2 * (cols * rows)) => (s.get b.1 (b.2 + j)).getD 0
  have hr : s.readBlock b.1 b.2 (2 * (cols * rows)) = some xs := by
    refine Store.readBlock_eq_some_iff.mpr ⟨by simp [xs], fun j hj => ?_⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h j hj)
    simp [xs, hv, hj]
  let A₀ : Matrix (Fin rows) (Fin cols) ℂ :=
    decodeMatrix id ((EntryCodec.pair ℝ).matrix rows cols xs)
  have hw : matrixWords A₀ = xs := by
    have hcomponents : (A₀.map fun z => (z.re, z.im)) = (EntryCodec.pair ℝ).matrix rows cols xs :=
      by ext i j <;> rfl
    unfold matrixWords
    rw [hcomponents]
    exact (EntryCodec.pair ℝ).packFinMatrix_matrix rows cols xs (by
      simp only [xs, List.length_ofFn]
      ring)
  have hA₀ : HoldsMatrix b A₀ s := by
    rw [HoldsMatrix, hw]
    exact hr
  rwa [← hA₀.eq_storedMatrix]

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

/-- The state of the rounded worklist before round `j` on the good tapes: a state of
`NLAlib.ShiftedQR.RoundedWorklistState` that has not failed, at a matrix reached from
$\mathbf{H}_0$ by a perturbed unitary similarity with error $j e$. -/
def RoundedReached {n : ℕ} (H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (e thr : ℝ) (ps : List ℝ)
    (a t p st out w r f : ℕ × ℕ) (j : ℕ) (μ : Mem ℝ) : Prop :=
  ∃ M, IsPerturbedUnitarySimilar H₀ M (j * e) ∧
    RoundedWorklistState False H₀ e thr ps a t p st out w r f j M μ

/-- The state of round `j` on the good tapes after the pop of the range $(lo, d)$ and the copy
of its block to the work matrix, at a matrix reached from $\mathbf{H}_0$ with error $j e$. -/
def RoundedCopied {n : ℕ} (H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (e thr : ℝ) (ps : List ℝ)
    (a t p st out w r f : ℕ × ℕ) (j lo d : ℕ) (μ : Mem ℝ) : Prop :=
  ∃ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (rest done : List (ℕ × ℕ))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (roots : Fin (n + 1) → ℂ),
    IsPerturbedUnitarySimilar H₀ M (j * e) ∧
      RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ ∧
      HoldsMatrix w (subBlock A (lo, d)) μ.store

/-! ### Randomized routines with parameter words and a cap dimension -/

/-- **The contract of a randomized leaf routine with parameter words and a cap**
([BanksGarzaVargasSrivastava2025, Theorem 1.1], as the worklist calls it), with the backward
error `β`, the failure probability `φ`, the order bound `kmax`, the norm bound `Nmax`, the
parameter words `ps` and the cap `T`, all fixed outside the quantifiers: from an upper Hessenberg
matrix $\mathbf{B}$ of order $d \le k_{\max}$ with $\|\mathbf{B}\|_2 \le N_{\max}$ and the words
stored, except with probability at most $\varphi$, the run writes only its $2d$ output words and
stores a listing of the eigenvalues, with multiplicity, of $\mathbf{B} + \mathbf{F}$ for some
$\|\mathbf{F}\|_2 \le \beta$. The interface is `[d, np, T] (B, P) → (Ev)`. The bounds are what a
routine that is not an oracle can meet; `NLAlib.ShiftedQR.RandomLeafContract` quantifies every
order. -/
def RandomLeafRoutineContract (law : ℕ → Measure ℝ) (β φ : ℝ) (kmax : ℕ) (Nmax : ℝ)
    (ps : List ℝ) (T : ℕ) (L : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w p o : ℕ × ℕ} (B : Matrix (Fin d) (Fin d) ℂ), d ≤ kmax → IsUpperHessenberg B →
    specNorm B ≤ Nmax →
    PWrites law I L.body (Env.frame [d, ps.length, T] [w, p, o]) (Store.inBlock o.1 o.2 (2 * d))
      (fun μ => HoldsMatrix w B μ.store ∧ μ.store.readBlock p.1 p.2 ps.length = some ps ∧
        μ.Live [w, p, o] ∧ o.2 + 2 * d ≤ μ.store.len o.1 ∧
        Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)) ∧
        Fp.Disj (Store.inBlock p.1 p.2 ps.length) (Store.inBlock o.1 o.2 (2 * d)))
      (fun μ' => ∃ (roots : Fin d → ℂ) (F : Matrix (Fin d) (Fin d) ℂ), specNorm F ≤ β ∧
        IsEigenvalueListing (B + F) roots ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) φ

/-- **The contract of a randomized decoupling routine with a cap dimension**:
`NLAlib.ShiftedQR.RandomDecouplingContract` for a decoupler with the interface
`[n, k, np, F, T] (W, P) → (W, Fl)`, with the class bounds `B`, `g`, the failure probability `φ`,
the bottom width `k`, the iteration cap `F`, the routine cap `T`, the outer bounds `nmax`,
`Nmax`, the words `ps`, the threshold `ω` and the error `ε`. From an upper Hessenberg
$\mathbf{H}$ of order $n + 1$, $k \le n \le n_{\max}$, stored in place, of norm at most
$N \le N_{\max}$, diagonalizable with condition at most $B$ and eigenvalues separated by $g$,
except with probability at most $\varphi$ the run writes only the matrix and the flag, sets the
flag to $0$ and stores an upper Hessenberg perturbed unitary similarity with backward error
$\varepsilon(N)$ having one of its bottom $k$ subdiagonal entries of modulus at most $\omega$. -/
def RandomDecouplingRoutineContract (law : ℕ → Measure ℝ) (B g φ : ℝ) (k F T nmax : ℕ)
    (Nmax : ℝ) (ps : List ℝ) (ω : ℝ) (ε : ℝ → ℝ) (D : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {N : ℝ} {w q f : ℕ × ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
    k ≤ n → n ≤ nmax → N ≤ Nmax → IsUpperHessenberg H → specNorm H ≤ N → IsUnit V →
    H * V = V * Matrix.diagonal d → pseudoConditionNumber V ≤ B → (∀ i j, i ≠ j → g ≤ ‖d i - d j‖) →
    PWrites law I D.body (Env.frame [n + 1, k, ps.length, F, T] [w, q, w, f])
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

/-- A randomized leaf routine (`NLAlib.ShiftedQR.RandomLeafContract`), lifted by
`NLAlib.ShiftedQR.liftLeaf`, meets the routine contract for every order bound, norm bound,
parameter words and cap. -/
theorem RandomLeafContract.randomLeafRoutineContract {law : ℕ → Measure ℝ} {β φ : ℝ}
    {L : Impl O Q} {I : Interp O Q ℝ} (h : RandomLeafContract law β φ L I) (kmax : ℕ) (Nmax : ℝ)
    (ps : List ℝ) (T : ℕ) : RandomLeafRoutineContract law β φ kmax Nmax ps T (liftLeaf L) I := by
  sorry

/-- A randomized decoupler (`NLAlib.ShiftedQR.RandomDecouplingContract`), lifted by
`NLAlib.ShiftedQR.liftDecoupler`, meets the routine contract for every cap. -/
theorem RandomDecouplingContract.randomDecouplingRoutineContract {law : ℕ → Measure ℝ}
    {B g φ : ℝ} {k F nmax : ℕ} {Nmax : ℝ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} {D : Impl O Q}
    {I : Interp O Q ℝ} (h : RandomDecouplingContract law B g φ k F nmax Nmax ps ω ε D I) (T : ℕ) :
    RandomDecouplingRoutineContract law B g φ k F T nmax Nmax ps ω ε (liftDecoupler D) I := by
  sorry

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The leaf call of a round on the good tapes: from a copied state of round $j$, a leaf
routine meeting `NLAlib.ShiftedQR.RandomLeafContract` with error $\beta \le e$ reaches the state
before round $j + 1$, except with probability at most $\varphi_L$. -/
theorem roundedLeaf_pwrites {I : Interp O Q ℝ} (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {β φL : ℝ} (L : Impl O Q)
    (hLeaf : RandomLeafContract law β φL L I) {n j lo d : ℕ} {a t p st out w r f : ℕ × ℕ}
    {H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e thr : ℝ} {ps : List ℝ} (hβe : β ≤ e) :
    PWrites law I L.body (Env.frame [d] [w, (out.1, out.2 + 2 * lo)])
      (Store.inBlock out.1 (out.2 + 2 * lo) (2 * d))
      (RoundedCopied H₀ e thr ps a t p st out w r f j lo d)
      (RoundedReached H₀ e thr ps a t p st out w r f (j + 1)) φL := by
  have hst := PWrites.pstep_of_forall (ι := {B : Matrix (Fin d) (Fin d) ℂ // IsUpperHessenberg B})
    hI hloc (fun x => hLeaf (w := w) (o := (out.1, out.2 + 2 * lo)) x.1 x.2)
    (measurableSet_leafOutcome d β w (out.1, out.2 + 2 * lo)
      (Store.inBlock out.1 (out.2 + 2 * lo) (2 * d))) ?_
  · refine PStep.mono hst (fun μ ⟨M, rest, done, A, roots, _, hP, hW⟩ => ?_)
      (fun μ μ' ⟨M, rest, done, A, roots, hHM, hP, hW⟩ ⟨hfr, hinit, G, hG, hList⟩ => ?_) le_rfl
    · have hr := hP.2.2.2.2.2.1.active_block (r := (lo, d)) List.mem_cons_self
      exact ⟨⟨subBlock A (lo, d), hr.2.2⟩, hW, hP.leaf_operands⟩
    · rw [← hW.eq_storedMatrix] at hList
      have hcol : (Matrix.of fun i (_ : Fin 1) =>
          storedMatrix (out.1, out.2 + 2 * lo) d 1 μ'.store i 0) =
          storedMatrix (out.1, out.2 + 2 * lo) d 1 μ'.store := by
        ext i k
        fin_cases k
        rfl
      obtain ⟨M', hMM', hcore⟩ := roundedLeaf_core hP hβe hfr
        ⟨_, G, hG, hList, hcol ▸ holdsMatrix_storedMatrix hinit⟩
      refine ⟨hfr, M', (hHM.trans hMM').mono (le_of_eq (by push_cast; ring)),
        RoundedWorklistState.of_core hP.1 hP.2.1 hP.2.2.1 hfr ?_ hcore⟩
      have hr := hP.2.2.2.2.2.1.active_block (r := (lo, d)) List.mem_cons_self
      have := hr.2.1
      fp_sub [roundedWorklistFp]
  · rintro x μ μ' ⟨hH, -, -, -⟩ hfr ⟨roots, G, hG, hList, hO⟩
    refine ⟨hfr, fun i hi => by rw [Store.get_of_readBlock hO hi 0]; rfl, G, hG, ?_⟩
    have hroots : (fun i => storedMatrix (out.1, out.2 + 2 * lo) d 1 μ'.store i 0) = roots := by
      funext i
      rw [← hO.eq_storedMatrix]
      rfl
    rw [← hH.eq_storedMatrix, hroots]
    exact hList

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The decoupling call of a round on the good tapes: from a copied state of round
$j < 2(n + 1)$ on the range $(lo, d + 1)$, $d \ge k$, the copied block is in the decoupler's class
(norm at most $N_0$, condition at most $2B$, separation $g/2$, by
`NLAlib.DeflationInv.exists_pseudoConditionNumber_subBlock_le_and_le_norm_sub`), so a decoupler
meeting `NLAlib.ShiftedQR.RandomDecouplingContract` returns, except with probability at most
$\varphi_D$, the flag $0$ and an upper Hessenberg perturbed unitary similarity of the block with
error $\varepsilon(N_0)$ and a bottom-$k$ subdiagonal entry of modulus at most $\omega$. -/
theorem roundedDecouple_pwrites {I : Interp O Q ℝ} (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD : ℝ} {k F : ℕ}
    {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    {n : ℕ} {N₀ : ℝ}
    (hD : RandomDecouplingContract law (2 * B) (g / 2) φD k F n N₀ ps ω ε D I) {j lo d : ℕ}
    {a t p st out w r f : ℕ × ℕ} {H₀ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {dd : Fin (n + 1) → ℂ} {e thr : ℝ} (hV : IsUnit V)
    (hHV : H₀ * V = V * Matrix.diagonal dd) (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g ≤ ‖dd i - dd j‖) (hk : k ≤ d) (hdn : d ≤ n) (he0 : 0 ≤ e)
    (hN₀ : specNorm H₀ + 2 * (n + 1) * e ≤ N₀)
    (hsmall : 2 * (n + 1) * e ≤ g / (16 * (n + 1) * B)) (hj : j < 2 * (n + 1)) :
    PWrites law I D.body (Env.frame [d + 1, k, ps.length, F] [w, p, w, f])
      (Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (RoundedCopied H₀ e thr ps a t p st out w r f j lo (d + 1))
      (fun μ₁ => ∃ (μ : Mem ℝ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (rest done : List (ℕ × ℕ)) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (roots : Fin (n + 1) → ℂ), IsPerturbedUnitarySimilar H₀ M (j * e) ∧
        RoundedPopped H₀ e thr ps a t p st out w r f j M lo (d + 1) rest done A roots μ ∧
        μ.store.EqOff (Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ⊔
          Store.inBlock f.1 f.2 1) μ₁.store ∧
        μ₁.store.get f.1 f.2 = some 0 ∧
        ∃ H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ,
          IsPerturbedUnitarySimilar (subBlock A (lo, d + 1)) H' (ε N₀) ∧
          IsUpperHessenberg H' ∧ (∃ i : Fin d, d ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω) ∧
          HoldsMatrix w H' μ₁.store) φD := by
  let ι := {H : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ // IsUpperHessenberg H ∧ specNorm H ≤ N₀ ∧
    ∃ (Vr : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (dr : Fin (d + 1) → ℂ), IsUnit Vr ∧
      H * Vr = Vr * Matrix.diagonal dr ∧ pseudoConditionNumber Vr ≤ 2 * B ∧
      ∀ i j, i ≠ j → g / 2 ≤ ‖dr i - dr j‖}
  have hst := PWrites.pstep_of_forall hI hloc (fun x : ι =>
    have hx := x.2.2.2.choose_spec.choose_spec
    hD (n := d) (N := N₀) (w := w) (q := p) (f := f) x.1 _ _ hk hdn le_rfl x.2.1 x.2.2.1 hx.1
      hx.2.1 hx.2.2.1 hx.2.2.2)
    (measurableSet_decoupleOutcome d k (ε N₀) ω w f
      (Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1)) ?_
  · refine PStep.mono hst (fun μ ⟨M, rest, done, A, roots, hHM, hP, hW⟩ => ?_)
      (fun μ μ' ⟨M, rest, done, A, roots, hHM, hP, hW⟩
        ⟨hfr, hf0, hinit, hPUS, hHess, hsm⟩ => ?_) le_rfl
    · obtain ⟨hHess, hnorm, hp, hlD, hroomW, hroomF, hWF, hPWF⟩ := hP.decouple_operands he0 hN₀ hj
      have hInv := hP.2.2.2.2.2.1.of_isPerturbedUnitarySimilar hHM
      have hje : (j : ℝ) * e + 0 ≤ g / (16 * (n + 1) * B) := by
        have : (j : ℝ) * e ≤ 2 * (n + 1) * e :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hj.le) he0
        linarith
      obtain ⟨Vr, dr, hVr, hHVr, hκr, hgr⟩ :=
        hInv.exists_pseudoConditionNumber_subBlock_le_and_le_norm_sub hV hHV hκ hg hgap hje
          (r := (lo, d + 1)) List.mem_cons_self
      exact ⟨⟨subBlock A (lo, d + 1), hHess, hnorm, Vr, dr, hVr, hHVr, hκr, hgr⟩,
        hW, hp, hlD, hroomW, hroomF, hWF, hPWF⟩
    · rw [← hW.eq_storedMatrix] at hPUS
      exact ⟨hfr, μ, M, rest, done, A, roots, hHM, hP, hfr, hf0, _, hPUS, hHess, hsm,
        holdsMatrix_storedMatrix hinit⟩
  · rintro x μ μ' ⟨hH, -⟩ hfr ⟨hf0, H', hPUS, hHess, hsm, hW'⟩
    rw [hH.eq_storedMatrix, hW'.eq_storedMatrix] at hPUS
    rw [hW'.eq_storedMatrix] at hHess hsm
    exact ⟨hfr, hf0, fun i hi => by rw [Store.get_of_readBlock hW' hi 0]; rfl, hPUS, hHess, hsm⟩

/-- The large branch of a round on the good tapes: from a copied state of round
$j < 2(n + 1)$ on the range $(lo, d + 1)$, $d \ge k$, the decoupling call
(`NLAlib.ShiftedQR.roundedDecouple_pwrites`) and the deterministic rest of the branch
(`NLAlib.ShiftedQR.roundedLargeRest_writes`) reach the state before round $j + 1$, except with
probability at most $\varphi_D$. -/
theorem roundedLarge_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD : ℝ} {k F : ℕ}
    {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    {N₀ : ℝ} (hD : RandomDecouplingContract law (2 * B) (g / 2) φD k F n N₀ ps ω ε D I)
    {j lo d : ℕ}
    {a t p st out w r f : ℕ × ℕ} {H₀ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {dd : Fin (n + 1) → ℂ} {e thr c : ℝ} (hV : IsUnit V)
    (hHV : H₀ * V = V * Matrix.diagonal dd) (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g ≤ ‖dd i - dd j‖) (hd : lo + (d + 1) ≤ n + 1) (hk : k ≤ d)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (he : c + ε N₀ ≤ e) (he0 : 0 ≤ e) (hN₀ : specNorm H₀ + 2 * (n + 1) * e ≤ N₀)
    (hsmall : 2 * (n + 1) * e ≤ g / (16 * (n + 1) * B)) (hj : j < 2 * (n + 1)) :
    PWrites law I (roundedProcessLarge D).body
      (Env.frame [n + 1, k, ps.length, F, lo, d + 1] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (RoundedCopied H₀ e thr ps a t p st out w r f j lo (d + 1))
      (RoundedReached H₀ e thr ps a t p st out w r f (j + 1)) φD := by
  have hD' := roundedDecouple_pwrites (a := a) (t := t) (p := p) (st := st) (out := out) (w := w)
    (r := r) (f := f) (lo := lo) (thr := thr) hI hloc D hD hV hHV hκ hg hgap hk (by omega) he0 hN₀
    hsmall hj
  have hsq := Nat.mul_le_mul (show d + 1 ≤ n + 1 by omega) (show d + 1 ≤ n + 1 by omega)
  unfold roundedProcessLarge
  refine (PWrites.seq hI hloc le_rfl (hD'.in_frame rfl rfl
    fun μ ⟨_, _, _, _, _, _, hP, _⟩ => hP.1.live_of_subset (by simp))
    (PWrites.of_writes (F := roundedWorklistFp (n + 1) a st out w r f) le_rfl
      fun μ₁ τ hμ₁ => ?_)).mono (fun _ h => h) (by fp_sub [roundedWorklistFp]) (fun _ h => h)
    (by simp)
  obtain ⟨μ, M, rest, done, A, roots, hHM, hP, hfr, hf0, H', h1, h2, h3, h4⟩ := hμ₁
  refine (roundedLargeRest_writes hS hM hu hu1 hL hNat hQ hC D (fails := False) (tape := τ) hP hk
    hfind hcut hc he he0 hfr (Or.inr ⟨hf0, H', h1, h2, h3, h4⟩)).mono le_rfl ?_
  rintro μ' hfr' ⟨M', hMM', hcore⟩
  exact ⟨M', (hHM.trans hMM').mono (le_of_eq (by push_cast; ring)),
    RoundedWorklistState.of_core hP.1 hP.2.1 hP.2.2.1 (hfr.trans' hfr')
      (by fp_sub [roundedWorklistFp]) hcore⟩

/-- Processing a popped range on the good tapes: from a popped state of round
$j < 2(n + 1)$ on the range $(lo, d)$, $lo + d \le n + 1$, the copy, then the leaf call
(order at most $k$) or the large branch reach the state before round $j + 1$, except with
probability at most $\varphi_L + \varphi_D$. -/
theorem roundedRange_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD β φL : ℝ} {k F : ℕ}
    {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    {N₀ : ℝ} (hD : RandomDecouplingContract law (2 * B) (g / 2) φD k F n N₀ ps ω ε D I)
    (L : Impl O Q) (hLeaf : RandomLeafContract law β φL L I) (hφD : 0 ≤ φD) (hφL : 0 ≤ φL)
    {j lo d : ℕ} {a t p st out w r f : ℕ × ℕ} {H₀ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {dd : Fin (n + 1) → ℂ} {e thr c : ℝ} (hV : IsUnit V)
    (hHV : H₀ * V = V * Matrix.diagonal dd) (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g ≤ ‖dd i - dd j‖) (hd : lo + d ≤ n + 1)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀) (he : c + ε N₀ + β ≤ e)
    (hN₀ : specNorm H₀ + 2 * (n + 1) * e ≤ N₀)
    (hsmall : 2 * (n + 1) * e ≤ g / (16 * (n + 1) * B)) (hj : j < 2 * (n + 1)) :
    PWrites law I (roundedProcessRange D L).body
      (Env.frame [n + 1, k, ps.length, F, lo, d] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (fun μ => ∃ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (rest done : List (ℕ × ℕ))
        (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (roots : Fin (n + 1) → ℂ),
        IsPerturbedUnitarySimilar H₀ M (j * e) ∧
          RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ)
      (RoundedReached H₀ e thr ps a t p st out w r f (j + 1)) (φL + φD) := by
  have hsq := Nat.mul_le_mul (show d ≤ n + 1 by omega) (show d ≤ n + 1 by omega)
  have hcopy : ∀ ds args, IExp.evalList
      (Env.frame [n + 1, k, ps.length, F, lo, d] [a, t, p, st, out, w, r, f]).idx ds =
        some [n + 1, lo, d] →
      Operand.evalList (Env.frame [n + 1, k, ps.length, F, lo, d] [a, t, p, st, out, w, r, f])
        args = some [a, w] →
      PWrites law I (Stmt.frame ds args (copyToWork (Op := O) (Tst := Q)).body)
        (Env.frame [n + 1, k, ps.length, F, lo, d] [a, t, p, st, out, w, r, f])
        (Store.inBlock w.1 w.2 (2 * (d * d)))
        (fun μ => ∃ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (rest done : List (ℕ × ℕ))
          (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (roots : Fin (n + 1) → ℂ),
          IsPerturbedUnitarySimilar H₀ M (j * e) ∧
            RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ)
        (RoundedCopied H₀ e thr ps a t p st out w r f j lo d) 0 := fun ds args hds hargs =>
    PWrites.of_writes le_rfl fun μ τ ⟨M, rest, done, A, roots, hHM, hP⟩ =>
      ((hP.writes_copyToWork (tape := τ) hS).in_frame hds hargs
        (hP.1.live_of_subset (by simp))).mono le_rfl fun μ₁ _ ⟨hP₁, hW₁⟩ =>
          ⟨M, rest, done, A, roots, hHM, hP₁, hW₁⟩
  unfold roundedProcessRange
  by_cases hs : d ≤ k
  · refine (PWrites.seq hI hloc (by positivity) (hcopy _ _ rfl rfl) (PWrites.seq hI hloc hφD
      (PWrites.ifPos (n := k + 1 - d) rfl hφL
        (fun _ => (roundedLeaf_pwrites hI hloc L hLeaf (show β ≤ e by linarith) (a := a) (t := t)
          (p := p) (st := st) (out := out) (w := w) (r := r) (f := f) (H₀ := H₀) (thr := thr)
          (ps := ps) (j := j) (lo := lo) (d := d)).in_frame
          rfl rfl fun μ ⟨_, _, _, _, _, _, hP, _⟩ => hP.leaf_operands.1)
        (fun h0 => absurd h0 (by omega)))
      (PWrites.ifPos (F := ⊥) (n := d - k) rfl hφD (fun h => absurd h (by omega))
        fun _ _ h => h))).mono
      (fun _ h => h) (by fp_sub [roundedWorklistFp]) (fun _ h => h) (by simp)
  · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    refine (PWrites.seq hI hloc (by positivity) (hcopy _ _ rfl rfl) (PWrites.seq hI hloc hφD
      (PWrites.ifPos (F := ⊥) (n := k + 1 - (d' + 1)) rfl hφL (fun h => absurd h (by omega))
        fun _ _ h => h)
      (PWrites.ifPos (n := d' + 1 - k) rfl hφD (fun _ => (roundedLarge_pwrites hS hM hu hu1 hL hNat
        hQ hC hI hloc
        D hD hV hHV hκ hg hgap hd (by omega) hfind hcut hc (by linarith) (by linarith) hN₀
        hsmall hj).in_frame rfl rfl fun μ ⟨_, _, _, _, _, _, hP, _⟩ => hP.1.live)
        (fun h0 => absurd h0 (by omega))))).mono
      (fun _ h => h) (by fp_sub [roundedWorklistFp]) (fun _ h => h) (by simp)

/-- One round of the rounded worklist on the good tapes: from the state before round
$j < 2(n + 1)$ with a positive stack count, the pop, the two bounded index reads and the
processing of the popped range (`NLAlib.ShiftedQR.roundedRange_pwrites`) reach the state before
round $j + 1$, except with probability at most $\varphi_L + \varphi_D$. -/
theorem roundedWorklistRound_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD β φL : ℝ} {k F : ℕ}
    {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    {N₀ : ℝ} (hD : RandomDecouplingContract law (2 * B) (g / 2) φD k F n N₀ ps ω ε D I)
    (L : Impl O Q) (hLeaf : RandomLeafContract law β φL L I) (hφD : 0 ≤ φD) (hφL : 0 ≤ φL)
    {j : ℕ} {a t p st out w r f : ℕ × ℕ} {H₀ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {dd : Fin (n + 1) → ℂ} {e thr c : ℝ} (hV : IsUnit V)
    (hHV : H₀ * V = V * Matrix.diagonal dd) (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g ≤ ‖dd i - dd j‖)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀) (he : c + ε N₀ + β ≤ e)
    (hN₀ : specNorm H₀ + 2 * (n + 1) * e ≤ N₀)
    (hsmall : 2 * (n + 1) * e ≤ g / (16 * (n + 1) * B)) (hj : j < 2 * (n + 1)) :
    PWrites law I (roundedWorklistRound D L).body
      (Env.frame [n + 1, k, ps.length, F] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (fun μ => RoundedReached H₀ e thr ps a t p st out w r f j μ ∧
        ∃ count : ℕ, μ.store.get st.1 st.2 = some (count : ℝ) ∧ 0 < count)
      (RoundedReached H₀ e thr ps a t p st out w r f (j + 1)) (φL + φD) := by
  unfold roundedWorklistRound
  refine (PWrites.seq (F₂ := roundedWorklistFp (n + 1) a st out w r f) (φ₁ := 0)
    (φ₂ := φL + φD) (Mid := fun μ₁ => ∃ M, IsPerturbedUnitarySimilar H₀ M (j * e) ∧
      ∃ (lo d : ℕ) (rest done : List (ℕ × ℕ)) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (roots : Fin (n + 1) → ℂ),
        RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ₁ ∧
          μ₁.store.get r.1 r.2 = some (lo : ℝ) ∧ μ₁.store.get r.1 (r.2 + 1) = some (d : ℝ))
    hI hloc (by positivity)
    (PWrites.of_writes (F := Store.inBlock st.1 st.2 1 ⊔ Store.inBlock r.1 r.2 2) le_rfl
      fun μ τ ⟨⟨M, hHM, hst⟩, cnt, hcnt, hpos⟩ =>
        ((hst.writes_rangePop (tape := τ) hS hL hQ hNat hcnt hpos).in_frame rfl rfl
          (hst.1.live_of_subset (by simp))).mono le_rfl fun μ₁ _ h => ⟨M, hHM, h⟩) ?_).mono
    (fun _ h => h) (by fp_sub [roundedWorklistFp]) (fun _ h => h) (by simp)
  refine PWrites.bindIdx hI (B := n + 1) rfl rfl
    (fun μ ⟨M, hHM, lo, d, rest, done, A, roots, hP, hLo, hd⟩ => ⟨lo,
      by have := (hP.2.2.2.2.2.1.active_block (r := (lo, d)) List.mem_cons_self).2.1; omega,
      hQ.index_eq_of_decode_nat hLo rfl⟩) fun v _ => ?_
  refine PWrites.bindIdx hI (B := n + 1) rfl rfl
    (fun μ ⟨⟨M, hHM, lo, d, rest, done, A, roots, hP, hLo, hd⟩, _⟩ => ⟨d,
      by have := (hP.2.2.2.2.2.1.active_block (r := (lo, d)) List.mem_cons_self).2.1; omega,
      hQ.index_eq_of_decode_nat hd rfl⟩) fun v' _ => ?_
  have hpre : ∀ μ, ((∃ M, IsPerturbedUnitarySimilar H₀ M (j * e) ∧ ∃ (lo d : ℕ)
      (rest done : List (ℕ × ℕ)) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (roots : Fin (n + 1) → ℂ),
      RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ ∧
        μ.store.get r.1 r.2 = some (lo : ℝ) ∧ μ.store.get r.1 (r.2 + 1) = some (d : ℝ)) ∧
      I.index (Has.inj IdxTst.toNat) [r] μ = some v) ∧
      I.index (Has.inj IdxTst.toNat) [(r.1, r.2 + 1)] μ = some v' →
      v + v' ≤ n + 1 ∧ ∃ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (rest done : List (ℕ × ℕ))
        (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (roots : Fin (n + 1) → ℂ),
        IsPerturbedUnitarySimilar H₀ M (j * e) ∧
          RoundedPopped H₀ e thr ps a t p st out w r f j M v v' rest done A roots μ := by
    rintro μ ⟨⟨⟨M, hHM, lo, d, rest, done, A, roots, hP, hLo, hd⟩, hv⟩, hv'⟩
    obtain rfl : lo = v := Option.some.inj ((hQ.index_eq_of_decode_nat hLo rfl).symm.trans hv)
    obtain rfl : d = v' := Option.some.inj ((hQ.index_eq_of_decode_nat hd rfl).symm.trans hv')
    exact ⟨(hP.2.2.2.2.2.1.active_block (r := (lo, d)) List.mem_cons_self).2.1,
      M, rest, done, A, roots, hHM, hP⟩
  by_cases hvv : v + v' ≤ n + 1
  · exact ((roundedRange_pwrites hS hM hu hu1 hL hNat hQ hC hI hloc D hD L hLeaf hφD hφL hV hHV
      hκ hg hgap hvv hfind hcut hc hβ hε0 he hN₀ hsmall hj).in_frame rfl rfl
      fun μ ⟨_, _, _, _, _, _, hP⟩ => hP.1.live).mono (fun μ h => (hpre μ h).2) le_rfl
      (fun _ h => h) le_rfl
  · exact ⟨fun _ => Set.univ, by simp, fun _ _ _ _ => Iff.rfl,
      fun μ h => absurd (hpre μ h).1 hvv⟩

/-- The capped worklist on the good tapes: from the initialized views holding an upper
Hessenberg $\mathbf{H}$, diagonalizable with condition at most $B$ and eigenvalues separated by
$g > 0$, with the threshold word, the decoupler and the leaf as in
`NLAlib.ShiftedQR.RandomDecouplingContract` (condition $2B$, separation $g/2$, norm $N_0$) and
`NLAlib.ShiftedQR.RandomLeafContract`, and $2(n + 1)(c + \varepsilon(N_0) + \beta)$ at most
$N_0 - \|\mathbf{H}\|_2$ and at most $g/(16(n + 1)B)$, the
initialization and the $2(n + 1)$ capped rounds (`NLAlib.Ops.PWrites.whileFuel`, each round
`NLAlib.ShiftedQR.roundedWorklistRound_pwrites`) reach, except with probability at most
$2(n + 1)(\varphi_L + \varphi_D)$, a final state that has not failed, for a matrix reached from
$\mathbf{H}$ with error $2(n + 1)(c + \varepsilon(N_0) + \beta)$. -/
theorem roundedWorklist_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD β φL : ℝ} {k F : ℕ}
    {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    {N₀ : ℝ} (hD : RandomDecouplingContract law (2 * B) (g / 2) φD k F n N₀ ps ω ε D I)
    (L : Impl O Q) (hLeaf : RandomLeafContract law β φL L I) (hφD : 0 ≤ φD) (hφL : 0 ≤ φL)
    {a t p st out w r f : ℕ × ℕ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {dd : Fin (n + 1) → ℂ} {thr c : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal dd) (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g ≤ ‖dd i - dd j‖)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀)
    (hN₀ : specNorm H + 2 * (n + 1) * (c + ε N₀ + β) ≤ N₀)
    (hsmall : 2 * (n + 1) * (c + ε N₀ + β) ≤ g / (16 * (n + 1) * B)) :
    PWrites law I (roundedWorklist D L).body
      (Env.frame [n + 1, k, ps.length, F] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (fun μ => RoundedGeometry (n + 1) ps.length a t p st out w r f μ ∧
        HoldsMatrix a H μ.store ∧ μ.store.get t.1 t.2 = some thr ∧
        μ.store.readBlock p.1 p.2 ps.length = some ps)
      (fun μ' => ∃ M', IsPerturbedUnitarySimilar H M' (2 * (n + 1) * (c + ε N₀ + β)) ∧
        RoundedFinal False out f M' μ') (2 * (n + 1) * (φL + φD)) := by
  have he0 : 0 ≤ c + ε N₀ + β := by linarith
  have h0 : Mch.lit ((0 : ℕ) : ℚ) = 0 := by simpa using hNat 0 (Nat.zero_le _)
  unfold roundedWorklist
  refine (PWrites.seq hI hloc (by positivity)
    (PWrites.of_writes (F := Store.inBlock f.1 f.2 1) (Post := fun μ₁ => ∃ μ,
      (RoundedGeometry (n + 1) ps.length a t p st out w r f μ ∧ HoldsMatrix a H μ.store ∧
        μ.store.get t.1 t.2 = some thr ∧ μ.store.readBlock p.1 p.2 ps.length = some ps) ∧
      μ.store.EqOff (Store.inBlock f.1 f.2 1) μ₁.store ∧ μ₁.store.get f.1 f.2 = some 0) le_rfl
      fun μ τ hpre => ?_)
    (PWrites.seq hI hloc (by positivity)
      (PWrites.of_writes (F := Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
        (Post := RoundedReached H (c + ε N₀ + β) thr ps a t p st out w r f 0) le_rfl
        fun μ₁ τ ⟨μ, ⟨hG, hA, ht, hp⟩, hfr₁, hF₁⟩ => ?_)
      (PWrites.whileFuel (F := roundedWorklistFp (n + 1) a st out w r f) (G := ⊥)
        (N := 2 * (n + 1)) hI hloc rfl
        (RoundedReached H (c + ε N₀ + β) thr ps a t p st out w r f)
        (fun _ => φL + φD) (fun _ _ => by positivity) le_rfl (fun _ h => h) ?_ ?_ ?_))).mono
    (fun _ h => h) (by fp_sub [roundedWorklistFp]) (fun _ h => h) (le_of_eq ?_)
  · refine (writes_indexLit hL rfl rfl
      (by have := hpre.1.room.2.2.2.2.2.2.2.1; omega)).mono le_rfl ?_
    rintro μ₁ hfr ⟨-, hF⟩
    exact ⟨μ, hpre, hfr, by simpa only [h0] using hF⟩
  · have hlS : μ₁.Live [st] := (hG.of_eqOff hfr₁).live_of_subset (by simp)
    obtain ⟨hFA, hFS⟩ : Fp.Disj (Store.inBlock f.1 f.2 1)
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) ∧ Fp.Disj (Store.inBlock f.1 f.2 1)
        (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) :=
      ⟨by simpa using hG.disj 7 0 (by simp), by simpa using hG.disj 7 3 (by simp)⟩
    have hSA : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by simpa using hG.disj 3 0 (by simp)
    refine ((stackInit_writes_of_isExactNatLit (Op := O) (Tst := Q) (τ := τ) hL hQ hNat
      (lo := 0) (size := n + 1) (by omega) le_rfl le_rfl (Nat.succ_pos n)
      (by simpa only [Nat.add_assoc] using (hG.of_eqOff hfr₁).room.2.2.2.1)).in_frame rfl rfl
      hlS).mono le_rfl ?_
    rintro μ₂ hfr₂ ⟨-, hSt₂⟩
    have hfr₁₂ := hfr₁.trans' hfr₂
    refine ⟨H, by simpa using IsPerturbedUnitarySimilar.refl H,
      RoundedWorklistState.of_core hG ht hp
      hfr₁₂ (by fp_sub [roundedWorklistFp]) (Or.inr ⟨hfr₂.keep (Store.readsOnly_get _ _ _)
        hFS.symm hF₁, by simp, [(0, n + 1)], [], H, fun _ => 0, hHess.deflationInv_init _,
        hA.of_eqOff hfr₁₂ (Fp.disj_sup_left.mpr ⟨hFA, hSA⟩), fun _ hq => by simp at hq,
        by simpa using hSt₂, by simp⟩)⟩
  · rintro i - μ ⟨M, -, hst⟩
    obtain ⟨cnt, hcnt, -, -⟩ := hst.count
    exact ⟨_, by rw [Interp.testAt_eq rfl rfl, hC.test_isPos hcnt]⟩
  · intro i hi
    refine ((roundedWorklistRound_pwrites hS hM hu hu1 hL hNat hQ hC hI hloc D hD L hLeaf hφD hφL
      hV hHV hκ hg hgap hfind hcut hc hβ hε0 le_rfl hN₀ hsmall hi).in_frame rfl rfl
      fun μ ⟨⟨_, _, hst⟩, _⟩ => hst.1.live).mono (fun μ ⟨⟨M, hHM, hst⟩, htest⟩ => ?_) le_rfl
      (fun _ h => h) le_rfl
    obtain ⟨cnt, hcnt, -, -⟩ := hst.count
    rw [Interp.testAt_eq rfl rfl, hC.test_isPos hcnt] at htest
    have hpos : (0 : ℝ) < id (cnt : ℝ) := of_decide_eq_true (Option.some.inj htest)
    exact ⟨⟨M, hHM, hst⟩, cnt, hcnt, by simpa using hpos⟩
  · intro i hi
    refine PWrites.of_writes le_rfl fun μ τ ⟨⟨M, hHM, hst⟩, hcase⟩ => ?_
    obtain ⟨cnt, hcnt, hfin, hlt⟩ := hst.count
    have hc0 : cnt = 0 := by
      rcases hcase with rfl | htest
      · by_contra hne
        have := hlt (Nat.pos_of_ne_zero hne)
        omega
      · rw [Interp.testAt_eq rfl rfl, hC.test_isPos hcnt] at htest
        by_contra hne
        have hp : (0 : ℝ) < cnt := by exact_mod_cast Nat.pos_of_ne_zero hne
        simp [hp] at htest
    subst hc0
    refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := st) hcnt) ?_
    rw [show decide (0 < id ((0 : ℕ) : ℝ)) = false by simp, if_neg (by simp)]
    refine Writes.skip ⟨M, hHM.mono ?_, hfin rfl⟩
    have : (i : ℝ) ≤ 2 * (n + 1) := by exact_mod_cast hi
    nlinarith
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_zero, zero_add]
    push_cast
    ring

/-- **The rounded worklist with randomized routines** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3], the worklist with the probability of success): on a machine with the standard model
at $0 \le \boldsymbol{u} < 1$ whose natural literals up to $n + 1$ are exact, with a measurable
interpretation that reads the tape only in its windows, let the decoupler `D` meet
`NLAlib.ShiftedQR.RandomDecouplingContract` on the class (condition $2B$, separation $g/2$) up
to order $n + 1$ and norm $N_0$, with failure probability $\varphi_D \ge 0$, and the leaf `L` meet
`NLAlib.ShiftedQR.RandomLeafContract` with error $\beta \ge 0$ and failure probability
$\varphi_L \ge 0$. Let $\mathbf{H}$ be upper Hessenberg of
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
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD β φL : ℝ} {k F : ℕ}
    {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    {N₀ : ℝ} (hD : RandomDecouplingContract law (2 * B) (g / 2) φD k F n N₀ ps ω ε D I)
    (L : Impl O Q) (hLeaf : RandomLeafContract law β φL L I) (hφD : 0 ≤ φD) (hφL : 0 ≤ φL)
    {a t p out f : ℕ × ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {thr c : ℝ}
    (hHess : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀)
    (hN₀ : specNorm H + 2 * (n + 1) * (c + ε N₀ + β) ≤ N₀)
    (hsmall : 2 * (n + 1) * (c + ε N₀ + β) ≤ g / (16 * (n + 1) * B)) :
    PWrites law I (solveRounded D L).body (Env.frame [n + 1, k, ps.length, F] [a, t, p, out, f])
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
  unfold solveRounded
  refine PWrites.allocs (lens := [.const 1 + .const 2 * .var 0, .const 2 * (.var 0 * .var 0),
    .const 5]) (ns := [1 + 2 * (n + 1), 2 * ((n + 1) * (n + 1)), 5]) rfl
    (Pre₁ := fun b₀ μ => RoundedGeometry (n + 1) ps.length a t p (b₀, 0) out (b₀ + 1, 0)
      (b₀ + 2, 0) f μ ∧ HoldsMatrix a H μ.store ∧ μ.store.get t.1 t.2 = some thr ∧
      μ.store.readBlock p.1 p.2 ps.length = some ps) ?_ ?_ fun b₀ => ?_
  · rintro μ s₁ ⟨hl, hr, ha, hA, ht, hp⟩ hs hlens hBelow
    exact ⟨roundedGeometry_allocated hl hr ha hs hlens hBelow, hA.of_below hBelow (hl a (by simp)),
      hBelow.get_of (hl t (by simp)) ht, (hBelow.readBlock (hl p (by simp)) p.2 ps.length).trans hp⟩
  · rintro μ ⟨hl, -⟩ s s' pos hBelow ⟨hf, roots, E, hOut, hE, hR⟩
    exact ⟨hBelow.get_of (hl f (by simp)) hf, roots, E, hOut.of_below hBelow (hl out (by simp)),
      hE, hR⟩
  · refine ((roundedWorklist_pwrites (a := a) (t := t) (p := p) (st := (b₀, 0)) (out := out)
      (w := (b₀ + 1, 0)) (r := (b₀ + 2, 0)) (f := f) hS hM hu hu1 hL hNat hQ hC hI hloc D hD L
      hLeaf hφD hφL hHess
      hV hHV hκ hg hgap hfind hcut hc hβ hε0 hN₀ hsmall).in_frame rfl rfl
      fun μ h => h.1.live).mono (fun _ h => h) (by fp_sub [roundedWorklistFp]) ?_
      (le_of_eq (by ring))
    rintro μ' ⟨M', hHM, ⟨hfalse, -⟩ | ⟨hf, done, A, roots, hInv, hOut⟩⟩
    · exact hfalse.elim
    · obtain ⟨E, hE, hR⟩ := (hInv.of_isPerturbedUnitarySimilar hHM).exists_roots_eq
      exact ⟨hf, roots, E, hOut, by simpa using hE, hR⟩

/-- **The probability of success of the rounded worklist** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3], at the level of the worklist): on a machine with the standard model at
$0 \le \boldsymbol{u} < 1$ whose natural literals up to $n + 1$ are exact, with a measurable
interpretation that reads the tape only in its windows, let the decoupler `D` meet
`NLAlib.ShiftedQR.RandomDecouplingContract` on the class (condition $2B$, separation $g/2$) up
to order $n + 1$ and norm $N_0$, with failure probability $\varphi_D \ge 0$, and the leaf `L` meet
`NLAlib.ShiftedQR.RandomLeafContract` with error $\beta \ge 0$ and failure probability
$\varphi_L \ge 0$. Let $\mathbf{H}$ be upper Hessenberg of order $n + 1$ with
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$, $\kappa(\mathbf{V}) \le B$ and
eigenvalues separated by $g > 0$; let the threshold word $t$ satisfy
$(1 + \boldsymbol{u})^2\omega^2 \le t \le (1 - \boldsymbol{u})^2c^2$, $c \ge 0$, let
$\varepsilon(N_0) \ge 0$, $e = c + \varepsilon(N_0) + \beta$, $\|\mathbf{H}\|_2 + 2(n+1)e \le N_0$
and $2(n + 1)e \le g/(16(n+1)B)$; let the five views be live, have room and be pairwise apart,
holding $\mathbf{H}$, $t$ and the parameter words, and let `ξ` be a random tape with the stream
laws `law`. Then the run fails to write only the matrix, the output and the failure word, set
the failure word to $0$ and store the spectrum of some $\mathbf{H} + \mathbf{E}$ with
$\|\mathbf{E}\|_2 \le 2(n + 1)e$, with probability at most $2(n + 1)(\varphi_D + \varphi_L)$. -/
theorem solveRounded_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD β φL : ℝ} {k F : ℕ}
    {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    {N₀ : ℝ} (hD : RandomDecouplingContract law (2 * B) (g / 2) φD k F n N₀ ps ω ε D I)
    (L : Impl O Q) (hLeaf : RandomLeafContract law β φL L I) (hφD : 0 ≤ φD) (hφL : 0 ≤ φL)
    {a t p out f : ℕ × ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {thr c : ℝ}
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
      (Env.frame [n + 1, k, ps.length, F] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
          HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
          specNorm E ≤ 2 * (n + 1) * (c + ε N₀ + β) ∧
          (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)) μ} ≤
      2 * (n + 1) * (φD + φL) :=
  (solveRounded_pwrites hS hM hu hu1 hL hNat hQ hC hI hloc D hD L hLeaf hφD hφL hHess hV hHV hκ
    hg hgap hfind hcut hc hβ hε0 hN₀ hsmall).measureReal_not_writes_le ⟨hl, hr, ha, hA, ht, hp⟩ hξ

/-- **The rounded worklist with routines as a probabilistic block**
([BanksGarzaVargasSrivastava2025, Theorem 6.1]; [BanksGarzaVargasSrivastava2022, Theorem 6.3]):
`NLAlib.ShiftedQR.solveRounded_pwrites` for `NLAlib.ShiftedQR.solveRoundedWith`, with a decoupling
routine meeting `NLAlib.ShiftedQR.RandomDecouplingRoutineContract` at the class $(2B, g/2)$ and a
leaf routine meeting `NLAlib.ShiftedQR.RandomLeafRoutineContract` on the blocks of order at most
$\min(k, n + 1)$ and norm at most $N_0$. On a machine with the standard model at
$0 \le \boldsymbol{u} < 1$,
exact natural literals up to $n + 1$, exact `toNat` and comparisons, a measurable interpretation
reading the tape only in its windows, let $\mathbf{H}$ of order $n + 1$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$ and eigenvalues separated by $g > 0$, the threshold
$t$ with $(1 + \boldsymbol{u})^2\omega^2 \le t \le (1 - \boldsymbol{u})^2c^2$, $c, \beta,
\varepsilon(N_0) \ge 0$, $\|\mathbf{H}\|_2 + 2(n + 1)(c + \varepsilon(N_0) + \beta) \le N_0$ and
$2(n + 1)(c + \varepsilon(N_0) + \beta) \le g/(16(n + 1)B)$. Then, from the stored input, except
with probability at most $2(n + 1)(\varphi_D + \varphi_L)$, the run writes only the matrix, the
output and the failure word, sets the failure word to $0$ and stores all eigenvalues of
$\mathbf{H} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le 2(n + 1)(c + \varepsilon(N_0) + \beta)$. -/
theorem solveRoundedWith_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD β φL : ℝ} {k F T : ℕ}
    {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q) {N₀ : ℝ}
    (hD : RandomDecouplingRoutineContract law (2 * B) (g / 2) φD k F T n N₀ ps ω ε D I)
    (L : Impl O Q) (hLeaf : RandomLeafRoutineContract law β φL (min k (n + 1)) N₀ ps T L I)
    (hφD : 0 ≤ φD)
    (hφL : 0 ≤ φL) {a t p out f : ℕ × ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {thr c : ℝ}
    (hHess : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀)
    (hN₀ : specNorm H + 2 * (n + 1) * (c + ε N₀ + β) ≤ N₀)
    (hsmall : 2 * (n + 1) * (c + ε N₀ + β) ≤ g / (16 * (n + 1) * B)) :
    PWrites law I (solveRoundedWith D L).body
      (Env.frame [n + 1, k, ps.length, F, T] [a, t, p, out, f])
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

end Theorems

end NLAlib.ShiftedQR
