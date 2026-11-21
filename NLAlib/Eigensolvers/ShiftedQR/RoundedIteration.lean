/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedRegularize
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSh
public import NLAlib.Eigensolvers.ShiftedQR.RoundedShStep
public import NLAlib.Eigensolvers.ShiftedQR.RoundedShExcTrials

/-!
# One rounded iteration of the decoupling loop

One iteration of the loop of [BanksGarzaVargasSrivastava2022, Lemma 6.4] in floating point:
`Regularize` either decouples the matrix with one of its trial steps or returns $\theta$-optimal
shifts away from the spectrum, and in the second case the shifting strategy $\mathrm{Sh}_{k,B}$
takes a step with them. Except with the sum of the two failure probabilities, the matrix becomes
an upper Hessenberg perturbed unitary similarity that is decoupled at the bottom or whose
potential $\psi_k$ has contracted by $1.002(1 - \gamma)$.

## Main definitions

* `NLAlib.ShiftedQR.shIterationWith`: the program with a small-eigenvalue routine;
  `NLAlib.ShiftedQR.shIteration`: the program with the `SmallEig` kernel;
  `NLAlib.ShiftedQR.ShIterationOutcome`: its outcome.

## Main results

* `NLAlib.ShiftedQR.measurableSet_iterationOutcome`: the outcome is measurable.
* `NLAlib.ShiftedQR.shStep_pwrites_of_forall`, `NLAlib.ShiftedQR.shIteration_regularize_pwrites`:
  the two branches of an iteration.
* `NLAlib.ShiftedQR.shIterationWithScratchWith_pwrites`: one iteration with its scratch log, as a
  probabilistic block.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- One iteration with a small-eigenvalue routine and caller-owned scratch:
`NLAlib.ShiftedQR.regularizeWith` of the order-$N$ matrix `A` (radius word `Rd`, `Optimal` word
`C`, threshold word `Thr`, the routine `SE` with the words `Qw` and the cap $T$) into the $k$
shift pairs `S` and the flag `Fl`; if the flag is $0$ (the shifts are optimal),
`NLAlib.ShiftedQR.shStep` with them and the words `Cg`, `Cr`, `Cw`, `Cp`, the net `G` of $n_0$
points and `Thr`. The iteration's $k + 1 + n_0$ trial sites record their rotations in the slots
$j_0, \dots, j_0 + k + n_0$ of the slotted log `Lg` of slot width $w$: `Regularize`'s trials at
$j_0 + t$, `Sh`'s test step at $j_0 + k$ and its exceptional trials after it. The interface is
`[N, m, k, n0, nq, T, w, j0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw, S) → (A, Fl, Lg)`. -/
def shIterationWithScratchWith (SE : Stmt O Q) : Stmt O Q :=
  ops% [N, m, k, n0, nq, T, w, j0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw, S) → (A, Fl, Lg) {
    run (regularizeWith SE) [N, k, nq, T, w, j0] (A, Rd, C, Thr, Qw, A, S, Fl, Lg);
    if (Has.inj CmpTst.isZero) [] (Fl) {
      run (shStep (O := O) (Q := Q)) [N, m, k, n0, w, j0 + k]
        (A, S, Cg, Cr, Cw, Cp, G, Thr, A, Fl, Lg)
    } else { skip }
  }

/-- **One iteration of the decoupling loop with a small-eigenvalue routine**
([BanksGarzaVargasSrivastava2022, Lemma 6.4], the body of the loop): `Regularize` with the
routine `SE`, then `Sh` with its shifts if they are optimal. The scratch for the $k$ shift pairs
is scoped; the rotations go to the slots $j_0, \dots, j_0 + k + n_0$ of the log `Lg`. The
interface is `[N, m, k, n0, nq, T, w, j0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw) → (A, Fl, Lg)`. -/
def shIterationWith (SE : Stmt O Q) : Stmt O Q :=
  ops% [N, m, k, n0, nq, T, w, j0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw) → (A, Fl, Lg) {
    let S ← alloc (2 * k);
    run (shIterationWithScratchWith SE) [N, m, k, n0, nq, T, w, j0]
      (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw, S, A, Fl, Lg)
  }

/-- **One iteration of the decoupling loop** ([BanksGarzaVargasSrivastava2022, Lemma 6.4], the
body of the loop): `NLAlib.ShiftedQR.shIterationWith` with the `SmallEig` kernel
(`NLAlib.ShiftedQR.smallEigKernel`), no words and the cap $0$: `Regularize`, then `Sh` with its
shifts if they are optimal, recording the rotations in the slots $j_0, \dots, j_0 + k + n_0$ of
the log `Lg`. The interface is `[N, m, k, n0, w, j0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G) →
(A, Fl, Lg)`. -/
def shIteration : Stmt O Q :=
  ops% [N, m, k, n0, w, j0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G) → (A, Fl, Lg) {
    run (shIterationWith (smallEigKernel (O := O) (Q := Q))) [N, m, k, n0, 0, 0, w, j0]
      (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Rd, A, Fl, Lg)
  }

end Program

variable {n : ℕ}

/-- **The outcome of one iteration**, with the decoupling rate $\gamma$, the scan threshold $t$
and the backward error $\varepsilon$: `a` holds an upper Hessenberg perturbed unitary similarity
$\widehat{\mathbf{H}}$ of $\mathbf{H}$ with error $\varepsilon$ that is decoupled at the bottom
(one of its last $k$ subdiagonal entries has $(1 - \boldsymbol{u})^2\lvert h\rvert^2 \le t$) or
has $\psi_k(\widehat{\mathbf{H}}) \le 1.002(1 - \gamma)\psi_k(\mathbf{H})$. -/
def ShIterationOutcome (u : ℝ) (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (γ tv ε : ℝ) (a : ℕ × ℕ) (m' : Mem ℝ) : Prop :=
  ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    IsPerturbedUnitarySimilar H H' ε ∧ IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
    ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
      hessenbergPotential k H' ≤ 1.002 * (1 - γ) * hessenbergPotential k H)

/-- **The outcome of one iteration by its recorded unitary**: `NLAlib.ShiftedQR.ShIterationOutcome`
with the witness named. The iteration closes `c` slots `Ls` after the slots `LL` of the log at
`lg`, and $\widehat{\mathbf{H}}$ is a perturbed similarity of $\mathbf{H}$ by the exact unitary
of their valid entries. -/
def ShIterationOutcomeBy (u : ℝ) (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (γ tv ε : ℝ) (a lg : ℕ × ℕ) (ns w : ℕ) (LL : List (Option (List GivensEntry))) (c : ℕ)
    (m' : Mem ℝ) : Prop :=
  ∃ Ls : List (Option (List GivensEntry)), Ls.length = c ∧
    (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store ∧
  ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries w Ls)) H H' ε ∧
    IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
    ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
      hessenbergPotential k H' ≤ 1.002 * (1 - γ) * hessenbergPotential k H)

/-- Forgetting the witness of an outcome. -/
theorem ShIterationOutcomeBy.shIterationOutcome {u : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {γ tv ε : ℝ} {a lg : ℕ × ℕ} {ns w c : ℕ}
    {LL : List (Option (List GivensEntry))} {m' : Mem ℝ}
    (h : ShIterationOutcomeBy u k H γ tv ε a lg ns w LL c m') :
    ShIterationOutcome u k H γ tv ε a m' := by
  obtain ⟨Ls, -, -, -, H', hby, hH', hA, hd⟩ := h
  exact ⟨H', hby.isPerturbedUnitarySimilar, hH', hA, hd⟩

/-- **The outcomes of an iteration by the recorded unitary form a measurable set**: as
`NLAlib.ShiftedQR.measurableSet_iterationOutcome`, with the witness the unitary of the log read
after (`NLAlib.slottedLogRead`) beyond its first `j0` slots. -/
theorem measurableSet_iterationOutcomeBy (u : ℝ) (k : ℕ) (c tv ε : ℝ) (a lg : ℕ × ℕ)
    (ns w j0 : ℕ) (F : Fp) :
    MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (x.2.store.get a.1 (a.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilarBy
        (givensLog (n + 1) (slotEntries w ((slottedLogRead lg ns w x.2.store).drop j0)))
        (storedMatrix a (n + 1) (n + 1) x.1.store) (storedMatrix a (n + 1) (n + 1) x.2.store) ε ∧
      IsUpperHessenberg (storedMatrix a (n + 1) (n + 1) x.2.store) ∧
      ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧
          (1 - u) ^ 2 * ‖storedMatrix a (n + 1) (n + 1) x.2.store i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
        hessenbergPotential k (storedMatrix a (n + 1) (n + 1) x.2.store) ≤
          c * hessenbergPotential k (storedMatrix a (n + 1) (n + 1) x.1.store))} := by
  have hm := measurable_storedMatrix a (n + 1) (n + 1)
  have h1 : Measurable fun x : Mem ℝ × Mem ℝ => storedMatrix a (n + 1) (n + 1) x.1.store :=
    hm.comp measurable_fst
  have h2 : Measurable fun x : Mem ℝ × Mem ℝ => storedMatrix a (n + 1) (n + 1) x.2.store :=
    hm.comp measurable_snd
  have hV : Measurable fun x : Mem ℝ × Mem ℝ =>
      givensLog (n + 1) (slotEntries w ((slottedLogRead lg ns w x.2.store).drop j0)) :=
    (measurable_givensLog_slottedLogRead_drop lg ns w (n + 1) j0).comp measurable_snd
  have hent (i j : Fin (n + 1)) : Measurable fun x : Mem ℝ × Mem ℝ =>
      storedMatrix a (n + 1) (n + 1) x.2.store i j := (Matrix.measurable_apply i j).comp h2
  have hpot : Measurable fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => hessenbergPotential k A :=
    (Finset.measurable_prod _ fun i _ =>
      ((Matrix.measurable_apply i.succ i.castSucc).norm)).pow_const _
  simp only [Set.ofPred_and, Set.ofPred_or]
  refine (Mem.measurableSet_eqOff F).inter ((measurable_snd (measurableSet_forall_isSome a _)).inter
    (((isClosed_setOf_isPerturbedUnitarySimilarBy ε).measurableSet.preimage
      (hV.prodMk (h1.prodMk h2))).inter
      ((?_ : MeasurableSet _).inter ((?_ : MeasurableSet _).union
        (measurableSet_le (hpot.comp h2) ((hpot.comp h1).const_mul c))))))
  · simp only [IsUpperHessenberg, Set.ofPred_forall]
    refine .iInter fun i => .iInter fun j => ?_
    by_cases hij : (j : ℕ) + 1 < i
    · simpa [hij] using measurableSet_eq_fun (hent i j) measurable_const
    · simp [hij]
  · simp only [Set.ofPred_exists, Set.ofPred_and]
    exact .iUnion fun i => (MeasurableSet.const _).inter
      (measurableSet_le (((hent _ _).norm.pow_const 2).const_mul _) measurable_const)

/-- The outcomes of an iteration form a measurable set: the pairs of a memory before and
after with the frame `F`, an initialised matrix at `a` after, and the matrix read after an upper
Hessenberg perturbed unitary similarity with error $\varepsilon$ of the matrix read before that is
decoupled at the bottom (a bottom subdiagonal entry with $(1 - \boldsymbol{u})^2\lvert h\rvert^2
\le t$) or whose potential $\psi_k$ is at most $c$ times that of the matrix before. -/
theorem measurableSet_iterationOutcome (u : ℝ) (k : ℕ) (c tv ε : ℝ) (a : ℕ × ℕ) (F : Fp) :
    MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (x.2.store.get a.1 (a.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilar (storedMatrix a (n + 1) (n + 1) x.1.store)
        (storedMatrix a (n + 1) (n + 1) x.2.store) ε ∧
      IsUpperHessenberg (storedMatrix a (n + 1) (n + 1) x.2.store) ∧
      ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧
          (1 - u) ^ 2 * ‖storedMatrix a (n + 1) (n + 1) x.2.store i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
        hessenbergPotential k (storedMatrix a (n + 1) (n + 1) x.2.store) ≤
          c * hessenbergPotential k (storedMatrix a (n + 1) (n + 1) x.1.store))} := by
  have hm := measurable_storedMatrix a (n + 1) (n + 1)
  have h1 : Measurable fun x : Mem ℝ × Mem ℝ => storedMatrix a (n + 1) (n + 1) x.1.store :=
    hm.comp measurable_fst
  have h2 : Measurable fun x : Mem ℝ × Mem ℝ => storedMatrix a (n + 1) (n + 1) x.2.store :=
    hm.comp measurable_snd
  have hent (i j : Fin (n + 1)) : Measurable fun x : Mem ℝ × Mem ℝ =>
      storedMatrix a (n + 1) (n + 1) x.2.store i j := (Matrix.measurable_apply i j).comp h2
  have hpot : Measurable fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => hessenbergPotential k A :=
    (Finset.measurable_prod _ fun i _ =>
      ((Matrix.measurable_apply i.succ i.castSucc).norm)).pow_const _
  simp only [Set.ofPred_and, Set.ofPred_or]
  refine (Mem.measurableSet_eqOff F).inter ((measurable_snd (measurableSet_forall_isSome a _)).inter
    (((isClosed_setOf_isPerturbedUnitarySimilar ε).measurableSet.preimage (h1.prodMk h2)).inter
      ((?_ : MeasurableSet _).inter ((?_ : MeasurableSet _).union
        (measurableSet_le (hpot.comp h2) ((hpot.comp h1).const_mul c))))))
  · simp only [IsUpperHessenberg, Set.ofPred_forall]
    refine .iInter fun i => .iInter fun j => ?_
    by_cases hij : (j : ℕ) + 1 < i
    · simpa [hij] using measurableSet_eq_fun (hent i j) measurable_const
    · simp [hij]
  · simp only [Set.ofPred_exists, Set.ofPred_and]
    exact .iUnion fun i => (MeasurableSet.const _).inter
      (measurableSet_le (((hent _ _).norm.pow_const 2).const_mul _) measurable_const)

/-- The outcome of an iteration read back from its measurable form
(`NLAlib.ShiftedQR.measurableSet_iterationOutcome`) at a memory holding $\mathbf{H}$. -/
theorem shIterationOutcome_of_mem {u : ℝ} {k : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {γ tv ε : ℝ} {a : ℕ × ℕ} {F : Fp} {m m' : Mem ℝ} (hH : HoldsMatrix a H m.store)
    (h : m.store.EqOff F m'.store ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (m'.store.get a.1 (a.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilar (storedMatrix a (n + 1) (n + 1) m.store)
        (storedMatrix a (n + 1) (n + 1) m'.store) ε ∧
      IsUpperHessenberg (storedMatrix a (n + 1) (n + 1) m'.store) ∧
      ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧
          (1 - u) ^ 2 * ‖storedMatrix a (n + 1) (n + 1) m'.store i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
        hessenbergPotential k (storedMatrix a (n + 1) (n + 1) m'.store) ≤
          1.002 * (1 - γ) * hessenbergPotential k (storedMatrix a (n + 1) (n + 1) m.store))) :
    m.store.EqOff F m'.store ∧ ShIterationOutcome u k H γ tv ε a m' := by
  obtain ⟨hfr, hinit, hsim, hHess, hdec⟩ := h
  rw [← hH.eq_storedMatrix] at hsim hdec
  exact ⟨hfr, _, hsim, hHess, holdsMatrix_storedMatrix hinit, hdec⟩

/-- An outcome of `Sh` is in the measurable form of the outcome of an iteration
(`NLAlib.ShiftedQR.measurableSet_iterationOutcome`). -/
theorem mem_iterationOutcome_of_shOutcome {u : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {γ tv ε : ℝ} {a f lg : ℕ × ℕ} {ns w c : ℕ}
    {LL : List (Option (List GivensEntry))} {F : Fp}
    {m m' : Mem ℝ} (hH : HoldsMatrix a H m.store) (hfr : m.store.EqOff F m'.store)
    (h : ShOutcome u k H γ tv ε a f lg ns w LL c m') :
    m.store.EqOff F m'.store ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (m'.store.get a.1 (a.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilar (storedMatrix a (n + 1) (n + 1) m.store)
        (storedMatrix a (n + 1) (n + 1) m'.store) ε ∧
      IsUpperHessenberg (storedMatrix a (n + 1) (n + 1) m'.store) ∧
      ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧
          (1 - u) ^ 2 * ‖storedMatrix a (n + 1) (n + 1) m'.store i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
        hessenbergPotential k (storedMatrix a (n + 1) (n + 1) m'.store) ≤
          1.002 * (1 - γ) * hessenbergPotential k (storedMatrix a (n + 1) (n + 1) m.store)) := by
  obtain ⟨-, Ls, -, -, -, H', hsim, hHess, hA, hdec⟩ := h
  rw [← hH.eq_storedMatrix, ← hA.eq_storedMatrix]
  exact ⟨hfr, fun j hj => by rw [Store.get_of_readBlock hA hj 0]; rfl,
    hsim.isPerturbedUnitarySimilar, hHess, hdec⟩

/-- An outcome of `Sh` after the slots `LL` is in the measurable form of the outcome of an
iteration by the recorded unitary (`NLAlib.ShiftedQR.measurableSet_iterationOutcomeBy` with
`j0 = LL.length`). -/
private theorem mem_iterationOutcomeBy_of_shOutcome {u : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {γ tv ε : ℝ} {a f lg : ℕ × ℕ} {ns w c : ℕ}
    {LL : List (Option (List GivensEntry))} {F : Fp}
    {m m' : Mem ℝ} (hH : HoldsMatrix a H m.store) (hfr : m.store.EqOff F m'.store)
    (h : ShOutcome u k H γ tv ε a f lg ns w LL c m') :
    m.store.EqOff F m'.store ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (m'.store.get a.1 (a.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilarBy
        (givensLog (n + 1) (slotEntries w ((slottedLogRead lg ns w m'.store).drop LL.length)))
        (storedMatrix a (n + 1) (n + 1) m.store) (storedMatrix a (n + 1) (n + 1) m'.store) ε ∧
      IsUpperHessenberg (storedMatrix a (n + 1) (n + 1) m'.store) ∧
      ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧
          (1 - u) ^ 2 * ‖storedMatrix a (n + 1) (n + 1) m'.store i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
        hessenbergPotential k (storedMatrix a (n + 1) (n + 1) m'.store) ≤
          1.002 * (1 - γ) * hessenbergPotential k (storedMatrix a (n + 1) (n + 1) m.store)) := by
  obtain ⟨-, Ls, -, -, hlog, H', hsim, hHess, hA, hdec⟩ := h
  rw [← hH.eq_storedMatrix, ← hA.eq_storedMatrix, hlog.slotEntries_read_drop]
  exact ⟨hfr, fun j hj => by rw [Store.get_of_readBlock hA hj 0]; rfl, hsim, hHess, hdec⟩

/-- An outcome by the unitary read back after the slots `LL`, with `c` slots closed after them,
is an outcome by the unitary of those slots. -/
private theorem shIterationOutcomeBy_of_read {u : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {γ tv ε : ℝ} {a lg : ℕ × ℕ} {ns w c : ℕ}
    {LL : List (Option (List GivensEntry))} {m' : Mem ℝ}
    (h : ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsPerturbedUnitarySimilarBy
        (givensLog (n + 1) (slotEntries w ((slottedLogRead lg ns w m'.store).drop LL.length)))
        H H' ε ∧ IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
      ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
        hessenbergPotential k H' ≤ 1.002 * (1 - γ) * hessenbergPotential k H))
    (hl : ∃ Ls : List (Option (List GivensEntry)), Ls.length = c ∧
      (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) :
    ShIterationOutcomeBy u k H γ tv ε a lg ns w LL c m' := by
  obtain ⟨H', hsim, hHess, hA, hdec⟩ := h
  obtain ⟨Ls, hLs, hpl, hlog⟩ := hl
  rw [hlog.slotEntries_read_drop] at hsim
  exact ⟨Ls, hLs, hpl, hlog, H', hsim, hHess, hA, hdec⟩

/-- An outcome of an iteration after `c'` rejected slots is an outcome with those slots. -/
private theorem ShIterationOutcomeBy.of_append_replicate_none {u : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {γ tv ε : ℝ} {a lg : ℕ × ℕ} {ns w c c' : ℕ}
    {LL : List (Option (List GivensEntry))} {m' : Mem ℝ}
    (h : ShIterationOutcomeBy u k H γ tv ε a lg ns w (LL ++ List.replicate c' none) c m') :
    ShIterationOutcomeBy u k H γ tv ε a lg ns w LL (c' + c) m' := by
  obtain ⟨Ls, hLs, hpl, hlog, H', hsim, hHess, hA, hdec⟩ := h
  exact ⟨List.replicate c' none ++ Ls, by simp [hLs], by simpa using hpl, by simpa using hlog, H',
    by simpa using hsim, hHess, hA, hdec⟩

section Assembly

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]

/-- `Sh` from the shifts of `Regularize`: on a scalar machine with the standard model at
$\boldsymbol{u} \le 1$, exact comparisons, index literals, index conversion and exact natural
literals up to $n + 1$, a measurable tape-local interpretation and an exact polar disk sampler on
a stream `s₀` uniform on $[0, 1]$, let $\mathbf{H}$ be upper Hessenberg of order $n + 1$,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with $\mathbf{V}$ invertible
and $\kappa(\mathbf{V}) \le B$, $\|\mathbf{H}\|_2 \le \Sigma$, $2 \le k = 2^q \le n$,
$0 < \omega \le \psi_k(\mathbf{H})$, $\theta \ge 1$, $d > 0$, $\alpha = (1.01B)^{4q/2^q}$,
$0 < \gamma < 1$,
$\varepsilon = (0.998(1 - \gamma)^2/((13B^4)^{1/k}\alpha^2\theta^2))^{k/(k-1)} \le 1/2$,
$0 < \varphi \le 1/5$, $\rho = \theta\alpha B^{1/k}$,
$d \le \varepsilon \cdot 1.998^{1/k}\rho\omega\sqrt{\varphi/(11(n + 1))}/4$,
$1.1 + 2.1 \cdot 2.002^{1/k}\rho \le C$, a threshold word $t \ge (1 + \boldsymbol{u})^2\omega^2$,
and the precision conditions $(n + 1)\boldsymbol{u} \le 1/2500$, $10^5k\boldsymbol{u} \le 1$,
$x = 300(n + 1)^2\boldsymbol{u} \le (8004B)^{-1}(d/((2 + 2C)\Sigma))^k$,
$(66 + 2C)B\Sigma((2 + 2C)\Sigma/d)^k\sqrt{n + 1}\,x \le 0.001\omega$, and
$6\boldsymbol{u}(1.1\Sigma + 3 \cdot 2.002^{1/k}\rho\Sigma)$ at most
$0.005\varepsilon \cdot 1.998^{1/k}\rho\omega$ and at most
$\varepsilon \cdot 1.998^{1/k}\rho\omega\sqrt{\varphi/(11(n + 1))}/8$. From a memory holding
$\mathbf{H}$ at `a`, the words of `Sh` ($(1 - \gamma)^k$, $2^{1/k}\rho$, $\varepsilon/2$,
$1.0015(1 - \gamma)$, the net `NLAlib.ShiftedQR.excNet ε`, $t$), room for the flag, the matrix
and the flag apart from each other and from the inputs, and at `s` any $k$ shifts that are
$\theta$-optimal, at distance at least $d$ from every $e_i$ and in
$\mathbb{D}(0, 1.1\|\mathbf{H}\|_2)$, `NLAlib.ShiftedQR.shStep` writes only the matrix and the
flag and ends in `NLAlib.ShiftedQR.ShIterationOutcome` with the error
$(1 + C)\|\mathbf{H}\|_2((1 + x)^k - 1)$ except with probability at most $\varphi$. One good set
serves all shifts: the outcome is measurable
(`NLAlib.ShiftedQR.measurableSet_iterationOutcome`).
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem shStep_pwrites_of_forall {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k q : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    (hkn : k ≤ n) {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ}
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔
        Store.inBlock ww.1 ww.2 1 ⊔ Store.inBlock wp.1 wp.2 1 ⊔
        Store.inBlock g.1 g.2 (2 * (excNet ε).length) ⊔ Store.inBlock thr.1 thr.2 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω θ α γ φ C d tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hSH : specNorm H ≤ S) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H) (hθ : 1 ≤ θ)
    (hd' : 0 < d) (hα : α = (1.01 * B) ^ ((4 * q : ℝ) / 2 ^ q)) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^
      ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ) (hφ1 : φ ≤ 1 / 5)
    (hd : d ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * ω) *
      √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4)
    (hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹)) ≤ C)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hku : 100000 * k * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hexc1 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * S)) ≤
      0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * ω))
    (hexc2 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * S)) ≤
      ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * ω) *
        √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
        (hj : LL.length + (excNet ε).length < ns) (hw : k * n ≤ w)
    (hlgv : ∀ b ∈ [a, s, wg, wr, ww, wp, g, thr, f], b.1 ≠ lg.1) :
    PWrites law I (shStep (O := O) (Q := Q))
      (Env.frame [n + 1, q, k, (excNet ε).length, w, LL.length]
          [a, s, wg, wr, ww, wp, g, thr, a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => m.Live [a, s, wg, wr, ww, wp, g, thr, f] ∧ HoldsMatrix a H m.store ∧
        m.store.get wg.1 wg.2 = some ((1 - γ) ^ k) ∧
        m.store.get wr.1 wr.2 = some ((2 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹))) ∧
        m.store.get ww.1 ww.2 = some (ε / 2) ∧ m.store.get wp.1 wp.2 = some (1.0015 * (1 - γ)) ∧
        m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧
        m.store.get thr.1 thr.2 = some tv ∧ f.2 < m.store.len f.1 ∧ ∃ zs : Fin k → ℂ,
          m.store.readBlock s.1 s.2 (2 * k) =
            some ((List.ofFn zs).flatMap fun z => [z.re, z.im]) ∧
          IsOptimalRitzValues θ H (List.ofFn zs) ∧ (∀ j i, d ≤ ‖e i - zs j‖) ∧
          (∀ j, ‖zs j‖ ≤ 1.1 * specNorm H) ∧
        HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg])
      (ShIterationOutcomeBy u k H γ tv
          ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))
        a lg ns w LL (1 + (excNet ε).length)) φ := by
  have hu0 := hM.roundoff_nonneg
  have hk0 : 0 < k := by omega
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hψS : hessenbergPotential k H ≤ S := (hessenbergPotential_le_specNorm hk0 hkn H).trans hSH
  have hα0 : 0 ≤ α := hα ▸ Real.rpow_nonneg (by positivity) _
  have hε0 : 0 ≤ ε := hε ▸ Real.rpow_nonneg (div_nonneg (by nlinarith) (by positivity)) _
  set c₁ := (1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) with hc₁
  set c₂ := (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hL1 : 6 * u * (1.1 * S + 3 * (c₂ * hessenbergPotential k H)) ≤
      6 * u * (1.1 * S + 3 * (c₂ * S)) := by gcongr
  have hR1 : c₁ * ω ≤ c₁ * hessenbergPotential k H := by gcongr
  have hdψ : d ≤ ε * (c₁ * hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4 :=
    hd.trans (by gcongr)
  have he1 : 6 * u * (1.1 * S + 3 * (c₂ * hessenbergPotential k H)) ≤
      0.005 * ε * (c₁ * hessenbergPotential k H) := hL1.trans (hexc1.trans (by gcongr))
  have he2 : 6 * u * (1.1 * S + 3 * (c₂ * hessenbergPotential k H)) ≤
      ε * (c₁ * hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8 :=
    hL1.trans (hexc2.trans (by gcongr))
  have hst := PWrites.pstep_of_forall hI hloc
    (ι := {zs : Fin k → ℂ // IsOptimalRitzValues θ H (List.ofFn zs) ∧
      (∀ s ∈ List.ofFn zs, ∀ i, d ≤ ‖e i - s‖) ∧ ∀ s ∈ List.ofFn zs, ‖s‖ ≤ 1.1 * specNorm H})
    (fun zs => shStep_pwrites (ss := List.ofFn zs.1) (e := e) hI hloc hS hM hu1 hL hNat hC hQ hD
      hU hkq hk hkn haf hio hH hV hHV hκ hSH hω hψ (List.length_ofFn) zs.2.1 hθ hd' zs.2.2.1
      zs.2.2.2 hα hγ hγ1 hε hε2 hφ hφ1 hdψ hC1 hnu hku hxu hbound he1 he2 hthrω hj hw hlgv)
    ((measurableSet_iterationOutcomeBy (n := n) u k (1.002 * (1 - γ)) tv
      ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a lg ns w LL.length
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))).inter (measurable_snd
          (measurableSet_exists_holdsSlottedLog_append lg ns w (n + 1) (1 + (excNet ε).length)
            LL)))
    (fun _ _ _ hP hfr hO => ⟨mem_iterationOutcomeBy_of_shOutcome hP.2.1 hfr hO, by
      obtain ⟨-, Ls, hLs, hpl, hlog, -⟩ := hO
      exact ⟨Ls, hLs, hpl, hlog⟩⟩)
  refine PStep.mono hst ?_ (fun m m' hm hT => ⟨hT.1.1, shIterationOutcomeBy_of_read
    ⟨storedMatrix a (n + 1) (n + 1) m'.store,
      by have h := hT.1.2.2.1; rw [← hm.2.1.eq_storedMatrix] at h; exact h,
      hT.1.2.2.2.1, holdsMatrix_storedMatrix hT.1.2.1,
      by have h := hT.1.2.2.2.2; rw [← hm.2.1.eq_storedMatrix] at h; exact h⟩ hT.2⟩) le_rfl
  rintro m ⟨hl, hA, hwg, hwr, hww, hwp, hg, ht, hf, zs, hzs, hopt, hdist, hsH, hlog, hlg⟩
  refine ⟨⟨zs, hopt, fun s hs i => ?_, fun s hs => ?_⟩, hl, hA, hzs, hwg, hwr, hww, hwp, hg,
    ht, hf, hlog, hlg⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
    exact hdist j i
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
    exact hsH j

variable [Has EigenvalueKernelOp O]

-- The hypothesis lists of `Regularize` and the kept words of `Sh` make elaboration heavy.
set_option maxHeartbeats 1000000 in
-- (the reason is stated above)
omit [Has IdxTst Q] [Has EigenvalueKernelOp O] in
/-- `Regularize` with a small-eigenvalue routine inside an iteration: the outcome of
`NLAlib.ShiftedQR.regularizeWith_pwrites_at`, with the words of `Sh` kept.
A step in the proof of `shIterationWithScratchWith_pwrites`. -/
theorem shIteration_regularize_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {law : ℕ → Measure ℝ} {s₀ : ℕ}
    {β φse : ℝ} (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse)
    (hD : IsPolarDiskSampler s₀ I) (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {ε : ℝ} {ρ : Env} {a rd c thr wg wr ww wp g s f : ℕ × ℕ}
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hsf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1 ⊔
          Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
          Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length)))
    {nq T : ℕ} {qs : List ℝ} {SE : Stmt O Q} {qw : ℕ × ℕ}
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock qw.1 qw.2 qs.length))
    {ds : List IExp} {args : List Operand} {ns w : ℕ} {lg : ℕ × ℕ}
        {LL : List (Option (List GivensEntry))}
    (hρ : IExp.evalList ρ.idx ds = some [n + 1, k, nq, T, w, LL.length])
    (hρa : Operand.evalList ρ args = some [a, rd, c, thr, qw, a, s, f, lg])
    (hj : LL.length + k ≤ ns) (hw : k * n ≤ w)
    (hlgv : ∀ b ∈ [a, rd, c, thr, wg, wr, ww, wp, g, qw, s, f], b.1 ≠ lg.1)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω R φ tv cg cr cw cp : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hR : 0 < R) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φ / (2 * k))) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (16 * B)⁻¹ * (R * √(φ / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (R * √(φ / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    (hSE : RandomSmallEigContractAt law β φse k nq T S qs SE I) :
    PWrites law I (.frame ds args (regularizeWith SE)) ρ
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg] ∧
          m.Live [a, rd, c, thr, wg, wr, ww, wp, g, qw, s, f] ∧ HoldsMatrix a H m.store ∧
        m.store.readBlock qw.1 qw.2 qs.length = some qs ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ m.store.get wg.1 wg.2 = some cg ∧
        m.store.get wr.1 wr.2 = some cr ∧ m.store.get ww.1 ww.2 = some cw ∧
        m.store.get wp.1 wp.2 = some cp ∧
        m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧
        s.2 + 2 * k ≤ m.store.len s.1 ∧ f.2 < m.store.len f.1)
      (fun m' => RegularizeOutcome k H e u (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) *
          (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) (R * √(φ / (2 * k)) / 2) tv
          ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f lg ns w LL m' ∧
        m'.Live [lg] ∧
        m'.Live [a, rd, c, thr, wg, wr, ww, wp, g, s, f] ∧
        m'.store.get thr.1 thr.2 = some tv ∧ m'.store.get wg.1 wg.2 = some cg ∧
        m'.store.get wr.1 wr.2 = some cr ∧ m'.store.get ww.1 ww.2 = some cw ∧
        m'.store.get wp.1 wp.2 = some cp ∧
        m'.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧ f.2 < m'.store.len f.1)
      (φse + φ / 2) := by
  have hio' : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1) :=
    hio.mono le_rfl (by fp_sub)
  have hlgv' := hlgv
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlgv'
  obtain ⟨hga, hgrd, hgc, hgt, hgwg, hgwr, hgww, hgwp, hgg, hgq, hgs, hgf⟩ := hlgv'
  have hLG : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1 ⊔
        Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
        Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length)) := by
    disjoint
  refine ((regularizeWith_pwrites_at hI hloc hS hM hu1 hL hNat hC hβ0 hφse hD hU hk0 hk has haf
    hsf hio' hH hV hHV hκ hBk hω hψ hSH hgap hR hφ hφ1 hβ hdη hnu huo huo1 hxu hbound
    hthrω hSE hqw hj hw (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hga, hgrd, hgc, hgt, hgq, hgs, hgf⟩)).in_frame hρ hρa ?_).mono_eqOff ?_ ?_
  · rintro m ⟨hl, -, -, -, -, -, -, -, -, hlg⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl hlg ⊢
    tauto
  · rintro m ⟨hlog, hlg, hl, hA, hq, hrd, hc, ht, -, -, -, -, -, hs, hf⟩
    exact ⟨hl.mono (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto),
      hA, hq, hrd, hc, ht, hs, hf, hlog, hlg⟩
  · rintro m m' ⟨-, hlg, hl, -, -, -, -, ht, hwg, hwr, hww, hwp, hg, -, hf⟩ hfr hout
    have hD' : ∀ {G : Fp}, G ≤ Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔
        Store.inBlock thr.1 thr.2 1 ⊔ Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔
        Store.inBlock ww.1 ww.2 1 ⊔ Store.inBlock wp.1 wp.2 1 ⊔
        Store.inBlock g.1 g.2 (2 * (excNet ε).length) → Fp.Disj _ G :=
      fun hG => (Fp.disj_sup_left.mpr ⟨hio, hLG⟩).mono le_rfl hG
    exact ⟨hout, hlg.congr hfr.length_eq, (hl.congr hfr.length_eq).mono (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto),
      hfr.keep (Store.readsOnly_get _ _ _) (hD' (by fp_sub)) ht,
      hfr.keep (Store.readsOnly_get _ _ _) (hD' (by fp_sub)) hwg,
      hfr.keep (Store.readsOnly_get _ _ _) (hD' (by fp_sub)) hwr,
      hfr.keep (Store.readsOnly_get _ _ _) (hD' (by fp_sub)) hww,
      hfr.keep (Store.readsOnly_get _ _ _) (hD' (by fp_sub)) hwp,
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hD' (by fp_sub)) hg,
      by rw [hfr.len_eq]; exact hf⟩

/-- The optimality parameter of `Regularize`,
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, is at least $1$ for $B \ge 1$. -/
theorem one_le_regularizeTheta {B : ℝ} (hB : 1 ≤ B) (k : ℕ) :
    1 ≤ 1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) := by
  have h1 : 1 ≤ (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by norm_num) (by norm_num)
      (neg_nonpos.mpr (by positivity))
  have h2 : 1 ≤ (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) :=
    Real.one_le_rpow (by nlinarith [one_le_pow₀ (n := 4) hB]) (by positivity)
  nlinarith

-- The hypothesis lists of `Regularize` and `Sh` together, with their long real constants, make
-- the elaboration of the composition heavy.
set_option maxHeartbeats 1000000 in
-- (the reason is stated above)
omit [Has EigenvalueKernelOp O] in
/-- One iteration with caller-owned scratch as a probabilistic block: the hypotheses of
`NLAlib.ShiftedQR.shIteration_pwrites`, with the $k$ shift pairs at `s` apart from the other
views.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem shIterationWithScratchWith_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ}
    (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse) (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k q : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    (hkn : k ≤ n) {ε : ℝ} {a rd c thr wg wr ww wp g s f : ℕ × ℕ}
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hsf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
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
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
        (hj : LL.length + (k + 1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ w)
    (hlgv : ∀ b ∈ [a, rd, c, thr, wg, wr, ww, wp, g, qw, s, f], b.1 ≠ lg.1) :
    PWrites law I (shIterationWithScratchWith SE)
      (Env.frame [n + 1, q, k, (excNet ε).length, nq, T, w, LL.length]
        [a, rd, c, thr, wg, wr, ww, wp, g, qw, s, a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => m.Live [a, rd, c, thr, wg, wr, ww, wp, g, qw, s, f] ∧ HoldsMatrix a H m.store ∧
        m.store.readBlock qw.1 qw.2 qs.length = some qs ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ m.store.get wg.1 wg.2 = some ((1 - γ) ^ k) ∧
        m.store.get wr.1 wr.2 = some ((2 : ℝ) ^ ((k : ℝ)⁻¹) *
          ((1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
            B ^ ((k : ℝ)⁻¹))) ∧
        m.store.get ww.1 ww.2 = some (ε / 2) ∧ m.store.get wp.1 wp.2 = some (1.0015 * (1 - γ)) ∧
        m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧
        s.2 + 2 * k ≤ m.store.len s.1 ∧ f.2 < m.store.len f.1 ∧
        HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg])
      (ShIterationOutcomeBy u k H γ tv
          ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))
        a lg ns w LL (k + 1 + (excNet ε).length)) (φse + φR / 2 + φ) := by
  have hu0 := hM.roundoff_nonneg
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hθ := one_le_regularizeTheta hB1 k
  have hd' : 0 < R * √(φR / (2 * k)) / 2 := by
    have : 0 < φR / (2 * k) := by have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
                                  positivity
    positivity
  have hku : 100000 * k * u ≤ 1 := by
    refine le_trans ?_ huo1
    have : (k : ℝ) ≤ ((n + 1 + k : ℕ) : ℝ) ^ 2 := by
      have : k ≤ (n + 1 + k) ^ 2 := by nlinarith
      exact_mod_cast this
    nlinarith
  have hioS : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔
        Store.inBlock ww.1 ww.2 1 ⊔ Store.inBlock wp.1 wp.2 1 ⊔
        Store.inBlock g.1 g.2 (2 * (excNet ε).length) ⊔ Store.inBlock thr.1 thr.2 1) := by
    have hfs := hsf.symm
    simp only [Fp.disj_sup_left, Fp.disj_sup_right] at hio ⊢
    tauto
  have hCε : (1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1) ≤
      (1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1) := by
    have hα0 : 0 ≤ α := hα ▸ Real.rpow_nonneg (by positivity) _
    have hC11 : (1.1 : ℝ) ≤ C := le_trans (le_add_of_nonneg_right (by positivity)) hC1
    have hx : 0 ≤ (1 + 300 * (n + 1) ^ 2 * u) ^ k - 1 :=
      sub_nonneg.mpr (one_le_pow₀ (le_add_of_nonneg_right (by positivity)))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith)
      (specNorm_nonneg H)) hx
  have hw0 : 0 < w := lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) hw
  have hsh := shStep_pwrites_of_forall (f := f) (a := a) (s := s) (wg := wg) (wr := wr)
    (ww := ww) (wp := wp) (g := g) (thr := thr) (LL := LL ++ List.replicate k none) (ns := ns)
    (w := w) (lg := lg) hI hloc hS hM
    hu1 hL hNat hC hQ hD hU hkq hk hkn haf hioS hH hV hHV hκ hSH hω hψ hθ hd' hα hγ hγ1 hε hε2 hφ
    hφ1 hd hC1 hnu hku hxu hbound hexc1 hexc2 hthrω
    (by rw [List.length_append, List.length_replicate]; omega) hw
    (fun b hb => hlgv b (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢; tauto))
  unfold shIterationWithScratchWith
  refine (PWrites.seq hI hloc (le_max_right φ 0)
    (shIteration_regularize_pwrites (ρ := Env.frame [n + 1, q, k, (excNet ε).length, nq, T, w,
      LL.length] [a, rd, c, thr, wg, wr, ww, wp, g, qw, s, a, f, lg]) (ns := ns) (w := w)
      (lg := lg) (LL := LL) hI hloc hS hM hu1 hL hNat hC
      hβ0 hφse hD hU (by omega) hkn has haf hsf hio hqw ?_ ?_ (by omega) hw hlgv hH hV hHV hκ hBk
      hω hψ hSH hgap hR hφR hφR1 hβ hdη hnu huo huo1 hxuR hboundR hthrω hSE)
    (PWrites.ite hI ?_ ((hsh.in_frame ?_ ?_ ?_).mono ?_ le_rfl ?_ le_rfl)
      (PWrites.of_writes le_rfl ?_))).mono
      (fun _ ⟨hl, hA, hq, hrd, hc, ht, hwg, hwr, hww, hwp, hg, hs, hf, hlog, hlg⟩ =>
        ⟨hlog, hlg, hl, hA, hq, hrd, hc, ht, hwg, hwr, hww, hwp, hg, hs, hf⟩) (by fp_sub)
      (fun _ h => h) (by rw [max_eq_left hφ.le])
  · rfl
  · rfl
  · rintro m ⟨⟨Ls, -, -, -, ⟨hF, -⟩ | ⟨hF, -⟩⟩, -⟩ <;>
      exact ⟨_, by rw [Interp.testAt_eq rfl rfl, hC.test_isZero hF]⟩
  · rw [List.length_append, List.length_replicate]
    rfl
  · rfl
  · rintro m ⟨hl, -, -, -, -, -, -, -, -, zs, -, -, -, -, -, hlg⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl hlg ⊢
    tauto
  · rintro m ⟨⟨⟨Ls, hLs, -, hlog, ⟨hF, hA, hnil, zs, hzs, hopt, hdist, hsH⟩ | ⟨hF, -⟩⟩, hlg, hl,
      ht, hwg, hwr, hww, hwp, hg, hf⟩, htest⟩
    · rw [eq_replicate_none_of_slotEntries_eq_nil hw0 hnil, hLs] at hlog
      exact ⟨hl.mono (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                         tauto), hA, hwg, hwr, hww, hwp, hg, ht, hf, zs, hzs, hopt, hdist, hsH,
        hlog, hlg⟩
    · rw [Interp.testAt_eq rfl rfl, hC.test_isZero hF] at htest
      norm_num at htest
  · intro m' h
    rw [Nat.add_assoc]
    exact h.of_append_replicate_none
  · rintro m τ ⟨⟨⟨Ls, hLs, hpl, hlog, ⟨hF, -⟩ | ⟨hF, H', hsim, hH', hA, hdec⟩⟩, -⟩, htest⟩
    · rw [Interp.testAt_eq rfl rfl, hC.test_isZero hF] at htest
      norm_num at htest
    · have hlog' := hlog.rejects (c := 1 + (excNet ε).length) (by simp [hLs]; omega)
      exact (Writes.skip ⟨Ls ++ List.replicate (1 + (excNet ε).length) none,
        by simp [hLs]; omega, by simpa using hpl, by simpa using hlog', H',
        by simpa using hsim.mono hCε, hH', hA, Or.inl hdec⟩).mono bot_le fun _ _ h => h

end Assembly
end NLAlib.ShiftedQR
