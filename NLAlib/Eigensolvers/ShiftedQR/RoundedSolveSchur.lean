/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedWorklistTermination
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveSteps
public import NLAlib.Matrix.FinitePrecision.GivensLogSlots
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveCompletion

/-!
# The rounds of the Schur-mode worklist on the good tapes

The pieces of a round of the rounded deflation worklist in Schur mode
(`NLAlib.ShiftedQR.solveRoundedWith`) with randomized routines: the outcomes of the randomized
leaf and decoupler calls are measurable, the replay and leaf errors of a round fit the round
budget, and the value states of a round (`NLAlib.ShiftedQR.SchurReached`,
`NLAlib.ShiftedQR.SchurPopped`) are carried through the leaf, split and large-block steps.

## Main definitions

* `NLAlib.ShiftedQR.SchurReached`, `NLAlib.ShiftedQR.SchurPopped`: the states of a round on the
  good tapes.

## Main results

* `NLAlib.ShiftedQR.measurableSet_schurLeafOutcome`,
  `NLAlib.ShiftedQR.measurableSet_schurDecoupleOutcome`: the outcomes of the randomized calls.
* `NLAlib.ShiftedQR.roundedLeafRest_reached`, `NLAlib.ShiftedQR.roundedSplitUpdate_reached`,
  `NLAlib.ShiftedQR.roundedLargeRest_reached`: the steps of a round keep the state.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops MeasureTheory
open scoped Matrix

variable {O Q : Type}

/-! ### Measurable outcomes of the randomized calls -/

/-- The outcomes of a Schur leaf call that the worklist uses, as pairs of a memory before and
after: the frame `F`, initialised words of the block at `w` and of the leaf accumulator at `ub`,
the block read after upper triangular, and the pair read after tracked from $(\mathbf{I},
\mathbf{B})$, $\mathbf{B}$ the block read before, with errors $(\varepsilon_L, \beta)$. They form
a measurable set. -/
theorem measurableSet_schurLeafOutcome (d : ℕ) (εL β : ℝ) (w ub : ℕ × ℕ) (F : Fp) :
    MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧
      (∀ j < 2 * (d * d), (x.2.store.get w.1 (w.2 + j)).isSome) ∧
      (∀ j < 2 * (d * d), (x.2.store.get ub.1 (ub.2 + j)).isSome) ∧
      (storedMatrix w d d x.2.store).IsUpperTriangular ∧
      IsTrackedUnitarySimilar εL β 1 (storedMatrix w d d x.1.store)
        (storedMatrix ub d d x.2.store) (storedMatrix w d d x.2.store)} := by
  have hm : ∀ b, Measurable fun x : Mem ℝ × Mem ℝ => storedMatrix b d d x.2.store :=
    fun b => (measurable_storedMatrix b d d).comp measurable_snd
  have hut : MeasurableSet {x : Mem ℝ × Mem ℝ |
      (storedMatrix w d d x.2.store).IsUpperTriangular} := by
    have e : {x : Mem ℝ × Mem ℝ | (storedMatrix w d d x.2.store).IsUpperTriangular} =
        ⋂ i, ⋂ j, {x | j < i → storedMatrix w d d x.2.store i j = 0} := by
      ext x
      simp [Matrix.IsUpperTriangular, Matrix.BlockTriangular]
    rw [e]
    exact .iInter fun i => .iInter fun j => (MeasurableSet.const (j < i)).imp
      (measurableSet_eq_fun ((Matrix.measurable_apply i j).comp (hm w)) measurable_const)
  have htr : MeasurableSet {x : Mem ℝ × Mem ℝ | IsTrackedUnitarySimilar εL β 1
      (storedMatrix w d d x.1.store) (storedMatrix ub d d x.2.store)
      (storedMatrix w d d x.2.store)} := by
    have hf : Measurable fun x : Mem ℝ × Mem ℝ =>
        (((1 : Matrix (Fin d) (Fin d) ℂ), storedMatrix w d d x.1.store),
          (storedMatrix ub d d x.2.store, storedMatrix w d d x.2.store)) :=
      (measurable_const.prodMk ((measurable_storedMatrix w d d).comp measurable_fst)).prodMk
        ((hm ub).prodMk (hm w))
    exact hf (isClosed_setOf_isTrackedUnitarySimilar εL β).measurableSet
  exact (Mem.measurableSet_eqOff F).inter ((measurable_snd (measurableSet_forall_isSome w _)).inter
    ((measurable_snd (measurableSet_forall_isSome ub _)).inter (hut.inter htr)))

/-- The outcomes of a decoupling call with a log that the worklist uses, as pairs of a memory
before and after: the frame `F`, the flag $0$, an initialised work matrix, the matrix read after
an upper Hessenberg perturbed unitary similarity with error $\varepsilon$ of the matrix read
before by the unitary of the log read after, a bottom-$k$ subdiagonal entry of modulus at most
$\omega$, and the log after closed with planes below $d$. They form a measurable set. -/
theorem measurableSet_schurDecoupleOutcome (d k : ℕ) (ε ω : ℝ) (w f lg : ℕ × ℕ) (ns ws : ℕ)
    (F : Fp) :
    MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧
      x.2.store.get f.1 f.2 = some 0 ∧
      (∀ j < 2 * ((d + 1) * (d + 1)), (x.2.store.get w.1 (w.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilarBy
        (givensLog (d + 1) (slotEntries ws (slottedLogRead lg ns ws x.2.store)))
        (storedMatrix w (d + 1) (d + 1) x.1.store) (storedMatrix w (d + 1) (d + 1) x.2.store) ε ∧
      IsUpperHessenberg (storedMatrix w (d + 1) (d + 1) x.2.store) ∧
      (∃ i : Fin d, d ≤ (i : ℕ) + k ∧
        ‖storedMatrix w (d + 1) (d + 1) x.2.store i.succ i.castSucc‖ ≤ ω) ∧
      ∃ Ls : List (Option (List GivensEntry)), Ls.length = ns ∧
        (∀ e ∈ slotEntries ws Ls, e.1 + 1 < d + 1) ∧
        HoldsSlottedLog lg ns ws ([] ++ Ls) [] x.2.store} := by
  have hm := measurable_storedMatrix w (d + 1) (d + 1)
  have h2 : Measurable fun x : Mem ℝ × Mem ℝ => storedMatrix w (d + 1) (d + 1) x.2.store :=
    hm.comp measurable_snd
  have hV : Measurable fun x : Mem ℝ × Mem ℝ =>
      givensLog (d + 1) (slotEntries ws (slottedLogRead lg ns ws x.2.store)) :=
    (measurable_givensLog_slottedLogRead lg ns ws (d + 1)).comp measurable_snd
  have hent (i j : Fin (d + 1)) : Measurable fun x : Mem ℝ × Mem ℝ =>
      storedMatrix w (d + 1) (d + 1) x.2.store i j := (Matrix.measurable_apply i j).comp h2
  simp only [Set.ofPred_and]
  refine (Mem.measurableSet_eqOff F).inter ((measurable_snd (Mem.measurableSet_get_eq f 0)).inter
    ((measurable_snd (measurableSet_forall_isSome w _)).inter
      (((isClosed_setOf_isPerturbedUnitarySimilarBy ε).measurableSet.preimage
        (hV.prodMk ((hm.comp measurable_fst).prodMk h2))).inter
        ((?_ : MeasurableSet _).inter ((?_ : MeasurableSet _).inter
          (measurable_snd
            (measurableSet_exists_holdsSlottedLog_append lg ns ws (d + 1) ns [])))))))
  · simp only [IsUpperHessenberg, Set.ofPred_forall]
    refine .iInter fun i => .iInter fun j => ?_
    by_cases hij : (j : ℕ) + 1 < i
    · simpa [hij] using measurableSet_eq_fun (hent i j) measurable_const
    · simp [hij]
  · simp only [Set.ofPred_exists, Set.ofPred_and]
    exact .iUnion fun i => (MeasurableSet.const _).inter
      (measurableSet_le (hent _ _).norm measurable_const)

/-! ### Precision of a round -/

/-- The replay error of a decoupled block within its share of the budget: with
$R \le M$ entries, $0 \le x \le N_0$ and $2(n + 1) \cdot 78\boldsymbol{u}MN_0 \le N_0$,
$((1 + 24\boldsymbol{u})^R - 1)x \le 78\boldsymbol{u}MN_0$. -/
theorem replayError_le {u N₀ x : ℝ} {R M n : ℕ} (hu0 : 0 ≤ u) (hR : R ≤ M) (hx0 : 0 ≤ x)
    (hx : x ≤ N₀) (hroom : 2 * (n + 1) * (78 * u * M * N₀) ≤ N₀) :
    ((1 + 24 * u) ^ R - 1) * x ≤ 78 * u * M * N₀ := by
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  rcases hx0.eq_or_lt with rfl | hxp
  · rw [mul_zero]; positivity
  have hN : 0 < N₀ := hxp.trans_le hx
  have hMu : 156 * ((M : ℝ) * u) ≤ 1 := by
    have h1 : 2 * ((n : ℝ) + 1) * (78 * u * M) ≤ 1 := by
      have := hroom; rw [show 2 * ((n : ℝ) + 1) * (78 * u * M * N₀) =
        (2 * ((n : ℝ) + 1) * (78 * u * M)) * N₀ by ring] at this
      exact (mul_le_iff_le_one_left hN).mp this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg hM0 hu0]
  have hp := one_add_pow_sub_one_le (x := 24 * u) (n := M) (by positivity) (by nlinarith)
  have hRM : (1 + 24 * u) ^ R ≤ (1 + 24 * u) ^ M := pow_le_pow_right₀ hX1 hR
  have hb : (1 + 24 * u) ^ R - 1 ≤ 78 * u * M := by nlinarith [mul_nonneg hM0 hu0]
  have h0 : 0 ≤ (1 + 24 * u) ^ R - 1 := by linarith [one_le_pow₀ (n := R) hX1]
  calc ((1 + 24 * u) ^ R - 1) * x ≤ (78 * u * M) * N₀ :=
        mul_le_mul hb hx hx0 (by positivity)
    _ = 78 * u * M * N₀ := by ring

/-- The leaf error within its share of the budget: with $1 \le d \le k$, $d \le n + 1$,
$0 \le \boldsymbol{u} \le 1/100$, $\varepsilon_L \ge 0$, $0 \le x \le N_0$ and
$2(n + 1) \cdot 8(n + 1)(k + 2)\boldsymbol{u}N_0 \le N_0$, the backward error of
`NLAlib.ShiftedQR.leafUpdate_isTrackedUnitarySimilar` at the norm $x$ is at most
$8(n + 1)(k + 2)\boldsymbol{u}N_0 + 2\varepsilon_L N_0$. -/
theorem leafError_le {u εL N₀ x : ℝ} {d k n : ℕ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hεL : 0 ≤ εL) (hdk : d ≤ k) (hdn : d ≤ n + 1) (hx0 : 0 ≤ x) (hx : x ≤ N₀)
    (hroom : 2 * (n + 1) * (8 * (n + 1) * (k + 2) * u * N₀) ≤ N₀) :
    ((1 + (6 * u + 5 * u ^ 2)) ^ d * (5 * u + d * (6 * u + 5 * u ^ 2)) * d * (1 + εL) + εL) *
      x ≤ 8 * (n + 1) * (k + 2) * u * N₀ + 2 * εL * N₀ := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdk' : (d : ℝ) ≤ k := by exact_mod_cast hdk
  have hdn' : (d : ℝ) ≤ n + 1 := by exact_mod_cast hdn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hN0 : 0 ≤ N₀ := hx0.trans hx
  rcases hx0.eq_or_lt with rfl | hxp
  · rw [mul_zero]; positivity
  have hN : 0 < N₀ := hxp.trans_le hx
  have h16 : 16 * ((n : ℝ) + 1) ^ 2 * (k + 2) * u ≤ 1 := by
    have := hroom
    rw [show 2 * ((n : ℝ) + 1) * (8 * (n + 1) * (k + 2) * u * N₀) =
      (16 * ((n : ℝ) + 1) ^ 2 * (k + 2) * u) * N₀ by ring] at this
    exact (mul_le_iff_le_one_left hN).mp this
  have h32 : 32 * ((d : ℝ) + 1) * u ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : (d : ℝ) ≤ 1 := by simpa using hdn'
      nlinarith
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h4 : (4 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      have hk0 : (0 : ℝ) ≤ (k + 2) * u := by positivity
      have h64 : 64 * ((k : ℝ) + 2) * u ≤ 1 := by
        nlinarith [mul_le_mul_of_nonneg_right h4 hk0]
      nlinarith
  have hg := matMul_growth_le (p := d) hu0 h32
  have h8 : 8 * ((n : ℝ) + 1) * (k + 1) * u ≤ 1 / 2 := by nlinarith
  set g := (1 + (6 * u + 5 * u ^ 2)) ^ d * (5 * u + d * (6 * u + 5 * u ^ 2))
  have hgd : g * d ≤ 8 * ((n : ℝ) + 1) * (k + 1) * u := by
    have := mul_le_mul_of_nonneg_right hg hd0
    have h2 : 8 * ((d : ℝ) + 1) * u * d ≤ 8 * ((n : ℝ) + 1) * (k + 1) * u := by
      have := mul_le_mul hdn' (show (d : ℝ) + 1 ≤ k + 1 by linarith) (by positivity)
        (by positivity)
      nlinarith
    linarith
  have hg0 : 0 ≤ g * d := by positivity
  have hc : g * d * (1 + εL) + εL ≤ 8 * ((n : ℝ) + 1) * (k + 2) * u + 2 * εL := by
    have := mul_le_mul_of_nonneg_right hgd (show (0 : ℝ) ≤ 1 + εL by linarith)
    nlinarith
  calc (g * d * (1 + εL) + εL) * x ≤ (8 * ((n : ℝ) + 1) * (k + 2) * u + 2 * εL) * N₀ :=
        mul_le_mul hc hx hx0 (by positivity)
    _ = _ := by ring

/-! ### The states of the worklist on the good tapes -/

/-- The core of the value state of the worklist in Schur mode before round `j`, for the input
$(\mathbf{U}, \mathbf{H})$, the per-round accumulator factor $(1 + 24\boldsymbol{u})^m$, the
per-leaf factor $1 + \varepsilon_L$ and the per-round backward error $e$: the failure word is
$0$, the stack holds the active ranges, the stored matrix $\mathbf{A}$ has the shape
`NLAlib.ShiftedQR.SchurShape` with the finished ranges, twice the finished plus the active ranges
count $j + 1$, and the stored accumulator and $\mathbf{A}$ are tracked from
$(\mathbf{U}, \mathbf{H})$ with the errors $((1 + 24\boldsymbol{u})^{jm}(1 +
\varepsilon_L)^{\ell} - 1, je)$, $\ell$ the number of finished ranges. -/
def SchurReachedCore (n : ℕ) (H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (u εL e : ℝ)
    (m : ℕ) (a uo f st : ℕ × ℕ) (j : ℕ) (μ : Mem ℝ) : Prop :=
  μ.store.get f.1 f.2 = some 0 ∧ ∃ (rs done : List (ℕ × ℕ))
    (A U' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), StackHolds st rs μ.store ∧
    HoldsMatrix a A μ.store ∧ HoldsMatrix uo U' μ.store ∧ SchurShape n rs done A ∧
    2 * done.length + rs.length = j + 1 ∧
    IsTrackedUnitarySimilar ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ done.length - 1) (j * e)
      U H U' A

/-- The value state of the worklist in Schur mode before round `j`: the geometry, the
threshold and parameter words and the core `NLAlib.ShiftedQR.SchurReachedCore`. -/
def SchurReached (n : ℕ) (H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (u εL e : ℝ) (m : ℕ)
    (thr : ℝ) (ps : List ℝ) (a t p uo f st wk ub r : ℕ × ℕ) (j : ℕ) (μ : Mem ℝ) : Prop :=
  SchurGeometry (n + 1) ps.length a t p uo f st wk ub r μ ∧ μ.store.get t.1 t.2 = some thr ∧
    μ.store.readBlock p.1 p.2 ps.length = some ps ∧ SchurReachedCore n H U u εL e m a uo f st j μ

/-- From the geometry with the threshold and parameter words stored at `μ`, a write inside the
round footprint to `μ'` keeps them, so the core at `μ'` gives the state at `μ'`. -/
theorem SchurReached.of_core {n : ℕ} {H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {u εL e : ℝ}
    {m : ℕ} {thr : ℝ} {ps : List ℝ} {a t p uo f st wk ub r : ℕ × ℕ} {j : ℕ} {μ μ' : Mem ℝ}
    {F : Fp} (h : SchurGeometry (n + 1) ps.length a t p uo f st wk ub r μ)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hfr : μ.store.EqOff F μ'.store) (hF : F ≤ schurRoundFp (n + 1) a uo f st wk ub r)
    (hcore : SchurReachedCore n H U u εL e m a uo f st j μ') :
    SchurReached n H U u εL e m thr ps a t p uo f st wk ub r j μ' := by
  have hd := h.disj_params.mono hF le_rfl
  exact ⟨h.of_eqOff hfr, hfr.keep (Store.readsOnly_get _ _ _) (hd.mono le_rfl le_sup_left) ht,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hd.mono le_rfl le_sup_right) hp, hcore⟩

/-- The value state after the pop of the range $(lo, d)$ in round `j`: the geometry, the
words, the failure word $0$, the stack holding the other active ranges, a matrix $\mathbf{A}$ of
the shape with the popped range last among the active ones, and the tracked pair. With `cp`, the
block of the range is also in the work matrix. -/
def SchurPopped (cp : Bool) (n : ℕ) (H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (u εL e : ℝ)
    (m : ℕ) (thr : ℝ) (ps : List ℝ) (a t p uo f st wk ub r : ℕ × ℕ) (j lo d : ℕ) (μ : Mem ℝ) :
    Prop :=
  SchurGeometry (n + 1) ps.length a t p uo f st wk ub r μ ∧ μ.store.get t.1 t.2 = some thr ∧
    μ.store.readBlock p.1 p.2 ps.length = some ps ∧ μ.store.get f.1 f.2 = some 0 ∧
    ∃ (rs done : List (ℕ × ℕ)) (A U' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      StackHolds st rs μ.store ∧ HoldsMatrix a A μ.store ∧ HoldsMatrix uo U' μ.store ∧
      (cp → HoldsMatrix wk (subBlock A (lo, d)) μ.store) ∧
      SchurShape n (rs ++ [(lo, d)]) done A ∧ 2 * done.length + rs.length = j ∧
      IsTrackedUnitarySimilar ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ done.length - 1) (j * e)
        U H U' A

/-- A decoupled block's round as a tracked step of the worklist: the decoupling update of
`NLAlib.ShiftedQR.decoupleUpdateMatrix_isPerturbedUnitarySimilarBy` with the column replay on the
accumulator advances the tracked pair of round $j < 2(n + 1)$ to round $j + 1$, when the
decoupling error, the replay error and the cut are within the round's budget $e$. -/
theorem decoupleRound_tracked {Mch : Machine ℝ} {u : ℝ} (hM : StdModel u id Mch) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 100) (hz : Mch.lit 0 = 0) {n lo d ns w m j ℓ : ℕ} (hN : lo + (d + 1) ≤ n + 1)
    {A U' H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : IsRangeBlockTriangular lo (d + 1) A)
    {es : List GivensEntry} (hpl : ∀ e ∈ es, e.1 + 1 < d + 1)
    {H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} {εD c εL e N₀ : ℝ}
    (hblk : IsPerturbedUnitarySimilarBy (givensLog (d + 1) es) (subBlock A (lo, d + 1)) H' εD)
    (i : Fin d) (hc : ‖H' i.succ i.castSucc‖ ≤ c) (hm : ns * w ≤ m) (hes : es.length ≤ ns * w)
    (hεL : 0 ≤ εL) (he : εD + 78 * u * (ns * w : ℕ) * N₀ + c ≤ e)
    (hroom : 2 * (n + 1) * (78 * u * (ns * w : ℕ) * N₀) ≤ N₀) (he0 : 0 ≤ e)
    (hN₀ : specNorm H + 2 * (n + 1) * e ≤ N₀) (hj : j < 2 * (n + 1))
    (htr : IsTrackedUnitarySimilar ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ - 1) (j * e) U H U' A) :
    IsTrackedUnitarySimilar ((1 + 24 * u) ^ ((j + 1) * m) * (1 + εL) ^ ℓ - 1) ((j + 1 : ℕ) * e)
      U H (es.foldl (replayColumnStep Mch lo 0 (n + 1)) U')
      (decoupleUpdateMatrix Mch lo (d + 1) i es (setSubBlock A (lo, d + 1) H')) := by
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith
  have hY1 : (1 : ℝ) ≤ 1 + εL := by linarith
  have hnA : specNorm A ≤ N₀ := by
    have := htr.specNorm_le_add
    have : (j : ℝ) * e ≤ 2 * (n + 1) * e :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj.le) he0
    linarith
  have hstep : IsTrackedUnitarySimilar ((1 + 24 * u) ^ es.length - 1)
      (εD + ((1 + 24 * u) ^ es.length - 1) * specNorm A + c) U' A
      (es.foldl (replayColumnStep Mch lo 0 (n + 1)) U')
      (decoupleUpdateMatrix Mch lo (d + 1) i es (setSubBlock A (lo, d + 1) H')) :=
    ⟨_, decoupleUpdateMatrix_isPerturbedUnitarySimilarBy hM hu0 hu hz hN hA hpl hblk i hc,
      specNorm_foldl_replayColumnStep_sub_le hM hu0 hu hN es
        (fun e he => ⟨by have := hpl e he; omega, Or.inl (hpl e he)⟩) U'⟩
  refine IsTrackedUnitarySimilar.round (one_le_pow₀ hX1) htr hstep ?_ ?_
  · rw [add_mul, one_mul, pow_add]
    have h1 : (1 + 24 * u) ^ es.length ≤ (1 + 24 * u) ^ m := pow_le_pow_right₀ hX1 (hes.trans hm)
    have h0 : 0 ≤ (1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ :=
      mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
    nlinarith
  · have := replayError_le hu0 hes (specNorm_nonneg A) hnA hroom
    linarith

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- The part of the leaf branch after the leaf call: write the block back and update the
couplings and the accumulator. -/
def roundedLeafRest : Stmt O Q :=
  (Stmt.frame [IExp.var 0, IExp.var 7, IExp.var 8]
      [{ buf := 5, off := IExp.var 14 }, { buf := 0, off := IExp.var 9 }]
      (copyToGlobal (Op := O) (Tst := Q)).body).seq
    (Stmt.frame [IExp.var 0, IExp.var 7, IExp.var 8]
      [{ buf := 6, off := IExp.var 15 }, { buf := 0, off := IExp.var 9 },
        { buf := 4, off := IExp.var 13 }] (roundedLeafUpdate (O := O) (Q := Q)).body)

omit [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The rest of a leaf round on the good tapes: on a scalar machine with the standard model
at $0 \le \boldsymbol{u} \le 1/100$, from the geometry of the worklist in Schur mode with the
failure word $0$, a matrix $\mathbf{A}$ of the shape with the popped range $(lo, d)$, $d \le k$,
the tracked pair of round $j < 2(n + 1)$, and the leaf's output $(\mathbf{U}_b, \mathbf{T}_b)$
stored, $\mathbf{T}_b$ upper triangular and tracked from $(\mathbf{I}, \mathbf{A}_{lo:lo+d})$ with
$(\varepsilon_L, \beta)$, writing the block back and updating the couplings and the accumulator
reach the core of round $j + 1$, when the leaf error is within the round's budget $e$. -/
theorem roundedLeafRest_reached {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    {n k F T ns w m : ℕ} (hm2 : 2 * k * (k + 2) ≤ m) {ps : List ℝ} {εL β e N₀ : ℝ}
    (hεL : 0 ≤ εL) (he : β + (8 * (n + 1) * (k + 2) * u * N₀ + 2 * εL * N₀) ≤ e)
    (hroom : 2 * (n + 1) * (8 * (n + 1) * (k + 2) * u * N₀) ≤ N₀)
    {H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (he0 : 0 ≤ e)
    (hN₀ : specNorm H + 2 * (n + 1) * e ≤ N₀) {tape : Tape ℝ} {μ : Mem ℝ} {lo d j : ℕ}
    (hj : j < 2 * (n + 1)) (hdk : d ≤ k) {a t p uo f st wk ub r : ℕ × ℕ}
    {rs done : List (ℕ × ℕ)} {A U' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {Ub Tb : Matrix (Fin d) (Fin d) ℂ}
    (hG : SchurGeometry (n + 1) ps.length a t p uo f st wk ub r μ)
    (hf : μ.store.get f.1 f.2 = some 0) (hA : HoldsMatrix a A μ.store)
    (hU' : HoldsMatrix uo U' μ.store) (hTb : HoldsMatrix wk Tb μ.store)
    (hUb : HoldsMatrix ub Ub μ.store) (hSt : StackHolds st rs μ.store)
    (hsh : SchurShape n (rs ++ [(lo, d)]) done A) (hcnt : 2 * done.length + rs.length = j)
    (htr : IsTrackedUnitarySimilar ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ done.length - 1)
      (j * e) U H U' A)
    (hleaf : IsTrackedUnitarySimilar εL β 1 (subBlock A (lo, d)) Ub Tb)
    (hup : Tb.IsUpperTriangular) :
    Writes .total I tape (roundedLeafRest (O := O) (Q := Q))
      (Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d] [a, t, p, st, uo, wk, ub, r, f])
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (SchurReachedCore n H U u εL e m a uo f st (j + 1)) μ := by
  have hmem : (lo, d) ∈ rs ++ [(lo, d)] ++ done := by simp
  have hfit0 := hsh.1.2.1 _ hmem
  simp only at hfit0
  have hd : d ≤ n + 1 := by omega
  have hsq := Nat.mul_le_mul hd hd
  have hWd : Store.inBlock wk.1 wk.2 (2 * (d * d)) ≤
      Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  have hUd : Store.inBlock ub.1 ub.2 (2 * (d * d)) ≤
      Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  have g : ∀ i j : Fin 9, i ≠ j → _ := fun i j h => hG.disj' i j h
  have hAW : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using g 0 6 (by simp)
  have hlWA : μ.Live [wk, a] := hG.live_of_subset (by simp)
  unfold roundedLeafRest
  refine ((copyToGlobal_writes (τ := tape) hS hlWA hA hTb hfit0.2 hG.room.1
    (hAW.symm.mono hWd le_rfl)).in_frame rfl rfl hlWA).seq_le
    ((blockFp_le a hfit0.2).trans (by fp_sub [schurRoundFp])) ?_
  rintro μ₂ hfr₂ ⟨-, hA₂⟩
  have hAX : ∀ i : Fin 9, i ≠ 0 → Fp.Disj ((EntryCodec.pair ℝ).regionFp a.1
      (a.2 + 2 * (lo * (n + 1) + lo)) d (fun i j => j * (n + 1) + i) (fun _ => d))
      (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
    fun i h0 => (g 0 i (Ne.symm h0)).mono (blockFp_le a hfit0.2) le_rfl
  have hUb₂ := hUb.of_eqOff hfr₂ ((hAX 7 (by simp)).mono le_rfl hUd)
  have hU₂ := hU'.of_eqOff hfr₂ (hAX 3 (by simp))
  have hG₂ := hG.of_eqOff hfr₂
  have hlU : μ₂.Live [ub, a, uo] := hG₂.live_of_subset (by simp)
  refine ((roundedLeafUpdate_writes (O := O) (Q := Q) (τ := tape) (M := Mch) hS hfit0.2 hlU hUb₂
    hA₂ hU₂ hG₂.room.1 hG₂.room.2.2.2.1 ((g 7 0 (by simp)).mono hUd le_rfl)
    (by simpa [schurBlock] using g 0 3 (by simp))).in_frame rfl rfl hlU).mono
    (by fp_sub [schurRoundFp]) ?_
  rintro μ₃ hfr₃ ⟨-, hA₃, hU₃⟩
  have hAU3 : ∀ i : Fin 9, i ≠ 0 → i ≠ 3 → Fp.Disj
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))))
      (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
    fun i h0 h3 => Fp.disj_sup_left.mpr ⟨g 0 i (Ne.symm h0), g 3 i (Ne.symm h3)⟩
  have hlen := (hsh.deflationInv (H := A) (V := 1) (ε := 0)
    (by simpa using IsPerturbedUnitarySimilarBy.refl A)).length_le
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  have hst5 : Store.inBlock st.1 st.2 (1 + 2 * rs.length) ≤
      Store.inBlock st.1 st.2 (1 + 2 * (n + 1)) :=
    Fp.inBlock_le_inBlock le_rfl (by omega)
  refine ⟨(hfr₂.trans' hfr₃).keep (Store.readsOnly_get _ _ _)
      (Fp.disj_sup_left.mpr ⟨hAX 4 (by simp), hAU3 4 (by simp) (by simp)⟩) hf, rs,
    (lo, d) :: done, _, _, (hSt.of_eqOff hfr₂ ((hAX 5 (by simp)).mono le_rfl hst5)).of_eqOff hfr₃
      ((hAU3 5 (by simp) (by simp)).mono le_rfl hst5), hA₃, hU₃, hsh.leaf Mch Ub hup,
    by simp; omega, ?_⟩
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith
  have hY1 : (1 : ℝ) ≤ 1 + εL := by linarith
  have hstep := leafUpdate_isTrackedUnitarySimilar hM hu0 (by linarith) hfit0.2
    (hsh.isRangeBlockTriangular hmem) (U := U') hεL hleaf
  have hnA : specNorm A ≤ N₀ := by
    have := htr.specNorm_le_add
    have : (j : ℝ) * e ≤ 2 * (n + 1) * e :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj.le) he0
    linarith
  refine IsTrackedUnitarySimilar.round (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hX1) hY1)
    htr hstep ?_ ?_
  · simpa [List.length_cons] using accumFactor_leaf_le hu0 hεL (j := j) (ℓ := done.length)
      (le_trans (by
        have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hdk) (Nat.add_le_add_right hdk 2)
        linarith) hm2)
  · have := leafError_le hu0 hu hεL hdk hd (specNorm_nonneg A) hnA hroom
    linarith

/-- The split after a decoupled block on the good tapes: on a scalar machine with the
standard model at $0 \le \boldsymbol{u} \le 1/100$, exact natural literals up to $n + 1$ and
exact `toNat` and comparisons, from the geometry with the failure word $0$, a matrix
$\mathbf{A}$ of the shape with the popped range $(lo, d + 1)$, the tracked pair of round
$j < 2(n + 1)$, a closed log at `(lgb, 0)` (a fresh buffer) of `ns` slots whose entries are
inside the block, an upper Hessenberg $\mathbf{H}'$ in the work matrix that is a perturbed
unitary similarity of the block of $\mathbf{A}$ with error $\varepsilon_D$ by the log's unitary,
and the cut $i < d$ with $|h'_{i+1,i}| \le c$, `writeAndSplit` and `roundedDecoupleUpdate` reach
the core of round $j + 1$, when the decoupling error is within the round's budget $e$. -/
theorem roundedSplitUpdate_reached {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {k F T ns w m : ℕ} (hm : ns * w ≤ m) {np : ℕ} {tape : Tape ℝ}
    {μ : Mem ℝ} {lo d j lgb : ℕ} (hj : j < 2 * (n + 1)) {a t p uo f st wk ub r : ℕ × ℕ}
    {rs done : List (ℕ × ℕ)} {H U A U' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} {εL εD c e N₀ : ℝ} (hεL : 0 ≤ εL)
    (he : εD + 78 * u * (ns * w : ℕ) * N₀ + c ≤ e)
    (hroom : 2 * (n + 1) * (78 * u * (ns * w : ℕ) * N₀) ≤ N₀) (he0 : 0 ≤ e)
    (hN₀ : specNorm H + 2 * (n + 1) * e ≤ N₀) {L : List (Option (List GivensEntry))}
    (hG : SchurGeometry (n + 1) np a t p uo f st wk ub r μ)
    (hf : μ.store.get f.1 f.2 = some 0) (hA : HoldsMatrix a A μ.store)
    (hU' : HoldsMatrix uo U' μ.store) (hW : HoldsMatrix wk H' μ.store)
    (hSt : StackHolds st rs μ.store) (hsh : SchurShape n (rs ++ [(lo, d + 1)]) done A)
    (hcnt : 2 * done.length + rs.length = j)
    (htr : IsTrackedUnitarySimilar ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ done.length - 1)
      (j * e) U H U' A)
    (hlog : HoldsSlottedLog (lgb, 0) ns w L [] μ.store) (hlen : L.length = ns)
    (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d + 1) (hlgb : lgb < μ.store.length)
    (hlgv : ∀ v ∈ [a, t, p, uo, f, st, wk, ub, r], v.1 < lgb)
    (hblk : IsPerturbedUnitarySimilarBy (givensLog (d + 1) (slotEntries w L))
      (subBlock A (lo, d + 1)) H' εD)
    (hH' : IsUpperHessenberg H') (i : Fin d) (hc : ‖H' i.succ i.castSucc‖ ≤ c) :
    Writes .total I tape
      ((Stmt.frame [IExp.var 0, IExp.var 7, IExp.var 8, IExp.var 17]
          [{ buf := 0, off := IExp.var 9 }, { buf := 3, off := IExp.var 12 },
            { buf := 5, off := IExp.var 14 }] (writeAndSplit (O := O) (Q := Q)).body).seq
        (Stmt.frame [IExp.var 0, IExp.var 7, IExp.var 8, IExp.var 17, IExp.var 5, IExp.var 6]
          [{ buf := 8, off := IExp.const 0 }, { buf := 0, off := IExp.var 9 },
            { buf := 4, off := IExp.var 13 }] (roundedDecoupleUpdate (O := O) (Q := Q)).body))
      ((⟨(Env.frame [n + 1, k, np, F, T, ns, w, lo, d + 1] [a, t, p, st, uo, wk, r, f]).idx,
        (Env.frame [n + 1, k, np, F, T, ns, w, lo, d + 1] [a, t, p, st, uo, wk, r, f]).buf ++
          [lgb]⟩ : Env).pushIdx i)
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (SchurReachedCore n H U u εL e m a uo f st (j + 1)) μ := by
  have hmem : (lo, d + 1) ∈ rs ++ [(lo, d + 1)] ++ done := by simp
  have hfit0 := hsh.1.2.1 _ hmem
  simp only at hfit0
  have hlen0 := (hsh.deflationInv (H := A) (V := 1) (ε := 0)
    (by simpa using IsPerturbedUnitarySimilarBy.refl A)).length_le
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen0
  have hd : d + 1 ≤ n + 1 := by omega
  have hz : Mch.lit 0 = 0 := by simpa using hNat 0 (by omega)
  have hcap := ((hsh.split hz hH' hpl i).deflationInv (H := _) (V := 1) (ε := 0)
    (by simpa using IsPerturbedUnitarySimilarBy.refl _)).length_le
  simp only [List.length_append, List.length_cons, List.length_nil] at hcap
  have hi := i.isLt
  have hWw : Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ≤
      Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by
    have := Nat.mul_le_mul hd hd; fp_sub
  have g : ∀ i j : Fin 9, i ≠ j → _ := fun i j h => hG.disj' i j h
  have hWA : Fp.Disj (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by
    simpa [schurBlock] using g 6 0 (by simp)
  have hAS : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) := by simpa [schurBlock] using g 0 5 (by simp)
  have hAU : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) := by
    simpa [schurBlock] using g 0 3 (by simp)
  have hSU : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
      (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) := by
    simpa [schurBlock] using g 5 3 (by simp)
  have hFA : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) :=
    by simpa [schurBlock] using g 4 0 (by simp)
  have hFS : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) := by
    simpa using g 4 5 (by simp)
  have hFU : Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) := by
    simpa [schurBlock] using g 4 3 (by simp)
  have hlASW : μ.Live [a, st, wk] := hG.live_of_subset (by simp)
  have hsplit := writeAndSplit_writes_mem (O := O) (Q := Q) (τ := tape) (i := i) hS hL hQ hNat
    hlASW hA hW hSt hfit0.2 (by omega) (by omega) hG.room.1 hG.room.2.2.2.2.2.1
    (hWA.mono hWw le_rfl) hAS
  refine (hsplit.in_frame rfl rfl hlASW).seq_le (by fp_sub [schurRoundFp]) ?_
  rintro μ₃ hfr₃ ⟨-, hA₃, hSt₃⟩
  have hU₃ := hU'.of_eqOff hfr₃ (Fp.disj_sup_left.mpr ⟨hAU, hSU⟩)
  have hne : ∀ v ∈ [a, t, p, uo, f, st, wk, ub, r], v.1 ≠ lgb := fun v hv => by
    have := hlgv v hv; omega
  have hlog₃ := hfr₃.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (hne a (by simp)),
      Fp.disj_inBlock_of_ne (hne st (by simp))⟩) hlog
  have es_ok : ∀ e ∈ slotEntries w L, lo + e.1 + 1 < n + 1 := fun e he => by
    have := hpl e he; omega
  have hl₃ : μ₃.Live [(lgb, 0), a, uo] := fun v hv => by
    rw [hfr₃.length_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h <;> rw [h]
    exacts [hlgb, hG.live a (by simp), hG.live uo (by simp)]
  refine ((roundedDecoupleUpdate_writes (O := O) (Q := Q) (τ := tape) (M := Mch) hS hQ hC
    hfit0.2 (show (i : ℕ) + 1 < d + 1 by omega) es_ok (lg := (lgb, 0)) hl₃ hlog₃ hlen hA₃ hU₃
    (by rw [hfr₃.len_eq]; exact hG.room.1)
    (Fp.disj_inBlock_of_ne (hne a (by simp)).symm) (Fp.disj_inBlock_of_ne (hne uo (by simp)).symm)
    hAU).in_frame rfl rfl hl₃).mono (by fp_sub [schurRoundFp]) ?_
  rintro μ₄ hfr₄ ⟨-, hA₄, hU₄⟩
  have hSt₄ := hSt₃.of_eqOff hfr₄ (Fp.disj_sup_left.mpr ⟨hAS.mono le_rfl (by
    simp only [List.length_append, List.length_cons, List.length_nil]; fp_sub), hSU.symm.mono le_rfl
      (by simp only [List.length_append, List.length_cons, List.length_nil]; fp_sub)⟩)
  set es := slotEntries w L
  have hes : es.length ≤ ns * w := hlen ▸ hlog.length_slotEntries_le
  refine ⟨(hfr₃.trans' hfr₄).keep (Store.readsOnly_get _ _ _) (Fp.disj_sup_left.mpr
      ⟨Fp.disj_sup_left.mpr ⟨hFA.symm, hFS.symm⟩, Fp.disj_sup_left.mpr ⟨hFA.symm, hFU.symm⟩⟩) hf,
    _, done, _, _, hSt₄, hA₄, hU₄, hsh.split hz hH' hpl i, by simp; omega, ?_⟩
  exact decoupleRound_tracked hM hu0 hu hz hfit0.2 (hsh.isRangeBlockTriangular hmem) hpl hblk i
    hc hm hes hεL he hroom he0 hN₀ hj htr

/-- The rest of the large branch on the good tapes: under the conditions of
`NLAlib.ShiftedQR.roundedSplitUpdate_reached`, with the threshold word $t$,
$(1 + \boldsymbol{u})^2\omega^2 \le t \le (1 - \boldsymbol{u})^2c^2$, $c \ge 0$, $k \le d$, the
decoupler's flag $0$ and one of the bottom $k$ subdiagonal entries of $\mathbf{H}'$ of modulus at
most $\omega$, the branch on the flag, the bottom scan, the split and the update
(`NLAlib.ShiftedQR.roundedLargeRest`) reach the core of round $j + 1$: the scan always finds a
cut of modulus at most $c$. -/
theorem roundedLargeRest_reached {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {k F T ns w m : ℕ} (hm : ns * w ≤ m) {np : ℕ} {tape : Tape ℝ}
    {μ : Mem ℝ} {lo d j lgb : ℕ} (hj : j < 2 * (n + 1)) (hk : k ≤ d)
    {a t p uo f st wk ub r : ℕ × ℕ}
    {rs done : List (ℕ × ℕ)} {H U A U' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} {εL εD c e N₀ thr ω : ℝ} (hεL : 0 ≤ εL)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (he : εD + 78 * u * (ns * w : ℕ) * N₀ + c ≤ e)
    (hroom : 2 * (n + 1) * (78 * u * (ns * w : ℕ) * N₀) ≤ N₀) (he0 : 0 ≤ e)
    (hN₀ : specNorm H + 2 * (n + 1) * e ≤ N₀) {L : List (Option (List GivensEntry))}
    (hG : SchurGeometry (n + 1) np a t p uo f st wk ub r μ)
    (ht : μ.store.get t.1 t.2 = some thr)
    (hf : μ.store.get f.1 f.2 = some 0) (hA : HoldsMatrix a A μ.store)
    (hU' : HoldsMatrix uo U' μ.store) (hW : HoldsMatrix wk H' μ.store)
    (hSt : StackHolds st rs μ.store) (hsh : SchurShape n (rs ++ [(lo, d + 1)]) done A)
    (hcnt : 2 * done.length + rs.length = j)
    (htr : IsTrackedUnitarySimilar ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ done.length - 1)
      (j * e) U H U' A)
    (hlog : HoldsSlottedLog (lgb, 0) ns w L [] μ.store) (hlen : L.length = ns)
    (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d + 1) (hlgb : lgb < μ.store.length)
    (hlgv : ∀ v ∈ [a, t, p, uo, f, st, wk, ub, r], v.1 < lgb)
    (hblk : IsPerturbedUnitarySimilarBy (givensLog (d + 1) (slotEntries w L))
      (subBlock A (lo, d + 1)) H' εD)
    (hH' : IsUpperHessenberg H')
    (hsm : ∃ i : Fin d, d ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω) :
    Writes .total I tape (roundedLargeRest (O := O) (Q := Q))
      ⟨(Env.frame [n + 1, k, np, F, T, ns, w, lo, d + 1] [a, t, p, st, uo, wk, r, f]).idx,
        (Env.frame [n + 1, k, np, F, T, ns, w, lo, d + 1] [a, t, p, st, uo, wk, r, f]).buf ++
          [lgb]⟩
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (SchurReachedCore n H U u εL e m a uo f st (j + 1)) μ := by
  have hmem : (lo, d + 1) ∈ rs ++ [(lo, d + 1)] ++ done := by simp
  have hfit0 := hsh.1.2.1 _ hmem
  simp only at hfit0
  have hd : d + 1 ≤ n + 1 := by omega
  have hWw : Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ≤
      Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by
    have := Nat.mul_le_mul hd hd; fp_sub
  have hlen0 := (hsh.deflationInv (H := A) (V := 1) (ε := 0)
    (by simpa using IsPerturbedUnitarySimilarBy.refl A)).length_le
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen0
  unfold roundedLargeRest
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := f) hf) ?_
  rw [if_neg (by simp)]
  have hRW : Fp.Disj (Store.inBlock r.1 r.2 5)
      (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1)))) :=
    by simpa [schurBlock] using hG.disj' 8 6 (by simp)
  have hRT : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock t.1 t.2 1) := by
    simpa using hG.disj' 8 1 (by simp)
  have hRX : ∀ i : Fin 9, i ≠ 8 → Fp.Disj (Store.inBlock r.1 r.2 5)
      (schurBlock (n + 1) np a t p uo f st wk ub r i) :=
    fun i hi => hG.disj' 8 i (Ne.symm hi)
  have hlS : μ.Live [wk, t, r] := hG.live_of_subset (by simp)
  have hb := bottomScan_writes (τ := tape) (n := d) (k := k) hS hM hu0 (by linarith) hL
    (hNat.mono (by omega)) hC hk hW ht hlS hG.room.2.2.2.2.2.2.2.2.1 (hRW.mono le_rfl hWw) hRT
  refine (hb.in_frame rfl rfl hlS).seq_le (by fp_sub [schurRoundFp]) ?_
  rintro μ₂ hfr₂ ⟨-, hscan⟩
  have hG₂ := hG.of_eqOff hfr₂
  have hA₂ := hA.of_eqOff hfr₂ (by simpa [schurBlock] using hRX 0 (by simp))
  have hU₂ := hU'.of_eqOff hfr₂ (by simpa [schurBlock] using hRX 3 (by simp))
  have hf₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by simpa [schurBlock] using hRX 4 (by simp)) hf
  have hSt₂ := hSt.of_eqOff hfr₂ ((by simpa [schurBlock] using hRX 5 (by simp) :
    Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))).mono le_rfl
      (Fp.inBlock_le_inBlock le_rfl (by omega)))
  have hlog₂ := hfr₂.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
    (Fp.disj_inBlock_of_ne (by have := hlgv r (by simp); omega)) hlog
  have hu1 : 0 < 1 - u := by linarith
  rcases hscan with ⟨hR1, i, -, hRi, hti⟩ | ⟨-, hall⟩
  · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (r.1, r.2 + 3)) hR1) ?_
    rw [if_pos (by simp)]
    have hi := i.isLt
    refine writes_bindIdx_of_decode_nat hQ rfl rfl hRi rfl (by omega) ?_
    have hci : ‖H' i.succ i.castSucc‖ ≤ c := by
      have h1 : (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ (1 - u) ^ 2 * c ^ 2 := hti.trans hcut
      have h2 : ‖H' i.succ i.castSucc‖ ^ 2 ≤ c ^ 2 := le_of_mul_le_mul_left h1 (by positivity)
      exact (sq_le_sq₀ (norm_nonneg _) hc).mp h2
    exact roundedSplitUpdate_reached hS hM hu0 hu hL hNat hQ hC hm hj hεL he hroom he0 hN₀ hG₂
      hf₂ hA₂ hU₂ (hW.of_eqOff hfr₂ (hRW.mono le_rfl hWw)) hSt₂ hsh hcnt htr hlog₂ hlen hpl
      (by rw [hfr₂.length_eq]; exact hlgb) hlgv hblk hH' i hci
  · exfalso
    obtain ⟨i, hik, hiω⟩ := hsm
    have h1 := hall i hik
    have h2 : (1 + u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ (1 + u) ^ 2 * ω ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hiω 2) (by positivity)
    linarith

end Theorems
end NLAlib.ShiftedQR
