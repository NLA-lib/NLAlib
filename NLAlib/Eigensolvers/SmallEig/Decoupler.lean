/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveTermination
public import NLAlib.Eigensolvers.SmallEig.Decouple
public import NLAlib.Eigensolvers.SmallEig.OneEig
public import NLAlib.Eigensolvers.SmallEig.DecouplerPrecision
public import NLAlib.Eigensolvers.SmallEig.RandomHessenberg
public import NLAlib.Matrix.FinitePrecision.GivensLogClose
public import NLAlib.Matrix.FinitePrecision.GivensLogSlots
public import NLAlib.Eigensolvers.SmallEig.DecoupleTermination

/-!
# The decoupler of the small-eigenvalue solver

One node of the deflation of [BanksGarzaVargasSrivastava2025, §6] (the paper's `Eig` on a block,
with `RHess` at every node, decision D7 of the design): `RHess` makes the last-row weights large,
`OneEig` finds a shift within $\beta' = \omega/20$ of an eigenvalue and at least $\eta_1$ away from
the spectrum, and `Decouple` makes the last subdiagonal entry at most $\omega$. As the decoupler of
the rounded worklist at the bottom width $k = 1$ it satisfies the randomized decoupling contract on
the class of the blocks; Lemma 6.2's preservation of the class is carried by the composition of the
three contracts, and the class inside the node by one doubling
(`NLAlib.SmallEig.class_of_rhess`).

## Main definitions

* `NLAlib.SmallEig.smallEigDecoupler`: the program `[N, k, np, F, T] (W, P) → (W, Fl)`.

## Main results

* `NLAlib.SmallEig.smallEigDecoupler_randomDecouplingRoutineContract`,
  `NLAlib.SmallEig.smallEigDecoupler_terminatingDecouplerRoutine`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The decoupler of the small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025, §6], one
node): read the cap words $m$ (bound $T$), $q$ (bound $m$), $t$ and $m_2$ (bound $T$) from
`P[8..11]`; `NLAlib.SmallEig.rhess` on the block `W` in place; `NLAlib.SmallEig.oneEig` with the
words `P` into the shift `Lam` and the flag; if the flag is $0$,
`NLAlib.SmallEig.decoupleLast` with the shift. The rotations are recorded in the slotted log `Lg`
of `ns` slots of `w` entries, zero-filled first: `rhess` in the slots $0, \dots, N - 2$, the
steps of `decoupleLast` from the slot $N - 1$ on (so $N - 1 + m_2 \le n_s$ and $N - 1 \le w$).
The interface is `[N, k, np, F, T, ns, w] (W, P) → (W, Fl, Lg)`, that of the decoupling routine
of `NLAlib.ShiftedQR.solveRoundedWith`; the bottom width and the iteration cap are not read.
Algorithm: small-eig -/
def smallEigDecoupler (sG : ℕ) : Stmt O Q :=
  ops% [N, k, np, F, T, ns, w] (W, P) → (W, Fl, Lg) {
  let m ← index (Has.inj IdxTst.toNat) (P[8]) ≤ T;
  let q ← index (Has.inj IdxTst.toNat) (P[9]) ≤ m;
  let t ← index (Has.inj IdxTst.toNat) (P[10]) ≤ T;
  let m2 ← index (Has.inj IdxTst.toNat) (P[11]) ≤ T;
  let Lam ← alloc 2;
  run (slottedLogOpen (O := O) (Q := Q)) [ns, w] (Lg);
  run (rhess (O := O) (Q := Q) sG) [N, w, 0] (W, W, Lg);
  run (oneEig (O := O) (Q := Q)) [N, m, q, t] (W, P, Lam, Fl);
  if (Has.inj CmpTst.isZero) [] (Fl) {
    run (decoupleLast (O := O) (Q := Q)) [N, m2, w, N - 1] (W, Lam, P, W, Fl, Lg)
  } else { skip }
}

end Program

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- The outcomes of a decoupling call by the unitary of its log on a fixed block
$\mathbf{H}$, as pairs of a memory before and after: the frame `F`, the flag $0$, an initialised
work matrix whose value after is an upper Hessenberg perturbed unitary similarity of $\mathbf{H}$
by the unitary of the log read after (`NLAlib.slottedLogRead`) with error $\varepsilon$ and last
subdiagonal entry of modulus at most $\omega$, and the `ns` slots of the log closed with planes
below $n$. They form a measurable set. -/
theorem measurableSet_decoupleOutcomeBy {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ε ω : ℝ) (w f lg : ℕ × ℕ) (ns ws : ℕ) (F : Fp) :
    MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧
      x.2.store.get f.1 f.2 = some 0 ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (x.2.store.get w.1 (w.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilarBy
        (givensLog (n + 1) (slotEntries ws (slottedLogRead lg ns ws x.2.store))) H
        (storedMatrix w (n + 1) (n + 1) x.2.store) ε ∧
      IsUpperHessenberg (storedMatrix w (n + 1) (n + 1) x.2.store) ∧
      (∃ i : Fin n, n ≤ (i : ℕ) + 1 ∧
        ‖storedMatrix w (n + 1) (n + 1) x.2.store i.succ i.castSucc‖ ≤ ω) ∧
      ∃ Ls : List (Option (List GivensEntry)), Ls.length = ns ∧
        (∀ e ∈ slotEntries ws Ls, e.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns ws ([] ++ Ls) [] x.2.store} := by
  have hm : Measurable fun x : Mem ℝ × Mem ℝ => storedMatrix w (n + 1) (n + 1) x.2.store :=
    (measurable_storedMatrix w (n + 1) (n + 1)).comp measurable_snd
  have hV : Measurable fun x : Mem ℝ × Mem ℝ =>
      givensLog (n + 1) (slotEntries ws (slottedLogRead lg ns ws x.2.store)) :=
    (measurable_givensLog_slottedLogRead lg ns ws (n + 1)).comp measurable_snd
  have hent (i j : Fin (n + 1)) : Measurable fun x : Mem ℝ × Mem ℝ =>
      storedMatrix w (n + 1) (n + 1) x.2.store i j :=
    (Matrix.measurable_apply i j).comp hm
  simp only [Set.ofPred_and]
  refine (Mem.measurableSet_eqOff F).inter ((measurable_snd (Mem.measurableSet_get_eq f 0)).inter
    ((measurable_snd (measurableSet_forall_isSome w _)).inter
      (((isClosed_setOf_isPerturbedUnitarySimilarBy ε).measurableSet.preimage
        (hV.prodMk (measurable_const.prodMk hm))).inter ((?_ : MeasurableSet _).inter
          ((?_ : MeasurableSet _).inter (measurable_snd
            (measurableSet_exists_holdsSlottedLog_append lg ns ws (n + 1) ns [])))))))
  · simp only [IsUpperHessenberg, Set.ofPred_forall]
    refine .iInter fun i => .iInter fun j => ?_
    by_cases hij : (j : ℕ) + 1 < i
    · simpa [hij] using measurableSet_eq_fun (hent i j) measurable_const
    · simp [hij]
  · simp only [Set.ofPred_exists, Set.ofPred_and]
    exact .iUnion fun i => (MeasurableSet.const _).inter
      (measurableSet_le (hent _ _).norm measurable_const)

/-- The input of `OneEig` survives a write of the matrix: after a run that writes only the block
of the matrix and stores $\mathbf{H}'$ there, `NLAlib.SmallEig.OneEigInput` holds with
$\mathbf{H}'$. -/
theorem OneEigInput.of_eqOff_matrix {n : ℕ} {H H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} {h qw lam f : ℕ × ℕ} {μ μ' : Mem ℝ} (hin : OneEigInput H qs h qw lam f μ)
    (hfr : μ.store.EqOff (Store.inBlock h.1 h.2 (2 * ((n + 1) * (n + 1)))) μ'.store)
    (hH' : HoldsMatrix h H' μ'.store) : OneEigInput H' qs h qw lam f μ' := by
  obtain ⟨hl, hr, hA, -, hq⟩ := hin
  have hA' := hA
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true] at hA'
  refine ⟨fun x hx => hfr.length_eq ▸ hl x hx, ?_, hA, hH', ?_⟩
  · simpa only [Mem.Room, hfr.len_eq] using hr
  · exact hfr.keep (Store.readsOnly_readBlock _ _ _ _) hA'.1.1 hq

/-- The input of `OneEig` survives a write away from the words: after a run whose writes `F`
miss the words and that leaves a matrix $\mathbf{H}'$ stored, `NLAlib.SmallEig.OneEigInput`
holds with $\mathbf{H}'$. -/
theorem OneEigInput.of_eqOff {n : ℕ} {H H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} {h qw lam f : ℕ × ℕ} {μ μ' : Mem ℝ} {F : Fp}
    (hin : OneEigInput H qs h qw lam f μ) (hfr : μ.store.EqOff F μ'.store)
    (hdq : Fp.Disj F (Store.inBlock qw.1 qw.2 qs.length)) (hH' : HoldsMatrix h H' μ'.store) :
    OneEigInput H' qs h qw lam f μ' := by
  obtain ⟨hl, hr, hA, -, hq⟩ := hin
  refine ⟨fun x hx => hfr.length_eq ▸ hl x hx, ?_, hA, hH', hfr.keep
    (Store.readsOnly_readBlock _ _ _ _) hdq hq⟩
  simpa only [Mem.Room, hfr.len_eq] using hr

/-- The matrix and the words of `NLAlib.SmallEig.OneEigInput` are apart. -/
theorem OneEigInput.disj_words {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} {h qw lam f : ℕ × ℕ} {μ : Mem ℝ} (hin : OneEigInput H qs h qw lam f μ) :
    Fp.Disj (Store.inBlock h.1 h.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock qw.1 qw.2 qs.length) := by
  have hA := hin.2.2.1
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true] at hA
  exact hA.1.1

/-- From the input of `OneEig` to the input of `Decouple`: after a run that writes only the pair
`lam` and the flag and stores the point $z$ in the pair, `NLAlib.SmallEig.DecoupleInput` holds with
the shift $z$. -/
theorem OneEigInput.decoupleInput_of_eqOff {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} {h qw lam f : ℕ × ℕ} {μ μ' : Mem ℝ} {z : ℂ}
    (hin : OneEigInput H qs h qw lam f μ)
    (hfr : μ.store.EqOff (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1) μ'.store)
    (hz : μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im]) :
    DecoupleInput H z qs h lam qw f μ' := by
  obtain ⟨d1, d2, -⟩ := hin.disj
  obtain ⟨hl, hr, hA, hH, hq⟩ := hin
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true] at hA
  obtain ⟨⟨hhq, hhl, hhf⟩, ⟨hql, hqf⟩, hlf⟩ := hA
  refine ⟨fun x hx => ?_, ?_, ?_, hH.of_eqOff hfr d1, hz,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) d2 hq⟩
  · have := hl x (by simp only [List.mem_cons] at hx ⊢; tauto)
    exact hfr.length_eq ▸ this
  · simp only [Mem.Room, ← hfr.len_eq] at hr ⊢
    exact ⟨hr.1, hr.2.2.1, hr.2.1, hr.2.2.2⟩
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨hhl, hhq, hhf⟩, ⟨hql.symm, hlf⟩, hqf⟩

omit [Has SampleOp O] [Has IdxTst Q] in
/-- **`OneEig` inside the decoupler** ([BanksGarzaVargasSrivastava2025, Proposition 3.5] at the
parameters of `NLAlib.SmallEig.smallEigParams`): on a block of order $n + 1$,
$1 \le n \le n_{\max}$ with exact natural literals up to $n$, after `RHess` (upper Hessenberg,
condition at most $4B_c$, separation
$g_c/4$, last-row weights at least $p$, norm at most
$2\Sigma(1 + 200(n_{\max} + 1)^2\boldsymbol{u})$), `OneEig` with the cap words $m = 2^q$, $q$,
$t$ sets the flag to $0$ and stores a point at distance between $\eta_1$ and
$\beta'$ from the spectrum, except with probability at most $\varphi_D/2$.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem smallEigDecoupler_oneEig_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I)
    (hC : IsCmp id I) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn1 : 1 ≤ nmax)
    {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {n : ℕ} (hNat : IsExactNatLit id M n) (hn : 1 ≤ n)
    (hnn : n ≤ nmax)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    (hH : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ 4 * smallEigCondition nmax S δ φ c₂)
    (hgap : ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ / 4 ≤ ‖d i - d j‖)
    (hw : ∀ i, smallEigWeight nmax S δ φ c₂ ≤ lastRowWeights V i)
    (hHS : specNorm H ≤ 2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u)) {h qw lam f : ℕ × ℕ} :
    PWrites law I (oneEig (O := O) (Q := Q))
      (Env.frame [n + 1, 2 ^ smallEigDegreeLog nmax S δ φ c₂, smallEigDegreeLog nmax S δ φ c₂,
        smallEigRounds nmax S δ φ c₁ c₂] [h, qw, lam, f])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1)
      (OneEigInput H (smallEigParams nmax S δ φ c₁ c₂) h qw lam f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ z : ℂ,
        μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im] ∧
        smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ ⨅ i, ‖z - d i‖ ∧
        ⨅ i, ‖z - d i‖ ≤ smallEigAccuracy nmax S δ φ c₁ c₂)
      (smallEigDecouplerFailure nmax φ / 2) := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hS0 : 0 < S := hδ.trans_le hδS
  have hn' : (1 : ℝ) ≤ nmax := by exact_mod_cast hn1
  have hnn' : (n : ℝ) ≤ nmax := by exact_mod_cast hnn
  obtain ⟨ha, -, -, hd, he, -, -⟩ := smallEigDecoupler_precision hb₁ hb₂ hn1 hδ hδS hφ hφ1 hu
  obtain ⟨hβ, hβS⟩ := smallEigAccuracy_le hb₁ hb₂ hn1 hδ hδS hφ hφ1
  have hsep := smallEigSeparation_pos hb₁ hn1 hS0.le hδ hφ hφ1
  have hBc := smallEigCondition_ge hb₂ hn1 hS0.le hδ hφ hφ1
  obtain ⟨hp0, -⟩ := smallEigWeight_pos_le hb₂ hn1 hS0.le hδ hφ hφ1
  have hη₁ := smallEigInnerRadius_pos hb₁ hb₂ hn1 hδ hδS hφ hφ1
  have hD : 0 < smallEigDecouplerFailure nmax φ / 2 := by
    unfold smallEigDecouplerFailure; positivity
  have hD1 : smallEigDecouplerFailure nmax φ / 2 ≤ 1 := by
    unfold smallEigDecouplerFailure
    rw [div_div, div_le_one (by positivity)]; nlinarith
  have hη₁6 := oneEigInnerRadius_le hβ hβS
    (by positivity : 0 < smallEigSeparation nmax S δ φ c₁ / 4) hD1
  have hη₂β : smallEigOuterRadius nmax S δ φ c₁ c₂ ≤ smallEigAccuracy nmax S δ φ c₁ c₂ / 40 :=
    min_le_left _ _
  have hη₁S : smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ S := by
    change oneEigInnerRadius _ _ _ _ ≤ S at *
    unfold smallEigOuterRadius at hη₂β
    linarith
  obtain ⟨h1, h2, h3⟩ := smallEigDecoupler_oneEig_precision
    (m := 2 ^ smallEigDegreeLog nmax S δ φ c₂) hnn hu0 hS0 hη₁ hη₁S (by linarith)
    (specNorm_nonneg H) hHS ha he
  have hm : distSpecDegree (4 * smallEigCondition nmax S δ φ c₂) (smallEigWeight nmax S δ φ c₂)
      ≤ 2 ^ smallEigDegreeLog nmax S δ φ c₂ := by
    refine le_trans ?_ (distSpecDegree_le_two_pow_smallEigDegreeLog nmax S δ φ c₂)
    unfold distSpecDegree
    exact Nat.ceil_mono (by
      linarith [Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity)
        (by linarith : 4 * smallEigCondition nmax S δ φ c₂ ≤ 8 * smallEigCondition nmax S δ φ c₂)])
  have hnu : ((n : ℝ) + 1) * u ≤ 1 / 2500 := by nlinarith
  have hum : 30000 * (((2 ^ smallEigDegreeLog nmax S δ φ c₂ : ℕ) : ℝ) + 1) * u ≤ 1 := by
    push_cast; exact hd
  exact oneEig_pwrites_of_norm_le hS hM hL hNat hC hI hloc hDisk hU hn hH hV hHV hκ hp0 hw
    (by positivity) hgap hHS h1 h2 hβ hβS hD hD1 rfl hm rfl rfl rfl hnu hum h3
    (by simp [smallEigParams, smallEigOuterRadius]) (by simp [smallEigParams])
    (by simp [smallEigParams])


omit [Has SampleOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- **`Decouple` inside the decoupler, with its log** ([BanksGarzaVargasSrivastava2025,
Proposition 4.3] at the parameters of `NLAlib.SmallEig.smallEigParams`; deterministic): let
$\mathbf{H}_1$ of order $k + 2 \le n_{\max} + 1$ be the block after `RHess`, a perturbed unitary
similarity by $\mathbf{Q}_1$ with error at most $200(n_{\max} + 1)^2\boldsymbol{u}N$ of a block
$\mathbf{H}$ of norm at most $N \le 2\Sigma$, upper Hessenberg with condition at most $4B_c$,
separation $g_c/4$ and last-row weights at least $p$, and let the shift $z$ of `OneEig` be at
distance between $\eta_1$ and $\beta'$ from the spectrum. Then on every tape `Decouple`, from a log
with the closed slots `LL` and room for $m_2$ more, sets the flag to $0$, closes at most $m_2$
slots `Ls` (planes below $k + 1$), and stores an upper Hessenberg perturbed unitary similarity of
$\mathbf{H}$ by $\mathbf{Q}_1$ times the unitary of `Ls` with the error
`NLAlib.SmallEig.smallEigDecoupleError` at $N$ whose last subdiagonal entry is at most
$1.5\,\omega$.

Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem smallEigDecoupler_decouple_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn1 : 1 ≤ nmax)
    {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {k : ℕ} (hk : k + 1 ≤ nmax)
    (hNat : IsExactNatLit id M (k + 1 + 1)) {N ε₁ : ℝ}
    {H H₁ V Q₁ : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ} {d : Fin (k + 1 + 1) → ℂ}
    (hHN : specNorm H ≤ N) (hN : N ≤ 2 * S) (hH₁ : IsPerturbedUnitarySimilarBy Q₁ H H₁ ε₁)
    (hε₁ : ε₁ ≤ 200 * ((nmax : ℝ) + 1) ^ 2 * u * N)
    (hHess : IsUpperHessenberg H₁) (hV : IsUnit V) (hHV : H₁ * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ 4 * smallEigCondition nmax S δ φ c₂)
    (hgap : ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ / 4 ≤ ‖d i - d j‖)
    (hw : ∀ i, smallEigWeight nmax S δ φ c₂ ≤ lastRowWeights V i) {z : ℂ}
    (hz1 : smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ ⨅ i, ‖z - d i‖)
    (hz2 : ⨅ i, ‖z - d i‖ ≤ smallEigAccuracy nmax S δ φ c₁ c₂) {τ : Tape ℝ} {μ : Mem ℝ}
    {h lam qw f : ℕ × ℕ}
    (hin : DecoupleInput H₁ z (smallEigParams nmax S δ φ c₁ c₂) h lam qw f μ)
    {ns ws : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns ws LL [] μ.store)
    (hj : LL.length + smallEigDecoupleSteps nmax S δ φ c₂ ≤ ns) (hws : k + 1 ≤ ws)
    (hlgl : μ.Live [lg]) (hlgb : ∀ b ∈ [h, lam, qw, f], b.1 ≠ lg.1) :
    Writes .total I τ (decoupleLast (O := O) (Q := Q))
      (Env.frame [k + 1 + 1, smallEigDecoupleSteps nmax S δ φ c₂, ws, LL.length]
        [h, lam, qw, h, f, lg])
      (Store.inBlock h.1 h.2 (2 * ((k + 1 + 1) * (k + 1 + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ (Ls : List (Option (List GivensEntry)))
          (H' : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ),
        Ls.length ≤ smallEigDecoupleSteps nmax S δ φ c₂ ∧
        (∀ x ∈ slotEntries ws Ls, x.1 + 1 < k + 1 + 1) ∧
        HoldsSlottedLog lg ns ws (LL ++ Ls) [] μ'.store ∧
        IsPerturbedUnitarySimilarBy (Q₁ * givensLog (k + 1 + 1) (slotEntries ws Ls)) H H'
          (smallEigDecoupleError nmax S δ φ c₂ u N) ∧
        IsUpperHessenberg H' ∧
        (∃ i : Fin (k + 1), k + 1 ≤ (i : ℕ) + 1 ∧
          ‖H' i.succ i.castSucc‖ ≤ 1.5 * smallEigOmega nmax S δ φ c₁ c₂) ∧
        HoldsMatrix h H' μ'.store) μ := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  obtain ⟨hH0, hH₁2, hζ, hdist, ⟨i, hzi⟩, hxu, hfwd⟩ := smallEigDecoupler_decouple_conditions
    hb₁ hb₂ hn1 hu0 hδ hδS hφ hφ1 hu hk hHN hN hH₁.isPerturbedUnitarySimilar hε₁ hV hHV hgap
    hz1 hz2
  obtain ⟨ha, -⟩ := smallEigDecoupler_precision hb₁ hb₂ hn1 hδ hδS hφ hφ1 hu
  obtain ⟨-, -, -, -, -, -, hω, -, -, -, hp0, -, -, hm₂B⟩ :=
    smallEigParams_spec hb₁ hb₂ hn1 hδ hδS hφ hφ1
  have hnsq : (1 : ℝ) ≤ ((nmax : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ nmax := nmax.cast_nonneg; nlinarith
  have hu' : u ≤ 1 / 100 := by
    have := le_mul_of_one_le_left hu0 hnsq; linarith
  have hN0 : 0 ≤ N := (specNorm_nonneg H).trans hHN
  have hm₂ : 1 ≤ smallEigDecoupleSteps nmax S δ φ c₂ := by
    unfold smallEigDecoupleSteps decoupleSteps; omega
  have hβ : smallEigAccuracy nmax S δ φ c₁ c₂ = smallEigOmega nmax S δ φ c₁ c₂ / 20 := rfl
  have hBc := smallEigCondition_ge hb₂ hn1 (hδ.le.trans hδS) hδ hφ hφ1
  have h7 : (smallEigParams nmax S δ φ c₁ c₂).getD 7 0 = 2 * smallEigOmega nmax S δ φ c₁ c₂ ^ 2 :=
    by simp [smallEigParams]
  have htL : (1 + u) ^ 2 * smallEigOmega nmax S δ φ c₁ c₂ ^ 2 ≤
      (smallEigParams nmax S δ φ c₁ c₂).getD 7 0 := by
    rw [h7]
    have : (1 + u) ^ 2 ≤ 2 := by
      have := mul_le_mul hu' hu' hu0 (by norm_num : (0 : ℝ) ≤ 1 / 100)
      ring_nf; linarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hres := decoupleLast_spec (n := k) (C := 10) (B := 4 * smallEigCondition nmax S δ φ c₂)
    (O := O) (Q := Q) (τ := τ) hS hM (by linarith) hL hC (hNat.mono (by omega)) hHess hH0 hV
    hHV hκ (by norm_num) hζ (smallEigInnerRadius_pos hb₁ hb₂ hn1 hδ hδS hφ hφ1) hdist hzi hp0
    (hw i) (by rw [hβ]; linarith) hm₂ (by linarith) hxu hfwd (by simp [smallEigParams]) htL hin
    hlog hj hws hlgl hlgb
  have e : Env.frame [k + 2, smallEigDecoupleSteps nmax S δ φ c₂, ws, LL.length]
      [h, lam, qw, h, f, lg] =
      Env.frame [k + 1 + 1, smallEigDecoupleSteps nmax S δ φ c₂, ws, LL.length]
        [h, lam, qw, h, f, lg] :=
    congrArg (fun x => Env.frame [x, smallEigDecoupleSteps nmax S δ φ c₂, ws, LL.length]
      [h, lam, qw, h, f, lg]) (by omega)
  have eF : Store.inBlock h.1 h.2 (2 * ((k + 2) * (k + 2))) =
      Store.inBlock h.1 h.2 (2 * ((k + 1 + 1) * (k + 1 + 1))) :=
    congrArg (fun x => Store.inBlock h.1 h.2 (2 * (x * x))) (by omega)
  rw [e, eF] at hres
  refine hres.mono le_rfl ?_
  rintro μ' - ⟨hf0, Ls, H', hLs, hpl, hlg, hby, hHess', hW, hsub⟩
  refine ⟨hf0, Ls, H', hLs, hpl, hlg,
    (hH₁.trans hby).mono (smallEigDecoupleError_le hk hu0 hN0 hH₁2 hε₁), hHess',
    ⟨Fin.last k, by simp, ?_⟩, hW⟩
  rw [h7] at hsub
  rw [Fin.succ_last]
  exact le_of_sub_mul_le_sqrt hω hu' hsub

/-- The blocks after `RHess` inside the decoupler: $\mathbf{H}_1$ is upper Hessenberg, a perturbed
unitary similarity of the block $\mathbf{H}$ by $\mathbf{Q}$ with the error $\varepsilon$, and has a
diagonalization with condition at most $4B_c$, separation $g_c/4$ and last-row weights at least
$p$. -/
def SmallEigRHessClass (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ε : ℝ)
    (Q H₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  IsUpperHessenberg H₁ ∧ IsPerturbedUnitarySimilarBy Q H H₁ ε ∧
    ∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
      IsUnit V ∧ H₁ * V = V * Matrix.diagonal d ∧
      pseudoConditionNumber V ≤ 4 * smallEigCondition nmax S δ φ c₂ ∧
      (∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ / 4 ≤ ‖d i - d j‖) ∧
      ∀ i, smallEigWeight nmax S δ φ c₂ ≤ lastRowWeights V i

omit [Has DiskSampleOp O] [Has IdxTst Q] in
/-- **`RHess` inside the decoupler, with its log** ([BanksGarzaVargasSrivastava2025,
Proposition 5.3] at the parameters of `NLAlib.SmallEig.smallEigParams`): on a block of order
$n + 1$, $1 \le n \le n_{\max}$, with exact natural literals up to $n_l \ge n$, of norm at most
$N \le 2\Sigma$ in the class $(2B_c, g_c/2)$, and an empty log with room for $n$ slots of at least
$n$ entries, `RHess` closes $n$ slots `Ls` (planes below $n$) and stores a block in
`NLAlib.SmallEig.SmallEigRHessClass` by the unitary of `Ls` with the error
$200(n + 1)^2\boldsymbol{u}N$, except with probability at most $\varphi_D/2$.

Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem smallEigDecoupler_rhess_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hzero : M.lit 0 = 0) (hC : IsCmp id I)
    (hL : IsIndexLit M I) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sG : ℕ}
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : 1 ≤ nmax) {nl : ℕ} (hNat : IsExactNatLit id M nl) {S δ φ : ℝ} (hδ : 0 < δ)
    (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {n : ℕ} (hn1 : 1 ≤ n) (hnn : n ≤ nmax) (hnl : n ≤ nl)
    {N : ℝ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hN : N ≤ 2 * S)
    (hHN : specNorm H ≤ N) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ 2 * smallEigCondition nmax S δ φ c₂)
    (hgap : ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ / 2 ≤ ‖d i - d j‖) {w lg : ℕ × ℕ}
    {ns ws : ℕ} (hns : n ≤ ns) (hws : n ≤ ws) :
    PWrites law I (rhess (O := O) (Q := Q) sG) (Env.frame [n + 1, ws, 0] [w, w, lg])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
      (fun μ => HoldsMatrix w H μ.store ∧ μ.Live [w] ∧ HoldsSlottedLog lg ns ws [] [] μ.store ∧
        μ.Live [lg] ∧ lg.1 ≠ w.1)
      (fun μ' => ∃ (H₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Ls : List (Option (List GivensEntry))), HoldsMatrix w H₁ μ'.store ∧ Ls.length = n ∧
        (∀ e ∈ slotEntries ws Ls, e.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns ws Ls [] μ'.store ∧
        SmallEigRHessClass nmax S δ φ c₁ c₂ H (200 * ((n : ℝ) + 1) ^ 2 * u * N)
          (givensLog (n + 1) (slotEntries ws Ls)) H₁)
      (smallEigDecouplerFailure nmax φ / 2) := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hS0 : 0 < S := hδ.trans_le hδS
  have hN0 : 0 ≤ N := (specNorm_nonneg H).trans hHN
  have hBc := smallEigCondition_ge hb₂ hn hS0.le hδ hφ hφ1
  have hsep := smallEigSeparation_pos hb₁ hn hS0.le hδ hφ hφ1
  have hgcS : smallEigSeparation nmax S δ φ c₁ ≤ S := by
    obtain ⟨-, hg⟩ := smallEigGap_pos_le hb₁ hn hS0.le hδ hφ hφ1
    have hW : 3 ≤ smallEigNoiseLevel φ := by
      unfold smallEigNoiseLevel; linarith [Real.sqrt_nonneg (Real.log (4 / φ))]
    have hγ := smallEigScale_mul_noiseLevel δ φ
    have hγ0 := (smallEigScale_pos (φ := φ) hδ).le
    have := mul_le_mul_of_nonneg_left hW hγ0
    unfold smallEigSeparation; linarith
  obtain ⟨ha, hb, hc, -, -, -, -⟩ := smallEigDecoupler_precision hb₁ hb₂ hn hδ hδS hφ hφ1 hu
  obtain ⟨hs, hR, hpw, hsp, hRr, hfail⟩ := smallEigDecoupler_rhess_params hn hnn
    hφ hφ1 (by linarith) S δ c₂ rfl
  obtain ⟨hnu, hus, huc⟩ := smallEigDecoupler_rhess_precision hnn hu0 hN0 hN hsep hgcS hBc hs hR
    hsp ha hb hc
  have hφD : 0 < smallEigDecouplerFailure nmax φ := by unfold smallEigDecouplerFailure; positivity
  have hφD1 : smallEigDecouplerFailure nmax φ ≤ 1 := by
    unfold smallEigDecouplerFailure; rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
    nlinarith
  exact (rhess_pwrites (a := w) (lg := lg) (LL := []) hS hM hzero hC hSmp hG hV hHV hκ
    (by positivity) hgap hHN hs (φ' := smallEigDecouplerFailure nmax φ / 4) (by positivity)
    (by linarith) hRr hnu hus huc hL hn1 hNat hnl (by simpa using hns) hws).mono
    (fun _ h => h) le_rfl
    (fun μ' ⟨H₁, V', d', Ls, hW₁, hLs, hpl, hlg, hHess₁, hPUS₁, hV', hHV', hκ', hgap', hw'⟩ =>
      ⟨H₁, Ls, hW₁, hLs, hpl, by simpa using hlg, hHess₁, hPUS₁, V', d', hV', hHV',
        by linarith, fun i j hij => by linarith [hgap' i j hij], fun i => hpw ▸ hw' i⟩) hfail

/-- The memory after `RHess` inside the decoupler, for the block $\mathbf{H}_1$ and the closed
slots `Ls₁`: the input of `OneEig` with the pair at `(L, 0)`, and the log, live and in a buffer
of its own. -/
def SmallEigTailInput {n : ℕ} (H₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (qs : List ℝ)
    (w q f lg : ℕ × ℕ) (L ns ws : ℕ) (Ls₁ : List (Option (List GivensEntry))) (μ : Mem ℝ) :
    Prop :=
  OneEigInput H₁ qs w q (L, 0) f μ ∧ HoldsSlottedLog lg ns ws Ls₁ [] μ.store ∧ μ.Live [lg] ∧
    ∀ b ∈ [w, (L, 0), q, f], b.1 ≠ lg.1

/-- The outcome of the decoupling contract (`NLAlib.ShiftedQR.RandomDecouplingRoutineContract`)
for the block $\mathbf{H}$ of order $n + 1$ at the bottom width $1$: the flag $0$, the `ns` slots
of the log closed (planes below $n$), and an upper Hessenberg perturbed unitary similarity of
$\mathbf{H}$ by the unitary of the log, with error $\varepsilon$ and last subdiagonal entry of
modulus at most $\omega$, stored at `w`. -/
def SmallEigDecoupleOutcome {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ε ω : ℝ)
    (w f lg : ℕ × ℕ) (ns ws : ℕ) (μ' : Mem ℝ) : Prop :=
  μ'.store.get f.1 f.2 = some 0 ∧
    ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (L : List (Option (List GivensEntry))),
      L.length = ns ∧ (∀ e ∈ slotEntries ws L, e.1 + 1 < n + 1) ∧
      HoldsSlottedLog lg ns ws L [] μ'.store ∧
      IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries ws L)) H H' ε ∧
      IsUpperHessenberg H' ∧ (∃ i : Fin n, n ≤ (i : ℕ) + 1 ∧ ‖H' i.succ i.castSucc‖ ≤ ω) ∧
      HoldsMatrix w H' μ'.store

omit [Has SampleOp O] [Has IdxTst Q] in
/-- The tail of the decoupler (`OneEig`, then `Decouple` on the flag $0$): from a block
$\mathbf{H}_1$ in `NLAlib.SmallEig.SmallEigRHessClass` of a block $\mathbf{H}$ of order
$k + 2 \le n_{\max} + 1$ and norm at most $N \le 2\Sigma$ by the unitary of the $k + 1$ closed
slots `Ls₁`, with the pair at `(L, 0)` and room in the log for the steps of `Decouple`, the tail
of `NLAlib.SmallEig.smallEigDecoupler` reaches the outcome of the decoupling contract, except with
probability at most $\varphi_D/2$. The frames are given by their evaluations. -/
theorem smallEigDecoupler_tail_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    (hU : law sU = volume.restrict (Set.Icc 0 1)) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b)
    (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : 1 ≤ nmax)
    {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {k : ℕ} (hnn : k + 1 ≤ nmax)
    (hNat : IsExactNatLit id M (k + 1 + 1)) {N : ℝ}
    {H H₁ : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ} (hHN : specNorm H ≤ N) (hN : N ≤ 2 * S)
    {ns ws : ℕ} {Ls₁ : List (Option (List GivensEntry))} (hLs₁ : Ls₁.length = k + 1)
    (hpl₁ : ∀ e ∈ slotEntries ws Ls₁, e.1 + 1 < k + 1 + 1)
    (hx : SmallEigRHessClass nmax S δ φ c₁ c₂ H (200 * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 * u * N)
      (givensLog (k + 1 + 1) (slotEntries ws Ls₁)) H₁)
    (hj : k + 1 + smallEigDecoupleSteps nmax S δ φ c₂ ≤ ns) (hws : k + 1 ≤ ws)
    {ρ : Env} {ds₁ ds₂ : List IExp} {args₁ tins args₂ : List Operand} {w q f lg : ℕ × ℕ} {L : ℕ}
    (hd₁ : IExp.evalList ρ.idx ds₁ = some [k + 1 + 1, 2 ^ smallEigDegreeLog nmax S δ φ c₂,
      smallEigDegreeLog nmax S δ φ c₂, smallEigRounds nmax S δ φ c₁ c₂])
    (ha₁ : Operand.evalList ρ args₁ = some [w, q, (L, 0), f])
    (ht : Operand.evalList ρ tins = some [f])
    (hd₂ : IExp.evalList ρ.idx ds₂ = some [k + 1 + 1, smallEigDecoupleSteps nmax S δ φ c₂, ws,
      k + 1])
    (ha₂ : Operand.evalList ρ args₂ = some [w, (L, 0), q, w, f, lg]) :
    PWrites law I ((Stmt.frame ds₁ args₁ (oneEig (O := O) (Q := Q))).seq
        (Stmt.ite (Has.inj CmpTst.isZero) [] tins
          (Stmt.frame ds₂ args₂ (decoupleLast (O := O) (Q := Q))) Stmt.skip)) ρ
      (Store.inBlock L 0 2 ⊔ Store.inBlock f.1 f.2 1 ⊔
        (Store.inBlock w.1 w.2 (2 * ((k + 1 + 1) * (k + 1 + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
          Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws))))
      (SmallEigTailInput H₁ (smallEigParams nmax S δ φ c₁ c₂) w q f lg L ns ws Ls₁)
      (SmallEigDecoupleOutcome H (smallEigDecoupleError nmax S δ φ c₂ u N)
        (1.5 * smallEigOmega nmax S δ φ c₁ c₂) w f lg ns ws)
      (smallEigDecouplerFailure nmax φ / 2) := by
  obtain ⟨hHess₁, hPUS₁, V', d', hV', hHV', hκ', hgap', hw'⟩ := hx
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hε₁ : 200 * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 * u * N ≤ 200 * ((nmax : ℝ) + 1) ^ 2 * u * N := by
    have := (specNorm_nonneg H).trans hHN
    have : ((k + 1 : ℕ) : ℝ) ≤ nmax := by exact_mod_cast hnn
    gcongr
  have hH₁S : specNorm H₁ ≤ 2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u) := by
    have h1 := hPUS₁.isPerturbedUnitarySimilar.specNorm_le
    have h2 : 200 * ((nmax : ℝ) + 1) ^ 2 * u * N ≤ 200 * ((nmax : ℝ) + 1) ^ 2 * u * (2 * S) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    nlinarith
  have hA := smallEigDecoupler_oneEig_pwrites (O := O) (Q := Q) hS hM hL hC hI hloc hDisk hU hb₁
    hb₂ hn hδ hδS hφ hφ1 hu (n := k + 1) (hNat.mono (by omega)) (by omega) hnn hHess₁ hV' hHV'
    hκ' hgap' hw' hH₁S (h := w) (qw := q) (lam := (L, 0)) (f := f)
  refine (PWrites.seq (Mid := fun μ₂ => μ₂.store.get f.1 f.2 = some 0 ∧ ∃ z : ℂ,
      DecoupleInput H₁ z (smallEigParams nmax S δ φ c₁ c₂) w (L, 0) q f μ₂ ∧
      smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ ⨅ i, ‖z - d' i‖ ∧
      ⨅ i, ‖z - d' i‖ ≤ smallEigAccuracy nmax S δ φ c₁ c₂ ∧
      HoldsSlottedLog lg ns ws Ls₁ [] μ₂.store ∧ μ₂.Live [lg] ∧
      ∀ b ∈ [w, (L, 0), q, f], b.1 ≠ lg.1)
    hI hloc le_rfl ((hA.mono_eqOff (fun _ h => h.1)
      (fun μ μ' hμ hfr ⟨hf0, z, hz, hz1, hz2⟩ =>
        ⟨hf0, z, hμ.1.decoupleInput_of_eqOff hfr hz, hz1, hz2,
          hfr.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
            (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (hμ.2.2.2 _ (by simp)),
              Fp.disj_inBlock_of_ne (hμ.2.2.2 _ (by simp))⟩) hμ.2.1,
          fun x hx => hfr.length_eq ▸ hμ.2.2.1 x hx, hμ.2.2.2⟩)).in_frame hd₁ ha₁
        (fun μ hμ => hμ.1.1))
    (PWrites.of_writes (F := Store.inBlock w.1 w.2 (2 * ((k + 1 + 1) * (k + 1 + 1))) ⊔
      Store.inBlock f.1 f.2 1 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws))) le_rfl
      fun μ₂ τ ⟨hf0, z, hdin, hz1, hz2, hlg, hlgl, hne⟩ => ?_)).mono
    (fun _ h => h) le_rfl (fun _ h => h) (by simp)
  refine writes_ite (a := [f]) rfl ht (hC.test_isZero hf0) ?_
  simp only [id, decide_true, if_true]
  have hd₂' : IExp.evalList ρ.idx ds₂ = some [k + 1 + 1, smallEigDecoupleSteps nmax S δ φ c₂, ws,
      Ls₁.length] := by rw [hd₂, hLs₁]
  refine ((smallEigDecoupler_decouple_writes (O := O) (Q := Q) hS hM hL hC hb₁ hb₂ hn hδ
    hδS hφ hφ1 hu hnn hNat hHN hN hPUS₁ hε₁ hHess₁ hV' hHV' hκ' hgap' hw' hz1 hz2 hdin hlg
    (by omega) hws hlgl (fun b hb => hne b (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢; tauto))).in_frame
    hd₂' ha₂ (fun x hx => by
      have hd := hdin.1
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hd hlgl hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [hd.1, hd.2.1, hd.2.2.1, hd.1, hd.2.2.2, hlgl])).mono le_rfl ?_
  rintro μ' - ⟨hf0', Ls₂, H', hLs₂, hpl₂, hlg', hby, hHess', hsub, hW'⟩
  have hc : (Ls₁ ++ Ls₂).length + (ns - (k + 1) - Ls₂.length) ≤ ns := by simp; omega
  refine ⟨hf0', H', Ls₁ ++ Ls₂ ++ List.replicate (ns - (k + 1) - Ls₂.length) none,
    by simp; omega, fun e he => ?_, hlg'.rejects hc, ?_, hHess', hsub, hW'⟩
  · simp only [slotEntries_append, slotEntries_replicate_none, List.append_nil,
      List.mem_append] at he
    rcases he with he | he
    exacts [hpl₁ e he, hpl₂ e he]
  · simpa only [slotEntries_append, slotEntries_replicate_none, List.append_nil,
      givensLog_append] using hby

omit [Has SampleOp O] [Has IdxTst Q] in
/-- The input of `OneEig` after the allocation of the pair: from the memory of the decoupling
contract (`NLAlib.ShiftedQR.RandomDecouplingRoutineContract`) and a store with one fresh buffer of
two words at the handle $L$ = the old buffer count, `NLAlib.SmallEig.OneEigInput` holds with the
pair at `(L, 0)`. -/
theorem OneEigInput.of_alloc {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {qs : List ℝ}
    (hqs : 0 < qs.length) {w q f : ℕ × ℕ} {μ : Mem ℝ} {s₁ : Store ℝ}
    (hW : HoldsMatrix w H μ.store) (hq : μ.store.readBlock q.1 q.2 qs.length = some qs)
    (hl : μ.Live [w, q, w, f]) (hwr : w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1)
    (hfr : f.2 + 1 ≤ μ.store.len f.1)
    (hwf : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hqwf : Fp.Disj (Store.inBlock q.1 q.2 qs.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1))
    (hlen : s₁.length = μ.store.length + 1) (hL2 : s₁.len μ.store.length = 2)
    (hBelow : Store.Below μ.store.length μ.store s₁) :
    OneEigInput H qs w q (μ.store.length, 0) f ⟨s₁, μ.pos⟩ := by
  simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hl
  obtain ⟨hlw, hlq, -, hlf⟩ := hl
  have hq₁ := hBelow.readBlock_of hlq hq
  have hD : ∀ {b o k : ℕ}, b < μ.store.length →
      Fp.Disj (Store.inBlock μ.store.length 0 2) (Store.inBlock b o k) :=
    fun hb => Fp.disj_inBlock_of_ne (by omega)
  have hqw := (hqwf.mono le_rfl le_sup_left).symm
  have hqf := hqwf.mono le_rfl le_sup_right
  refine ⟨by simp [Mem.Live, hlen]; omega, ?_, ?_, hW.of_below hBelow hlw, hq₁⟩
  · simp only [Mem.Room]
    exact ⟨(hBelow w.1 hlw).1 ▸ hwr, Store.le_len_of_readBlock hq₁ hqs, by simp [hL2],
      (hBelow f.1 hlf).1 ▸ hfr, trivial⟩
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨hqw, (hD hlw).symm, hwf⟩, ⟨(hD hlq).symm, hqf⟩, hD hlf⟩

/-- The memory of `NLAlib.SmallEig.smallEigDecoupler` after the allocation of the pair at
`(L, 0)`: the input of `OneEig`, and the log live, with room for its `ns` slots of `ws` entries
and in a buffer of its own. -/
def SmallEigDecouplerAlloc {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (qs : List ℝ)
    (w q f lg : ℕ × ℕ) (ns ws L : ℕ) (μ : Mem ℝ) : Prop :=
  OneEigInput H qs w q (L, 0) f μ ∧ μ.Live [lg] ∧ lg.2 + ns * (1 + 5 * ws) ≤ μ.store.len lg.1 ∧
    ∀ b ∈ [w, (L, 0), q, f], b.1 ≠ lg.1

omit [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The memory of the decoupling contract after the allocation of the pair: from the memory of
`NLAlib.ShiftedQR.RandomDecouplingRoutineContract` and a store with one fresh buffer of two
words at the handle $L$ = the old buffer count, `NLAlib.SmallEig.SmallEigDecouplerAlloc` holds. -/
theorem SmallEigDecouplerAlloc.of_alloc {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} (hqs : 0 < qs.length) {w q f lg : ℕ × ℕ} {ns ws : ℕ} {μ : Mem ℝ}
    {s₁ : Store ℝ} (hW : HoldsMatrix w H μ.store)
    (hq : μ.store.readBlock q.1 q.2 qs.length = some qs) (hl : μ.Live [w, q, w, f, lg])
    (hlgb : ∀ b ∈ [w, q, f], b.1 ≠ lg.1) (hwr : w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1)
    (hfr : f.2 + 1 ≤ μ.store.len f.1) (hlgr : lg.2 + ns * (1 + 5 * ws) ≤ μ.store.len lg.1)
    (hA : Fp.Apart [w, f, lg] [2 * ((n + 1) * (n + 1)), 1, ns * (1 + 5 * ws)])
    (hqd : Fp.Disj (Store.inBlock q.1 q.2 qs.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws))))
    (hlen : s₁.length = μ.store.length + 1) (hL2 : s₁.len μ.store.length = 2)
    (hBelow : Store.Below μ.store.length μ.store s₁) :
    SmallEigDecouplerAlloc H qs w q f lg ns ws μ.store.length ⟨s₁, μ.pos⟩ := by
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true] at hA
  have hl' : μ.Live [w, q, w, f] := fun x hx => hl x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  have hlg1 : lg.1 < μ.store.length := hl lg (by simp)
  refine ⟨OneEigInput.of_alloc hqs hW hq hl' hwr hfr hA.1.1
    (hqd.mono le_rfl (sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left)))
    hlen hL2 hBelow, fun x hx => ?_, ?_, fun b hb => ?_⟩
  · rw [List.mem_singleton.mp hx]
    change lg.1 < s₁.length
    omega
  · change lg.2 + ns * (1 + 5 * ws) ≤ s₁.len lg.1
    rw [(hBelow lg.1 hlg1).1]; exact hlgr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hlgb _ (by simp)
    · exact (Nat.ne_of_lt hlg1).symm
    · exact hlgb _ (by simp)
    · exact hlgb _ (by simp)

/-- The memory of `NLAlib.SmallEig.smallEigDecoupler` after the log is opened: the block at `w`
and the empty log, live and in buffers of their own, and the input of `OneEig` with the pair at
`(L, 0)`. -/
def SmallEigDecouplerOpened {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (qs : List ℝ)
    (w q f lg : ℕ × ℕ) (ns ws L : ℕ) (μ : Mem ℝ) : Prop :=
  HoldsMatrix w H μ.store ∧ μ.Live [w] ∧ HoldsSlottedLog lg ns ws [] [] μ.store ∧ μ.Live [lg] ∧
    lg.1 ≠ w.1 ∧ OneEigInput H qs w q (L, 0) f μ ∧ ∀ b ∈ [w, (L, 0), q, f], b.1 ≠ lg.1

omit [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- Opening the log of the decoupler: from `NLAlib.SmallEig.SmallEigDecouplerAlloc`, the frame of
`NLAlib.slottedLogOpen` given by its evaluations writes only the log and reaches
`NLAlib.SmallEig.SmallEigDecouplerOpened`. -/
theorem smallEigDecoupler_open_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} {w q f lg : ℕ × ℕ} {ns ws L : ℕ} {ρ : Env} {ds : List IExp}
    {args : List Operand} (hd : IExp.evalList ρ.idx ds = some [ns, ws])
    (ha : Operand.evalList ρ args = some [lg]) {τ : Tape ℝ} {μ : Mem ℝ}
    (hμ : SmallEigDecouplerAlloc H qs w q f lg ns ws L μ) :
    Writes .total I τ (.frame ds args (slottedLogOpen (O := O) (Q := Q))) ρ
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
      (SmallEigDecouplerOpened H qs w q f lg ns ws L) μ := by
  obtain ⟨hin, hlgl, hlgr, hne⟩ := hμ
  refine ((slottedLogOpen_writes hS hM hlgr).in_frame hd ha hlgl).mono le_rfl ?_
  rintro μ' hfr ⟨-, hlog⟩
  have hin' := hin.of_eqOff hfr (Fp.disj_inBlock_of_ne (hne q (by simp)).symm)
    (hin.2.2.2.1.of_eqOff hfr (Fp.disj_inBlock_of_ne (hne w (by simp)).symm))
  exact ⟨hin'.2.2.2.1, fun x hx => hin'.1 x (by simp at hx ⊢; tauto), hlog,
    fun x hx => hfr.length_eq ▸ hlgl x hx, (hne w (by simp)).symm, hin', hne⟩

/-- After `RHess` (a run writing only the block and the log, storing $\mathbf{H}_1$ and the closed
slots `Ls`), the opened memory of the decoupler is the input of its tail
(`NLAlib.SmallEig.SmallEigTailInput`). -/
theorem SmallEigDecouplerOpened.tailInput {n : ℕ} {H H₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} {w q f lg : ℕ × ℕ} {ns ws L : ℕ} {Ls : List (Option (List GivensEntry))}
    {μ μ' : Mem ℝ} (hμ : SmallEigDecouplerOpened H qs w q f lg ns ws L μ)
    (hfr : μ.store.EqOff (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws))) μ'.store)
    (hW₁ : HoldsMatrix w H₁ μ'.store) (hlog : HoldsSlottedLog lg ns ws Ls [] μ'.store) :
    SmallEigTailInput H₁ qs w q f lg L ns ws Ls μ' :=
  ⟨hμ.2.2.2.2.2.1.of_eqOff hfr (Fp.disj_sup_left.mpr ⟨hμ.2.2.2.2.2.1.disj_words,
    Fp.disj_inBlock_of_ne (hμ.2.2.2.2.2.2 q (by simp)).symm⟩) hW₁, hlog,
    fun x hx => hfr.length_eq ▸ hμ.2.2.2.1 x hx, hμ.2.2.2.2.2.2⟩

/-- The opened memory of the decoupler has the views of `RHess` live. -/
theorem SmallEigDecouplerOpened.live {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} {w q f lg : ℕ × ℕ} {ns ws L : ℕ} {μ : Mem ℝ}
    (hμ : SmallEigDecouplerOpened H qs w q f lg ns ws L μ) : μ.Live [w, w, lg] := fun x hx => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  exacts [hμ.2.1 _ (by simp), hμ.2.1 _ (by simp), hμ.2.2.2.1 _ (by simp)]

/-- The decoupler meets the randomized decoupling contract at a smaller order bound
(`NLAlib.SmallEig.smallEigDecoupler_randomDecouplingRoutineContract` with the words still at
$n_{\max}$): the contract holds at orders up to $k_b \le n_{\max}$ when the natural literals are
exact up to $k_b + 1$ only, and the log has $n_s \ge k_b + T$ slots of $w_s \ge k_b$ entries. -/
theorem smallEigDecoupler_randomDecouplingRoutineContract_of_le {M : Machine ℝ}
    {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I) (hM : StdModel u id M) (hzero : M.lit 0 = 0)
    (hL : IsIndexLit M I) {nmax kb : ℕ} (hkb : kb ≤ nmax) (hNat : IsExactNatLit id M (kb + 1))
    (hC : IsCmp id I)
    (hQ : IsToNat id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) (F : ℕ) {ns ws : ℕ}
    (hns : kb + smallEigCap nmax S δ φ c₁ c₂ ≤ ns) (hws : kb ≤ ws) :
    RandomDecouplingRoutineContract law (2 * smallEigCondition nmax S δ φ c₂)
      (smallEigSeparation nmax S δ φ c₁ / 2) (smallEigDecouplerFailure nmax φ) 1 F
      (smallEigCap nmax S δ φ c₁ c₂) kb (2 * S) (smallEigParams nmax S δ φ c₁ c₂) ns ws
      (1.5 * smallEigOmega nmax S δ φ c₁ c₂) (smallEigDecoupleError nmax S δ φ c₂ u)
      (smallEigDecoupler (O := O) (Q := Q) sG) I := by
  intro n N w q f lg H V d hk hnb hN hH hHN hV hHV hκ hgap
  have hnn : n ≤ nmax := hnb.trans hkb
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hφD : 0 < smallEigDecouplerFailure nmax φ := by unfold smallEigDecouplerFailure; positivity
  have hsteps : smallEigDecoupleSteps nmax S δ φ c₂ ≤ smallEigCap nmax S δ φ c₁ c₂ :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hRH := smallEigDecoupler_rhess_pwrites (O := O) (Q := Q) (w := w) (lg := lg) hS hM hzero
    hC hL hSmp hG hb₁ hb₂ hn hNat hδ hδS hφ hφ1 hu (by omega) hnn (by omega) hN hHN hV hHV hκ
    hgap (ns := ns) (ws := ws) (by omega) (by omega)
  have hget : ∀ μ : Mem ℝ, μ.store.readBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length =
      some (smallEigParams nmax S δ φ c₁ c₂) → ∀ i < 12,
        μ.store.get q.1 (q.2 + i) = some ((smallEigParams nmax S δ φ c₁ c₂).getD i 0) :=
    fun μ hq i hi => Store.get_of_readBlock hq (by simp [smallEigParams]; omega) 0
  unfold smallEigDecoupler
  refine PWrites.bindIdx_of_index_eq hI rfl rfl (le_max_left _ _) (fun μ hμ =>
    hQ.index_eq_of_decode_nat (hget μ hμ.2.1 8 (by omega)) (by simp [smallEigParams])) hφD.le ?_
  refine PWrites.bindIdx_of_index_eq hI rfl rfl Nat.lt_two_pow_self.le (fun μ hμ =>
    hQ.index_eq_of_decode_nat (hget μ hμ.2.1 9 (by omega)) (by simp [smallEigParams])) hφD.le ?_
  refine PWrites.bindIdx_of_index_eq hI rfl rfl ((le_max_left _ _).trans (le_max_right _ _))
    (fun μ hμ => hQ.index_eq_of_decode_nat (hget μ hμ.2.1 10 (by omega))
      (by simp [smallEigParams])) hφD.le ?_
  refine PWrites.bindIdx_of_index_eq hI rfl rfl hsteps
    (fun μ hμ => hQ.index_eq_of_decode_nat (hget μ hμ.2.1 11 (by omega))
      (by simp [smallEigParams])) hφD.le ?_
  change PWrites law I (Stmt.allocs [.const 2] _) _ _ _ _ _
  refine PWrites.allocs (ns := [2]) rfl
    (Pre₁ := fun L μ => SmallEigDecouplerAlloc H (smallEigParams nmax S δ φ c₁ c₂) w q f lg ns ws
      L μ)
    (fun μ s₁ ⟨hW, hq, hl, hlgb, hwr, hfr, hlgr, hA, hqd⟩ hlen hlens hBelow =>
      SmallEigDecouplerAlloc.of_alloc (by simp [smallEigParams]) hW hq hl hlgb hwr hfr hlgr hA hqd
        (by simpa using hlen) (by simpa using hlens 0 (by simp)) hBelow) ?_ fun L => ?_
  · rintro μ ⟨-, -, hl, -⟩ s s' p hBelow ⟨hf0, H', L', hL', hpl, hlog, hby, h2, h3, hW'⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl
    exact ⟨hBelow.get_of hl.2.2.2.1 hf0, H', L', hL', hpl,
      hBelow.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
        (fun b i g => by rw [g.1]; exact hl.2.2.2.2) hlog, hby, h2, h3, hW'.of_below hBelow hl.1⟩
  -- the body: open the log, `RHess`, then the tail
  let ι := {p : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ × List (Option (List GivensEntry)) //
    p.2.length = k + 1 ∧ (∀ e ∈ slotEntries ws p.2, e.1 + 1 < k + 1 + 1) ∧
    SmallEigRHessClass nmax S δ φ c₁ c₂ H (200 * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 * u * N)
      (givensLog (k + 1 + 1) (slotEntries ws p.2)) p.1}
  refine (PWrites.seq (Mid := SmallEigDecouplerOpened H (smallEigParams nmax S δ φ c₁ c₂) w q f lg
      ns ws L) (φ₂ := smallEigDecouplerFailure nmax φ / 2 + smallEigDecouplerFailure nmax φ / 2)
      hI hloc (by positivity) (PWrites.of_writes (F := Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
        le_rfl fun μ τ hμ => smallEigDecoupler_open_writes hS hM rfl rfl hμ)
    (PWrites.seq (Mid := fun μ => ∃ x : ι, SmallEigTailInput x.1.1
      (smallEigParams nmax S δ φ c₁ c₂) w q f lg L ns ws x.1.2 μ)
      (F₂ := (Store.inBlock L 0 2 ⊔ Store.inBlock f.1 f.2 1 ⊔
      (Store.inBlock w.1 w.2 (2 * ((k + 1 + 1) * (k + 1 + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))))
      (φ₂ := smallEigDecouplerFailure nmax φ / 2) hI hloc (by positivity) ((hRH.mono_eqOff
        (fun μ hμ => ⟨hμ.1, hμ.2.1, hμ.2.2.1, hμ.2.2.2.1, hμ.2.2.2.2.1⟩)
        (fun μ μ' hμ hfr ⟨H₁, Ls, hW₁, hLs, hpl, hlog, hx⟩ =>
          ⟨⟨(H₁, Ls), hLs, hpl, hx⟩, hμ.tailInput hfr hW₁ hlog⟩)).in_frame rfl rfl
        (fun μ hμ => hμ.live)) ?_)).mono (fun _ h => h) (by fp_sub) (fun _ h => h) (by linarith)
  refine PStep.mono (PWrites.pstep_of_forall hI hloc
    (F := (Store.inBlock L 0 2 ⊔ Store.inBlock f.1 f.2 1 ⊔
      (Store.inBlock w.1 w.2 (2 * ((k + 1 + 1) * (k + 1 + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))))
    (P := fun (x : ι) μ => SmallEigTailInput x.1.1 (smallEigParams nmax S δ φ c₁ c₂) w q f lg L
      ns ws x.1.2 μ)
    (fun x => smallEigDecoupler_tail_pwrites (O := O) (Q := Q) hS hM hL hC hI hloc hDisk hU hb₁
      hb₂ hn hδ hδS hφ hφ1 hu hnn (hNat.mono (by omega)) hHN hN x.2.1 x.2.2.1 x.2.2.2
      (by omega) (by omega) rfl rfl rfl rfl rfl)
    (measurableSet_decoupleOutcomeBy H (smallEigDecoupleError nmax S δ φ c₂ u N)
      (1.5 * smallEigOmega nmax S δ φ c₁ c₂) w f lg ns ws
      (Store.inBlock L 0 2 ⊔ Store.inBlock f.1 f.2 1 ⊔
      (Store.inBlock w.1 w.2 (2 * ((k + 1 + 1) * (k + 1 + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws))))) ?_) (fun μ h => h) ?_ le_rfl
  · rintro x μ μ' - hfr ⟨hf0, H', L', hL', hpl, hlog, hby, hHess, hsm, hW'⟩
    rw [hW'.eq_storedMatrix] at hby hHess hsm
    rw [hlog.slotEntries_read hL'] at hby
    exact ⟨hfr, hf0, fun i hi => by rw [Store.get_of_readBlock hW' hi 0]; rfl, hby, hHess, hsm,
      L', hL', hpl, by simpa using hlog⟩
  · rintro μ μ' - ⟨hfr, hf0, hinit, hby, hHess, hsm, L', hL', hpl, hlog⟩
    have hlog' : HoldsSlottedLog lg ns ws L' [] μ'.store := by simpa using hlog
    rw [← hlog'.slotEntries_read hL'] at hby
    exact ⟨hfr, hf0, _, L', hL', hpl, hlog', hby, hHess, hsm, holdsMatrix_storedMatrix hinit⟩

/-- **The decoupler meets the randomized decoupling contract** ([BanksGarzaVargasSrivastava2025,

Theorem 6.1], one node; [BanksGarzaVargasSrivastava2025, Lemma 6.2] carried by the composition):
on a scalar machine with the standard model at $\boldsymbol{u} \le$
`NLAlib.SmallEig.uSmallEig`, $M.\mathrm{lit}(0) = 0$, index literals, exact natural literals up to
$n_{\max} + 1$, exact comparisons and conversion, a measurable interpretation reading the tape
only in its windows whose draws store the tape entry, a stream `sG` with the standard real
Gaussian law and an exact polar sampler on a stream `sU` uniform on $[0, 1]$: for tail records
with $b_1, b_2 > 0$, $1 \le n_{\max}$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$,
`NLAlib.SmallEig.smallEigDecoupler` with the words `NLAlib.SmallEig.smallEigParams` and the cap
`NLAlib.SmallEig.smallEigCap` meets `NLAlib.ShiftedQR.RandomDecouplingRoutineContract` at the
bottom width $1$, any iteration cap, orders up to $n_{\max}$ and norms up to $2\Sigma$, on the
class $(2B_c, g_c/2)$ of the blocks ($B_c, g_c$ = `NLAlib.SmallEig.smallEigCondition`,
`NLAlib.SmallEig.smallEigSeparation`), with failure probability $\varphi_D$ =
`NLAlib.SmallEig.smallEigDecouplerFailure`, the level $1.5\,\omega$ and the backward error
`NLAlib.SmallEig.smallEigDecoupleError`. -/
theorem smallEigDecoupler_randomDecouplingRoutineContract {M : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} (hS : IsScalar M I) (hM : StdModel u id M) (hzero : M.lit 0 = 0)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M (nmax + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) (F : ℕ) {ns ws : ℕ}
    (hns : nmax + smallEigCap nmax S δ φ c₁ c₂ ≤ ns) (hws : nmax ≤ ws) :
    RandomDecouplingRoutineContract law (2 * smallEigCondition nmax S δ φ c₂)
      (smallEigSeparation nmax S δ φ c₁ / 2) (smallEigDecouplerFailure nmax φ) 1 F
      (smallEigCap nmax S δ φ c₁ c₂) nmax (2 * S) (smallEigParams nmax S δ φ c₁ c₂) ns ws
      (1.5 * smallEigOmega nmax S δ φ c₁ c₂) (smallEigDecoupleError nmax S δ φ c₂ u)
      (smallEigDecoupler (O := O) (Q := Q) sG) I :=
  smallEigDecoupler_randomDecouplingRoutineContract_of_le hS hM hzero hL le_rfl hNat hC hQ hI hloc
    hSmp hDisk hU hG hb₁ hb₂ hn hδ hδS hφ hφ1 hu F hns hws

/-- The decoupler terminates: on a scalar machine with index literals, exact natural literals
up to $n_{\max} + 1$, exact comparisons and conversion, draws that store the tape entry and an
exact polar sampler, for words `qs` with valid cap words for the cap $T$
(`NLAlib.SmallEig.SmallEigCaps`), at least twelve words and a log of $n_s \ge n_{\max} + T$
slots of $w_s \ge n_{\max}$ entries, `NLAlib.SmallEig.smallEigDecoupler` is a terminating
decoupling routine (`NLAlib.ShiftedQR.TerminatingDecouplerRoutine`) at the bottom width $1$, any
iteration cap and orders up to $n_{\max} + 1$. -/
theorem smallEigDecoupler_terminatingDecouplerRoutine {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M (nmax + 1))
    (hC : IsCmp id I) (hQ : IsToNat id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {T F : ℕ} {qs : List ℝ} (hqs : SmallEigCaps T qs)
    (hlen : 12 ≤ qs.length) {ns ws : ℕ} (hns : nmax + T ≤ ns) (hws : nmax ≤ ws) :
    TerminatingDecouplerRoutine nmax 1 F T qs ns ws (smallEigDecoupler (O := O) (Q := Q) sG) I :=
  by
  intro n w q f lg tape μ H hk hn hW hq hl hwr hfr hlgr hne hA hqd
  obtain ⟨m, qq, t, m₂, h8, h9, h10, h11, hmq, hmT, htT, hm2T⟩ := hqs
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hget : ∀ i < qs.length, μ.store.get q.1 (q.2 + i) = some (qs.getD i 0) :=
    fun i hi => Store.get_of_readBlock hq hi 0
  have hlg1 : lg.1 < μ.store.length := hl lg (by simp)
  have hf1 : f.1 < μ.store.length := hl f (by simp)
  have hw1 : w.1 < μ.store.length := hl w (by simp)
  have hqm : qq ≤ m := hmq ▸ Nat.lt_two_pow_self.le
  have hzero : M.lit 0 = 0 := by simpa using hNat 0 (by omega)
  unfold smallEigDecoupler
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 8 (by omega)) (by simpa using h8) hmT ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 9 (by omega)) (by simpa using h9) hqm ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 10 (by omega)) (by simpa using h10) htT ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 11 (by omega)) (by simpa using h11) hm2T ?_
  change Writes .total I tape (Stmt.allocs [.const 2] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2]) rfl (fun hBelow ⟨⟨x, hx⟩, ⟨H', hH'⟩, Ls, hLs,
    hpl, hlog⟩ => ⟨⟨x, hBelow.get_of hf1 hx⟩, ⟨H', hH'.of_below hBelow hw1⟩, Ls, hLs, hpl,
      hBelow.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
        (fun b i g => by rw [g.1]; exact hlg1) hlog⟩) ?_
  intro s₁ hlen₁ hlens hBelow
  obtain ⟨hin₀, hlgl₀, hlgr₀, hne'⟩ := SmallEigDecouplerAlloc.of_alloc (by omega) hW hq hl hne hwr
    hfr hlgr hA hqd (by simpa using hlen₁) (by simpa using hlens 0 (by simp)) hBelow
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen₁
  refine (slottedLogOpen_writes_of_lit_zero (τ := tape) (μ := ⟨s₁, μ.pos⟩) hS hzero
    hlgr₀).frame_seq_le rfl rfl hlgl₀
    (fun b i hb => Or.inl (Or.inr hb)) ?_
  rintro μ₀ hfr₀ ⟨-, hlog₀⟩
  have hin₀' := hin₀.of_eqOff hfr₀ (Fp.disj_inBlock_of_ne (hne' q (by simp)).symm)
    (hin₀.2.2.2.1.of_eqOff hfr₀ (Fp.disj_inBlock_of_ne (hne' w (by simp)).symm))
  refine (rhess_terminates (τ := tape) (μ := μ₀) (sG := sG) hS hC hSmp
    (fun x hx => hin₀'.1 x (by simp at hx ⊢; tauto)) hin₀'.2.2.2.1 hL
    (hNat.mono (by omega) : IsExactNatLit id M nmax) (by omega) (by omega) (by omega) hlog₀
    (by simp; omega) (by omega) (by simp [Mem.Live, hfr₀.length_eq]; omega)
    (hne' w (by simp)).symm).frame_seq_le rfl rfl
    (by simp [Mem.Live, hfr₀.length_eq]; omega) (by fp_sub) ?_
  rintro μ₁ hfr₁ ⟨H₁, hH₁, Ls₁, hLs₁, hpl₁, hlog₁⟩
  simp only [List.nil_append] at hlog₁
  have hin₁ : OneEigInput H₁ qs w q (L, 0) f μ₁ :=
    hin₀'.of_eqOff hfr₁ (Fp.disj_sup_left.mpr ⟨hin₀'.disj_words,
      Fp.disj_inBlock_of_ne (hne' q (by simp)).symm⟩) hH₁
  refine (oneEig_terminates (m := m) (q := qq) (t := t) hS hzero hL hC hDisk
    (hNat.mono (by omega)) (by omega) hin₁).frame_seq_le rfl rfl hin₁.1 (by fp_sub) ?_
  rintro μ₂ hfr₂ ⟨⟨z, hz⟩, x, hx⟩
  have hdin : DecoupleInput H₁ z qs w (L, 0) q f μ₂ := hin₁.decoupleInput_of_eqOff hfr₂ hz
  have hlog₂ : HoldsSlottedLog lg ns ws Ls₁ [] μ₂.store :=
    hfr₂.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
      (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (hne' (L, 0) (by simp)),
        Fp.disj_inBlock_of_ne (hne' f (by simp))⟩) hlog₁
  have hlgl₂ : μ₂.Live [lg] := by
    simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq, hfr₀.length_eq]; omega
  refine writes_ite (a := [f]) rfl rfl (hC.test_isZero hx) ?_
  split_ifs
  · refine ((decoupleLast_terminates (n := n') (m₂ := m₂) hS hL hC (hNat.mono (by omega))
      (by omega) hdin hlog₂ (by omega) (by omega) hlgl₂ (fun b hb => hne' b (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢; tauto))).in_frame
      (by simp [hLs₁]) rfl (fun x hx => by
        have hd := hdin.1
        have hlgl' := hlgl₂
        simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] at hd hlgl' hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        exacts [hd.1, hd.2.1, hd.2.2.1, hd.1, hd.2.2.2, hlgl'])).mono (by fp_sub) ?_
    rintro μ₃ - ⟨⟨H₃, hH₃⟩, y, hy, Ls₂, hLs₂, hpl₂, hlog₃⟩
    refine ⟨⟨y, hy⟩, ⟨H₃, hH₃⟩, Ls₁ ++ Ls₂ ++ List.replicate (ns - Ls₁.length - Ls₂.length) none,
      by simp; omega, fun e he => ?_, hlog₃.rejects (by simp; omega)⟩
    simp only [slotEntries_append, slotEntries_replicate_none, List.append_nil,
      List.mem_append] at he
    rcases he with he | he
    exacts [hpl₁ e he, hpl₂ e he]
  · refine (Writes.skip ⟨⟨x, hx⟩, ⟨H₁, hH₁.of_eqOff hfr₂ hin₁.disj.1⟩,
      Ls₁ ++ List.replicate (ns - Ls₁.length) none, by simp; omega, fun e he => ?_,
      hlog₂.rejects (by omega)⟩).mono bot_le fun _ _ h => h
    simp only [slotEntries_append, slotEntries_replicate_none, List.append_nil] at he
    exact hpl₁ e he

end Theorems

end NLAlib.SmallEig
