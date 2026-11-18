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

/-!
# The decoupler of the small-eigenvalue solver

One node of the deflation of [BanksGarzaVargasSrivastava2025, §6] (the paper's `Eig` on a block,
with `RHess` at every node, decision D7 of the design): `RHess` makes the last-row weights large,
`OneEig` finds a shift within $\beta' = \omega/20$ of an eigenvalue and at least $\eta_1$ away from
the spectrum, and `Decouple` makes the last subdiagonal entry at most $\omega$. As the decoupler of
the rounded worklist at the bottom width $k = 1$ it meets the randomized decoupling contract on the
class of the blocks; Lemma 6.2's preservation of the class is carried by the composition of the
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
def smallEigDecoupler (sG : ℕ) : Impl O Q :=
  opsImpl% [N, k, np, F, T, ns, w] (W, P) → (W, Fl, Lg) {
  let m ← index (Has.inj IdxTst.toNat) (P[8]) ≤ T;
  let q ← index (Has.inj IdxTst.toNat) (P[9]) ≤ m;
  let t ← index (Has.inj IdxTst.toNat) (P[10]) ≤ T;
  let m2 ← index (Has.inj IdxTst.toNat) (P[11]) ≤ T;
  let Lam ← alloc 2;
  run (slottedLogOpen (O := O) (Q := Q)).body [ns, w] (Lg);
  run (rhess (O := O) (Q := Q) sG).body [N, w, 0] (W, W, Lg);
  run (oneEig (O := O) (Q := Q)).body [N, m, q, t] (W, P, Lam, Fl);
  if (Has.inj CmpTst.isZero) [] (Fl) {
    run (decoupleLast (O := O) (Q := Q)).body [N, m2, w, N - 1] (W, Lam, P, W, Fl, Lg)
  } else { skip }
}

end Program

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- The outcomes of a decoupling call on a fixed block $\mathbf{H}$, as pairs of a memory before
and after: the frame `F`, the flag $0$, an initialised work matrix, and the matrix read after is an
upper Hessenberg perturbed unitary similarity of $\mathbf{H}$ with error $\varepsilon$ whose last
subdiagonal entry has modulus at most $\omega$. They form a measurable set. -/
theorem measurableSet_decoupleOutcome_of {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ε ω : ℝ) (w f : ℕ × ℕ) (F : Fp) :
    MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧
      x.2.store.get f.1 f.2 = some 0 ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (x.2.store.get w.1 (w.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilar H (storedMatrix w (n + 1) (n + 1) x.2.store) ε ∧
      IsUpperHessenberg (storedMatrix w (n + 1) (n + 1) x.2.store) ∧
      ∃ i : Fin n, n ≤ (i : ℕ) + 1 ∧
        ‖storedMatrix w (n + 1) (n + 1) x.2.store i.succ i.castSucc‖ ≤ ω} := by
  have hm : Measurable fun x : Mem ℝ × Mem ℝ => storedMatrix w (n + 1) (n + 1) x.2.store :=
    (measurable_storedMatrix w (n + 1) (n + 1)).comp measurable_snd
  have hent (i j : Fin (n + 1)) : Measurable fun x : Mem ℝ × Mem ℝ =>
      storedMatrix w (n + 1) (n + 1) x.2.store i j :=
    (Matrix.measurable_apply i j).comp hm
  simp only [Set.ofPred_and]
  refine (Mem.measurableSet_eqOff F).inter ((measurable_snd (Mem.measurableSet_get_eq f 0)).inter
    ((measurable_snd (measurableSet_forall_isSome w _)).inter
      (((isClosed_setOf_isPerturbedUnitarySimilar ε).measurableSet.preimage
        (measurable_const.prodMk hm)).inter ((?_ : MeasurableSet _).inter ?_))))
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
omit [Has SampleOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- The blocks after `RHess` inside the decoupler: $\mathbf{H}_1$ is upper Hessenberg, a perturbed
unitary similarity of the block $\mathbf{H}$ with the error $\varepsilon$, and has a diagonalization
with condition at most $4B_c$, separation $g_c/4$ and last-row weights at least $p$. -/
def SmallEigRHessClass (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ε : ℝ) (H₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Prop :=
  IsUpperHessenberg H₁ ∧ IsPerturbedUnitarySimilar H H₁ ε ∧
    ∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
      IsUnit V ∧ H₁ * V = V * Matrix.diagonal d ∧
      pseudoConditionNumber V ≤ 4 * smallEigCondition nmax S δ φ c₂ ∧
      (∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ / 4 ≤ ‖d i - d j‖) ∧
      ∀ i, smallEigWeight nmax S δ φ c₂ ≤ lastRowWeights V i

omit [Has IndexOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
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

/-- The decoupler meets the randomized decoupling contract at a smaller order bound
(`NLAlib.SmallEig.smallEigDecoupler_randomDecouplingRoutineContract` with the words still at
$n_{\max}$): the contract holds at orders up to $k_b \le n_{\max}$ when the natural literals are
exact up to $k_b + 1$ only. -/
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
    (hns : nmax + smallEigCap nmax S δ φ c₁ c₂ ≤ ns) (hws : nmax ≤ ws) :
    RandomDecouplingRoutineContract law (2 * smallEigCondition nmax S δ φ c₂)
      (smallEigSeparation nmax S δ φ c₁ / 2) (smallEigDecouplerFailure nmax φ) 1 F
      (smallEigCap nmax S δ φ c₁ c₂) kb (2 * S) (smallEigParams nmax S δ φ c₁ c₂) ns ws
      (1.5 * smallEigOmega nmax S δ φ c₁ c₂) (smallEigDecoupleError nmax S δ φ c₂ u)
      (smallEigDecoupler (O := O) (Q := Q) sG) I := sorry

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
      (smallEigDecoupler (O := O) (Q := Q) sG) I := sorry

/-- The decoupler terminates: on a scalar machine with index literals, exact natural literals
up to $n_{\max} + 1$, exact comparisons and conversion, draws that store the tape entry and an
exact polar sampler, for words `qs` with valid cap words for the cap $T$
(`NLAlib.SmallEig.SmallEigCaps`) and at least twelve words, `NLAlib.SmallEig.smallEigDecoupler`
is a terminating decoupling routine (`NLAlib.ShiftedQR.TerminatingDecouplerRoutine`) at the
bottom width $1$, any iteration cap and orders up to $n_{\max} + 1$. -/
theorem smallEigDecoupler_terminatingDecouplerRoutine {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M (nmax + 1))
    (hC : IsCmp id I) (hQ : IsToNat id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {T F : ℕ} {qs : List ℝ} (hqs : SmallEigCaps T qs)
    (hlen : 12 ≤ qs.length) {ns ws : ℕ} (hns : nmax + T ≤ ns) (hws : nmax ≤ ws) :
    TerminatingDecouplerRoutine nmax 1 F T qs ns ws (smallEigDecoupler (O := O) (Q := Q) sG) I :=
  sorry

end Theorems

end NLAlib.SmallEig
