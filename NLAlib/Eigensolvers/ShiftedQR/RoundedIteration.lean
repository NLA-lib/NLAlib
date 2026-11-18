/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedRegularize
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSh
public import NLAlib.Eigensolvers.ShiftedQR.RoundedShStep

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

* `NLAlib.ShiftedQR.shIterationWith_pwrites_at`, `NLAlib.ShiftedQR.shIteration_pwrites`: one
  iteration as a probabilistic block.
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
def shIterationWithScratchWith (SE : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, n0, nq, T, w, j0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw, S) → (A, Fl, Lg) {
    run (regularizeWith SE).body [N, k, nq, T, w, j0] (A, Rd, C, Thr, Qw, A, S, Fl, Lg);
    if (Has.inj CmpTst.isZero) [] (Fl) {
      run (shStep (O := O) (Q := Q)).body [N, m, k, n0, w, j0 + k]
        (A, S, Cg, Cr, Cw, Cp, G, Thr, A, Fl, Lg)
    } else { skip }
  }

/-- **One iteration of the decoupling loop with a small-eigenvalue routine**
([BanksGarzaVargasSrivastava2022, Lemma 6.4], the body of the loop): `Regularize` with the
routine `SE`, then `Sh` with its shifts if they are optimal. The scratch for the $k$ shift pairs
is scoped; the rotations go to the slots $j_0, \dots, j_0 + k + n_0$ of the log `Lg`. The
interface is `[N, m, k, n0, nq, T, w, j0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw) → (A, Fl, Lg)`. -/
def shIterationWith (SE : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, n0, nq, T, w, j0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw) → (A, Fl, Lg) {
    let S ← alloc (2 * k);
    run (shIterationWithScratchWith SE).body [N, m, k, n0, nq, T, w, j0]
      (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw, S, A, Fl, Lg)
  }

/-- **One iteration of the decoupling loop** ([BanksGarzaVargasSrivastava2022, Lemma 6.4], the
body of the loop): `NLAlib.ShiftedQR.shIterationWith` with the `SmallEig` kernel
(`NLAlib.ShiftedQR.smallEigKernel`), no words and the cap $0$: `Regularize`, then `Sh` with its
shifts if they are optimal, recording the rotations in the slots $j_0, \dots, j_0 + k + n_0$ of
the log `Lg`. The interface is `[N, m, k, n0, w, j0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G) →
(A, Fl, Lg)`. -/
def shIteration : Impl O Q :=
  opsImpl% [N, m, k, n0, w, j0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G) → (A, Fl, Lg) {
    run (shIterationWith (smallEigKernel (O := O) (Q := Q))).body [N, m, k, n0, 0, 0, w, j0]
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
          c * hessenbergPotential k (storedMatrix a (n + 1) (n + 1) x.1.store))} := sorry

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
          1.002 * (1 - γ) * hessenbergPotential k (storedMatrix a (n + 1) (n + 1) m.store)) := sorry

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
(`NLAlib.ShiftedQR.measurableSet_iterationOutcome`). -/
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
    PWrites law I (shStep (O := O) (Q := Q)).body
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
          ∀ j, ‖zs j‖ ≤ 1.1 * specNorm H ∧
        HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg])
      (ShIterationOutcomeBy u k H γ tv
          ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))
        a lg ns w LL (1 + (excNet ε).length)) φ := sorry

variable [Has EigenvalueKernelOp O]

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The hypothesis lists of `Regularize` and the kept words of `Sh` make elaboration heavy.
omit [Has IdxTst Q] [Has EigenvalueKernelOp O] in
/-- `Regularize` with a small-eigenvalue routine inside an iteration: the outcome of
`NLAlib.ShiftedQR.regularizeWith_pwrites_at`, with the words of `Sh` kept. -/
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
    {nq T : ℕ} {qs : List ℝ} {SE : Impl O Q} {qw : ℕ × ℕ}
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
    PWrites law I (.frame ds args (regularizeWith SE).body) ρ
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
      (φse + φ / 2) := sorry

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

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The hypothesis lists of `Regularize` and `Sh` together, with their long real constants, make
-- the elaboration of the composition heavy.
omit [Has EigenvalueKernelOp O] in
/-- One iteration with caller-owned scratch as a probabilistic block: the hypotheses of
`NLAlib.ShiftedQR.shIteration_pwrites`, with the $k$ shift pairs at `s` apart from the other
views. -/
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
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) {nq T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContractAt law β φse k nq T S qs SE I) {qw : ℕ × ℕ}
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
        (hj : LL.length + (k + 1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ w)
    (hlgv : ∀ b ∈ [a, rd, c, thr, wg, wr, ww, wp, g, qw, s, f], b.1 ≠ lg.1) :
    PWrites law I (shIterationWithScratchWith SE).body
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
        a lg ns w LL (k + 1 + (excNet ε).length)) (φse + φR / 2 + φ) := sorry
-- The hypothesis lists of `Regularize` and `Sh` together, with their long real constants, make
-- the elaboration of the composition heavy.
set_option maxHeartbeats 1000000 in
omit [Has EigenvalueKernelOp O] in
/-- **One rounded iteration with a small-eigenvalue routine as a probabilistic block**, with the
word count `nq` apart from the words `qs` (`NLAlib.ShiftedQR.RandomSmallEigContractAt`), the
words stored at `qw` apart from the matrix and the flag: `NLAlib.ShiftedQR.shIteration_pwrites`
for `NLAlib.ShiftedQR.shIterationWith`. One rounded iteration of the decoupling loop as a
probabilistic block
([BanksGarzaVargasSrivastava2022, Lemma 6.4], one round, corrected: the dichotomy constant of
Theorem 4.1 is $\tfrac12 k^{-1/(2k)}$ for the printed $(2k)^{-1/(2k)}$, and the test in the proof
of Lemma 4.6 is $\psi_k \ge \varepsilon$; the net of `Exc`, Lemma 5.3, has rounding at most
$0.005\varepsilon\widetilde{R}$, covers $\mathbb{D}(r, (1 + \varepsilon)\widetilde{R})$ and has
at most $11$ points near an eigenvalue, and its radius keeps the factor $2^{1/k}$ the paper omits
($2.002^{1/k}$ for $1.001$, so the shift bound is $4.1\|\mathbf{H}\|_2$ for $3\|\mathbf{H}\|_2$);
`Sh`, Lemma 5.4, returns the computed step, assumes $\|\mathbf{H}\|_2 \le \Sigma$ and $k \ge 2$,
and reports with a flag that no shift was accepted; the precision of `Optimal`, Lemma 4.5,
carries $n + kn^{3/2}$ for the printed $2n^2$): on a scalar machine with the standard model, exact
comparisons, index literals, index conversion and exact natural literals up to $n + 1$, a
measurable tape-local interpretation whose `SmallEig` is a randomized kernel with forward error
$\beta \ge 0$ and failure probability $\varphi_{\mathrm{se}} \ge 0$ on a stream `s₀` uniform on
$[0, 1]$, and an exact polar disk sampler on the same stream: let $\mathbf{H}$ be upper Hessenberg
of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with
$\kappa(\mathbf{V}) \le B$, $B^{2/k} \le 2$, $2 \le k = 2^m \le n$, $\|\mathbf{H}\|_2 \le
\Sigma$, $0 < \omega \le \psi_k(\mathbf{H})$, eigenvalues separated by $2\omega^2/\Sigma$; the words
of `Regularize` (radius $R > 0$, $0.999\theta^k$ for
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, the threshold $t \ge (1 + \boldsymbol{u})^2
\omega^2$) with $0 < \varphi_R \le 1$, $\eta = R\sqrt{\varphi_R/(2k)}$ and $d = \eta/2$, and the
words of `Sh` ($(1 - \gamma)^k$, $2^{1/k}\theta\alpha B^{1/k}$, $\varepsilon/2$,
$1.0015(1 - \gamma)$,
the net `NLAlib.ShiftedQR.excNet ε`) with $\alpha = (1.01B)^{4m/2^m}$, $0 < \gamma < 1$,
$\varepsilon = (0.998(1 - \gamma)^2/((13B^4)^{1/k}\alpha^2\theta^2))^{k/(k-1)} \le 1/2$,
$0 < \varphi \le 1/5$, $1.1 + 2.1 \cdot 2.002^{1/k}\theta\alpha B^{1/k} \le C$,
$d \le \varepsilon \cdot 1.998^{1/k}\theta\alpha B^{1/k}\omega\sqrt{\varphi/(11(n + 1))}/4$; and the
precision conditions of `Regularize` and `Sh`, those of `Sh` that involve $\psi_k(\mathbf{H})$
asked at $\omega$ (below) and at $\Sigma$ (above). Then `NLAlib.ShiftedQR.shIteration` writes only
the matrix and the flag and, except with probability at most
$\varphi_{\mathrm{se}} + \varphi_R/2 + \varphi$, ends in `NLAlib.ShiftedQR.ShIterationOutcome`: an
upper Hessenberg perturbed unitary similarity of $\mathbf{H}$ with error
$(1 + C)\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$, decoupled at the bottom
or with $\psi_k \le 1.002(1 - \gamma)\psi_k(\mathbf{H})$. -/
theorem shIterationWith_pwrites_at {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ}
    (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse) (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k q : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    (hkn : k ≤ n) {ε : ℝ} {a rd c thr wg wr ww wp g f : ℕ × ℕ}
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
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
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) {nq T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContractAt law β φse k nq T S qs SE I) {qw : ℕ × ℕ}
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
        (hj : LL.length + (k + 1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ w)
    (hlgv : ∀ b ∈ [a, rd, c, thr, wg, wr, ww, wp, g, qw, f], b.1 ≠ lg.1) :
    PWrites law I (shIterationWith SE).body
      (Env.frame [n + 1, q, k, (excNet ε).length, nq, T, w, LL.length]
        [a, rd, c, thr, wg, wr, ww, wp, g, qw, a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => m.Live [a, rd, c, thr, wg, wr, ww, wp, g, qw, f] ∧ HoldsMatrix a H m.store ∧
        m.store.readBlock qw.1 qw.2 qs.length = some qs ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ m.store.get wg.1 wg.2 = some ((1 - γ) ^ k) ∧
        m.store.get wr.1 wr.2 = some ((2 : ℝ) ^ ((k : ℝ)⁻¹) *
          ((1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
            B ^ ((k : ℝ)⁻¹))) ∧
        m.store.get ww.1 ww.2 = some (ε / 2) ∧ m.store.get wp.1 wp.2 = some (1.0015 * (1 - γ)) ∧
        m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧ f.2 < m.store.len f.1 ∧
        HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg])
      (ShIterationOutcomeBy u k H γ tv
          ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))
        a lg ns w LL (k + 1 + (excNet ε).length)) (φse + φR / 2 + φ) := sorry
-- The hypothesis lists of `Regularize` and `Sh` together, with their long real constants, make
-- the elaboration of the composition heavy.
set_option maxHeartbeats 1000000 in
/-- **One rounded iteration of the decoupling loop as a probabilistic block**
([BanksGarzaVargasSrivastava2022, Lemma 6.4], one round, corrected: the dichotomy constant of
Theorem 4.1 is $\tfrac12 k^{-1/(2k)}$ for the printed $(2k)^{-1/(2k)}$, and the test in the proof
of Lemma 4.6 is $\psi_k \ge \varepsilon$; the net of `Exc`, Lemma 5.3, has rounding at most
$0.005\varepsilon\widetilde{R}$, covers $\mathbb{D}(r, (1 + \varepsilon)\widetilde{R})$ and has
at most $11$ points near an eigenvalue, and its radius keeps the factor $2^{1/k}$ the paper omits
($2.002^{1/k}$ for $1.001$, so the shift bound is $4.1\|\mathbf{H}\|_2$ for $3\|\mathbf{H}\|_2$);
`Sh`, Lemma 5.4, returns the computed step, assumes $\|\mathbf{H}\|_2 \le \Sigma$ and $k \ge 2$,
and reports with a flag that no shift was accepted; the precision of `Optimal`, Lemma 4.5,
carries $n + kn^{3/2}$ for the printed $2n^2$): on a scalar machine with the standard model, exact
comparisons, index literals, index conversion and exact natural literals up to $n + 1$, a
measurable tape-local interpretation whose `SmallEig` is a randomized kernel with forward error
$\beta \ge 0$ and failure probability $\varphi_{\mathrm{se}} \ge 0$ on a stream `s₀` uniform on
$[0, 1]$, and an exact polar disk sampler on the same stream: let $\mathbf{H}$ be upper Hessenberg
of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with
$\kappa(\mathbf{V}) \le B$, $B^{2/k} \le 2$, $2 \le k = 2^m \le n$, $\|\mathbf{H}\|_2 \le
\Sigma$, $0 < \omega \le \psi_k(\mathbf{H})$, eigenvalues separated by $2\omega^2/\Sigma$; the words
of `Regularize` (radius $R > 0$, $0.999\theta^k$ for
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, the threshold $t \ge (1 + \boldsymbol{u})^2
\omega^2$) with $0 < \varphi_R \le 1$, $\eta = R\sqrt{\varphi_R/(2k)}$ and $d = \eta/2$, and the
words of `Sh` ($(1 - \gamma)^k$, $2^{1/k}\theta\alpha B^{1/k}$, $\varepsilon/2$,
$1.0015(1 - \gamma)$,
the net `NLAlib.ShiftedQR.excNet ε`) with $\alpha = (1.01B)^{4m/2^m}$, $0 < \gamma < 1$,
$\varepsilon = (0.998(1 - \gamma)^2/((13B^4)^{1/k}\alpha^2\theta^2))^{k/(k-1)} \le 1/2$,
$0 < \varphi \le 1/5$, $1.1 + 2.1 \cdot 2.002^{1/k}\theta\alpha B^{1/k} \le C$,
$d \le \varepsilon \cdot 1.998^{1/k}\theta\alpha B^{1/k}\omega\sqrt{\varphi/(11(n + 1))}/4$; and the
precision conditions of `Regularize` and `Sh`, those of `Sh` that involve $\psi_k(\mathbf{H})$
asked at $\omega$ (below) and at $\Sigma$ (above). Then `NLAlib.ShiftedQR.shIteration` writes only
the matrix and the flag and, except with probability at most
$\varphi_{\mathrm{se}} + \varphi_R/2 + \varphi$, ends in `NLAlib.ShiftedQR.ShIterationOutcome`: an
upper Hessenberg perturbed unitary similarity of $\mathbf{H}$ with error
$(1 + C)\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$, decoupled at the bottom
or with $\psi_k \le 1.002(1 - \gamma)\psi_k(\mathbf{H})$. -/
theorem shIteration_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ} (hSE : IsRandomSmallEig law s₀ β φse I)
    (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse) (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k q : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    (hkn : k ≤ n) {ε : ℝ} {a rd c thr wg wr ww wp g f : ℕ × ℕ}
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
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
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
        (hj : LL.length + (k + 1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ w)
    (hlgv : ∀ b ∈ [a, rd, c, thr, wg, wr, ww, wp, g, f], b.1 ≠ lg.1) :
    PWrites law I (shIteration (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length, w, LL.length]
          [a, rd, c, thr, wg, wr, ww, wp, g, a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => m.Live [a, rd, c, thr, wg, wr, ww, wp, g, f] ∧ HoldsMatrix a H m.store ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ m.store.get wg.1 wg.2 = some ((1 - γ) ^ k) ∧
        m.store.get wr.1 wr.2 = some ((2 : ℝ) ^ ((k : ℝ)⁻¹) *
          ((1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
            B ^ ((k : ℝ)⁻¹))) ∧
        m.store.get ww.1 ww.2 = some (ε / 2) ∧ m.store.get wp.1 wp.2 = some (1.0015 * (1 - γ)) ∧
        m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧ f.2 < m.store.len f.1 ∧
        HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg])
      (ShIterationOutcomeBy u k H γ tv
          ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))
        a lg ns w LL (k + 1 + (excNet ε).length)) (φse + φR / 2 + φ) := sorry

end Assembly

end NLAlib.ShiftedQR
