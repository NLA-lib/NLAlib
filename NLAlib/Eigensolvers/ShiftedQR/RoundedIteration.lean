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
points and `Thr`. The interface is
`[N, m, k, n0, nq, T] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw, S) → (A, Fl)`. -/
def shIterationWithScratchWith (SE : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, n0, nq, T] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw, S) → (A, Fl) {
    run (regularizeWith SE).body [N, k, nq, T] (A, Rd, C, Thr, Qw, A, S, Fl);
    if (Has.inj CmpTst.isZero) [] (Fl) {
      run (shStep (O := O) (Q := Q)).body [N, m, k, n0] (A, S, Cg, Cr, Cw, Cp, G, Thr, A, Fl)
    } else { skip }
  }

/-- **One iteration of the decoupling loop with a small-eigenvalue routine**
([BanksGarzaVargasSrivastava2022, Lemma 6.4], the body of the loop): `Regularize` with the
routine `SE`, then `Sh` with its shifts if they are optimal. The scratch for the $k$ shift pairs
is scoped. The interface is
`[N, m, k, n0, nq, T] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw) → (A, Fl)`. -/
def shIterationWith (SE : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, n0, nq, T] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw) → (A, Fl) {
    let S ← alloc (2 * k);
    run (shIterationWithScratchWith SE).body [N, m, k, n0, nq, T]
      (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Qw, S, A, Fl)
  }

/-- **One iteration of the decoupling loop** ([BanksGarzaVargasSrivastava2022, Lemma 6.4], the
body of the loop): `NLAlib.ShiftedQR.shIterationWith` with the `SmallEig` kernel
(`NLAlib.ShiftedQR.smallEigKernel`), no words and the cap $0$: `Regularize`, then `Sh` with its
shifts if they are optimal. The interface is
`[N, m, k, n0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G) → (A, Fl)`. -/
def shIteration : Impl O Q :=
  opsImpl% [N, m, k, n0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G) → (A, Fl) {
    run (shIterationWith (smallEigKernel (O := O) (Q := Q))).body [N, m, k, n0, 0, 0]
      (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, Rd, A, Fl)
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
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {γ tv ε : ℝ} {a f : ℕ × ℕ} {F : Fp}
    {m m' : Mem ℝ} (hH : HoldsMatrix a H m.store) (hfr : m.store.EqOff F m'.store)
    (h : ShOutcome u k H γ tv ε a f m') :
    m.store.EqOff F m'.store ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (m'.store.get a.1 (a.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilar (storedMatrix a (n + 1) (n + 1) m.store)
        (storedMatrix a (n + 1) (n + 1) m'.store) ε ∧
      IsUpperHessenberg (storedMatrix a (n + 1) (n + 1) m'.store) ∧
      ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧
          (1 - u) ^ 2 * ‖storedMatrix a (n + 1) (n + 1) m'.store i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
        hessenbergPotential k (storedMatrix a (n + 1) (n + 1) m'.store) ≤
          1.002 * (1 - γ) * hessenbergPotential k (storedMatrix a (n + 1) (n + 1) m.store)) := by
  obtain ⟨-, H', hsim, hHess, hA, hdec⟩ := h
  rw [← hH.eq_storedMatrix, ← hA.eq_storedMatrix]
  exact ⟨hfr, fun j hj => by rw [Store.get_of_readBlock hA hj 0]; rfl, hsim, hHess, hdec⟩

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
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) :
    PWrites law I (shStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length] [a, s, wg, wr, ww, wp, g, thr, a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
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
          ∀ j, ‖zs j‖ ≤ 1.1 * specNorm H)
      (ShIterationOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))
        a) φ := by
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
      zs.2.2.2 hα hγ hγ1 hε hε2 hφ hφ1 hdψ hC1 hnu hku hxu hbound he1 he2 hthrω)
    (measurableSet_iterationOutcome (n := n) u k (1.002 * (1 - γ)) tv
      ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1))
    (fun _ _ _ hP hfr hO => mem_iterationOutcome_of_shOutcome hP.2.1 hfr hO)
  refine PStep.mono hst (fun m ⟨hl, hA, hwg, hwr, hww, hwp, hg, ht, hf, zs, hzs, hopt, hdist,
    hsH⟩ => ⟨⟨zs, hopt, ?_, ?_⟩, hl, hA, hzs, hwg, hwr, hww, hwp, hg, ht, hf⟩)
    (fun m m' hm hT => shIterationOutcome_of_mem hm.2.1 hT) le_rfl
  · intro s hs i
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
    exact hdist j i
  · intro s hs
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
    exact hsH j

variable [Has EigenvalueKernelOp O]

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The hypothesis lists of `Regularize` and the kept words of `Sh` make elaboration heavy.
omit [Has IdxTst Q] in
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
    {ds : List IExp} {args : List Operand} (hρ : IExp.evalList ρ.idx ds = some [n + 1, k, nq, T])
    (hρa : Operand.evalList ρ args = some [a, rd, c, thr, qw, a, s, f])
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
        Store.inBlock f.1 f.2 1)
      (fun m => m.Live [a, rd, c, thr, wg, wr, ww, wp, g, qw, s, f] ∧ HoldsMatrix a H m.store ∧
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
          ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f m' ∧
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
  refine ((regularizeWith_pwrites_at hI hloc hS hM hu1 hL hNat hC hβ0 hφse hD hU hk0 hk has haf
    hsf hio' hH hV hHV hκ hBk hω hψ hSH hgap hR hφ hφ1 hβ hdη hnu huo huo1 hxu hbound
    hthrω hSE hqw).in_frame hρ hρa ?_).mono_eqOff ?_ ?_
  · rintro m ⟨hl, -⟩
    exact hl.mono (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  · rintro m ⟨hl, hA, hq, hrd, hc, ht, -, -, -, -, -, hs, hf⟩
    exact ⟨hl.mono (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto),
      hA, hq, hrd, hc, ht, hs, hf⟩
  · rintro m m' ⟨hl, -, -, -, -, ht, hwg, hwr, hww, hwp, hg, -, hf⟩ hfr hout
    have hD' : ∀ {G : Fp}, G ≤ Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔
        Store.inBlock thr.1 thr.2 1 ⊔ Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔
        Store.inBlock ww.1 ww.2 1 ⊔ Store.inBlock wp.1 wp.2 1 ⊔
        Store.inBlock g.1 g.2 (2 * (excNet ε).length) → Fp.Disj _ G := fun hG => hio.mono le_rfl hG
    exact ⟨hout, (hl.congr hfr.length_eq).mono (by
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

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The hypothesis lists of `Regularize` and `Sh` together, with their long real constants, make
-- the elaboration of the composition heavy.
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
        (Store.inBlock qw.1 qw.2 qs.length)) :
    PWrites law I (shIterationWithScratchWith SE).body
      (Env.frame [n + 1, q, k, (excNet ε).length, nq, T]
        [a, rd, c, thr, wg, wr, ww, wp, g, qw, s, a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1)
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
        s.2 + 2 * k ≤ m.store.len s.1 ∧ f.2 < m.store.len f.1)
      (ShIterationOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))
        a) (φse + φR / 2 + φ) := by
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
  have hsh := shStep_pwrites_of_forall (f := f) (a := a) (s := s) (wg := wg) (wr := wr)
    (ww := ww) (wp := wp) (g := g) (thr := thr) hI hloc hS hM hu1 hL hNat hC hQ hD hU hkq hk hkn
    haf hioS hH hV hHV hκ hSH hω hψ hθ hd' hα hγ hγ1 hε hε2 hφ hφ1 hd hC1 hnu hku hxu hbound
    hexc1 hexc2 hthrω
  unfold shIterationWithScratchWith
  refine (PWrites.seq hI hloc (le_max_right φ 0)
    (shIteration_regularize_pwrites (ρ := Env.frame [n + 1, q, k, (excNet ε).length, nq, T]
      [a, rd, c, thr, wg, wr, ww, wp, g, qw, s, a, f]) hI hloc hS hM hu1 hL hNat hC hβ0 hφse hD hU
      (by omega) hkn has haf hsf hio hqw ?_ ?_ hH hV hHV hκ hBk hω hψ hSH hgap hR hφR hφR1 hβ hdη
      hnu huo huo1 hxuR hboundR hthrω hSE)
    (PWrites.ite hI ?_ ((hsh.in_frame ?_ ?_ ?_).mono ?_ le_rfl (fun _ h => h) le_rfl)
      (PWrites.of_writes le_rfl ?_))).mono (fun _ h => h) (by fp_sub) (fun _ h => h)
      (by rw [max_eq_left hφ.le])
  · rfl
  · rfl
  · rintro m ⟨⟨hF, -⟩ | ⟨hF, -⟩, -⟩ <;>
      exact ⟨_, by rw [Interp.testAt_eq rfl rfl, hC.test_isZero hF]⟩
  · rfl
  · rfl
  · rintro m ⟨hl, -⟩
    exact hl.mono (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                      tauto)
  · rintro m ⟨⟨⟨hF, hA, zs, hzs, hopt, hdist, hsH⟩ | ⟨hF, -⟩, hl, ht, hwg, hwr, hww, hwp, hg, hf⟩,
      htest⟩
    · exact ⟨hl.mono (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                         tauto), hA, hwg, hwr, hww, hwp, hg, ht, hf, zs, hzs, hopt, hdist, hsH⟩
    · rw [Interp.testAt_eq rfl rfl, hC.test_isZero hF] at htest
      norm_num at htest
  · rintro m τ ⟨⟨⟨hF, -⟩ | ⟨hF, H', hsim, hH', hA, hdec⟩, -⟩, htest⟩
    · rw [Interp.testAt_eq rfl rfl, hC.test_isZero hF] at htest
      norm_num at htest
    · exact (Writes.skip ⟨H', hsim.mono hCε, hH', hA, Or.inl hdec⟩).mono bot_le fun _ _ h => h

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The hypothesis lists of `Regularize` and `Sh` together, with their long real constants, make
-- the elaboration of the composition heavy.
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
      (Store.inBlock qw.1 qw.2 qs.length)) :
    PWrites law I (shIterationWith SE).body
      (Env.frame [n + 1, q, k, (excNet ε).length, nq, T]
        [a, rd, c, thr, wg, wr, ww, wp, g, qw, a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
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
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧ f.2 < m.store.len f.1)
      (ShIterationOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))
        a) (φse + φR / 2 + φ) := by
  have hφ0 : 0 ≤ φse + φR / 2 + φ := by positivity
  have e : (shIterationWith SE).body = Stmt.allocs [.const 2 * .var 2]
      (.frame [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5] [⟨0, .var 6⟩, ⟨1, .var 7⟩,
        ⟨2, .var 8⟩, ⟨3, .var 9⟩, ⟨4, .var 10⟩, ⟨5, .var 11⟩, ⟨6, .var 12⟩, ⟨7, .var 13⟩,
        ⟨8, .var 14⟩, ⟨9, .var 15⟩, ⟨12, .const 0⟩, ⟨0, .var 6⟩, ⟨11, .var 17⟩]
        (shIterationWithScratchWith SE).body) :=
    rfl
  rw [e]
  refine PWrites.allocs (ns := [2 * k]) ?_ (Pre₁ := fun L μ => (a.1 < L ∧ rd.1 < L ∧ c.1 < L ∧
      thr.1 < L ∧ wg.1 < L ∧ wr.1 < L ∧ ww.1 < L ∧ wp.1 < L ∧ g.1 < L ∧ f.1 < L ∧ qw.1 < L) ∧
    μ.Live [a, rd, c, thr, wg, wr, ww, wp, g, qw, (L, 0), f] ∧ HoldsMatrix a H μ.store ∧
      μ.store.readBlock qw.1 qw.2 qs.length = some qs ∧
      μ.store.get rd.1 rd.2 = some R ∧ μ.store.get c.1 c.2 = some
        (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
      μ.store.get thr.1 thr.2 = some tv ∧ μ.store.get wg.1 wg.2 = some ((1 - γ) ^ k) ∧
      μ.store.get wr.1 wr.2 = some ((2 : ℝ) ^ ((k : ℝ)⁻¹) *
        ((1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
          B ^ ((k : ℝ)⁻¹))) ∧
      μ.store.get ww.1 ww.2 = some (ε / 2) ∧ μ.store.get wp.1 wp.2 = some (1.0015 * (1 - γ)) ∧
      μ.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
        some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧
      0 + 2 * k ≤ μ.store.len L ∧ f.2 < μ.store.len f.1) ?_ ?_ fun L => ?_
  · rfl
  · rintro m s₁ ⟨hl, hA, hq, hrd, hc, ht, hwg, hwr, hww, hwp, hg, hf⟩ hlen hlens hBelow
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11, h10⟩ : a.1 < m.store.length ∧
        rd.1 < m.store.length ∧ c.1 < m.store.length ∧ thr.1 < m.store.length ∧
        wg.1 < m.store.length ∧ wr.1 < m.store.length ∧ ww.1 < m.store.length ∧
        wp.1 < m.store.length ∧ g.1 < m.store.length ∧ qw.1 < m.store.length ∧
        f.1 < m.store.length := by
      simpa [Mem.Live] using hl
    have hl0 := hlens 0 (by simp)
    simp only [List.length_cons, List.length_nil] at hlen
    refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, ?_, hA.of_below hBelow h1,
      (hBelow.readBlock h11 qw.2 qs.length).trans hq, hBelow.get_of h2 hrd, hBelow.get_of h3 hc,
      hBelow.get_of h4 ht, hBelow.get_of h5 hwg,
      hBelow.get_of h6 hwr, hBelow.get_of h7 hww, hBelow.get_of h8 hwp,
      hBelow.readBlock_of h9 hg, by simpa using hl0.ge, by rw [(hBelow f.1 h10).1]; exact hf⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, hlen]
    omega
  · rintro m ⟨hl, -⟩ st st' p hBelow ⟨H', hsim, hH', hA, hdec⟩
    have h1 : a.1 < m.store.length := hl a (by simp)
    exact ⟨H', hsim, hH', hA.of_below hBelow h1, hdec⟩
  · by_cases hvL : a.1 < L ∧ rd.1 < L ∧ c.1 < L ∧ thr.1 < L ∧ wg.1 < L ∧ wr.1 < L ∧
        ww.1 < L ∧ wp.1 < L ∧ g.1 < L ∧ f.1 < L ∧ qw.1 < L
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hvL
      have hne : ∀ {b : ℕ × ℕ} {o n' : ℕ}, b.1 < L →
          Fp.Disj (Store.inBlock b.1 b.2 o) (Store.inBlock (L, 0).1 (L, 0).2 n') :=
        fun hb => Fp.disj_inBlock_of_ne (by simp; omega)
      have hio' : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L, 0).1 (L, 0).2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
          (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1 ⊔
            Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
            Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length)) := by
        have := (hne h2 (o := 1) (n' := 2 * k)).symm; have := (hne h3 (o := 1) (n' := 2 * k)).symm
        have := (hne h4 (o := 1) (n' := 2 * k)).symm; have := (hne h5 (o := 1) (n' := 2 * k)).symm
        have := (hne h6 (o := 1) (n' := 2 * k)).symm; have := (hne h7 (o := 1) (n' := 2 * k)).symm
        have := (hne h8 (o := 1) (n' := 2 * k)).symm
        have := (hne h9 (o := 2 * (excNet ε).length) (n' := 2 * k)).symm
        simp only [Fp.disj_sup_left, Fp.disj_sup_right] at hio ⊢
        tauto
      have hqw' : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L, 0).1 (L, 0).2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
          (Store.inBlock qw.1 qw.2 qs.length) := by
        have := (hne h11 (o := qs.length) (n' := 2 * k)).symm
        simp only [Fp.disj_sup_left] at hqw ⊢
        tauto
      refine ((shIterationWithScratchWith_pwrites (s := (L, 0)) hI hloc hS hM hu1 hL hNat hC hQ
        hβ0 hφse hD hU hkq hk hkn (hne h1) haf (hne h10).symm hio' hH hV hHV hκ hBk hω hψ hSH
        hgap hR hφR hφR1 hβ hdη hnu huo huo1 hxuR hboundR hα hγ hγ1 hε hε2 hφ hφ1 hd hC1 hxu
        hbound hexc1 hexc2 hthrω hSE hqw').in_frame ?_ ?_ ?_).mono (fun _ h => h.2) (by fp_sub)
        (fun _ h => h) le_rfl
      · rfl
      · rfl
      · rintro μ ⟨hl, -⟩
        exact hl.mono (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                          tauto)
    · exact PWrites.of_writes hφ0 fun _ _ h => absurd h.1 hvL

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The hypothesis lists of `Regularize` and `Sh` together, with their long real constants, make
-- the elaboration of the composition heavy.
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
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) :
    PWrites law I (shIteration (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length] [a, rd, c, thr, wg, wr, ww, wp, g, a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun m => m.Live [a, rd, c, thr, wg, wr, ww, wp, g, f] ∧ HoldsMatrix a H m.store ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ m.store.get wg.1 wg.2 = some ((1 - γ) ^ k) ∧
        m.store.get wr.1 wr.2 = some ((2 : ℝ) ^ ((k : ℝ)⁻¹) *
          ((1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
            B ^ ((k : ℝ)⁻¹))) ∧
        m.store.get ww.1 ww.2 = some (ε / 2) ∧ m.store.get wp.1 wp.2 = some (1.0015 * (1 - γ)) ∧
        m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧ f.2 < m.store.len f.1)
      (ShIterationOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))
        a) (φse + φR / 2 + φ) := by
  unfold shIteration
  refine ((shIterationWith_pwrites_at hI hloc hS hM hu1 hL hNat hC hQ hβ0 hφse hD hU hkq hk hkn
    haf hio hH hV hHV hκ hBk hω hψ hSH hgap hR hφR hφR1 hβ hdη hnu huo huo1 hxuR hboundR hα hγ
    hγ1 hε hε2 hφ hφ1 hd hC1 hxu hbound hexc1 hexc2 hthrω
    (hSE.randomSmallEigContractAt k 0 0 S []) (qw := rd)
    (fun _ _ _ h => by obtain ⟨-, h1, h2⟩ := h; simp at h2; omega)).in_frame (by simp)
    (by simp [Operand.evalList, Operand.eval]) ?_).mono ?_ le_rfl (fun _ h => h) le_rfl
  · rintro μ ⟨hl, -⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl ⊢
    tauto
  · rintro μ ⟨hl, hA, hrest⟩
    refine ⟨?_, hA, by simp, hrest⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl ⊢
    tauto

end Assembly

end NLAlib.ShiftedQR
