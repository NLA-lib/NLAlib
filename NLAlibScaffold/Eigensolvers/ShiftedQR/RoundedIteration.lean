/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedRegularize
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedSh

/-!
# One rounded iteration of the decoupling loop

One iteration of the loop of [BanksGarzaVargasSrivastava2022, Lemma 6.4] in floating point:
`Regularize` either decouples the matrix with one of its trial steps or returns $\theta$-optimal
shifts away from the spectrum, and in the second case the shifting strategy $\mathrm{Sh}_{k,B}$
takes a step with them. Except with the sum of the two failure probabilities, the matrix becomes
an upper Hessenberg perturbed unitary similarity that is decoupled at the bottom or whose
potential $\psi_k$ has contracted by $1.002(1 - \gamma)$.

## Main definitions

* `NLAlib.ShiftedQR.shIteration`: the program; `NLAlib.ShiftedQR.ShIterationOutcome`: its
  outcome.

## Main results

* `NLAlib.ShiftedQR.shIteration_pwrites`: one iteration as a probabilistic block.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- One iteration with caller-owned scratch: `NLAlib.ShiftedQR.regularize` of the order-$N$
matrix `A` (radius word `Rd`, `Optimal` word `C`, threshold word `Thr`) into the $k$ shift pairs
`S` and the flag `Fl`; if the flag is $0$ (the shifts are optimal),
`NLAlib.ShiftedQR.shStep` with them and the words `Cg`, `Cr`, `Cw`, `Cp`, the net `G` of $n_0$
points and `Thr`. The interface is `[N, m, k, n0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, S) →
(A, Fl)`. -/
def shIterationWithScratch : Impl O Q :=
  opsImpl% [N, m, k, n0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, S) → (A, Fl) {
    run (regularize (O := O) (Q := Q)).body [N, k] (A, Rd, C, Thr, A, S, Fl);
    if (Has.inj CmpTst.isZero) [] (Fl) {
      run (shStep (O := O) (Q := Q)).body [N, m, k, n0] (A, S, Cg, Cr, Cw, Cp, G, Thr, A, Fl)
    } else { skip }
  }

/-- **One iteration of the decoupling loop** ([BanksGarzaVargasSrivastava2022, Lemma 6.4], the
body of the loop): `Regularize`, then `Sh` with its shifts if they are optimal. The scratch for
the $k$ shift pairs is scoped. The interface is
`[N, m, k, n0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G) → (A, Fl)`. -/
def shIteration : Impl O Q :=
  opsImpl% [N, m, k, n0] (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G) → (A, Fl) {
    let S ← alloc (2 * k);
    run (shIterationWithScratch (O := O) (Q := Q)).body [N, m, k, n0]
      (A, Rd, C, Thr, Cg, Cr, Cw, Cp, G, S, A, Fl)
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

/-- **The outcomes of an iteration form a measurable set**: the pairs of a memory before and
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

/-- **`Sh` from the shifts of `Regularize`**: under the hypotheses of
`NLAlib.ShiftedQR.shStep_pwrites` with the shifts stored at `s` not fixed but any $k$ shifts that
are $\theta$-optimal, at distance at least $d$ from the spectrum and in
$\mathbb{D}(0, 1.1\|\mathbf{H}\|_2)$, `Sh` ends in `NLAlib.ShiftedQR.ShIterationOutcome` except
with probability at most $\varphi$; the conditions of `NLAlib.ShiftedQR.shStep_pwrites` that
depend on $\psi_k(\mathbf{H})$ are asked at $\omega \le \psi_k(\mathbf{H})$ and
$\psi_k(\mathbf{H}) \le \Sigma$. One good set serves all shifts: the outcome is measurable
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

end Assembly

end NLAlib.ShiftedQR
