/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.TapeLaw
public import NLAlib.Ops.Logic.Index
public import NLAlib.Eigensolvers.SpectralBisectionSamples.Lazy

/-!
# Spectral bisection samples on a tape with one shared position

A level draws `n` uniform words followed by `4 * n * n` Gaussian words. Thus its tape interval
starts at `d * (n + 4 * n * n)`. The mathematical lazy-sampling theorem indexes each stream
separately. An injective coordinate map embeds that indexing into the actual shared-position
schedule, preserving its complete product law. This reuses the pure ideal sample-tree theorem;
no old execution semantics or interpreter is constructed.

## Main results

* `NLAlib.SpectralBisection.injective_idealCoordinate`: distinct ideal coordinates remain distinct.
* `NLAlib.SpectralBisection.hasLaw_idealTape`: the reindexed tape has the fixed ideal product law.
* `NLAlib.SpectralBisection.iIndepFun_eighIdealTree_idealTape`: independent ideal node samples.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib.SpectralBisection

open Ops

/-- The exact number of scalar words drawn at each level, across both declared streams:
the batch length is <!-- value SpectralBisection.levelSampleSize n -->
$$n + 4 n^2 \,.$$
-/
def levelSampleSize (n : ℕ) : ℕ := n + 4 * (n * n)

/-- The global tape position of a uniform word indexed within its stream. -/
def uniformPosition (n r : ℕ) : ℕ := (r / n) * levelSampleSize n + r % n

/-- The global tape position of a Gaussian word indexed within its stream. -/
def gaussianPosition (n r : ℕ) : ℕ :=
  (r / (4 * (n * n))) * levelSampleSize n + n + r % (4 * (n * n))

/-- The operation stream corresponding to a mathematical sample distribution. -/
def distributionStream : Computation.Dist → ℕ
  | .uniform => Stream.unif
  | .gaussian => Stream.gauss
  | .rademacher => Stream.sign

/-- A fixed embedding of the ideal distribution/position coordinates into the actual Ops tape.
Unused random-sign coordinates occupy their own stream and are left in their original order. -/
def idealCoordinate (n : ℕ) : Computation.Dist × ℕ → ℕ × ℕ
  | (.uniform, r) => (uniformPosition n r, Stream.unif)
  | (.gaussian, r) => (gaussianPosition n r, Stream.gauss)
  | (.rademacher, r) => (r, Stream.sign)

/-- Reindex an ideal tape by the actual program schedule, without changing any sampled value. -/
def idealTape (n : ℕ) (τ : Tape ℝ) (d : Computation.Dist) (r : ℕ) : ℝ :=
  τ (idealCoordinate n (d, r)).1 (idealCoordinate n (d, r)).2

/-- Uniform stream positions are embedded injectively, including the empty-size convention. -/
theorem injective_uniformPosition (n : ℕ) : Function.Injective (uniformPosition n) := by
  by_cases hn : n = 0
  · subst n
    intro a b hab
    simpa only [uniformPosition, levelSampleSize, Nat.mul_zero, Nat.add_zero,
      Nat.div_zero, Nat.zero_mul, Nat.mod_zero, Nat.zero_add] using hab
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  intro a b hab
  have ha : a % n < levelSampleSize n := (Nat.mod_lt _ hnpos).trans_le (Nat.le_add_right _ _)
  have hb : b % n < levelSampleSize n := (Nat.mod_lt _ hnpos).trans_le (Nat.le_add_right _ _)
  have hq := congrArg (fun r => r / levelSampleSize n) hab
  simp only [uniformPosition, Idx.div_add ha, Idx.div_add hb] at hq
  have hr : a % n = b % n := by unfold uniformPosition at hab; rw [hq] at hab; omega
  have hrec := Nat.div_add_mod a n
  rw [hq, hr] at hrec
  exact hrec.symm.trans (Nat.div_add_mod b n)

/-- Gaussian stream positions are embedded injectively, including the empty-size convention. -/
theorem injective_gaussianPosition (n : ℕ) : Function.Injective (gaussianPosition n) := by
  by_cases hn : n = 0
  · subst n
    intro a b hab
    simpa only [gaussianPosition, levelSampleSize, Nat.mul_zero, Nat.add_zero,
      Nat.div_zero, Nat.zero_mul, Nat.mod_zero, Nat.zero_add] using hab
  have hw : 0 < 4 * (n * n) := by positivity
  intro a b hab
  have ha : n + a % (4 * (n * n)) < levelSampleSize n := by
    have h := Nat.mod_lt a hw
    unfold levelSampleSize
    omega
  have hb : n + b % (4 * (n * n)) < levelSampleSize n := by
    have h := Nat.mod_lt b hw
    unfold levelSampleSize
    omega
  have hq := congrArg (fun r => r / levelSampleSize n) hab
  simp only [gaussianPosition, Nat.add_assoc, Idx.div_add ha, Idx.div_add hb] at hq
  have hr : a % (4 * (n * n)) = b % (4 * (n * n)) := by
    unfold gaussianPosition at hab
    rw [hq] at hab
    omega
  have hrec := Nat.div_add_mod a (4 * (n * n))
  rw [hq, hr] at hrec
  exact hrec.symm.trans (Nat.div_add_mod b (4 * (n * n)))

/-- Different distribution/position coordinates remain different in the actual tape schedule. -/
theorem injective_idealCoordinate (n : ℕ) : Function.Injective (idealCoordinate n) := by
  rintro ⟨d, a⟩ ⟨d', b⟩ hab
  cases d <;> cases d' <;> simp only [idealCoordinate, Prod.mk.injEq] at hab
  all_goals try { obtain ⟨-, h⟩ := hab; contradiction }
  · exact Prod.ext rfl (injective_gaussianPosition n hab.1)
  · exact Prod.ext rfl hab.1
  · exact Prod.ext rfl (injective_uniformPosition n hab.1)

/-- The coordinate embedding preserves the declared distribution stream. -/
theorem idealCoordinate_stream (n : ℕ) (d : Computation.Dist) (r : ℕ) :
    (idealCoordinate n (d, r)).2 = distributionStream d := by cases d <;> rfl

/-- The stream-local uniform position is exactly the global level start plus its slot offset. -/
theorem uniformPosition_mul_add (n d lo : ℕ) (hlo : lo < n) :
    uniformPosition n (n * d + lo) = d * levelSampleSize n + lo := by
  rw [Nat.mul_comm n d]
  simp only [uniformPosition, Idx.div_add hlo, Idx.mod_add hlo]

/-- The stream-local Gaussian word position is exactly its position in the level's second batch. -/
theorem gaussianPosition_mul_add (n d word : ℕ) (hw : word < 4 * (n * n)) :
    gaussianPosition n (4 * (n * n) * d + word) = d * levelSampleSize n + n + word := by
  rw [Nat.mul_comm (4 * (n * n)) d]
  simp only [gaussianPosition, Idx.div_add hw, Idx.mod_add hw]

/-- The word offset of one Gaussian component in a level's stored batch: node column `lo+j`,
projector side `side`, row `i`, and real/imaginary component `component`. -/
def gaussianWord (n lo j side i component : ℕ) : ℕ :=
  2 * (n * (2 * (lo + j) + side) + i) + component

/-- Every accessed Gaussian component belongs to the level's complete stored batch. -/
theorem gaussianWord_lt (n lo j side i component : ℕ) (hcol : lo + j < n)
    (hside : side < 2) (hrow : i < n) (hcomponent : component < 2) :
    gaussianWord n lo j side i component < 4 * (n * n) := by
  have hc := Idx.add_lt_mul hcol hside
  have he := Idx.add_lt_mul hc hrow
  have hw := Idx.add_lt_mul he hcomponent
  unfold gaussianWord
  nlinarith

/-- Reindexing the ideal complex Gaussian position gives exactly the scalar component address
used by deflation in the actual shared-position schedule. -/
theorem gaussianPosition_gaussianWord (n d lo j side i component : ℕ) (hcol : lo + j < n)
    (hside : side < 2) (hrow : i < n) (hcomponent : component < 2) :
    gaussianPosition n
      (2 * (2 * (n * n) * d + n * (2 * (lo + j) + side) + i) + component) =
      d * levelSampleSize n + n + gaussianWord n lo j side i component := by
  have hpos : 2 * (2 * (n * n) * d + n * (2 * (lo + j) + side) + i) + component =
      4 * (n * n) * d + gaussianWord n lo j side i component := by
    unfold gaussianWord
    ring
  rw [hpos]
  exact gaussianPosition_mul_add n d _ (gaussianWord_lt n lo j side i component
    hcol hside hrow hcomponent)

/-- The mathematical tape selected from the actual schedule has the fixed product law of the
three ideal distributions. The three used stream laws are explicit and independent of inputs. -/
theorem hasLaw_idealTape {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {law : ℕ → Measure ℝ} {ξ : Ω → Tape ℝ} (h : IsTapeLaw law P ξ)
    (hstream : ∀ d : Computation.Dist, law (distributionStream d) = d.law) (n : ℕ) :
    HasLaw (fun ω => idealTape n (ξ ω)) Computation.tapeLaw P := by
  have hflat := h.hasLaw_reindex (idealCoordinate n) (injective_idealCoordinate n)
  have hflat' : HasLaw (fun ω (p : Computation.Dist × ℕ) => idealTape n (ξ ω) p.1 p.2)
      (Measure.infinitePi fun p : Computation.Dist × ℕ => p.1.law) P := by
    have hmeasure : (fun p : Computation.Dist × ℕ => law (idealCoordinate n p).2) =
        fun p => p.1.law := by
      funext ⟨d, r⟩
      rw [idealCoordinate_stream, hstream]
    rw [hmeasure] at hflat
    exact hflat
  have hcurry : HasLaw (MeasurableEquiv.curry Computation.Dist ℕ ℝ) Computation.tapeLaw
      (Measure.infinitePi fun p : Computation.Dist × ℕ => p.1.law) :=
    ⟨(MeasurableEquiv.curry Computation.Dist ℕ ℝ).measurable.aemeasurable,
      Measure.infinitePi_map_curry (fun (d : Computation.Dist) (_ : ℕ) => d.law)⟩
  exact hcurry.comp hflat'

/-- The pure ideal sample tree remains independent with its original node law on the actual
Ops tape schedule. The machine's sampler measurability/countability assumptions are exactly
those of the existing mathematical lazy-sampling theorem; no program execution is assumed. -/
theorem iIndepFun_eighIdealTree_idealTape {F : Type*} (M : FloatMachine F ℝ ℂ)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (n signFuel D : ℕ) (R₀ β : F) (x : EighNode F) (hx : x.k ≤ n)
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {law : ℕ → Measure ℝ}
    {ξ : Ω → Tape ℝ} (h : IsTapeLaw law P ξ)
    (hstream : ∀ d : Computation.Dist, law (distributionStream d) = d.law) :
    iIndepFun (fun a ω => eighIdealTree M n signFuel D R₀ β (idealTape n (ξ ω))
      0 0 (some x) [] a) P ∧
      ∀ a, HasLaw (fun ω => eighIdealTree M n signFuel D R₀ β (idealTape n (ξ ω))
        0 0 (some x) [] a) (eighSampleLaw n) P :=
  iIndepFun_eighIdealTree M hunifm hunifc hnormalm hnormalc n signFuel D R₀ β x hx
    (hasLaw_idealTape h hstream n)

end NLAlib.SpectralBisection
