/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Isotropic
public import NLAlib.Ops.Catalog.Random
public import NLAlib.Ops.Law

/-!
# Test case: the Girard–Hutchinson trace estimator (visible randomness)

`hutch` adds to the cell `est` the sum of `gᵢᵀ (A gᵢ)` over `N` probes. The algorithm itself
draws each probe into its own scratch block `g` with the vector draw `gauss`, so the values are
in its store and it computes with them: `matvec`, then `dot` of the probe with the product.

## Main results

* `NLAlib.Ops.Examples.integral_hutchF`, `variance_hutchF`: mathematics. For probes whose
  decoded law is isotropic, `𝔼 Σᵢ gᵢᵀ A gᵢ = N tr A`; the probes are independent (they are
  windows at disjoint positions), so the variance is `N` times that of one quadratic form.
* `NLAlib.Ops.Examples.runs_hutch`: the run, for every interpretation meeting the contracts and
  every tape: `N` calls of each operation, `2 n + 1` scratch cells and the workspace of one
  operation.
* `NLAlib.Ops.Examples.runsLaw_hutch`: **the abstract theorem**: the estimate `est / N` is
  unbiased, `𝔼 est / N = tr A`, and its variance is that of one quadratic form divided by `N`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib.Ops.Examples

variable {K Tst : Type}

/-- **The Girard–Hutchinson estimator.** Index variables: `N`, `n`, the offset of `est`, then
the loop variable; buffer variables: `est`, then the scratch blocks `g`, `y` and the cell `t`. -/
def hutch : Stmt ROp Tst :=
  .alloc (.var 1) (.alloc (.var 1) (.alloc (.const 1) (.loop (.var 0)
    (.seq (.call .gauss [.var 1] [] [⟨1, .const 0⟩])
      (.seq (.call .matvec [.var 1] [⟨1, .const 0⟩] [⟨2, .const 0⟩])
        (.seq (.call .dot [.var 1] [⟨1, .const 0⟩, ⟨2, .const 0⟩] [⟨3, .const 0⟩])
          (.call .add [] [⟨0, .var 2⟩, ⟨3, .const 0⟩] [⟨0, .var 2⟩])))))))

/-- The call counts of `hutch`: `N` vector draws, products, dot products and additions. -/
noncomputable def hutchCount (N n : ℕ) : Count ROp Tst :=
  N • (Count.one .gauss [n] + (Count.one .matvec [n] + (Count.one .dot [n] + Count.one .add [])))

/-- The workspace of `hutch`: the probe, the product, one cell, and the workspace of the
operation that needs most. -/
def hutchPeak (W : ROp → List ℕ → ℕ) (n : ℕ) : ℕ :=
  n + (n + (1 + max (W .gauss [n]) (max (W .matvec [n]) (max (W .dot [n]) (W .add [])))))

theorem staticCost_hutch (N n o : ℕ) :
    staticCost (hutch (Tst := Tst)) [N, n, o] = hutchCount N n := by
  simp [hutch, staticCost, useCost, hutchCount]

theorem staticPeak_hutch_le (W : ROp → List ℕ → ℕ) (N n o : ℕ) :
    staticPeak W (hutch (Tst := Tst)) [N, n, o] ≤ hutchPeak W n := by
  simp only [hutch, staticPeak, hutchPeak]
  refine Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
    (Finset.sup_le fun i _ => ?_) _) _) _
  simp

/-! ### Mathematics -/

/-- The `i`-th probe of `n` Gaussian entries from the position `p`, decoded. -/
def probe (dec : K → ℝ) (n : ℕ) (τ : Tape K) (p i : ℕ) : Fin n → ℝ :=
  fun j => dec (τ (p + i * n + j) Stream.gauss)

/-- The sum of the quadratic forms of the first `N` probes. -/
def hutchF (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (τ : Tape K) (p N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, quadForm A (probe dec n τ p i)

theorem decv_window [Inhabited K] (dec : K → ℝ) (n : ℕ) (τ : Tape K) (p i : ℕ) :
    decv dec n (τ.window Stream.gauss (p + i * n) n) = probe dec n τ p i := by
  funext j
  exact congrArg dec (vec_window τ Stream.gauss (p + i * n) j.2)

section Math

variable [MeasurableSpace K] {Ω : Type} {mΩ : MeasurableSpace Ω} {law : ℕ → Measure K}
  {P : Measure Ω} {ξ : Ω → Tape K} {dec : K → ℝ} {n : ℕ}

/-- A probe is a function of the entries of its window. -/
theorem measurable_probe (hdec : Measurable dec) (ξ : Ω → Tape K) (p i : ℕ) :
    Measurable[Tape.sigma ξ (Set.Ico (p + i * n) (p + i * n + n))]
      fun ω => probe dec n (ξ ω) p i :=
  (measurable_pi_lambda _ fun j => hdec.comp (measurable_pi_apply j)).comp
    (Tape.measurable_windowFn (fun j hj => Set.mem_Ico.mpr ⟨by omega, by omega⟩) Stream.gauss)

/-- The law of a probe. -/
theorem map_probe (h : IsTapeLaw law P ξ) (hdec : Measurable dec) (p i : ℕ) :
    P.map (fun ω => probe dec n (ξ ω) p i) = probeLaw dec (law Stream.gauss) n := by
  have hm : Measurable fun w : Fin n → K => fun j => dec (w j) :=
    measurable_pi_lambda _ fun j => hdec.comp (measurable_pi_apply j)
  have hw : Measurable fun ω => Tape.windowFn (ξ ω) Stream.gauss (p + i * n) n :=
    (Tape.measurable_windowFn_future Stream.gauss _ n).mono (h.sigma_le _) le_rfl
  rw [probeLaw, ← h.map_windowFn Stream.gauss (p + i * n) n, Measure.map_map hm hw]
  rfl

/-- **The estimator is unbiased**: `𝔼 Σᵢ gᵢᵀ A gᵢ = N tr A`, for isotropic probes. -/
theorem integral_hutchF (h : IsTapeLaw law P ξ) (hdec : Measurable dec)
    (hiso : IsIsotropic (probeLaw dec (law Stream.gauss) n)) (A : Matrix (Fin n) (Fin n) ℝ)
    (p N : ℕ) : ∫ ω, hutchF dec A (ξ ω) p N ∂P = N * A.trace := by
  have hmp : ∀ i, Measurable fun ω => probe dec n (ξ ω) p i := fun i =>
    (measurable_probe hdec ξ p i).mono (h.sigma_le _) le_rfl
  have hint : ∀ i, Integrable (fun ω => quadForm A (probe dec n (ξ ω) p i)) P := fun i =>
    (integrable_map_measure (measurable_quadForm A).aestronglyMeasurable
      (hmp i).aemeasurable).mp (by rw [map_probe h hdec]; exact hiso.integrable_quadForm A)
  have hval : ∀ i, ∫ ω, quadForm A (probe dec n (ξ ω) p i) ∂P = A.trace := fun i => by
    rw [← hiso.integral_quadForm A, ← map_probe h hdec p i,
      integral_map (hmp i).aemeasurable (measurable_quadForm A).aestronglyMeasurable]
  simp only [hutchF]
  rw [integral_finsetSum _ fun i _ => hint i]
  simp [hval]

/-- **The variance of the estimator**: the probes are independent, so the variance of the sum is
`N` times the variance of one quadratic form. -/
theorem variance_hutchF (h : IsTapeLaw law P ξ) (hdec : Measurable dec)
    (A : Matrix (Fin n) (Fin n) ℝ) (hq : MemLp (quadForm A) 2 (probeLaw dec (law Stream.gauss) n))
    (p N : ℕ) : Var[fun ω => hutchF dec A (ξ ω) p N; P] =
      N * Var[quadForm A; probeLaw dec (law Stream.gauss) n] := by
  have hmp : ∀ i, Measurable fun ω => probe dec n (ξ ω) p i := fun i =>
    (measurable_probe hdec ξ p i).mono (h.sigma_le _) le_rfl
  have hfun : (fun ω => hutchF dec A (ξ ω) p N) =
      ∑ i ∈ Finset.range N, fun ω => quadForm A (probe dec n (ξ ω) p i) := by
    funext ω
    simp [hutchF]
  have hvar : ∀ i, Var[fun ω => quadForm A (probe dec n (ξ ω) p i); P] =
      Var[quadForm A; probeLaw dec (law Stream.gauss) n] := fun i => by
    rw [← map_probe h hdec p i, variance_map
      (measurable_quadForm A).aemeasurable (hmp i).aemeasurable]
    rfl
  rw [hfun, IndepFun.variance_sum (fun i _ => ?_) fun i _ j _ hij => ?_]
  · simp [hvar]
  · have := (memLp_map_measure_iff (measurable_quadForm A).aestronglyMeasurable
      (hmp i).aemeasurable).mp (by rw [map_probe h hdec]; exact hq)
    exact this
  · refine (h.indepFun_of_measurable ?_ (measurable_probe hdec ξ p i)
      (measurable_probe hdec ξ p j)).comp (measurable_quadForm A) (measurable_quadForm A)
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_mul] at this
      exact Set.disjoint_left.mpr fun q h1 h2 => by
        have := (Set.mem_Ico.mp h1).2
        have := (Set.mem_Ico.mp h2).1
        omega
    · have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_mul] at this
      exact Set.disjoint_left.mpr fun q h1 h2 => by
        have := (Set.mem_Ico.mp h1).1
        have := (Set.mem_Ico.mp h2).2
        omega

end Math

/-! ### The run -/

variable [Inhabited K]

/-- **The run of `hutch`**, for every interpretation meeting the contracts and every tape: the
cell `est` receives a word that decodes to its old value plus the sum of the quadratic forms of
the `N` probes, the position advances by `N n`, nothing else is written. -/
theorem wp_hutch {dec : K → ℝ} {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {J : Interp ROp Tst K}
    (hJ : IsRandLin dec A J) {τ : Tape K} {N : ℕ} {e : ℕ × ℕ} {m : Mem K} {z₀ : K}
    (he : m.store.get e.1 e.2 = some z₀) :
    Wp .total J τ hutch ⟨[N, n, e.2], [e.1]⟩ (fun m' => ∃ v,
      m' = (m.updBlock e [v]).advance (N * n) ∧ dec v = dec z₀ + hutchF dec A τ m.pos N) m := by
  obtain ⟨s, p⟩ := m
  obtain ⟨be, oe⟩ := e
  have hbe : be < s.length := Store.lt_length_of_get he
  have hoe : oe < s.len be := Store.lt_len_of_get he
  have hl1 : (s.push n).length = s.length + 1 := Store.length_push _ _
  have hl2 : ((s.push n).push n).length = s.length + 2 := by simp
  let F : ℕ → ℕ → Prop := ((Store.inBlock be oe 1 ⊔ Store.inBuf s.length) ⊔
    Store.inBuf (s.push n).length) ⊔ Store.inBuf ((s.push n).push n).length
  refine wp_alloc rfl (wp_alloc rfl (wp_alloc rfl (wp_loop (k := N) rfl
    (fun i m' => ∃ s' v q, m' = ⟨s', q⟩ ∧ q = p + i * n ∧
      (((s.push n).push n).push 1).EqOff F s' ∧ s'.get be oe = some v ∧
      dec v = dec z₀ + hutchF dec A τ p i)
    ⟨_, z₀, p, rfl, by simp, Store.EqOff.refl _ _, by store_simp, by simp [hutchF]⟩ ?_ ?_)))
  · rintro i hi m' ⟨s', v, q, rfl, rfl, hfr, hv, hdv⟩
    have hlen : s'.length = s.length + 3 := by rw [hfr.length_eq]; simp
    have hlg : s'.len s.length = n := by
      rw [hfr.len_eq, Store.len_push_of_lt (by simp), Store.len_push_of_lt (by simp)]
      simp
    have hly : s'.len (s.length + 1) = n := by
      rw [hfr.len_eq, Store.len_push_of_lt (by simp), ← hl1, Store.len_push_top]
    have hlt : s'.len (s.length + 2) = 1 := by
      rw [hfr.len_eq, ← hl2, Store.len_push_top]
    have hle : s'.len be = s.len be := by
      rw [hfr.len_eq, Store.len_push_of_lt (by simp; omega),
        Store.len_push_of_lt (by simp; omega), Store.len_push_of_lt hbe]
    -- the probe, into the scratch block `g`
    refine wp_seq (wp_call_win hJ.gauss (k := n) (l := n) rfl rfl rfl rfl rfl rfl ⟨rfl, by simp⟩
      ?_ (xs := []) ?_ ?_ fun ws hwl hws => ?_)
    · store_simp
    · rfl
    · store_simp
    obtain rfl : ws = τ.window Stream.gauss (p + i * n) n := hws
    -- the product, into the scratch block `y`
    refine wp_seq (wp_call_rel hJ.matvec rfl rfl rfl rfl ⟨rfl, by simp⟩ ?_
      (xs := [τ.window Stream.gauss (p + i * n) n]) ?_ ?_ fun ys hyl hys => ?_)
    · store_simp
    · store_simp
    · store_simp
    replace hyl : ys.length = n := hyl
    -- the quadratic form, into the scratch cell `t`
    refine wp_seq (wp_call_rel_cell hJ.dot rfl rfl rfl rfl rfl ⟨rfl, by simp; omega⟩ ?_
      (xs := [τ.window Stream.gauss (p + i * n) n, ys]) ?_ ?_ fun t ht => ?_)
    · store_simp
    · store_simp
    · store_simp
    -- the accumulation
    refine wp_call_rel_cell hJ.add rfl rfl rfl rfl rfl trivial ?_ (xs := [[v], [t]]) ?_ ?_
      fun v' hv' => ⟨_, v', _, rfl, by simp [Mem.advance, Mem.upd, Mem.updBlock]; ring,
        (((hfr.updBlock fun _ _ => Or.inl (Or.inl (Or.inr rfl))).updBlock
          fun _ _ => Or.inl (Or.inr rfl)).upd (Or.inr rfl) _).upd
          (Or.inl (Or.inl (Or.inl ⟨rfl, by omega, by omega⟩))) _, ?_, ?_⟩
    · store_simp
    · store_simp [BlockFn.readBlock_one]
    · store_simp
    · store_simp
    · have hv'' : dec v' = dec v + dec t := hv'
      have ht' : dec t = ∑ j, decv dec n (τ.window Stream.gauss (p + i * n) n) j *
          decv dec n ys j := ht
      have hys' : decv dec n ys = A.mulVec (decv dec n (τ.window Stream.gauss (p + i * n) n)) :=
        hys
      rw [hv'', hdv, ht', hys', decv_window, hutchF, hutchF, Finset.sum_range_succ,
        quadForm_eq_sum_mulVec, add_assoc]
  · rintro m' ⟨s', v, q, rfl, rfl, hfr, hv, hdv⟩
    have h3 : s.EqOff (Store.inBlock be oe 1) s'.pop.pop.pop := hfr.pop.pop.pop
    have hlen : s'.length = s.length + 3 := by rw [hfr.length_eq]; simp
    have hg : s'.pop.pop.pop.readBlock be oe 1 = some [v] :=
      Store.readBlock_one_of_get (by
        rw [Store.get_pop_of_lt (by simp [Store.length_pop]; omega),
          Store.get_pop_of_lt (by simp [Store.length_pop]; omega),
          Store.get_pop_of_lt (by omega), hv])
    exact ⟨v, by simp [Mem.updBlock, Mem.advance, h3.eq_updBlock hg], hdv⟩

/-- The run of `hutch` within its counts and workspace. -/
theorem runs_hutch {dec : K → ℝ} {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {J : Interp ROp Tst K}
    (hJ : IsRandLin dec A J) (W : ROp → List ℕ → ℕ) {τ : Tape K} {N : ℕ} {e : ℕ × ℕ}
    {m : Mem K} {z₀ : K} (he : m.store.get e.1 e.2 = some z₀) :
    Runs J W τ hutch ⟨[N, n, e.2], [e.1]⟩ m (hutchCount N n) (hutchPeak W n) (fun m' => ∃ v,
      m' = (m.updBlock e [v]).advance (N * n) ∧ dec v = dec z₀ + hutchF dec A τ m.pos N) := by
  obtain ⟨m', hrun, hpost⟩ := wp_hutch hJ (τ := τ) (N := N) he
  exact (Runs.of_run hrun hpost W).mono (le_of_eq (staticCost_hutch ..))
    (staticPeak_hutch_le ..) fun _ h => h

variable [MeasurableSpace K]

/-- The postcondition of `hutch` for the accumulated sum `x`: the cell `est` holds a word that
decodes to `x`, the position has advanced by `N n`, nothing else is written. -/
def HutchPost (dec : K → ℝ) (N n : ℕ) (e : ℕ × ℕ) (m : Mem K) (x : ℝ) (m' : Mem K) : Prop :=
  ∃ v, m' = (m.updBlock e [v]).advance (N * n) ∧ dec v = x

/-- **The abstract theorem of the Girard–Hutchinson estimator**, for every interpretation
meeting the contracts and every law of the tape whose decoded probes are isotropic. For every
sample: `N` calls of each operation, `2 n + 1` scratch cells. In law, from `est = 0`: the
estimate `est / N` has mean `tr A` and the variance of one quadratic form divided by `N`. -/
theorem runsLaw_hutch {dec : K → ℝ} {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {J : Interp ROp Tst K} (hJ : IsRandLin dec A J) {law : ℕ → Measure K} {Ω : Type}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ξ : Ω → Tape K} (h : IsTapeLaw law P ξ)
    (hdec : Measurable dec) (hiso : IsIsotropic (probeLaw dec (law Stream.gauss) n))
    (hq : MemLp (quadForm A) 2 (probeLaw dec (law Stream.gauss) n)) (W : ROp → List ℕ → ℕ)
    {N : ℕ} (hN : 0 < N) {e : ℕ × ℕ} {m : Mem K} {z₀ : K} (he : m.store.get e.1 e.2 = some z₀)
    (hz : dec z₀ = 0) :
    RunsLaw J W ξ hutch ⟨[N, n, e.2], [e.1]⟩ m (hutchCount N n) (hutchPeak W n)
      (HutchPost dec N n e m) fun X => ∫ ω, X ω / N ∂P = A.trace ∧
        Var[fun ω => X ω / N; P] = Var[quadForm A; probeLaw dec (law Stream.gauss) n] / N := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  refine ⟨fun ω => hutchF dec A (ξ ω) m.pos N, fun ω => (runs_hutch hJ W he).mono le_rfl le_rfl
    fun m' ⟨v, h1, h2⟩ => ⟨v, h1, by rw [h2, hz, zero_add]⟩, ?_, ?_⟩
  · rw [integral_div, integral_hutchF h hdec hiso]
    field_simp
  · have e1 : (fun ω => hutchF dec A (ξ ω) m.pos N / N) =
        fun ω => (N : ℝ)⁻¹ * hutchF dec A (ξ ω) m.pos N := by
      funext ω
      rw [div_eq_inv_mul]
    rw [e1, variance_const_mul, variance_hutchF h hdec A hq]
    field_simp

end NLAlib.Ops.Examples
