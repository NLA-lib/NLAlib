/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Isotropic
public import NLAlib.Ops.Catalog.Random
public import NLAlib.Ops.Examples.Noisy
public import NLAlib.Ops.TapeLaw

/-!
# Witnesses for the randomized examples

The hypotheses of the randomized examples can be met jointly.

## Main results

* `NLAlib.Ops.Examples.stdLaw`: the laws of the streams of a real tape: uniform on `[0, 1]`,
  standard Gaussian. `NLAlib.Ops.Examples.exists_isTapeLaw_stdLaw`: there is a tape with these
  laws; its Gaussian stream is a standard law (`isStdLaw_stdLaw_gauss`).
* `NLAlib.Ops.Examples.exists_isRandLin`: for every matrix there is an interpretation over the
  real numbers, in exact arithmetic, that meets the contracts `IsRandLin` with tape-local
  operations at the registered windows.
* `NLAlib.Ops.Examples.exists_isRandLin_isTapeLaw`: the joint witness at the law level
  (interpretation, tape with the standard laws, standard decoded stream, isotropic probes).
* `NLAlib.Ops.Examples.exists_isNoisy`, `NLAlib.Ops.Examples.exists_isNoisy_isNoisyMv`: the
  contract of the noisy product for every noise function, and jointly with the conditional law
  of the noise and the law of the tape.
* `NLAlib.Ops.Examples.memLp_quadForm_gaussian`: the quadratic form of a Gaussian probe is
  square integrable, the hypothesis of the variance of the Girard–Hutchinson estimator.
* `NLAlib.Ops.Examples.sqNorm_mulVec_le`: every matrix satisfies the norm bound assumed of the
  noisy power iteration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib.Ops.Examples

/-! ### The laws of the streams -/

/-- **The laws of the streams of a real tape**: uniform on `[0, 1]`, standard Gaussian; the other
streams are not used and hold zeros. -/
noncomputable def stdLaw : ℕ → Measure ℝ
  | 0 => volume.restrict (Set.Icc 0 1)
  | 1 => gaussianReal 0 1
  | _ => Measure.dirac 0

instance (s : ℕ) : IsProbabilityMeasure (stdLaw s) := by
  rcases s with _ | _ | s
  · exact ⟨by simp [stdLaw]⟩
  · exact inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
  · exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))

/-- There is a random tape with the standard laws. -/
theorem exists_isTapeLaw_stdLaw :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (ξ : Ω → Tape ℝ),
      IsTapeLaw stdLaw P ξ :=
  exists_isTapeLaw stdLaw

/-- The Gaussian stream of the standard laws is a standard law, with the identity as decoding. -/
theorem isStdLaw_stdLaw_gauss : IsStdLaw ((stdLaw Stream.gauss).map id) := by
  rw [Measure.map_id]
  exact isStdLaw_gaussianReal

/-- **The quadratic form of a Gaussian probe is square integrable.** -/
theorem memLp_quadForm_gaussian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (quadForm A) 2 (probeLaw id (stdLaw Stream.gauss) n) := by
  have e : probeLaw id (stdLaw Stream.gauss) n = Measure.pi fun _ : Fin n => gaussianReal 0 1 := by
    rw [probeLaw]
    exact Measure.map_id
  rw [e]
  have h4 : ∀ i : Fin n, MemLp (fun g : Fin n → ℝ => g i) 4
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := fun i =>
    (memLp_id_gaussianReal (μ := 0) (v := 1) 4).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)
  have hT : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [← two_mul, show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
      ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]⟩
  refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => ?_
  have e2 : (fun g : Fin n → ℝ => g i * A i j * g j) = fun g => A i j * (g i * g j) := by
    funext g
    ring
  rw [e2]
  exact ((h4 j).mul' (r := 2) (h4 i)).const_mul (A i j)

/-- The probes of the standard Gaussian stream are isotropic. -/
theorem isIsotropic_probeLaw_stdLaw (n : ℕ) :
    IsIsotropic (probeLaw id (stdLaw Stream.gauss) n) :=
  isIsotropic_probeLaw measurable_id isStdLaw_stdLaw_gauss n

/-- Every matrix is bounded in the Euclidean norm, with the square of its Frobenius norm: the
hypothesis `‖A v‖² ≤ a ‖v‖²` of the noisy power iteration can be met. -/
theorem sqNorm_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    sqNorm (A.mulVec v) ≤ (∑ i, ∑ j, A i j ^ 2) * sqNorm v := by
  simp only [sqNorm]
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) v

/-! ### An interpretation in exact arithmetic over the reals -/

variable {n : ℕ} {Tst : Type}

/-- The block functions of the operations of `ROp` over the real numbers, in exact arithmetic. -/
noncomputable def randFns (A : Matrix (Fin n) (Fin n) ℝ) : ROp → BlockFn ℝ
  | .draw => .draw Stream.gauss
  | .gauss => .drawVec Stream.gauss
  | .operator .matvec => exactMatvecFn A
  | .dot => .of2 1 (fun d => d.headD 0) (fun d => d.headD 0) (fun _ => 1) fun _ x y =>
      some [∑ i, decv id n x i * decv id n y i]
  | .add => .bin fun a b => some (a + b)
  | .nrm2 => .of1 1 (fun d => d.headD 0) (fun _ => 1) fun _ x =>
      some [√(∑ i, decv id n x i ^ 2)]
  | .mulc q => .un fun a => some (q * a)
  | .axpy => .of3 1 (fun _ => 1) (fun d => d.headD 0) (fun d => d.headD 0) (fun d => d.headD 0)
      fun _ a x y => some (List.ofFn fun i => decv id n y i + vec a 0 * decv id n x i)

/-- **Witness**: for every matrix, the interpretation by exact real arithmetic meets the
contracts of the randomized examples, and its operations read the tape only in the registered
windows. -/
theorem exists_isRandLin (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ I : Interp ROp Tst ℝ, IsRandLin id A I ∧ ∀ o, I.TapeLocal o (randWindow o) := by
  have hfn := fun o => Interp.ofFns_isFn (Tst := Tst) (randFns A) .total o AnyOperands
  refine ⟨Interp.ofFns (randFns A), ⟨⟨hfn .draw, ?_, ?_, ?_, ?_, fun q => ?_, ?_⟩, ?_⟩, fun o => ?_⟩
  · exact Interp.IsFn.meets_matvec (A := A) (hfn (.operator .matvec))
  · refine (hfn .dot).meets_rel (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) ?_
    intro d w xs m ins outs hnd _ hadm hr _
    obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hnd
    obtain rfl : n = k := hadm.1.symm
    obtain ⟨x, y, xs, ys, rfl, hx, hy, rfl⟩ := Mem.readBlocks_two hr
    exact ⟨[[∑ i, decv id n xs i * decv id n ys i]], by simp [randFns, BlockFn.of2], rfl,
      Fin.sum_univ_eq_sum_range (fun i => vec xs i * vec ys i) n⟩
  · refine (hfn .add).meets_rel (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) ?_
    intro d w xs m ins outs hnd _ hadm hr _
    obtain ⟨x, y, xs, ys, rfl, hx, hy, rfl⟩ := Mem.readBlocks_two hr
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hx)
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hy)
    exact ⟨[[a + b]], by simp [randFns, BlockFn.bin], rfl, rfl⟩
  · refine (hfn .nrm2).meets_rel (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) ?_
    intro d w xs m ins outs hnd _ hadm hr _
    obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hnd
    obtain rfl : n = k := hadm.1.symm
    obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hr
    exact ⟨[[√(∑ i, decv id n xs i ^ 2)]], by simp [randFns, BlockFn.of1], rfl,
      congrArg Real.sqrt (Fin.sum_univ_eq_sum_range (fun i => vec xs i ^ 2) n)⟩
  · refine (hfn (.mulc q)).meets_rel (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) ?_
    intro d w xs m ins outs hnd _ hadm hr _
    obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hr
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hx)
    exact ⟨[[(q : ℝ) * a]], by simp [randFns, BlockFn.un], rfl, rfl⟩
  · refine (hfn .axpy).meets_rel (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) ?_
    intro d w xs m ins outs hnd _ hadm hr _
    obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hnd
    obtain rfl : n = k := hadm.1.symm
    obtain ⟨a, x, y, as, xs, ys, rfl, ha, hx, hy, rfl⟩ := Mem.readBlocks_three hr
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock ha)
    exact ⟨[List.ofFn fun i => decv id n ys i + vec [a] 0 * decv id n xs i],
      by simp [randFns, BlockFn.of3], by simp [axpyExactRel, axpyRel], by
      intro j hj
      exact congrFun (decv_ofFn (fun i : Fin n =>
        decv id n ys i + vec [a] 0 * decv id n xs i)) ⟨j, hj⟩⟩
  · exact (hfn .gauss).meets_drawRel fun _ _ _ _ => trivial
  · have := Interp.ofFns_tapeLocal (Tst := Tst) (randFns A) o
    cases o
    case operator op => cases op; exact this
    all_goals exact this

/-- **Joint witness of the randomized examples at the law level**: for every matrix, an
interpretation meeting the contracts of the exact operations and the draws with tape-local
operations, a random tape with the standard laws, whose Gaussian stream decodes to a standard
law and whose probes are isotropic. This is the contract set of `runsLaw_hutch`,
`runsLaw_hutch_link` and `runsLaw_npow_link`. -/
theorem exists_isRandLin_isTapeLaw (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (I : Interp ROp Tst ℝ) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (ξ : Ω → Tape ℝ), IsRandLin id A I ∧ (∀ o, I.TapeLocal o (randWindow o)) ∧
        IsTapeLaw stdLaw P ξ ∧ IsStdLaw ((stdLaw Stream.gauss).map id) ∧
        IsIsotropic (probeLaw id (stdLaw Stream.gauss) n) := by
  obtain ⟨I, h1, h2⟩ := exists_isRandLin (Tst := Tst) A
  obtain ⟨Ω, mΩ, P, ξ, h3⟩ := exists_isTapeLaw_stdLaw
  exact ⟨I, Ω, mΩ, P, ξ, h1, h2, h3, isStdLaw_stdLaw_gauss, isIsotropic_probeLaw_stdLaw n⟩

/-! ### The noisy product -/

/-- The block function of a noisy product over the reals: the output block is `N` of the input
block and of the window. -/
noncomputable def nmvFn (N : (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ) : BlockFn ℝ where
  nd := 1
  stream := Stream.gauss
  win d := d.headD 0
  inLens d := [d.headD 0]
  outLens d := [d.headD 0]
  fn _ w xs := match xs with
    | [x] => some [List.ofFn (N (decv id n x) fun i => vec w i)]
    | _ => none

/-- **Witness**: the contract of `nmv` can be met for every noise function, by the
interpretation that applies it to the window. -/
theorem exists_isNoisy (N : (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ) :
    ∃ J : Interp NOp Tst ℝ, IsNoisy id N J := by
  refine ⟨Interp.ofFns fun _ => nmvFn N,
    (Interp.ofFns_isFn (Tst := Tst) (fun _ : NOp => nmvFn N) .total .nmv AnyOperands).meets_rel
      (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_⟩
  intro d w xs m ins outs hnd _ hadm hr _
  obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain rfl : k = n := hadm.1
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hr
  exact ⟨[List.ofFn (N (decv id k xs) fun i => vec w i)], rfl, by simp [nmvRel],
    by simp [nmvRel, decv_ofFn]⟩

/-- **Joint witness of the noisy power iteration at the law level**: for every matrix and every
`σ`, an interpretation meeting the contract of `nmv` for a noise function with the conditional
law of `A v + σ ‖v‖ g`, `g` isotropic, and a random tape with the standard laws. This is the
contract set of `runsLaw_npow`. -/
theorem exists_isNoisy_isNoisyMv (A : Matrix (Fin n) (Fin n) ℝ) (σ : ℝ) :
    ∃ (J : Interp NOp Tst ℝ) (N : (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ)
      (ν : Measure (Fin n → ℝ)) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (ξ : Ω → Tape ℝ), IsNoisy id N J ∧ IsNoisyMv A σ ν (stdLaw Stream.gauss) N ∧
        IsTapeLaw stdLaw P ξ := by
  obtain ⟨J, hJ⟩ := exists_isNoisy (Tst := Tst) (noiseFn id A σ)
  obtain ⟨Ω, mΩ, P, ξ, h⟩ := exists_isTapeLaw_stdLaw
  exact ⟨J, _, _, Ω, mΩ, P, ξ, hJ, isNoisyMv_noiseFn measurable_id isStdLaw_stdLaw_gauss A σ, h⟩

end NLAlib.Ops.Examples
