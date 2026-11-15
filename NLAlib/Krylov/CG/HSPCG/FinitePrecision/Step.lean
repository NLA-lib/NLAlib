/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Pairing
public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Bounds

/-!
# Active rounded preconditioned CG steps

The existing Hestenes–Stiefel tree retains all four computed vectors. Mathematical input
margins imply positivity of its computed numerator and curvature, hence both scalar division
laws apply. The two actual residual pairings are recorded separately.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.RoundBounds` records the perturbed PCG recurrence.
* `NLAlib.Krylov.CG.HSPCG.Rounded.step_spec` gives total active-step execution.
* `NLAlib.Krylov.CG.HSPCG.Rounded.step_writes` exposes the actual stored output state.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded

open Ops
open scoped Matrix

/-- Input dot-product margins make the computed numerator and curvature positive for every
matrix-vector product admitted by the system operation's normwise error contract. -/
def Margins {n : ℕ} (em ed : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (s : PCGState ℝ (Fin n)) : Prop :=
  ed * ∑ i, |s.r i * s.z i| < s.r ⬝ᵥ s.z ∧
    ∀ q : Fin n → ℝ,
      ‖WithLp.toLp 2 (A *ᵥ s.p - q)‖ ≤ em * specNorm A * ‖WithLp.toLp 2 s.p‖ →
      ed * ∑ i, |s.p i * q i| < s.p ⬝ᵥ q

/-- The local PCG recurrence retains the actual two residual pairings, actual system
product and fixed approximate preconditioner action. Scalar and componentwise vector errors
have independent operation-level allowances. [Saad2003, Algorithm 9.1]. -/
def RoundBounds {n : ℕ} (em u ed ea : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    {P : Matrix (Fin n) (Fin n) ℝ} (O : MatvecOracle P)
    (s s' : PCGState ℝ (Fin n)) (rho rho' : ℝ) : Prop :=
  ∃ q : Fin n → ℝ, ∃ curvature alpha beta : ℝ,
    ‖WithLp.toLp 2 (A *ᵥ s.p - q)‖ ≤ em * specNorm A * ‖WithLp.toLp 2 s.p‖ ∧
    0 < rho ∧ 0 < curvature ∧
    |rho - s.r ⬝ᵥ s.z| ≤ ed * ∑ i, |s.r i * s.z i| ∧
    |curvature - s.p ⬝ᵥ q| ≤ ed * ∑ i, |s.p i * q i| ∧
    |alpha - rho / curvature| ≤ u * |rho / curvature| ∧
    (∀ i, |s'.x i - (s.x i + alpha * s.p i)| ≤ ea * (|s.x i| + |alpha * s.p i|)) ∧
    (∀ i, |s'.r i - (s.r i - alpha * q i)| ≤ ea * (|s.r i| + |alpha * q i|)) ∧
    s'.z = O.mulVec s'.r ∧
    |rho' - s'.r ⬝ᵥ s'.z| ≤ ed * ∑ i, |s'.r i * s'.z i| ∧
    |beta - rho' / rho| ≤ u * |rho' / rho| ∧
    (∀ i, |s'.p i - (s'.z i + beta * s.p i)| ≤ ea * (|s'.z i| + |beta * s.p i|))

/-- Componentwise operation bounds give the normwise local errors used by the existing
PCG run model. Both actual residual pairings and the fixed oracle action are preserved.
[Higham2002, §3.1]. -/
theorem RoundBounds.exists_run_errors {n : ℕ} {em u ed ea e : ℝ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P}
    {s s' : PCGState ℝ (Fin n)} {rho rho' : ℝ}
    (h : RoundBounds em u ed ea A O s s' rho rho')
    (hu : 0 ≤ u) (hd : 0 ≤ ed) (ha : 0 ≤ ea)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ed ≤ e) (hae : ea ≤ e) :
    ∃ q : Fin n → ℝ, ∃ curv alpha beta eg eb : ℝ,
      ‖WithLp.toLp 2 (A *ᵥ s.p - q)‖ ≤ e * specNorm A * ‖WithLp.toLp 2 s.p‖ ∧
      0 < rho ∧ 0 < curv ∧
      |rho - s.r ⬝ᵥ s.z| ≤ e * ‖WithLp.toLp 2 s.r‖ * ‖WithLp.toLp 2 s.z‖ ∧
      |curv - s.p ⬝ᵥ q| ≤ e * ‖WithLp.toLp 2 s.p‖ * ‖WithLp.toLp 2 q‖ ∧
      alpha = rho / curv * (1 + eg) ∧ |eg| ≤ e ∧
      beta = rho' / rho * (1 + eb) ∧ |eb| ≤ e ∧
      s'.z = O.mulVec s'.r ∧
      |rho' - s'.r ⬝ᵥ s'.z| ≤ e * ‖WithLp.toLp 2 s'.r‖ * ‖WithLp.toLp 2 s'.z‖ ∧
      ‖WithLp.toLp 2 (s.x + alpha • s.p - s'.x)‖ ≤
        e * (‖WithLp.toLp 2 s.x‖ + |alpha| * ‖WithLp.toLp 2 s.p‖) ∧
      ‖WithLp.toLp 2 (s.r - alpha • q - s'.r)‖ ≤
        e * (‖WithLp.toLp 2 s.r‖ + |alpha| * ‖WithLp.toLp 2 q‖) ∧
      ‖WithLp.toLp 2 (s'.z + beta • s.p - s'.p)‖ ≤
        e * (‖WithLp.toLp 2 s'.z‖ + |beta| * ‖WithLp.toLp 2 s.p‖) := by
  obtain ⟨q, curv, alpha, beta, hmv, hrho, hcurv, hn, hc, halpha, hx, hr, hz, hn',
    hbeta, hp⟩ := h
  obtain ⟨eg, heg, healpha⟩ := HSCG.Carried.Rounded.exists_relative_error hu halpha
  obtain ⟨eb, heb, hebeta⟩ := HSCG.Carried.Rounded.exists_relative_error hu hbeta
  have hvec {a : ℝ} {x y z : Fin n → ℝ}
      (hh : ∀ i, |z i - (y i + a * x i)| ≤ ea * (|y i| + |a * x i|)) :
      ‖WithLp.toLp 2 (y + a • x - z)‖ ≤
        e * (‖WithLp.toLp 2 y‖ + |a| * ‖WithLp.toLp 2 x‖) := by
    rw [← neg_sub z, WithLp.toLp_neg, norm_neg]
    exact (HSCG.Carried.Rounded.norm_update_le ha hh).trans
      (mul_le_mul_of_nonneg_right hae (by positivity))
  have hdot {v : ℝ} {x y : Fin n → ℝ}
      (hh : |v - x ⬝ᵥ y| ≤ ed * ∑ i, |x i * y i|) :
      |v - x ⬝ᵥ y| ≤ e * ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
    calc
      _ ≤ ed * (‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖) :=
        hh.trans (mul_le_mul_of_nonneg_left (HSCG.Carried.Rounded.sum_abs_mul_le x y) hd)
      _ ≤ e * (‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖) :=
        mul_le_mul_of_nonneg_right hde (by positivity)
      _ = _ := (mul_assoc ..).symm
  refine ⟨q, curv, alpha, beta, eg, eb,
    hmv.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hem (specNorm_nonneg _)) (norm_nonneg _)),
    hrho, hcurv, hdot hn, hdot hc, healpha, heg.trans hue, hebeta, heb.trans hue,
    hz, hdot hn', hvec hx, ?_, hvec hp⟩
  have hh := hvec (a := -alpha) (x := q) (y := s.r) (z := s'.r)
    (by simpa only [neg_mul, ← sub_eq_add_neg, abs_neg] using hr)
  simpa only [sub_eq_add_neg, neg_smul, abs_neg] using hh

variable {Op Tst : Type}
  [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]

/-- The stored step relation accepts mathematical input margins and returns the computed
state with both actual pairings, rather than assuming that the step succeeds. -/
@[simps (attr := storeNF)]
noncomputable def stepRel {n : ℕ} (em u : ℝ) (ε : Blas1Err)
    (A : Matrix (Fin n) (Fin n) ℝ) {P : Matrix (Fin n) (Fin n) ℝ}
    (O : MatvecOracle P)
    (Q : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ → Prop := fun _ _ _ _ => True) :
    BlockRel ℝ where
  nd := 1
  inLens d := [d.headD 0, d.headD 0, d.headD 0, d.headD 0]
  outLens d := [d.headD 0, d.headD 0, d.headD 0, d.headD 0]
  dom _ X _ := match X with
    | [xs, rs, zs, ps] => Margins em (ε.dot n) A (decodedState id n xs rs zs ps)
    | _ => False
  rel _ X _ Y := match X, Y with
    | [xs, rs, zs, ps], [xs', rs', zs', ps'] => ∃ rho rho',
        RoundBounds em u (ε.dot n) ε.axpy A O (decodedState id n xs rs zs ps)
          (decodedState id n xs' rs' zs' ps') rho rho' ∧
        Q n (decv id n rs) (decv id n zs) rho ∧
        Q n (decv id n rs') (decv id n zs') rho'
    | _, _ => False

-- The framed four-state PCG proof needs more than the default elaboration budget.
set_option maxHeartbeats 600000 in
-- Thirteen framed calls and three scoped allocations require extra elaboration work.
/-- Input numerical margins guarantee both positive computed divisors, and local rounded
contracts establish the actual four-vector PCG update. -/
theorem step_spec_with_pairings {F : Machine ℝ} {n : ℕ} {em u : ℝ} {ε : Blas1Err}
    {A P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    {ok : ℕ → Prop}
    {Q : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ → Prop}
    (hS : IsScalar F I) (hF : StdModel u id F)
    (hB : IsBlas1 id ε ok I) (hok : ok n) (hA : IsMatvec id A (em * specNorm A) I)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n))
    (hD : I.Meets .total (Has.inj Blas1Op.dot)
      ((dotEvidenceRel ε Q).spec (OutApart ok))) :
    (stepImpl (Op := Op) (Tst := Tst)).Triple I .total
      ((stepRel em u ε A O Q).spec (StepOperands n)) := by
  have hO := meets_preconditioner_oracle hP
  cert_intro [m] (x, r, z, p) → (x', r', z', p') reads (xs, rs, zs, ps)
  obtain ⟨hd, hx, hr, hz, hp, hxr, hxz, hxp, hrz, hrp, hzp⟩ := hadm
  subst m x' r' z' p'
  change Margins em (ε.dot n) A (decodedState id n xs rs zs ps) at hdom
  refine writes_allocs (lens := [.var 0, .var 0, .const 4]) (ns := [n, n, 4]) rfl
    fun s₁ hs₁ hlen hB₁ => ?_
  have hq : s₁.len μ.store.length = n := by simpa using hlen 0 (by simp)
  have hu : s₁.len (μ.store.length + 1) = n := by simpa using hlen 1 (by simp)
  have ht : s₁.len (μ.store.length + 2) = 4 := by simpa using hlen 2 (by simp)
  dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
    List.length_cons, List.length_nil, Nat.add_zero] at *
  step hD as m₁ hfr₁ ⟨hpos₁, ρ, hρ, heρ, hPair⟩
  step hA as m₂ hfr₂ ⟨hpos₂, qs, hqs, heq⟩
  step hB.dot as m₃ hfr₃ ⟨hpos₃, pq, hpq, hepq⟩
  step (hS .div) as m₄ hfr₄ ⟨hpos₄, a, ha, hea⟩
  step hB.axpy as m₅ hfr₅ ⟨hpos₅, xs', hxs', hex⟩
  step (hS .neg) as m₆ hfr₆ ⟨hpos₆, na, hna, hena⟩
  step hB.axpy as m₇ hfr₇ ⟨hpos₇, rs', hrs', her⟩
  step hO as m₈ hfr₈ ⟨hpos₈, zs', hzs', hez⟩
  step hD as m₉ hfr₉ ⟨hpos₉, ρ', hρ', heρ', hPair'⟩
  have hx₉ : m₉.store.readBlock x.1 x.2 n = some xs' := by kept
  have hr₉ : m₉.store.readBlock r.1 r.2 n = some rs' := by kept
  have hz₉ : m₉.store.readBlock z.1 z.2 n = some zs' := by kept
  have hp₉ : m₉.store.readBlock p.1 p.2 n = some ps := by kept
  have hρ₉ : m₉.store.get (μ.store.length + 2) 0 = some ρ := by kept
  clear hfr₁ hfr₂ hfr₃ hfr₄ hfr₅ hfr₆ hfr₇ hfr₈
  step (hS .div) as m₁₀ hfr₁₀ ⟨hpos₁₀, b, hb, heb⟩
  step hB.copy as m₁₁ hfr₁₁ ⟨hpos₁₁, us, hus, hcopy₁⟩
  step hB.axpy as m₁₂ hfr₁₂ ⟨hpos₁₂, ps', hps', hep⟩
  step hB.copy as m₁₃ hfr₁₃ ⟨hpos₁₃, ps'', hps'', hcopy₂⟩
  have hρpos : 0 < id ρ := heρ.pos_of_margin hdom.1
  have hpqpos : 0 < id pq := hepq.pos_of_margin (hdom.2 _ heq)
  have halpha := hea ▸ hF.div ρ pq hpqpos.ne'
  have hbeta := heb ▸ hF.div ρ' ρ hρpos.ne'
  have hnad : id na = -id a := hena ▸ hF.neg a
  have hrvec (i : Fin n) := her.decoded i
  simp only [hnad, neg_mul, ← sub_eq_add_neg, abs_neg] at hrvec
  subst us ps''
  intro s₂ hs₂ hB₂
  refine ⟨by simp [stepRel, hpos₁₃, hpos₁₂, hpos₁₁, hpos₁₀, hpos₉, hpos₈, hpos₇,
    hpos₆, hpos₅, hpos₄, hpos₃, hpos₂, hpos₁], [xs', rs', zs', ps'], ?_, ?_⟩
  · exact Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept)
      (Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl)))
  · exact ⟨id ρ, id ρ', ⟨decv id n qs, id pq, id a, id b, heq, hρpos, hpqpos,
      heρ.decoded, hepq.decoded, halpha, hex.decoded, hrvec, hez, heρ'.decoded,
      hbeta, hep.decoded⟩, hPair, hPair'⟩

/-- Input numerical margins guarantee a total rounded step. This specializes the shared
pairing-evidence proof to ordinary numerical BLAS contracts. -/
theorem step_spec {F : Machine ℝ} {n : ℕ} {em u : ℝ} {ε : Blas1Err}
    {A P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    {ok : ℕ → Prop} (hS : IsScalar F I) (hF : StdModel u id F)
    (hB : IsBlas1 id ε ok I) (hok : ok n) (hA : IsMatvec id A (em * specNorm A) I)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n)) :
    (stepImpl (Op := Op) (Tst := Tst)).Triple I .total
      ((stepRel em u ε A O).spec (StepOperands n)) :=
  step_spec_with_pairings hS hF hB hok hA hP (dot_trivial_meets hB.dot)

/-- Additional dot pairing evidence is retained by the total active step, together with its
actual stored four-vector state and local perturbed recurrence. Both scalar divisors follow
from the input mathematical margins. -/
theorem step_writes_with_pairings {F : Machine ℝ} {n : ℕ} {em u : ℝ} {ε : Blas1Err}
    {A P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    {ok : ℕ → Prop}
    {Q : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ → Prop}
    (hS : IsScalar F I) (hF : StdModel u id F)
    (hB : IsBlas1 id ε ok I) (hok : ok n) (hA : IsMatvec id A (em * specNorm A) I)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n))
    (hD : I.Meets .total (Has.inj Blas1Op.dot)
      ((dotEvidenceRel ε Q).spec (OutApart ok))) {τ : Tape ℝ} {μ : Mem ℝ}
    {x r z p : ℕ × ℕ} {s : PCGState ℝ (Fin n)}
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [x, r, z, p]) (hstate : StoresState id n x r z p s μ)
    (hdom : Margins em (ε.dot n) A s) (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    Writes .total I τ step (Env.frame [n] [x, r, z, p, x, r, z, p])
      (Fp.blocks [x, r, z, p] [n, n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ s' rho rho', StoresState id n x r z p s' μ' ∧
        RoundBounds em u (ε.dot n) ε.axpy A O s s' rho rho' ∧
        Q n s.r s.z rho ∧ Q n s'.r s'.z rho') μ := by
  obtain ⟨xs, rs, zs, ps, hread, hstate⟩ := hstate
  refine ((step_spec_with_pairings hS hF hB hok hA hP hD).writes_blocks rfl
    ⟨rfl, x, r, z, p, rfl, rfl, hxr, hxz, hxp, hrz, hrp, hzp⟩
    ((μ.live_append _ _).mpr ⟨hl, hl⟩) hread
    (by change Margins em (ε.dot n) A (decodedState id n xs rs zs ps); rwa [hstate])
    hz (by disjoint)).mono le_rfl ?_
  rintro μ' _ ⟨hpos, ys, hys, hrel⟩
  obtain ⟨xs', rs', zs', ps', rfl⟩ := List.length_eq_four.mp
    (by simpa [stepRel] using congrArg List.length (Mem.map_length_of_readBlocks hys))
  obtain ⟨rho, rho', hb, hPair, hPair'⟩ := hrel
  exact ⟨by simpa [stepRel] using hpos, decodedState id n xs' rs' zs' ps', rho, rho',
    ⟨xs', rs', zs', ps', hys, rfl⟩, by simpa only [hstate] using hb,
    by simpa only [← hstate, decodedState] using hPair, hPair'⟩

/-- A total active rounded step retains both actual pairings as the fixed scalar dot kernel
on the initial and final finite vectors. Identical vector operands therefore give identical
recomputed incoming and preceding outgoing pairings. -/
theorem step_writes_function {F : Machine ℝ} {n : ℕ} {em u : ℝ} {ε : Blas1Err}
    {A P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    {ok : ℕ → Prop}
    (hS : IsScalar F I) (hF : StdModel u id F)
    (hB : IsBlas1 id ε ok I) (hok : ok n) (hA : IsMatvec id A (em * specNorm A) I)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n))
    (hD : I.IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn F) (OutApart (fun _ => True)))
    {τ : Tape ℝ} {μ : Mem ℝ}
    {x r z p : ℕ × ℕ} {s : PCGState ℝ (Fin n)}
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [x, r, z, p]) (hstate : StoresState id n x r z p s μ)
    (hdom : Margins em (ε.dot n) A s) (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    Writes .total I τ step (Env.frame [n] [x, r, z, p, x, r, z, p])
      (Fp.blocks [x, r, z, p] [n, n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ s' rho rho', StoresState id n x r z p s' μ' ∧
        RoundBounds em u (ε.dot n) ε.axpy A O s s' rho rho' ∧
        rho = pairingValue F s.r s.z ∧ rho' = pairingValue F s'.r s'.z) μ := by
  exact step_writes_with_pairings hS hF hB hok hA hP (dot_function_meets hB.dot hD)
    hxr hxz hxp hrz hrp hzp hl hstate hdom hz

/-- A total active step updates the actual stored four-vector state and exposes its local
perturbed recurrence, with both scalar divisors justified by mathematical margins. -/
theorem step_writes {F : Machine ℝ} {n : ℕ} {em u : ℝ} {ε : Blas1Err}
    {A P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    {ok : ℕ → Prop} (hS : IsScalar F I) (hF : StdModel u id F)
    (hB : IsBlas1 id ε ok I) (hok : ok n) (hA : IsMatvec id A (em * specNorm A) I)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n)) {τ : Tape ℝ} {μ : Mem ℝ}
    {x r z p : ℕ × ℕ} {s : PCGState ℝ (Fin n)}
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [x, r, z, p]) (hstate : StoresState id n x r z p s μ)
    (hdom : Margins em (ε.dot n) A s) (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    Writes .total I τ step (Env.frame [n] [x, r, z, p, x, r, z, p])
      (Fp.blocks [x, r, z, p] [n, n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ s' rho rho', StoresState id n x r z p s' μ' ∧
        RoundBounds em u (ε.dot n) ε.axpy A O s s' rho rho') μ := by
  refine (step_writes_with_pairings hS hF hB hok hA hP (dot_trivial_meets hB.dot)
    hxr hxz hxp hrz hrp hzp hl hstate hdom hz).mono le_rfl ?_
  rintro μ' _ ⟨hpos, s', rho, rho', hstored, hbounds, _, _⟩
  exact ⟨hpos, s', rho, rho', hstored, hbounds⟩

/-- The same active step has the existing tree's exact primitive counts and scratch bound,
with its actual output satisfying the perturbed recurrence. -/
theorem runs_step {F : Machine ℝ} {n : ℕ} {em u : ℝ} {ε : Blas1Err}
    {A P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    {ok : ℕ → Prop} (hS : IsScalar F I) (hF : StdModel u id F)
    (hB : IsBlas1 id ε ok I) (hok : ok n) (hA : IsMatvec id A (em * specNorm A) I)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n)) (W : Op → List ℕ → ℕ)
    {τ : Tape ℝ} {μ : Mem ℝ} {x r z p : ℕ × ℕ} {xs rs zs ps : List ℝ}
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [x, r, z, p])
    (hread : μ.readBlocks [x, r, z, p] [n, n, n, n] = some [xs, rs, zs, ps])
    (hdom : Margins em (ε.dot n) A (decodedState id n xs rs zs ps))
    (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    ConditionalRuns I W τ step (Env.frame [n] [x, r, z, p, x, r, z, p]) μ
      (stepCount n) (stepPeak W n)
      ((stepRel em u ε A O).Post [n] [xs, rs, zs, ps] [x, r, z, p] [] μ) := by
  refine ((step_spec hS hF hB hok hA hP).runs_rel W (d := [n])
    (ins := [x, r, z, p]) (outs := [x, r, z, p]) rfl
    ⟨rfl, x, r, z, p, rfl, rfl, hxr, hxz, hxp, hrz, hrp, hzp⟩
    ((μ.live_append _ _).mpr ⟨hl, hl⟩) hread hdom hz).mono
      (le_of_eq (staticCost_step ..)) (staticPeak_step_le ..) ?_
  intro μ' h
  exact h

end NLAlib.Krylov.CG.HSPCG.Rounded
