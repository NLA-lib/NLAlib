/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Tape
public import NLAlib.Eigensolvers.SpectralBisection
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Levels

/-!
# The samples a spectral bisection run reads

`NLAlib.eigh` on a machine of a semantics uses its samples only through the samplers, and only at
the nodes it reaches (the seed and the leading block of each test matrix). So the output on the tape
machine with the tree of sample positions at the slots (`NLAlib.eighTapeMachine`,
`NLAlib.eighSlotTree`) is the output on the ideal machine with the tree of ideal samples
(`NLAlib.eighIdealTree`), for a rounding of the tape that does not depend on the position. Also the
σ-algebras of the tape positions and the law of the sample a node reads, which the lazy sampling of
`NLAlib/Eigensolvers/SpectralBisectionSamples/Lazy.lean` uses.

## Main results

* `NLAlib.eigh_toFloatMachine_map_samples`, `NLAlib.eigh_congr_samples`,
  `NLAlib.eigh_eighTapeMachine_eq_eigh_eighIdealTree`: from positions to ideal samples.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

open Computation

/-! ### From positions to ideal samples -/

/-- The Newton–Schulz loop on two machines of one semantics that differ only in their samplers
(private helper of `NLAlib.eigh_toFloatMachine_map_samples`). -/
private theorem newtonSchulzSign_toFloatMachine_samplers {P K : Type} [Inhabited K]
    {Su Sg Su' Sg' : Type} (sem : ScalarSem P K) (p : P)
    (toNat : K → ℕ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K)
    (normal : Sg → K × K) (unif' : K → Su' → K) (normal' : Sg' → K × K) {k : ℕ}
    (b x : K) (N : ℕ) (B : Matrix (Fin k) (Fin k) (K × K)) :
    newtonSchulzSign (sem.toFloatMachine p toNat mm qr unif normal) b x N B =
      newtonSchulzSign (sem.toFloatMachine p toNat mm qr unif' normal') b x N B := by
  suffices h : ∀ η N (B' : Matrix (Fin k) (Fin k) (K × K)),
      newtonSchulzLoop (sem.toFloatMachine p toNat mm qr unif normal) η N B' =
        newtonSchulzLoop (sem.toFloatMachine p toNat mm qr unif' normal') η N B' from h _ N _
  intro η N
  induction N with
  | zero => intro B'; rfl
  | succ N ih => intro B'; simp only [newtonSchulzLoop, ih]; rfl

/-- The deflation of a leading block on two machines of one semantics whose normal samplers agree
along $g$. The equality holds for every leading block with size at most the sample size.
No printed source. -/
theorem deflate_leadingBlock_toFloatMachine_map {P K : Type} [Inhabited K]
    {Su Sg Su' Sg' : Type} [Inhabited Sg] [Inhabited Sg'] (sem : ScalarSem P K) (p : P)
    (toNat : K → ℕ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K)
    (normal : Sg → K × K) (unif' : K → Su' → K) (normal' : Sg' → K × K) (g : Sg → Sg')
    (hn : ∀ z, normal z = normal' (g z)) {n k : ℕ} (hk : k ≤ n) (r : ℕ)
    (Pm : Matrix (Fin k) (Fin k) (K × K)) (G : Matrix (Fin n) (Fin n) Sg) :
    deflate (sem.toFloatMachine p toNat mm qr unif normal) r Pm (leadingBlock k G) =
      deflate (sem.toFloatMachine p toNat mm qr unif' normal') r Pm
        (leadingBlock k (G.map g)) := by
  have hG : (leadingBlock k G).map normal = (leadingBlock k (G.map g)).map normal' := by
    refine Matrix.ext fun i j => ?_
    have hi : (i : ℕ) < n ∧ (j : ℕ) < n := ⟨i.2.trans_le hk, j.2.trans_le hk⟩
    simp only [leadingBlock, Matrix.map_apply, Matrix.of_apply, dif_pos hi, hn]
  simp only [deflate]
  exact congrArg _ (by rw [show (leadingBlock k G).map
    (sem.toFloatMachine p toNat mm qr unif normal).normal = _ from hG]; rfl)

/-- One step on two machines of one semantics whose samplers agree along $f$ and $g$ (private
helper of `NLAlib.eigh_toFloatMachine_map_samples`). -/
private theorem eighStep_toFloatMachine_map {P K : Type} [Inhabited K]
    {Su Sg Su' Sg' : Type} [Inhabited Sg] [Inhabited Sg'] (sem : ScalarSem P K) (p : P)
    (toNat : K → ℕ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K)
    (normal : Sg → K × K) (unif' : K → Su' → K) (normal' : Sg' → K × K) (f : Su → Su')
    (g : Sg → Sg') (hu : ∀ c v, unif c v = unif' c (f v)) (hn : ∀ z, normal z = normal' (g z))
    (n signFuel : ℕ) (R₀ β : K) {k : ℕ} (hk : k ≤ n) (A : Matrix (Fin k) (Fin k) (K × K))
    (R ε : K) (ℓ : ℕ) (s : EighSample Su Sg n) :
    eighStep (sem.toFloatMachine p toNat mm qr unif normal) n signFuel R₀ β A R ε ℓ s =
      eighStep (sem.toFloatMachine p toNat mm qr unif' normal') n signFuel R₀ β A R ε ℓ
        (f s.1, fun b => (s.2 b).map g) := by
  obtain rfl : unif = fun c v => unif' c (f v) := funext fun c => funext (hu c)
  obtain rfl : normal = fun z => normal' (g z) := funext hn
  by_cases hk1 : k ≤ 1
  · simp only [eighStep, if_pos hk1]; rfl
  simp only [eighStep, if_neg hk1]
  generalize_proofs h₁ h₂
  revert h₁ h₂
  rw [newtonSchulzSign_toFloatMachine_samplers sem p toNat mm qr _ _ unif' normal']
  intro h₁ h₂
  simp only [deflate_leadingBlock_toFloatMachine_map sem p toNat mm qr _ _ unif' normal' g hn hk]
  rfl

/-- `NLAlib.eigh` sees its samples only through the samplers: on two machines of the same
semantics, conversion and black boxes whose samplers agree along maps $f$ of seeds and $g$ of
Gaussian samples ($\mathrm{unif}(c, v) = \mathrm{unif}'(c, f(v))$,
$\mathrm{normal}(z) = \mathrm{normal}'(g(z))$), the output on a tree of samples is the output on the
tree mapped by $f$ and $g$. No printed source. -/
theorem eigh_toFloatMachine_map_samples {P K : Type} [Inhabited K] {Su Sg Su' Sg' : Type}
    [Inhabited Sg] [Inhabited Sg'] (sem : ScalarSem P K) (p : P) (toNat : K → ℕ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K) (normal : Sg → K × K)
    (unif' : K → Su' → K) (normal' : Sg' → K × K) (f : Su → Su') (g : Sg → Sg')
    (hu : ∀ c v, unif c v = unif' c (f v)) (hn : ∀ z, normal z = normal' (g z)) (signFuel ℓ : ℕ)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) (K × K)) (R₀ ε β : K)
    (s : List Bool → EighSample Su Sg n) :
    eigh (sem.toFloatMachine p toNat mm qr unif normal) signFuel ℓ A R₀ ε β s =
      eigh (sem.toFloatMachine p toNat mm qr unif' normal') signFuel ℓ A R₀ ε β
        (fun a => (f (s a).1, fun b => ((s a).2 b).map g)) := by
  suffices h : ∀ (fuel k : ℕ) (A : Matrix (Fin k) (Fin k) (K × K)) (R ε : K) (ℓ : ℕ)
      (s : List Bool → EighSample Su Sg n), k ≤ n →
      eighAux (sem.toFloatMachine p toNat mm qr unif normal) n signFuel R₀ β fuel A R ε ℓ s =
        eighAux (sem.toFloatMachine p toNat mm qr unif' normal') n signFuel R₀ β fuel A R ε ℓ
          (fun a => (f (s a).1, fun b => ((s a).2 b).map g)) from h _ n A R₀ ε ℓ s le_rfl
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro k A R ε ℓ s hk
    simp only [eighAux]
    rw [eighStep_toFloatMachine_map sem p toNat mm qr unif normal unif' normal' f g hu hn n signFuel
      R₀ β hk]
    generalize eighStep (sem.toFloatMachine p toNat mm qr unif' normal') n signFuel R₀ β A R ε ℓ
      (f (s []).1, fun b => ((s []).2 b).map g) = st
    cases st with
    | leaf U d => rfl
    | shift b A' σ => dsimp only; rw [ih _ A' _ _ _ _ hk]; rfl
    | split kp h Qp Qm Ap Am σ =>
      dsimp only
      rw [ih _ Ap _ _ _ _ (h.trans hk), ih _ Am _ _ _ _ ((Nat.sub_le _ _).trans hk)]
      rfl

/-- A step of `NLAlib.eighStep` reads its sample only through the seed and the leading blocks of
the test matrices of its size. -/
theorem eighStep_congr_sample {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    (N signFuel : ℕ) (R₀ β : F) {k : ℕ} (A : Matrix (Fin k) (Fin k) (F × F)) (R ε : F) (ℓ : ℕ)
    {t t' : EighSample Su Sg N} (h1 : t.1 = t'.1)
    (h2 : ∀ b, leadingBlock k (t.2 b) = leadingBlock k (t'.2 b)) :
    eighStep M N signFuel R₀ β A R ε ℓ t = eighStep M N signFuel R₀ β A R ε ℓ t' := by
  obtain ⟨v, G⟩ := t
  obtain ⟨v', G'⟩ := t'
  simp only at h1 h2
  subst h1
  unfold eighStep
  simp only [h2]

/-- The sample of a child is the sample below its side: the node at `b :: a` is the node at `a`
below the child on side `b`. -/
private lemma eighNodeAt_cons_of_eighChild {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) (N signFuel : ℕ) (R₀ β : F) (x c : EighNode F) (b : Bool)
    (a : List Bool) (s : List Bool → EighSample Su Sg N)
    (hc : eighChild M N signFuel R₀ β x (s []) b = some c) :
    eighNodeAt M N signFuel R₀ β (b :: a) x s =
      eighNodeAt M N signFuel R₀ β a c (fun a' => s (b :: a')) := by
  simp [eighNodeAt, hc]

/-- The budget-$f$ recursion `NLAlib.eighAux` from a node reads its samples only at the paths of
length below $f$ that the node reaches. Induction on the budget. -/
private lemma eighAux_congr_samples {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    (signFuel : ℕ) {n : ℕ} (R₀ β : F) (f : ℕ) :
    ∀ {k : ℕ} (A : Matrix (Fin k) (Fin k) (F × F)) (R ε : F) (ℓ : ℕ)
      {s s' : List Bool → EighSample Su Sg n},
      (∀ (a : List Bool) (y : EighNode F), a.length < f →
        eighNodeAt M n signFuel R₀ β a ⟨k, A, R, ε, ℓ⟩ s = some y →
          (s a).1 = (s' a).1 ∧ ∀ b, leadingBlock y.k ((s a).2 b) = leadingBlock y.k ((s' a).2 b)) →
      eighAux M n signFuel R₀ β f A R ε ℓ s = eighAux M n signFuel R₀ β f A R ε ℓ s' := by
  induction f with
  | zero => intro k A R ε ℓ s s' _; rfl
  | succ f ih =>
    intro k A R ε ℓ s s' H
    have H0 := H [] ⟨k, A, R, ε, ℓ⟩ (by simp) rfl
    have hstep := eighStep_congr_sample M n signFuel R₀ β A R ε ℓ (t := s []) (t' := s' [])
      H0.1 (fun b => H0.2 b)
    have hchild : ∀ (b : Bool) (c : EighNode F),
        eighChild M n signFuel R₀ β ⟨k, A, R, ε, ℓ⟩ (s []) b = some c →
        ∀ (a : List Bool) (y : EighNode F), a.length < f →
          eighNodeAt M n signFuel R₀ β a c (fun a' => s (b :: a')) = some y →
            (s (b :: a)).1 = (s' (b :: a)).1 ∧
              ∀ d, leadingBlock y.k ((s (b :: a)).2 d) = leadingBlock y.k ((s' (b :: a)).2 d) := by
      intro b c hc a y hl hy
      exact H (b :: a) y (by simp only [List.length_cons]; omega)
        ((eighNodeAt_cons_of_eighChild M n signFuel R₀ β _ c b a s hc).trans hy)
    simp only [eighAux]
    rw [hstep]
    cases hT : eighStep M n signFuel R₀ β A R ε ℓ (s' []) with
    | leaf U d => rfl
    | shift b A' σ =>
      have hc : eighChild M n signFuel R₀ β ⟨k, A, R, ε, ℓ⟩ (s []) b =
          some ⟨k, A', (eighNextParams M R ε ℓ).1, (eighNextParams M R ε ℓ).2, ℓ + 1⟩ := by
        simp [eighChild, hstep.trans hT]
      dsimp only
      rw [ih A' _ _ (ℓ + 1) (hchild b _ hc)]
    | split kp h Qp Qm Ap Am σ =>
      have hcT : eighChild M n signFuel R₀ β ⟨k, A, R, ε, ℓ⟩ (s []) true =
          some ⟨kp, Ap, (eighNextParams M R ε ℓ).1, (eighNextParams M R ε ℓ).2, ℓ + 1⟩ := by
        simp [eighChild, hstep.trans hT]
      have hcF : eighChild M n signFuel R₀ β ⟨k, A, R, ε, ℓ⟩ (s []) false =
          some ⟨k - kp, Am, (eighNextParams M R ε ℓ).1, (eighNextParams M R ε ℓ).2, ℓ + 1⟩ := by
        simp [eighChild, hstep.trans hT]
      dsimp only
      rw [ih Ap _ _ (ℓ + 1) (hchild true _ hcT), ih Am _ _ (ℓ + 1) (hchild false _ hcF)]

/-- `NLAlib.eigh` reads only the samples of the nodes it reaches: two trees of samples that
agree, at every path of length at most $\ell$ (the nodes with a positive budget) that
`NLAlib.eighNodeAt` follows, on the seed and on the leading $k \times k$ blocks of the test matrices
($k$ the node's size), give the same output. No printed source. -/
theorem eigh_congr_samples {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    (signFuel ℓ : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) (F × F)) (R₀ ε β : F)
    {s s' : List Bool → EighSample Su Sg n}
    (h : ∀ (a : List Bool) (y : EighNode F), a.length ≤ ℓ →
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y →
        (s a).1 = (s' a).1 ∧ ∀ b, leadingBlock y.k ((s a).2 b) = leadingBlock y.k ((s' a).2 b)) :
    eigh M signFuel ℓ A R₀ ε β s = eigh M signFuel ℓ A R₀ ε β s' := by
  exact eighAux_congr_samples M signFuel R₀ β (ℓ + 1) A R₀ ε ℓ
    (fun a y hl hy => h a y (Nat.lt_succ_iff.mp hl) hy)

/-- The ideal sample of a node below the depth budget has the seed and the leading blocks of the
slot's positions read on the ideal tape (private helper of
`NLAlib.eigh_eighTapeMachine_eq_eigh_eighIdealTree`). -/
private theorem eighIdealSample_eq_eighTapeSample (ξ : Dist → ℕ → ℝ) {N D d : ℕ} (hd : d < D)
    (lo k : ℕ) (pre : List Bool) :
    ξ .uniform (eighTapeSample N d lo).1 = (eighIdealSample ξ N D d lo (some k) pre).1 ∧
      ∀ b, leadingBlock k (((eighTapeSample N d lo).2 b).map (eighIdealComplex ξ)) =
        leadingBlock k ((eighIdealSample ξ N D d lo (some k) pre).2 b) := by
  refine ⟨by simp only [eighTapeSample, eighIdealSample, if_pos hd], fun b => ?_⟩
  refine Matrix.ext fun i j => ?_
  simp only [leadingBlock, eighTapeSample, eighIdealSample, if_pos hd, Matrix.of_apply,
    Matrix.map_apply, i.2, j.2, and_self, if_true]

/-- Along every path below the budget, the slot tree mapped to ideal samples and the tree of ideal
samples agree on the seed and the leading blocks of the node reached (private helper of
`NLAlib.eigh_eighTapeMachine_eq_eigh_eighIdealTree`). -/
private theorem eighSlotTree_map_agree_eighIdealTree {P K : Type} [Inhabited K]
    (sem : ScalarSem P K) (p : P) (toN : K → ℕ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → ℕ → K) (normal : ℕ → K × K) (unif' : K → ℝ → K) (normal' : ℂ → K × K)
    (ξ : Dist → ℕ → ℝ) (hu : ∀ c i, unif c i = unif' c (ξ .uniform i))
    (hn : ∀ z, normal z = normal' (eighIdealComplex ξ z)) (n signFuel D : ℕ) (R₀ β : K) :
    ∀ (a : List Bool) (d lo : ℕ) (x : EighNode K) (pre : List Bool) (y : EighNode K), x.k ≤ n →
      d + a.length < D →
      eighNodeAt (sem.toFloatMachine p toN mm qr unif' normal') n signFuel R₀ β a x
          (fun a => (ξ .uniform
            (eighSlotTree (sem.toFloatMachine p toN mm qr unif normal) n signFuel R₀ β d lo x a).1,
            fun b => ((eighSlotTree (sem.toFloatMachine p toN mm qr unif normal) n signFuel R₀ β d
              lo x a).2 b).map (eighIdealComplex ξ))) = some y →
        ξ .uniform
            (eighSlotTree (sem.toFloatMachine p toN mm qr unif normal) n signFuel R₀ β d lo x a).1 =
          (eighIdealTree (sem.toFloatMachine p toN mm qr unif' normal') n signFuel D R₀ β ξ d lo
            (some x) pre a).1 ∧
        ∀ b, leadingBlock y.k (((eighSlotTree (sem.toFloatMachine p toN mm qr unif normal) n
            signFuel R₀ β d lo x a).2 b).map (eighIdealComplex ξ)) =
          leadingBlock y.k ((eighIdealTree (sem.toFloatMachine p toN mm qr unif' normal') n
            signFuel D R₀ β ξ d lo (some x) pre a).2 b) := by
  intro a
  induction a with
  | nil =>
    intro d lo x pre y _ hd h
    obtain rfl : x = y := Option.some.inj h
    exact eighIdealSample_eq_eighTapeSample ξ (by simpa using hd) lo x.k pre
  | cons b a ih =>
    intro d lo x pre y hx hd h
    have hst := eighStep_toFloatMachine_map sem p toN mm qr unif normal unif' normal' (ξ .uniform)
      (eighIdealComplex ξ) hu hn n signFuel R₀ β hx x.A x.R x.ε x.ℓ (eighTapeSample n d lo)
    have h0 := eighIdealSample_eq_eighTapeSample ξ (d := d) (D := D) (N := n) (by simp at hd; omega)
      lo x.k pre
    have hJ := eighStep_congr_sample (sem.toFloatMachine p toN mm qr unif' normal') n signFuel
      R₀ β x.A x.R x.ε x.ℓ (t := (ξ .uniform (eighTapeSample n d lo).1,
        fun b => ((eighTapeSample n d lo).2 b).map (eighIdealComplex ξ)))
      (t' := eighIdealSample ξ n D d lo (some x.k) pre) h0.1 h0.2
    have hd' : d + 1 + a.length < D := by simp only [List.length_cons] at hd; omega
    simp only [eighNodeAt, eighChild, eighSlotTree.eq_1, eighSlotTree.eq_2] at h
    rw [eighSlotTree.eq_2, eighIdealTree.eq_3, ← hJ, ← hst]
    rw [← hst] at h
    generalize eighStep (sem.toFloatMachine p toN mm qr unif normal) n signFuel R₀ β x.A x.R x.ε x.ℓ
      (eighTapeSample n d lo) = st at h ⊢
    cases st with
    | leaf U e => simp only [Option.bind_none, reduceCtorEq] at h
    | shift b' A' σ =>
      by_cases hb : b = b'
      · simp only [hb, if_true, Option.bind_some] at h ⊢
        exact ih (d + 1) lo _ (pre ++ [b']) y hx hd' h
      · simp only [hb, if_false, Option.bind_none, reduceCtorEq] at h
    | split kp hkp Qp Qm Ap Am σ =>
      cases b
      · simp only [Bool.false_eq_true, if_false, Option.bind_some] at h ⊢
        exact ih (d + 1) (lo + kp) _ (pre ++ [false]) y ((Nat.sub_le _ _).trans hx) hd' h
      · simp only [if_true, Option.bind_some] at h ⊢
        exact ih (d + 1) lo _ (pre ++ [true]) y (hkp.trans hx) hd' h

/-- The run's output on positions is the output on ideal samples: for an interpretation whose
tape is a rounding $\rho \circ \xi$ of an ideal tape $\xi$, with $\rho$ independent of the position,
`NLAlib.eigh` on the tape machine (`NLAlib.eighTapeMachine`) with the tree of sample positions at
the slots (`NLAlib.eighSlotTree`) is `NLAlib.eigh` on the ideal machine (the machine of the
semantics with the samplers `NLAlib.Computation.ScalarSem.uniformUnif` and
`NLAlib.Computation.ScalarSem.gaussianNormal` of $\rho$) with the tree of ideal samples
(`NLAlib.eighIdealTree`, budget $\ell + 1$). No printed source. -/
theorem eigh_eighTapeMachine_eq_eigh_eighIdealTree {P ι K C : Type} [Inhabited K]
    (I : Interp P ι K C) (p : P) (mmR : MatMulMap (K × K)) (qrR : QRMap (K × K))
    (ρ : Dist → ℕ → ℝ → K) (hρ : ∀ (g : Dist) (i j : ℕ) (y : ℝ), ρ g i y = ρ g j y)
    (ξ : Dist → ℕ → ℝ) (signFuel ℓ : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) (K × K))
    (R₀ ε β : K) :
    eigh (eighTapeMachine ({ I with tape := fun d i => ρ d i (ξ d i) } : Interp P ι K C) p mmR qrR)
        signFuel ℓ A R₀ ε β
        (eighSlotTree
          (eighTapeMachine ({ I with tape := fun d i => ρ d i (ξ d i) } : Interp P ι K C) p mmR qrR)
          n signFuel R₀ β 0 0 ⟨n, A, R₀, ε, ℓ⟩) =
      eigh (I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
          (I.sem.uniformUnif p (ρ .uniform 0)) (I.sem.gaussianNormal p (ρ .gaussian 0)))
        signFuel ℓ A R₀ ε β
        (fun a => eighIdealTree (I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR
          qrR (I.sem.uniformUnif p (ρ .uniform 0)) (I.sem.gaussianNormal p (ρ .gaussian 0)))
          n signFuel (ℓ + 1) R₀ β ξ 0 0 (some ⟨n, A, R₀, ε, ℓ⟩) [] a) := by
  have hu : ∀ c i, I.sem.tapeUnif p (fun i => ρ .uniform i (ξ .uniform i)) c i =
      I.sem.uniformUnif p (ρ .uniform 0) c (ξ .uniform i) := fun c i => by
    simp only [ScalarSem.tapeUnif, ScalarSem.uniformUnif, hρ .uniform i 0]
  have hn : ∀ z, I.sem.tapeNormal p (fun i => ρ .gaussian i (ξ .gaussian i)) z =
      I.sem.gaussianNormal p (ρ .gaussian 0) (eighIdealComplex ξ z) := fun z => by
    have h2 : √2 ≠ 0 := by positivity
    simp only [ScalarSem.tapeNormal, ScalarSem.gaussianNormal, eighIdealComplex,
      mul_div_cancel₀ _ h2, hρ .gaussian _ 0]
  refine (eigh_toFloatMachine_map_samples I.sem p (fun x => (I.sem.toNat p x).getD 0) mmR qrR _ _
    _ _ (ξ .uniform) (eighIdealComplex ξ) hu hn signFuel ℓ A R₀ ε β _).trans ?_
  refine eigh_congr_samples _ signFuel ℓ A R₀ ε β fun a y ha h => ?_
  exact eighSlotTree_map_agree_eighIdealTree I.sem p _ mmR qrR _ _ _ _ ξ hu hn n signFuel (ℓ + 1)
    R₀ β a 0 0 _ [] y le_rfl (by omega) h

/-- The σ-algebra of the tape coordinates in `Q`. -/
noncomputable abbrev tapeSigma (Q : Set (Dist × ℕ)) : MeasurableSpace (Dist → ℕ → ℝ) :=
  ⨆ p ∈ Q, MeasurableSpace.comap (fun ξ : Dist → ℕ → ℝ => ξ p.1 p.2) inferInstance

private lemma measurable_tape_apply (p : Dist × ℕ) :
    Measurable fun ξ : Dist → ℕ → ℝ => ξ p.1 p.2 :=
  (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)

/-- The σ-algebra of tape coordinates is coarser than the product σ-algebra. -/
lemma tapeSigma_le (Q : Set (Dist × ℕ)) :
    tapeSigma Q ≤ (inferInstance : MeasurableSpace (Dist → ℕ → ℝ)) :=
  iSup₂_le fun p _ => (measurable_tape_apply p).comap_le

/-- The σ-algebra of tape coordinates is monotone in the set of coordinates. -/
lemma tapeSigma_mono {Q Q' : Set (Dist × ℕ)} (h : Q ⊆ Q') : tapeSigma Q ≤ tapeSigma Q' :=
  biSup_mono h

/-- A tape coordinate in `Q` is measurable for the σ-algebra of the coordinates in `Q`. -/
lemma measurable_tapeSigma_apply {Q : Set (Dist × ℕ)} {p : Dist × ℕ} (hp : p ∈ Q) :
    Measurable[tapeSigma Q] fun ξ : Dist → ℕ → ℝ => ξ p.1 p.2 :=
  Measurable.of_comap_le (le_iSup₂ (f := fun p (_ : p ∈ Q) => MeasurableSpace.comap
    (fun ξ : Dist → ℕ → ℝ => ξ p.1 p.2) inferInstance) p hp)

/-- Under the tape law, the σ-algebras of disjoint sets of tape coordinates are independent. -/
lemma indep_tapeSigma {Q Q' : Set (Dist × ℕ)} (h : Disjoint Q Q') :
    Indep (tapeSigma Q) (tapeSigma Q') tapeLaw := by
  have hind : iIndepFun (fun (p : Dist × ℕ) (ξ : Dist → ℕ → ℝ) => ξ p.1 p.2) tapeLaw := by
    have h := iIndepFun_uncurry_infinitePi' (Ω := fun (_ : Dist) (_ : ℕ) => ℝ)
      (fun d (_ : ℕ) => d.law) (X := fun (_ : Dist) (_ : ℕ) (x : ℝ) => x)
      (fun _ _ => measurable_id)
    exact h
  rw [iIndepFun_iff_iIndep] at hind
  exact indep_iSup_of_disjoint (fun p => (measurable_tape_apply p).comap_le) hind h

/-- The ideal sample read at the uniform position `u` and the complex Gaussian positions `z`. -/
noncomputable def eighReadSample (N u : ℕ) (z : Bool → Fin N → Fin N → ℕ)
    (ξ : Dist → ℕ → ℝ) : EighSample ℝ ℂ N :=
  (ξ .uniform u, fun b => Matrix.of fun i j => eighIdealComplex ξ (z b i j))

private lemma measurable_complexPair :
    Measurable fun v : Fin 2 → ℝ => (⟨v 0 / √2, v 1 / √2⟩ : ℂ) :=
  Complex.measurableEquivRealProd.symm.measurable.comp (f := fun v : Fin 2 → ℝ =>
    (v 0 / √2, v 1 / √2)) (((measurable_pi_apply 0).div_const _).prodMk
      ((measurable_pi_apply 1).div_const _))

/-- The complex number with measurable real and imaginary parts is measurable. -/
lemma measurable_complex_mk {α : Type*} {mα : MeasurableSpace α} {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => (⟨f x, g x⟩ : ℂ) :=
  Complex.measurableEquivRealProd.symm.measurable.comp (hf.prodMk hg)

/-- Pairs of independent standard Gaussians scaled by $1/\sqrt2$, arranged as a matrix, form a
standard complex Gaussian matrix. -/
private lemma map_pi_gaussianReal_eq_complexGaussianMatrix (n : ℕ) :
    Measure.map
      (fun y : (Fin n × Fin n) × Fin 2 → ℝ =>
        (Matrix.of fun i j => (⟨y ((i, j), 0) / √2, y ((i, j), 1) / √2⟩ : ℂ) :
          Matrix (Fin n) (Fin n) ℂ))
      (Measure.pi fun _ : (Fin n × Fin n) × Fin 2 => gaussianReal 0 1) =
        complexGaussianMatrix (Fin n) (Fin n) := by
  have hG := measurePreserving_curry_pi (m := Fin n × Fin n) (n := Fin 2)
    (ν := fun _ _ => gaussianReal 0 1)
  have hH := measurePreserving_curry_pi (m := Fin n) (n := Fin n) (α := Fin 2 → ℝ)
    (ν := fun _ _ => Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
  have hHG := hH.comp hG
  have hPmap : Measure.map
      (fun x : Fin n → Fin n → Fin 2 → ℝ =>
        (Matrix.of fun i j => (⟨x i j 0 / √2, x i j 1 / √2⟩ : ℂ) : Matrix (Fin n) (Fin n) ℂ))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n =>
        Measure.pi fun _ : Fin 2 => gaussianReal 0 1) = complexGaussianMatrix (Fin n) (Fin n) := by
    refine (Measure.pi_map_pi (f := fun _ (r : Fin n → Fin 2 → ℝ) j =>
        (⟨r j 0 / √2, r j 1 / √2⟩ : ℂ))
      (fun _ => (measurable_pi_lambda _ fun j =>
        measurable_complexPair.comp (measurable_pi_apply j)).aemeasurable)).trans ?_
    refine congrArg Measure.pi (funext fun i => ?_)
    refine (Measure.pi_map_pi (f := fun _ (v : Fin 2 → ℝ) => (⟨v 0 / √2, v 1 / √2⟩ : ℂ))
      (fun _ => measurable_complexPair.aemeasurable)).trans ?_
    exact congrArg Measure.pi (funext fun _ => map_pi_fin_two_eq_complexGaussian)
  have hPm : Measurable fun x : Fin n → Fin n → Fin 2 → ℝ =>
      (Matrix.of fun i j => (⟨x i j 0 / √2, x i j 1 / √2⟩ : ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      measurable_complexPair.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))
  rw [← hPmap, ← hHG.map_eq, Measure.map_map hPm hHG.measurable]
  rfl

/-- The law of a sample read at distinct positions: under the law of the tape, the ideal sample
read at one uniform position and at pairwise distinct complex Gaussian positions has the law
`NLAlib.eighSampleLaw`. -/
lemma hasLaw_eighReadSample (N u : ℕ) (z : Bool → Fin N → Fin N → ℕ)
    (hz : Function.Injective fun p : Bool × Fin N × Fin N => z p.1 p.2.1 p.2.2) :
    HasLaw (eighReadSample N u z) (eighSampleLaw N) tapeLaw := by
  have hid : HasLaw (fun ξ : Dist → ℕ → ℝ => ξ) tapeLaw tapeLaw := ⟨aemeasurable_id, Measure.map_id⟩
  -- the uniform seed
  have hU : HasLaw (fun ξ : Dist → ℕ → ℝ => ξ .uniform u) Dist.uniform.law tapeLaw :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => Dist.uniform.law) u).fun_comp_hasLaw
      (hasLaw_apply_of_hasLaw_tapeLaw hid .uniform)
  -- the Gaussian draws at the positions
  have hf : Function.Injective fun p : Bool × ((Fin N × Fin N) × Fin 2) =>
      2 * z p.1 p.2.1.1 p.2.1.2 + p.2.2.1 := by
    rintro ⟨b, ⟨i, j⟩, t⟩ ⟨b', ⟨i', j'⟩, t'⟩ h
    have ht : t.1 = t'.1 := by simp only at h; omega
    have hz' : z b i j = z b' i' j' := by simp only at h; omega
    have := hz (a₁ := (b, i, j)) (a₂ := (b', i', j')) hz'
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl, rfl⟩ := this
    rw [Fin.ext ht]
  have hY : HasLaw (fun (ξ : Dist → ℕ → ℝ) (p : Bool × ((Fin N × Fin N) × Fin 2)) =>
      ξ .gaussian (2 * z p.1 p.2.1.1 p.2.1.2 + p.2.2.1))
      (Measure.pi fun _ : Bool × ((Fin N × Fin N) × Fin 2) => gaussianReal 0 1) tapeLaw :=
    (hasLaw_apply_of_hasLaw_tapeLaw hid .gaussian).comp_of_injective hf
  have hC := measurePreserving_curry_pi (m := Bool) (n := (Fin N × Fin N) × Fin 2)
    (ν := fun _ _ => gaussianReal 0 1)
  have hMm : ∀ _ : Bool, Measurable fun y : (Fin N × Fin N) × Fin 2 → ℝ =>
      (Matrix.of fun i j => (⟨y ((i, j), 0) / √2, y ((i, j), 1) / √2⟩ : ℂ) :
        Matrix (Fin N) (Fin N) ℂ) := fun _ =>
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      measurable_complexPair.comp (measurable_pi_lambda
        (fun (c : (Fin N × Fin N) × Fin 2 → ℝ) (t : Fin 2) => c ((i, j), t))
        fun _ => measurable_pi_apply _)
  have hmap : Measure.map
      (fun y : Bool → (Fin N × Fin N) × Fin 2 → ℝ => fun b =>
        (Matrix.of fun i j => (⟨y b ((i, j), 0) / √2, y b ((i, j), 1) / √2⟩ : ℂ) :
          Matrix (Fin N) (Fin N) ℂ))
      (Measure.pi fun _ : Bool => Measure.pi fun _ : (Fin N × Fin N) × Fin 2 => gaussianReal 0 1)
      = Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N) := by
    refine (Measure.pi_map_pi (fun b => (hMm b).aemeasurable)).trans ?_
    exact congrArg Measure.pi (funext fun _ => map_pi_gaussianReal_eq_complexGaussianMatrix N)
  have hGm : Measurable fun y : Bool → (Fin N × Fin N) × Fin 2 → ℝ => fun b =>
      (Matrix.of fun i j => (⟨y b ((i, j), 0) / √2, y b ((i, j), 1) / √2⟩ : ℂ) :
        Matrix (Fin N) (Fin N) ℂ) :=
    measurable_pi_lambda _ fun b => (hMm b).comp (measurable_pi_apply b)
  have hG : HasLaw (fun ξ : Dist → ℕ → ℝ => fun b =>
      (Matrix.of fun i j => eighIdealComplex ξ (z b i j) : Matrix (Fin N) (Fin N) ℂ))
      (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)) tapeLaw := by
    have := (HasLaw.mk (hGm.comp hC.measurable).aemeasurable
      (by rw [← Measure.map_map hGm hC.measurable, hC.map_eq, hmap])).comp hY
    convert this using 1
    funext ξ b
    ext i j
    simp [eighIdealComplex, MeasurableEquiv.curry, Function.curry]
  -- the seed and the matrices are independent
  have hind : iIndepFun (fun (d : Dist) (ξ : Dist → ℕ → ℝ) => ξ d) tapeLaw :=
    iIndepFun_infinitePi (P := fun d : Dist => iidSequence d.law)
      (X := fun (_ : Dist) (x : ℕ → ℝ) => x) fun _ => measurable_id
  have hUG : IndepFun (fun ξ : Dist → ℕ → ℝ => ξ .uniform u) (fun ξ : Dist → ℕ → ℝ => fun b =>
      (Matrix.of fun i j => eighIdealComplex ξ (z b i j) : Matrix (Fin N) (Fin N) ℂ)) tapeLaw := by
    have h2 := hind.indepFun (i := .uniform) (j := .gaussian) (by simp)
    refine h2.comp (φ := fun x : ℕ → ℝ => x u) (ψ := fun (x : ℕ → ℝ) (b : Bool) =>
      (Matrix.of fun i j => (⟨x (2 * z b i j) / √2, x (2 * z b i j + 1) / √2⟩ : ℂ) :
        Matrix (Fin N) (Fin N) ℂ)) (measurable_pi_apply u) ?_
    exact measurable_pi_lambda _ fun b => measurable_pi_lambda _ fun i =>
      measurable_pi_lambda _ fun j => measurable_complex_mk
        ((measurable_pi_apply _).div_const _) ((measurable_pi_apply _).div_const _)
  exact hUG.hasLaw_prod hU hG

/-! ### The shape of a step -/

/-- The sizes of a step: a one-child node has size at least $2$, and a split is proper. -/
private lemma eighStep_shape {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    (N signFuel : ℕ) (R₀ β : F) {k : ℕ} (A : Matrix (Fin k) (Fin k) (F × F)) (R ε : F) (ℓ : ℕ)
    (s : EighSample Su Sg N) :
    match eighStep M N signFuel R₀ β A R ε ℓ s with
    | .leaf _ _ => True
    | .shift _ _ _ => 2 ≤ k
    | .split kp _ _ _ _ _ _ => 0 < kp ∧ kp < k := by
  unfold eighStep
  dsimp only
  split_ifs with h1 h2 h3 h4
  · trivial
  · trivial
  · omega
  · omega
  · exact ⟨Nat.pos_of_ne_zero h4, lt_of_le_of_ne (min_le_left _ _) h3⟩

/-- The two children of a node: none, one child of the same size (at least $2$), or a proper
split. -/
lemma eighChild_cases {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    (N signFuel : ℕ) (R₀ β : F) (x : EighNode F) (s : EighSample Su Sg N) :
    (eighChild M N signFuel R₀ β x s true = none ∧ eighChild M N signFuel R₀ β x s false = none) ∨
    (∃ y, eighChild M N signFuel R₀ β x s true = some y ∧
      eighChild M N signFuel R₀ β x s false = none ∧ y.k = x.k ∧ 2 ≤ x.k) ∨
    (∃ y, eighChild M N signFuel R₀ β x s true = none ∧
      eighChild M N signFuel R₀ β x s false = some y ∧ y.k = x.k ∧ 2 ≤ x.k) ∨
    (∃ y y', eighChild M N signFuel R₀ β x s true = some y ∧
      eighChild M N signFuel R₀ β x s false = some y' ∧ 1 ≤ y.k ∧ 1 ≤ y'.k ∧
        y.k + y'.k = x.k) := by
  have h := eighStep_shape M N signFuel R₀ β x.A x.R x.ε x.ℓ s
  unfold eighChild
  generalize eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ s = st at h ⊢
  cases st with
  | leaf U e => simp
  | shift b' A' σ => cases b' <;> simp [h]
  | split kp hkp Qp Qm Ap Am σ =>
    simp only [Bool.false_eq_true, if_false, if_true]
    right; right; right
    exact ⟨_, _, rfl, rfl, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩

end NLAlib
