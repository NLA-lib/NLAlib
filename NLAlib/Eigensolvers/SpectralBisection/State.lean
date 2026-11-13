/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Split
public import NLAlib.Matrix.FinitePrecision.SpectralBisection
public import NLAlib.Matrix.FinitePrecision.OpsSampling

/-!
# Stored outcomes of a mathematical bisection step

One storage predicate represents every constructor of the existing mathematical `EighStep`.
It records the actual packed outputs and metadata, and relates the constructor's shift to
the radius word retained for the upward traversal. It introduces no execution-phase records.
Stored sample words also supply a mathematical sample directly, before any probability law
or rounding-error argument is imposed.

## Main definitions

* `NLAlib.SpectralBisection.StoresStep`: stored leaf, single-child or split outcome.
* `NLAlib.SpectralBisection.storedNodeSample`: the two selected raw-word sample matrices.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Output locations of a mathematical node outcome, in the order of its packed contract. -/
def stepOutputs {K : Type} (n d lo : ℕ) (ma ua qa ea sz kd ks : ℕ × ℕ) {k : ℕ} :
    EighStep K k → List (ℕ × ℕ)
  | .leaf .. => [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
      (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)]
  | .shift .. => [(ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
      (sz.1, sz.2 + n * (d + 1) + lo), (kd.1, kd.2 + n * d + lo)]
  | .split kp .. => splitOutputs n d lo k kp ma qa sz kd ks

/-- Occupied word lengths of a mathematical node outcome. -/
def stepOutputLengths {K : Type} {k : ℕ} : EighStep K k → List ℕ
  | .leaf .. => [2 * (k * k), k, 1]
  | .shift .. => [2 * (k * k), 1, 1]
  | .split kp .. => splitOutputLengths k kp

/-- Actual packed words represented by the constructor's mathematical matrices and metadata. -/
def stepOutputWords {K : Type} (M : Machine K) {k : ℕ} : EighStep K k → List (List K)
  | .leaf U values => [(EntryCodec.pair K).packFinMatrix U, List.ofFn values, [M.lit 1]]
  | .shift side A _ => [(EntryCodec.pair K).packFinMatrix A, [M.lit (k : ℚ)],
      [M.lit (if side then 2 else 3)]]
  | .split kp _ Qp Qm Ap Am _ =>
      [(EntryCodec.pair K).packFinMatrix Qp, (EntryCodec.pair K).packFinMatrix Qm,
        (EntryCodec.pair K).packFinMatrix Ap, (EntryCodec.pair K).packFinMatrix Am,
        [M.lit (kp : ℚ)], [M.lit ((k - kp : ℕ) : ℚ)], [M.lit 4], [M.lit (kp : ℚ)]]

/-- A complete stored node outcome. The constructor's shift is retained mathematically as
the signed half-radius reconstructed by the upward traversal; its scratch cell is not kept.
All matrix, vector and metadata fields are constrained by one actual block-read tuple. -/
def StoresStep {K : Type} (M : Machine K) (R : K) (n d lo : ℕ)
    (ma ua qa ea sz kd ks : ℕ × ℕ) {k : ℕ} (step : EighStep K k) (m : Mem K) : Prop :=
  (match step with
    | .leaf .. => True
    | .shift side _ sigma =>
        sigma = if side then M.div R (M.lit 2) else M.neg (M.div R (M.lit 2))
    | .split _ _ _ _ _ _ sigma => sigma = M.div R (M.lit 2)) ∧
    m.readBlocks (stepOutputs n d lo ma ua qa ea sz kd ks step) (stepOutputLengths step) =
      some (stepOutputWords M step)

/-- Disjoint writes preserve the complete represented node outcome. -/
theorem StoresStep.of_eqOff {K : Type} {M : Machine K} {R : K} {n d lo k : ℕ}
    {ma ua qa ea sz kd ks : ℕ × ℕ} {step : EighStep K k} {m m' : Mem K} {F : Fp}
    (hfr : m.store.EqOff F m'.store)
    (hdis : Fp.Disj F (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd ks step)
      (stepOutputLengths step)))
    (h : StoresStep M R n d lo ma ua qa ea sz kd ks step m) :
    StoresStep M R n d lo ma ua qa ea sz kd ks step m' :=
  ⟨h.1, Mem.readBlocks_of_eqOff hfr hdis h.2⟩

/-- Agreement below the caller's handles preserves a represented node outcome, including
across the removal of a whole scratch-allocation chain. -/
theorem StoresStep.of_below {K : Type} {M : Machine K} {R : K} {n d lo k L : ℕ}
    {ma ua qa ea sz kd ks : ℕ × ℕ} {step : EighStep K k} {m m' : Mem K}
    (hfr : Store.Below L m.store m'.store)
    (hz : ∀ z ∈ stepOutputs n d lo ma ua qa ea sz kd ks step, z.1 < L)
    (h : StoresStep M R n d lo ma ua qa ea sz kd ks step m) :
    StoresStep M R n d lo ma ua qa ea sz kd ks step m' :=
  ⟨h.1, (Mem.readBlocks_eq_of_below hfr hz).trans h.2⟩

/-- The raw stored uniform word and the two alternating-column Gaussian matrices selected
by this node. Unused columns may be arbitrary: the mathematical step reads only its leading
size-k blocks, whose slot bounds place them inside the actual stored sample rectangle. -/
def storedNodeSample {K : Type} (n lo : ℕ) (u : K) (S : ℕ → ℕ → K × K) :
    EighSample K (K × K) n :=
  (u, fun side => Matrix.of fun i j => S i (2 * (lo + j) + if side then 0 else 1))

/-- The stored node's uniform seed is its supplied raw word. -/
@[simp] theorem storedNodeSample_uniform {K : Type} (n lo : ℕ) (u : K)
    (S : ℕ → ℕ → K × K) : (storedNodeSample n lo u S).1 = u := rfl

/-- Selecting the leading block and applying the actual two component multiplications agrees
with the program's sampled Gaussian matrix. No sample distribution or numerical accuracy is
used by this equality on stored words. -/
theorem sampledGaussian_eq_normalWords {K : Type} [Inhabited K] (M : Machine K)
    {n k lo : ℕ} (hslot : lo + k ≤ n) (u : K) (S : ℕ → ℕ → K × K) (side : Bool) :
    sampledGaussian M k lo (if side then 0 else 1) S M.sqrtHalf =
      (leadingBlock k ((storedNodeSample n lo u S).2 side)).map
        (fun z => M.normalWords z.1 z.2) := by
  apply Matrix.ext
  intro i j
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  simp [sampledGaussian, leadingBlock, storedNodeSample, hi, hj, Machine.normalWords]

/-- The existing mathematical deflation routine on raw stored samples is exactly the QR
basis computed from the program's sampled Gaussian matrix. The size bound supplies every
requested column; no QR accuracy or rank assumption is needed for this functional equality. -/
theorem deflate_storedNodeSample {K : Type} [Inhabited K] (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) {n k lo r : ℕ}
    (hslot : lo + k ≤ n) (hr : r ≤ k) (u : K) (S : ℕ → ℕ → K × K) (side : Bool)
    (P : Matrix (Fin k) (Fin k) (K × K)) :
    NLAlib.deflate (M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2))
      r P (leadingBlock k ((storedNodeSample n lo u S).2 side)) =
        (qr (mm P (sampledGaussian M k lo (if side then 0 else 1) S M.sqrtHalf))).1.submatrix
          id (Fin.castLE hr) := by
  have hsample := sampledGaussian_eq_normalWords M hslot u S side
  apply Matrix.ext
  intro i j
  have hj : (j : ℕ) < k := lt_of_lt_of_le j.isLt hr
  simp only [NLAlib.deflate, Machine.toFloatMachine, Matrix.of_apply, dif_pos hj,
    Matrix.submatrix_apply]
  rw [← hsample]
  rfl

/-- Branch output locations determined solely by the bounded split size. No matrix values or
arithmetic model enter these spatial requirements. -/
def branchOutputs (n d lo k kp : ℕ) (ma qa sz kd ks : ℕ × ℕ) : List (ℕ × ℕ) :=
  if kp = k ∨ kp = 0 then
    [(ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
      (sz.1, sz.2 + n * (d + 1) + lo), (kd.1, kd.2 + n * d + lo)]
  else splitOutputs n d lo k kp ma qa sz kd ks

/-- Branch output lengths determined solely by the bounded split size. -/
def branchLengths (k kp : ℕ) : List ℕ :=
  if kp = k ∨ kp = 0 then [2 * (k * k), 1, 1] else splitOutputLengths k kp

/-- The mathematical outcome selected by the computed bounded split size. This is the
nonleaf tail of `eighStep`, on the actual stored Gaussian words and machine functions. -/
noncomputable def branchOutcome {K : Type} (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (lo : ℕ) {k : ℕ}
    (R : K) (S : ℕ → ℕ → K × K) (A Pp Pm : Matrix (Fin k) (Fin k) (K × K))
    (kp : ℕ) (hkp : kp ≤ k) : EighStep K k :=
  let F := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
  let half := M.div R (M.lit 2)
  if kp = k then .shift true (F.hermShift A half) half
  else if kp = 0 then .shift false (F.hermShift A (M.neg half)) (M.neg half)
  else
    let Qp := (qr (mm Pp (sampledGaussian M k lo 0 S M.sqrtHalf))).1.submatrix
      id (Fin.castLE hkp)
    let Qm := (qr (mm Pm (sampledGaussian M k lo 1 S M.sqrtHalf))).1.submatrix
      id (Fin.castLE (Nat.sub_le k kp))
    .split kp hkp Qp Qm
      (F.hermShift (F.hermAvg (mm (mm (F.conjTransposeMat Qp) A) Qp) (M.lit 2)) half)
      (F.hermShift (F.hermAvg (mm (mm (F.conjTransposeMat Qm) A) Qm) (M.lit 2)) (M.neg half))
      half

/-- The stored outcome's locations coincide with its purely spatial branch layout. -/
theorem stepOutputs_branchOutcome {K : Type} (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (n d lo : ℕ) {k kp : ℕ}
    (hkp : kp ≤ k) (R : K) (S : ℕ → ℕ → K × K)
    (A Pp Pm : Matrix (Fin k) (Fin k) (K × K)) (ma ua qa ea sz kd ks : ℕ × ℕ) :
    stepOutputs n d lo ma ua qa ea sz kd ks
      (branchOutcome M dec mm qr lo R S A Pp Pm kp hkp) =
        branchOutputs n d lo k kp ma qa sz kd ks := by
  by_cases hp : kp = k
  · simp [branchOutcome, branchOutputs, stepOutputs, hp]
  · by_cases hm : kp = 0
    · have hz : 0 ≠ k := by simpa only [hm] using hp
      simp [branchOutcome, branchOutputs, stepOutputs, hm, hz]
    · simp [branchOutcome, branchOutputs, stepOutputs, hp, hm]

/-- The stored outcome's lengths coincide with its purely spatial branch layout. -/
theorem stepOutputLengths_branchOutcome {K : Type} (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (lo : ℕ) {k kp : ℕ}
    (hkp : kp ≤ k) (R : K) (S : ℕ → ℕ → K × K)
    (A Pp Pm : Matrix (Fin k) (Fin k) (K × K)) :
    stepOutputLengths (branchOutcome M dec mm qr lo R S A Pp Pm kp hkp) = branchLengths k kp := by
  by_cases hp : kp = k
  · simp [branchOutcome, branchLengths, stepOutputLengths, hp]
  · by_cases hm : kp = 0
    · have hz : 0 ≠ k := by simpa only [hm] using hp
      simp [branchOutcome, branchLengths, stepOutputLengths, hm, hz]
    · simp [branchOutcome, branchLengths, stepOutputLengths, hp, hm]

/-- A branch outcome's signed shift already is its retained half-radius; its storage obligation
is exactly the tuple of represented output words. -/
theorem storesStep_branchOutcome_iff {K : Type} (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (n d lo : ℕ) {k kp : ℕ}
    (hkp : kp ≤ k) (R : K) (S : ℕ → ℕ → K × K)
    (A Pp Pm : Matrix (Fin k) (Fin k) (K × K)) (ma ua qa ea sz kd ks : ℕ × ℕ) (m : Mem K) :
    let step := branchOutcome M dec mm qr lo R S A Pp Pm kp hkp
    StoresStep M R n d lo ma ua qa ea sz kd ks step m ↔
      m.readBlocks (stepOutputs n d lo ma ua qa ea sz kd ks step) (stepOutputLengths step) =
        some (stepOutputWords M step) := by
  dsimp only
  by_cases hp : kp = k
  · simp [branchOutcome, StoresStep, hp]
  · by_cases hm : kp = 0
    · have hz : 0 ≠ k := by simpa only [hm] using hp
      simp [branchOutcome, StoresStep, hm, hz]
    · simp [branchOutcome, StoresStep, hp, hm]

/-- The computed-index branch outcome is exactly the existing nonleaf mathematical step.
The size and failed stopping test are explicit, and all Gaussian normalization uses the
same machine word as the executed program. -/
theorem eighStep_eq_branchOutcome {K : Type} [Inhabited K] (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) {n k lo fuel ell : ℕ}
    (hslot : lo + k ≤ n) (hk : 2 ≤ k) (R R0 beta eps U : K) (S : ℕ → ℕ → K × K)
    (A : Matrix (Fin k) (Fin k) (K × K)) (hactive : ¬ dec R ≤ dec (M.mul eps R0)) :
    let F := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
    let B := newtonSchulzSign F beta (M.mul (M.lit 2) R) fuel
      (F.hermShift A (M.mul (M.div R (M.lit (ell : ℚ))) U))
    let Pp := F.hermScale (F.hermShift B (M.neg (M.lit 1))) (M.lit 2)
    let Pm := F.hermScale (F.negMat (F.hermShift B (M.lit 1))) (M.lit 2)
    let kp := min k (F.toNat (M.add (F.traceRe Pp) (M.div (M.lit 1) (M.lit 2))))
    eighStep F n fuel R0 beta A R eps ell (storedNodeSample n lo U S) =
      branchOutcome M dec mm qr lo R S A Pp Pm kp (min_le_left _ _) := by
  let F := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
  let B := newtonSchulzSign F beta (M.mul (M.lit 2) R) fuel
    (F.hermShift A (M.mul (M.div R (M.lit (ell : ℚ))) U))
  let Pp := F.hermScale (F.hermShift B (M.neg (M.lit 1))) (M.lit 2)
  let Pm := F.hermScale (F.negMat (F.hermShift B (M.lit 1))) (M.lit 2)
  let kp := min k (F.toNat (M.add (F.traceRe Pp) (M.div (M.lit 1) (M.lit 2))))
  change eighStep F n fuel R0 beta A R eps ell (storedNodeSample n lo U S) =
    branchOutcome M dec mm qr lo R S A Pp Pm kp (min_le_left _ _)
  have hstop : F.le R (F.mul eps R0) = false := by
    simp [F, Machine.toFloatMachine, hactive]
  have hQp := deflate_storedNodeSample M dec mm qr (r := kp) hslot
    (min_le_left _ _) U S true Pp
  have hQm := deflate_storedNodeSample M dec mm qr (r := k - kp) hslot
    (Nat.sub_le k kp) U S false Pm
  simp only [eighStep, show ¬ k ≤ 1 by omega, if_false, hstop, Bool.false_eq_true]
  unfold branchOutcome
  change (if kp = k then _ else if kp = 0 then _ else _) =
    (if kp = k then _ else if kp = 0 then _ else _)
  by_cases hp : kp = k
  · simp only [hp, if_true]
    simp [F, Machine.toFloatMachine]
  · simp only [hp, if_false]
    by_cases hm : kp = 0
    · simp only [hm, if_true]
      simp [F, Machine.toFloatMachine]
    · simp only [hm, if_false]
      simp only [F, Pp, Pm, B, kp, Machine.toFloatMachine, Nat.cast_ofNat,
        storedNodeSample_uniform] at hQp hQm ⊢
      rw [hQp, hQm]
      rfl

end NLAlib.SpectralBisection
