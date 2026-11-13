/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.State
public import NLAlib.Eigensolvers.SpectralBisection.Child
public import NLAlib.Eigensolvers.SpectralBisection.NodeScalars
public import NLAlib.Eigensolvers.SpectralBisection.Partition
public import NLAlib.Ops.Logic.Loop

/-!
# Total bisection node outcomes

The executed branches store the existing mathematical step's matrices and metadata. The
outcome is represented by the single `StoresStep` predicate, including the signed shift
reconstructed during the upward traversal. Local operation contracts and actual storage
conditions establish total execution; no successful-run premise is used.

## Main results

* `NLAlib.SpectralBisection.writes_child_storesStep`: a child represents its whole shift outcome.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The actual single-child program stores every field of its mathematical shift outcome,
including the signed half-radius recovered from the retained radius on the upward pass. -/
theorem writes_child_storesStep {K Su Sg Op Tst : Type} [Inhabited K]
    [Has ScalarOp Op] [Has IndexOp Op] {M : Machine K} (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K)
    (normal : Sg → K × K) {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I)
    {τ : Tape K} {μ : Mem K} {n d lo k : ℕ} {ma ua qa ea sz kd ks sigma : ℕ × ℕ}
    (side : Bool) (R : K) (A : Matrix (Fin k) (Fin k) (K × K)) :
    let shift := if side then M.div R (M.lit 2) else M.neg (M.div R (M.lit 2))
    let step := EighStep.shift side
      ((M.toFloatMachine dec mm qr unif normal).hermShift A shift) shift
    let x := (ma.1, ma.2 + 2 * (n * n) * d + 2 * n * lo)
    let y := (ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo)
    let z := (sz.1, sz.2 + n * (d + 1) + lo)
    let w := (kd.1, kd.2 + n * d + lo)
    μ.Live [ma, sz, kd, sigma] →
    μ.store.readBlock x.1 x.2 (2 * (k * k)) = some ((EntryCodec.pair K).packFinMatrix A) →
    μ.store.get sigma.1 sigma.2 = some shift →
    μ.Room [y, z, w] [2 * (k * k), 1, 1] →
    Fp.Disj (Store.inBlock x.1 x.2 (2 * (k * k)))
      (Store.inBlock y.1 y.2 (2 * (k * k))) →
    Fp.Disj (Store.inBlock sigma.1 sigma.2 1) (Store.inBlock y.1 y.2 (2 * (k * k))) →
    Fp.Apart [y, z, w] [2 * (k * k), 1, 1] →
    Writes .total I τ (child (Op := Op) (Tst := Tst))
      (Env.frame [n, d, lo, k, if side then 2 else 3] [ma, sz, kd, sigma])
      (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd ks step) (stepOutputLengths step))
      (fun μ' => μ'.pos = μ.pos ∧ StoresStep M R n d lo ma ua qa ea sz kd ks step μ') μ := by
  dsimp only
  intro hl hA hshift hroom hxy hsy hap
  obtain ⟨hy, hz, hw, -⟩ := hroom
  refine (writes_child dec mm qr unif normal hS hL A _ hl hA hshift hy
    (by omega) (by omega) hxy hsy hap).mono le_rfl ?_
  intro μ' _ ⟨hpos, hreads⟩
  refine ⟨hpos, rfl, ?_⟩
  cases side <;> simpa only [stepOutputs, stepOutputLengths, stepOutputWords,
    Bool.false_eq_true, if_false, if_true, Nat.cast_ofNat] using hreads

/-- An interior split stores the complete existing mathematical branch outcome, with its two
bases, compressions, child sizes and parent metadata in one tuple. -/
theorem writes_split_storesStep {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has IndexOp Op] [Has MatrixOp Op] {M : Machine K} (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) {I : Interp Op Tst K}
    (hS : IsScalar M I) (hL : IsIndexLit M I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    {τ : Tape K} {μ : Mem K} {n d lo k kp : ℕ}
    {sg pp pm ma ua qa ea sz kd ks c t : ℕ × ℕ}
    (S : ℕ → ℕ → K × K) (Pp Pm A : Matrix (Fin k) (Fin k) (K × K)) (R : K)
    (hInterior : 0 < kp ∧ kp < k) (hslot : lo + k ≤ n)
    (hl : μ.Live [sg, pp, pm, ma, qa, sz, kd, ks, c, t])
    (hread : μ.readBlocks (splitInputs n d lo sg pp pm ma c t) (splitInputLengths n k) =
      some [(EntryCodec.pair K).packMatrix n (2 * n) S, (EntryCodec.pair K).packFinMatrix Pp,
        (EntryCodec.pair K).packFinMatrix Pm, (EntryCodec.pair K).packFinMatrix A,
        [M.lit 2], [M.sqrtHalf], [M.div R (M.lit 2)], [M.neg (M.div R (M.lit 2))]])
    (hroom : μ.Room (splitOutputs n d lo k kp ma qa sz kd ks) (splitOutputLengths k kp))
    (hap : Fp.Apart (splitOutputs n d lo k kp ma qa sz kd ks) (splitOutputLengths k kp))
    (hprotect : Fp.Disj (Fp.blocks (splitOutputs n d lo k kp ma qa sz kd ks)
      (splitOutputLengths k kp))
      (Fp.blocks (splitInputs n d lo sg pp pm ma c t) (splitInputLengths n k))) :
    let step := branchOutcome M dec mm qr lo R S A Pp Pm kp hInterior.2.le
    Writes .total I τ (split (Op := Op) (Tst := Tst))
      (Env.frame [n, d, lo, k, kp] [sg, pp, pm, ma, qa, sz, kd, ks, c, t])
      (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd ks step) (stepOutputLengths step))
      (fun μ' => μ'.pos = μ.pos ∧ StoresStep M R n d lo ma ua qa ea sz kd ks step μ') μ := by
  dsimp only
  simp only [branchOutcome, if_neg (Nat.ne_of_lt hInterior.2), if_neg (Nat.ne_of_gt hInterior.1)]
  refine (writes_split dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
    hS hL hMM hQR S Pp Pm A (M.lit 2) M.sqrtHalf (M.div R (M.lit 2))
    (M.neg (M.div R (M.lit 2))) hInterior hslot hl hread hroom hap hprotect).mono le_rfl ?_
  intro μ' _ ⟨hpos, hreads⟩
  exact ⟨hpos, rfl, hreads⟩

/-- Both child variants inherit their input separation from the common protected tuple. -/
private theorem child_inputs_disjoint {n d lo k : ℕ}
    {sg pp pm ma sz kd c t : ℕ × ℕ} (side : Bool)
    (h : Fp.Disj
      (Fp.blocks [(ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
        (sz.1, sz.2 + n * (d + 1) + lo), (kd.1, kd.2 + n * d + lo)]
        [2 * (k * k), 1, 1])
      (Fp.blocks (splitInputs n d lo sg pp pm ma c t) (splitInputLengths n k))) :
    Fp.Disj (Store.inBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo) (2 * (k * k)))
        (Store.inBlock ma.1 (ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo) (2 * (k * k))) ∧
      Fp.Disj (Store.inBlock t.1 (if side then t.2 else t.2 + 1) 1)
        (Store.inBlock ma.1 (ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo) (2 * (k * k))) := by
  have hd := h.inBlock_getD_left (i := 0) (by simp)
  have hA := hd.symm.inBlock_getD_left (i := 3) (by simp [splitInputs, splitInputLengths])
  have hs := hd.symm.inBlock_getD_left (i := if side then 6 else 7)
    (by cases side <;> simp [splitInputs, splitInputLengths])
  refine ⟨by simpa [splitInputs, splitInputLengths] using hA, ?_⟩
  cases side <;> simpa [splitInputs, splitInputLengths] using hs

/-- The parent matrix and two shift cells are projected from the common branch inputs. -/
private theorem splitInputs_matrix_shifts {K : Type} {m : Mem K} {n d lo k : ℕ}
    {sg pp pm ma c t : ℕ × ℕ} {xs : List (List K)}
    (h : m.readBlocks (splitInputs n d lo sg pp pm ma c t) (splitInputLengths n k) = some xs)
    {A : Matrix (Fin k) (Fin k) (K × K)} {p q : K}
    (hA : xs.getD 3 [] = (EntryCodec.pair K).packFinMatrix A)
    (hp : xs.getD 6 [] = [p]) (hq : xs.getD 7 [] = [q]) :
    m.store.readBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) =
        some ((EntryCodec.pair K).packFinMatrix A) ∧
      m.store.get t.1 t.2 = some p ∧ m.store.get t.1 (t.2 + 1) = some q := by
  have ha := Mem.readBlocks_getD h (i := 3) (by simp [splitInputs, splitInputLengths])
  rw [hA] at ha
  have hp' := Mem.get_of_readBlocks_getD h (i := 6)
    (by simp [splitInputs, splitInputLengths]) rfl hp
  have hq' := Mem.get_of_readBlocks_getD h (i := 7)
    (by simp [splitInputs, splitInputLengths]) rfl hq
  exact ⟨by simpa [splitInputs, splitInputLengths] using ha, by simpa [splitInputs] using hp',
    by simpa [splitInputs] using hq'⟩

/-- The three explicit dispatch loops execute exactly the selected child or split and store
its entire mathematical outcome. Every premise is a primitive contract or a condition on
actual readable inputs, writable outputs and their spatial separation. -/
theorem writes_nodeBranch {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has IndexOp Op] [Has MatrixOp Op] {M : Machine K} (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) {I : Interp Op Tst K}
    (hS : IsScalar M I) (hL : IsIndexLit M I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    {τ : Tape K} {μ : Mem K} {n d lo k kp : ℕ}
    {sg pp pm ma ua qa ea sz kd ks c t : ℕ × ℕ}
    (S : ℕ → ℕ → K × K) (Pp Pm A : Matrix (Fin k) (Fin k) (K × K)) (R : K)
    (hk : 0 < k) (hkp : kp ≤ k) (hslot : lo + k ≤ n)
    (hl : μ.Live [sg, pp, pm, ma, qa, sz, kd, ks, c, t])
    (hread : μ.readBlocks (splitInputs n d lo sg pp pm ma c t) (splitInputLengths n k) =
      some [(EntryCodec.pair K).packMatrix n (2 * n) S, (EntryCodec.pair K).packFinMatrix Pp,
        (EntryCodec.pair K).packFinMatrix Pm, (EntryCodec.pair K).packFinMatrix A,
        [M.lit 2], [M.sqrtHalf], [M.div R (M.lit 2)], [M.neg (M.div R (M.lit 2))]]) :
    let step := branchOutcome M dec mm qr lo R S A Pp Pm kp hkp
    μ.Room (stepOutputs n d lo ma ua qa ea sz kd ks step) (stepOutputLengths step) →
    Fp.Apart (stepOutputs n d lo ma ua qa ea sz kd ks step) (stepOutputLengths step) →
    Fp.Disj (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd ks step) (stepOutputLengths step))
      (Fp.blocks (splitInputs n d lo sg pp pm ma c t) (splitInputLengths n k)) →
    Writes .total I τ (nodeBranch (Op := Op) (Tst := Tst))
      (Env.frame [n, d, lo, k, kp] [sg, pp, pm, ma, qa, sz, kd, ks, c, t])
      (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd ks step) (stepOutputLengths step))
      (fun μ' => μ'.pos = μ.pos ∧ StoresStep M R n d lo ma ua qa ea sz kd ks step μ') μ := by
  dsimp only
  intro hroom hap hprotect
  let F := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
  let half := M.div R (M.lit 2)
  let Post (step : EighStep K k) (μ' : Mem K) :=
    μ'.pos = μ.pos ∧ StoresStep M R n d lo ma ua qa ea sz kd ks step μ'
  obtain ⟨hA, hhalf, hnegative⟩ := splitInputs_matrix_shifts hread rfl rfl rfl
  have hlchild : μ.Live [ma, sz, kd, t] := fun z hz => hl z (by simp at hz ⊢; tauto)
  by_cases hp : kp = k
  · subst kp
    simp only [branchOutcome, if_true] at hroom hap hprotect ⊢
    simp only [stepOutputs, stepOutputLengths] at hroom hap hprotect
    obtain ⟨hxy, hsy⟩ := child_inputs_disjoint true hprotect
    refine (writes_ifZero (P := Post (.shift true (F.hermShift A half) half)) rfl ?_).seq_le
      le_rfl ?_
    · simp only [Nat.sub_self]
      exact writes_frame rfl rfl (by room) (writes_child_storesStep dec mm qr M.mul
        (fun z : K × K => M.normalWords z.1 z.2) hS hL true R A
          hlchild hA hhalf hroom hxy hsy hap)
    intro μ₁ hfr₁ hstate
    refine (writes_ifZero (P := Post (.shift true (F.hermShift A half) half)) rfl ?_).seq_le
      le_rfl ?_
    · simpa only [if_neg (Nat.ne_of_gt hk)] using hstate
    intro μ₂ hfr₂ hstate
    apply writes_ifPos rfl
    simpa only [Nat.sub_self, Nat.mul_zero, Nat.lt_irrefl, if_false] using hstate
  · by_cases hm : kp = 0
    · subst kp
      simp only [branchOutcome, if_neg (Ne.symm (Nat.ne_of_gt hk)), if_true] at hroom hap hprotect ⊢
      simp only [stepOutputs, stepOutputLengths] at hroom hap hprotect
      obtain ⟨hxy, hsy⟩ := child_inputs_disjoint false hprotect
      refine (writes_ifZero (P := fun μ' => μ' = μ) rfl ?_).seq_le le_rfl ?_
      · simp only [Nat.sub_zero, if_neg (Nat.ne_of_gt hk)]
      intro μ₁ _ hsame
      subst μ₁
      refine (writes_ifZero (P := Post (.shift false
        (F.hermShift A (M.neg half)) (M.neg half))) rfl ?_).seq_le le_rfl ?_
      · exact writes_frame rfl rfl
          (by simpa only [Mem.live_cons, Mem.live_nil, and_true] using hlchild)
          (writes_child_storesStep dec mm qr M.mul
            (fun z : K × K => M.normalWords z.1 z.2) hS hL false R A
            (by simpa only [Mem.live_cons, Mem.live_nil, and_true] using hlchild)
            hA hnegative hroom hxy hsy hap)
      intro μ₂ _ hstate
      apply writes_ifPos rfl
      simpa only [Nat.zero_mul, Nat.lt_irrefl, if_false] using hstate
    · have hi : 0 < kp ∧ kp < k := by omega
      refine (writes_ifZero (P := fun μ' => μ' = μ) rfl ?_).seq_le le_rfl ?_
      · simp only [if_neg (show k - kp ≠ 0 by omega)]
      intro μ₁ _ hsame
      subst μ₁
      refine (writes_ifZero (P := fun μ' => μ' = μ) rfl ?_).seq_le le_rfl ?_
      · simp only [if_neg hm]
      intro μ₂ _ hsame
      subst μ₂
      apply writes_ifPos rfl
      rw [if_pos (Nat.mul_pos hi.1 (by omega))]
      exact writes_frame rfl rfl (by room) (writes_split_storesStep dec mm qr hS hL hMM hQR
        S Pp Pm A R hi hslot hl hread (by simpa only [branchOutcome, hp, hm, if_false, stepOutputs,
          stepOutputLengths] using hroom)
        (by simpa only [branchOutcome, hp, hm, if_false, stepOutputs,
          stepOutputLengths] using hap)
        (by simpa only [branchOutcome, hp, hm, if_false, stepOutputs,
          stepOutputLengths] using hprotect))

end NLAlib.SpectralBisection
