/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Arena
public import NLAlib.Eigensolvers.SpectralBisection.StepRead
public import NLAlib.Ops.Logic.BlockPartition

/-!
# Slot reservations for downward bisection outputs

Each matrix slot reserves `2*n` words and each scalar slot one word. One collection of apart
output-level regions covers every leaf, child and split. Mathematical slot intervals then
separate all outputs without pairwise instruction-level frame arguments.

## Main results

* `NLAlib.SpectralBisection.downRegion_le_level`: a slot reservation fits its output levels.
* `NLAlib.SpectralBisection.disj_downRegion`: disjoint slots have disjoint output reservations.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The next matrix/size levels and current result/basis/metadata levels, in matching order. -/
def downArenaOrigins (n d : ℕ) (ma ua qa ea sz kd kp : ℕ × ℕ) : Fin 7 → ℕ × ℕ :=
  ![(ma.1, ma.2 + 2 * (n * n) * (d + 1)), (ua.1, ua.2 + 2 * (n * n) * d),
    (qa.1, qa.2 + 2 * (n * n) * d), (ea.1, ea.2 + n * d),
    (sz.1, sz.2 + n * (d + 1)), (kd.1, kd.2 + n * d), (kp.1, kp.2 + n * d)]

/-- A matrix slot reserves an ambient column of complex words; scalar slots reserve one word. -/
def downArenaStride (n : ℕ) : Fin 7 → ℕ := ![2 * n, 2 * n, 2 * n, 1, 1, 1, 1]

/-- All potential outputs of one size-k node lie in these seven slot reservations. -/
def downRegion (n d lo k : ℕ) (ma ua qa ea sz kd kp : ℕ × ℕ) : Fp :=
  Fp.blocks (List.ofFn fun i => ((downArenaOrigins n d ma ua qa ea sz kd kp i).1,
    (downArenaOrigins n d ma ua qa ea sz kd kp i).2 + downArenaStride n i * lo))
    (List.ofFn fun i => downArenaStride n i * k)

/-- The complete seven output-level regions. -/
def downLevelRegion (n d : ℕ) (ma ua qa ea sz kd kp : ℕ × ℕ) : Fp :=
  Fp.blocks (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
    (List.ofFn fun i => downArenaStride n i * n)

/-- Every slot interval inside the root range occupies only its declared output levels. -/
theorem downRegion_le_level {n d lo k : ℕ} (hslot : lo + k ≤ n)
    (ma ua qa ea sz kd kp : ℕ × ℕ) :
    downRegion n d lo k ma ua qa ea sz kd kp ≤ downLevelRegion n d ma ua qa ea sz kd kp := by
  apply Fp.blocks_ofFn_le
  intro i
  refine (Fp.inBlock_le_inBlock (by omega) ?_).trans
    (Fp.inBlock_ofFn_le_blocks (downArenaOrigins n d ma ua qa ea sz kd kp)
      (fun i => downArenaStride n i * n) i)
  have h := Nat.mul_le_mul_left (downArenaStride n i) hslot
  rw [Nat.mul_add] at h
  omega

/-- Empty slots have no output reservation. -/
theorem downRegion_zero (n d lo : ℕ) (ma ua qa ea sz kd kp : ℕ × ℕ) :
    downRegion n d lo 0 ma ua qa ea sz kd kp = ⊥ := by
  funext b x
  apply propext
  simp [downRegion, List.ofFn_succ, Fp.blocks, Store.inBlock]

/-- Ordered nonempty slot intervals separate corresponding views of every output arena. -/
theorem disj_downRegion_of_le {n d lo k lo' k' : ℕ}
    (hslot : lo + k ≤ n) (hslot' : lo' + k' ≤ n) (hsep : lo + k ≤ lo')
    (ma ua qa ea sz kd kp : ℕ × ℕ)
    (hAP : Fp.Apart (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n)) :
    Fp.Disj (downRegion n d lo k ma ua qa ea sz kd kp)
      (downRegion n d lo' k' ma ua qa ea sz kd kp) := by
  refine hAP.disj_view_collections ?_ ?_ ?_
  · intro i
    apply Fp.inBlock_le_inBlock (by omega)
    have h := Nat.mul_le_mul_left (downArenaStride n i) hslot
    rw [Nat.mul_add] at h
    omega
  · intro i
    apply Fp.inBlock_le_inBlock (by omega)
    have h := Nat.mul_le_mul_left (downArenaStride n i) hslot'
    rw [Nat.mul_add] at h
    omega
  · intro i
    apply Fp.disj_inBlock_of_le
    have h := Nat.mul_le_mul_left (downArenaStride n i) hsep
    rw [Nat.mul_add] at h
    omega

/-- Pairwise disjoint mathematical slot intervals separate all downward result reservations. -/
theorem disj_downRegion {n d lo k lo' k' : ℕ}
    (hslot : lo + k ≤ n) (hslot' : lo' + k' ≤ n)
    (hsep : Disjoint (Finset.Ico lo (lo + k)) (Finset.Ico lo' (lo' + k')))
    (ma ua qa ea sz kd kp : ℕ × ℕ)
    (hAP : Fp.Apart (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n)) :
    Fp.Disj (downRegion n d lo k ma ua qa ea sz kd kp)
      (downRegion n d lo' k' ma ua qa ea sz kd kp) := by
  by_cases h0 : k = 0
  · subst k
    rw [downRegion_zero]
    exact Fp.disj_bot_left _
  by_cases h0' : k' = 0
  · subst k'
    rw [downRegion_zero]
    exact Fp.disj_bot_right _
  have ho : lo + k ≤ lo' ∨ lo' + k' ≤ lo := by
    by_contra h
    push Not at h
    exact Finset.disjoint_left.mp hsep
      (Finset.mem_Ico.mpr ⟨le_max_left _ _, by omega⟩)
      (Finset.mem_Ico.mpr ⟨le_max_right _ _, by omega⟩)
  exact ho.elim
    (fun h => disj_downRegion_of_le hslot hslot' h ma ua qa ea sz kd kp hAP)
    (fun h => (disj_downRegion_of_le hslot' hslot h ma ua qa ea sz kd kp hAP).symm)

/-- A leaf's identity, value vector and kind occupy only its reserved slots. -/
theorem leafFp_le_downRegion {n d lo k : ℕ} (hk : k ≤ n) (hpos : 0 < k)
    (ma ua qa ea sz kd kp : ℕ × ℕ) :
    Fp.blocks [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
      (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1] ≤
      downRegion n d lo k ma ua qa ea sz kd kp := by
  let target := fun i : Fin 7 => ((downArenaOrigins n d ma ua qa ea sz kd kp i).1,
    (downArenaOrigins n d ma ua qa ea sz kd kp i).2 + downArenaStride n i * lo)
  let sizes := fun i : Fin 7 => downArenaStride n i * k
  let parent : Fin 3 → Fin 7 := ![1, 3, 5]
  let source := [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
    (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)]
  let lengths := [2 * (k * k), k, 1]
  have hmul := Nat.mul_le_mul_left (2 * k) hk
  have hview (i : Fin 3) :
      Store.inBlock (source.getD i (0, 0)).1 (source.getD i (0, 0)).2 (lengths.getD i 0) ≤
        Store.inBlock (target (parent i)).1 (target (parent i)).2 (sizes (parent i)) := by
    fin_cases i <;> apply Fp.inBlock_le_inBlock <;>
      simp [source, lengths, target, sizes, parent, downArenaOrigins, downArenaStride] <;>
      nlinarith
  apply Fp.blocks_le_of_forall_getD
  intro i hi
  have hi' : i < 3 := by simpa using hi
  exact (hview ⟨i, hi'⟩).trans (Fp.inBlock_ofFn_le_blocks target sizes (parent ⟨i, hi'⟩))

/-- Every bounded child/split branch fits the node's common output reservations. -/
theorem branchFp_le_downRegion {n d lo k r : ℕ} (hk : k ≤ n) (hpos : 0 < k) (hr : r ≤ k)
    (ma ua qa ea sz kd kp : ℕ × ℕ) :
    Fp.blocks (branchOutputs n d lo k r ma qa sz kd kp) (branchLengths k r) ≤
      downRegion n d lo k ma ua qa ea sz kd kp := by
  let target := fun i : Fin 7 => ((downArenaOrigins n d ma ua qa ea sz kd kp i).1,
    (downArenaOrigins n d ma ua qa ea sz kd kp i).2 + downArenaStride n i * lo)
  let sizes := fun i : Fin 7 => downArenaStride n i * k
  have hmul := Nat.mul_le_mul_left (2 * k) hk
  by_cases hedge : r = k ∨ r = 0
  · simp only [branchOutputs, branchLengths, if_pos hedge]
    let source := [(ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
      (sz.1, sz.2 + n * (d + 1) + lo), (kd.1, kd.2 + n * d + lo)]
    let lengths := [2 * (k * k), 1, 1]
    let parent : Fin 3 → Fin 7 := ![0, 4, 5]
    have hview (i : Fin 3) :
        Store.inBlock (source.getD i (0, 0)).1 (source.getD i (0, 0)).2 (lengths.getD i 0) ≤
          Store.inBlock (target (parent i)).1 (target (parent i)).2 (sizes (parent i)) := by
      fin_cases i <;> apply Fp.inBlock_le_inBlock <;>
        simp [source, lengths, target, sizes, parent, downArenaOrigins, downArenaStride] <;>
        nlinarith
    apply Fp.blocks_le_of_forall_getD
    intro i hi
    have hi' : i < 3 := by simpa using hi
    exact (hview ⟨i, hi'⟩).trans (Fp.inBlock_ofFn_le_blocks target sizes (parent ⟨i, hi'⟩))
  · have hrpos : 0 < r := by omega
    have hrlt : r < k := by omega
    have hleft := Nat.mul_le_mul_left (2 * r) (hr.trans hk)
    have hright := Nat.mul_le_mul_left (2 * (k - r)) ((Nat.sub_le k r).trans hk)
    have hsum := Nat.sub_add_cancel hr
    have hmatrix : 2 * n * r + 2 * ((k - r) * (k - r)) ≤ 2 * n * k := by
      calc
        _ ≤ 2 * n * r + 2 * n * (k - r) := by nlinarith
        _ = 2 * n * k := by rw [← Nat.mul_add, Nat.add_sub_of_le hr]
    have hq := congrArg (fun z : ℕ => 2 * k * z) (Nat.add_sub_of_le hr)
    let parent : Fin 8 → Fin 7 := ![2, 2, 0, 0, 4, 4, 5, 6]
    have hview (i : Fin 8) :
        Store.inBlock ((splitOutputs n d lo k r ma qa sz kd kp).getD i (0, 0)).1
          ((splitOutputs n d lo k r ma qa sz kd kp).getD i (0, 0)).2
          ((splitOutputLengths k r).getD i 0) ≤
          Store.inBlock (target (parent i)).1 (target (parent i)).2 (sizes (parent i)) := by
      fin_cases i <;> apply Fp.inBlock_le_inBlock <;>
        simp [splitOutputs, splitOutputLengths, target, sizes, parent, downArenaOrigins,
          downArenaStride] <;> nlinarith
    simp only [branchOutputs, branchLengths, if_neg hedge]
    apply Fp.blocks_le_of_forall_getD
    intro i hi
    have hi' : i < 8 := by simpa [splitOutputs, splitOutputLengths] using hi
    exact (hview ⟨i, hi'⟩).trans (Fp.inBlock_ofFn_le_blocks target sizes (parent ⟨i, hi'⟩))

/-- The mathematical step's occupied words fit its slot reservation in every outcome. -/
theorem stepFp_le_downRegion {K : Type} [Inhabited K] (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) {n d lo k fuel ell : ℕ}
    (hslot : lo + k ≤ n) (hpos : 0 < k) (R0 beta R eps U : K) (S : ℕ → ℕ → K × K)
    (A : Matrix (Fin k) (Fin k) (K × K)) (ma ua qa ea sz kd kp : ℕ × ℕ) :
    let N := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
    let outcome := eighStep N n fuel R0 beta A R eps ell (storedNodeSample n lo U S)
    Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp outcome) (stepOutputLengths outcome) ≤
      downRegion n d lo k ma ua qa ea sz kd kp := by
  classical
  dsimp only
  by_cases hk1 : k ≤ 1
  · simp only [eighStep, if_pos hk1, stepOutputs, stepOutputLengths]
    exact leafFp_le_downRegion (by omega) hpos ma ua qa ea sz kd kp
  by_cases hstop : dec R ≤ dec (M.mul eps R0)
  · simp only [eighStep, if_neg hk1, Machine.toFloatMachine, hstop, decide_true, if_true,
      stepOutputs, stepOutputLengths]
    exact leafFp_le_downRegion (by omega) hpos ma ua qa ea sz kd kp
  · rw [eighStep_eq_branchOutcome M dec mm qr hslot (by omega) R R0 beta eps U S A hstop,
      stepOutputs_branchOutcome, stepOutputLengths_branchOutcome]
    exact branchFp_le_downRegion (by omega) hpos (Nat.min_le_left _ _)
      ma ua qa ea sz kd kp

/-- Exact active result cells lie within the corresponding disjoint slot reservation. -/
theorem activeStepFp_le_downRegion {K : Type} [Inhabited K] (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) {n d lo k fuel ell : ℕ}
    (hslot : lo + k ≤ n) (R0 beta R eps U : K) (S : ℕ → ℕ → K × K)
    (A : Matrix (Fin k) (Fin k) (K × K)) (ma ua qa ea sz kd kp : ℕ × ℕ) :
    let N := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
    activeStepFp n d lo ma ua qa ea sz kd kp
      (eighStep N n fuel R0 beta A R eps ell (storedNodeSample n lo U S)) ≤
      downRegion n d lo k ma ua qa ea sz kd kp := by
  classical
  dsimp only
  by_cases hpos : 0 < k
  · simp only [activeStepFp, if_pos hpos]
    exact stepFp_le_downRegion M dec mm qr hslot hpos R0 beta R eps U S A
      ma ua qa ea sz kd kp
  · simp only [activeStepFp, if_neg hpos]
    exact bot_le

end NLAlib.SpectralBisection
