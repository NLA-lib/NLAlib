/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.NodeData

/-!
# Surviving handles of bisection node regions

Input views and constructor-dependent output tuples use only the caller's arena handles.
These facts connect the mathematical node representation to shared scratch-cleanup rules;
changing an offset or child size does not create a new buffer handle.

## Main results

* `NLAlib.SpectralBisection.live_nodeInputs`: readable input views use caller handles.
* `NLAlib.SpectralBisection.live_branchOutputs`: every branch uses caller output handles.
* `NLAlib.SpectralBisection.live_stepOutputs`: mathematical outcomes survive scratch release.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The eight input views belong to the supplied caller buffers. -/
theorem live_nodeInputs {K : Type} {m : Mem K} {n d lo : ℕ}
    {par lv su sg ma c : ℕ × ℕ} (h : m.Live [par, lv, su, sg, ma, c]) :
    m.Live (nodeInputs n d lo par lv su sg ma c) := by
  simp only [Mem.live_cons, Mem.live_nil, and_true] at h
  simp only [nodeInputs, Mem.live_cons, Mem.live_nil, and_true]
  tauto

/-- Every bounded-index branch writes only the five caller-owned matrix and metadata arenas. -/
theorem live_branchOutputs {K : Type} {m : Mem K} {n d lo k r : ℕ}
    {ma qa sz kd ks : ℕ × ℕ} (h : m.Live [ma, qa, sz, kd, ks]) :
    m.Live (branchOutputs n d lo k r ma qa sz kd ks) := by
  simp only [Mem.live_cons, Mem.live_nil, and_true] at h
  unfold branchOutputs
  split_ifs <;> simp only [splitOutputs, Mem.live_cons, Mem.live_nil, and_true] <;> tauto

/-- The stored representation of every mathematical outcome uses only caller-owned buffers.
The conclusion holds for leaves, either shifted child, and the two-child split. -/
theorem live_stepOutputs {K : Type} {m : Mem K} {n d lo k : ℕ}
    {ma ua qa ea sz kd ks : ℕ × ℕ} (h : m.Live [ma, ua, qa, ea, sz, kd, ks])
    (step : EighStep K k) : m.Live (stepOutputs n d lo ma ua qa ea sz kd ks step) := by
  simp only [Mem.live_cons, Mem.live_nil, and_true] at h
  cases step <;> simp only [stepOutputs, splitOutputs, Mem.live_cons, Mem.live_nil,
    and_true] <;> tauto

/-- The projector operands are separated views of the node scratch and readable constants.
Only four of the five shared constant words are read by this subprogram. -/
theorem apart_nodeProjectors {n d lo k : ℕ}
    {par lv su sg ma c t sp w b tm pp pm : ℕ × ℕ}
    (h : Fp.Apart [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))
    (hp : Fp.Disj (Fp.blocks [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))
      (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k))) :
    Fp.Apart [w, sp, c, b, tm, pp, pm]
      [2 * (k * k), 2, 4, 2 * (k * k), 2 * (k * k), 2 * (k * k), 2 * (k * k)] := by
  have hc : Store.inBlock c.1 c.2 5 ≤
      Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k) := by
    fp_sub [nodeInputs, nodeInputLengths]
  have hfull : Fp.Apart ([c] ++ [t, sp, w, b, tm, pp, pm])
      ([5] ++ nodeScratchLengths k) :=
    (show Fp.Apart [c] [5] from by disjoint).append h rfl
      (by simpa only [Fp.blocks, sup_bot_eq] using (hp.mono le_rfl hc).symm)
  let parent : Fin 7 → Fin 8 := ![3, 2, 0, 4, 5, 6, 7]
  have hparent : Function.Injective parent := by decide
  have hv := hfull.subviews parent
    ![0, 0, 0, 0, 0, 0, 0]
    ![2 * (k * k), 2, 4, 2 * (k * k), 2 * (k * k), 2 * (k * k), 2 * (k * k)]
    (by intro i; fin_cases i <;> simp [parent, nodeScratchLengths])
    (fun a b hab hp' => False.elim (hab (hparent hp')))
  simpa [List.ofFn_succ, parent, nodeScratchLengths] using hv

end NLAlib.SpectralBisection
