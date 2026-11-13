/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpDispatch
public import NLAlib.Eigensolvers.SpectralBisection.UpStepData
public import NLAlib.Eigensolvers.SpectralBisection.UpGeometry
public import NLAlib.Eigensolvers.SpectralBisection.Assembly

/-!
# Upward reconstruction of mathematical node outcomes

The stored constructor and child results determine the upward output. Leaves keep their
stored result; one-child outcomes copy the child basis and add their stored signed shift.
The proofs consume the same mathematical outcome representation as the downward node.

## Main results

* `NLAlib.SpectralBisection.writes_upNode_leaf`: a stored leaf keeps its complete result.
* `NLAlib.SpectralBisection.writes_upNode_shiftResult`: actual one-child assembly.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Common arena regions used by upward node reconstruction: parent outputs, child
reservations, parent basis, constructor metadata, split metadata and signed shifts. -/
def upNodeRegions (n d lo : ℕ) (ua qa ea kd kp t : ℕ × ℕ) : List (ℕ × ℕ) :=
  resultOperands n d lo ua ea ++
    [(ua.1, ua.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
      (ea.1, ea.2 + n * (d + 1) + lo),
      (qa.1, qa.2 + 2 * (n * n) * d + 2 * n * lo),
      (kd.1, kd.2 + n * d + lo), (kp.1, kp.2 + n * d + lo), t]

/-- Capacities reserved for the common upward regions. Child matrices use root-stride slots. -/
def upNodeRegionLengths (n k : ℕ) : List ℕ :=
  [2 * (k * k), k, 2 * n * k, k, 2 * (k * k), 1, 1, 2]

/-- A stored leaf already has its mathematical output, and its actual metadata dispatch
executes no arithmetic or matrix calls. -/
theorem writes_upNode_leaf {K Op Tst : Type} [Has ScalarOp Op] [Has MatrixOp Op]
    [Has IdxTst Tst] {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hQ : IsToNat dec I) {τ : Tape K} {m : Mem K} {n d lo k : ℕ} {R : K}
    {ma ua qa ea sz kd kp t : ℕ × ℕ} (U : Matrix (Fin k) (Fin k) (K × K))
    (values : Fin k → K) (hLit : dec (M.lit 1) = 1)
    (hStep : StoresStep M R n d lo ma ua qa ea sz kd kp (.leaf U values) m) :
    Writes .total I τ (upNodeImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [n, d, lo, k] [ua, qa, ea, kd, kp, t])
      (Fp.blocks (resultOperands n d lo ua ea) (resultLengths k))
      (fun m' => m'.pos = m.pos ∧ StoresResult n d lo ua ea (U, values) m'.store) m := by
  have hev := eval_upNode_leaf (τ := τ) (k := k) (ua := ua) (qa := qa) (ea := ea)
    (kp := kp) (t := t) hQ hStep.kind_read hLit
  unfold Writes Wp
  rw [hev]
  exact ⟨m, rfl, Store.EqOff.refl _ _, rfl, hStep.leaf_storesResult⟩

/-- A one-child outcome is reconstructed into its child basis and shifted eigenvalues.
The scalar shift words are the actual upward half-radius computation, and constructor
literals decode exactly within their explicitly declared integer range. -/
theorem writes_upNode_shiftResult {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has MatrixOp Op] [Has IdxTst Tst] {M : Machine K} {dec : K → ℝ}
    {I : Interp Op Tst K} (hS : IsScalar M I) (hQ : IsToNat dec I)
    {τ : Tape K} {m : Mem K} {n d lo k : ℕ} {R sigma : K} {side : Bool}
    {ma ua qa ea sz kd kp t : ℕ × ℕ} {A : Matrix (Fin k) (Fin k) (K × K)}
    (child : Matrix (Fin k) (Fin k) (K × K) × (Fin k → K))
    (hStep : StoresStep M R n d lo ma ua qa ea sz kd kp (.shift side A sigma) m)
    (hChild : StoresResult n (d + 1) lo ua ea child m.store)
    (hLit : IsExactNatLit dec M (max n 4)) (hk : k ≤ n)
    (hl : m.Live [ua, qa, ea, kd, kp, t])
    (ht : m.store.get t.1 t.2 = some (M.div R (M.lit 2)) ∧
      m.store.get t.1 (t.2 + 1) = some (M.neg (M.div R (M.lit 2))))
    (hroom : m.Room (resultOperands n d lo ua ea) (resultLengths k))
    (hap : Fp.Apart (upNodeRegions n d lo ua qa ea kd kp t) (upNodeRegionLengths n k)) :
    Writes .total I τ (upNodeImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [n, d, lo, k] [ua, qa, ea, kd, kp, t])
      (Fp.blocks (resultOperands n d lo ua ea) (resultLengths k))
      (fun m' => m'.pos = m.pos ∧ StoresResult n d lo ua ea
        (child.1, fun i => M.add (child.2 i) sigma) m'.store) m := by
  have hs : m.store.get t.1 (t.2 + if side then 0 else 1) = some sigma := by
    rw [hStep.1]
    cases side with
    | false => simpa using ht.2
    | true => simpa using ht.1
  have hdec : dec (M.lit ((if side then 2 else 3 : ℕ) : ℚ)) =
      (if side then (2 : ℕ) else 3) := by
    exact hLit _ (by cases side <;> simp)
  have hApart := apart_upShift hk (by
    simpa only [upNodeRegions, upNodeRegionLengths, resultOperands, List.cons_append,
      List.nil_append] using hap) side
  simp only [resultOperands, resultLengths, Mem.room_cons, Mem.room_nil, and_true] at hroom
  refine (writes_upNode_shift hS hQ side child.1 (List.ofFn child.2) sigma
    (M.lit ((if side then 2 else 3 : ℕ) : ℚ)) hl hStep.kind_read hdec
    hChild.matrix_read hChild.values_read hs hroom.1 hroom.2 hApart).mono le_rfl ?_
  intro m' _ ⟨hp, hr⟩
  refine ⟨hp, storesResult_iff_readBlocks.mpr ?_⟩
  simpa only [resultOperands, resultLengths, List.map_ofFn, Function.comp_def] using hr

end NLAlib.SpectralBisection
