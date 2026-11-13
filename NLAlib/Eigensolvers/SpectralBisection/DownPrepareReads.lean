/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownLayout
public import NLAlib.Eigensolvers.SpectralBisection.NodeInputAssembly
public import NLAlib.Ops.Logic.EntryPacking

/-!
# Scan inputs after actual level preparation

Preparation preserves the current matrix, size words and parameters while writing the two
sample batches. These ordinary read facts are shared by functional and resource proofs.

## Main results

* `NLAlib.SpectralBisection.downScan_inputs_of_prepare`: sizes and complete node input tuples.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The level's spatial requirements depend only on buffer capacities and live handles. -/
theorem DownLevelGeometry.congr {K : Type} {n d : ℕ} {ks : ℕ → ℕ}
    {par lv su sg ma ua qa ea sz kd kp c t : ℕ × ℕ} {s s' : Store K}
    (h : DownLevelGeometry n d ks par lv su sg ma ua qa ea sz kd kp c t s)
    (hlength : s'.length = s.length) (hlens : ∀ b, s'.len b = s.len b) :
    DownLevelGeometry n d ks par lv su sg ma ua qa ea sz kd kp c t s' :=
  { h with
    live := h.live.congr hlength
    scratch_room := by rw [hlens]; exact h.scratch_room
    next_room := by rw [hlens]; exact h.next_room
    uniform_room := by rw [hlens]; exact h.uniform_room
    gaussian_room := by rw [hlens]; exact h.gaussian_room
    nodes := fun lo hlo hp =>
      ⟨⟨(h.nodes lo hlo hp).1.1.congr hlens, (h.nodes lo hlo hp).1.2⟩,
        fun r hr => ⟨((h.nodes lo hlo hp).2 r hr).1.congr hlens,
          ((h.nodes lo hlo hp).2 r hr).2⟩⟩ }

/-- The actual preparation frame and its two sample reads supply all pending scan inputs.
This statement concerns stored words and does not impose a probability or accuracy model. -/
theorem downScan_inputs_of_prepare {K : Type} [Inhabited K] (M : Machine K)
    {μ ν : Mem K} {n d : ℕ} {par lv su sg ma sz c t : ℕ × ℕ}
    (ks : ℕ → ℕ) (A : (lo : ℕ) → Matrix (Fin (ks lo)) (Fin (ks lo)) (K × K))
    (R0 eps0 beta R eps : K) (uniform gaussian : List K)
    (hslot : ∀ lo < n, lo + ks lo ≤ n)
    (hsizes : ∀ lo < n, μ.store.get sz.1 (sz.2 + n * d + lo) = some (M.lit (ks lo : ℕ)))
    (hmat : ∀ lo < n, 0 < ks lo →
      μ.store.readBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo)
        (2 * (ks lo * ks lo)) = some ((EntryCodec.pair K).packFinMatrix (A lo)))
    (hpar : μ.store.readBlock par.1 par.2 3 = some [R0, eps0, beta])
    (hlv : μ.store.readBlock lv.1 (lv.2 + 2 * d) 2 = some [R, eps])
    (hc : μ.store.readBlock c.1 c.2 5 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf])
    (hsep : Fp.Disj (downPrepareFp n d lv su sg t)
      (Fp.blocks [par, (lv.1, lv.2 + 2 * d),
        (ma.1, ma.2 + 2 * (n * n) * d), (sz.1, sz.2 + n * d), c]
        [3, 2, 2 * (n * n), n, 5]))
    (hfr : μ.store.EqOff (downPrepareFp n d lv su sg t) ν.store)
    (hU : ν.store.readBlock su.1 su.2 n = some uniform)
    (hG : ν.store.readBlock sg.1 sg.2 (4 * (n * n)) = some gaussian) :
    (∀ lo < n, ν.store.get sz.1 (sz.2 + n * d + lo) = some (M.lit (ks lo : ℕ))) ∧
      ∀ lo < n, 0 < ks lo →
        ν.readBlocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo)) =
          some (nodeInputWords M n R0 beta R eps (vec uniform lo)
            (fun i j => (EntryCodec.pair K).entry gaussian (j * n + i)) (A lo)) := by
  have hSource (i : Fin 5) := (hsep.symm.inBlock_getD_left (i := i.val) (by simp)).symm
  have hp' := hfr.keep (Store.readsOnly_readBlock par.1 par.2 3 _) (by simpa using hSource 0) hpar
  have hlv' := hfr.keep (Store.readsOnly_readBlock lv.1 (lv.2 + 2 * d) 2 _)
    (by simpa using hSource 1) hlv
  have hc' := hfr.keep (Store.readsOnly_readBlock c.1 c.2 5 _) (by simpa using hSource 4) hc
  refine ⟨fun lo hi => hfr.keep (Store.readsOnly_get sz.1 (sz.2 + n * d + lo) _)
    ((hSource 3).mono le_rfl (by apply Fp.inBlock_le_inBlock <;> simp; omega))
    (hsizes lo hi), ?_⟩
  intro lo hi hpos
  have hMaSep : Fp.Disj (downPrepareFp n d lv su sg t)
      (Store.inBlock ma.1 (ma.2 + 2 * (n * n) * d) (2 * (n * n))) := by
    simpa using hSource 2
  have hmat' := hfr.keep (Store.readsOnly_readBlock ma.1
    (ma.2 + 2 * (n * n) * d + 2 * n * lo) (2 * (ks lo * ks lo)) _)
    (hMaSep.mono le_rfl (by
      apply Fp.inBlock_le_inBlock (by omega)
      have hk : ks lo ≤ n := by have := hslot lo hi; omega
      have hm := Nat.mul_le_mul_left (2 * ks lo) hk
      have hs := Nat.mul_le_mul_left (2 * n) (hslot lo hi)
      nlinarith)) (hmat lo hi hpos)
  apply nodeInputs_of_reads hp' hlv' _ _ hmat' hc'
  · exact Store.get_of_readBlock hU hi default
  · have hpack := (EntryCodec.pair K).packMatrix_entry n (2 * n) gaussian (by
      rw [Store.length_of_readBlock hG]; simp [Nat.mul_assoc]; ring)
    simpa only [hpack, show 2 * ((2 * n) * n) = 4 * (n * n) by ring] using hG

end NLAlib.SpectralBisection
