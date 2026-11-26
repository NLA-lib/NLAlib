/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Alg
public import NLAlib.Matrix.Factorizations.LU.Prefix
public import NLAlib.Matrix.Factorizations.LU.StepCorrect

/-!
# Correctness of stored Gaussian elimination

The loop maintains the actual Gaussian residual and committed canonical factor prefixes.
Initialization, materialization and elimination are the scalar routines of the algorithm;
the invariant relates their actual word outputs to the pure factor functions. The residual
is released at return, leaving only the two declared output blocks changed.

## Main results

* `NLAlib.LU.factor_meets`: total stored computation of the canonical LU factors under exact
  scalar arithmetic and comparisons.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has CmpTst Tst]

/-- The fixed scalar elimination routine meets its canonical-factor specification. Every
admitted input executes successfully, including dimension zero. The actual loop uses the
zero-safe step, while the declared input domain ensures that these factors reconstruct the
input matrix. -/
theorem factor_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) :
    (factor (Op := Op) (Tst := Tst)).Meets I (factorSpec dec) := by
  routine_intro [n] (A, L, U) reads (as)
  let B := decodeMatrix dec n n as
  change Writes .total I τ _ (Env.frame [n] [A, L, U])
    (Fp.blocks [L, U] [n * n, n * n]) _ m
  alloc as R
  have hAR : A.1 ≠ R := by change A.1 ≠ m.store.length + 0; omega
  have hRL : R ≠ L.1 := by change m.store.length + 0 ≠ L.1; omega
  have hRU : R ≠ U.1 := by change m.store.length + 0 ≠ U.1; omega
  call (initializeFactors_meets hI) [n] (A, (R, 0), L, U)
    as m₁ hfr₁ hpos₁ (rs, ls, us) hinit
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change A.1 < s_R.length ∧ m.store.length < s_R.length ∧
      L.1 < s_R.length ∧ U.1 < s_R.length
    simp only [List.length_singleton] at hlen_R
    omega
  case' hroom =>
    change (0 + n * n ≤ s_R.len R) ∧ (L.2 + n * n ≤ s_R.len L.1) ∧
      (U.2 + n * n ≤ s_R.len U.1) ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hR.ge,
      by rw [(hbelow_R L.1 hl.2.1).1]; exact hroom.1,
      by rw [(hbelow_R U.1 hl.2.2).1]; exact hroom.2, trivial⟩
  obtain ⟨rfl, rfl, rfl⟩ := hinit
  have hstart : IsFactorPrefix dec B 0 (R, 0) L U m₁.store :=
    IsFactorPrefix.initial hM hrs hls hus
  loop_inv (fun _ => Fp.blocks [(R, 0), L, U] [n * n, n * n, n * n])
    (fun k μ => μ.pos = m.pos ∧ IsFactorPrefix dec B k (R, 0) L U μ.store)
    with k hk m₂ hfr hP
  case round =>
    obtain ⟨hp, hstate⟩ := hP
    obtain ⟨rs, ls, us, hrs, hls, hus, hres, hlo, hup⟩ := hstate.read_blocks
    have hn : 0 < n * n := Nat.mul_pos (Nat.zero_lt_of_lt hk) (Nat.zero_lt_of_lt hk)
    call (step_meets hI hcmp) [n, k] ((R, 0), L, U) (pre := hk)
      as m₃ hfr₃ hpos₃ (rs', ls', us') hpost
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      change m.store.length < m₂.store.length ∧ L.1 < m₂.store.length ∧ U.1 < m₂.store.length
      simp only [List.length_singleton] at hlen_R
      omega
    case' hroom =>
      change (0 + n * n ≤ m₂.store.len R) ∧ (L.2 + n * n ≤ m₂.store.len L.1) ∧
        (U.2 + n * n ≤ m₂.store.len U.1) ∧ True
      rw [hfr.len_eq, hfr.len_eq, hfr.len_eq, hfr₁.len_eq, hfr₁.len_eq, hfr₁.len_eq]
      exact ⟨by simpa only [Nat.zero_add] using hR.ge,
        by rw [(hbelow_R L.1 hl.2.1).1]; exact hroom.1,
        by rw [(hbelow_R U.1 hl.2.2).1]; exact hroom.2, trivial⟩
    have hnext := stepSpec_prefix hM B ⟨k, hk⟩ hpost hres hlo hup
    exact ⟨hpos₃.trans hp,
      IsFactorPrefix.of_reads hrs' hls' hus' hnext.1 hnext.2.1 hnext.2.2⟩
  case exit =>
    rintro m₂ _ ⟨hp, hstate⟩ s₂ hs₂ hB
    obtain ⟨ls, us, hls, hus, hlo, hup⟩ := hstate.read_factors
    refine ⟨hp, [ls, us], Mem.readBlocks_of_cons ?_ (Mem.readBlocks_of_cons ?_ rfl), hlo, hup⟩
    · exact Store.Below.readBlock_of hB hl.2.1 hls
    · exact Store.Below.readBlock_of hB hl.2.2 hus

end NLAlib.LU
