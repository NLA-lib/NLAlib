/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.OneEigParts

/-!
# `OneEig`: one approximate eigenvalue by a regularized search

`OneEig` ([BanksGarzaVargasSrivastava2025, §3.2]) finds a point within $\beta'$ of the spectrum of
an upper Hessenberg matrix whose eigenvalues all carry weight, and at least $\eta_1$ away from it:
from a disk sample $s_0$ of radius $\eta_2$ (not the paper's unperturbed start, its erratum B3),
each round estimates the distances of the six perturbed net points $s + \tau e^{i\pi j/3} + w$
with `DistSpec` and moves to the best one if its estimate is at most $0.66\,\tau$; the search stops
with the flag $0$ when the estimate is at most $0.9\beta'$, with the flag $1$ if a round makes no
progress or the round cap $t$ is reached. One attempt, no retry loop (the paper's erratum P13):
a failure is counted in the probability.

The probability of failure is a union bound over the start and the $t$ rounds: each draws one
polar sample, and a sample is bad only if it brings a candidate (computed in rounded arithmetic)
within $\eta_1 + 40\boldsymbol{u}\Sigma$ of an eigenvalue; on the good samples the run is an
abstract run (`NLAlib.SmallEig.OneEigRun`) with steps of size $\eta_2 + 60\boldsymbol{u}\Sigma$.

## Main definitions

* `NLAlib.SmallEig.oneEig`: the program `[N, m, q, t] (H, Q) → (Lam, Fl)`, from its parts in
  `NLAlib.Eigensolvers.SmallEig.OneEigParts`.
* `NLAlib.SmallEig.OneEigInput`: the memory of a call.
* `NLAlib.SmallEig.OneEigFrame`, `NLAlib.SmallEig.OneEigLoopInv`: the memory of a run and the
  invariant of its loop.

## Main results

* `NLAlib.SmallEig.oneEigRound_pwrites`, `NLAlib.SmallEig.oneEigStart_pwrites`: the round and
  the start as probabilistic blocks.
* `NLAlib.SmallEig.oneEig_writes_word`, `NLAlib.SmallEig.oneEig_pwrites`,
  `NLAlib.SmallEig.oneEig_terminates`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Metric Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]

/-- **`OneEig`** ([BanksGarzaVargasSrivastava2025, Proposition 3.5], corrected): the six
directions $e^{i\pi j/3}$; the start `Lam` a polar sample of
the radius $\eta_2$ = `Q[4]` and its estimate $\tau$ by `NLAlib.SmallEig.distSpec`; the flag $0$
(`NLAlib.SmallEig.oneEigStart`);
then, while $0.9\beta'$ = `Q[5]` $< \tau$ and for at most $t$ rounds, one round
(`NLAlib.SmallEig.oneEigRound`: one polar sample $w$, the estimates of the six points
$s + \tau e^{i\pi j/3} + w$, and the move to the best one if its estimate is at most
$0.66\,\tau$, otherwise the flag $1$ and the estimate $0$, which ends the loop); at the cap with
$0.9\beta' < \tau$, the flag $1$ (`NLAlib.SmallEig.oneEigCheck`). The interface is
`[N, m, q, t] (H, Q) → (Lam, Fl)`; the scratch is scoped.
Algorithm: small-eig -/
def oneEig : Impl O Q := opsImpl% [N, m, q, t] (H, Qw) → (Lam, Fl) {
  let Tau ← alloc 1;
  let Z ← alloc 2;
  let Pt ← alloc 2;
  let Tc ← alloc 1;
  let Bt ← alloc 3;
  let D ← alloc 12;
  let K ← alloc 2;
  run (oneEigStart (O := O) (Q := Q)).body [N, m, q] (H, Qw, Lam, Tau, Fl, D, K);
  while i < t, (Has.inj CmpTst.lt) [] (Qw[5], Tau) {
    run (oneEigRound (O := O) (Q := Q)).body [N, m, q]
      (H, Qw, D, Lam, Tau, Fl, Z, Pt, Tc, Bt, K)
  } then {
    run (oneEigCheck (O := O) (Q := Q)).body [] (Qw[5], Tau, Fl)
  }
}

end Program

/-- The memory of a call of `NLAlib.SmallEig.oneEig` on $\mathbf{H}$ of order $n + 1$: the
matrix at `h`, the words `qs` at `qw`, room for the pair `lam` and the flag `f`, all live and
apart. -/
def OneEigInput {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (qs : List ℝ)
    (h qw lam f : ℕ × ℕ) (μ : Mem ℝ) : Prop :=
  μ.Live [h, qw, lam, f] ∧ μ.Room [h, qw, lam, f] [2 * ((n + 1) * (n + 1)), qs.length, 2, 1] ∧
    Fp.Apart [h, qw, lam, f] [2 * ((n + 1) * (n + 1)), qs.length, 2, 1] ∧
    HoldsMatrix h H μ.store ∧ μ.store.readBlock qw.1 qw.2 qs.length = some qs

/-! ### Cells holding words -/

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]

/-- The views of `NLAlib.SmallEig.OneEigInput` are apart: `lam` and `f` from the matrix, from
each other and from the words. -/
theorem OneEigInput.disj {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {qs : List ℝ}
    {h qw lam f : ℕ × ℕ} {μ : Mem ℝ} (hin : OneEigInput H qs h qw lam f μ) :
    Fp.Disj (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock h.1 h.2 (2 * ((n + 1) * (n + 1)))) ∧
    Fp.Disj (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock qw.1 qw.2 qs.length) ∧
    Fp.Disj (Store.inBlock lam.1 lam.2 2) (Store.inBlock f.1 f.2 1) := by
  obtain ⟨-, -, ⟨dh, dq, dl, -⟩, -, -⟩ := hin
  simp only [Fp.blocks_cons, Fp.blocks_nil] at dh dq dl
  exact ⟨(dh.mono le_rfl (sup_le (le_sup_left.trans le_sup_right)
      ((le_sup_left.trans le_sup_right).trans le_sup_right))).symm,
    (dq.mono le_rfl (sup_le le_sup_left (le_sup_left.trans le_sup_right))).symm,
    dl.mono le_rfl le_sup_left⟩

/-- `NLAlib.SmallEig.oneEig` on a scalar machine with the literal $0$ exact, index literals,
exact comparisons and an exact polar sampler: from `NLAlib.SmallEig.OneEigInput` with at least
six words, on every tape, it writes only the pair `lam` and the flag `f`, and stores a pair and a
flag $0$ or $1$. -/
theorem oneEig_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hzero : M.lit 0 = 0) (hL : IsIndexLit M I) (hCmp : IsCmp id I) {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {n m q t : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} (hqs : 6 ≤ qs.length) {τ : Tape ℝ} {μ : Mem ℝ} {h qw lam f : ℕ × ℕ}
    (hin : OneEigInput H qs h qw lam f μ) :
    Writes .total I τ (oneEig (O := O) (Q := Q)).body (Env.frame [n + 1, m, q, t] [h, qw, lam, f])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ z : ℂ, μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im]) ∧
        (μ'.store.get f.1 f.2 = some (M.lit 0) ∨ μ'.store.get f.1 f.2 = some (M.lit 1))) μ := by
  obtain ⟨hdh, hdq, hlf⟩ := hin.disj
  obtain ⟨hl, ⟨-, -, hrl, hrf, -⟩, -, hH, hq⟩ := hin
  have hlive : h.1 < μ.store.length ∧ qw.1 < μ.store.length ∧ lam.1 < μ.store.length ∧
      f.1 < μ.store.length := by simpa [Mem.Live] using hl
  unfold oneEig
  change Writes .total I τ (Stmt.allocs [.const 1, .const 2, .const 2, .const 1, .const 3,
    .const 12, .const 2] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [1, 2, 2, 1, 3, 12, 2]) rfl
    (fun hBelow ⟨⟨z, hz⟩, hF⟩ => ⟨⟨z, hBelow.readBlock_of hlive.2.2.1 hz⟩,
      hF.imp (hBelow.get_of hlive.2.2.2) (hBelow.get_of hlive.2.2.2)⟩) ?_
  intro s₁ hlen hlens hBelow
  set L := μ.store.length with hLd
  simp only [List.length_cons, List.length_nil] at hlen
  obtain ⟨hH₁, hq₁⟩ := And.intro (hH.of_below hBelow hlive.1) (hBelow.readBlock_of hlive.2.1 hq)
  have hG : Fp.Disj (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (Store.inBlock h.1 h.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_sup_left.mpr ⟨hdh, disj_above_inBlock_of_lt hlive.1⟩
  have hGq : Fp.Disj (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (Store.inBlock qw.1 qw.2 qs.length) :=
    Fp.disj_sup_left.mpr ⟨hdq, disj_above_inBlock_of_lt hlive.2.1⟩
  refine (oneEigStart_writes (μ := ⟨s₁, μ.pos⟩) (m := m) (q := q) hS hzero hL hCmp hDisk
    hlive.1 hlive.2.1 hlive.2.2.1 hlen (by simpa using hlens 0 (by simp))
    (by simpa using hlens 5 (by simp)) (by simpa using hlens 6 (by simp))
    (by rw [(hBelow lam.1 hlive.2.2.1).1]; exact hrl)
    (by rw [(hBelow f.1 hlive.2.2.2).1]; exact hrf)
    (hdh.mono le_sup_left le_rfl) hH₁ (Store.get_of_readBlock hq₁ (by omega) 0)).frame_seq_le
    rfl rfl (by simp [Mem.Live]; omega) le_rfl ?_
  rintro μ₄ hfrA ⟨hW₄, hF₄⟩
  have hcheck : ∀ μ' : Mem ℝ, (⟨s₁, μ.pos⟩ : Mem ℝ).store.EqOff (Store.inBlock lam.1 lam.2 2 ⊔
      Store.inBlock f.1 f.2 1 ⊔ Fp.above L) μ'.store →
      HoldsWords μ'.store (oneEigCells L lam) → OneEigFlag M f μ'.store →
      (∃ v, μ'.store.get qw.1 (qw.2 + 5) = some v) ∧ ∃ v, μ'.store.get L 0 = some v := by
    intro μ' hfr hW _
    exact ⟨⟨_, hfr.keep (Store.readsOnly_get _ _ _) (hGq.mono le_rfl
      (Fp.inBlock_le_inBlock (by omega) (by omega))) (Store.get_of_readBlock hq₁ (j := 5)
        (by omega) 0)⟩, hW.get (by simp [oneEigCells])⟩
  refine (writes_whileFuel (N := t) rfl (fun _ => Store.inBlock lam.1 lam.2 2 ⊔
      Store.inBlock f.1 f.2 1 ⊔ Fp.above L) (fun _ _ => le_rfl) (Store.inBlock f.1 f.2 1)
    (fun _ μ' => HoldsWords μ'.store (oneEigCells L lam) ∧ OneEigFlag M f μ'.store) _
    ⟨hW₄, hF₄⟩ ?_ ?_).mono (sup_le le_rfl (le_sup_right.trans le_sup_left)) fun _ _ h => h
  · rintro i - μ' hfr' ⟨hW', hF'⟩
    have hfrC := hfrA.trans' hfr'
    have hG' : Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L ⊔
        (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L) ≤
        Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L := sup_le le_rfl le_rfl
    obtain ⟨⟨a, ha⟩, b, hb⟩ := hcheck μ' (hfrC.mono hG') hW' hF'
    refine ⟨_, (Interp.testAt_eq (a := [(qw.1, qw.2 + 5), (L, 0)]) rfl rfl).trans
      (hCmp.test_lt ha hb), ?_⟩
    dsimp only
    split_ifs
    · refine (oneEigRound_writes hS hzero hL hCmp hDisk hqs hlive.1 hlive.2.1 hlive.2.2.1
        hlive.2.2.2 (by rw [hfrC.length_eq]; exact hlen)
        (by rw [hfrC.len_eq]; simpa using hlens 0 (by simp))
        (by rw [hfrC.len_eq]; simpa using hlens 1 (by simp))
        (by rw [hfrC.len_eq]; simpa using hlens 2 (by simp))
        (by rw [hfrC.len_eq]; simpa using hlens 3 (by simp))
        (by rw [hfrC.len_eq]; simpa using hlens 4 (by simp))
        (by rw [hfrC.len_eq]; simpa using hlens 6 (by simp))
        (by rw [hfrC.len_eq, (hBelow lam.1 hlive.2.2.1).1]; exact hrl)
        (by rw [hfrC.len_eq, (hBelow f.1 hlive.2.2.2).1]; exact hrf) hlf
        ((hH₁.of_eqOff (hfrC.mono hG') hG)) (hfrC.mono hG' |>.keep
          (Store.readsOnly_readBlock _ _ _ _) hGq hq₁) hW' hF').in_frame rfl rfl
        (by simp [Mem.Live, hfrC.length_eq]; omega)
    · have hrf' : f.2 < μ'.store.len f.1 := by
        rw [hfrC.len_eq, (hBelow f.1 hlive.2.2.2).1]; exact hrf
      refine ((oneEigCheck_writes hL hCmp ha hb hrf' hF').in_frame rfl rfl
        (by simp [Mem.Live, hfrC.length_eq]; omega)).mono le_rfl fun μ'' hfr'' hF'' => ⟨?_, hF''⟩
      obtain ⟨x, y, hz⟩ := hW'.readBlock_pair (b := lam.1) (o := lam.2) (by simp [oneEigCells])
        (by simp [oneEigCells])
      exact ⟨⟨x, y⟩, hfr''.keep (Store.readsOnly_readBlock _ _ _ _) hlf.symm hz⟩
  · rintro μ' hfr' ⟨hW', hF'⟩
    have hfrC := (hfrA.trans' hfr').mono fun _ _ h => h.elim id id
    obtain ⟨⟨a, ha⟩, b, hb⟩ := hcheck μ' hfrC hW' hF'
    have hrf' : f.2 < μ'.store.len f.1 := by
      rw [hfrC.len_eq, (hBelow f.1 hlive.2.2.2).1]; exact hrf
    refine ((oneEigCheck_writes hL hCmp ha hb hrf' hF').in_frame rfl rfl
      (by simp [Mem.Live, hfrC.length_eq]; omega)).mono le_rfl fun μ'' hfr'' hF'' => ⟨?_, hF''⟩
    obtain ⟨x, y, hz⟩ := hW'.readBlock_pair (b := lam.1) (o := lam.2) (by simp [oneEigCells])
      (by simp [oneEigCells])
    exact ⟨⟨x, y⟩, hfr''.keep (Store.readsOnly_readBlock _ _ _ _) hlf.symm hz⟩

/-- The memory of a run of `NLAlib.SmallEig.oneEig` with the scratch from `L`: the views `h`,
`qw`, `lam`, `f` of `NLAlib.SmallEig.OneEigInput` below `L` and apart, the seven scratch buffers
`Tau`, `Z`, `Pt`, `Tc`, `Bt`, `D`, `K` at `L`, …, `L + 6` with their lengths, the matrix at `h`
and the words at `qw`. -/
structure OneEigFrame {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (qs : List ℝ)
    (h qw lam f : ℕ × ℕ) (L : ℕ) (μ : Mem ℝ) : Prop where
  /-- The matrix view is below the scratch. -/
  hh : h.1 < L
  /-- The words are below the scratch. -/
  hqw : qw.1 < L
  /-- The point is below the scratch. -/
  hlam : lam.1 < L
  /-- The flag is below the scratch. -/
  hf : f.1 < L
  /-- The views are apart. -/
  apart : Fp.Apart [h, qw, lam, f] [2 * ((n + 1) * (n + 1)), qs.length, 2, 1]
  /-- The scratch ends the store. -/
  length : μ.store.length = L + 7
  /-- The lengths of the scratch buffers. -/
  len : μ.store.len L = 1 ∧ μ.store.len (L + 1) = 2 ∧ μ.store.len (L + 2) = 2 ∧
    μ.store.len (L + 3) = 1 ∧ μ.store.len (L + 4) = 3 ∧ μ.store.len (L + 5) = 12 ∧
    μ.store.len (L + 6) = 2
  /-- Room for the point. -/
  roomLam : lam.2 + 2 ≤ μ.store.len lam.1
  /-- Room for the flag. -/
  roomF : f.2 < μ.store.len f.1
  /-- The matrix. -/
  matrix : HoldsMatrix h H μ.store
  /-- The words. -/
  words : μ.store.readBlock qw.1 qw.2 qs.length = some qs

namespace OneEigFrame

variable {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {qs : List ℝ} {h qw lam f : ℕ × ℕ}
  {L : ℕ} {μ μ' : Mem ℝ}

/-- The point and the flag are apart from the matrix, from the words and from each other. -/
theorem disj (hF : OneEigFrame H qs h qw lam f L μ) :
    Fp.Disj (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (Store.inBlock h.1 h.2 (2 * ((n + 1) * (n + 1)))) ∧
    Fp.Disj (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (Store.inBlock qw.1 qw.2 qs.length) ∧
    Fp.Disj (Store.inBlock lam.1 lam.2 2) (Store.inBlock f.1 f.2 1) := by
  obtain ⟨dh, dq, dl, -⟩ := hF.apart
  simp only [Fp.blocks_cons, Fp.blocks_nil] at dh dq dl
  exact ⟨Fp.disj_sup_left.mpr ⟨(dh.mono le_rfl (sup_le (le_sup_left.trans le_sup_right)
      ((le_sup_left.trans le_sup_right).trans le_sup_right))).symm,
      disj_above_inBlock_of_lt hF.hh⟩,
    Fp.disj_sup_left.mpr ⟨(dq.mono le_rfl (sup_le le_sup_left
      (le_sup_left.trans le_sup_right))).symm, disj_above_inBlock_of_lt hF.hqw⟩,
    dl.mono le_rfl le_sup_left⟩

/-- The frame survives writes to the point, the flag and the scratch. -/
theorem of_eqOff (hF : OneEigFrame H qs h qw lam f L μ)
    (hfr : μ.store.EqOff (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      μ'.store) : OneEigFrame H qs h qw lam f L μ' := by
  obtain ⟨dh, dq, -⟩ := hF.disj
  obtain ⟨l0, l1, l2, l3, l4, l5, l6⟩ := hF.len
  exact ⟨hF.hh, hF.hqw, hF.hlam, hF.hf, hF.apart, by rw [hfr.length_eq, hF.length],
    ⟨by rw [hfr.len_eq, l0], by rw [hfr.len_eq, l1], by rw [hfr.len_eq, l2],
      by rw [hfr.len_eq, l3], by rw [hfr.len_eq, l4], by rw [hfr.len_eq, l5],
      by rw [hfr.len_eq, l6]⟩, by rw [hfr.len_eq]; exact hF.roomLam,
    by rw [hfr.len_eq]; exact hF.roomF, hF.matrix.of_eqOff hfr dh,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) dq hF.words⟩

/-- The frame's views are live. -/
theorem live (hF : OneEigFrame H qs h qw lam f L μ) : μ.Live [h, qw, lam, f] := by
  have := hF.length; have := hF.hh; have := hF.hqw; have := hF.hlam; have := hF.hf
  simp [Mem.Live]; omega

end OneEigFrame

/-- The invariant of the loop of `NLAlib.SmallEig.oneEig` with the scratch from `L` before round
$i$: the frame (`NLAlib.SmallEig.OneEigFrame`), the computed directions at `D`, the factor
$\mathrm{fl}(0.66)$ at `K[0]`, the flag $0$, and an abstract run (`NLAlib.SmallEig.OneEigRun`)
of $i$ rounds on the $d_k$ with steps of size at most $\eta$, starting within $\eta_2$ of $0$, with
estimates above $0.9\beta$ before round $i$ and points at distance at least $\eta_1$, whose last
point is at `Lam` and last estimate at `Tau`. -/
def OneEigLoopInv (M : Machine ℝ) {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (d : Fin (n + 1) → ℂ) (qs : List ℝ) (h qw lam f : ℕ × ℕ) (L : ℕ) (β η₁ η₂ η : ℝ) (i : ℕ)
    (μ : Mem ℝ) : Prop :=
  OneEigFrame H qs h qw lam f L μ ∧
    (∀ k < 12, μ.store.get (L + 5) k = some (oneEigDirWords M k)) ∧
    μ.store.get (L + 6) 0 = some (M.lit (66 / 100)) ∧ μ.store.get f.1 f.2 = some 0 ∧
    ∃ (s : ℕ → ℂ) (τ : ℕ → ℝ), OneEigRun (Set.range d) η i s τ ∧ ‖s 0‖ ≤ η₂ ∧
      (∀ k < i, 0.9 * β < τ k) ∧ (∀ k ≤ i, η₁ ≤ Metric.infDist (s k) (Set.range d)) ∧
      μ.store.readBlock lam.1 lam.2 2 = some [(s i).re, (s i).im] ∧ μ.store.get L 0 = some (τ i)

/-- The centre $s + \tau D_j$ of the candidate `j` of a round of `NLAlib.SmallEig.oneEig` with
the scratch from `L`: the point read at `lam`, the estimate read at `Tau` (uninitialised words
read as $0$) and the computed direction `j`. -/
def oneEigCentre (M : Machine ℝ) (lam : ℕ × ℕ) (L j : ℕ) (μ : Mem ℝ) : ℂ :=
  storedMatrix lam 1 1 μ.store 0 0 + (((μ.store.get L 0).getD 0 : ℝ) : ℂ) * oneEigDir M j

/-- The centre read from a memory holding the point $s$ and the estimate $\tau$. -/
theorem oneEigCentre_eq {M : Machine ℝ} {lam : ℕ × ℕ} {L j : ℕ} {μ : Mem ℝ} {s : ℂ} {t : ℝ}
    (hs : μ.store.readBlock lam.1 lam.2 2 = some [s.re, s.im]) (ht : μ.store.get L 0 = some t) :
    oneEigCentre M lam L j μ = s + t * oneEigDir M j := by
  have hre := Store.get_of_readBlock hs (j := 0) (by norm_num) 0
  have him := Store.get_of_readBlock hs (j := 1) (by norm_num) 0
  simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at hre him
  have : storedMatrix lam 1 1 μ.store 0 0 = s := by
    apply Complex.ext <;> simp [storedMatrix, hre, him]
  rw [oneEigCentre, this, ht, Option.getD_some]

/-- The bad windows of a round of `NLAlib.SmallEig.oneEig` with the scratch from `L`: off the unit
square, or bringing some centre plus the polar sample of radius $\eta_2$ within $\eta$ of some
$d_i$. Jointly measurable in the memory and the window. -/
theorem measurableSet_oneEigBad (M : Machine ℝ) (lam : ℕ × ℕ) (L : ℕ) {N : ℕ} (d : Fin N → ℂ)
    (η₂ η : ℝ) :
    MeasurableSet {x : Mem ℝ × (Fin 2 → ℝ) | (∃ k, x.2 k ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ (j : Fin 6) (i : Fin N), ‖oneEigCentre M lam L j x.1 + polarDisk 0 η₂ x.2 - d i‖ < η} := by
  have hw : Measurable fun m : Mem ℝ => (m.store.get L 0).getD 0 :=
    measurable_snd.comp (Mem.measurable_cell (L, 0))
  have hc : ∀ j : ℕ, Measurable fun m : Mem ℝ => oneEigCentre M lam L j m := fun j =>
    ((measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp
      (measurable_storedMatrix lam 1 1))).add ((Complex.measurable_ofReal.comp hw).mul_const _)
  have hp : Measurable (polarDisk 0 η₂) := by unfold polarDisk; fun_prop
  have e1 : {x : Mem ℝ × (Fin 2 → ℝ) | (∃ k, x.2 k ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ (j : Fin 6) (i : Fin N), ‖oneEigCentre M lam L j x.1 + polarDisk 0 η₂ x.2 - d i‖ < η} =
      (⋃ k, (fun x : Mem ℝ × (Fin 2 → ℝ) => x.2 k) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ) ∪
        ⋃ (j : Fin 6) (i : Fin N),
          {x | ‖oneEigCentre M lam L j x.1 + polarDisk 0 η₂ x.2 - d i‖ < η} := by
    ext x; simp
  rw [e1]
  refine (MeasurableSet.iUnion fun k => measurableSet_Icc.compl.preimage
    ((measurable_pi_apply k).comp measurable_snd)).union
      (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun i => ?_)
  exact measurableSet_lt ((((hc j).comp measurable_fst).add (hp.comp measurable_snd)).sub_const _
    |>.norm) measurable_const

/-- A good round of `OneEig` extends the run: on a scalar machine in the standard model at
$0 \le \boldsymbol{u} \le 1/5000$ with index literals, the literals $0$ and $1$ exact, exact
comparisons and an exact polar sampler on the stream `sU`, with `DistSpec` accurate on the points
of modulus at most $10\Sigma$ at distance at least $\eta_1$ from the $d_i$, $\lvert d_i\rvert \le
\Sigma$, $0 \le \eta_2 \le 0.02\,\Sigma$, $\beta > 0$, $\eta = \eta_2 + 60\boldsymbol{u}\Sigma \le
0.027\,\beta$ and the word $\eta_2$ at `qw[4]`: from the loop invariant
`NLAlib.SmallEig.OneEigLoopInv` before round $i$ with an estimate above $0.9\beta$, if the window
at the current position is good (in the unit square, and no centre
`NLAlib.SmallEig.oneEigCentre` plus the polar sample within $\eta_1 + 40\boldsymbol{u}\Sigma$ of a
$d_i$), the round writes only the point, the flag and the scratch and ends in the invariant before
round $i + 1$. -/
theorem oneEigRound_step {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 5000) (hL : IsIndexLit M I)
    (h0 : M.lit 0 = 0) (h1 : M.lit 1 = 1) (hCmp : IsCmp id I) {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {n m q L : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} {S β η₁ η₂ : ℝ}
    (hDS : DistSpecAccurateOn (O := O) (Q := Q) I H d m q
      {p | ‖p‖ ≤ 10 * S ∧ ∀ i, η₁ ≤ ‖d i - p‖})
    (hdS : ∀ i, ‖d i‖ ≤ S) (hη₂0 : 0 ≤ η₂) (hη₂S : η₂ ≤ 0.02 * S) (hβ : 0 < β)
    (hηr : η₂ + 60 * u * S ≤ 0.027 * β) {qs : List ℝ} (hqs : 6 ≤ qs.length)
    (hq4 : qs.getD 4 0 = η₂) {τ : Tape ℝ} {μ : Mem ℝ} {h qw lam f : ℕ × ℕ} {i : ℕ}
    (hI : OneEigLoopInv M H d qs h qw lam f L β η₁ η₂ (η₂ + 60 * u * S) i μ)
    (htest : ∃ v, μ.store.get L 0 = some v ∧ 0.9 * β < v)
    (hgood : Tape.windowFn τ sU μ.pos 2 ∉ {x : Fin 2 → ℝ | (∃ k, x k ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ (j : Fin 6) (i : Fin (n + 1)),
        ‖oneEigCentre M lam L j μ + polarDisk 0 η₂ x - d i‖ < η₁ + 40 * u * S}) :
    Writes .total I τ (oneEigRound (O := O) (Q := Q)).body
      (Env.frame [n + 1, m, q] [h, qw, (L + 5, 0), lam, (L, 0), f, (L + 1, 0), (L + 2, 0),
        (L + 3, 0), (L + 4, 0), (L + 6, 0)])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (OneEigLoopInv M H d qs h qw lam f L β η₁ η₂ (η₂ + 60 * u * S) (i + 1)) μ := by
  obtain ⟨hF, hD, hK, hFl, s, τs, hrun, hs0, hτβ, hdist, hlam, hT⟩ := hI
  obtain ⟨v, hv, hvβ⟩ := htest
  obtain rfl : v = τs i := Option.some.inj (hv.symm.trans hT)
  simp only [Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hgood
  obtain ⟨hsq, hfar⟩ := hgood
  set w := polarDisk 0 η₂ (Tape.windowFn τ sU μ.pos 2) with hw_def
  have hw : ‖w‖ ≤ η₂ := norm_polarDisk_le hη₂0 fun k => not_not.mp (hsq k)
  have hpot := hrun.norm_add_le (z := d 0) ⟨0, rfl⟩ (hdS 0) hs0
    (fun k hk => by linarith [hτβ k hk]) i le_rfl
  have hτ0 : 0 < τs i := by linarith
  have hsτ : ‖s i‖ + τs i ≤ 4.06 * S := by nlinarith
  obtain ⟨hcand, j₀, hj₀⟩ := oneEigCandidates_spec hM hu0 hu h0 h1 hβ hηr hη₂S hvβ
    (hrun.accurate i le_rfl) hsτ hw fun j i' => by
      have := hfar j i'; rwa [oneEigCentre_eq hlam hT] at this
  have hq4' : μ.store.get qw.1 (qw.2 + 4) = some η₂ := by
    rw [← hq4]; exact Store.get_of_readBlock hF.words (by omega) 0
  obtain ⟨l0, l1, l2, l3, l4, -, l6⟩ := hF.len
  refine ((oneEigRound_good hS hL h0 h1 hCmp hDisk (θ := 0.6501 * τs i) hDS hF.hh hF.hqw hF.hlam
    hF.hf hF.length l0 l1 l2 l3 l4 l6 hF.roomLam hF.matrix hq4' hT hD hK hlam
    (fun j hj => (hcand ⟨j, hj⟩).1) ⟨j₀, j₀.2, hj₀⟩
    (lt_mul_lit_sixtySix hM hu hτ0)).mono (sup_le (le_sup_left.trans le_sup_left)
      le_sup_right) ?_)
  rintro μ' hfr ⟨⟨j, hj, hlam', b, hb, hbθ, ha, hb'⟩, hD', hK'⟩
  have hfr' : μ.store.EqOff (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔
      Fp.above L) μ'.store := hfr.mono (by fp_sub)
  obtain ⟨hcj, hpj⟩ := hcand ⟨j, hj⟩
  set p := oneEigPointWord M (τs i) (oneEigDir M j) (s i) w
  have hacc : 0.9 * infDist p (Set.range d) ≤ b ∧ b ≤ 1.1 * infDist p (Set.range d) := by
    rw [infDist_range_eq_iInf]; exact ⟨ha, hb'⟩
  have hrun' := hrun.snoc (p := p) (w := p - (s i + τs i * hexDir ⟨j, hj⟩)) (τ' := b)
    (j := ⟨j, hj⟩) hpj (by ring) (by linarith) hacc
  refine ⟨hF.of_eqOff hfr', hD', hK', hfr.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_sup_left.mpr ⟨hF.disj.2.2, disj_above_inBlock_of_lt hF.hf⟩) hFl, _, _, hrun',
    by simpa using hs0, fun k hk => ?_, fun k hk => ?_, by simpa using hlam',
    by simpa using hb⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · simpa [hk.le] using hτβ k hk
    · simpa using hvβ
  · rcases Nat.le_succ_iff.mp hk with hk | rfl
    · simpa [hk] using hdist k hk
    · simp only [show ¬ i + 1 ≤ i by omega, if_false]
      exact (le_infDist (Set.range_nonempty d)).mpr fun _ ⟨i', hi'⟩ => by
        rw [← hi', dist_eq_norm, ← norm_neg, neg_sub]; exact hcj.2 i'

/-- A good start of `OneEig` starts the run: on a scalar machine with index literals, the
literal $0$ exact and an exact polar sampler on the stream `sU`, with `DistSpec` accurate on the
points of modulus at most $10\Sigma$ at distance at least $\eta_1$ from the $d_i$,
$0 \le \eta_2 \le 0.02\,\Sigma$, $\varepsilon \ge 0$ and the word $\eta_2$ at `qw[4]`: from the
frame `NLAlib.SmallEig.OneEigFrame`, if the window at the current position is in the unit square
and its polar sample is at distance at least $\eta_1 + \varepsilon$ from every $d_i$, the start
writes only the point, the flag and the scratch and ends in the loop invariant before round $0$. -/
theorem oneEigStart_step {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (h0 : M.lit 0 = 0) {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {n m q L : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {S β η₁ η₂ η ε : ℝ}
    (hDS : DistSpecAccurateOn (O := O) (Q := Q) I H d m q
      {p | ‖p‖ ≤ 10 * S ∧ ∀ i, η₁ ≤ ‖d i - p‖})
    (hη₂0 : 0 ≤ η₂) (hη₂S : η₂ ≤ 0.02 * S) (hε : 0 ≤ ε) {qs : List ℝ} (hqs : 6 ≤ qs.length)
    (hq4 : qs.getD 4 0 = η₂) {τ : Tape ℝ} {μ : Mem ℝ} {h qw lam f : ℕ × ℕ}
    (hF : OneEigFrame H qs h qw lam f L μ)
    (hgood : Tape.windowFn τ sU μ.pos 2 ∉ {x : Fin 2 → ℝ | (∃ k, x k ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ i, ‖polarDisk 0 η₂ x - d i‖ < η₁ + ε}) :
    Writes .total I τ (oneEigStart (O := O) (Q := Q)).body
      (Env.frame [n + 1, m, q] [h, qw, lam, (L, 0), f, (L + 5, 0), (L + 6, 0)])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (OneEigLoopInv M H d qs h qw lam f L β η₁ η₂ η 0) μ := by
  simp only [Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hgood
  obtain ⟨hsq, hfar⟩ := hgood
  set w := polarDisk 0 η₂ (Tape.windowFn τ sU μ.pos 2) with hw_def
  have hw : ‖w‖ ≤ η₂ := norm_polarDisk_le hη₂0 fun k => not_not.mp (hsq k)
  have hfar' : ∀ i, η₁ ≤ ‖d i - w‖ := fun i => by
    rw [← norm_neg, neg_sub]; linarith [hfar i]
  have hq4' : μ.store.get qw.1 (qw.2 + 4) = some η₂ := by
    rw [← hq4]; exact Store.get_of_readBlock hF.words (by omega) 0
  obtain ⟨l0, -, -, -, -, l5, l6⟩ := hF.len
  obtain ⟨dh, -, dlf⟩ := hF.disj
  refine (oneEigStart_good hS hL h0 hDisk hDS hF.hh hF.hqw hF.hlam hF.hf hF.length l0 l5 l6
    hF.roomLam hF.roomF (dh.mono (le_sup_left.trans le_sup_left) le_rfl) dlf hF.matrix hq4'
    ⟨by linarith, hfar'⟩).mono le_rfl ?_
  rintro μ' hfr ⟨hD', hK', hlam', ⟨t, ht, ha, hb⟩, hf'⟩
  have hacc : 0.9 * infDist w (Set.range d) ≤ t ∧ t ≤ 1.1 * infDist w (Set.range d) := by
    rw [infDist_range_eq_iInf]; exact ⟨ha, hb⟩
  refine ⟨hF.of_eqOff hfr, hD', hK', hf', fun _ => w, fun _ => t, oneEigRun_zero hacc, hw,
    fun k hk => absurd hk (Nat.not_lt_zero _), fun k _ => ?_, hlam', ht⟩
  exact (le_infDist (Set.range_nonempty d)).mpr fun _ ⟨i', hi'⟩ => by
    rw [← hi', dist_eq_norm, ← norm_neg, neg_sub]; exact hfar' i'

omit [Has ScalarOp O] [Has DiskSampleOp O] in
/-- The exit of `OneEig` after a good run: with exact comparisons, from the
loop invariant `NLAlib.SmallEig.OneEigLoopInv` before round $i$ with the estimate at most
$0.9\beta$ = `qw[5]`, the final check writes only the flag, keeps it $0$, and the point at `Lam`
is at distance between $\eta_1$ and $\beta$ from the $d_i$. -/
theorem oneEigCheck_exit {M : Machine ℝ} {I : Interp O Q ℝ} (hCmp : IsCmp id I) {n L : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} {β η₁ η₂ η : ℝ} {qs : List ℝ} (hqs : 6 ≤ qs.length)
    (hq5 : qs.getD 5 0 = 0.9 * β) {τ : Tape ℝ} {μ : Mem ℝ} {h qw lam f : ℕ × ℕ} {i : ℕ}
    (hI : OneEigLoopInv M H d qs h qw lam f L β η₁ η₂ η i μ)
    (hτ : ∀ v, μ.store.get L 0 = some v → v ≤ 0.9 * β) :
    Writes .total I τ (oneEigCheck (O := O) (Q := Q)).body
      (Env.frame [] [(qw.1, qw.2 + 5), (L, 0), f]) (Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ z : ℂ,
        μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im] ∧
        η₁ ≤ ⨅ i, ‖z - d i‖ ∧ ⨅ i, ‖z - d i‖ ≤ β) μ := by
  obtain ⟨hF, -, -, hFl, s, τs, hrun, -, -, hdist, hlam, hT⟩ := hI
  have hq5' : μ.store.get qw.1 (qw.2 + 5) = some (0.9 * β) := by
    rw [← hq5]; exact Store.get_of_readBlock hF.words (by omega) 0
  have hle := hτ _ hT
  unfold oneEigCheck
  refine writes_ite (a := [(qw.1, qw.2 + 5), (L, 0)]) rfl rfl (hCmp.test_lt hq5' hT) ?_
  rw [if_neg (by simpa using hle)]
  refine (Writes.skip ⟨hFl, s i, hlam, ?_, ?_⟩).mono bot_le fun _ _ h => h
  · rw [← infDist_range_eq_iInf]; exact hdist i le_rfl
  · rw [← infDist_range_eq_iInf]; linarith [(hrun.accurate i le_rfl).1]

open MeasureTheory in
/-- The start of `OneEig` as a probabilistic block: on a scalar machine with index literals,
the literal $0$ exact and an exact polar sampler on a stream `sU` uniform on $[0, 1]$, with
`DistSpec` accurate (`NLAlib.SmallEig.DistSpecAccurateOn`) on the points of modulus at most
$10\Sigma$ at distance at least $\eta_1$ from the $d_i$, $0 < \eta_2 \le 0.02\,\Sigma$,
$\varepsilon \ge 0$, $\eta_1 + \varepsilon \ge 0$, distinct $d_i$ at distance at least
$2(\eta_1 + \varepsilon + \eta_2)$ and the word $\eta_2$ at `qw[4]` of at least six words: from
the frame `NLAlib.SmallEig.OneEigFrame`, except with probability at most
$((\eta_1 + \varepsilon)/\eta_2)^2$, the start writes only the point, the flag and the scratch and
ends in the loop invariant `NLAlib.SmallEig.OneEigLoopInv` before round $0$. -/
theorem oneEigStart_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (h0 : M.lit 0 = 0) {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {law : ℕ → Measure ℝ} (hU : law sU = volume.restrict (Set.Icc 0 1))
    {n m q L : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {S β η₁ η₂ η ε : ℝ}
    (hDS : DistSpecAccurateOn (O := O) (Q := Q) I H d m q
      {p | ‖p‖ ≤ 10 * S ∧ ∀ i, η₁ ≤ ‖d i - p‖})
    (hη₂ : 0 < η₂) (hη₂S : η₂ ≤ 0.02 * S) (hε : 0 ≤ ε) (hη₁ε : 0 ≤ η₁ + ε)
    (hsep : ∀ i j, d i ≠ d j → 2 * (η₁ + ε + η₂) ≤ ‖d i - d j‖) {qs : List ℝ}
    (hqs : 6 ≤ qs.length) (hq4 : qs.getD 4 0 = η₂) {h qw lam f : ℕ × ℕ} :
    PWrites law I (oneEigStart (O := O) (Q := Q)).body
      (Env.frame [n + 1, m, q] [h, qw, lam, (L, 0), f, (L + 5, 0), (L + 6, 0)])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (OneEigFrame H qs h qw lam f L) (OneEigLoopInv M H d qs h qw lam f L β η₁ η₂ η 0)
      (((η₁ + ε) / η₂) ^ 2) := by
  have hB : MeasurableSet {x : Fin 2 → ℝ | (∃ k, x k ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ i, ‖polarDisk 0 η₂ x - d i‖ < η₁ + ε} := by
    have hp : Measurable (polarDisk 0 η₂) := by unfold polarDisk; fun_prop
    have e : {x : Fin 2 → ℝ | (∃ k, x k ∉ Set.Icc (0 : ℝ) 1) ∨
        ∃ i, ‖polarDisk 0 η₂ x - d i‖ < η₁ + ε} =
        (⋃ k, (fun x : Fin 2 → ℝ => x k) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ) ∪
          ⋃ i, {x | ‖polarDisk 0 η₂ x - d i‖ < η₁ + ε} := by ext x; simp
    rw [e]
    exact (MeasurableSet.iUnion fun k => measurableSet_Icc.compl.preimage
      (measurable_pi_apply k)).union (MeasurableSet.iUnion fun i =>
        measurableSet_lt (hp.sub_const _).norm measurable_const)
  refine PWrites.of_window (s := sU) (W := 2) (Bad := fun _ => {x | (∃ k, x k ∉ Set.Icc (0 : ℝ) 1)
    ∨ ∃ i, ‖polarDisk 0 η₂ x - d i‖ < η₁ + ε}) (measurable_snd hB) (fun _ _ => ?_)
    fun μ τ hF hgood => oneEigStart_step hS hL h0 hDisk hDS hη₂.le hη₂S hε hqs hq4 hF hgood
  rw [hU]
  simpa using measureReal_polarDisk_bad_le (fun _ : Fin 1 => (0 : ℂ)) d hη₂ hη₁ε hsep

open MeasureTheory in
/-- A round of `OneEig` as a probabilistic block: on a scalar machine in the standard model at
$0 \le \boldsymbol{u} \le 1/5000$ with index literals, the literals $0$ and $1$ exact, exact
comparisons and an exact polar sampler on a stream `sU` uniform on $[0, 1]$, with `DistSpec`
accurate (`NLAlib.SmallEig.DistSpecAccurateOn`) on the points of modulus at most $10\Sigma$ at
distance at least $\eta_1$ from the $d_i$, $\lvert d_i\rvert \le \Sigma$,
$0 < \eta_2 \le 0.02\,\Sigma$, $\beta > 0$, $\eta_2 + 60\boldsymbol{u}\Sigma \le 0.027\,\beta$,
$\eta_1 + 40\boldsymbol{u}\Sigma \ge 0$, distinct $d_i$ at distance at least
$2(\eta_1 + 40\boldsymbol{u}\Sigma + \eta_2)$ and the word $\eta_2$ at `qw[4]` of at least six
words: round $i$ from the loop invariant `NLAlib.SmallEig.OneEigLoopInv` with an estimate above
$0.9\beta$ ends in the invariant before round $i + 1$, writing only the point, the flag and the
scratch, except with probability at most $6((\eta_1 + 40\boldsymbol{u}\Sigma)/\eta_2)^2$. -/
theorem oneEigRound_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 5000) (hL : IsIndexLit M I)
    (h0 : M.lit 0 = 0) (h1 : M.lit 1 = 1) (hCmp : IsCmp id I) {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {law : ℕ → Measure ℝ}
    (hU : law sU = volume.restrict (Set.Icc 0 1)) {n m q L : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {S β η₁ η₂ : ℝ}
    (hDS : DistSpecAccurateOn (O := O) (Q := Q) I H d m q
      {p | ‖p‖ ≤ 10 * S ∧ ∀ i, η₁ ≤ ‖d i - p‖})
    (hdS : ∀ i, ‖d i‖ ≤ S) (hη₂ : 0 < η₂) (hη₂S : η₂ ≤ 0.02 * S) (hβ : 0 < β)
    (hηr : η₂ + 60 * u * S ≤ 0.027 * β) (hη₁ε : 0 ≤ η₁ + 40 * u * S)
    (hsep : ∀ i j, d i ≠ d j → 2 * (η₁ + 40 * u * S + η₂) ≤ ‖d i - d j‖) {qs : List ℝ}
    (hqs : 6 ≤ qs.length) (hq4 : qs.getD 4 0 = η₂) {h qw lam f : ℕ × ℕ} (i : ℕ) :
    PWrites law I (oneEigRound (O := O) (Q := Q)).body
      (Env.frame [n + 1, m, q] [h, qw, (L + 5, 0), lam, (L, 0), f, (L + 1, 0), (L + 2, 0),
        (L + 3, 0), (L + 4, 0), (L + 6, 0)])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (fun μ => OneEigLoopInv M H d qs h qw lam f L β η₁ η₂ (η₂ + 60 * u * S) i μ ∧
        ∃ v, μ.store.get L 0 = some v ∧ 0.9 * β < v)
      (OneEigLoopInv M H d qs h qw lam f L β η₁ η₂ (η₂ + 60 * u * S) (i + 1))
      (6 * ((η₁ + 40 * u * S) / η₂) ^ 2) := by
  refine PWrites.of_window (s := sU) (W := 2) (Bad := fun μ => {x | (∃ k, x k ∉ Set.Icc (0 : ℝ) 1)
    ∨ ∃ (j : Fin 6) (i : Fin (n + 1)),
      ‖oneEigCentre M lam L j μ + polarDisk 0 η₂ x - d i‖ < η₁ + 40 * u * S})
    (measurableSet_oneEigBad M lam L d η₂ _) (fun μ _ => ?_)
    fun μ τ ⟨hI, ht⟩ hgood => oneEigRound_step hS hM hu0 hu hL h0 h1 hCmp hDisk hDS hdS hη₂.le
      hη₂S hβ hηr hqs hq4 hI ht hgood
  rw [hU]
  simpa using measureReal_polarDisk_bad_le (fun j : Fin 6 => oneEigCentre M lam L j μ) d hη₂
    hη₁ε hsep

/-- The views of a frame of `NLAlib.SmallEig.oneEig` are below the end of the store. -/
theorem OneEigFrame.lt_length {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {qs : List ℝ}
    {h qw lam f : ℕ × ℕ} {L : ℕ} {μ : Mem ℝ} (hF : OneEigFrame H qs h qw lam f L μ) :
    h.1 < L ∧ qw.1 < L ∧ lam.1 < L ∧ f.1 < L ∧ μ.store.length = L + 7 :=
  ⟨hF.hh, hF.hqw, hF.hlam, hF.hf, hF.length⟩

/-- The input of `NLAlib.SmallEig.oneEig` with fresh scratch buffers above `L` is a frame. -/
theorem OneEigInput.oneEigFrame {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} {h qw lam f : ℕ × ℕ} {μ : Mem ℝ} (hin : OneEigInput H qs h qw lam f μ)
    {s₁ : Store ℝ} (hlen : s₁.length = μ.store.length + [1, 2, 2, 1, 3, 12, 2].length)
    (hlens : ∀ i (hi : i < [1, 2, 2, 1, 3, 12, 2].length),
      s₁.len (μ.store.length + i) = [1, 2, 2, 1, 3, 12, 2][i])
    (hBelow : Store.Below μ.store.length μ.store s₁) :
    OneEigFrame H qs h qw lam f μ.store.length ⟨s₁, μ.pos⟩ := by
  obtain ⟨hl, ⟨-, -, hrl, hrf, -⟩, hap, hH, hq⟩ := hin
  have hlive : h.1 < μ.store.length ∧ qw.1 < μ.store.length ∧ lam.1 < μ.store.length ∧
      f.1 < μ.store.length := by simpa [Mem.Live] using hl
  exact ⟨hlive.1, hlive.2.1, hlive.2.2.1, hlive.2.2.2, hap, by simpa using hlen,
    ⟨by simpa using hlens 0 (by simp), by simpa using hlens 1 (by simp),
      by simpa using hlens 2 (by simp), by simpa using hlens 3 (by simp),
      by simpa using hlens 4 (by simp), by simpa using hlens 5 (by simp),
      by simpa using hlens 6 (by simp)⟩,
    by simp only; rw [(hBelow lam.1 hlive.2.2.1).1]; exact hrl,
    by simp only; rw [(hBelow f.1 hlive.2.2.2).1]; exact hrf,
    hH.of_below hBelow hlive.1, hBelow.readBlock_of hlive.2.1 hq⟩

omit [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] in
/-- The test of the loop of `NLAlib.SmallEig.oneEig` before round $i$: with exact comparisons,
from the loop invariant, it compares the word $0.9\beta$ at `qw[5]` with the estimate at `Tau`. -/
theorem OneEigLoopInv.testAt_eq {M : Machine ℝ} {I : Interp O Q ℝ} (hCmp : IsCmp id I)
    {n L : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {β η₁ η₂ η : ℝ} {qs : List ℝ} (hqs : 6 ≤ qs.length) (hq5 : qs.getD 5 0 = 0.9 * β)
    {μ : Mem ℝ} {h qw lam f : ℕ × ℕ} {i : ℕ} {ρ : Env} {ds : List IExp} {ins : List Operand}
    {e : List ℕ} (hd : IExp.evalList ρ.idx ds = some e)
    (hρ : Operand.evalList ρ ins = some [(qw.1, qw.2 + 5), (L, 0)])
    (hI : OneEigLoopInv M H d qs h qw lam f L β η₁ η₂ η i μ) :
    ∃ v, μ.store.get L 0 = some v ∧
      I.testAt (Has.inj CmpTst.lt) ds ins ρ μ = some (decide (0.9 * β < v)) := by
  obtain ⟨hF, -, -, -, s, τs, -, -, -, -, -, hT⟩ := hI
  have hq5' : μ.store.get qw.1 (qw.2 + 5) = some (0.9 * β) := by
    rw [← hq5]; exact Store.get_of_readBlock hF.words (by omega) 0
  exact ⟨_, hT, (Interp.testAt_eq hd hρ).trans (hCmp.test_lt hq5' hT)⟩

omit [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] in
/-- A true test of the loop of `NLAlib.SmallEig.oneEig` reads an estimate above $0.9\beta$. -/
theorem OneEigLoopInv.lt_of_testAt {M : Machine ℝ} {I : Interp O Q ℝ} (hCmp : IsCmp id I)
    {n L : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {β η₁ η₂ η : ℝ} {qs : List ℝ} (hqs : 6 ≤ qs.length) (hq5 : qs.getD 5 0 = 0.9 * β)
    {μ : Mem ℝ} {h qw lam f : ℕ × ℕ} {i : ℕ} {ρ : Env} {ds : List IExp} {ins : List Operand}
    {e : List ℕ} (hd : IExp.evalList ρ.idx ds = some e)
    (hρ : Operand.evalList ρ ins = some [(qw.1, qw.2 + 5), (L, 0)])
    (hI : OneEigLoopInv M H d qs h qw lam f L β η₁ η₂ η i μ)
    (ht : I.testAt (Has.inj CmpTst.lt) ds ins ρ μ = some true) :
    ∃ v, μ.store.get L 0 = some v ∧ 0.9 * β < v := by
  obtain ⟨v, hv, hvt⟩ := hI.testAt_eq hCmp hqs hq5 hd hρ
  rw [hvt] at ht
  exact ⟨v, hv, by simpa using ht⟩

omit [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] in
/-- A false test of the loop of `NLAlib.SmallEig.oneEig` reads an estimate at most $0.9\beta$. -/
theorem OneEigLoopInv.le_of_testAt {M : Machine ℝ} {I : Interp O Q ℝ} (hCmp : IsCmp id I)
    {n L : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {β η₁ η₂ η : ℝ} {qs : List ℝ} (hqs : 6 ≤ qs.length) (hq5 : qs.getD 5 0 = 0.9 * β)
    {μ : Mem ℝ} {h qw lam f : ℕ × ℕ} {i : ℕ} {ρ : Env} {ds : List IExp} {ins : List Operand}
    {e : List ℕ} (hd : IExp.evalList ρ.idx ds = some e)
    (hρ : Operand.evalList ρ ins = some [(qw.1, qw.2 + 5), (L, 0)])
    (hI : OneEigLoopInv M H d qs h qw lam f L β η₁ η₂ η i μ)
    (ht : I.testAt (Has.inj CmpTst.lt) ds ins ρ μ = some false) :
    ∀ v, μ.store.get L 0 = some v → v ≤ 0.9 * β := by
  obtain ⟨v, hv, hvt⟩ := hI.testAt_eq hCmp hqs hq5 hd hρ
  rw [hvt] at ht
  intro v' hv'
  obtain rfl : v = v' := Option.some.inj (hv.symm.trans hv')
  simpa using ht

open MeasureTheory in
/-- `OneEig` as a probabilistic block, from the precision facts: on a scalar machine in the
standard model at $0 \le \boldsymbol{u} \le 1/5000$ with index literals, the literals $0$ and $1$
exact, exact comparisons, a measurable interpretation reading the tape only in its windows and an
exact polar sampler on a stream `sU` uniform on $[0, 1]$, with `DistSpec` accurate on the points
of modulus at most $10\Sigma$ at distance at least $\eta_1$ from the $d_i$, $\lvert d_i\rvert \le
\Sigma$, $0 < \eta_2 \le 0.02\,\Sigma$, $\beta > 0$,
$\eta_2 + 60\boldsymbol{u}\Sigma \le 0.027\,\beta$, $\eta_1 + 40\boldsymbol{u}\Sigma \ge 0$,
distinct $d_i$ at distance at least $2(\eta_1 + 40\boldsymbol{u}\Sigma + \eta_2)$,
$2.3 \cdot 0.66^t \cdot 2\Sigma \le 0.9\beta$ and the words `qs` with $\eta_2$ at $4$ and
$0.9\beta$ at $5$: from `NLAlib.SmallEig.OneEigInput`, except with probability at most
$(6t + 1)((\eta_1 + 40\boldsymbol{u}\Sigma)/\eta_2)^2$, the run writes only the pair and the flag,
sets the flag to $0$ and stores a point $z$ with $\eta_1 \le \min_i\lvert z - d_i\rvert \le
\beta$. -/
theorem oneEig_pwrites_of {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 5000) (hL : IsIndexLit M I)
    (h0 : M.lit 0 = 0) (h1 : M.lit 1 = 1) (hCmp : IsCmp id I) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    {n m q t : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {S β η₁ η₂ : ℝ}
    (hDS : DistSpecAccurateOn (O := O) (Q := Q) I H d m q
      {p | ‖p‖ ≤ 10 * S ∧ ∀ i, η₁ ≤ ‖d i - p‖})
    (hdS : ∀ i, ‖d i‖ ≤ S) (hη₂ : 0 < η₂) (hη₂S : η₂ ≤ 0.02 * S) (hβ : 0 < β)
    (hηr : η₂ + 60 * u * S ≤ 0.027 * β) (hη₁ε : 0 ≤ η₁ + 40 * u * S)
    (hsep : ∀ i j, d i ≠ d j → 2 * (η₁ + 40 * u * S + η₂) ≤ ‖d i - d j‖)
    (ht : 2.3 * 0.66 ^ t * (2 * S) ≤ 0.9 * β) {qs : List ℝ} (hqs : 6 ≤ qs.length)
    (hq4 : qs.getD 4 0 = η₂) (hq5 : qs.getD 5 0 = 0.9 * β) {h qw lam f : ℕ × ℕ} :
    PWrites law I (oneEig (O := O) (Q := Q)).body (Env.frame [n + 1, m, q, t] [h, qw, lam, f])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1) (OneEigInput H qs h qw lam f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ z : ℂ,
        μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im] ∧
        η₁ ≤ ⨅ i, ‖z - d i‖ ∧ ⨅ i, ‖z - d i‖ ≤ β)
      ((6 * t + 1) * ((η₁ + 40 * u * S) / η₂) ^ 2) := by
  have e : (6 * (t : ℝ) + 1) * ((η₁ + 40 * u * S) / η₂) ^ 2 = ((η₁ + 40 * u * S) / η₂) ^ 2 +
      (∑ _i ∈ Finset.range t, 6 * ((η₁ + 40 * u * S) / η₂) ^ 2 + 0) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [e]
  have hS0 : 0 ≤ S := by linarith
  have hε : 0 ≤ 40 * u * S := by positivity
  unfold oneEig
  change PWrites law I (Stmt.allocs [.const 1, .const 2, .const 2, .const 1, .const 3,
    .const 12, .const 2] _) _ _ _ _ _
  refine PWrites.allocs (ns := [1, 2, 2, 1, 3, 12, 2]) rfl
    (Pre₁ := fun L μ => OneEigFrame H qs h qw lam f L μ)
    (fun μ s₁ hin hlen hlens hBelow => hin.oneEigFrame hlen hlens hBelow) ?_ fun L => ?_
  · rintro μ ⟨hl, -⟩ s s' p hBelow ⟨hf, z, hz, hz1, hz2⟩
    have hlive : lam.1 < μ.store.length ∧ f.1 < μ.store.length := by
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hl
      exact ⟨hl.2.2.1, hl.2.2.2⟩
    exact ⟨hBelow.get_of hlive.2 hf, z, hBelow.readBlock_of hlive.1 hz, hz1, hz2⟩
  refine (PWrites.seq (F₂ := Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L ⊔
    Store.inBlock f.1 f.2 1) hI hloc (by positivity) ((oneEigStart_pwrites hS hL h0 hDisk hU
    (L := L)
    (β := β) (η := η₂ + 60 * u * S) hDS hη₂ hη₂S hε hη₁ε hsep hqs hq4).in_frame
      rfl rfl fun μ hF => ?_) ?_).mono (fun _ h => h) (by fp_sub) (fun _ h => h) le_rfl
  · obtain ⟨a, b, c, e, hlen⟩ := hF.lt_length; simp [Mem.Live, hlen]; omega
  refine (PWrites.whileFuel hI hloc (N := t) rfl (G := Store.inBlock f.1 f.2 1)
    (fun i => OneEigLoopInv M H d qs h qw lam f L β η₁ η₂ (η₂ + 60 * u * S) i)
    (fun _ => 6 * ((η₁ + 40 * u * S) / η₂) ^ 2) (fun _ _ => by positivity) le_rfl
    (fun _ h => h) ?_ ?_ ?_).mono (fun _ h => h) le_rfl (fun _ h => h) le_rfl
  · intro i _ μ hInv
    exact ⟨_, (hInv.testAt_eq hCmp hqs hq5 (by rfl) (by rfl)).choose_spec.2⟩
  · intro i _
    refine ((oneEigRound_pwrites hS hM hu0 hu hL h0 h1 hCmp hDisk hU hDS hdS hη₂ hη₂S hβ hηr
      hη₁ε hsep hqs hq4 i).in_frame rfl rfl fun μ hP => ?_).mono
      (fun μ hP => ⟨hP.1, ?_⟩) le_rfl (fun _ h => h) le_rfl
    · obtain ⟨a, b, c, e, hlen⟩ := hP.1.1.lt_length; simp [Mem.Live, hlen]; omega
    · exact hP.1.lt_of_testAt hCmp hqs hq5 (by rfl) (by rfl) hP.2
  · intro i hi
    refine PWrites.of_writes le_rfl fun μ τ hP => ((oneEigCheck_exit hCmp hqs hq5 hP.1
      fun v hv => ?_).in_frame rfl rfl ?_)
    · rcases hP.2 with rfl | hc
      · by_contra hlt
        push Not at hlt
        obtain ⟨-, -, -, -, s, τs, hrun, hs0, hτβ, -, -, hT⟩ := hP.1
        obtain rfl : v = τs i := Option.some.inj (hv.symm.trans hT)
        obtain ⟨k, hk, hkτ, -⟩ := hrun.exists_le_of_rounds (R := 2 * S)
          (Set.range_nonempty d) (by rintro z ⟨j, rfl⟩; linarith [hdS j])
          (hs0.trans (by nlinarith)) (by nlinarith) (by linarith) hβ ht
        rcases Nat.lt_or_eq_of_le hk with hk | rfl
        · linarith [hτβ k hk]
        · linarith
      · exact hP.1.le_of_testAt hCmp hqs hq5 (by rfl) (by rfl) hc v hv
    · obtain ⟨a, b, c, e, hlen⟩ := hP.1.1.lt_length; simp [Mem.Live, hlen]; omega

/-- `DistSpec` is accurate on the reach of `OneEig` (`NLAlib.SmallEig.distSpec_accuracy`):
under its hypotheses on $\mathbf{H} \ne 0$, the precision condition at the distance $\eta_1$
and the shift reach $10\Sigma$, $\Sigma \ge 0$, `DistSpec` is accurate
(`NLAlib.SmallEig.DistSpecAccurateOn`) on the points of modulus at most $10\Sigma$ at distance
at least $\eta_1$ from the $d_i$. -/
theorem distSpecAccurateOn_of {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I) (hL : IsIndexLit M I)
    (hM : StdModel u id M) (hCmp : IsCmp id I) {n m q : ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {κ p S η₁ : ℝ}
    (hH : IsUpperHessenberg H) (hH0 : H ≠ 0) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ κ) (hp : 0 < p)
    (hw : ∀ i, p ≤ lastRowWeights V i) (hS0 : 0 ≤ S) (hη₁ : 0 < η₁) (hmq : m = 2 ^ q)
    (hm : distSpecDegree κ p ≤ m) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hum : 30000 * ((m : ℝ) + 1) * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * κ)⁻¹ * (η₁ / (2 * specNorm H + 20 * S)) ^ m) :
    DistSpecAccurateOn (O := O) (Q := Q) I H d m q {p | ‖p‖ ≤ 10 * S ∧ ∀ i, η₁ ≤ ‖d i - p‖} := sorry

/-- The rounding of `OneEig` is small against the inner radius: from $480000\boldsymbol{u}\Sigma^2
\le \eta_1^2$ (the precision of `DistSpec`), $0 < \eta_1 \le \Sigma/300$ and $\eta_1 L \le
0.4\,\Sigma$ with $L \ge 0$: $2.4 \cdot 10^7\boldsymbol{u}\Sigma \le \eta_1$ and
$4000\boldsymbol{u}\Sigma L \le \eta_1$. -/
theorem rounding_le_innerRadius {u S η₁ L : ℝ} (hS : 0 < S) (hη₁ : 0 < η₁)
    (hη₁S : η₁ ≤ S / 300) (hprec : 480000 * u * S ^ 2 ≤ η₁ ^ 2) (hL0 : 0 ≤ L)
    (hη₁L : η₁ * L ≤ 0.4 * S) :
    24000000 * (u * S) ≤ η₁ ∧ 100 * (40 * u * S) * L ≤ η₁ := by
  constructor
  · have a : η₁ * η₁ ≤ η₁ * (S / 300) := mul_le_mul_of_nonneg_left hη₁S hη₁.le
    have b : S * (480000 * (u * S)) ≤ S * (η₁ / 300) := by
      have e1 : S * (480000 * (u * S)) = 480000 * u * S ^ 2 := by ring
      have e2 : S * (η₁ / 300) = η₁ * (S / 300) := by ring
      rw [e1, e2]; nlinarith
    have := le_of_mul_le_mul_left b hS
    linarith
  · have a1 : 4000 * L * (480000 * u * S ^ 2) ≤ 4000 * L * η₁ ^ 2 :=
      mul_le_mul_of_nonneg_left hprec (by positivity)
    have a3 : 4000 * η₁ * (η₁ * L) ≤ 4000 * η₁ * (0.4 * S) :=
      mul_le_mul_of_nonneg_left hη₁L (by positivity)
    have a5 : 480000 * S * (100 * (40 * u * S) * L) ≤ 480000 * S * η₁ := by
      have e1 : 480000 * S * (100 * (40 * u * S) * L) = 4000 * L * (480000 * u * S ^ 2) := by
        ring
      have e2 : 4000 * L * η₁ ^ 2 = 4000 * η₁ * (η₁ * L) := by ring
      nlinarith
    exact le_of_mul_le_mul_left a5 (by positivity)

/-- **`OneEig` finds a point near the spectrum, with the norm slightly above the parameters**
([BanksGarzaVargasSrivastava2025, Proposition 3.5], corrected: $\eta_2 = \min(\beta'/40, g/3)$ (P5),
the round cap (P6), $\log_2$ (P7), a perturbed start (B3)): on a scalar machine with the standard
model at the unit roundoff $\boldsymbol{u}$, index literals, exact natural literals up to $1$, exact
comparisons, a measurable interpretation reading the tape only in its windows and an exact polar
sampler on a stream `sU` uniform on $[0, 1]$: let $\mathbf{H}$ of order $n + 1 \ge 2$ be upper
Hessenberg, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le \kappa$, every last-row weight at least $p > 0$,
eigenvalues separated by $g > 0$, $0 < \beta' \le 0.8\,\Sigma'$, $0 < \varphi \le 1$, $m = 2^q$ at
least `NLAlib.SmallEig.distSpecDegree` $\kappa$ $p$, $t$ = `NLAlib.SmallEig.oneEigRounds` $\Sigma'$
$\beta'$, $\eta_2, \eta_1$ = `NLAlib.SmallEig.oneEigOuterRadius` $\beta'$ $g$,
`NLAlib.SmallEig.oneEigInnerRadius` $\Sigma'$ $\beta'$ $g$ $\varphi$, while $\|\mathbf{H}\|_2 \le
\Sigma''$ for some $\Sigma' \le \Sigma'' \le 1.01\,\Sigma'$, the words `qs` with $\eta_2$ at $4$ and
$0.9\beta'$ at $5$, and the precision conditions of `DistSpec` at the distance $\eta_1$ and the
shift reach $10\Sigma''$: $(n + 1)\boldsymbol{u} \le 1/2500$, $30000(m + 1)\boldsymbol{u} \le 1$ and
$300(n + 1)^2\boldsymbol{u} \le (8004\kappa)^{-1}(\eta_1/(2\|\mathbf{H}\|_2 + 20\Sigma''))^m$. Then
from `NLAlib.SmallEig.OneEigInput`, except with probability at most $\varphi$, the run writes only
the pair and the flag, sets the flag to $0$ and stores a point $z$ with $\eta_1 \le \min_i\lvert z -
d_i\rvert \le \beta'$. -/
theorem oneEig_pwrites_of_norm_le {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hNat : IsExactNatLit id M 1)
    (hCmp : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    {n m q t : ℕ} (hn : 1 ≤ n) {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {κ p g S' S'' β' φ η₁ η₂ : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ κ) (hp : 0 < p)
    (hw : ∀ i, p ≤ lastRowWeights V i) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hHS : specNorm H ≤ S'') (hS'' : S' ≤ S'') (hS''1 : S'' ≤ 1.01 * S') (hβ' : 0 < β')
    (hβ'S : β' ≤ 0.8 * S') (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hmq : m = 2 ^ q) (hm : distSpecDegree κ p ≤ m) (ht : t = oneEigRounds S' β')
    (hη₂ : η₂ = oneEigOuterRadius β' g) (hη₁ : η₁ = oneEigInnerRadius S' β' g φ)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hum : 30000 * ((m : ℝ) + 1) * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * κ)⁻¹ * (η₁ / (2 * specNorm H + 20 * S'')) ^ m)
    {qs : List ℝ} (hq4 : qs.getD 4 0 = η₂) (hq5 : qs.getD 5 0 = 0.9 * β') (hqs : 6 ≤ qs.length)
    {h qw lam f : ℕ × ℕ} :
    PWrites law I (oneEig (O := O) (Q := Q)).body (Env.frame [n + 1, m, q, t] [h, qw, lam, f])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1) (OneEigInput H qs h qw lam f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ z : ℂ,
        μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im] ∧
        η₁ ≤ ⨅ i, ‖z - d i‖ ∧ ⨅ i, ‖z - d i‖ ≤ β') φ := sorry

/-- **`OneEig` finds a point near the spectrum** ([BanksGarzaVargasSrivastava2025,
Proposition 3.5], corrected: $\eta_2 = \min(\beta'/40, g/3)$ (P5), the round cap (P6), $\log_2$
(P7), a perturbed start (B3)): on a scalar machine with the standard model at the unit roundoff
$\boldsymbol{u}$, index literals, exact natural literals up to $1$, exact comparisons,
a measurable interpretation reading the tape only in its windows and an exact polar sampler on a
stream `sU` uniform on $[0, 1]$: let $\mathbf{H}$ of order $n + 1 \ge 2$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le \kappa$, every last-row weight at least $p > 0$,
eigenvalues separated by $g > 0$, $\|\mathbf{H}\|_2 \le \Sigma'$, $0 < \beta' \le 0.8\,\Sigma'$,
$0 < \varphi \le 1$, $m = 2^q$ at least `NLAlib.SmallEig.distSpecDegree` $\kappa$ $p$, $t$ =
`NLAlib.SmallEig.oneEigRounds` $\Sigma'$ $\beta'$, $\eta_2, \eta_1$ =
`NLAlib.SmallEig.oneEigOuterRadius` $\beta'$ $g$, `NLAlib.SmallEig.oneEigInnerRadius`
$\Sigma'$ $\beta'$ $g$ $\varphi$, the words `qs` with $\eta_2$ at $4$ and $0.9\beta'$ at $5$, and
the precision conditions of `DistSpec` at the distance $\eta_1$ and the shift reach $10\Sigma'$:
$(n + 1)\boldsymbol{u} \le 1/2500$, $30000(m + 1)\boldsymbol{u} \le 1$ and
$300(n + 1)^2\boldsymbol{u} \le (8004\kappa)^{-1}(\eta_1/(2\|\mathbf{H}\|_2 + 20\Sigma'))^m$. Then
from `NLAlib.SmallEig.OneEigInput`, except with probability at most $\varphi$, the run writes only
the pair and the flag, sets the flag to $0$ and stores a point $z$ with
$\eta_1 \le \min_i\lvert z - d_i\rvert \le \beta'$. -/
theorem oneEig_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hNat : IsExactNatLit id M 1)
    (hCmp : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    {n m q t : ℕ} (hn : 1 ≤ n) {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {κ p g S' β' φ η₁ η₂ : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ κ) (hp : 0 < p)
    (hw : ∀ i, p ≤ lastRowWeights V i) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hHS : specNorm H ≤ S') (hβ' : 0 < β') (hβ'S : β' ≤ 0.8 * S') (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hmq : m = 2 ^ q) (hm : distSpecDegree κ p ≤ m) (ht : t = oneEigRounds S' β')
    (hη₂ : η₂ = oneEigOuterRadius β' g) (hη₁ : η₁ = oneEigInnerRadius S' β' g φ)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hum : 30000 * ((m : ℝ) + 1) * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * κ)⁻¹ * (η₁ / (2 * specNorm H + 20 * S')) ^ m)
    {qs : List ℝ} (hq4 : qs.getD 4 0 = η₂) (hq5 : qs.getD 5 0 = 0.9 * β') (hqs : 6 ≤ qs.length)
    {h qw lam f : ℕ × ℕ} :
    PWrites law I (oneEig (O := O) (Q := Q)).body (Env.frame [n + 1, m, q, t] [h, qw, lam, f])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1) (OneEigInput H qs h qw lam f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ z : ℂ,
        μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im] ∧
        η₁ ≤ ⨅ i, ‖z - d i‖ ∧ ⨅ i, ‖z - d i‖ ≤ β') φ :=
  oneEig_pwrites_of_norm_le hS hM hL hNat hCmp hI hloc hDisk hU hn hH hV hHV hκ hp hw hg hgap hHS
    le_rfl (by nlinarith [specNorm_nonneg H]) hβ' hβ'S hφ hφ1 hmq hm ht hη₂ hη₁ hnu hum hxu hq4 hq5
    hqs

/-- `NLAlib.SmallEig.oneEig` terminates on every tape: on a scalar machine with the literal $0$
exact, index literals, exact comparisons and an exact polar sampler, from
`NLAlib.SmallEig.OneEigInput` with any matrix and at least six words, it writes only the pair and
the flag and stores both. -/
theorem oneEig_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hzero : M.lit 0 = 0) (hL : IsIndexLit M I) (hCmp : IsCmp id I) {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I)
    {n m q t : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {qs : List ℝ} (hqs : 6 ≤ qs.length)
    {τ : Tape ℝ} {μ : Mem ℝ} {h qw lam f : ℕ × ℕ} (hin : OneEigInput H qs h qw lam f μ) :
    Writes .total I τ (oneEig (O := O) (Q := Q)).body (Env.frame [n + 1, m, q, t] [h, qw, lam, f])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ z : ℂ, μ'.store.readBlock lam.1 lam.2 2 = some [z.re, z.im]) ∧
        ∃ x, μ'.store.get f.1 f.2 = some x) μ :=
  (oneEig_writes_word hS hzero hL hCmp hDisk hqs hin).mono le_rfl fun _ _ ⟨hz, hF⟩ =>
    ⟨hz, hF.elim (fun h => ⟨_, h⟩) fun h => ⟨_, h⟩⟩

end Theorems

end NLAlib.SmallEig
