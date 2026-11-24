/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedExc
public import NLAlib.Eigensolvers.SmallEig.DistSpec
public import NLAlib.Eigensolvers.SmallEig.OneEigRounding
public import NLAlib.Matrix.QRIteration.EigenvectorWeights

/-!
# The parts of `OneEig`

The parts of the program `OneEig` ([BanksGarzaVargasSrivastava2025, §3.2]): the six directions,
one candidate point of a round with its `DistSpec` estimate, the move to the best candidate, a
round, the start at a polar disk sample of radius $\eta_2$ and the flag at
the round cap; their footprints, and their accurate forms: with `DistSpec` accurate on the
candidates (`NLAlib.SmallEig.DistSpecAccurateOn`), a round whose six candidates include one with
$1.1$ times its distance below the bar moves to a candidate with an estimate within $10\%$ of its
distance and at most that bound.

## Main definitions

* `NLAlib.SmallEig.oneEigDirections`, `NLAlib.SmallEig.oneEigPoint`,
  `NLAlib.SmallEig.oneEigMove`, `NLAlib.SmallEig.oneEigRound`, `NLAlib.SmallEig.oneEigStart`,
  `NLAlib.SmallEig.oneEigCheck`: the parts.
* `NLAlib.SmallEig.DistSpecAccurateOn`: `DistSpec` accurate on a set of points.

## Main results

* `NLAlib.SmallEig.oneEigRound_writes`, `NLAlib.SmallEig.oneEigStart_writes`: the footprints.
* `NLAlib.SmallEig.oneEigRound_good`, `NLAlib.SmallEig.oneEigStart_good`: the accurate forms.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Metric Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]

/-- **The six directions of `OneEig`**: the factor $0.66$ into `K` and the pairs
$e^{i\pi j/3}$, $j < 6$, into `D`, from the literals $1$, $0$, $1/2$, $3$, a rounded square root
and negations. The interface is `[] () → (D, K)`.
Algorithm: small-eig -/
def oneEigDirections : Stmt O Q := ops% [] () → (D, K) {
  call (Has.inj (ScalarOp.lit (66 / 100))) [] () → (K);
  call (Has.inj (ScalarOp.lit 1)) [] () → (D);
  call (Has.inj (ScalarOp.lit 0)) [] () → (D[1]);
  call (Has.inj (ScalarOp.lit (1 / 2))) [] () → (D[2]);
  call (Has.inj (ScalarOp.lit 3)) [] () → (D[3]);
  call (Has.inj ScalarOp.sqrt) [] (D[3]) → (D[3]);
  call (Has.inj ScalarOp.mul) [] (D[3], D[2]) → (D[3]);
  call (Has.inj ScalarOp.neg) [] (D[2]) → (D[4]);
  call (Has.inj ScalarOp.copy) [] (D[3]) → (D[5]);
  call (Has.inj ScalarOp.neg) [] (D) → (D[6]);
  call (Has.inj (ScalarOp.lit 0)) [] () → (D[7]);
  call (Has.inj ScalarOp.copy) [] (D[4]) → (D[8]);
  call (Has.inj ScalarOp.neg) [] (D[3]) → (D[9]);
  call (Has.inj ScalarOp.copy) [] (D[2]) → (D[10]);
  call (Has.inj ScalarOp.copy) [] (D[9]) → (D[11])
}

/-- **One candidate point of a round of `OneEig`**: the point
$s + \tau e^{i\pi j/3} + w$ into `Pt` (rounded, from the estimate `Tau`, the direction `D[2j]`,
the point `Lam` and the sample `Z`), its estimate by `NLAlib.SmallEig.distSpec` into `Tc`, and,
if the estimate is at most the best one `Bt[2]`, the point and its estimate into `Bt` and the
mark $1$ into `K[1]`. The interface is `[N, m, q, j] (H, Tau, D, Lam, Z) → (Pt, Tc, Bt, K)`.
Algorithm: small-eig -/
def oneEigPoint : Stmt O Q := ops% [N, m, q, j] (H, Tau, D, Lam, Z) → (Pt, Tc, Bt, K) {
  call (Has.inj ScalarOp.mul) [] (Tau, D[2 * j]) → (Pt);
  call (Has.inj ScalarOp.add) [] (Pt, Lam) → (Pt);
  call (Has.inj ScalarOp.add) [] (Pt, Z) → (Pt);
  call (Has.inj ScalarOp.mul) [] (Tau, D[2 * j + 1]) → (Pt[1]);
  call (Has.inj ScalarOp.add) [] (Pt[1], Lam[1]) → (Pt[1]);
  call (Has.inj ScalarOp.add) [] (Pt[1], Z[1]) → (Pt[1]);
  run (distSpec (O := O) (Q := Q)) [N, m, q] (H, Pt, Tc);
  if (Has.inj CmpTst.le) [] (Tc, Bt[2]) {
    call (Has.inj ScalarOp.copy) [] (Pt) → (Bt);
    call (Has.inj ScalarOp.copy) [] (Pt[1]) → (Bt[1]);
    call (Has.inj ScalarOp.copy) [] (Tc) → (Bt[2]);
    call (Has.inj IndexOp.lit) [1] () → (K[1])
  } else { skip }
}

/-- **The end of a round of `OneEig`**: if the mark `K[1]` is positive, the best point `Bt` and
its estimate `Bt[2]` into `Lam` and `Tau`; otherwise the flag $1$ and the estimate $0$. The
interface is `[] (Bt, K) → (Lam, Tau, Fl)`.
Algorithm: small-eig -/
def oneEigMove : Stmt O Q := ops% [] (Bt, K) → (Lam, Tau, Fl) {
  if (Has.inj CmpTst.isPos) [] (K[1]) {
    call (Has.inj ScalarOp.copy) [] (Bt) → (Lam);
    call (Has.inj ScalarOp.copy) [] (Bt[1]) → (Lam[1]);
    call (Has.inj ScalarOp.copy) [] (Bt[2]) → (Tau)
  } else {
    call (Has.inj IndexOp.lit) [1] () → (Fl);
    call (Has.inj (ScalarOp.lit 0)) [] () → (Tau)
  }
}

/-- **One round of `OneEig`**: a polar sample $w$ of the radius $\eta_2$ = `Qw[4]` into `Z`, the
bar $0.66\,\tau$ into `Bt[2]`, the mark $0$ into `K[1]`, the six candidate points
(`NLAlib.SmallEig.oneEigPoint`), and the move to the best one if one was marked, otherwise the
flag $1$ and the estimate $0$ (`NLAlib.SmallEig.oneEigMove`). The interface is
`[N, m, q] (H, Qw, D) → (Lam, Tau, Fl, Z, Pt, Tc, Bt, K)`.
Algorithm: small-eig -/
def oneEigRound : Stmt O Q :=
    ops% [N, m, q] (H, Qw, D) → (Lam, Tau, Fl, Z, Pt, Tc, Bt, K) {
  call (Has.inj DiskSampleOp.polar) [] (Qw[4]) → (Z);
  call (Has.inj ScalarOp.mul) [] (Tau, K) → (Bt[2]);
  call (Has.inj IndexOp.lit) [0] () → (K[1]);
  for j < 6 {
    run (oneEigPoint (O := O) (Q := Q)) [N, m, q, j] (H, Tau, D, Lam, Z, Pt, Tc, Bt, K)
  };
  run (oneEigMove (O := O) (Q := Q)) [] (Bt, K, Lam, Tau, Fl)
}

/-- **The start of `OneEig`**: the six directions (`NLAlib.SmallEig.oneEigDirections`) into `D`
and `K`, a polar sample of the radius $\eta_2$ = `Qw[4]` into `Lam`, its estimate by
`NLAlib.SmallEig.distSpec` into `Tau`, and the flag $0$. The interface is
`[N, m, q] (H, Qw) → (Lam, Tau, Fl, D, K)`.
Algorithm: small-eig -/
def oneEigStart : Stmt O Q := ops% [N, m, q] (H, Qw) → (Lam, Tau, Fl, D, K) {
  run (oneEigDirections (O := O) (Q := Q)) [] (D, K);
  call (Has.inj DiskSampleOp.polar) [] (Qw[4]) → (Lam);
  run (distSpec (O := O) (Q := Q)) [N, m, q] (H, Lam, Tau);
  call (Has.inj IndexOp.lit) [0] () → (Fl)
}

/-- **The flag at the cap of `OneEig`**: if $0.9\beta'$ = `Th` $< \tau$ = `Tau`, the flag $1$
into `Fl`. The interface is `[] (Th, Tau) → (Fl)`.
Algorithm: small-eig -/
def oneEigCheck : Stmt O Q := ops% [] (Th, Tau) → (Fl) {
  if (Has.inj CmpTst.lt) [] (Th, Tau) {
    call (Has.inj IndexOp.lit) [1] () → (Fl)
  } else { skip }
}

end Program

/-- The scratch buffers from `L` on are apart from a block below `L`. -/
theorem disj_above_inBlock_of_lt {L b o n : ℕ} (hb : b < L) :
    Fp.Disj (Fp.above L) (Store.inBlock b o n) := fun _ _ ha hb' => by
  obtain ⟨rfl, -, -⟩ := hb'
  exact absurd ha (Nat.not_le_of_gt hb)

/-- The flag of `NLAlib.SmallEig.oneEig` at `f` is the literal $0$ or $1$. -/
def OneEigFlag (M : Machine ℝ) (f : ℕ × ℕ) (s : Store ℝ) : Prop :=
  s.get f.1 f.2 = some (M.lit 0) ∨ s.get f.1 f.2 = some (M.lit 1)

/-- The flag survives writes apart from it. -/
theorem OneEigFlag.of_eqOff {M : Machine ℝ} {f : ℕ × ℕ} {s s' : Store ℝ} {F : Fp}
    (h : OneEigFlag M f s) (hfr : s.EqOff F s') (hd : Fp.Disj F (Store.inBlock f.1 f.2 1)) :
    OneEigFlag M f s' :=
  h.imp (hfr.keep (Store.readsOnly_get _ _ _) hd) (hfr.keep (Store.readsOnly_get _ _ _) hd)

/-- The words a round of `NLAlib.SmallEig.oneEig` reads with the scratch from `L`: the estimate
`Tau`, the point `Lam`, the factor `K[0]` and the twelve direction words `D`. -/
def oneEigCells (L : ℕ) (lam : ℕ × ℕ) : List (ℕ × ℕ) :=
  [(L, 0), lam, (lam.1, lam.2 + 1), (L + 6, 0)] ++ (List.range 12).map fun i => (L + 5, i)

/-- The cells of `NLAlib.SmallEig.oneEigCells` lie in `Lam` (below `L`) or in the buffers `L`,
`L + 5` and `K[0]`, off a footprint that misses them. -/
theorem not_mem_oneEigCells {L : ℕ} {lam : ℕ × ℕ} {F : Fp} (hlam : ¬ F lam.1 lam.2)
    (hlam1 : ¬ F lam.1 (lam.2 + 1)) (hT : ¬ F L 0) (hK : ¬ F (L + 6) 0)
    (hD : ∀ i < 12, ¬ F (L + 5) i) : ∀ c ∈ oneEigCells L lam, ¬ F c.1 c.2 := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    exacts [hT, hlam, hlam1, hK]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    exact hD i (List.mem_range.mp hi)

/-- The cells of `NLAlib.SmallEig.oneEigCells` and the sample `Z` (at `L + 1`) keep their words
across writes to the buffers from `L + 2` on other than `D` and `K[0]`. -/
theorem holdsWords_oneEigScratch_of_eqOff {s s' : Store ℝ} {F : Fp} {L : ℕ} {lam : ℕ × ℕ}
    (hlam : lam.1 < L) (h : HoldsWords s ((L + 1, 0) :: (L + 1, 1) :: oneEigCells L lam))
    (hfr : s.EqOff F s') (hF : ∀ b i, F b i → L + 2 ≤ b ∧ b ≠ L + 5 ∧ (b = L + 6 → 1 ≤ i)) :
    HoldsWords s' ((L + 1, 0) :: (L + 1, 1) :: oneEigCells L lam) := by
  refine h.of_eqOff hfr fun c hc hc' => ?_
  have hc'' := hF _ _ hc'
  rcases List.mem_cons.mp hc with rfl | hc
  · dsimp only at hc''; omega
  rcases List.mem_cons.mp hc with rfl | hc
  · dsimp only at hc''; omega
  exact not_mem_oneEigCells (F := fun b i => L + 2 ≤ b ∧ b ≠ L + 5 ∧ (b = L + 6 → 1 ≤ i))
    (by omega) (by omega) (by omega) (by omega) (fun i _ => by omega) c hc hc''

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] in
/-- A polar sample stores a pair: on an exact polar disk sampler, from a radius word at `rd` and
room for two words at `z`, the call writes only those two words and stores a pair there.
The rule for one call of the operation. -/
theorem polar_writes_pair {I : Interp O Q ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {τ : Tape ℝ} {μ : Mem ℝ} {ρ : Env} {ins outs : List Operand} {rd z : ℕ × ℕ} {R : ℝ}
    (ha : Operand.evalList ρ ins = some [rd]) (hb : Operand.evalList ρ outs = some [z])
    (hrd : μ.store.get rd.1 rd.2 = some R) (hl : μ.Live [rd, z])
    (hz : z.2 + 2 ≤ μ.store.len z.1) :
    Writes .total I τ (.call (Has.inj DiskSampleOp.polar) [] ins outs) ρ
      (Store.inBlock z.1 z.2 2)
      (fun μ' => ∃ w : ℂ, μ'.store.readBlock z.1 z.2 2 = some [w.re, w.im]) μ := by
  have hread : μ.readBlocks [rd] [1] = some [[R]] := by
    simp [Mem.readBlocks, Store.readBlock, hrd]
  refine (writes_call (R := polarDiskRel sU) hDisk (d := []) (a := [rd]) (b := [z])
    (k := 2) (ls := [2]) rfl ha hb rfl rfl rfl trivial (by simp [Fp.Apart])
    (fun _ => ⟨by simpa using hl, ⟨_, hread, trivial⟩, by simp [Mem.Room]; omega⟩)).mono
    (by simp) ?_
  rintro μ' - ⟨-, xs, ys, hr, hys, hrel⟩
  have hys' := hrel R (Option.some.inj (hr.symm.trans hread))
  subst hys'
  obtain ⟨y, hy, hyy⟩ := Option.bind_eq_some_iff.mp (by simpa [Mem.readBlocks] using hys)
  simp only [Option.some.injEq, List.cons.injEq, and_true] at hyy
  exact ⟨_, by rw [hy, hyy]⟩

omit [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] in
/-- `NLAlib.SmallEig.oneEigDirections` on a scalar machine: with room for twelve words at `d`
and one at `k` in another buffer, it writes only those words and stores words there.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem oneEigDirections_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {μ : Mem ℝ} {L : ℕ} (hlen : L + 7 ≤ μ.store.length)
    (h5 : μ.store.len (L + 5) = 12) (h6 : μ.store.len (L + 6) = 2) :
    Writes .total I τ (oneEigDirections (O := O) (Q := Q))
      (Env.frame [] [(L + 5, 0), (L + 6, 0)])
      (Store.inBlock (L + 5) 0 12 ⊔ Store.inBlock (L + 6) 0 1)
      (fun μ' => HoldsWords μ'.store ((L + 6, 0) :: (List.range 12).map fun i => (L + 5, i)))
      μ := by
  unfold oneEigDirections
  step (hS (.lit (66 / 100))) as μ₁ hfr₁ ⟨-, k₀, hk₀, -⟩
  step (hS (.lit 1)) as μ₂ hfr₂ ⟨-, d₀, hd₀, -⟩
  step (hS (.lit 0)) as μ₃ hfr₃ ⟨-, d₁, hd₁, -⟩
  step (hS (.lit (1 / 2))) as μ₄ hfr₄ ⟨-, d₂, hd₂, -⟩
  step (hS (.lit 3)) as μ₅ hfr₅ ⟨-, d₃, hd₃, -⟩
  step (hS .sqrt) as μ₆ hfr₆ ⟨-, d₃', hd₃', -⟩
  step (hS .mul) as μ₇ hfr₇ ⟨-, d₃'', hd₃'', -⟩
  step (hS .neg) as μ₈ hfr₈ ⟨-, d₄, hd₄, -⟩
  step (hS .copy) as μ₉ hfr₉ ⟨-, d₅, hd₅, -⟩
  step (hS .neg) as μ₁₀ hfr₁₀ ⟨-, d₆, hd₆, -⟩
  step (hS (.lit 0)) as μ₁₁ hfr₁₁ ⟨-, d₇, hd₇, -⟩
  step (hS .copy) as μ₁₂ hfr₁₂ ⟨-, d₈, hd₈, -⟩
  step (hS .neg) as μ₁₃ hfr₁₃ ⟨-, d₉, hd₉, -⟩
  step (hS .copy) as μ₁₄ hfr₁₄ ⟨-, d₁₀, hd₁₀, -⟩
  step (hS .copy) as μ₁₅ hfr₁₅ ⟨-, d₁₁, hd₁₁, -⟩
  intro c hc
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
  rcases hc with rfl | ⟨i, hi, rfl⟩
  · exact ⟨_, by kept⟩
  interval_cases i <;> exact ⟨_, by kept⟩

omit [Has DiskSampleOp O] in
/-- One candidate point (`NLAlib.SmallEig.oneEigPoint`) with the scratch of
`NLAlib.SmallEig.oneEig` from `L`: on a scalar machine with the literal $0$ exact, index literals
and exact comparisons, from any matrix of order $n + 1$ at `h`, words at the cells read and the
mark `K[1]` $0$ or the best point stored, it writes only `Pt`, `Tc`, `Bt` and `K[1]`, keeps the
tape position, and keeps the best estimate and the mark stored.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem oneEigPoint_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hzero : M.lit 0 = 0) (hL : IsIndexLit M I) (hCmp : IsCmp id I) {n m q j L : ℕ}
    (hNat : IsExactNatLit id M n)
    (hj : j < 6) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    {h lam : ℕ × ℕ} (hh : h.1 < L) (hlam : lam.1 < L) (hlen : μ.store.length = L + 7)
    (h2 : μ.store.len (L + 2) = 2) (h3 : μ.store.len (L + 3) = 1)
    (h4 : μ.store.len (L + 4) = 3) (h6 : μ.store.len (L + 6) = 2)
    (hH : HoldsMatrix h H μ.store)
    (hw : HoldsWords μ.store ((L + 1, 0) :: (L + 1, 1) :: oneEigCells L lam))
    (hb2 : ∃ v, μ.store.get (L + 4) 2 = some v)
    (hK : μ.store.get (L + 6) 1 = some 0 ∨
      HoldsWords μ.store [(L + 6, 1), (L + 4, 2), (L + 4, 1), (L + 4, 0)]) :
    Writes .total I τ (oneEigPoint (O := O) (Q := Q))
      (Env.frame [n + 1, m, q, j] [h, (L, 0), (L + 5, 0), lam, (L + 1, 0), (L + 2, 0),
        (L + 3, 0), (L + 4, 0), (L + 6, 0)])
      (Store.inBlock (L + 2) 0 2 ⊔ Store.inBlock (L + 3) 0 1 ⊔ Store.inBlock (L + 4) 0 3 ⊔
        Store.inBlock (L + 6) 1 1)
      (fun μ' => μ'.pos = μ.pos ∧ (∃ v, μ'.store.get (L + 4) 2 = some v) ∧
        (μ'.store.get (L + 6) 1 = some 0 ∨
          HoldsWords μ'.store [(L + 6, 1), (L + 4, 2), (L + 4, 1), (L + 4, 0)])) μ := by
  have hm : ∀ {c}, c ∈ oneEigCells L lam →
      c ∈ (L + 1, 0) :: (L + 1, 1) :: oneEigCells L lam := fun hc =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)
  obtain ⟨vT, hT⟩ := hw.get (b := L) (o := 0) (hm (by simp [oneEigCells]))
  obtain ⟨vD₀, hD₀⟩ := hw.get (b := L + 5) (o := 2 * j) (hm (List.mem_append_right _
    (List.mem_map.mpr ⟨2 * j, List.mem_range.mpr (by omega), rfl⟩)))
  obtain ⟨vD₁, hD₁⟩ := hw.get (b := L + 5) (o := 2 * j + 1) (hm (List.mem_append_right _
    (List.mem_map.mpr ⟨2 * j + 1, List.mem_range.mpr (by omega), rfl⟩)))
  obtain ⟨vL₀, hL₀⟩ := hw.get (b := lam.1) (o := lam.2) (hm (by simp [oneEigCells]))
  obtain ⟨vL₁, hL₁⟩ := hw.get (b := lam.1) (o := lam.2 + 1) (hm (by simp [oneEigCells]))
  obtain ⟨vZ₀, hZ₀⟩ := hw.get (b := L + 1) (o := 0) (by simp)
  obtain ⟨vZ₁, hZ₁⟩ := hw.get (b := L + 1) (o := 1) (by simp)
  obtain ⟨vB, hB⟩ := hb2
  have hD₀' : μ.store.get (L + 5) (0 + 2 * j) = some vD₀ := by rwa [Nat.zero_add]
  have hD₁' : μ.store.get (L + 5) (0 + (2 * j + 1)) = some vD₁ := by rwa [Nat.zero_add]
  unfold oneEigPoint
  step (hS .mul) as μ₁ hfr₁ ⟨hp₁, a₁, ha₁, -⟩
  step (hS .add) as μ₂ hfr₂ ⟨hp₂, a₂, ha₂, -⟩
  step (hS .add) as μ₃ hfr₃ ⟨hp₃, a₃, ha₃, -⟩
  step (hS .mul) as μ₄ hfr₄ ⟨hp₄, b₁, hb₁, -⟩
  step (hS .add) as μ₅ hfr₅ ⟨hp₅, b₂, hb₂, -⟩
  step (hS .add) as μ₆ hfr₆ ⟨hp₆, b₃, hb₃, -⟩
  have hsp : μ₆.store.readBlock (L + 2) 0 2 = some [(⟨a₃, b₃⟩ : ℂ).re, (⟨a₃, b₃⟩ : ℂ).im] :=
    Store.readBlock_add (n := 1) (k := 1) (Store.readBlock_one_of_get (by kept))
      (Store.readBlock_one_of_get (by kept))
  have hH₆ : HoldsMatrix h H μ₆.store := by unfold HoldsMatrix at hH ⊢; kept
  refine (distSpec_terminates (τ := τ) (μ := μ₆) (h := h) (sp := (L + 2, 0))
    (tau := (L + 3, 0)) (m := m) (q := q) hS hL hzero hCmp hNat le_rfl (by room) hH₆ hsp
    (by room)).frame_seq_le rfl rfl (by room) (by fp_sub) ?_
  rintro μ₇ hfr₇ ⟨hp₇, t₇, ht₇⟩
  refine writes_ite (a := [(L + 3, 0), (L + 4, 2)]) rfl rfl (hCmp.test_le ht₇ (by kept)) ?_
  split_ifs
  · step (hS .copy) as μ₈ hfr₈ ⟨hp₈, c₁, hc₁, -⟩
    step (hS .copy) as μ₉ hfr₉ ⟨hp₉, c₂, hc₂, -⟩
    step (hS .copy) as μ₁₀ hfr₁₀ ⟨hp₁₀, c₃, hc₃, -⟩
    refine (writes_indexLit hL rfl rfl (by room)).mono (by fp_sub) ?_
    rintro μ₁₁ hfr₁₁ ⟨hp₁₁, hk₁₁⟩
    refine ⟨by simp only [hp₁₁, hp₁₀, hp₉, hp₈, hp₇, hp₆, hp₅, hp₄, hp₃, hp₂, hp₁],
      ⟨_, by kept⟩, Or.inr fun c hc => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    exacts [⟨_, hk₁₁⟩, ⟨_, by kept⟩, ⟨_, by kept⟩, ⟨_, by kept⟩]
  · refine (Writes.skip ⟨by simp only [hp₇, hp₆, hp₅, hp₄, hp₃, hp₂, hp₁],
      ⟨_, by kept⟩, ?_⟩).mono bot_le fun _ _ h => h
    rcases hK with hK | hK
    · exact Or.inl (by kept)
    · obtain ⟨x₀, hx₀⟩ := hK.get (b := L + 6) (o := 1) (by simp)
      obtain ⟨x₁, hx₁⟩ := hK.get (b := L + 4) (o := 2) (by simp)
      obtain ⟨x₂, hx₂⟩ := hK.get (b := L + 4) (o := 1) (by simp)
      obtain ⟨x₃, hx₃⟩ := hK.get (b := L + 4) (o := 0) (by simp)
      refine Or.inr fun c hc => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨_, by kept⟩

omit [Has DiskSampleOp O] in
/-- The end of a round (`NLAlib.SmallEig.oneEigMove`) with the scratch of
`NLAlib.SmallEig.oneEig` from `L`: on a scalar machine with index literals and exact
comparisons, from the mark `K[1]` $0$ or the best point stored, a pair at `lam` and a
flag $0$ or $1$ at `f` apart from it, it writes only `lam`, `Tau` and `f`, and stores words in
`Tau` and `lam` and a flag $0$ or $1$.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem oneEigMove_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hCmp : IsCmp id I) {L : ℕ} {τ : Tape ℝ}
    {μ : Mem ℝ} {lam f : ℕ × ℕ} (hlam : lam.1 < L) (hf : f.1 < L)
    (hlen : μ.store.length = L + 7) (h0 : μ.store.len L = 1)
    (hroom : lam.2 + 2 ≤ μ.store.len lam.1) (hroomf : f.2 < μ.store.len f.1)
    (hlf : Fp.Disj (Store.inBlock lam.1 lam.2 2) (Store.inBlock f.1 f.2 1))
    (hw : HoldsWords μ.store [lam, (lam.1, lam.2 + 1)])
    (hK : μ.store.get (L + 6) 1 = some 0 ∨
      HoldsWords μ.store [(L + 6, 1), (L + 4, 2), (L + 4, 1), (L + 4, 0)])
    (hF : OneEigFlag M f μ.store) :
    Writes .total I τ (oneEigMove (O := O) (Q := Q))
      (Env.frame [] [(L + 4, 0), (L + 6, 0), lam, (L, 0), f])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock L 0 1 ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => HoldsWords μ'.store [(L, 0), lam, (lam.1, lam.2 + 1)] ∧
        OneEigFlag M f μ'.store) μ := by
  obtain ⟨k, hk, hk'⟩ : ∃ k, μ.store.get (L + 6) 1 = some k ∧
      (k = 0 ∨ HoldsWords μ.store [(L + 4, 2), (L + 4, 1), (L + 4, 0)]) := by
    rcases hK with hK | hK
    · exact ⟨0, hK, Or.inl rfl⟩
    · obtain ⟨k, hk⟩ := hK.get (b := L + 6) (o := 1) (by simp)
      exact ⟨k, hk, Or.inr (hK.mono fun c hc => List.mem_cons_of_mem _ hc)⟩
  obtain ⟨x₀, hx₀⟩ := hw.get (b := lam.1) (o := lam.2) (by simp)
  unfold oneEigMove
  refine writes_ite (a := [(L + 6, 1)]) rfl rfl (hCmp.test_isPos hk) ?_
  split_ifs with hpos
  · have hw' : HoldsWords μ.store [(L + 4, 2), (L + 4, 1), (L + 4, 0)] :=
      hk'.resolve_left (by rintro rfl; simp at hpos)
    obtain ⟨y₀, hy₀⟩ := hw'.get (b := L + 4) (o := 0) (by simp)
    obtain ⟨y₁, hy₁⟩ := hw'.get (b := L + 4) (o := 1) (by simp)
    obtain ⟨y₂, hy₂⟩ := hw'.get (b := L + 4) (o := 2) (by simp)
    step (hS .copy) as μ₁ hfr₁ ⟨-, c₁, hc₁, -⟩
    step (hS .copy) as μ₂ hfr₂ ⟨-, c₂, hc₂, -⟩
    step (hS .copy) as μ₃ hfr₃ ⟨-, c₃, hc₃, -⟩
    refine ⟨fun c hc => ?_, ((hF.of_eqOff hfr₁ (hlf.mono (by fp_sub) le_rfl)).of_eqOff hfr₂
      (hlf.mono (by fp_sub) le_rfl)).of_eqOff hfr₃ (Fp.disj_inBlock_of_ne (by omega))⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact ⟨_, by kept⟩
  · refine (writes_indexLit (z := f) hL rfl rfl hroomf).seq_le (by fp_sub) ?_
    rintro μ₁ hfr₁ ⟨-, hf₁⟩
    step (hS (.lit 0)) as μ₂ hfr₂ ⟨-, t₂, ht₂, -⟩
    refine ⟨((hw.cons_of_eqOff le_rfl hfr₁ hf₁).cons_of_eqOff le_rfl hfr₂ ht₂).mono ?_,
      Or.inr (hfr₂.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_ne (by omega))
        (by simpa using hf₁))⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl <;> simp

omit [Has ScalarOp O] [Has DiskSampleOp O] in
/-- `NLAlib.SmallEig.oneEigCheck` with index literals and exact comparisons: from words at `th`
and `tau` and a flag $0$ or $1$ at `f`, it writes only the flag and keeps it $0$ or $1$.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem oneEigCheck_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hL : IsIndexLit M I)
    (hCmp : IsCmp id I) {τ : Tape ℝ} {μ : Mem ℝ} {th tau f : ℕ × ℕ} {a b : ℝ}
    (hth : μ.store.get th.1 th.2 = some a) (htau : μ.store.get tau.1 tau.2 = some b)
    (hroomf : f.2 < μ.store.len f.1) (hF : OneEigFlag M f μ.store) :
    Writes .total I τ (oneEigCheck (O := O) (Q := Q)) (Env.frame [] [th, tau, f])
      (Store.inBlock f.1 f.2 1) (fun μ' => OneEigFlag M f μ'.store) μ := by
  unfold oneEigCheck
  refine writes_ite (a := [th, tau]) rfl rfl (hCmp.test_lt hth htau) ?_
  split_ifs
  · refine (writes_indexLit (z := f) hL rfl rfl hroomf).mono le_rfl ?_
    rintro μ' - ⟨-, hf'⟩
    exact Or.inr (by simpa using hf')
  · exact (Writes.skip hF).mono bot_le fun _ _ h => h

/-- The frame of a round of `NLAlib.SmallEig.oneEig` with the scratch from `L` misses the factor
`K[0]` and the directions `D`. -/
theorem holdsWords_directions_of_eqOff {s s' : Store ℝ} {F : Fp} {L : ℕ}
    (h : HoldsWords s ((L + 6, 0) :: (List.range 12).map fun i => (L + 5, i)))
    (hfr : s.EqOff F s') (hF : ∀ i, ¬ F (L + 6) 0 ∧ ¬ F (L + 5) i) :
    HoldsWords s' ((L + 6, 0) :: (List.range 12).map fun i => (L + 5, i)) := by
  refine h.of_eqOff hfr fun c hc => ?_
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
  rcases hc with rfl | ⟨i, -, rfl⟩
  exacts [(hF 0).1, (hF i).2]

/-- The words of `NLAlib.SmallEig.oneEigCells` from those of `Tau` and `Lam` and those of `K[0]`
and `D`. -/
theorem holdsWords_oneEigCells {s : Store ℝ} {L : ℕ} {lam : ℕ × ℕ}
    (h₁ : HoldsWords s [(L, 0), lam, (lam.1, lam.2 + 1)])
    (h₂ : HoldsWords s ((L + 6, 0) :: (List.range 12).map fun i => (L + 5, i))) :
    HoldsWords s (oneEigCells L lam) := by
  intro c hc
  simp only [oneEigCells, List.cons_append, List.mem_cons] at hc
  rcases hc with rfl | rfl | rfl | hc
  exacts [h₁ _ (by simp), h₁ _ (by simp), h₁ _ (by simp), h₂ _ (List.mem_cons.mpr hc)]

/-- One round of `NLAlib.SmallEig.oneEig` (`NLAlib.SmallEig.oneEigRound`) with the scratch from
`L` (the buffers `Tau`, `Z`, `Pt`, `Tc`, `Bt`, `D`, `K` at `L`, …, `L + 6`): on a scalar machine
with the literal $0$ exact, index literals, exact comparisons and an exact polar sampler, from any
matrix of order $n + 1$ at `h`, at least six words at `qw`, words at
`NLAlib.SmallEig.oneEigCells` and a flag $0$ or $1$ at `f` apart from `lam`, it writes only `lam`,
`f` and the scratch, and keeps the words and the flag.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem oneEigRound_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hzero : M.lit 0 = 0) (hL : IsIndexLit M I) (hCmp : IsCmp id I) {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {n m q L : ℕ} (hNat : IsExactNatLit id M n)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {qs : List ℝ} (hqs : 6 ≤ qs.length) {τ : Tape ℝ} {μ : Mem ℝ} {h qw lam f : ℕ × ℕ}
    (hh : h.1 < L) (hqw : qw.1 < L) (hlam : lam.1 < L) (hf : f.1 < L)
    (hlen : μ.store.length = L + 7) (h0 : μ.store.len L = 1) (h1 : μ.store.len (L + 1) = 2)
    (h2 : μ.store.len (L + 2) = 2) (h3 : μ.store.len (L + 3) = 1)
    (h4 : μ.store.len (L + 4) = 3) (h6 : μ.store.len (L + 6) = 2)
    (hroom : lam.2 + 2 ≤ μ.store.len lam.1) (hroomf : f.2 < μ.store.len f.1)
    (hlf : Fp.Disj (Store.inBlock lam.1 lam.2 2) (Store.inBlock f.1 f.2 1))
    (hH : HoldsMatrix h H μ.store) (hq : μ.store.readBlock qw.1 qw.2 qs.length = some qs)
    (hw : HoldsWords μ.store (oneEigCells L lam)) (hF : OneEigFlag M f μ.store) :
    Writes .total I τ (oneEigRound (O := O) (Q := Q))
      (Env.frame [n + 1, m, q] [h, qw, (L + 5, 0), lam, (L, 0), f, (L + 1, 0), (L + 2, 0),
        (L + 3, 0), (L + 4, 0), (L + 6, 0)])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (fun μ' => HoldsWords μ'.store (oneEigCells L lam) ∧ OneEigFlag M f μ'.store) μ := by
  have hq4 : μ.store.get qw.1 (qw.2 + 4) = some (qs.getD 4 0) :=
    Store.get_of_readBlock hq (by omega) 0
  obtain ⟨vT, hT⟩ := hw.get (b := L) (o := 0) (by simp [oneEigCells])
  obtain ⟨vK, hK⟩ := hw.get (b := L + 6) (o := 0) (by simp [oneEigCells])
  have hKD : HoldsWords μ.store ((L + 6, 0) :: (List.range 12).map fun i => (L + 5, i)) :=
    hw.mono fun c hc => by simp only [oneEigCells, List.cons_append, List.mem_cons] at hc ⊢; tauto
  unfold oneEigRound
  refine (polar_writes_pair hDisk (rd := (qw.1, qw.2 + 4)) (z := (L + 1, 0)) rfl rfl hq4
    (by simp [Mem.Live]; omega) (by simp [h1])).seq_le (Fp.inBlock_le_sup_above (by omega)) ?_
  rintro μ₁ hfr₁ ⟨w, hw₁⟩
  step (hS .mul) as μ₂ hfr₂ ⟨-, b₂, hb₂, -⟩
  refine (writes_indexLit (z := (L + 6, 1)) hL rfl rfl (by room)).seq_le
    (Fp.inBlock_le_sup_above (by omega)) ?_
  rintro μ₃ hfr₃ ⟨-, hk₃⟩
  have hfrA := (hfr₁.trans' hfr₂).trans' hfr₃
  have hW₃ : HoldsWords μ₃.store ((L + 1, 0) :: (L + 1, 1) :: oneEigCells L lam) :=
    holdsWords_oneEigScratch_of_eqOff hlam (holdsWords_oneEigScratch_of_eqOff hlam
      (hw.pair_of_eqOff le_rfl hfr₁ hw₁) hfr₂ fun _ _ h => by simp only [fpNF] at h; omega)
      hfr₃ fun _ _ h => by simp only [fpNF] at h; omega
  refine (writes_loop (N := 6) rfl (fun _ => Store.inBlock (L + 2) 0 2 ⊔
      Store.inBlock (L + 3) 0 1 ⊔ Store.inBlock (L + 4) 0 3 ⊔ Store.inBlock (L + 6) 1 1)
    (fun _ _ => le_rfl) (fun _ μ' => (∃ v, μ'.store.get (L + 4) 2 = some v) ∧
      (μ'.store.get (L + 6) 1 = some 0 ∨
        HoldsWords μ'.store [(L + 6, 1), (L + 4, 2), (L + 4, 1), (L + 4, 0)]))
    ⟨⟨b₂, (hfr₃.get_eq (by simp only [fpNF]; omega)).trans hb₂⟩,
      Or.inl (by rw [hk₃, Nat.cast_zero, hzero])⟩ ?_).seq_le (by fp_sub) ?_
  · rintro j hj μ' hfr' ⟨hb', hK'⟩
    refine ((oneEigPoint_writes hS hzero hL hCmp hNat (j := j) (L := L) hj hh hlam
      (by rw [hfr'.length_eq, hfrA.length_eq, hlen])
      (by rw [hfr'.len_eq, hfrA.len_eq, h2]) (by rw [hfr'.len_eq, hfrA.len_eq, h3])
      (by rw [hfr'.len_eq, hfrA.len_eq, h4]) (by rw [hfr'.len_eq, hfrA.len_eq, h6])
      ((hH.of_eqOff hfrA fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega).of_eqOff hfr'
        fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega)
      (holdsWords_oneEigScratch_of_eqOff hlam hW₃ hfr' fun _ _ h => by
        simp only [fpNF] at h; omega)
      hb' hK').in_frame rfl rfl
      (by simp [Mem.Live, hfr'.length_eq, hfrA.length_eq, hlen]; omega)).mono le_rfl
      fun _ _ h => h.2
  rintro μ₄ hfr₄ ⟨-, hK₄⟩
  have hfrB := hfrA.trans' hfr₄
  have hw₄ : HoldsWords μ₄.store [lam, (lam.1, lam.2 + 1)] := by
    refine (hw.mono fun c hc => ?_).of_eqOff hfrB fun c hc hc' => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [oneEigCells]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      simp only [fpNF] at hc'
      rcases hc with rfl | rfl <;> omega
  refine ((oneEigMove_writes hS hL hCmp hlam hf (by rw [hfrB.length_eq, hlen])
    (by rw [hfrB.len_eq, h0]) (by rw [hfrB.len_eq]; exact hroom)
    (by rw [hfrB.len_eq]; exact hroomf) hlf hw₄ hK₄
    (hF.of_eqOff hfrB fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega)).in_frame rfl
    rfl (by simp [Mem.Live, hfrB.length_eq, hlen]; omega)).mono (by fp_sub) ?_
  rintro μ₅ hfr₅ ⟨hm, hF₅⟩
  refine ⟨holdsWords_oneEigCells hm (holdsWords_directions_of_eqOff
    (holdsWords_directions_of_eqOff hKD hfrB fun i => ?_) hfr₅ fun i => ?_), hF₅⟩
  all_goals simp only [fpNF]; omega

/-- The start of `NLAlib.SmallEig.oneEig` (`NLAlib.SmallEig.oneEigStart`) with the scratch from
`L`: on a scalar machine with the literal $0$ exact, index literals, exact comparisons and an
exact polar sampler, from any matrix of order $n + 1$ at `h` apart from `lam` and at least five
words at `qw`, it writes only `lam`, `f` and the scratch, and stores words at
`NLAlib.SmallEig.oneEigCells` and the flag $0$.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem oneEigStart_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hzero : M.lit 0 = 0) (hL : IsIndexLit M I) (hCmp : IsCmp id I) {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {n m q L : ℕ} (hNat : IsExactNatLit id M n)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {τ : Tape ℝ} {μ : Mem ℝ} {h qw lam f : ℕ × ℕ} {r : ℝ}
    (hh : h.1 < L) (hqw : qw.1 < L) (hlam : lam.1 < L)
    (hlen : μ.store.length = L + 7) (h0 : μ.store.len L = 1) (h5 : μ.store.len (L + 5) = 12)
    (h6 : μ.store.len (L + 6) = 2)
    (hroom : lam.2 + 2 ≤ μ.store.len lam.1) (hroomf : f.2 < μ.store.len f.1)
    (hlh : Fp.Disj (Store.inBlock lam.1 lam.2 2) (Store.inBlock h.1 h.2 (2 * ((n + 1) * (n + 1)))))
    (hH : HoldsMatrix h H μ.store) (hq4 : μ.store.get qw.1 (qw.2 + 4) = some r) :
    Writes .total I τ (oneEigStart (O := O) (Q := Q))
      (Env.frame [n + 1, m, q] [h, qw, lam, (L, 0), f, (L + 5, 0), (L + 6, 0)])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (fun μ' => HoldsWords μ'.store (oneEigCells L lam) ∧ OneEigFlag M f μ'.store) μ := by
  unfold oneEigStart
  refine ((oneEigDirections_writes hS (L := L) (by omega) h5 h6).frame_seq_le rfl rfl
    (by simp [Mem.Live]; omega) (sup_le (Fp.inBlock_le_sup_above (by omega))
      (Fp.inBlock_le_sup_above (by omega))) ?_)
  rintro μ₁ hfr₁ hD₁
  refine (polar_writes_pair hDisk (rd := (qw.1, qw.2 + 4)) (z := lam) rfl rfl
    ((hfr₁.get_eq (by simp only [fpNF]; omega)).trans hq4)
    (by simp [Mem.Live, hfr₁.length_eq]; omega) (by rw [hfr₁.len_eq]; exact hroom)).seq_le
    (le_sup_left.trans le_sup_left) ?_
  rintro μ₂ hfr₂ ⟨z₀, hz₀⟩
  have hfr₁₂ := hfr₁.trans' hfr₂
  refine (distSpec_terminates (τ := τ) (μ := μ₂) (h := h) (sp := lam) (tau := (L, 0)) (m := m)
    (q := q) hS hL hzero hCmp hNat le_rfl (by simp [Mem.Live, hfr₁₂.length_eq]; omega)
    ((hH.of_eqOff hfr₁ fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega).of_eqOff hfr₂ hlh)
    hz₀ (by rw [hfr₁₂.len_eq, h0]; omega)).frame_seq_le rfl rfl
    (by simp [Mem.Live, hfr₁₂.length_eq]; omega) (Fp.inBlock_le_sup_above le_rfl) ?_
  rintro μ₃ hfr₃ ⟨-, t₃, ht₃⟩
  refine (writes_indexLit (z := f) hL rfl rfl
    (by rw [hfr₃.len_eq, hfr₁₂.len_eq]; exact hroomf)).mono
    (le_sup_right.trans le_sup_left) ?_
  rintro μ₄ hfr₄ ⟨-, hf₄⟩
  refine ⟨(((hD₁.pair_of_eqOff le_rfl hfr₂ hz₀).cons_of_eqOff le_rfl hfr₃ ht₃).cons_of_eqOff
      le_rfl hfr₄ hf₄).mono fun c hc => ?_, Or.inl (by simpa using hf₄)⟩
  simp only [oneEigCells, List.cons_append, List.mem_cons, Prod.mk.eta] at hc ⊢
  tauto

-- The default heartbeat budget does not cover fifteen calls whose twelve outputs are read back
-- across all later frames.
set_option maxHeartbeats 400000 in
-- (fifteen calls, twelve outputs read back)
omit [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] in
/-- `NLAlib.SmallEig.oneEigDirections` on a scalar machine stores its words: with room for twelve
words at `d` and two at `k` in other buffers, it writes only those words, keeps the position and
stores the factor $\mathrm{fl}(0.66)$ at `K[0]` and the words `NLAlib.SmallEig.oneEigDirWords`
at `D`.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem oneEigDirections_writes_value {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {μ : Mem ℝ} {L : ℕ} (hlen : L + 7 ≤ μ.store.length)
    (h5 : μ.store.len (L + 5) = 12) (h6 : μ.store.len (L + 6) = 2) :
    Writes .total I τ (oneEigDirections (O := O) (Q := Q))
      (Env.frame [] [(L + 5, 0), (L + 6, 0)])
      (Store.inBlock (L + 5) 0 12 ⊔ Store.inBlock (L + 6) 0 1)
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.get (L + 6) 0 = some (M.lit (66 / 100)) ∧
        ∀ i < 12, μ'.store.get (L + 5) i = some (oneEigDirWords M i)) μ := by
  unfold oneEigDirections
  step (hS (.lit (66 / 100))) as μ₁ hfr₁ ⟨hp₁, k₀, hk₀, rfl⟩
  step (hS (.lit 1)) as μ₂ hfr₂ ⟨hp₂, d₀, hd₀, rfl⟩
  step (hS (.lit 0)) as μ₃ hfr₃ ⟨hp₃, d₁, hd₁, rfl⟩
  step (hS (.lit (1 / 2))) as μ₄ hfr₄ ⟨hp₄, d₂, hd₂, rfl⟩
  step (hS (.lit 3)) as μ₅ hfr₅ ⟨hp₅, d₃, hd₃, rfl⟩
  step (hS .sqrt) as μ₆ hfr₆ ⟨hp₆, d₃', hd₃', rfl⟩
  step (hS .mul) as μ₇ hfr₇ ⟨hp₇, d₃'', hd₃'', rfl⟩
  step (hS .neg) as μ₈ hfr₈ ⟨hp₈, d₄, hd₄, rfl⟩
  step (hS .copy) as μ₉ hfr₉ ⟨hp₉, d₅, hd₅, rfl⟩
  step (hS .neg) as μ₁₀ hfr₁₀ ⟨hp₁₀, d₆, hd₆, rfl⟩
  step (hS (.lit 0)) as μ₁₁ hfr₁₁ ⟨hp₁₁, d₇, hd₇, rfl⟩
  step (hS .copy) as μ₁₂ hfr₁₂ ⟨hp₁₂, d₈, hd₈, rfl⟩
  step (hS .neg) as μ₁₃ hfr₁₃ ⟨hp₁₃, d₉, hd₉, rfl⟩
  step (hS .copy) as μ₁₄ hfr₁₄ ⟨hp₁₄, d₁₀, hd₁₀, rfl⟩
  step (hS .copy) as μ₁₅ hfr₁₅ ⟨hp₁₅, d₁₁, hd₁₁, rfl⟩
  refine ⟨by simp only [hp₁₅, hp₁₄, hp₁₃, hp₁₂, hp₁₁, hp₁₀, hp₉, hp₈, hp₇, hp₆, hp₅, hp₄, hp₃,
    hp₂, hp₁], by kept, fun i hi => ?_⟩
  interval_cases i <;> simp only [oneEigDirWords] <;> kept

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] in
/-- A polar sample stores the sample of the window: on an exact polar disk sampler on the stream
`sU`, from a radius word $R$ at `rd` and room for two words at `z`, the call writes only those
two words, stores the polar sample `NLAlib.polarDisk` of the window at the current
position and advances the position by two.
The rule for one call of the operation. -/
theorem polar_writes_sample {I : Interp O Q ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {τ : Tape ℝ} {μ : Mem ℝ} {ρ : Env} {ins outs : List Operand} {rd z : ℕ × ℕ} {R : ℝ}
    (ha : Operand.evalList ρ ins = some [rd]) (hb : Operand.evalList ρ outs = some [z])
    (hrd : μ.store.get rd.1 rd.2 = some R) (hl : μ.Live [rd, z])
    (hz : z.2 + 2 ≤ μ.store.len z.1) :
    Writes .total I τ (.call (Has.inj DiskSampleOp.polar) [] ins outs) ρ
      (Store.inBlock z.1 z.2 2)
      (fun μ' => μ'.pos = μ.pos + 2 ∧ μ'.store.readBlock z.1 z.2 2 =
        some [(polarDisk 0 R (Tape.windowFn τ sU μ.pos 2)).re,
          (polarDisk 0 R (Tape.windowFn τ sU μ.pos 2)).im]) μ := by
  have hread : μ.readBlocks [rd] [1] = some [[R]] := by
    simp [Mem.readBlocks, Store.readBlock, hrd]
  refine (writes_call (R := polarDiskRel sU) hDisk (d := []) (a := [rd]) (b := [z])
    (k := 2) (ls := [2]) rfl ha hb rfl rfl rfl trivial (by simp [Fp.Apart])
    (fun _ => ⟨by simpa using hl, ⟨_, hread, trivial⟩, by simp [Mem.Room]; omega⟩)).mono
    (by simp) ?_
  rintro μ' - ⟨hp, xs, ys, hr, hys, hrel⟩
  have hys' := hrel R (Option.some.inj (hr.symm.trans hread))
  have hwin : (fun j : Fin 2 => (τ.window sU μ.pos 2).getD j 0) = Tape.windowFn τ sU μ.pos 2 := by
    funext j
    fin_cases j <;> simp [Tape.window, Tape.windowFn, List.getD_eq_getElem?_getD]
  simp only [polarDiskRel] at hys'
  rw [hwin] at hys'
  subst hys'
  obtain ⟨y, hy, hyy⟩ := Option.bind_eq_some_iff.mp (by simpa [Mem.readBlocks] using hys)
  simp only [Option.some.injEq, List.cons.injEq, and_true] at hyy
  exact ⟨hp, by rw [hy, hyy]⟩

omit [Has IndexOp O] [Has DiskSampleOp O] in
/-- **`DistSpec` is accurate on a set of points** `P`: from any matrix $\mathbf{H}$ of order
$n + 1$ at `h`, a point $p \in P$ at `sp` and room for the estimate at `tau` apart from both, the
run with the degree $m = 2^q$ writes only the estimate and stores a value within $10\%$ of the
distance from $p$ to the $d_i$. `NLAlib.SmallEig.distSpec_accuracy` gives it on the points of
modulus at most $C\|\mathbf{H}\|_2$ at distance at least $\eta_1$. -/
def DistSpecAccurateOn (I : Interp O Q ℝ) {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (d : Fin (n + 1) → ℂ) (m q : ℕ) (P : Set ℂ) : Prop :=
  ∀ (τ : Tape ℝ) (μ : Mem ℝ) (h sp tau : ℕ × ℕ) (p : ℂ), p ∈ P → μ.Live [h, sp, tau] →
    HoldsMatrix h H μ.store → μ.store.readBlock sp.1 sp.2 2 = some [p.re, p.im] →
    tau.2 < μ.store.len tau.1 → tau.1 ≠ h.1 → tau.1 ≠ sp.1 →
    Writes .total I τ (distSpec (O := O) (Q := Q)) (Env.frame [n + 1, m, q] [h, sp, tau])
      (Store.inBlock tau.1 tau.2 1)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ t : ℝ, μ'.store.get tau.1 tau.2 = some t ∧
        0.9 * (⨅ i, ‖p - d i‖) ≤ t ∧ t ≤ 1.1 * (⨅ i, ‖p - d i‖)) μ

/-- The best candidate of a round of `NLAlib.SmallEig.oneEig` with the scratch from `L` after
the candidates $j' < j$ of the points `pt`: the best estimate $b$ at `Bt[2]` is the bar
$\bar b$ with the mark `K[1]` $0$, or is at most $\bar b$ with the mark $1$ and the best point
`Bt` one of the candidates with $b$ within $10\%$ of its distance to the $d_i$; and $b \le \theta$
once a candidate $j' < j$ has $1.1$ times its distance at most $\theta$. -/
def OneEigBest {n : ℕ} (d : Fin (n + 1) → ℂ) (L : ℕ) (bar θ : ℝ) (pt : ℕ → ℂ) (j : ℕ)
    (s : Store ℝ) : Prop :=
  ∃ b, s.get (L + 4) 2 = some b ∧
    ((s.get (L + 6) 1 = some 0 ∧ b = bar) ∨
      (s.get (L + 6) 1 = some 1 ∧ b ≤ bar ∧ ∃ k < 6, s.get (L + 4) 0 = some (pt k).re ∧
        s.get (L + 4) 1 = some (pt k).im ∧ 0.9 * (⨅ i, ‖pt k - d i‖) ≤ b ∧
          b ≤ 1.1 * (⨅ i, ‖pt k - d i‖))) ∧
    ∀ k < j, 1.1 * (⨅ i, ‖pt k - d i‖) ≤ θ → b ≤ θ

omit [Has DiskSampleOp O] in
/-- One candidate point (`NLAlib.SmallEig.oneEigPoint`) with the scratch from `L`, accurately:
on a scalar machine with index literals, the literals $0$ and $1$ exact and exact comparisons,
with `DistSpec` accurate on the candidate `NLAlib.SmallEig.oneEigPointWord` of the estimate
$\tau$, the direction `j`, the point $s$ and the sample $w$ read, it writes only `Pt`, `Tc`,
`Bt` and `K[1]`, keeps the position and moves the best candidate
(`NLAlib.SmallEig.OneEigBest`) from `j` to `j + 1`. -/
theorem oneEigPoint_best {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (h1 : M.lit 1 = 1) (hCmp : IsCmp id I)
    {n m q j L : ℕ} (hj : j < 6) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {P : Set ℂ} (hDS : DistSpecAccurateOn (O := O) (Q := Q) I H d m q P) {τ : Tape ℝ}
    {μ : Mem ℝ} {h lam : ℕ × ℕ} (hh : h.1 < L) (hlam : lam.1 < L)
    (hlen : μ.store.length = L + 7) (h2 : μ.store.len (L + 2) = 2)
    (h3 : μ.store.len (L + 3) = 1) (h4 : μ.store.len (L + 4) = 3) (h6 : μ.store.len (L + 6) = 2)
    (hH : HoldsMatrix h H μ.store) {t₀ bar θ : ℝ} {s w : ℂ} (hT : μ.store.get L 0 = some t₀)
    (hD : ∀ i < 12, μ.store.get (L + 5) i = some (oneEigDirWords M i))
    (hs : μ.store.readBlock lam.1 lam.2 2 = some [s.re, s.im])
    (hw : μ.store.readBlock (L + 1) 0 2 = some [w.re, w.im])
    (hP : oneEigPointWord M t₀ (oneEigDir M j) s w ∈ P)
    (hB : OneEigBest d L bar θ (fun k => oneEigPointWord M t₀ (oneEigDir M k) s w) j μ.store) :
    Writes .total I τ (oneEigPoint (O := O) (Q := Q))
      (Env.frame [n + 1, m, q, j] [h, (L, 0), (L + 5, 0), lam, (L + 1, 0), (L + 2, 0),
        (L + 3, 0), (L + 4, 0), (L + 6, 0)])
      (Store.inBlock (L + 2) 0 2 ⊔ Store.inBlock (L + 3) 0 1 ⊔ Store.inBlock (L + 4) 0 3 ⊔
        Store.inBlock (L + 6) 1 1)
      (fun μ' => μ'.pos = μ.pos ∧
        OneEigBest d L bar θ (fun k => oneEigPointWord M t₀ (oneEigDir M k) s w) (j + 1)
          μ'.store) μ := by
  set pt := fun k => oneEigPointWord M t₀ (oneEigDir M k) s w with hpt
  have hD₀ : μ.store.get (L + 5) (0 + 2 * j) = some (oneEigDirWords M (2 * j)) := by
    rw [Nat.zero_add]; exact hD _ (by omega)
  have hD₁ : μ.store.get (L + 5) (0 + (2 * j + 1)) = some (oneEigDirWords M (2 * j + 1)) := by
    rw [Nat.zero_add]; exact hD _ (by omega)
  have hL₀ : μ.store.get lam.1 lam.2 = some s.re := by
    simpa using Store.get_of_readBlock hs (j := 0) (by omega) 0
  have hL₁ : μ.store.get lam.1 (lam.2 + 1) = some s.im := by
    simpa using Store.get_of_readBlock hs (j := 1) (by omega) 0
  have hZ₀ : μ.store.get (L + 1) 0 = some w.re := by
    simpa using Store.get_of_readBlock hw (j := 0) (by omega) 0
  have hZ₁ : μ.store.get (L + 1) 1 = some w.im := by
    simpa using Store.get_of_readBlock hw (j := 1) (by omega) 0
  obtain ⟨b, hb, hBk, hBθ⟩ := hB
  unfold oneEigPoint
  step (hS .mul) as μ₁ hfr₁ ⟨hp₁, a₁, ha₁, rfl⟩
  step (hS .add) as μ₂ hfr₂ ⟨hp₂, a₂, ha₂, rfl⟩
  step (hS .add) as μ₃ hfr₃ ⟨hp₃, a₃, ha₃, rfl⟩
  step (hS .mul) as μ₄ hfr₄ ⟨hp₄, b₁, hb₁, rfl⟩
  step (hS .add) as μ₅ hfr₅ ⟨hp₅, b₂, hb₂, rfl⟩
  step (hS .add) as μ₆ hfr₆ ⟨hp₆, b₃, hb₃, rfl⟩
  have hsp : μ₆.store.readBlock (L + 2) 0 2 = some [(pt j).re, (pt j).im] :=
    Store.readBlock_add (n := 1) (k := 1) (Store.readBlock_one_of_get (by kept))
      (Store.readBlock_one_of_get (by kept))
  have hH₆ : HoldsMatrix h H μ₆.store := by unfold HoldsMatrix at hH ⊢; kept
  refine (hDS τ μ₆ h (L + 2, 0) (L + 3, 0) (pt j) hP (by room) hH₆ hsp (by room) (by omega)
    (by omega)).frame_seq_le rfl rfl (by room) (by fp_sub) ?_
  rintro μ₇ hfr₇ ⟨hp₇, t₇, ht₇, ha₇, hb₇⟩
  refine writes_ite (a := [(L + 3, 0), (L + 4, 2)]) rfl rfl (hCmp.test_le ht₇ (by kept)) ?_
  split_ifs with hle
  · step (hS .copy) as μ₈ hfr₈ ⟨hp₈, c₁, hc₁, rfl⟩
    step (hS .copy) as μ₉ hfr₉ ⟨hp₉, c₂, hc₂, rfl⟩
    step (hS .copy) as μ₁₀ hfr₁₀ ⟨hp₁₀, c₃, hc₃, rfl⟩
    refine (writes_indexLit hL rfl rfl (by room)).mono (by fp_sub) ?_
    rintro μ₁₁ hfr₁₁ ⟨hp₁₁, hk₁₁⟩
    have hle' : t₇ ≤ b := by simpa using hle
    have hbar : b ≤ bar := by
      rcases hBk with ⟨-, rfl⟩ | ⟨-, hbb, -⟩
      exacts [le_rfl, hbb]
    refine ⟨by simp only [hp₁₁, hp₁₀, hp₉, hp₈, hp₇, hp₆, hp₅, hp₄, hp₃, hp₂, hp₁],
      t₇, by kept, Or.inr ⟨by simpa [h1] using hk₁₁, hle'.trans hbar, j, hj, by kept, by kept,
        ha₇, hb₇⟩, fun k hk hkθ => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact hle'.trans (hBθ k hk hkθ)
    · exact hb₇.trans hkθ
  · refine (Writes.skip ⟨by simp only [hp₇, hp₆, hp₅, hp₄, hp₃, hp₂, hp₁], b, by kept,
      ?_, fun k hk hkθ => ?_⟩).mono bot_le fun _ _ h => h
    · rcases hBk with ⟨hk0, rfl⟩ | ⟨hk1, hbb, k, hk, hk₀, hk₁, hka, hkb⟩
      · exact Or.inl ⟨by kept, rfl⟩
      · exact Or.inr ⟨by kept, hbb, k, hk, by kept, by kept, hka, hkb⟩
    · have hlt : b < t₇ := by simpa using hle
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact hBθ k hk hkθ
      · exact hlt.le.trans (hb₇.trans hkθ)

omit [Has DiskSampleOp O] in
/-- The end of a round (`NLAlib.SmallEig.oneEigMove`) with a marked best candidate: from the
mark `K[1]` $1$ and the best point $(x, y)$ and estimate $b$ at `Bt`, on a scalar machine with
the literal $1$ exact and exact comparisons, it writes only `Lam` and `Tau`, stores the point and
the estimate there and keeps the position. -/
theorem oneEigMove_marked {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hCmp : IsCmp id I) {L : ℕ} {τ : Tape ℝ} {μ : Mem ℝ} {lam f : ℕ × ℕ} (hlam : lam.1 < L)
    (hlen : μ.store.length = L + 7) (h0 : μ.store.len L = 1)
    (hroom : lam.2 + 2 ≤ μ.store.len lam.1) {x y b : ℝ}
    (hK : μ.store.get (L + 6) 1 = some 1) (hx : μ.store.get (L + 4) 0 = some x)
    (hy : μ.store.get (L + 4) 1 = some y) (hb : μ.store.get (L + 4) 2 = some b) :
    Writes .total I τ (oneEigMove (O := O) (Q := Q))
      (Env.frame [] [(L + 4, 0), (L + 6, 0), lam, (L, 0), f])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock L 0 1)
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock lam.1 lam.2 2 = some [x, y] ∧
        μ'.store.get L 0 = some b) μ := by
  unfold oneEigMove
  refine writes_ite (a := [(L + 6, 1)]) rfl rfl (hCmp.test_isPos hK) ?_
  rw [if_pos (by simp)]
  step (hS .copy) as μ₁ hfr₁ ⟨hp₁, c₁, hc₁, rfl⟩
  step (hS .copy) as μ₂ hfr₂ ⟨hp₂, c₂, hc₂, rfl⟩
  step (hS .copy) as μ₃ hfr₃ ⟨hp₃, c₃, hc₃, rfl⟩
  exact ⟨by rw [hp₃, hp₂, hp₁], Store.readBlock_add (n := 1) (k := 1)
    (Store.readBlock_one_of_get (by kept)) (Store.readBlock_one_of_get (by kept)), by kept⟩

/-- One round of `NLAlib.SmallEig.oneEig` (`NLAlib.SmallEig.oneEigRound`) with the scratch from
`L` when its sample is good: on a scalar machine with index literals, the literals $0$ and $1$
exact, exact comparisons and an exact polar sampler on the stream `sU`, with `DistSpec` accurate
on a set $P$ holding the six candidates `NLAlib.SmallEig.oneEigPointWord` of the estimate
$\tau$ at `Tau`, the computed directions, the point $s$ at `Lam` and the polar sample $w$ of the
window at the current position (radius word $r$ at `qw[4]`), if $1.1$ times the distance of some
candidate is at most $\theta$ and $\theta$ is below the bar $\mathrm{fl}(\tau k_0)$ ($k_0$ at
`K[0]`), then the round writes only `Lam` and the scratch, and stores at `Lam` a candidate and at
`Tau` an estimate at most $\theta$ and within $10\%$ of its distance. -/
theorem oneEigRound_good {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (h0 : M.lit 0 = 0) (h1 : M.lit 1 = 1) (hCmp : IsCmp id I) {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {n m q L : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} {P : Set ℂ} (hDS : DistSpecAccurateOn (O := O) (Q := Q) I H d m q P)
    {τ : Tape ℝ} {μ : Mem ℝ} {h qw lam f : ℕ × ℕ}
    (hh : h.1 < L) (hqw : qw.1 < L) (hlam : lam.1 < L) (hf : f.1 < L)
    (hlen : μ.store.length = L + 7) (hl0 : μ.store.len L = 1) (hl1 : μ.store.len (L + 1) = 2)
    (hl2 : μ.store.len (L + 2) = 2) (hl3 : μ.store.len (L + 3) = 1)
    (hl4 : μ.store.len (L + 4) = 3) (hl6 : μ.store.len (L + 6) = 2)
    (hroom : lam.2 + 2 ≤ μ.store.len lam.1) (hH : HoldsMatrix h H μ.store) {r t₀ k₀ θ : ℝ}
    {s : ℂ} (hq4 : μ.store.get qw.1 (qw.2 + 4) = some r) (hT : μ.store.get L 0 = some t₀)
    (hD : ∀ i < 12, μ.store.get (L + 5) i = some (oneEigDirWords M i))
    (hK0 : μ.store.get (L + 6) 0 = some k₀)
    (hs : μ.store.readBlock lam.1 lam.2 2 = some [s.re, s.im])
    (hP : ∀ j < 6, oneEigPointWord M t₀ (oneEigDir M j) s
      (polarDisk 0 r (Tape.windowFn τ sU μ.pos 2)) ∈ P)
    (hcov : ∃ j < 6, 1.1 * (⨅ i, ‖oneEigPointWord M t₀ (oneEigDir M j) s
      (polarDisk 0 r (Tape.windowFn τ sU μ.pos 2)) - d i‖) ≤ θ) (hθ : θ < M.mul t₀ k₀) :
    Writes .total I τ (oneEigRound (O := O) (Q := Q))
      (Env.frame [n + 1, m, q] [h, qw, (L + 5, 0), lam, (L, 0), f, (L + 1, 0), (L + 2, 0),
        (L + 3, 0), (L + 4, 0), (L + 6, 0)])
      (Store.inBlock lam.1 lam.2 2 ⊔ Fp.above L)
      (fun μ' => (∃ j < 6, μ'.store.readBlock lam.1 lam.2 2 = some
        [(oneEigPointWord M t₀ (oneEigDir M j) s (polarDisk 0 r (Tape.windowFn τ sU μ.pos 2))).re,
          (oneEigPointWord M t₀ (oneEigDir M j) s
            (polarDisk 0 r (Tape.windowFn τ sU μ.pos 2))).im] ∧
        ∃ b, μ'.store.get L 0 = some b ∧ b ≤ θ ∧
          0.9 * (⨅ i, ‖oneEigPointWord M t₀ (oneEigDir M j) s
            (polarDisk 0 r (Tape.windowFn τ sU μ.pos 2)) - d i‖) ≤ b ∧
          b ≤ 1.1 * (⨅ i, ‖oneEigPointWord M t₀ (oneEigDir M j) s
            (polarDisk 0 r (Tape.windowFn τ sU μ.pos 2)) - d i‖)) ∧
        (∀ i < 12, μ'.store.get (L + 5) i = some (oneEigDirWords M i)) ∧
        μ'.store.get (L + 6) 0 = some k₀) μ := by
  set w := polarDisk 0 r (Tape.windowFn τ sU μ.pos 2) with hw_def
  set pt := fun k => oneEigPointWord M t₀ (oneEigDir M k) s w with hpt
  unfold oneEigRound
  refine (polar_writes_sample hDisk (rd := (qw.1, qw.2 + 4)) (z := (L + 1, 0)) rfl rfl hq4
    (by simp [Mem.Live]; omega) (by simp [hl1])).seq_le (Fp.inBlock_le_sup_above (by omega)) ?_
  rintro μ₁ hfr₁ ⟨-, hw₁⟩
  rw [← hw_def] at hw₁
  step (hS .mul) as μ₂ hfr₂ ⟨-, b₂, hb₂, rfl⟩
  refine (writes_indexLit (z := (L + 6, 1)) hL rfl rfl (by room)).seq_le
    (Fp.inBlock_le_sup_above (by omega)) ?_
  rintro μ₃ hfr₃ ⟨-, hk₃⟩
  have hfrA := (hfr₁.trans' hfr₂).trans' hfr₃
  have hB₀ : OneEigBest d L (M.mul t₀ k₀) θ pt 0 μ₃.store :=
    ⟨M.mul t₀ k₀, (hfr₃.get_eq (by simp only [fpNF]; omega)).trans hb₂,
      Or.inl ⟨by rw [hk₃, Nat.cast_zero, h0], rfl⟩,
      fun k hk => absurd hk (by omega)⟩
  refine (writes_loop (N := 6) rfl (fun _ => Store.inBlock (L + 2) 0 2 ⊔
      Store.inBlock (L + 3) 0 1 ⊔ Store.inBlock (L + 4) 0 3 ⊔ Store.inBlock (L + 6) 1 1)
    (fun _ _ => le_rfl) (fun j μ' => OneEigBest d L (M.mul t₀ k₀) θ pt j μ'.store) hB₀
    ?_).seq_le (by fp_sub) ?_
  · rintro j hj μ' hfr' hB'
    have hfrB := hfrA.trans' hfr'
    refine ((oneEigPoint_best hS hL h1 hCmp (j := j) (L := L) hj hDS hh hlam
      (by rw [hfrB.length_eq, hlen]) (by rw [hfrB.len_eq, hl2]) (by rw [hfrB.len_eq, hl3])
      (by rw [hfrB.len_eq, hl4]) (by rw [hfrB.len_eq, hl6])
      (hH.of_eqOff hfrB fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega)
      (by kept) (fun i hi => by have := hD i hi; kept)
      (hfrB.keep (Store.readsOnly_readBlock _ _ _ _)
        (fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega) hs)
      (((hfr₂.trans' hfr₃).trans' hfr').keep (Store.readsOnly_readBlock _ _ _ _)
        (fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega) hw₁) (hP j hj)
      hB').in_frame rfl rfl
      (by simp [Mem.Live, hfrB.length_eq, hlen]; omega)).mono le_rfl fun _ _ h => h.2
  rintro μ₄ hfr₄ ⟨b, hb, hBk, hBθ⟩
  obtain ⟨j₀, hj₀, hj₀θ⟩ := hcov
  have hbθ := hBθ j₀ hj₀ hj₀θ
  obtain ⟨hK1, -, k, hk, hx, hy, hka, hkb⟩ : μ₄.store.get (L + 6) 1 = some 1 ∧ b ≤ M.mul t₀ k₀ ∧
      ∃ k < 6, μ₄.store.get (L + 4) 0 = some (pt k).re ∧
        μ₄.store.get (L + 4) 1 = some (pt k).im ∧ 0.9 * (⨅ i, ‖pt k - d i‖) ≤ b ∧
          b ≤ 1.1 * (⨅ i, ‖pt k - d i‖) := by
    rcases hBk with ⟨-, rfl⟩ | hm
    · exact absurd hbθ (not_le.mpr hθ)
    · exact hm
  have hfrC := hfrA.trans' hfr₄
  refine ((oneEigMove_marked hS hCmp (f := f) hlam (by rw [hfrC.length_eq, hlen])
    (by rw [hfrC.len_eq, hl0]) (by rw [hfrC.len_eq]; exact hroom) hK1 hx hy hb).in_frame rfl
    rfl (by simp [Mem.Live, hfrC.length_eq, hlen]; omega)).mono (by fp_sub) ?_
  rintro μ₅ hfr₅ ⟨-, hlam₅, hT₅⟩
  have hfrD := hfrC.trans' hfr₅
  exact ⟨⟨k, hk, hlam₅, b, hT₅, hbθ, hka, hkb⟩, fun i hi => hfrD.keep (Store.readsOnly_get _ _ _)
    (fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega) (hD i hi),
    hfrD.keep (Store.readsOnly_get _ _ _)
      (fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega) hK0⟩

/-- The start of `NLAlib.SmallEig.oneEig` (`NLAlib.SmallEig.oneEigStart`) with the scratch from
`L` when its sample is good: on a scalar machine with index literals, the literal $0$ exact, exact
comparisons and an exact polar sampler on the stream `sU`, with `DistSpec` accurate on a set $P$
holding the polar sample $w_0$ of the window at the current position (radius word $r$ at
`qw[4]`), it writes only `Lam`, the flag and the scratch, and stores the computed directions,
the factor $\mathrm{fl}(0.66)$, the point $w_0$ at `Lam`, an estimate within $10\%$ of its
distance at `Tau` and the flag $0$. -/
theorem oneEigStart_good {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (h0 : M.lit 0 = 0) {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {n m q L : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {P : Set ℂ} (hDS : DistSpecAccurateOn (O := O) (Q := Q) I H d m q P) {τ : Tape ℝ}
    {μ : Mem ℝ} {h qw lam f : ℕ × ℕ} {r : ℝ} (hh : h.1 < L) (hqw : qw.1 < L) (hlam : lam.1 < L)
    (hf : f.1 < L) (hlen : μ.store.length = L + 7) (hl0 : μ.store.len L = 1)
    (hl5 : μ.store.len (L + 5) = 12)
    (hl6 : μ.store.len (L + 6) = 2) (hroom : lam.2 + 2 ≤ μ.store.len lam.1)
    (hroomf : f.2 < μ.store.len f.1)
    (hlh : Fp.Disj (Store.inBlock lam.1 lam.2 2) (Store.inBlock h.1 h.2 (2 * ((n + 1) * (n + 1)))))
    (hlf : Fp.Disj (Store.inBlock lam.1 lam.2 2) (Store.inBlock f.1 f.2 1))
    (hH : HoldsMatrix h H μ.store) (hq4 : μ.store.get qw.1 (qw.2 + 4) = some r)
    (hP : polarDisk 0 r (Tape.windowFn τ sU μ.pos 2) ∈ P) :
    Writes .total I τ (oneEigStart (O := O) (Q := Q))
      (Env.frame [n + 1, m, q] [h, qw, lam, (L, 0), f, (L + 5, 0), (L + 6, 0)])
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (fun μ' => (∀ i < 12, μ'.store.get (L + 5) i = some (oneEigDirWords M i)) ∧
        μ'.store.get (L + 6) 0 = some (M.lit (66 / 100)) ∧
        μ'.store.readBlock lam.1 lam.2 2 = some [(polarDisk 0 r (Tape.windowFn τ sU μ.pos 2)).re,
          (polarDisk 0 r (Tape.windowFn τ sU μ.pos 2)).im] ∧
        (∃ t, μ'.store.get L 0 = some t ∧
          0.9 * (⨅ i, ‖polarDisk 0 r (Tape.windowFn τ sU μ.pos 2) - d i‖) ≤ t ∧
          t ≤ 1.1 * (⨅ i, ‖polarDisk 0 r (Tape.windowFn τ sU μ.pos 2) - d i‖)) ∧
        μ'.store.get f.1 f.2 = some 0) μ := by
  set w := polarDisk 0 r (Tape.windowFn τ sU μ.pos 2) with hw_def
  unfold oneEigStart
  refine ((oneEigDirections_writes_value hS (L := L) (by omega) hl5 hl6).frame_seq_le rfl rfl
    (by simp [Mem.Live]; omega) (sup_le (Fp.inBlock_le_sup_above (by omega))
      (Fp.inBlock_le_sup_above (by omega))) ?_)
  rintro μ₁ hfr₁ ⟨hp₁, hK₁, hD₁⟩
  refine (polar_writes_sample hDisk (rd := (qw.1, qw.2 + 4)) (z := lam) rfl rfl
    ((hfr₁.get_eq (by simp only [fpNF]; omega)).trans hq4)
    (by simp [Mem.Live, hfr₁.length_eq]; omega) (by rw [hfr₁.len_eq]; exact hroom)).seq_le
    (le_sup_left.trans le_sup_left) ?_
  rintro μ₂ hfr₂ ⟨-, hz₀⟩
  rw [hp₁, ← hw_def] at hz₀
  have hfr₁₂ := hfr₁.trans' hfr₂
  refine (hDS τ μ₂ h lam (L, 0) w hP (by simp [Mem.Live, hfr₁₂.length_eq]; omega)
    ((hH.of_eqOff hfr₁ fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega).of_eqOff hfr₂ hlh)
    hz₀ (by rw [hfr₁₂.len_eq, hl0]; omega) (by omega) (by omega)).frame_seq_le rfl rfl
    (by simp [Mem.Live, hfr₁₂.length_eq]; omega) (Fp.inBlock_le_sup_above le_rfl) ?_
  rintro μ₃ hfr₃ ⟨-, t₃, ht₃, ha₃, hb₃⟩
  refine (writes_indexLit (z := f) hL rfl rfl
    (by rw [hfr₃.len_eq, hfr₁₂.len_eq]; exact hroomf)).mono
    (le_sup_right.trans le_sup_left) ?_
  rintro μ₄ hfr₄ ⟨-, hf₄⟩
  have hfr₃₄ := hfr₃.trans' hfr₄
  refine ⟨fun i hi => (hfr₂.trans' hfr₃₄).keep (Store.readsOnly_get _ _ _)
      (fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega) (hD₁ i hi),
    (hfr₂.trans' hfr₃₄).keep (Store.readsOnly_get _ _ _)
      (fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega) hK₁,
    hfr₄.keep (Store.readsOnly_readBlock _ _ _ _) hlf.symm
      (hfr₃.keep (Store.readsOnly_readBlock _ _ _ _)
        (fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega) hz₀),
    ⟨t₃, hfr₄.keep (Store.readsOnly_get _ _ _)
      (fun _ _ h₁ h₂ => by simp only [fpNF] at h₁ h₂; omega) ht₃, ha₃, hb₃⟩,
    by rw [hf₄, Nat.cast_zero, h0]⟩

end Theorems

end NLAlib.SmallEig
