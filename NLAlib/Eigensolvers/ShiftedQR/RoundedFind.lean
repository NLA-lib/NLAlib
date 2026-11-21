/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.FindRitz
public import NLAlib.Matrix.QRIteration.RoundedStrategy
public import NLAlib.Eigensolvers.ShiftedQR.PairBlocks
public import NLAlib.Eigensolvers.ShiftedQR.RoundedRitz
public import NLAlib.Eigensolvers.ShiftedQR.StableStep

/-!
# `Find` in floating point

The binary search $\mathrm{Find}$ of [BanksGarzaVargasSrivastava2022, Lemma 5.1] for a promising
Ritz value among $k = 2^m$ shifts, with computed comparison values. Each level compares the two
halves of the current window by a routine that computes
$\tau = \|\mathbf{e}_n^{\mathsf T}p_h(\mathbf{H})^{-e}\|^{-1}$ for a half $h$ and the current
exponent $e$ within the relative error $0.0011$ (`NLAlib.ShiftedQR.IsHalfTau`), keeps the half
with the smaller value, and doubles the exponent. The program is the exact-arithmetic search
(its initialization, decision and final copy, `NLAlib.ShiftedQR.findRitzSearch`) with the exact
half norms replaced by the routine; the routine is a parameter, met by $e$ rounded degree-$h$
steps (`NLAlib.ShiftedQR.multiStepStable`) followed by the rounded product of the moduli of the
last diagonal entries ([BanksGarzaVargasSrivastava2022, Lemma 3.9]).

The index words (window start, half length, exponent) are natural literals; the machine stores
them exactly up to $k$ (`NLAlib.Ops.IsExactNatLit`), as the standard model alone does not.

## Main definitions

* `NLAlib.ShiftedQR.IsHalfTau`: the contract of the comparison routine.
* `NLAlib.ShiftedQR.findRounded`: the program.
* `NLAlib.ShiftedQR.repeatBlock`, `NLAlib.ShiftedQR.stepComptau`,
  `NLAlib.ShiftedQR.comptauHalf`: a block copied $e$ times; `comptau` of a degree $k$ rounded
  step; the comparison routine (that step with the half repeated $e$ times).

## Main results

* `NLAlib.ShiftedQR.findRounded_writes_choice`: the stored result is a choice of `Find` with
  computed values (`NLAlib.IsFindRitzChoice`).
* `NLAlib.ShiftedQR.findRounded_writes`: the stored result is
  $(1.01B)^{4m/2^m}$-promising.
* `NLAlib.ShiftedQR.repeatBlock_writes`, `NLAlib.ShiftedQR.stepComptau_writes`: their memory and
  the $0.001$ of `comptau` after a degree $k$ rounded step.
* `NLAlib.ShiftedQR.comptauHalf_isHalfTau`: the comparison routine satisfies the contract.
* `NLAlib.ShiftedQR.findRitzInitialize_writes_of_exactNatLit`,
  `NLAlib.ShiftedQR.findRitzDecision_writes_of_exactNatLit`,
  `NLAlib.ShiftedQR.findRitzCopy_writes_of_readBlock`: the search words with exact natural
  literals.

Termination on any matrix is in `NLAlib.Eigensolvers.ShiftedQR.RoundedFindTermination`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type}

/-! ### The comparison routine and the program -/

/-- **A routine for the comparison values of `Find`** for the matrix $\mathbf{H}$ of order
$n + 1$ and the $k$ shifts `shifts`: on the dimensions `[n + 1, h, e]`, from $\mathbf{H}$ stored
at `A` and the $h$ consecutive shifts $l$ of `shifts` from the position $a$ stored as pairs at
`S`, with $a + h \le k$ and $2he = k$, the routine `Tau` writes only the word `P` (in a buffer of
its own), keeps the tape position, and stores a $t$ with
$$\lvert t - \tau\rvert \le 0.0011\,\tau, \qquad
\tau = \|\mathbf{e}_n^{\mathsf T}p_l(\mathbf{H})^{-e}\|^{-1}.$$
-/
def IsHalfTau {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (shifts : List ℂ)
    (Tau : Stmt O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ (a h e : ℕ), a + h ≤ shifts.length → 2 * (h * e) = shifts.length →
    ∀ (τ : Tape ℝ) (μ : Mem ℝ) (A S P : ℕ × ℕ), μ.Live [A, S, P] → HoldsMatrix A H μ.store →
      μ.store.readBlock S.1 S.2 (2 * h) =
        some (((shifts.drop a).take h).flatMap fun z => [z.re, z.im]) →
      P.2 < μ.store.len P.1 → P.1 ≠ A.1 → P.1 ≠ S.1 →
      Writes .total I τ Tau (Env.frame [n + 1, h, e] [A, S, P]) (Store.inBlock P.1 P.2 1)
        (fun μ' => μ'.pos = μ.pos ∧ ∃ t : ℝ, μ'.store.get P.1 P.2 = some t ∧
          |t - ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly ((shifts.drop a).take h)))⁻¹ ^ e)
            (Fin.last n))‖⁻¹| ≤ 0.0011 * ‖WithLp.toLp 2
              (((Polynomial.aeval H (shiftPoly ((shifts.drop a).take h)))⁻¹ ^ e)
                (Fin.last n))‖⁻¹) μ

/-! ### The comparison routine: `comptau` of the repeated half -/

section HalfTau

variable [Has ScalarOp O]

/-- **A block repeated**: the $n$ words at `S` copied $e$ times, one after the other, to `T`.
The interface is `[n, e] (S) → (T)`. -/
def repeatBlock : Stmt O Q := ops% [n, e] (S) → (T) {
  for j < e {
    run (unaryMap (Has.inj ScalarOp.copy)) [n] (S, T[n * j])
  }
}

/-- `repeatBlock` on any scalar machine stores the $n$ words $xs$ of `S` repeated $e$ times,
$xs^e$, and writes only that block. Source and target are in different buffers.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem repeatBlock_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {m : Mem ℝ} {n e : ℕ} {s t : ℕ × ℕ} {xs : List ℝ} (hl : m.Live [s, t])
    (hst : s.1 ≠ t.1) (hs : m.store.readBlock s.1 s.2 n = some xs)
    (ht : t.2 + n * e ≤ m.store.len t.1) :
    Writes .total I τ repeatBlock (Env.frame [n, e] [s, t]) (Store.inBlock t.1 t.2 (n * e))
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock t.1 t.2 (n * e) = some (List.replicate e xs).flatten) m := by
  unfold repeatBlock
  refine writes_loop (n := .var 1) (N := e) rfl (fun _ => Store.inBlock t.1 t.2 (n * e))
    (fun _ _ => le_rfl)
    (fun j μ => μ.pos = m.pos ∧
      μ.store.readBlock t.1 t.2 (n * j) = some (List.replicate j xs).flatten)
    ⟨rfl, by simp⟩ fun j hj μ hfr ⟨hp, hpre⟩ => ?_
  have hsμ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_ne hst.symm) hs
  have hcp := writes_unaryMap_of_disj_or_eq (md := .total) (τ := τ) (f := id) (hS .copy)
    (y := (t.1, t.2 + n * j)) (Or.inl (Fp.disj_inBlock_of_ne hst)) hsμ
    (by rw [hfr.len_eq]; nlinarith)
  refine (hcp.in_frame rfl rfl ?_).mono (Fp.inBlock_le_inBlock (by omega) (by nlinarith)) ?_
  · simpa [Mem.Live, hfr.length_eq] using hl
  intro μ' hfr' ⟨hp', hnew⟩
  have hpre' := hfr'.keep (Store.readsOnly_readBlock _ _ _ _)
    (Fp.disj_inBlock_of_le le_rfl).symm hpre
  refine ⟨hp'.trans hp, ?_⟩
  rw [Nat.mul_succ, List.replicate_succ', List.flatten_append, List.flatten_singleton]
  exact Store.readBlock_add hpre' (by simpa using hnew)

/-- The pairs of a list repeated $e$ times are its pairs repeated $e$ times. -/
theorem flatMap_flatten_replicate (l : List ℂ) (e : ℕ) :
    ((List.replicate e l).flatten.flatMap fun z => [z.re, z.im]) =
      (List.replicate e (l.flatMap fun z => [z.re, z.im])).flatten := by
  induction e with
  | zero => simp
  | succ e ih => rw [List.replicate_succ, List.replicate_succ, List.flatten_cons,
      List.flatten_cons, List.flatMap_append, ih]

variable [Has CmpTst Q]

/-- **`comptau` of a degree $k$ rounded step**: run `NLAlib.ShiftedQR.multiStepStable` with the
$k$ shifts at `S` on the matrix at `A`, in place, and store in `P` the
`NLAlib.ShiftedQR.comptau` of the $k$ last triangular diagonal entries (scoped). The interface is
`[d, k] (A, S) → (A, P)`. -/
def stepComptau : Stmt O Q := ops% [d, k] (A, S) → (A, P) {
  let Ds ← alloc (2 * k);
  run (multiStepStable (Op := O) (Tst := Q)) [d, k] (A, S, A, Ds);
  run (comptau (Op := O) (Tst := Q)) [k] (Ds, P)
}

/-- **`comptau` of a degree $k$ rounded step is within $0.001$**
([BanksGarzaVargasSrivastava2022, Lemmas 3.6 and 3.9]; the precision condition below, with
$8004\kappa$, comes from the last diagonal entry of the triangular factor of $p(\mathbf{H})$,
$\|\mathbf{e}_n^{\mathsf T}p(\mathbf{H})^{-1}\|^{-1}$, without Lemma 3.7; the paper's route
needs $\kappa^2$ and $24000$): on a scalar machine
with the standard model and exact comparisons, let $\mathbf{H} \ne 0$ of order $n + 1$ be
upper Hessenberg, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with
$\kappa(\mathbf{V}) \le \kappa$, the $k$ shifts $s_1, \dots, s_k$ in
$\mathbb{D}(0, C\|\mathbf{H}\|_2)$ ($C \ge 0$) at distance at least $d > 0$ from every $e_i$,
$(n + 1)\boldsymbol{u} \le 1/2500$, $30000(k + 1)\boldsymbol{u} \le 1$ and
$x = 300(n + 1)^2\boldsymbol{u} \le (8004\kappa)^{-1}(d/((2 + 2C)\|\mathbf{H}\|_2))^k$. Then
`stepComptau` (the chain of `NLAlib.ShiftedQR.multiStepStable`, then
`NLAlib.ShiftedQR.comptau`) stores in place the rounded step's output
$\widehat{\mathbf{H}}'$ (upper Hessenberg, the end of a stable chain from $\mathbf{H}$ with the
shifts $s_1, \dots, s_k$), and in `P` a $t$ with $\lvert t - \tau\rvert \le 0.001\,\tau$,
$\tau = \|\mathbf{e}_n^{\mathsf T}p(\mathbf{H})^{-1}\|_2^{-1}$.
It writes only the matrix and `P`; matrix, shifts and `P` are disjoint views.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine`, `NLAlib.ShiftedQR.shqrSmallEigRoutine`
and `NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem stepComptau_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hCmp : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {C κ d : ℝ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ev : Fin (n + 1) → ℂ}
    {ss : List ℂ} {a s p : ℕ × ℕ} (hH : IsUpperHessenberg H) (hH0 : H ≠ 0) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal ev) (hκ : pseudoConditionNumber V ≤ κ) (hC : 0 ≤ C)
    (hd : 0 < d) (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖ev i - s‖)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hu : 30000 * (ss.length + 1) * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * κ)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ ss.length)
    (hl : m.Live [a, s, p]) (hA : HoldsMatrix a H m.store)
    (hss : m.store.readBlock s.1 s.2 (2 * ss.length) = some (ss.flatMap fun z => [z.re, z.im]))
    (hp : p.2 < m.store.len p.1)
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * ss.length)))
    (hap : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock p.1 p.2 1)) :
    Writes .total I τ stepComptau (Env.frame [n + 1, ss.length] [a, s, a, p])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock p.1 p.2 1)
      (fun m' => m'.pos = m.pos ∧ ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
        IsStableQRChain (300 * (n + 1) ^ 2 * u) H ss H' Rs ∧ IsUpperHessenberg H' ∧
          HoldsMatrix a H' m'.store ∧ ∃ t : ℝ, m'.store.get p.1 p.2 = some t ∧
          |t - ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss))⁻¹ (Fin.last n))‖⁻¹| ≤
            0.001 * ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss))⁻¹ (Fin.last n))‖⁻¹) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length ∧ p.1 < m.store.length := by
    simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 2 * .var 1] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [2 * ss.length]) rfl
    (fun hBelow ⟨hp', H', Rs, hc, hH', hA', t, ht, hb⟩ => ⟨hp', H', Rs, hc, hH',
      hA'.of_below hBelow hlive.1, t, ((hBelow p.1 hlive.2.2).2 p.2).trans ht, hb⟩) ?_
  intro store hlen hlens hBelow
  let db : ℕ × ℕ := (m.store.length, 0)
  have hdb : store.len db.1 = 2 * ss.length := by simpa [db] using hlens 0 (by simp)
  have hms := multiStepStable_isStableQRChain (τ := τ) (m := ⟨store, m.pos⟩) (a := a) (s := s)
    (ds := db) (ss := ss) hS hM hM.roundoff_nonneg hCmp hH hnu
    (by simp [Mem.Live, db, hlen]; omega) (hA.of_below hBelow hlive.1)
    (hBelow.readBlock_of hlive.2.1 hss) (by simp [hdb, db])
    has (Fp.disj_inBlock_of_ne (by dsimp [db]; omega))
    (Fp.disj_inBlock_of_ne (by dsimp [db]; omega))
  refine hms.frame_seq_le rfl rfl (by simp [Mem.Live, db, hlen]; omega)
    (sup_le (le_sup_left.trans le_sup_left) (Fp.inBlock_le_sup_above le_rfl)) ?_
  intro μ₁ hfr₁ ⟨hp₁, H', Rs, hc, hH', hA₁, hD₁⟩
  have hRs : Rs.length = ss.length := by
    have := Store.length_of_readBlock hD₁
    simp at this
    omega
  have hp₀ : p.2 < μ₁.store.len p.1 := by
    rw [hfr₁.len_eq, (hBelow p.1 hlive.2.2).1]; exact hp
  have hct := comptau_writes (τ := τ) (μ := μ₁) (ds := db) (p := p) hS hM hc
    (by positivity [hM.roundoff_nonneg]) hC hd hH0 hV hHV hκ hs hdist hxu hu hRs hD₁
    (by simp [Mem.Live, hfr₁.length_eq, db, hlen]; omega) hp₀
    (Fp.disj_inBlock_of_ne (by dsimp [db]; omega))
  refine (hct.in_frame rfl rfl (by simp [Mem.Live, hfr₁.length_eq, db, hlen]; omega)).mono
    (le_sup_right.trans le_sup_left) ?_
  intro μ₂ hfr₂ ⟨hp₂, t, ht, hb⟩
  exact ⟨hp₂.trans hp₁, H', Rs, hc, hH',
    hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) hap.symm hA₁, t, ht, hb⟩

/-- **The comparison routine of `Find`** ([BanksGarzaVargasSrivastava2022, Lemmas 3.9 and 5.1]):
copy $\mathbf{H}$ from `A`, and the $h$ shifts $l$ from `S` repeated $e$ times
(`NLAlib.ShiftedQR.repeatBlock`), to scratch, and run `NLAlib.ShiftedQR.stepComptau` with the
shifts $l^e$ on the copy, storing in `P` the rounded product of the moduli of the $he$ last
triangular diagonal entries. The interface is `[d, h, e] (A, S) → (P)`; the copy and the shift
list are scoped. -/
def comptauHalf : Stmt O Q := ops% [d, h, e] (A, S) → (P) {
  let W ← alloc (2 * (d * d));
  let SS ← alloc (2 * (h * e));
  run (unaryMap (Has.inj ScalarOp.copy)) [2 * (d * d)] (A, W);
  run (repeatBlock (O := O) (Q := Q)) [2 * h, e] (S, SS);
  run (stepComptau (O := O) (Q := Q)) [d, h * e] (W, SS, W, P)
}

/-- **`comptauHalf` satisfies the contract of `Find`'s comparison values**
([BanksGarzaVargasSrivastava2022, Lemmas 3.9 and 5.1]): let $\mathbf{H}$ of order $n + 1$ be
upper Hessenberg and nonzero, $\mathbf{H}\mathbf{V} = \mathbf{V}\mathbf{D}$ with
$\kappa(\mathbf{V}) \le \kappa$, the $k$ shifts in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$ and at
distance at least $d > 0$ from every eigenvalue, and the machine the standard model with exact
comparisons, $(n + 1)\boldsymbol{u} \le 1/2500$, $30000(k/2 + 1)\boldsymbol{u} \le 1$ and
$$300(n + 1)^2\boldsymbol{u} \le (8004\kappa)^{-1}
  \Bigl(\frac{d}{(2 + 2C)\|\mathbf{H}\|_2}\Bigr)^{k/2}.$$
Then for every half $l$ of $h$ shifts and exponent $e$ with $2he = k$, `comptauHalf` stores a $t$
within $0.0011$ (indeed $0.001$), relatively, of
$\|\mathbf{e}_n^{\mathsf T}p_l(\mathbf{H})^{-e}\|^{-1}$: `NLAlib.ShiftedQR.stepComptau_writes`
with the $he$ shifts $l^e$, and $p_{l^e} = p_l^{\,e}$ (`NLAlib.shiftPoly_flatten_replicate`).
For odd $k$ the contract is empty; $k/2$ is the natural quotient. -/
theorem comptauHalf_isHalfTau {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hCmp : IsCmp id I) {n : ℕ} {C κ d : ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ev : Fin (n + 1) → ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hH0 : H ≠ 0) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal ev) (hκ : pseudoConditionNumber V ≤ κ) (hC : 0 ≤ C)
    (hd : 0 < d) (hs : ∀ s ∈ shifts, ‖s‖ ≤ C * specNorm H)
    (hdist : ∀ s ∈ shifts, ∀ i, d ≤ ‖ev i - s‖)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hu : 30000 * (((shifts.length / 2 : ℕ) : ℝ) + 1) * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (8004 * κ)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ (shifts.length / 2)) :
    IsHalfTau H shifts comptauHalf I := by
  intro a h e hah hhe τ μ A S P hl hA hSh hP hPA hPS
  set l := (shifts.drop a).take h with hl_def
  set L := (List.replicate e l).flatten with hL_def
  have hll : l.length = h := by simp only [l, List.length_take, List.length_drop]; omega
  have hLlen : L.length = h * e := by
    simp [L, List.length_flatten, List.map_replicate, List.sum_replicate, hll, mul_comm]
  have hhalf : L.length = shifts.length / 2 := by omega
  have hmem : ∀ s ∈ L, s ∈ shifts := fun s hs' => by
    obtain ⟨l', hl', hsl⟩ := List.mem_flatten.mp hs'
    rw [(List.mem_replicate.mp hl').2] at hsl
    exact List.mem_of_mem_drop (List.mem_of_mem_take hsl)
  have hlive : A.1 < μ.store.length ∧ S.1 < μ.store.length ∧ P.1 < μ.store.length := by
    simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0),
    .const 2 * (.var 1 * .var 2)] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2 * ((n + 1) * (n + 1)), 2 * (h * e)]) rfl
    (fun hBelow ⟨hp, t, ht, hb⟩ => ⟨hp, t, ((hBelow P.1 hlive.2.2).2 P.2).trans ht, hb⟩) ?_
  intro store hlen hlens hBelow
  let w : ℕ × ℕ := (μ.store.length, 0)
  let sb : ℕ × ℕ := (μ.store.length + 1, 0)
  have hw : store.len w.1 = 2 * ((n + 1) * (n + 1)) := by simpa [w] using hlens 0 (by simp)
  have hsb : store.len sb.1 = 2 * (h * e) := by simpa [sb] using hlens 1 (by simp)
  have hwF : Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ≤
      Store.inBlock P.1 P.2 1 ⊔ Fp.above μ.store.length := Fp.inBlock_le_sup_above le_rfl
  have hl₀ : (⟨store, μ.pos⟩ : Mem ℝ).Live [A, S, P, w, sb] := by
    simp [Mem.Live, w, sb, hlen]; omega
  -- the copy of the matrix
  refine (copyMatrix_writes (τ := τ) (b := w) hS (hA.of_below hBelow hlive.1)
    (by rw [hw]; simp [w]) (Fp.disj_inBlock_of_ne (by dsimp [w]; omega))).frame_seq_le rfl rfl
    (hl₀.mono (by simp)) hwF ?_
  intro μ₁ hfr₁ ⟨hp₁, hW₁⟩
  -- the repeated shifts
  have hrep := repeatBlock_writes (τ := τ) (m := μ₁) (s := S) (t := sb) (e := e) hS
    (by simp [Mem.Live, hfr₁.length_eq, sb, hlen]; omega) (by dsimp [sb]; omega)
    (hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_ne (by dsimp [w]; omega))
      (hBelow.readBlock_of hlive.2.1 hSh))
    (by rw [hfr₁.len_eq, hsb]; dsimp [sb]; rw [Nat.mul_assoc]; omega)
  rw [Nat.mul_assoc, ← flatMap_flatten_replicate, ← hLlen] at hrep
  refine hrep.frame_seq_le rfl rfl (by simp [Mem.Live, hfr₁.length_eq, sb, hlen]; omega)
    (by rw [hLlen]; exact Fp.inBlock_le_sup_above (by dsimp [sb]; omega)) ?_
  intro μ₂ hfr₂ ⟨hp₂, hSS₂⟩
  -- the rounded steps and `comptau`
  have hst := stepComptau_writes (τ := τ) (m := μ₂) (a := w) (s := sb) (p := P) (ss := L) hS hM
    hCmp hH hH0 hV hHV hκ hC hd (fun s hs' => hs s (hmem s hs'))
    (fun s hs' => hdist s (hmem s hs')) hnu (by rw [hhalf]; exact hu)
    (by rw [hhalf]; exact hxu)
    (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq, w, sb, hlen]; omega)
    (hfr₂.keep (Store.readsOnly_readBlock _ _ _ _)
      (Fp.disj_inBlock_of_ne (by dsimp [w, sb]; omega)) hW₁) hSS₂
    (by rw [hfr₂.len_eq, hfr₁.len_eq, (hBelow P.1 hlive.2.2).1]; exact hP)
    (Fp.disj_inBlock_of_ne (by dsimp [w, sb]; omega)) (Fp.disj_inBlock_of_ne (by dsimp [w]; omega))
  rw [hLlen] at hst
  refine (hst.in_frame rfl rfl
    (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq, w, sb, hlen]; omega)).mono
    (sup_le hwF le_sup_left) ?_
  intro μ₃ _ ⟨hp₃, _, _, _, _, _, t, ht, hb⟩
  rw [hL_def, shiftPoly_flatten_replicate, map_pow, ← Matrix.inv_pow'] at hb
  refine ⟨hp₃.trans (hp₂.trans hp₁), t, ht, hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr (norm_nonneg _))

end HalfTau

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- The comparison values of one level of `Find` with the routine `Tau`: the first half's value
in `R[4]`, the second half's in `R[3]` (so that the exact decision
`NLAlib.ShiftedQR.findRitzDecision`, which keeps the first half when the word at `R[4]` is at
most the one at `R[3]`, keeps the half with the smaller value, the first on a tie). The interface
is
`[d, k, a, h, e] (H, SS, R) → (R)`. -/
def findRoundedNorms (Tau : Stmt O Q) : Stmt O Q :=
  ops% [d, k, a, h, e] (H, SS, R) → (R) {
    run Tau [d, h, e] (H, SS[2 * a], R[4]);
    run Tau [d, h, e] (H, SS[2 * (a + h)], R[3])
  }

/-- One level of `Find` with the routine `Tau`: read the window start, half length and
exponent, compute the two values, and decide. The interface is `[d, k] (H, SS, R) → (R)`. -/
def findRoundedLevel (Tau : Stmt O Q) : Stmt O Q := ops% [d, k] (H, SS, R) → (R) {
  let a ← index (Has.inj IdxTst.toNat) (R) ≤ k;
  let h ← index (Has.inj IdxTst.toNat) (R[1]) ≤ k;
  let e ← index (Has.inj IdxTst.toNat) (R[2]) ≤ k;
  run (findRoundedNorms Tau) [d, k, a, h, e] (H, SS, R, R);
  run findRitzDecision [a, h, e] (R, R)
}

/-- `Find` with the routine `Tau` and six caller-owned search words: initialize the window,
run `m` levels, copy the selected shift. The interface is `[d, m, k] (H, SS, R) → (Center)`. -/
def findRoundedWithScratch (Tau : Stmt O Q) : Stmt O Q :=
  ops% [d, m, k] (H, SS, R) → (Center) {
    run findRitzInitialize [k] (R, R);
    for level < m {
      run (findRoundedLevel Tau) [d, k] (H, SS, R, R)
    };
    run findRitzCopy [k] (SS, R, Center)
  }

/-- **`Find` in floating point** ([BanksGarzaVargasSrivastava2022, Lemma 5.1]): the binary
search over the $k = 2^m$ shifts at `SS` for the matrix at `H`, comparing the halves by the
routine `Tau`, with six scoped search words; the selected shift is written as a pair to
`Center`. The interface is `[d, m, k] (H, SS) → (Center)`. -/
def findRounded (Tau : Stmt O Q) : Stmt O Q := ops% [d, m, k] (H, SS) → (Center) {
  let R ← alloc 6;
  run (findRoundedWithScratch Tau) [d, m, k] (H, SS, R, Center)
}

/-! ### Index words with exact natural literals -/

omit [Has ScalarOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- A dimension literal up to an exact bound stores the natural as an exact real word. The rule for
one call of the operation. -/
private theorem writes_indexNat_of_exactNatLit {M : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit M I) {B : ℕ} (hNat : IsExactNatLit id M B) {τ : Tape ℝ} {m : Mem ℝ}
    {ρ : Env} {e : IExp} {out : Operand} {n : ℕ} {z : ℕ × ℕ}
    (he : e.eval ρ.idx = some n) (ho : out.eval ρ = some z) (hn : n ≤ B)
    (hz : z.2 < m.store.len z.1) :
    Writes .total I τ (.call (Has.inj IndexOp.lit) [e] [] [out]) ρ (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 = some (n : ℝ)) m := by
  have hlit : M.lit (n : ℚ) = (n : ℝ) := by simpa using hNat n hn
  exact (writes_indexLit hL he ho hz).mono le_rfl
    (fun _ _ h => ⟨h.1, by simpa only [hlit] using h.2⟩)

omit [Has ScalarOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The initialization of the search words with exact natural literals up to $k \ge 1$.
Shared by the trees of `NLAlib.ShiftedQR.scalarDecouple`, `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem findRitzInitialize_writes_of_exactNatLit {M : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit M I) {k : ℕ} (hNat : IsExactNatLit id M k) (hk : 1 ≤ k) {τ : Tape ℝ}
    {m : Mem ℝ} {r : ℕ × ℕ} (hr : r.2 + 3 ≤ m.store.len r.1) :
    Writes .total I τ findRitzInitialize (Env.frame [k] [r, r])
      (Store.inBlock r.1 r.2 3)
      (fun m' => m'.pos = m.pos ∧ SearchWords r 0 (k / 2) 1 m'.store) m := by
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (writes_indexNat_of_exactNatLit hL hNat rfl rfl (Nat.zero_le _)
    (by change r.2 < m.store.len r.1; omega)) (by fp_sub) fun m' hfr ⟨hp, hzero⟩ => ?_
  refine Writes.seq_le (writes_indexNat_of_exactNatLit hL hNat rfl rfl (Nat.div_le_self _ _)
    (by change r.2 + 1 < m'.store.len r.1; rw [hfr.len_eq]; omega))
    (by fp_sub) fun m'' hfr' ⟨hp', hhalf⟩ => ?_
  have hzero' := hfr'.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_inBlock_of_le (by omega)).symm hzero
  refine (writes_indexNat_of_exactNatLit hL hNat rfl rfl hk (by
    change r.2 + 2 < m''.store.len r.1
    rw [hfr'.len_eq, hfr.len_eq]
    omega)).mono (by fp_sub) ?_
  intro m''' hfr'' ⟨hp'', hone⟩
  refine ⟨hp''.trans (hp'.trans hp), ?_⟩
  exact ⟨hfr''.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_inBlock_of_le (by omega)).symm hzero',
    hfr''.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm hhalf,
    by simpa using hone⟩

omit [Has ScalarOp O] [Has IdxTst Q] in
/-- The decision of a level with exact natural literals up to $B$: it keeps the first half when
the value in `R[4]` is at most the one in `R[3]`, halves the half length and doubles the
exponent.
Shared by the trees of `NLAlib.ShiftedQR.scalarDecouple`, `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem findRitzDecision_writes_of_exactNatLit {M : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit M I) {B : ℕ} (hNat : IsExactNatLit id M B) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {a h e : ℕ} {r : ℕ × ℕ} {left right : ℝ}
    (hwords : SearchWords r a h e m.store)
    (hl : m.store.get r.1 (r.2 + 3) = some left)
    (hr : m.store.get r.1 (r.2 + 4) = some right)
    (hcap : r.2 + 3 ≤ m.store.len r.1) (hah : a + h ≤ B) (he : 2 * e ≤ B) :
    Writes .total I τ findRitzDecision (Env.frame [a, h, e] [r, r])
      (Store.inBlock r.1 r.2 3)
      (fun m' => m'.pos = m.pos ∧
        SearchWords r (if right ≤ left then a else a + h) (h / 2) (2 * e) m'.store) m := by
  classical
  have hrl := Store.lt_length_of_get hwords.1
  have hlive : m.Live [r, r] := by simpa [Mem.Live] using hrl
  have hch : Writes .total I τ findRitzChoice (Env.frame [a, h] [r, r])
      (Store.inBlock r.1 r.2 1) (fun m' => m'.pos = m.pos ∧ m'.store.get r.1 r.2 =
        some ((if right ≤ left then a else a + h : ℕ) : ℝ)) m := by
    have ht := hCmp.test_le (d := []) (m := m) (x := (r.1, r.2 + 4))
      (y := (r.1, r.2 + 3)) hr hl
    by_cases hc : right ≤ left
    · simp only [id_eq, hc, decide_true] at ht
      refine writes_ite rfl rfl ht ?_
      exact (Writes.skip ⟨rfl, by simpa only [if_pos hc] using hwords.1⟩).mono bot_le
        (fun _ _ h => h)
    · simp only [id_eq, hc, decide_false] at ht
      refine writes_ite rfl rfl ht ?_
      refine (writes_indexNat_of_exactNatLit hL hNat rfl rfl hah ?_).mono le_rfl ?_
      · exact Store.lt_len_of_get hwords.1
      · intro m' _ hp
        exact ⟨hp.1, by simpa only [if_neg hc] using hp.2⟩
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hch.in_frame rfl rfl hlive) (by fp_sub) fun m' hfr ⟨hp, hstart⟩ => ?_
  refine Writes.seq_le (writes_indexNat_of_exactNatLit hL hNat rfl rfl
    ((Nat.div_le_self _ _).trans (by omega)) (by
      change r.2 + 1 < m'.store.len r.1
      rw [hfr.len_eq]
      omega)) (by fp_sub) fun m'' hfr' ⟨hp', hhalf⟩ => ?_
  have hstart' := hfr'.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_inBlock_of_le (by omega)).symm hstart
  refine (writes_indexNat_of_exactNatLit hL hNat rfl rfl he (by
    change r.2 + 2 < m''.store.len r.1
    rw [hfr'.len_eq, hfr.len_eq]
    omega)).mono (by fp_sub) ?_
  intro m''' hfr'' ⟨hp'', hexp⟩
  refine ⟨hp''.trans (hp'.trans hp), ?_,
    hfr''.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm hhalf, hexp⟩
  have h := hfr''.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm hstart'
  by_cases hc : right ≤ left <;> simpa [hc] using h

/-! ### One level -/

/-- The inverse norm $\|\mathbf{e}_n^{\mathsf T}p_l(\mathbf{H})^{-e}\|^{-1}$ that a comparison
value approximates (local notation for the statements of this section). -/
local notation "τinv" H:max l:max e:max =>
  ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly l))⁻¹ ^ e) (Fin.last _))‖⁻¹

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The two comparison values of a level: the first half's in `R[4]`, the second half's in `R[3]`,
each within $0.0011$ of its inverse norm. Only these two words are written. A fragment: its tree
runs only inside the tree of `NLAlib.ShiftedQR.findRoundedLevel`. -/
private theorem findRoundedNorms_writes {I : Interp O Q ℝ} {Tau : Stmt O Q} {n : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hTau : IsHalfTau H shifts Tau I) {τ : Tape ℝ} {m : Mem ℝ} {k a h e : ℕ}
    {b ss r : ℕ × ℕ} (hB : HoldsMatrix b H m.store)
    (hSS : m.store.readBlock ss.1 ss.2 (2 * shifts.length) =
      some (shifts.flatMap fun z => [z.re, z.im]))
    (hk : shifts.length = k) (hah : a + 2 * h ≤ k) (hhe : 2 * (h * e) = k)
    (hrb : r.1 ≠ b.1) (hrs : r.1 ≠ ss.1) (hl : m.Live [b, ss, r, r])
    (hr : r.2 + 6 ≤ m.store.len r.1) :
    Writes .total I τ (findRoundedNorms Tau) (Env.frame [n + 1, k, a, h, e] [b, ss, r, r])
      (Store.inBlock r.1 (r.2 + 3) 2)
      (fun m' => m'.pos = m.pos ∧ ∃ tA tB : ℝ, m'.store.get r.1 (r.2 + 4) = some tA ∧
        m'.store.get r.1 (r.2 + 3) = some tB ∧
        |tA - τinv H ((shifts.drop a).take h) e| ≤ 0.0011 * τinv H ((shifts.drop a).take h) e ∧
        |tB - τinv H ((shifts.drop (a + h)).take h) e| ≤
          0.0011 * τinv H ((shifts.drop (a + h)).take h) e) m := by
  obtain ⟨hbl, hsl, hrl⟩ : b.1 < m.store.length ∧ ss.1 < m.store.length ∧
      r.1 < m.store.length := by simpa [Mem.Live] using hl
  have hlive : ∀ {o₁ o₂ : ℕ} {μ : Mem ℝ}, μ.store.length = m.store.length →
      μ.Live [b, (ss.1, o₁), (r.1, o₂)] := fun h => by simp [Mem.Live, h, hbl, hsl, hrl]
  have hA := hTau a h e (by omega) (by omega) τ m b (ss.1, ss.2 + 2 * a) (r.1, r.2 + 4)
    (hlive rfl) hB (readBlock_flatMap_pair_window hSS (by omega)) (by dsimp only; omega) hrb hrs
  unfold findRoundedNorms
  refine hA.frame_seq_le (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, Env.frame, IExp.eval]) (hlive rfl)
    (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  rintro m₁ hfr₁ ⟨hp₁, tA, htA, hA'⟩
  have hB₁ := hB.of_eqOff hfr₁ (Fp.disj_inBlock_of_ne hrb)
  have hSS₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_ne hrs) hSS
  have hBb := hTau (a + h) h e (by omega) (by omega) τ m₁ b (ss.1, ss.2 + 2 * (a + h))
    (r.1, r.2 + 3) (hlive hfr₁.length_eq) hB₁ (readBlock_flatMap_pair_window hSS₁ (by omega))
    (by dsimp only; rw [hfr₁.len_eq]; omega) hrb hrs
  refine (hBb.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, Env.frame, IExp.eval])
    (hlive hfr₁.length_eq)).mono (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  rintro m₂ hfr₂ ⟨hp₂, tB, htB, hB'⟩
  exact ⟨hp₂.trans hp₁, tA, tB, hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) htA, htB,
    hA', hB'⟩

/-- **The search state of `Find` after `j` of `m` levels**: the search words hold a window start
$a$, the half length $2^{m-j}/2$ and the exponent $2^j$; the window of $2^{m-j}$ shifts from $a$
fits in `shifts`; and every choice of the remaining levels on that window is a choice of `Find`
on all of `shifts`. -/
def FindRoundedState {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (shifts : List ℂ)
    (m j : ℕ) (r : ℕ × ℕ) (s : Store ℝ) : Prop :=
  ∃ a : ℕ, SearchWords r a (2 ^ (m - j) / 2) (2 ^ j) s ∧ a + 2 ^ (m - j) ≤ shifts.length ∧
    ∀ c : ℂ, IsFindRitzChoice H (m - j) (2 ^ j) ((shifts.drop a).take (2 ^ (m - j))) c →
      IsFindRitzChoice H m 1 shifts c

/-- The state reads only the search words. -/
theorem readsOnly_findRoundedState {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (shifts : List ℂ) (m j : ℕ) (r : ℕ × ℕ) :
    Store.ReadsOnly (Store.inBlock r.1 r.2 3) (FindRoundedState H shifts m j r) :=
  fun s s' hg ⟨a, hw, ha, hc⟩ => ⟨a, readsOnly_searchWords r _ _ _ s s' hg hw, ha, hc⟩

/-- One halving step of the state, from the two compared values. -/
private theorem findRoundedState_succ {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {shifts : List ℂ} {m j a p : ℕ} (hp : m - j = p + 1) (ha : a + 2 ^ (p + 1) ≤ shifts.length)
    (hc : ∀ c : ℂ, IsFindRitzChoice H (m - j) (2 ^ j) ((shifts.drop a).take (2 ^ (m - j))) c →
      IsFindRitzChoice H m 1 shifts c) {tA tB : ℝ}
    (hA : |tA - τinv H ((shifts.drop a).take (2 ^ p)) (2 ^ j)| ≤
      0.0011 * τinv H ((shifts.drop a).take (2 ^ p)) (2 ^ j))
    (hB : |tB - τinv H ((shifts.drop (a + 2 ^ p)).take (2 ^ p)) (2 ^ j)| ≤
      0.0011 * τinv H ((shifts.drop (a + 2 ^ p)).take (2 ^ p)) (2 ^ j)) :
    ∀ c : ℂ, IsFindRitzChoice H p (2 ^ (j + 1))
      ((shifts.drop (if tA ≤ tB then a else a + 2 ^ p)).take (2 ^ p)) c →
        IsFindRitzChoice H m 1 shifts c := by
  intro c hch
  have hsplit : (shifts.drop a).take (2 ^ (m - j)) =
      (shifts.drop a).take (2 ^ p) ++ (shifts.drop (a + 2 ^ p)).take (2 ^ p) := by
    rw [hp, pow_succ, mul_two, List.take_add, List.drop_drop]
  have hab : ((shifts.drop a).take (2 ^ p)).length =
      ((shifts.drop (a + 2 ^ p)).take (2 ^ p)).length := by
    simp only [List.length_take, List.length_drop, pow_succ] at ha ⊢; omega
  rw [pow_succ, mul_comm] at hch
  refine hc c ?_
  rw [hsplit, hp]
  by_cases hle : tA ≤ tB
  · rw [if_pos hle] at hch
    exact .left tA tB hab hA hB hle hch
  · rw [if_neg hle] at hch
    exact .right tA tB hab hA hB (not_le.mp hle) hch

omit [Has ScalarOp O] in
/-- **One level of `Find` with computed values**: from the state after `j < m` levels, the level
advances the search words to the state after `j + 1` levels, writing only the six search words. A
fragment: its tree runs only inside the tree of `NLAlib.ShiftedQR.findRoundedWithScratch`. -/
private theorem findRoundedLevel_writes {M : Machine ℝ} {I : Interp O Q ℝ} {Tau : Stmt O Q}
    (hL : IsIndexLit M I) (hCmp : IsCmp id I) (hQ : IsToNat id I) {n m k j : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hTau : IsHalfTau H shifts Tau I) (hNat : IsExactNatLit id M k) {τ : Tape ℝ} {μ : Mem ℝ}
    {b ss r : ℕ × ℕ} (hkm : k = 2 ^ m) (hk : shifts.length = k) (hj : j < m)
    (hB : HoldsMatrix b H μ.store)
    (hSS : μ.store.readBlock ss.1 ss.2 (2 * shifts.length) =
      some (shifts.flatMap fun z => [z.re, z.im]))
    (hst : FindRoundedState H shifts m j r μ.store)
    (hrb : r.1 ≠ b.1) (hrs : r.1 ≠ ss.1) (hl : μ.Live [b, ss, r, r])
    (hr : r.2 + 6 ≤ μ.store.len r.1) :
    Writes .total I τ (findRoundedLevel Tau) (Env.frame [n + 1, k] [b, ss, r, r])
      (Store.inBlock r.1 r.2 6)
      (fun μ' => μ'.pos = μ.pos ∧ FindRoundedState H shifts m (j + 1) r μ'.store) μ := by
  obtain ⟨a, hw, ha, hc⟩ := hst
  obtain ⟨p, hp⟩ : ∃ p, m - j = p + 1 := ⟨m - j - 1, by omega⟩
  have hh : 2 ^ (m - j) / 2 = 2 ^ p := by rw [hp, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  rw [hh] at hw
  rw [hp] at ha
  have hpj : 2 ^ p * 2 ^ j * 2 = k := by
    rw [hkm, ← pow_add, ← pow_succ]; congr 1; omega
  have hjk : 2 ^ (j + 1) ≤ k := hkm ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpk : 2 ^ (p + 1) ≤ k := by omega
  change Writes .total I τ (.bindIdx _ _ _ _) _ _ _ μ
  have hak : a ≤ k := by have := Nat.one_le_two_pow (n := p + 1); omega
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw.1 rfl hak ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw.2.1 rfl (by rw [pow_succ] at hpk; omega) ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw.2.2 rfl
    ((Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)).trans hjk) ?_
  have hnorms := findRoundedNorms_writes (τ := τ) (a := a) (h := 2 ^ p) (e := 2 ^ j) hTau hB hSS hk
    (by rw [pow_succ] at ha; omega) (by rw [← hpj]; ring) hrb hrs hl hr
  change Writes .total I τ (.seq _ _) _ _ _ μ
  refine hnorms.frame_seq_le
    (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval]) hl
    (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  rintro μ₁ hfr₁ ⟨hp₁, tA, tB, htA, htB, hA, hB'⟩
  have hw₁ := hfr₁.keep (readsOnly_searchWords r _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm hw
  have hrl := Store.lt_length_of_get hw₁.1
  have hdec := findRitzDecision_writes_of_exactNatLit hL hNat hCmp (τ := τ) hw₁ htB htA
    (by rw [hfr₁.len_eq]; omega) (by rw [pow_succ] at ha; omega)
    (by rw [mul_comm, ← pow_succ]; exact hjk)
  refine (hdec.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (by simpa [Mem.Live] using hrl)).mono (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  rintro μ₂ _ ⟨hp₂, hw₂⟩
  have hmj : m - (j + 1) = p := by omega
  refine ⟨hp₂.trans hp₁, if tA ≤ tB then a else a + 2 ^ p, ?_, ?_, ?_⟩
  · rw [hmj, pow_succ 2 j, mul_comm]; exact hw₂
  · rw [hmj]; rw [pow_succ] at ha; split_ifs <;> omega
  · rw [hmj]; exact findRoundedState_succ hp (by omega) hc hA hB'

/-! ### The search -/

omit [Has IndexOp O] [Has CmpTst Q] in
/-- The final copy of the selected shift, from a block of pairs.
Shared by the trees of `NLAlib.ShiftedQR.scalarDecouple`, `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem findRitzCopy_writes_of_readBlock {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hQ : IsToNat id I) {τ : Tape ℝ} {m : Mem ℝ}
    {k a : ℕ} {ss r center : ℕ × ℕ} {shifts : List ℂ}
    (hSS : m.store.readBlock ss.1 ss.2 (2 * shifts.length) =
      some (shifts.flatMap fun z => [z.re, z.im])) (hk : shifts.length = k)
    (hA : m.store.get r.1 r.2 = some (a : ℝ)) (ha : a < k)
    (hsep : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * k)) (Store.inBlock center.1 center.2 2))
    (hCenter : center.2 + 2 ≤ m.store.len center.1) :
    Writes .total I τ findRitzCopy (Env.frame [k] [ss, r, center])
      (Store.inBlock center.1 center.2 2)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock center.1 center.2 2 =
        some [(shifts.getD a 0).re, (shifts.getD a 0).im]) m := by
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hA rfl (by omega) ?_
  have hgd : shifts.getD a 0 = shifts[a]'(by omega) := by
    simp [List.getD_eq_getElem?_getD, show a < shifts.length by omega]
  obtain ⟨hre, him⟩ := get_of_readBlock_flatMap_pair hSS (j := a) (by omega)
  rw [← hgd] at hre him
  have hlocal : Fp.Disj (Store.inBlock ss.1 (ss.2 + 2 * a) 2)
      (Store.inBlock center.1 center.2 2) :=
    hsep.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl
  have hsLive := Store.lt_length_of_get hre
  have hcLive := Store.lt_length_of_lt_len (show center.2 < m.store.len center.1 by omega)
  have hcopy := Writes.of_wp_eq_updBlock
    (Hermitian.wp_copyPair_of_disj (md := .total) (τ := τ)
      (x := (ss.1, ss.2 + 2 * a)) (z := center) hS hlocal hre (by simpa [Nat.add_assoc] using him)
      hCenter rfl)
  refine (hcopy.in_frame rfl rfl (by simp [Mem.Live]; omega)).mono le_rfl ?_
  rintro μ _ rfl
  exact ⟨rfl, Store.readBlock_updBlock_self (by simpa using hCenter)⟩

/-- **`Find` in floating point with six caller-owned search words**: the stored result is a choice
of `Find` with computed values. Shared by the trees of `NLAlib.ShiftedQR.findRounded` and
`NLAlib.ShiftedQR.shPrefix`. -/
private theorem findRoundedWithScratch_writes {M : Machine ℝ} {I : Interp O Q ℝ}
    {Tau : Stmt O Q} (hS : IsScalar M I) (hL : IsIndexLit M I) (hCmp : IsCmp id I)
    (hQ : IsToNat id I) {n m k : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {shifts : List ℂ} (hTau : IsHalfTau H shifts Tau I) (hNat : IsExactNatLit id M k)
    {τ : Tape ℝ} {μ : Mem ℝ} {b ss r z : ℕ × ℕ} (hkm : k = 2 ^ m) (hk : shifts.length = k)
    (hB : HoldsMatrix b H μ.store)
    (hSS : μ.store.readBlock ss.1 ss.2 (2 * shifts.length) =
      some (shifts.flatMap fun z => [z.re, z.im]))
    (hrb : r.1 ≠ b.1) (hrs : r.1 ≠ ss.1) (hl : μ.Live [b, ss, r, z])
    (hr : r.2 + 6 ≤ μ.store.len r.1)
    (hsep : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * k)) (Store.inBlock z.1 z.2 2))
    (hz : z.2 + 2 ≤ μ.store.len z.1) :
    Writes .total I τ (findRoundedWithScratch Tau) (Env.frame [n + 1, m, k] [b, ss, r, z])
      (Store.inBlock r.1 r.2 6 ⊔ Store.inBlock z.1 z.2 2)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ c : ℂ, μ'.store.readBlock z.1 z.2 2 = some [c.re, c.im] ∧
        IsFindRitzChoice H m 1 shifts c) μ := by
  obtain ⟨hbl, hsl, hrl, hzl⟩ : b.1 < μ.store.length ∧ ss.1 < μ.store.length ∧
      r.1 < μ.store.length ∧ z.1 < μ.store.length := by simpa [Mem.Live] using hl
  have hk1 : 1 ≤ k := hkm ▸ Nat.one_le_two_pow
  have hw := findRitzInitialize_writes_of_exactNatLit hL hNat hk1 (τ := τ) (m := μ) (r := r)
    (by omega)
  unfold findRoundedWithScratch
  refine hw.frame_seq_le rfl rfl (by simp [Mem.Live, hrl]) (by fp_sub) ?_
  rintro μ₁ hfr₁ ⟨hp₁, hw₁⟩
  -- the levels
  have hloop : Writes .total I τ (.loop (.var 1) (.frame [.var 0, .var 2]
      [⟨0, .var 3⟩, ⟨1, .var 4⟩, ⟨2, .var 5⟩, ⟨2, .var 5⟩] (findRoundedLevel Tau)))
      (Env.frame [n + 1, m, k] [b, ss, r, z]) (Store.inBlock r.1 r.2 6)
      (fun μ' => μ'.pos = μ.pos ∧ FindRoundedState H shifts m m r μ'.store) μ₁ := by
    refine (writes_loop rfl (fun _ => Store.inBlock r.1 r.2 6) (fun _ _ => le_rfl)
      (fun j μ' => μ'.pos = μ.pos ∧ FindRoundedState H shifts m j r μ'.store) ⟨hp₁, 0, ?_, ?_, ?_⟩
      ?_).mono le_rfl fun _ _ h => h
    · simpa [hkm] using hw₁
    · simp [hk, hkm]
    · intro c h
      simp only [Nat.sub_zero, pow_zero, List.drop_zero] at h
      rwa [List.take_of_length_le (by omega)] at h
    intro j hj μ' hfr ⟨hp', hst⟩
    have hB₁ := (hB.of_eqOff hfr₁ (Fp.disj_inBlock_of_ne hrb)).of_eqOff hfr
      (Fp.disj_inBlock_of_ne hrb)
    have hSS₁ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_ne hrs)
      (hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_ne hrs) hSS)
    have hlen : ∀ b, μ'.store.len b = μ.store.len b := fun b => by
      rw [hfr.len_eq, hfr₁.len_eq]
    have hlv : μ'.Live [b, ss, r, r] := by
      simp [Mem.Live, hfr.length_eq, hfr₁.length_eq, hbl, hsl, hrl]
    refine ((findRoundedLevel_writes (τ := τ) hL hCmp hQ hTau hNat hkm hk hj hB₁ hSS₁ hst hrb hrs
      hlv (by rw [hlen]; exact hr)).in_frame
        (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
        (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval]) hlv).mono
      le_rfl fun _ _ h => ⟨h.1.trans hp', h.2⟩
  refine Writes.seq_le hloop (by fp_sub) ?_
  rintro μ₂ hfr₂ ⟨hp₂, a, hw₂, ha₂, hc₂⟩
  simp only [Nat.sub_self, pow_zero] at hw₂ ha₂ hc₂
  have hSS₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_ne hrs)
    (hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_ne hrs) hSS)
  have hc := findRitzCopy_writes_of_readBlock hS hQ (τ := τ) hSS₂ hk hw₂.1 (by omega) hsep
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hz)
  refine (hc.in_frame rfl rfl
    (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq, hsl, hrl, hzl])).mono le_sup_right ?_
  rintro μ₃ _ ⟨hp₃, hread⟩
  refine ⟨hp₃.trans hp₂, _, hread, hc₂ _ ?_⟩
  have h1 : (shifts.drop a).take 1 = [shifts.getD a 0] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    have ha' : a < shifts.length := by omega
    simp [List.take_one, List.head?_drop, List.getElem?_eq_getElem ha']
  rw [h1]
  exact .single _ _

/-- `Find` in floating point selects a choice of `Find` with computed values: on a scalar
machine whose natural literals up to $k = 2^m$ are exact, with exact comparisons and index
conversion, a comparison routine `Tau` meeting `NLAlib.ShiftedQR.IsHalfTau` for $\mathbf{H}$
(of order $n + 1$, at `A`) and the $k$ shifts (as pairs at `SS`), the program
`NLAlib.ShiftedQR.findRounded` writes only the pair `Center`, keeps the tape position, and
stores there a shift $c$ with `NLAlib.IsFindRitzChoice H m 1 shifts c`. The shifts and `Center`
are disjoint views.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem findRounded_writes_choice {M : Machine ℝ} {I : Interp O Q ℝ} {Tau : Stmt O Q}
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hCmp : IsCmp id I) (hQ : IsToNat id I)
    {n m k : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hTau : IsHalfTau H shifts Tau I) (hNat : IsExactNatLit id M k) {τ : Tape ℝ} {μ : Mem ℝ}
    {b ss z : ℕ × ℕ} (hkm : k = 2 ^ m) (hk : shifts.length = k)
    (hB : HoldsMatrix b H μ.store)
    (hSS : μ.store.readBlock ss.1 ss.2 (2 * shifts.length) =
      some (shifts.flatMap fun z => [z.re, z.im]))
    (hl : μ.Live [b, ss, z])
    (hsep : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * k)) (Store.inBlock z.1 z.2 2))
    (hz : z.2 + 2 ≤ μ.store.len z.1) :
    Writes .total I τ (findRounded Tau) (Env.frame [n + 1, m, k] [b, ss, z])
      (Store.inBlock z.1 z.2 2)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ c : ℂ, μ'.store.readBlock z.1 z.2 2 = some [c.re, c.im] ∧
        IsFindRitzChoice H m 1 shifts c) μ := by
  obtain ⟨hbl, hsl, hzl⟩ : b.1 < μ.store.length ∧ ss.1 < μ.store.length ∧
      z.1 < μ.store.length := by simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 6] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [6]) rfl
    (fun hBelow ⟨hp, c, hc, hch⟩ => ⟨hp, c, (hBelow.readBlock hzl z.2 2).trans hc, hch⟩) ?_
  intro store hlen hlens hBelow
  let r : ℕ × ℕ := (μ.store.length, 0)
  have hr : store.len r.1 = 6 := by simpa [r] using hlens 0 (by simp)
  have hst : μ.store.length + 1 = store.length := by rw [hlen]; simp
  have hlv : (⟨store, μ.pos⟩ : Mem ℝ).Live [b, ss, r, z] := by
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨by omega, by omega, by simp only [r]; omega, by omega⟩
  have hbody := findRoundedWithScratch_writes (τ := τ) (μ := ⟨store, μ.pos⟩) (b := b) (ss := ss)
    (r := r) (z := z) hS hL hCmp hQ hTau hNat hkm hk (hB.of_below hBelow hbl)
    (hBelow.readBlock_of hsl hSS) (by simp only [r]; omega) (by simp only [r]; omega) hlv
    (by simp only [r] at hr ⊢; omega) hsep (by rw [(hBelow z.1 hzl).1]; exact hz)
  exact (hbody.in_frame rfl rfl hlv).mono
    (sup_le (Fp.inBlock_le_sup_above le_rfl) le_sup_left) (fun _ _ h => h)

/-- **`Find` in floating point is promising** ([BanksGarzaVargasSrivastava2022, Lemma 5.1],
corrected: $\kappa(\mathbf{V}) \le B$ is added to its requirements, and its $\log$ is
$\log_2$): let
$\mathbf{H}\mathbf{V} = \mathbf{V}\mathbf{D}$ with $\kappa(\mathbf{V}) \le B$, the
$k = 2^m$ shifts stored as pairs at `SS`, none an eigenvalue, and the comparison routine `Tau`
compute $\|\mathbf{e}_n^{\mathsf T}p_h(\mathbf{H})^{-e}\|^{-1}$ within the relative error
$0.0011$ for every half visited (`NLAlib.ShiftedQR.IsHalfTau`, for instance $e$ rounded steps
and the rounded product of the moduli of their last diagonal entries), on a scalar machine
whose natural literals up to $k$ are exact, with exact comparisons and index conversion. Then
`NLAlib.ShiftedQR.findRounded` writes only the pair `Center`, keeps the tape position, and
stores there a $(1.01B)^{4m/2^m}$-promising shift. The shifts and `Center` are disjoint
views.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem findRounded_writes {M : Machine ℝ} {I : Interp O Q ℝ} {Tau : Stmt O Q}
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hCmp : IsCmp id I) (hQ : IsToNat id I)
    {n m k : ℕ} {B : ℝ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {shifts : List ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e)
    (hκ : pseudoConditionNumber V ≤ B) (hne : ∀ r ∈ shifts, ∀ i, e i ≠ r)
    (hTau : IsHalfTau H shifts Tau I) (hNat : IsExactNatLit id M k) {τ : Tape ℝ} {μ : Mem ℝ}
    {b ss z : ℕ × ℕ} (hkm : k = 2 ^ m) (hk : shifts.length = k)
    (hB : HoldsMatrix b H μ.store)
    (hSS : μ.store.readBlock ss.1 ss.2 (2 * shifts.length) =
      some (shifts.flatMap fun z => [z.re, z.im]))
    (hl : μ.Live [b, ss, z])
    (hsep : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * k)) (Store.inBlock z.1 z.2 2))
    (hz : z.2 + 2 ≤ μ.store.len z.1) :
    Writes .total I τ (findRounded Tau) (Env.frame [n + 1, m, k] [b, ss, z])
      (Store.inBlock z.1 z.2 2)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ c : ℂ, μ'.store.readBlock z.1 z.2 2 = some [c.re, c.im] ∧
        IsPromisingRitzValue ((1.01 * B) ^ ((4 * m : ℝ) / 2 ^ m)) V e shifts c) μ :=
  (findRounded_writes_choice hS hL hCmp hQ hTau hNat hkm hk hB hSS hl hsep hz).mono le_rfl
    fun _ _ ⟨hp, c, hc, hch⟩ => ⟨hp, c, hc, hch.isPromisingRitzValue hV hHV hκ hne⟩


end NLAlib.ShiftedQR
