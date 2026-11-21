/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecouple
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveTermination
public import NLAlib.Eigensolvers.ShiftedQR.StableStepTermination
public import NLAlib.Matrix.QRIteration.StableStepForward
public import NLAlib.Matrix.FinitePrecision.GivensLogSlots

/-!
# `Decouple`: decoupling the last eigenvalue by a repeated shift

`Decouple` ([BanksGarzaVargasSrivastava2025, §4]) runs rounded QR steps with one shift
$\tilde\lambda$ close to an eigenvalue of large weight until the last subdiagonal entry is small:
after each step the bottom entry is scanned against the threshold word $t_L$, and the run stops
with the flag $0$ when it passes, with the flag $1$ at the cap $m_2$ (the paper's loop is
uncapped, its erratum P13). By inverse iteration (`NLAlib.exists_le_norm_subdiag_shiftedQR_pow`)
and the forward error of the rounded steps
(`NLAlib.IsStableQRChain.exists_norm_subdiag_le_of_dist`), a shift within $\beta' = \omega/20$ of
an eigenvalue of weight at least $p$ decouples within $m_2$ steps. The scan threshold is that of
the merged decoupling loop: $(1 + \boldsymbol{u})^2\omega^2 \le t_L$.

## Main definitions

* `NLAlib.SmallEig.decoupleLast`: the program `[N, m2] (H, Lam, Q) → (H, Fl)`.

## Main results

* `NLAlib.SmallEig.decoupleLast_writes_word`, `NLAlib.SmallEig.decoupleLast_spec`: the
  decoupling with its log and its unitary.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **`Decouple`** ([BanksGarzaVargasSrivastava2025, Proposition 4.3], capped): scan the last
subdiagonal entry of the order-$N$ matrix `H` with the threshold $t_L$ = `Q[7]`
(`NLAlib.ShiftedQR.bottomScan` at $k = 1$); while it does not pass, for at most $m_2$ rounds, one
rounded QR step with the shift `Lam` (`NLAlib.ShiftedQR.multiStepStable` at degree $1$) and a scan;
then the flag $0$ if the last scan passed, $1$ otherwise (`NLAlib.ShiftedQR.roundedDecoupleExit`).
Round $t$'s step records its rotations in slot $j_0 + t$ of the slotted log `Lg` (slot width
$w \ge N - 1$), validated at once (the step is committed). The interface is
`[N, m2, w, j0] (H, Lam, Q) → (H, Fl, Lg)`; the registers are scoped.
Algorithm: small-eig -/
def decoupleLast : Stmt O Q := ops% [N, m2, w, j0] (H, Lam, Qw) → (H, Fl, Lg) {
  let R ← alloc 5;
  let Ds ← alloc 2;
  run (bottomScan (O := O) (Q := Q)) [N, 1] (H, Qw[7], R);
  while j < m2, (Has.inj CmpTst.isZero) [] (R[3]) {
    run (multiStepStable (Op := O) (Tst := Q)) [N, 1, w, j0 + j] (H, Lam, H, Ds, Lg);
    run (slottedLogValidate (O := O) (Q := Q)) [w, j0 + j] (Lg);
    run (bottomScan (O := O) (Q := Q)) [N, 1] (H, Qw[7], R)
  } then {
    run (roundedDecoupleExit (O := O) (Q := Q)) [] (R, Fl)
  }
}

end Program

/-- The memory of a call of `NLAlib.SmallEig.decoupleLast` on $\mathbf{H}$ of order $n + 1$ with
the shift $\lambda$: the matrix at `h` (updated in place), the pair of $\lambda$ at `lam`, the words
`qs` at `qw` and room for the flag `f`, all live and apart. -/
def DecoupleInput {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ζ : ℂ) (qs : List ℝ)
    (h lam qw f : ℕ × ℕ) (μ : Mem ℝ) : Prop :=
  μ.Live [h, lam, qw, f] ∧ μ.Room [h, lam, qw, f] [2 * ((n + 1) * (n + 1)), 2, qs.length, 1] ∧
    Fp.Apart [h, lam, qw, f] [2 * ((n + 1) * (n + 1)), 2, qs.length, 1] ∧
    HoldsMatrix h H μ.store ∧ μ.store.readBlock lam.1 lam.2 2 = some [ζ.re, ζ.im] ∧
    μ.store.readBlock qw.1 qw.2 qs.length = some qs

/-- The scan state of `NLAlib.SmallEig.decoupleLast` at the registers `r`: the flag `r[3]` is $1$
and the last subdiagonal entry $h$ of $\mathbf{H}$ passed the threshold $t$,
$(1 - \boldsymbol{u})^2\lvert h\rvert^2 \le t$, or the flag is $0$ and it failed,
$t < (1 + \boldsymbol{u})^2\lvert h\rvert^2$. -/
def LastScan {n : ℕ} (u t : ℝ) (r : ℕ × ℕ) (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (s : Store ℝ) : Prop :=
  (s.get r.1 (r.2 + 3) = some 1 ∧
      (1 - u) ^ 2 * ‖H (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2 ≤ t) ∨
    (s.get r.1 (r.2 + 3) = some 0 ∧
      t < (1 + u) ^ 2 * ‖H (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2)

/-- The scan state reads only the flag. -/
theorem readsOnly_lastScan {n : ℕ} (u t : ℝ) (r : ℕ × ℕ)
    (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
    Store.ReadsOnly (Store.inBlock r.1 (r.2 + 3) 1) (LastScan u t r H) := by
  intro s s' hg hs
  have he : s'.get r.1 (r.2 + 3) = s.get r.1 (r.2 + 3) :=
    hg r.1 (r.2 + 3) ⟨rfl, le_rfl, by omega⟩
  unfold LastScan at hs ⊢
  rwa [he]

/-- The operands of the loop of `NLAlib.SmallEig.decoupleLast` at the order $n + 2$ with its
registers at the fresh buffers $L$ (the scan registers) and $L + 1$ (the diagonal words): the
store has $L + 2$ buffers, the matrix, the shift, the words and the flag lie below $L$, the shift
pair and the threshold word $t$ = `qs[7]` are stored, the registers and the flag have room, and
the matrix is apart from the shift, the threshold word and the flag. -/
def DecoupleLastCtx (n L : ℕ) (h lam qw f : ℕ × ℕ) (ζ : ℂ) (t : ℝ) (s : Store ℝ) : Prop :=
  s.length = L + 2 ∧ h.1 < L ∧ lam.1 < L ∧ qw.1 < L ∧ f.1 < L ∧
    s.readBlock lam.1 lam.2 2 = some [ζ.re, ζ.im] ∧ s.get qw.1 (qw.2 + 7) = some t ∧
    s.len L = 5 ∧ s.len (L + 1) = 2 ∧ f.2 < s.len f.1 ∧
    Fp.Disj (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))))
      (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock qw.1 (qw.2 + 7) 1 ⊔ Store.inBlock f.1 f.2 1)

/-- The operands of the loop survive the writes of a round (the matrix and the registers). -/
theorem DecoupleLastCtx.of_eqOff {n L : ℕ} {h lam qw f : ℕ × ℕ} {ζ : ℂ} {t : ℝ}
    {s s' : Store ℝ} (hc : DecoupleLastCtx n L h lam qw f ζ t s) {F : Fp}
    (hF : F ≤ Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock L 0 5 ⊔
      Store.inBlock (L + 1) 0 2) (hfr : s.EqOff F s') :
    DecoupleLastCtx n L h lam qw f ζ t s' := by
  obtain ⟨hlen, hh, hl, hq, hf, hlam, ht, hL, hL1, hfr', hd⟩ := hc
  have hD : ∀ {b o k : ℕ}, b < L → Fp.Disj (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))))
      (Store.inBlock b o k) → Fp.Disj F (Store.inBlock b o k) := fun hb hd' =>
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hd', Fp.disj_inBlock_of_ne (by omega)⟩,
      Fp.disj_inBlock_of_ne (by omega)⟩).mono hF le_rfl
  refine ⟨by have := hfr.length_eq; omega, hh, hl, hq, hf,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hD hl (hd.mono le_rfl
      (le_sup_left.trans le_sup_left))) hlam,
    hfr.keep (Store.readsOnly_get _ _ _) (hD hq (hd.mono le_rfl
      (le_sup_right.trans le_sup_left))) ht,
    by rw [hfr.len_eq]; exact hL, by rw [hfr.len_eq]; exact hL1, by rw [hfr.len_eq]; exact hfr',
    hd⟩

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has IdxTst Q] in
/-- The scan of the last subdiagonal entry (`NLAlib.ShiftedQR.bottomScan` at $k = 1$) of an
order-$(n + 2)$ matrix stores the scan state `NLAlib.SmallEig.LastScan`.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine`
and `NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem bottomScan_writes_lastScan {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 2)) (hC : IsCmp id I)
    {τ : Tape ℝ} {μ : Mem ℝ} {a t r : ℕ × ℕ} {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ}
    {thr : ℝ} (hH : HoldsMatrix a H μ.store) (ht : μ.store.get t.1 t.2 = some thr)
    (hl : μ.Live [a, t, r]) (hroom : r.2 + 5 ≤ μ.store.len r.1)
    (hA : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 2) * (n + 2)))))
    (hT : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock t.1 t.2 1)) :
    Writes .total I τ (bottomScan (O := O) (Q := Q)) (Env.frame [n + 2, 1] [a, t, r])
      (Store.inBlock r.1 r.2 5) (fun μ' => μ'.pos = μ.pos ∧ LastScan u thr r H μ'.store) μ := by
  refine (bottomScan_writes (n := n + 1) (k := 1) (τ := τ) hS hM hu hu1 hL hNat hC
    (by omega) hH ht hl hroom hA hT).mono le_rfl ?_
  rintro μ' - ⟨hp, ⟨h1, i, hi, -, hb⟩ | ⟨h0, hall⟩⟩
  · have hi' : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hi'
    exact ⟨hp, Or.inl ⟨h1, by simpa only [Fin.succ_last] using hb⟩⟩
  · have hb := hall (Fin.last n) (by simp only [Fin.val_last]; omega)
    rw [Fin.succ_last] at hb
    exact ⟨hp, Or.inr ⟨h0, hb⟩⟩

omit [Has ScalarOp O] [Has IdxTst Q] in
/-- The exit of `NLAlib.SmallEig.decoupleLast` (`NLAlib.ShiftedQR.roundedDecoupleExit`) from the
scan state `NLAlib.SmallEig.LastScan`: the flag $0$ with the scan bound, or the flag $1$ with the
scan flag $0$ and the failed scan.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine`
and `NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem roundedDecoupleExit_writes_lastScan {M : Machine ℝ} {I : Interp O Q ℝ} {u t : ℝ} {n : ℕ}
    (hL : IsIndexLit M I) (hC : IsCmp id I) (hNat : IsExactNatLit id M 1) {τ : Tape ℝ}
    {μ : Mem ℝ} {r f : ℕ × ℕ} {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ}
    (hs : LastScan u t r H μ.store) (hf : f.2 < μ.store.len f.1) :
    Writes .total I τ (roundedDecoupleExit (O := O) (Q := Q)) (Env.frame [] [r, f])
      (Store.inBlock f.1 f.2 1)
      (fun μ' => (μ'.store.get f.1 f.2 = some 0 ∧
          (1 - u) ^ 2 * ‖H (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2 ≤ t) ∨
        (μ'.store.get f.1 f.2 = some 1 ∧ μ.store.get r.1 (r.2 + 3) = some 0 ∧
          t < (1 + u) ^ 2 * ‖H (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2)) μ := by
  have h0 : M.lit ((0 : ℕ) : ℚ) = (0 : ℝ) := by simpa using hNat 0 (by omega)
  have h1 : M.lit ((1 : ℕ) : ℚ) = (1 : ℝ) := by simpa using hNat 1 le_rfl
  unfold roundedDecoupleExit
  rcases hs with ⟨hx, hb⟩ | ⟨hx, hb⟩
  · refine writes_ite (a := [(r.1, r.2 + 3)]) rfl rfl (hC.test_isPos hx) ?_
    rw [if_pos (by simp)]
    refine (writes_indexLit hL rfl rfl hf).mono le_rfl ?_
    rintro μ' - ⟨-, hF⟩
    exact Or.inl ⟨by rw [hF, h0], hb⟩
  · refine writes_ite (a := [(r.1, r.2 + 3)]) rfl rfl (hC.test_isPos hx) ?_
    rw [if_neg (by simp)]
    refine (writes_indexLit hL rfl rfl hf).mono le_rfl ?_
    rintro μ' - ⟨-, hF⟩
    exact Or.inr ⟨by rw [hF, h1], hx, hb⟩

/-- A chain by a named unitary extended by one step by $\mathbf{Q}_1$ is a chain by
$\mathbf{Q}\mathbf{Q}_1$. -/
private theorem chainBy_snoc {n : ℕ} {x : ℝ}
    {H H' H'' U U₁ R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ} {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)} {s : ℂ}
    (hc : IsStableQRChainBy x H ss H' Rs U)
    (hs : IsStableQRStepBy U₁ (x * (specNorm H' + ‖s‖)) H' s H'' R) :
    IsStableQRChainBy x H (ss ++ [s]) H'' (Rs ++ [R]) (U * U₁) := by
  induction hc with
  | nil K => simpa using IsStableQRChainBy.cons hs (.nil H'')
  | cons h _ ih => simpa [Matrix.mul_assoc] using IsStableQRChainBy.cons h (ih hs)

/-- A chain of one step by a named unitary is that step. -/
private theorem stepBy_of_chainBy_singleton {n : ℕ} {x : ℝ}
    {H H' G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s : ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)} (h : IsStableQRChainBy x H [s] H' Rs G) :
    ∃ R, IsStableQRStepBy G (x * (specNorm H + ‖s‖)) H s H' R := by
  cases h with
  | cons h t => cases t; exact ⟨_, by simpa using h⟩

omit [Has IdxTst Q] in
/-- One more rounded step with the shift $\lambda$ (`NLAlib.ShiftedQR.multiStepStable` at degree
$1$, recording its rotations in the pending slot of the log), from the ends of a stable chain
by a named unitary $\mathbf{Q}$: a chain of one more step by $\mathbf{Q}$ times the unitary of
the recorded entries. -/
private theorem multiStepStable_writes_by {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hC : IsCmp id I)
    (hL : IsIndexLit M I) {n i : ℕ} (hNat : IsExactNatLit id M (n + 1))
    (hnu : (n + 2 : ℝ) * u ≤ 1 / 2500) {H H' U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {ζ : ℂ}
    {Rs : List (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)}
    (hc : IsStableQRChainBy (300 * (n + 2) ^ 2 * u) H (List.replicate i ζ) H' Rs U)
    (hH' : IsUpperHessenberg H') {τ : Tape ℝ} {μ : Mem ℝ} {a s ds : ℕ × ℕ}
    (hl : μ.Live [a, s, ds]) (hA : HoldsMatrix a H' μ.store)
    (hs : μ.store.readBlock s.1 s.2 2 = some [ζ.re, ζ.im]) (hd : ds.2 + 2 ≤ μ.store.len ds.1)
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 2) * (n + 2)))) (Store.inBlock s.1 s.2 2))
    (had : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 2) * (n + 2)))) (Store.inBlock ds.1 ds.2 2))
    (hsd : Fp.Disj (Store.inBlock s.1 s.2 2) (Store.inBlock ds.1 ds.2 2))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] μ.store) (hj : LL.length < ns) (hw : n + 1 ≤ w)
    (hlgl : μ.Live [lg]) (hlgb : ∀ b ∈ [a, s, ds], b.1 ≠ lg.1) :
    Writes .total I τ (multiStepStable (Op := O) (Tst := Q))
      (Env.frame [n + 2, 1, w, LL.length] [a, s, a, ds, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock ds.1 ds.2 2 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ (H'' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
        (Rs' : List (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)) (es : List GivensEntry),
        es.length = n + 1 ∧ (∀ e ∈ es, e.1 + 1 < n + 2) ∧
          HoldsSlottedLog lg ns w LL es μ'.store ∧
        IsStableQRChainBy (300 * (n + 2) ^ 2 * u) H (List.replicate (i + 1) ζ) H'' Rs'
          (U * givensLog (n + 2) es) ∧
          IsUpperHessenberg H'' ∧ HoldsMatrix a H'' μ'.store) μ := by
  have hlgd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1 + 1) * (n + 1 + 1))) ⊔
        Store.inBlock s.1 s.2 (2 * [ζ].length) ⊔ Store.inBlock ds.1 ds.2 (2 * [ζ].length)) :=
    Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr
      ⟨Fp.disj_inBlock_of_ne (hlgb a (by simp)).symm,
        Fp.disj_inBlock_of_ne (hlgb s (by simp)).symm⟩,
      Fp.disj_inBlock_of_ne (hlgb ds (by simp)).symm⟩
  refine (multiStepStable_isStableQRChainBy (τ := τ) (ss := [ζ]) hS hM hu hC hL hNat hH'
    (by push_cast; linarith) le_rfl hlog hj (by simpa using hw)
    (by simp only [Mem.live_cons, Mem.live_nil, and_true] at hl hlgl ⊢
        exact ⟨hl.1, hl.2.1, hl.2.2, hlgl⟩) hA (by simpa using hs) (by simpa using hd) has had
    hsd hlgd).mono le_rfl ?_
  rintro μ' - ⟨hp, es, hes, hpl, hlog', H'', Rs', hc', hH'', hA'', -⟩
  have hx : (300 * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * u) = 300 * ((n : ℝ) + 2) ^ 2 * u := by
    push_cast; ring
  rw [hx] at hc'
  obtain ⟨R, hst⟩ := stepBy_of_chainBy_singleton hc'
  exact ⟨hp, H'', Rs ++ [R], es, by simpa using hes, hpl, hlog',
    by rw [List.replicate_succ']; exact chainBy_snoc hc hst, hH'', hA''⟩

omit [Has IdxTst Q] in
/-- One more rounded step with the shift $\lambda$ (`NLAlib.ShiftedQR.multiStepStable` at degree
$1$) extends a stable chain of $i$ steps with that shift to $i + 1$ steps.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine`
and `NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem multiStepStable_writes_replicate_succ {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hC : IsCmp id I)
    (hL : IsIndexLit M I) {n i : ℕ} (hNat : IsExactNatLit id M (n + 1))
    (hnu : (n + 2 : ℝ) * u ≤ 1 / 2500) {H H' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {ζ : ℂ}
    {Rs : List (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)}
    (hc : IsStableQRChain (300 * (n + 2) ^ 2 * u) H (List.replicate i ζ) H' Rs)
    (hH' : IsUpperHessenberg H') {τ : Tape ℝ} {μ : Mem ℝ} {a s ds : ℕ × ℕ}
    (hl : μ.Live [a, s, ds]) (hA : HoldsMatrix a H' μ.store)
    (hs : μ.store.readBlock s.1 s.2 2 = some [ζ.re, ζ.im]) (hd : ds.2 + 2 ≤ μ.store.len ds.1)
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 2) * (n + 2)))) (Store.inBlock s.1 s.2 2))
    (had : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 2) * (n + 2)))) (Store.inBlock ds.1 ds.2 2))
    (hsd : Fp.Disj (Store.inBlock s.1 s.2 2) (Store.inBlock ds.1 ds.2 2))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] μ.store) (hj : LL.length < ns) (hw : n + 1 ≤ w)
    (hlgl : μ.Live [lg]) (hlgb : ∀ b ∈ [a, s, ds], b.1 ≠ lg.1) :
    Writes .total I τ (multiStepStable (Op := O) (Tst := Q))
      (Env.frame [n + 2, 1, w, LL.length] [a, s, a, ds, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock ds.1 ds.2 2 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => ∃ (H'' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
        (Rs' : List (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)),
        IsStableQRChain (300 * (n + 2) ^ 2 * u) H (List.replicate (i + 1) ζ) H'' Rs' ∧
          IsUpperHessenberg H'' ∧ HoldsMatrix a H'' μ'.store ∧
        ∃ es : List GivensEntry, es.length = n + 1 ∧ HoldsSlottedLog lg ns w LL es μ'.store) μ := by
  have hlgd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1 + 1) * (n + 1 + 1))) ⊔
        Store.inBlock s.1 s.2 (2 * [ζ].length) ⊔ Store.inBlock ds.1 ds.2 (2 * [ζ].length)) :=
    Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr
      ⟨Fp.disj_inBlock_of_ne (hlgb a (by simp)).symm,
        Fp.disj_inBlock_of_ne (hlgb s (by simp)).symm⟩,
      Fp.disj_inBlock_of_ne (hlgb ds (by simp)).symm⟩
  refine (multiStepStable_isStableQRChainBy (τ := τ) (ss := [ζ]) hS hM hu hC hL hNat hH'
    (by push_cast; linarith) le_rfl hlog hj (by simpa using hw)
    (by simp only [Mem.live_cons, Mem.live_nil, and_true] at hl hlgl ⊢
        exact ⟨hl.1, hl.2.1, hl.2.2, hlgl⟩) hA (by simpa using hs) (by simpa using hd) has had
    hsd hlgd).mono le_rfl ?_
  rintro μ' - ⟨-, es, hes, -, hlog', H'', Rs', hc', hH'', hA'', -⟩
  have hx : (300 * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * u) = 300 * ((n : ℝ) + 2) ^ 2 * u := by
    push_cast; ring
  rw [hx] at hc'
  obtain ⟨R, hst⟩ := stepBy_of_chainBy_singleton hc'
  exact ⟨H'', Rs ++ [R], by rw [List.replicate_succ']; exact hc.snoc hst.isStableQRStep, hH'',
    hA'', es, by simpa using hes, hlog'⟩

omit [Has IdxTst Q] in
/-- The scan of `NLAlib.SmallEig.decoupleLast` from the operands of its loop
(`NLAlib.SmallEig.DecoupleLastCtx`) stores the scan state of the matrix at `h`.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine`
and `NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem bottomScan_writes_decoupleLastCtx {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 2)) (hC : IsCmp id I)
    {τ : Tape ℝ} {μ : Mem ℝ} {L : ℕ} {h lam qw f : ℕ × ℕ} {ζ : ℂ} {t : ℝ}
    {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} (hc : DecoupleLastCtx n L h lam qw f ζ t μ.store)
    (hW : HoldsMatrix h H μ.store) :
    Writes .total I τ (bottomScan (O := O) (Q := Q))
      (Env.frame [n + 2, 1] [h, (qw.1, qw.2 + 7), (L, 0)]) (Store.inBlock L 0 5)
      (fun μ' => μ'.pos = μ.pos ∧ LastScan u t (L, 0) H μ'.store) μ := by
  obtain ⟨hlen, hh, -, hq, -, -, ht, hL5, -⟩ := hc
  exact bottomScan_writes_lastScan hS hM hu hu1 hL hNat hC hW ht
    (by simp [Mem.Live, hlen]; omega) (by simp [hL5]) (Fp.disj_inBlock_of_ne (by omega))
    (Fp.disj_inBlock_of_ne (by omega))

/-- The history of the loop of `NLAlib.SmallEig.decoupleLast` after $i$ rounds: ends
$\widehat{\mathbf{H}}_k$, $k \le i$, of backward-stable chains (relative error
$300(n + 2)^2\boldsymbol{u}$) of $k$ steps with the shift $\lambda$ from $\mathbf{H}$, whose scans
failed for $k < i$, $t < (1 + \boldsymbol{u})^2\lvert h_k\rvert^2$; the last one upper Hessenberg,
at `h`, with its scan state at the registers `r`. -/
def DecoupleScans (u t : ℝ) {n : ℕ} (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (ζ : ℂ)
    (h r : ℕ × ℕ) (i : ℕ) (s : Store ℝ) : Prop :=
  ∃ Hs : ℕ → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ,
    (∀ k ≤ i, ∃ Rs, IsStableQRChain (300 * (n + 2) ^ 2 * u) H (List.replicate k ζ) (Hs k) Rs) ∧
    (∀ k < i, t < (1 + u) ^ 2 * ‖Hs k (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2) ∧
    IsUpperHessenberg (Hs i) ∧ HoldsMatrix h (Hs i) s ∧ LastScan u t r (Hs i) s

/-- A failed scan: the scan state with the flag $0$ gives
$t < (1 + \boldsymbol{u})^2\lvert h\rvert^2$. -/
theorem LastScan.lt_of_get {n : ℕ} {u t : ℝ} {r : ℕ × ℕ} {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ}
    {s : Store ℝ} (hs : LastScan u t r H s) (h0 : s.get r.1 (r.2 + 3) = some 0) :
    t < (1 + u) ^ 2 * ‖H (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2 := by
  rcases hs with ⟨h1, -⟩ | ⟨-, hb⟩
  · exact absurd (h1.symm.trans h0) (by simp)
  · exact hb

/-- The history of the loop of `NLAlib.SmallEig.decoupleLast` grows by a round: ends of chains
of $k \le i$ steps whose scans failed for $k \le i$, and one more step to an upper Hessenberg
$\widehat{\mathbf{H}}''$ at `h` with its scan state. -/
theorem DecoupleScans.succ {u t : ℝ} {n : ℕ} {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {ζ : ℂ}
    {h r : ℕ × ℕ} {i : ℕ} {s : Store ℝ} {Hs : ℕ → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ}
    (hch : ∀ k ≤ i, ∃ Rs, IsStableQRChain (300 * (n + 2) ^ 2 * u) H (List.replicate k ζ) (Hs k) Rs)
    (hfail : ∀ k ≤ i, t < (1 + u) ^ 2 * ‖Hs k (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2)
    {H'' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {Rs' : List (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)}
    (hc : IsStableQRChain (300 * (n + 2) ^ 2 * u) H (List.replicate (i + 1) ζ) H'' Rs')
    (hHess : IsUpperHessenberg H'') (hW : HoldsMatrix h H'' s) (hs : LastScan u t r H'' s) :
    DecoupleScans u t H ζ h r (i + 1) s := by
  refine ⟨fun k => if k ≤ i then Hs k else H'', fun k hk => ?_, fun k hk => ?_,
    by simpa using hHess, by simpa using hW, by simpa using hs⟩
  · rcases Nat.le_succ_iff.mp hk with hk | rfl
    · simpa [hk] using hch k hk
    · exact ⟨Rs', by simpa using hc⟩
  · simpa [Nat.lt_succ_iff.mp hk] using hfail k (Nat.lt_succ_iff.mp hk)

omit [Has ScalarOp O] [Has IdxTst Q] in
/-- The exit of `NLAlib.SmallEig.decoupleLast` after $i \le m_2$ rounds, from the history
`NLAlib.SmallEig.DecoupleScans`, at the cap $m_2$ if the last scan failed: the flag $0$ with the
last scan bound, or the flag $1$ at $i = m_2$ with every scan failed; the matrix is kept.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine`
and `NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem roundedDecoupleExit_writes_decoupleScans {M : Machine ℝ} {I : Interp O Q ℝ} {u t : ℝ}
    (hL : IsIndexLit M I) (hC : IsCmp id I) {n : ℕ} (hNat : IsExactNatLit id M (n + 2))
    {i m₂ : ℕ} (hi : i ≤ m₂) {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {ζ : ℂ} {τ : Tape ℝ}
    {μ : Mem ℝ} {h r f : ℕ × ℕ} (hs : DecoupleScans u t H ζ h r i μ.store)
    (hcap : μ.store.get r.1 (r.2 + 3) = some 0 → i = m₂)
    (hhf : Fp.Disj (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2)))) (Store.inBlock f.1 f.2 1))
    (hf : f.2 < μ.store.len f.1) :
    Writes .total I τ (roundedDecoupleExit (O := O) (Q := Q)) (Env.frame [] [r, f])
      (Store.inBlock f.1 f.2 1) (fun μ' => ∃ (ℓ : ℕ)
        (Hs : ℕ → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ), ℓ ≤ m₂ ∧
        (∀ k ≤ ℓ, ∃ Rs, IsStableQRChain (300 * (n + 2) ^ 2 * u) H (List.replicate k ζ) (Hs k) Rs) ∧
        (∀ k < ℓ, t < (1 + u) ^ 2 * ‖Hs k (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2) ∧
        IsUpperHessenberg (Hs ℓ) ∧ HoldsMatrix h (Hs ℓ) μ'.store ∧
        ((μ'.store.get f.1 f.2 = some 0 ∧
            (1 - u) ^ 2 * ‖Hs ℓ (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2 ≤ t) ∨
          (μ'.store.get f.1 f.2 = some 1 ∧ ℓ = m₂ ∧
            t < (1 + u) ^ 2 * ‖Hs ℓ (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2))) μ := by
  obtain ⟨Hs, hch, hfail, hHess, hW, hsc⟩ := hs
  refine (roundedDecoupleExit_writes_lastScan hL hC (hNat.mono (by omega)) hsc hf).mono le_rfl
    fun _ hfr hF => ⟨i, Hs, hi, hch, hfail, hHess, hW.of_eqOff hfr hhf.symm, ?_⟩
  rcases hF with hF | ⟨hF, h0, hb⟩
  exacts [Or.inl hF, Or.inr ⟨hF, hcap h0, hb⟩]

omit [Has IdxTst Q] in
/-- The scan of `NLAlib.SmallEig.decoupleLast` on any matrix, from the operands of its loop
(`NLAlib.SmallEig.DecoupleLastCtx`), stores a word in the scan flag. -/
theorem bottomScan_terminates_decoupleLastCtx {M : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 2))
    (hC : IsCmp id I) {τ : Tape ℝ} {μ : Mem ℝ} {L : ℕ} {h lam qw f : ℕ × ℕ} {ζ : ℂ} {t : ℝ}
    {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} (hc : DecoupleLastCtx n L h lam qw f ζ t μ.store)
    (hW : HoldsMatrix h H μ.store) :
    Writes .total I τ (bottomScan (O := O) (Q := Q))
      (Env.frame [n + 2, 1] [h, (qw.1, qw.2 + 7), (L, 0)]) (Store.inBlock L 0 5)
      (fun μ' => ∃ x, μ'.store.get L 3 = some x) μ := by
  obtain ⟨hlen, hh, -, hq, -, -, ht, hL5, -⟩ := hc
  refine (bottomScan_terminates (n := n + 1) (k := 1) hS hL hNat hC (by omega) hW ht
    (by simp [Mem.Live, hlen]; omega) (by simp [hL5]) (Fp.disj_inBlock_of_ne (by omega))
    (Fp.disj_inBlock_of_ne (by omega))).mono le_rfl ?_
  rintro μ' - ⟨-, ⟨h1, -⟩ | ⟨h0, -⟩⟩
  exacts [⟨_, by simpa using h1⟩, ⟨_, by simpa using h0⟩]

/-- The operands of the loop survive writes away from the shift pair and the threshold word. -/
theorem DecoupleLastCtx.of_eqOff_of_disj {n L : ℕ} {h lam qw f : ℕ × ℕ} {ζ : ℂ} {t : ℝ}
    {s s' : Store ℝ} (hc : DecoupleLastCtx n L h lam qw f ζ t s) {F : Fp}
    (hd : Fp.Disj F (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock qw.1 (qw.2 + 7) 1))
    (hfr : s.EqOff F s') : DecoupleLastCtx n L h lam qw f ζ t s' := by
  obtain ⟨hlen, hh, hl, hq, hf, hlam, ht, hL, hL1, hfr', hd'⟩ := hc
  exact ⟨by have := hfr.length_eq; omega, hh, hl, hq, hf,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hd.mono le_rfl le_sup_left) hlam,
    hfr.keep (Store.readsOnly_get _ _ _) (hd.mono le_rfl le_sup_right) ht,
    by rw [hfr.len_eq]; exact hL, by rw [hfr.len_eq]; exact hL1, by rw [hfr.len_eq]; exact hfr',
    hd'⟩

/-- The log of `NLAlib.SmallEig.decoupleLast` after $i$ rounds, with the unitary of its entries:
$i$ accepted slots `Ls` after the closed slots `LL`, planes below $n + 1$, and the matrix
$\mathbf{H}_c$ at `h` the end of a stable chain of $i$ steps with the shift $\lambda$ by the
unitary `NLAlib.givensLog` of the entries. -/
private def DecoupleLogBy (x : ℝ) {n : ℕ} (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (ζ : ℂ)
    (h lg : ℕ × ℕ) (ns w : ℕ) (LL : List (Option (List GivensEntry))) (i : ℕ) (s : Store ℝ) :
    Prop :=
  ∃ (Ls : List (Option (List GivensEntry))) (Rs : List (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ))
    (Hc : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ), Ls.length = i ∧
    (∀ e ∈ slotEntries w Ls, e.1 + 1 < n + 2) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] s ∧
    HoldsMatrix h Hc s ∧
    IsStableQRChainBy x H (List.replicate i ζ) Hc Rs (givensLog (n + 2) (slotEntries w Ls))

/-- The outcome of `NLAlib.SmallEig.decoupleLast` (the postcondition of
`NLAlib.SmallEig.decoupleLast_writes_scans` without the log). -/
private def DecoupleLastScansPost (u t : ℝ) {n : ℕ} (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (ζ : ℂ) (h f : ℕ × ℕ) (m₂ : ℕ) (s : Store ℝ) : Prop :=
  ∃ (ℓ : ℕ) (Hs : ℕ → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ), ℓ ≤ m₂ ∧
    (∀ k ≤ ℓ, ∃ Rs, IsStableQRChain (300 * (n + 2) ^ 2 * u) H (List.replicate k ζ) (Hs k) Rs) ∧
    (∀ k < ℓ, t < (1 + u) ^ 2 * ‖Hs k (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2) ∧
    IsUpperHessenberg (Hs ℓ) ∧ HoldsMatrix h (Hs ℓ) s ∧
    ((s.get f.1 f.2 = some 0 ∧
        (1 - u) ^ 2 * ‖Hs ℓ (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2 ≤ t) ∨
      (s.get f.1 f.2 = some 1 ∧ ℓ = m₂ ∧
        t < (1 + u) ^ 2 * ‖Hs ℓ (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2))

omit [Has IdxTst Q] in
/-- **One round of `NLAlib.SmallEig.decoupleLast` with its log**: after a failed scan, one rounded
step (recorded in the pending slot), the validation of the slot and a scan extend the history
`NLAlib.SmallEig.DecoupleScans` and its log by a round. -/
private theorem decoupleLast_round_by {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hC : IsCmp id I) {n : ℕ} (hNat : IsExactNatLit id M (n + 2))
    (hnu : (n + 2 : ℝ) * u ≤ 1 / 2500) {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {ζ : ℂ}
    {τ : Tape ℝ} {ρ : Env} {μ : Mem ℝ} {L i : ℕ} {h lam qw f lg : ℕ × ℕ} {t : ℝ} {ns w : ℕ}
    {LL : List (Option (List GivensEntry))} {dsM dsV dsS : List IExp}
    {asM asV asS : List Operand}
    (hdM : IExp.evalList ρ.idx dsM = some [n + 2, 1, w, LL.length + i])
    (haM : Operand.evalList ρ asM = some [h, lam, h, (L + 1, 0), lg])
    (hdV : IExp.evalList ρ.idx dsV = some [w, LL.length + i])
    (haV : Operand.evalList ρ asV = some [lg])
    (hdS : IExp.evalList ρ.idx dsS = some [n + 2, 1])
    (haS : Operand.evalList ρ asS = some [h, (qw.1, qw.2 + 7), (L, 0)])
    (hlgL : lg.1 < L) (hlgb : ∀ b ∈ [h, lam, qw, f], b.1 ≠ lg.1)
    (hc : DecoupleLastCtx n L h lam qw f ζ t μ.store)
    (hs : DecoupleScans u t H ζ h (L, 0) i μ.store)
    (hlog : DecoupleLogBy (300 * (n + 2) ^ 2 * u) H ζ h lg ns w LL i μ.store)
    (h0 : μ.store.get L 3 = some 0) (hj : LL.length + i < ns) (hw : n + 1 ≤ w) :
    Writes .total I τ
      (.seq (.frame dsM asM (multiStepStable (Op := O) (Tst := Q)))
        (.seq (.frame dsV asV (slottedLogValidate (O := O) (Q := Q)))
          (.frame dsS asS (bottomScan (O := O) (Q := Q))))) ρ
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock L 0 5 ⊔
        Store.inBlock (L + 1) 0 2 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => DecoupleLastCtx n L h lam qw f ζ t μ'.store ∧
        DecoupleScans u t H ζ h (L, 0) (i + 1) μ'.store ∧
        DecoupleLogBy (300 * (n + 2) ^ 2 * u) H ζ h lg ns w LL (i + 1) μ'.store) μ := by
  obtain ⟨Hs, hch, hfail, hHess, hW, hsc⟩ := hs
  obtain ⟨Ls, Rs, Hc, hLs, hpl, hlg, hWc, hcb⟩ := hlog
  obtain rfl : Hc = Hs i := hWc.eq_storedMatrix.trans hW.eq_storedMatrix.symm
  have hfi := hsc.lt_of_get (by simpa using h0)
  have hlen := hc.1
  have hhL : h.1 < L := hc.2.1
  have hlamL : lam.1 < L := hc.2.2.1
  have hqL : qw.1 < L := hc.2.2.2.1
  have hgh : h.1 ≠ lg.1 := hlgb h (by simp)
  have hgl : lam.1 ≠ lg.1 := hlgb lam (by simp)
  have hgq : qw.1 ≠ lg.1 := hlgb qw (by simp)
  have hdc := hc.2.2.2.2.2.2.2.2.2.2
  have hRH : ∀ {o k : ℕ}, Fp.Disj (Store.inBlock L o k)
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2)))) := Fp.disj_inBlock_of_ne (by omega)
  have hlgh : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2)))) :=
    Fp.disj_inBlock_of_ne (hlgb h (by simp)).symm
  have hDL : ∀ {b o k : ℕ}, b ≠ lam.1 → b ≠ qw.1 →
      Fp.Disj (Store.inBlock b o k)
        (Store.inBlock lam.1 lam.2 2 ⊔ Store.inBlock qw.1 (qw.2 + 7) 1) :=
    fun h1 h2 => Fp.disj_sup_right.mpr ⟨Fp.disj_inBlock_of_ne h1, Fp.disj_inBlock_of_ne h2⟩
  have hlgD := hDL (b := lg.1) (o := lg.2) (k := ns * (1 + 5 * w)) (hlgb lam (by simp)).symm
    (hlgb qw (by simp)).symm
  refine (multiStepStable_writes_by hS hM hu hC hL (hNat.mono (by omega)) hnu hcb hHess
    (by simp [Mem.Live, hlen]; omega) hW hc.2.2.2.2.2.1 (by simp [hc.2.2.2.2.2.2.2.2.1])
    (hdc.mono le_rfl (le_sup_left.trans le_sup_left)) (Fp.disj_inBlock_of_ne (by omega))
    (Fp.disj_inBlock_of_ne (by omega)) hlg (by simp; omega) hw
    (by simp [Mem.Live, hlen]; omega) (by simp; omega)).frame_seq_le
    (by rw [List.length_append, hLs]; exact hdM) haM (by simp [Mem.Live, hlen]; omega)
    (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)) le_sup_right) ?_
  rintro μ₁ hf₁ ⟨-, H'', Rs', es, hes, hpl', hlg₁, hcb', hH'', hW''⟩
  have hc₁ := hc.of_eqOff_of_disj (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
    ⟨hdc.mono le_rfl le_sup_left, hDL (by omega) (by omega)⟩, hlgD⟩) hf₁
  refine ((slottedLogValidate_writes_of_exactNat hL (hNat.mono (by omega)) hlg₁
    (by simp; omega)).in_frame (by rw [List.length_append, hLs]; exact hdV) haV
    (by simp [Mem.Live, hc₁.1]; omega)).seq_le le_sup_right ?_
  rintro μ₂ hf₂ ⟨-, hlg₂⟩
  have hc₂ := hc₁.of_eqOff_of_disj hlgD hf₂
  have hW₂ := hW''.of_eqOff hf₂ hlgh
  refine ((bottomScan_writes_decoupleLastCtx hS hM hu hu1 hL hNat hC hc₂ hW₂).in_frame hdS haS
    (by simp [Mem.Live, hc₂.1]; omega)).mono
    ((le_sup_right.trans le_sup_left).trans le_sup_left) ?_
  rintro μ₃ hf₃ ⟨-, hs₃⟩
  refine ⟨hc₂.of_eqOff (le_sup_right.trans le_sup_left) hf₃,
    DecoupleScans.succ hch (fun k hk => (Nat.lt_or_eq_of_le hk).elim (hfail k)
      fun h' => h' ▸ hfi) hcb'.isStableQRChain hH'' (hW₂.of_eqOff hf₃ hRH) hs₃,
    Ls ++ [some es], Rs', H'', by simp [hLs],
    planes_slotEntries_append_some (by omega) hpl hpl', ?_, hW₂.of_eqOff hf₃ hRH,
    by rw [givensLog_slotEntries_append_some]; exact hcb'⟩
  rw [← List.append_assoc]
  exact hf₃.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
    (Fp.disj_inBlock_of_ne (by omega)) hlg₂

omit [Has ScalarOp O] [Has IdxTst Q] in
/-- The exit of `NLAlib.SmallEig.decoupleLast` after $i \le m_2$ rounds keeps the log. -/
private theorem decoupleLast_exit_by {M : Machine ℝ} {I : Interp O Q ℝ} {u t : ℝ}
    (hL : IsIndexLit M I) (hC : IsCmp id I) {n : ℕ} (hNat : IsExactNatLit id M (n + 2))
    {i m₂ : ℕ} (hi : i ≤ m₂) {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {ζ : ℂ} {τ : Tape ℝ}
    {μ : Mem ℝ} {L : ℕ} {h lam qw f lg : ℕ × ℕ} {ns w : ℕ} {LL : List (Option (List GivensEntry))}
    (hc : DecoupleLastCtx n L h lam qw f ζ t μ.store)
    (hs : DecoupleScans u t H ζ h (L, 0) i μ.store)
    (hlog : DecoupleLogBy (300 * (n + 2) ^ 2 * u) H ζ h lg ns w LL i μ.store)
    (hcap : μ.store.get L 3 = some 0 → i = m₂) (hlgf : f.1 ≠ lg.1) :
    Writes .total I τ (roundedDecoupleExit (O := O) (Q := Q)) (Env.frame [] [(L, 0), f])
      (Store.inBlock f.1 f.2 1)
      (fun μ' => DecoupleLastScansPost u t H ζ h f m₂ μ'.store ∧
        ∃ k ≤ m₂, DecoupleLogBy (300 * (n + 2) ^ 2 * u) H ζ h lg ns w LL k μ'.store) μ := by
  have hhf := hc.2.2.2.2.2.2.2.2.2.2.mono le_rfl le_sup_right
  obtain ⟨Ls, Rs, Hc, hLs, hpl, hlg, hWc, hcb⟩ := hlog
  refine (roundedDecoupleExit_writes_decoupleScans hL hC hNat hi hs
    (fun h0 => hcap (by simpa using h0)) hhf hc.2.2.2.2.2.2.2.2.2.1).mono le_rfl ?_
  intro μ' hfr hpost
  exact ⟨hpost, i, hi, Ls, Rs, Hc, hLs, hpl,
    hfr.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (Fp.disj_inBlock_of_ne hlgf) hlg,
    hWc.of_eqOff hfr hhf.symm, hcb⟩

omit [Has IdxTst Q] in
/-- `NLAlib.SmallEig.decoupleLast_writes_scans` with the log and the unitary of its entries
(the log of the rounds). -/
private theorem decoupleLast_writes_scansBy {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hL : IsIndexLit M I)
    (hC : IsCmp id I) {n m₂ : ℕ} (hNat : IsExactNatLit id M (n + 2))
    (hnu : (n + 2 : ℝ) * u ≤ 1 / 2500) {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {ζ : ℂ}
    {qs : List ℝ} (hqs : 8 ≤ qs.length) (hH : IsUpperHessenberg H) {τ : Tape ℝ} {μ : Mem ℝ}
    {h lam qw f : ℕ × ℕ} (hin : DecoupleInput H ζ qs h lam qw f μ)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] μ.store) (hj : LL.length + m₂ ≤ ns) (hw : n + 1 ≤ w)
    (hlgl : μ.Live [lg]) (hlgb : ∀ b ∈ [h, lam, qw, f], b.1 ≠ lg.1) :
    Writes .total I τ (decoupleLast (O := O) (Q := Q))
      (Env.frame [n + 2, m₂, w, LL.length] [h, lam, qw, h, f, lg])
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => DecoupleLastScansPost u (qs.getD 7 0) H ζ h f m₂ μ'.store ∧
        ∃ k ≤ m₂, DecoupleLogBy (300 * (n + 2) ^ 2 * u) H ζ h lg ns w LL k μ'.store) μ := by
  obtain ⟨hl, ⟨hhr, -, -, hfr, -⟩, ⟨dH, -, -, -⟩, hHs, hlam, hqw⟩ := hin
  simp only [Fp.blocks_cons, Fp.blocks_nil] at dH
  have hu1 : u ≤ 1 := by nlinarith
  have hh1 : h.1 < μ.store.length := hl h (by simp)
  have hl1 : lam.1 < μ.store.length := hl lam (by simp)
  have hq1 : qw.1 < μ.store.length := hl qw (by simp)
  have hf1 : f.1 < μ.store.length := hl f (by simp)
  have hlg1 : lg.1 < μ.store.length := hlgl lg (by simp)
  have hlgf : f.1 ≠ lg.1 := hlgb f (by simp)
  unfold decoupleLast
  change Writes .total I τ (Stmt.allocs [.const 5, .const 2] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [5, 2]) rfl
    (fun hBelow ⟨⟨ℓ, Hs, hℓ, hch, hfail, hHess, hW, hF⟩, k, hk, Ls, Rs, Hc, hLs, hpl, hlg, hWc,
      hcb⟩ => ⟨⟨ℓ, Hs, hℓ, hch, hfail, hHess, hW.of_below hBelow hh1,
        hF.imp (fun h' => ⟨hBelow.get_of hf1 h'.1, h'.2⟩)
          (fun h' => ⟨hBelow.get_of hf1 h'.1, h'.2⟩)⟩, k, hk, Ls, Rs, Hc, hLs, hpl,
        hBelow.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
          (fun b i g => by rw [g.1]; exact hlg1) hlg, hWc.of_below hBelow hh1, hcb⟩) ?_
  intro s₁ hlen hlens hBelow
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  set G := Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock L 0 5 ⊔
    Store.inBlock (L + 1) 0 2 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)) with hG
  have hc₁ : DecoupleLastCtx n L h lam qw f ζ (qs.getD 7 0) s₁ :=
    ⟨by omega, hh1, hl1, hq1, hf1, hBelow.readBlock_of hl1 hlam,
      hBelow.get_of hq1 (Store.get_of_readBlock hqw (by omega) 0),
      by simpa using hlens 0 (by simp), by simpa using hlens 1 (by simp),
      by rw [(hBelow f.1 hf1).1]; omega, dH.mono le_rfl (by fp_sub)⟩
  have hRH : ∀ {o k : ℕ}, Fp.Disj (Store.inBlock L o k)
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2)))) := Fp.disj_inBlock_of_ne (by omega)
  set Inv : ℕ → Mem ℝ → Prop := fun i μ' =>
    DecoupleLastCtx n L h lam qw f ζ (qs.getD 7 0) μ'.store ∧
      DecoupleScans u (qs.getD 7 0) H ζ h (L, 0) i μ'.store ∧
      DecoupleLogBy (300 * (n + 2) ^ 2 * u) H ζ h lg ns w LL i μ'.store with hInv
  have hR3 : Store.inBlock L 0 5 ≤ Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔
      Store.inBlock L 0 5 ⊔ Store.inBlock (L + 1) 0 2 := le_sup_right.trans le_sup_left
  have hH₁ := hHs.of_below hBelow hh1
  have hlog₁ : HoldsSlottedLog lg ns w LL [] s₁ :=
    hBelow.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
      (fun b i g => by rw [g.1]; exact hlg1) hlog
  refine (bottomScan_writes_decoupleLastCtx (τ := τ) (μ := ⟨s₁, μ.pos⟩) hS hM hu hu1 hL hNat hC
    hc₁ hH₁).frame_seq_le rfl rfl (by simp [Mem.Live, hlen]; omega)
    (fun b i hb => Or.inr (hb.1 ▸ le_rfl)) ?_
  rintro μ₁ hfr₁ ⟨-, hs₁⟩
  have hlogμ₁ : HoldsSlottedLog lg ns w LL [] μ₁.store :=
    hfr₁.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (Fp.disj_inBlock_of_ne (by omega)) hlog₁
  refine (writes_whileFuel (N := m₂) rfl (fun _ => G) (fun _ _ => le_rfl)
    (Store.inBlock f.1 f.2 1) Inv _ ⟨hc₁.of_eqOff hR3 hfr₁, ⟨fun _ => H,
      fun k hk => ⟨[], by obtain rfl : k = 0 := (by omega); exact .nil H⟩,
      fun k hk => absurd hk (Nat.not_lt_zero _), hH, hH₁.of_eqOff hfr₁ hRH, hs₁⟩,
      [], [], H, rfl, by simp [slotEntries],
      by rw [List.append_nil]; exact hlogμ₁, hH₁.of_eqOff hfr₁ hRH, .nil H⟩ ?_ ?_).mono ?_
    (fun _ _ h => h)
  · rintro i hi μ' - ⟨hc', hs', hlog'⟩
    obtain ⟨v, hv⟩ : ∃ v, μ'.store.get L 3 = some v := by
      obtain ⟨Hs', -, -, -, -, hsc⟩ := hs'
      rcases hsc with ⟨h1, -⟩ | ⟨h0, -⟩
      exacts [⟨_, by simpa using h1⟩, ⟨_, by simpa using h0⟩]
    refine ⟨_, (Interp.testAt_eq (a := [(L, 3)]) rfl rfl).trans (hC.test_isZero hv), ?_⟩
    dsimp only
    split_ifs with hz
    · have hv0 : v = 0 := by simpa using hz
      exact decoupleLast_round_by hS hM hu hu1 hL hC hNat hnu rfl rfl rfl rfl rfl rfl hlg1 hlgb
        hc' hs' hlog' (by rw [hv, hv0]) (by omega) hw
    · exact (decoupleLast_exit_by hL hC hNat hi.le hc' hs' hlog'
        (fun h0 => absurd (Option.some.inj (hv.symm.trans h0)) (by simpa using hz)) hlgf).in_frame
        rfl rfl (by simp [Mem.Live, hc'.1]; omega)
  · rintro μ' - ⟨hc', hs', hlog'⟩
    exact (decoupleLast_exit_by hL hC hNat le_rfl hc' hs' hlog' (fun _ => rfl) hlgf).in_frame
      rfl rfl (by simp [Mem.Live, hc'.1]; omega)
  · exact sup_le (sup_le (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
      (fun b i hb => Or.inr (hb.1 ▸ le_rfl))) (fun b i hb => Or.inr (hb.1 ▸ Nat.le_succ L)))
      (le_sup_right.trans le_sup_left)) (le_sup_right.trans (le_sup_left.trans le_sup_left))

omit [Has IdxTst Q] in
/-- `NLAlib.SmallEig.decoupleLast` with its scan history, on a scalar machine with the standard
model at $0 \le \boldsymbol{u}$, $(n + 2)\boldsymbol{u} \le 1/2500$, index literals, exact
natural literals up to $n + 2$ and exact comparisons: from `NLAlib.SmallEig.DecoupleInput` with an
upper Hessenberg $\mathbf{H}$ of order $n + 2$, the shift $\lambda$ and at least eight words, on
every tape, it writes only the matrix and the flag and, for some $\ell \le m_2$, stores the end
$\widehat{\mathbf{H}}_\ell$ (upper Hessenberg) of ends $\widehat{\mathbf{H}}_k$, $k \le \ell$, of
backward-stable chains (relative error $300(n + 2)^2\boldsymbol{u}$) of $k$ steps with the shift
$\lambda$ whose scans failed for $k < \ell$, $t_L < (1 + \boldsymbol{u})^2\lvert h_k\rvert^2$
($t_L$ = `qs[7]`, $h_k$ the last subdiagonal entry); and the flag $0$ with
$(1 - \boldsymbol{u})^2\lvert h_\ell\rvert^2 \le t_L$, or the flag $1$ at $\ell = m_2$ with
$t_L < (1 + \boldsymbol{u})^2\lvert h_\ell\rvert^2$.

Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem decoupleLast_writes_scans {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu : 0 ≤ u) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {n m₂ : ℕ} (hNat : IsExactNatLit id M (n + 2))
    (hnu : (n + 2 : ℝ) * u ≤ 1 / 2500) {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {ζ : ℂ}
    {qs : List ℝ} (hqs : 8 ≤ qs.length) (hH : IsUpperHessenberg H) {τ : Tape ℝ} {μ : Mem ℝ}
    {h lam qw f : ℕ × ℕ} (hin : DecoupleInput H ζ qs h lam qw f μ)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] μ.store) (hj : LL.length + m₂ ≤ ns) (hw : n + 1 ≤ w)
    (hlgl : μ.Live [lg]) (hlgb : ∀ b ∈ [h, lam, qw, f], b.1 ≠ lg.1) :
    Writes .total I τ (decoupleLast (O := O) (Q := Q))
      (Env.frame [n + 2, m₂, w, LL.length] [h, lam, qw, h, f, lg])
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => ∃ (ℓ : ℕ) (Hs : ℕ → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ), ℓ ≤ m₂ ∧
        (∀ k ≤ ℓ, ∃ Rs, IsStableQRChain (300 * (n + 2) ^ 2 * u) H (List.replicate k ζ) (Hs k) Rs) ∧
        (∀ k < ℓ, qs.getD 7 0 <
          (1 + u) ^ 2 * ‖Hs k (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2) ∧
        IsUpperHessenberg (Hs ℓ) ∧ HoldsMatrix h (Hs ℓ) μ'.store ∧
        ((μ'.store.get f.1 f.2 = some 0 ∧
            (1 - u) ^ 2 * ‖Hs ℓ (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2 ≤ qs.getD 7 0) ∨
          (μ'.store.get f.1 f.2 = some 1 ∧ ℓ = m₂ ∧ qs.getD 7 0 <
            (1 + u) ^ 2 * ‖Hs ℓ (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2)) ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length ≤ m₂ ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 2) ∧
              HoldsSlottedLog lg ns w (LL ++ Ls) [] μ'.store) μ :=
  (decoupleLast_writes_scansBy hS hM hu hL hC hNat hnu hqs hH hin hlog hj hw hlgl hlgb).mono le_rfl
    fun _ _ ⟨⟨ℓ, Hs, hℓ, hch, hfail, hHess, hW, hF⟩, _, hk, Ls, _, _, hLs, hpl, hlg, _, _⟩ =>
      ⟨ℓ, Hs, hℓ, hch, hfail, hHess, hW, hF, Ls, hLs ▸ hk, hpl, hlg⟩

omit [Has IdxTst Q] in
/-- `NLAlib.SmallEig.decoupleLast` on a scalar machine with the standard model at
$0 \le \boldsymbol{u}$, $(n + 2)\boldsymbol{u} \le 1/2500$, index literals, exact natural literals
up to $n + 2$ and exact comparisons: from `NLAlib.SmallEig.DecoupleInput` with an
upper Hessenberg $\mathbf{H}$ of order $n + 2$, the shift $\lambda$ and at least eight words, on
every tape, it writes only the matrix and the flag and stores the end $\widehat{\mathbf{H}}'$ of a
backward-stable chain (relative error $300(n + 2)^2\boldsymbol{u}$) of at most $m_2$ steps with the
shift $\lambda$, upper Hessenberg, and a flag $0$ or $1$; with the flag $0$ the last subdiagonal
entry $h$ of $\widehat{\mathbf{H}}'$ passed the scan,
$(1 - \boldsymbol{u})^2\lvert h\rvert^2 \le t_L$ for the word $t_L$ = `qs[7]`.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem decoupleLast_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu : 0 ≤ u) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {n m₂ : ℕ} (hNat : IsExactNatLit id M (n + 2))
    (hnu : (n + 2 : ℝ) * u ≤ 1 / 2500) {H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {ζ : ℂ}
    {qs : List ℝ} (hqs : 8 ≤ qs.length) (hH : IsUpperHessenberg H) {τ : Tape ℝ} {μ : Mem ℝ}
    {h lam qw f : ℕ × ℕ} (hin : DecoupleInput H ζ qs h lam qw f μ)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] μ.store) (hj : LL.length + m₂ ≤ ns) (hw : n + 1 ≤ w)
    (hlgl : μ.Live [lg]) (hlgb : ∀ b ∈ [h, lam, qw, f], b.1 ≠ lg.1) :
    Writes .total I τ (decoupleLast (O := O) (Q := Q))
      (Env.frame [n + 2, m₂, w, LL.length] [h, lam, qw, h, f, lg])
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => ∃ (ℓ : ℕ) (H' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
        (Rs : List (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)), ℓ ≤ m₂ ∧
        IsStableQRChain (300 * (n + 2) ^ 2 * u) H (List.replicate ℓ ζ) H' Rs ∧
        IsUpperHessenberg H' ∧ HoldsMatrix h H' μ'.store ∧
        ((μ'.store.get f.1 f.2 = some 0 ∧
            (1 - u) ^ 2 * ‖H' (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2 ≤ qs.getD 7 0) ∨
          μ'.store.get f.1 f.2 = some 1) ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length ≤ m₂ ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 2) ∧
              HoldsSlottedLog lg ns w (LL ++ Ls) [] μ'.store) μ :=
  (decoupleLast_writes_scans hS hM hu hL hC hNat hnu hqs hH hin hlog hj hw hlgl hlgb).mono le_rfl
    fun _ _ ⟨ℓ, Hs, hℓ, hch, _, hHess, hW, hF, hLs⟩ =>
      let ⟨Rs, hc⟩ := hch ℓ le_rfl
      ⟨ℓ, Hs ℓ, Rs, hℓ, hc, hHess, hW, hF.imp id fun h' => h'.1, hLs⟩

omit [Has IdxTst Q] in
/-- **`Decouple` decouples the last eigenvalue** ([BanksGarzaVargasSrivastava2025,
Proposition 4.3], capped; deterministic): on a scalar machine with the standard model at
$0 \le \boldsymbol{u} < 1$, index literals, exact natural literals up to $n + 2$ and exact
comparisons: let $\mathbf{H} \ne 0$ of order $n + 2$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$, the shift $\lambda$ with
$\lvert\lambda\rvert \le C\|\mathbf{H}\|_2$ ($C \ge 0$), at distance at least $\eta_1 > 0$ from
every $d_j$ and within $\beta'$ of an eigenvalue $d_i$ of weight $w_i \ge p > 0$,
$4\beta' \le \omega$, $1 \le m_2$, $B \le 2^{m_2}\sqrt p$, the scan threshold $t_L$ = `qs[7]` with
$(1 + \boldsymbol{u})^2\omega^2 \le t_L$, and with $x = 300(n + 2)^2\boldsymbol{u}$, for every
$\ell \le m_2$, $x \le (16B)^{-1}(\eta_1/((2 + 2C)\|\mathbf{H}\|_2))^\ell$ and
$(66 + 2C)B\|\mathbf{H}\|_2((2 + 2C)\|\mathbf{H}\|_2/\eta_1)^\ell\sqrt{n + 2}\,x \le \omega/2$. Then
from `NLAlib.SmallEig.DecoupleInput`, on every tape, the run writes only the matrix and the flag,
sets the flag to $0$, and stores an upper Hessenberg perturbed unitary similarity
$\widehat{\mathbf{H}}'$ of $\mathbf{H}$ with backward error
$(1 + C)\|\mathbf{H}\|_2((1 + x)^{m_2} - 1)$ whose last subdiagonal entry is at most
$t_L^{1/2}/(1 - \boldsymbol{u})$. -/
theorem decoupleLast_spec {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u < 1) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {n m₂ : ℕ} (hNat : IsExactNatLit id M (n + 2))
    {H V : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {d : Fin (n + 2) → ℂ} {ζ : ℂ}
    {B C p η₁ β' ω : ℝ} (hH : IsUpperHessenberg H) (hH0 : H ≠ 0) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hC0 : 0 ≤ C)
    (hζ : ‖ζ‖ ≤ C * specNorm H) (hη₁ : 0 < η₁) (hdist : ∀ j, η₁ ≤ ‖d j - ζ‖)
    {i : Fin (n + 2)} (hi : ‖ζ - d i‖ ≤ β') (hp : 0 < p) (hpi : p ≤ lastRowWeights V i)
    (hω : 4 * β' ≤ ω) (hm₂ : 1 ≤ m₂) (hm₂B : B ≤ 2 ^ m₂ * √p)
    (hxu : ∀ ℓ ≤ m₂, 300 * ((n : ℝ) + 2) ^ 2 * u ≤
      (16 * B)⁻¹ * (η₁ / ((2 + 2 * C) * specNorm H)) ^ ℓ)
    (hfwd : ∀ ℓ ≤ m₂, (66 + 2 * C) * B * specNorm H * ((2 + 2 * C) * specNorm H / η₁) ^ ℓ *
      √((n : ℝ) + 2) * (300 * ((n : ℝ) + 2) ^ 2 * u) ≤ ω / 2)
    {qs : List ℝ} (hqs : 8 ≤ qs.length) (htL : (1 + u) ^ 2 * ω ^ 2 ≤ qs.getD 7 0)
    {τ : Tape ℝ} {μ : Mem ℝ} {h lam qw f : ℕ × ℕ} (hin : DecoupleInput H ζ qs h lam qw f μ)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] μ.store) (hj : LL.length + m₂ ≤ ns) (hw : n + 1 ≤ w)
    (hlgl : μ.Live [lg]) (hlgb : ∀ b ∈ [h, lam, qw, f], b.1 ≠ lg.1) :
    Writes .total I τ (decoupleLast (O := O) (Q := Q))
      (Env.frame [n + 2, m₂, w, LL.length] [h, lam, qw, h, f, lg])
      (Store.inBlock h.1 h.2 (2 * ((n + 2) * (n + 2))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ (Ls : List (Option (List GivensEntry))) (H' : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
        Ls.length ≤ m₂ ∧ (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 2) ∧
        HoldsSlottedLog lg ns w (LL ++ Ls) [] μ'.store ∧
        IsPerturbedUnitarySimilarBy (givensLog (n + 2) (slotEntries w Ls)) H H'
          ((1 + C) * specNorm H * ((1 + 300 * ((n : ℝ) + 2) ^ 2 * u) ^ m₂ - 1)) ∧
        IsUpperHessenberg H' ∧ HoldsMatrix h H' μ'.store ∧
        (1 - u) * ‖H' (Fin.last (n + 1)) (Fin.last n).castSucc‖ ≤ √(qs.getD 7 0)) μ := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hx0 : 0 ≤ 300 * ((n : ℝ) + 2) ^ 2 * u := by positivity
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hnu : (n + 2 : ℝ) * u ≤ 1 / 2500 := by
    have h0 := hxu 0 (Nat.zero_le _)
    rw [pow_zero, mul_one] at h0
    have h16 : (16 * B)⁻¹ ≤ 1 / 16 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) (by linarith)
    have hn2 : (2 : ℝ) ≤ n + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith [mul_le_mul_of_nonneg_right hn2 (mul_nonneg (by linarith : (0:ℝ) ≤ n + 2) hu0)]
  refine (decoupleLast_writes_scansBy hS hM hu0 hL hC hNat hnu hqs hH hin hlog hj hw hlgl
    hlgb).mono le_rfl ?_
  rintro μ' - ⟨⟨ℓ, Hs, hℓ, hch, hfail, hHess, hW, hF⟩, k, hk, Ls, Rs, Hc, hLs, hpl, hlg, hWc, hcb⟩
  rcases hF with ⟨hF, hb⟩ | ⟨-, rfl, hb⟩
  · obtain rfl : Hc = Hs ℓ := hWc.eq_storedMatrix.trans hW.eq_storedMatrix.symm
    have hsh : ∀ s ∈ List.replicate k ζ, ‖s‖ ≤ C * specNorm H := fun s hs => by
      rw [List.eq_of_mem_replicate hs]; exact hζ
    refine ⟨hF, Ls, Hs ℓ, hLs ▸ hk, hpl, hlg,
      (hcb.isPerturbedUnitarySimilarBy (C := C) hx0 hsh).mono ?_, hHess, hW, ?_⟩
    · rw [List.length_replicate]
      have hpow := pow_le_pow_right₀ (show (1 : ℝ) ≤ 1 + 300 * ((n : ℝ) + 2) ^ 2 * u by linarith)
        hk
      exact mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (by linarith) (specNorm_nonneg H))
    · have hh := norm_nonneg (Hs ℓ (Fin.last (n + 1)) (Fin.last n).castSucc)
      rw [← Real.sqrt_sq (by nlinarith :
        0 ≤ (1 - u) * ‖Hs ℓ (Fin.last (n + 1)) (Fin.last n).castSucc‖)]
      exact Real.sqrt_le_sqrt (by rw [mul_pow]; exact hb)
  · exfalso
    obtain ⟨k, hk, hkω⟩ := IsStableQRChain.exists_norm_subdiag_le_of_dist (Hs := Hs)
      (fun k hk => hch k hk) hx0 hC0 hH hH0 hV hHV hκ hζ hη₁ hdist hi hp hpi hω hm₂ hm₂B
      (by exact_mod_cast hxu) (by exact_mod_cast hfwd)
    obtain ⟨-, hkm⟩ := Finset.mem_Icc.mp hk
    have hlt : qs.getD 7 0 <
        (1 + u) ^ 2 * ‖Hs k (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2 := by
      rcases Nat.lt_or_eq_of_le hkm with hk' | rfl
      exacts [hfail k hk', hb]
    have : (1 + u) ^ 2 * ‖Hs k (Fin.last (n + 1)) (Fin.last n).castSucc‖ ^ 2 ≤
        (1 + u) ^ 2 * ω ^ 2 := by
      gcongr
    linarith

end Theorems
end NLAlib.SmallEig
