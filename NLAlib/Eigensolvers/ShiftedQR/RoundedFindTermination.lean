/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedFind
public import NLAlib.Eigensolvers.ShiftedQR.StableStepTermination

/-!
# Termination of `Find` in floating point

The rounded binary search `NLAlib.ShiftedQR.findRounded` and its comparison routine
`NLAlib.ShiftedQR.comptauHalf` terminate on every matrix and every shift words, with no numerical
hypothesis on the machine: only the scalar, index-literal, comparison and conversion contracts
and exact natural literals up to the shift count are used.

## Main definitions

* `NLAlib.ShiftedQR.TerminatingHalfTau`: the termination contract of a comparison routine.
* `NLAlib.ShiftedQR.FindStoredState`: the stored words of the search after a level.

## Main results

* `NLAlib.ShiftedQR.stepComptau_terminates`: a degree $k$ rounded step and its `comptau`.
* `NLAlib.ShiftedQR.comptauHalf_terminates`, `NLAlib.ShiftedQR.comptauHalf_terminatingHalfTau`:
  the comparison routine terminates.
* `NLAlib.ShiftedQR.findRounded_terminates`: the search terminates.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-! ### Termination on any matrix -/

section Termination

omit [Has IdxTst Q] in
/-- `comptau` of a degree $k$ rounded step terminates on any matrix: on a scalar machine with
exact comparisons and the literal $0$ exact, from any matrix of order $n + 1$ at `A` and any $2k$
shift words at `S`, `NLAlib.ShiftedQR.stepComptau` writes only the matrix, `P` and the log, keeps
the tape position, leaves both stored and fills the pending slot $j$ of the log with $kn$ entries
with planes below $n$. The matrix is disjoint from the shifts and from `P`; the log from all of
them. -/
theorem stepComptau_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hzero : M.lit 0 = 0) (hCmp : IsCmp id I) (hL : IsIndexLit M I) {nmax : ℕ}
    (hNat : IsExactNatLit id M nmax) {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {xs : List ℝ} {a s p lg : ℕ × ℕ} (hn : n ≤ nmax)
    {ns w : ℕ} {L : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w L [] m.store) (hj : L.length < ns) (hw : k * n ≤ w)
    (hl : m.Live [a, s, p, lg]) (hA : HoldsMatrix a H m.store)
    (hss : m.store.readBlock s.1 s.2 (2 * k) = some xs) (hp : p.2 < m.store.len p.1)
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (hap : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock p.1 p.2 1))
    (hlgd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock p.1 p.2 1)) :
    Writes .total I τ stepComptau.body (Env.frame [n + 1, k, w, L.length] [a, s, a, p, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock p.1 p.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.pos = m.pos ∧
        (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ t, m'.store.get p.1 p.2 = some t) ∧
        ∃ es : List GivensEntry, es.length = k * n ∧ (∀ e ∈ es, e.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w L es m'.store) m :=
  sorry

/-- **A terminating comparison routine of `Find`** for the order $n + 1$ and $k$ shifts: for
every window start $a$, half length $h$ and exponent $e$ with $a + h \le k$ and $2he = k$, from
any matrix at `A` and any $2h$ shift words at `S`, on every tape, the run is total, writes only
the word `P` (in a buffer apart from `A` and `S`) and leaves it stored. -/
def TerminatingHalfTau (n k : ℕ) (Tau : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ (a h e : ℕ), a + h ≤ k → 2 * (h * e) = k →
    ∀ (τ : Tape ℝ) (μ : Mem ℝ) (A S P : ℕ × ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (xs : List ℝ), μ.Live [A, S, P] → HoldsMatrix A H μ.store →
      μ.store.readBlock S.1 S.2 (2 * h) = some xs →
      P.2 < μ.store.len P.1 → P.1 ≠ A.1 → P.1 ≠ S.1 →
      Writes .total I τ Tau.body (Env.frame [n + 1, h, e] [A, S, P]) (Store.inBlock P.1 P.2 1)
        (fun μ' => ∃ t, μ'.store.get P.1 P.2 = some t) μ

omit [Has IdxTst Q] in
/-- `comptauHalf` terminates on any matrix and any shift words: on a scalar machine with exact
comparisons and the literal $0$ exact, for every half length $h$ and exponent $e$ (zero
included), from any matrix of order $n + 1$ at `A` and any $2h$ words at `S`, on every tape,
`NLAlib.ShiftedQR.comptauHalf` writes only the word `P`, keeps the tape position and leaves the
word stored. -/
theorem comptauHalf_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hzero : M.lit 0 = 0) (hCmp : IsCmp id I) (hL : IsIndexLit M I) {n h e : ℕ}
    {τ : Tape ℝ} {μ : Mem ℝ}
    {A S P : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {xs : List ℝ}
    (hl : μ.Live [A, S, P]) (hA : HoldsMatrix A H μ.store)
    (hSh : μ.store.readBlock S.1 S.2 (2 * h) = some xs) (hP : P.2 < μ.store.len P.1) :
    Writes .total I τ comptauHalf.body (Env.frame [n + 1, h, e] [A, S, P])
      (Store.inBlock P.1 P.2 1) (fun μ' => μ'.pos = μ.pos ∧ ∃ t, μ'.store.get P.1 P.2 = some t)
      μ := sorry

omit [Has IdxTst Q] in
/-- The comparison routine of `Find` terminates on any matrix: on a scalar machine with
exact comparisons and the literal $0$ exact, `NLAlib.ShiftedQR.comptauHalf` meets
`NLAlib.ShiftedQR.TerminatingHalfTau` for every order and number of shifts. -/
theorem comptauHalf_terminatingHalfTau {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hzero : M.lit 0 = 0) (hCmp : IsCmp id I) (hL : IsIndexLit M I) (n k : ℕ) :
    TerminatingHalfTau n k comptauHalf I :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hl hA hSh hP _ _ =>
    (comptauHalf_terminates hS hzero hCmp hL hl hA hSh hP).mono le_rfl fun _ _ h => h.2

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The two comparison values of a level with a terminating routine are stored. -/
private theorem findRoundedNorms_terminates {I : Interp O Q ℝ} {Tau : Impl O Q} {n k : ℕ}
    (hTau : TerminatingHalfTau n k Tau I) {τ : Tape ℝ} {m : Mem ℝ} {a h e : ℕ}
    {b ss r : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {xs : List ℝ}
    (hB : HoldsMatrix b H m.store) (hSS : m.store.readBlock ss.1 ss.2 (2 * k) = some xs)
    (hah : a + 2 * h ≤ k) (hhe : 2 * (h * e) = k)
    (hrb : r.1 ≠ b.1) (hrs : r.1 ≠ ss.1) (hl : m.Live [b, ss, r, r])
    (hr : r.2 + 6 ≤ m.store.len r.1) :
    Writes .total I τ (findRoundedNorms Tau).body (Env.frame [n + 1, k, a, h, e] [b, ss, r, r])
      (Store.inBlock r.1 (r.2 + 3) 2)
      (fun m' => (∃ tA, m'.store.get r.1 (r.2 + 4) = some tA) ∧
        ∃ tB, m'.store.get r.1 (r.2 + 3) = some tB) m := by
  obtain ⟨hbl, hsl, hrl⟩ : b.1 < m.store.length ∧ ss.1 < m.store.length ∧
      r.1 < m.store.length := by simpa [Mem.Live] using hl
  have hlive : ∀ {o₁ o₂ : ℕ} {μ : Mem ℝ}, μ.store.length = m.store.length →
      μ.Live [b, (ss.1, o₁), (r.1, o₂)] := fun h => by simp [Mem.Live, h, hbl, hsl, hrl]
  have hA := hTau a h e (by omega) hhe τ m b (ss.1, ss.2 + 2 * a) (r.1, r.2 + 4) H _
    (hlive rfl) hB (Store.readBlock_sub hSS (by omega)) (by dsimp only; omega) hrb hrs
  unfold findRoundedNorms
  refine hA.frame_seq_le (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, Env.frame, IExp.eval]) (hlive rfl)
    (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  rintro m₁ hfr₁ ⟨tA, htA⟩
  have hB₁ := hB.of_eqOff hfr₁ (Fp.disj_inBlock_of_ne hrb)
  have hSS₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_ne hrs) hSS
  have hBb := hTau (a + h) h e (by omega) hhe τ m₁ b (ss.1, ss.2 + 2 * (a + h))
    (r.1, r.2 + 3) H _ (hlive hfr₁.length_eq) hB₁ (Store.readBlock_sub hSS₁ (by omega))
    (by dsimp only; rw [hfr₁.len_eq]; omega) hrb hrs
  refine (hBb.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, Env.frame, IExp.eval])
    (hlive hfr₁.length_eq)).mono (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  rintro m₂ hfr₂ ⟨tB, htB⟩
  exact ⟨⟨tA, hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) htA⟩, tB, htB⟩

/-- The search words of `Find` after `j` of `m` levels, on any comparison values: a window
start $a$, the half length $2^{m-j}/2$ and the exponent $2^j$, the window within the $k$ shifts.
-/
def FindStoredState (k m j : ℕ) (r : ℕ × ℕ) (s : Store ℝ) : Prop :=
  ∃ a : ℕ, SearchWords r a (2 ^ (m - j) / 2) (2 ^ j) s ∧ a + 2 ^ (m - j) ≤ k

omit [Has ScalarOp O] in
/-- One level of `Find` with a terminating routine advances the search words. -/
private theorem findRoundedLevel_terminates {M : Machine ℝ} {I : Interp O Q ℝ} {Tau : Impl O Q}
    (hL : IsIndexLit M I) (hCmp : IsCmp id I) (hQ : IsToNat id I) {n m k j : ℕ}
    (hTau : TerminatingHalfTau n k Tau I) (hNat : IsExactNatLit id M k) {τ : Tape ℝ}
    {μ : Mem ℝ} {b ss r : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {xs : List ℝ}
    (hkm : k = 2 ^ m) (hj : j < m) (hB : HoldsMatrix b H μ.store)
    (hSS : μ.store.readBlock ss.1 ss.2 (2 * k) = some xs)
    (hst : FindStoredState k m j r μ.store)
    (hrb : r.1 ≠ b.1) (hrs : r.1 ≠ ss.1) (hl : μ.Live [b, ss, r, r])
    (hr : r.2 + 6 ≤ μ.store.len r.1) :
    Writes .total I τ (findRoundedLevel Tau).body (Env.frame [n + 1, k] [b, ss, r, r])
      (Store.inBlock r.1 r.2 6) (fun μ' => FindStoredState k m (j + 1) r μ'.store) μ := by
  obtain ⟨a, hw, ha⟩ := hst
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
  have hnorms := findRoundedNorms_terminates (τ := τ) (a := a) (h := 2 ^ p) (e := 2 ^ j) hTau hB
    hSS (by rw [pow_succ] at ha; omega) (by rw [← hpj]; ring) hrb hrs hl hr
  change Writes .total I τ (.seq _ _) _ _ _ μ
  refine hnorms.frame_seq_le
    (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval]) hl
    (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  rintro μ₁ hfr₁ ⟨⟨tA, htA⟩, tB, htB⟩
  have hw₁ := hfr₁.keep (readsOnly_searchWords r _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm hw
  have hrl := Store.lt_length_of_get hw₁.1
  have hdec := findRitzDecision_writes_of_exactNatLit hL hNat hCmp (τ := τ) hw₁ htB htA
    (by rw [hfr₁.len_eq]; omega) (by rw [pow_succ] at ha; omega)
    (by rw [mul_comm, ← pow_succ]; exact hjk)
  refine (hdec.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (by simpa [Mem.Live] using hrl)).mono (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  rintro μ₂ _ ⟨-, hw₂⟩
  have hmj : m - (j + 1) = p := by omega
  refine ⟨if tA ≤ tB then a else a + 2 ^ p, ?_, ?_⟩
  · rw [hmj, pow_succ 2 j, mul_comm]; exact hw₂
  · rw [hmj]; rw [pow_succ] at ha; split_ifs <;> omega

/-- `Find` with a terminating routine terminates on any matrix and any shifts: on a scalar
machine whose natural literals up to $k = 2^m$ are exact, with exact comparisons and index
conversion, a comparison routine `Tau` meeting `NLAlib.ShiftedQR.TerminatingHalfTau`, any matrix
at `A` and any $2k$ shift words at `SS`, `NLAlib.ShiftedQR.findRounded` writes only the pair
`Center` and leaves it stored. The shifts and `Center` are disjoint views. -/
theorem findRounded_terminates {M : Machine ℝ} {I : Interp O Q ℝ} {Tau : Impl O Q}
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hCmp : IsCmp id I) (hQ : IsToNat id I)
    {n m k : ℕ} (hTau : TerminatingHalfTau n k Tau I) (hNat : IsExactNatLit id M k)
    {τ : Tape ℝ} {μ : Mem ℝ} {b ss z : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {xs : List ℝ} (hkm : k = 2 ^ m) (hB : HoldsMatrix b H μ.store)
    (hSS : μ.store.readBlock ss.1 ss.2 (2 * k) = some xs) (hl : μ.Live [b, ss, z])
    (hsep : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * k)) (Store.inBlock z.1 z.2 2))
    (hz : z.2 + 2 ≤ μ.store.len z.1) :
    Writes .total I τ (findRounded Tau).body (Env.frame [n + 1, m, k] [b, ss, z])
      (Store.inBlock z.1 z.2 2)
      (fun μ' => ∃ c : ℂ, μ'.store.readBlock z.1 z.2 2 = some [c.re, c.im]) μ := by
  obtain ⟨hbl, hsl, hzl⟩ : b.1 < μ.store.length ∧ ss.1 < μ.store.length ∧
      z.1 < μ.store.length := by simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 6] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [6]) rfl
    (fun hBelow ⟨c, hc⟩ => ⟨c, (hBelow.readBlock hzl z.2 2).trans hc⟩) ?_
  intro store hlen hlens hBelow
  let r : ℕ × ℕ := (μ.store.length, 0)
  have hr : store.len r.1 = 6 := by simpa [r] using hlens 0 (by simp)
  have hst : μ.store.length + 1 = store.length := by rw [hlen]; simp
  have hk1 : 1 ≤ k := hkm ▸ Nat.one_le_two_pow
  have hB' := hB.of_below hBelow hbl
  have hSS' := hBelow.readBlock_of hsl hSS
  have hrb : r.1 ≠ b.1 := by simp only [r]; omega
  have hrs : r.1 ≠ ss.1 := by simp only [r]; omega
  refine Writes.in_frame (Writes.mono (F := Store.inBlock r.1 r.2 6 ⊔ Store.inBlock z.1 z.2 2) ?_
    (sup_le (Fp.inBlock_le_sup_above le_rfl) le_sup_left) fun _ _ h => h) rfl rfl
    (show (⟨store, μ.pos⟩ : Mem ℝ).Live [b, ss, r, z] by
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      exact ⟨by omega, by omega, by simp only [r]; omega, by omega⟩)
  unfold findRoundedWithScratch
  refine (findRitzInitialize_writes_of_exactNatLit hL hNat hk1 (τ := τ) (m := ⟨store, μ.pos⟩)
    (r := r) (by simp only [r] at hr ⊢; omega)).frame_seq_le rfl rfl
    (by simp [Mem.Live, r]; omega) (by fp_sub) ?_
  rintro μ₁ hfr₁ ⟨-, hw₁⟩
  refine Writes.seq_le (F := Store.inBlock r.1 r.2 6 ⊔ Store.inBlock z.1 z.2 2)
    (writes_loop (P := fun j μ' => FindStoredState k m j r μ'.store) rfl
      (fun _ => Store.inBlock r.1 r.2 6) (fun _ _ => le_rfl)
      ⟨0, by simpa [hkm] using hw₁, by simp [hkm]⟩ ?_) le_sup_left ?_
  · intro j hj μ' hfr hst'
    have hfr' := (hfr₁.trans' hfr).mono (by fp_sub : _ ≤ Store.inBlock r.1 r.2 6)
    have hlv : μ'.Live [b, ss, r, r] := by
      simp [Mem.Live, hfr.length_eq, hfr₁.length_eq, r]; omega
    refine (findRoundedLevel_terminates (τ := τ) hL hCmp hQ hTau hNat hkm hj
      (hB'.of_eqOff hfr' (Fp.disj_inBlock_of_ne hrb))
      (hfr'.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_ne hrs) hSS') hst' hrb
      hrs hlv (by rw [hfr.len_eq, hfr₁.len_eq]; simp only [r] at hr ⊢; omega)).in_frame
        (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
        (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval, r]) hlv
  rintro μ₂ hfr₂ ⟨a, hw₂, ha₂⟩
  simp only [Nat.sub_self, pow_zero] at hw₂ ha₂
  have hfr' := (hfr₁.trans' hfr₂).mono (by fp_sub : _ ≤ Store.inBlock r.1 r.2 6)
  obtain ⟨shifts, hsk, hSh⟩ := Store.exists_readBlock_flatMap_pair
    (hfr'.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_inBlock_of_ne hrs) hSS')
  have hc := findRitzCopy_writes_of_readBlock hS hQ (τ := τ) hSh hsk hw₂.1 (by omega) hsep
    (by rw [hfr₂.len_eq, hfr₁.len_eq, (hBelow z.1 hzl).1]; exact hz)
  refine (hc.in_frame rfl rfl
    (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq, r]; omega)).mono le_sup_right ?_
  rintro μ₃ _ ⟨-, hread⟩
  exact ⟨_, hread⟩

end Termination

end NLAlib.ShiftedQR
