/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.HessenbergReduction
public import NLAlib.Eigensolvers.SmallEig.Core
public import NLAlib.Eigensolvers.SmallEig.Perturb
public import NLAlib.Ops.Blas.Fill

/-!
# The small-eigenvalue program

The algorithm `Eig` of [BanksGarzaVargasSrivastava2025, Theorem 1.1] as a fixed program
`[d, nq, T] (Bk, Q) → (Ev)` over scalar arithmetic, index literals, draws of a Gaussian stream and
the polar disk sampler, with no eigenvalue oracle: a block of order at most $1$ is copied; for a
larger one the output words are set to zero (so that they are stored even when the core stops
early), the block is copied to scratch, perturbed by a scaled complex Gaussian matrix
(`NLAlib.SmallEig.ginibrePerturb`), reduced to Hessenberg form (`NLAlib.hessenbergReduceLast`), and
deflated by the core (`NLAlib.SmallEig.smallEigCore` at the bottom width $1$) with the threshold
word `Q[6]` and the words `Q`. The program has the interface of a small-eigenvalue routine
(`NLAlib.ShiftedQR.RandomSmallEigContract`), so the shifted QR algorithm can run it in the place
of its kernel.

## Main definitions

* `NLAlib.SmallEig.smallEigProg`: the program.
* `NLAlib.SmallEig.smallEigDims`, `NLAlib.SmallEig.SmallEigInput`,
  `NLAlib.SmallEig.SmallEigSpectrum`: the dimensions, the memory of the input and the memory of
  the output of a run.

## Main results

* `NLAlib.SmallEig.smallEigProg_terminates`: termination on every tape.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The small-eigenvalue program** ([BanksGarzaVargasSrivastava2025, Theorem 1.1], `Eig`, with
the base case of order at most $1$ and every loop capped): for $d \le 1$ copy the entry
(`NLAlib.SmallEig.copyLeaf`); otherwise set the $2d$ output words to zero (`NLAlib.Ops.fillMap`:
they stay stored if the core stops early), copy the threshold word `Q[6]` to scratch `Th` (the
core's views are apart) and the block to scratch `W`, perturb it
(`NLAlib.SmallEig.ginibrePerturb` with the Gaussian stream `sG` and the scale word `Q[0]`), reduce
it to Hessenberg form, and run the core at the bottom width $1$ with the threshold word `Th`, the
$n_q$ words `Q` and the cap $T$, into `Ev` and a scratch failure word. The interface is
`[d, nq, T] (Bk, Q) → (Ev)`.
Algorithm: small-eig -/
def smallEigProg (sG : ℕ) : Impl O Q := opsImpl% [d, nq, T] (Bk, Qw) → (Ev) {
  ifPos 2 - d {
    run (copyLeaf (O := O) (Q := Q)).body [d, nq, T] (Bk, Qw, Ev)
  };
  ifPos d - 1 {
    let W ← alloc (2 * (d * d));
    let Fl ← alloc 1;
    let Th ← alloc 1;
    run (fillMap (Tst := Q) (Has.inj (ScalarOp.lit 0) : O)).body [2 * d] (Ev);
    call (Has.inj ScalarOp.copy) [] (Qw[6]) → (Th);
    run (unaryMap (Tst := Q) (Has.inj ScalarOp.copy)).body [2 * (d * d)] (Bk, W);
    run (ginibrePerturb (O := O) (Q := Q) sG).body [d, nq] (W, Qw, W);
    run (hessenbergReduceLast (O := O) (Q := Q)).body [d] (W, W);
    run (smallEigCore (O := O) (Q := Q) sG).body [d, 1, nq, T, T] (W, Th, Qw, Ev, Fl)
  }
}

end Program

/-- The dimensions of a run at the order $n + 1$: the order, the number of words of
`NLAlib.SmallEig.smallEigParams` and the cap `NLAlib.SmallEig.smallEigCap`. -/
noncomputable def smallEigDims (n nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : List ℕ :=
  [n + 1, (smallEigParams nmax S δ φ c₁ c₂).length, smallEigCap nmax S δ φ c₁ c₂]

/-- **The memory holding the input** of the small-eigenvalue program: $\mathbf{M}$ at `w`, the
words `NLAlib.SmallEig.smallEigParams` at `q`, room for the $2(n + 1)$ output words at `o`, the
views live and the output apart from the matrix and the words. -/
def SmallEigInput {n : ℕ} (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) (w q o : ℕ × ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  HoldsMatrix w M μ.store ∧
    μ.store.readBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length =
      some (smallEigParams nmax S δ φ c₁ c₂) ∧
    μ.Live [w, q, o] ∧ o.2 + 2 * (n + 1) ≤ μ.store.len o.1 ∧
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock o.1 o.2 (2 * (n + 1))) ∧
    Fp.Disj (Store.inBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length)
      (Store.inBlock o.1 o.2 (2 * (n + 1)))

/-- **The memory holding the spectrum of a nearby matrix**: the output at `o` lists all
eigenvalues, with multiplicity, of $\mathbf{M} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le \delta$. -/
def SmallEigSpectrum {n : ℕ} (o : ℕ × ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (δ : ℝ)
    (μ' : Mem ℝ) : Prop :=
  ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), specNorm E ≤ δ ∧
    IsEigenvalueListing (M + E) roots ∧
    HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- The core keeps stored output words stored: `NLAlib.SmallEig.smallEigCore_terminates`,
and if the $2(n + 1)$ output words are stored before the run, they are stored after it, also
when the core stops early. -/
theorem smallEigCore_terminates_stored {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {T F : ℕ} {qs : List ℝ} (hqs : SmallEigCaps T qs)
    (hlen : 12 ≤ qs.length) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {tape : Tape ℝ}
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigCoreInput qs a t p out f H μ) :
    Writes .total I tape (smallEigCore (O := O) (Q := Q) sG).body
      (Env.frame [n + 1, 1, qs.length, F, T] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ ys, μ.store.readBlock out.1 out.2 (2 * (n + 1)) = some ys) →
        ∃ ys, μ'.store.readBlock out.1 out.2 (2 * (n + 1)) = some ys) μ :=
  solveRoundedWith_terminates_stored hS hL hNat hQ hC _
    (smallEigDecoupler_terminatingDecouplerRoutine hS hL hNat hC hQ hSmp hDisk hqs hlen) _
    (copyLeaf_terminates hS _ qs T) hin.1 hin.2.1 hin.2.2.1 hin.2.2.2.1 hin.2.2.2.2.1
    hin.2.2.2.2.2

/-- The memory of the core's call in `NLAlib.SmallEig.smallEigProg`: the work matrix at
`(L, 0)`, the failure word at `(L + 1, 0)` and the copied threshold word at `(L + 2, 0)` in three
scratch buffers on top of the store, with the words and the output below them, apart. -/
theorem smallEigCoreInput_of_scratch {n L : ℕ} {qs : List ℝ} {q o : ℕ × ℕ} {μ : Mem ℝ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hql : q.1 < L) (hol : o.1 < L)
    (hlen : μ.store.length = L + 3) (hW : μ.store.len L = 2 * ((n + 1) * (n + 1)))
    (hF : μ.store.len (L + 1) = 1) (hT : μ.store.len (L + 2) = 1)
    (hroom : o.2 + 2 * (n + 1) ≤ μ.store.len o.1) (hq12 : 12 ≤ qs.length)
    (hqo : Fp.Disj (Store.inBlock q.1 q.2 qs.length) (Store.inBlock o.1 o.2 (2 * (n + 1))))
    (hH : HoldsMatrix (L, 0) H μ.store) (ht : μ.store.get (L + 2) 0 = some (qs.getD 6 0))
    (hq : μ.store.readBlock q.1 q.2 qs.length = some qs) :
    SmallEigCoreInput qs (L, 0) (L + 2, 0) q o (L + 1, 0) H μ := by
  have hD : ∀ {b b' o₁ o₂ k₁ k₂ : ℕ}, b ≠ b' →
      Fp.Disj (Store.inBlock b o₁ k₁) (Store.inBlock b' o₂ k₂) := Fp.disj_inBlock_of_ne
  have hqr := Store.le_len_of_readBlock hq (by omega)
  refine ⟨?_, ?_, ?_, hH, ht, hq⟩
  · simp [Mem.Live, hlen]
    omega
  · simp only [Mem.Room]
    exact ⟨by simp [hW], by simp [hT], hqr, hroom, by simp [hF], trivial⟩
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨hD (by omega), hD (by omega), hD (by omega), hD (by omega)⟩,
      ⟨hD (by omega), hD (by omega), hD (by omega)⟩, ⟨hqo, hD (by omega)⟩, hD (by omega)⟩

/-- The branch of order at least $2$ of `NLAlib.SmallEig.smallEigProg_terminates`: zero the
output, copy the threshold word and the block to scratch, perturb, reduce and run the core; the
output stays stored. -/
theorem smallEigProg_terminates_of_two_le {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I) {T : ℕ} {qs : List ℝ}
    (hqs : SmallEigCaps T qs) (hlen : 12 ≤ qs.length) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 2)) {w q o : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    {B : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} (hB : HoldsMatrix w B μ.store)
    (hq : μ.store.readBlock q.1 q.2 qs.length = some qs) (hl : μ.Live [w, q, o])
    (hroom : o.2 + 2 * (n + 2) ≤ μ.store.len o.1)
    (hwo : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 2) * (n + 2))))
      (Store.inBlock o.1 o.2 (2 * (n + 2))))
    (hqo : Fp.Disj (Store.inBlock q.1 q.2 qs.length) (Store.inBlock o.1 o.2 (2 * (n + 2)))) :
    Writes .total I tape (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame [n + 2, qs.length, T] [w, q, o]) (Store.inBlock o.1 o.2 (2 * (n + 2)))
      (fun μ' => ∃ ys, μ'.store.readBlock o.1 o.2 (2 * (n + 2)) = some ys) μ := by
  have hwl : w.1 < μ.store.length := hl w (by simp)
  have hql : q.1 < μ.store.length := hl q (by simp)
  have hol : o.1 < μ.store.length := hl o (by simp)
  unfold smallEigProg
  refine (writes_ifPos (F := ⊥) (P := fun μ₁ => μ₁ = μ) (n := 2 - (n + 2)) rfl
    (by rw [if_neg (by omega)])).seq_le bot_le ?_
  intro μ₁ _ h₁
  subst μ₁
  refine writes_ifPos (n := n + 2 - 1) rfl ?_
  rw [if_pos (by omega)]
  change Writes .total I tape (Stmt.allocs [.const 2 * (.var 0 * .var 0), .const 1, .const 1] _)
    _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2 * ((n + 2) * (n + 2)), 1, 1]) rfl
    (fun hBelow ⟨ys, hy⟩ => ⟨ys, (hBelow.readBlock hol _ _).trans hy⟩) ?_
  intro s₁ hlen₁ hlens hBelow
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen₁
  have hW : s₁.len L = 2 * ((n + 2) * (n + 2)) := by simpa using hlens 0 (by simp)
  have hTh : s₁.len (L + 2) = 1 := by simpa using hlens 2 (by simp)
  have hab : ∀ b o' k, L ≤ b →
      Store.inBlock b o' k ≤ Store.inBlock o.1 o.2 (2 * (n + 2)) ⊔ Fp.above L :=
    fun b o' k hb _ _ hi => Or.inr (hi.1 ▸ hb)
  have hup : ∀ {b o' k : ℕ}, L ≤ b → ∀ b' i, Store.inBlock b o' k b' i → L ≤ b' :=
    fun hb _ _ hi => hi.1 ▸ hb
  have hq₀ := hBelow.readBlock_of hql hq
  refine (writes_fillMap_readBlock (hS (.lit 0)) (τ := tape) (m := ⟨s₁, μ.pos⟩) (y := o)
    (by rw [(hBelow o.1 hol).1]; exact hroom)).frame_seq_le rfl rfl
    (by simp [Mem.Live, hlen₁]; omega) le_sup_left ?_
  intro μ₁ hfr₁ hO₁
  have hq₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) hqo.symm hq₀
  refine (writes_call_un (hS .copy) (x := (q.1, q.2 + 6)) (z := (L + 2, 0)) rfl rfl trivial
    (Store.get_of_readBlock hq₁ (j := 6) (by omega) 0) rfl
    (by rw [hfr₁.len_eq, hTh]; omega)).seq_le (hab _ _ _ (by omega)) ?_
  rintro μ₂ hfr₂ ⟨-, hTh₂⟩
  have hB₂ : HoldsMatrix w B μ₂.store :=
    ((hB.of_below hBelow hwl).of_eqOff hfr₁ hwo.symm).of_eqOff hfr₂
      (Fp.disj_inBlock_of_ne (by omega))
  have hlen₂ : μ₂.store.length = L + 3 := by rw [hfr₂.length_eq, hfr₁.length_eq, hlen₁]
  refine (copyMatrix_writes hS (τ := tape) hB₂ (b := (L, 0))
    (by rw [hfr₂.len_eq, hfr₁.len_eq, hW]; simp) (Fp.disj_inBlock_of_ne (by omega))).frame_seq_le
    rfl rfl (by simp [Mem.Live, hlen₂]; omega) (hab _ _ _ le_rfl) ?_
  rintro μ₃ hfr₃ ⟨-, hW₃⟩
  have hB₂₃ := (hfr₂.below_of_above (hup (by omega))).trans (hfr₃.below_of_above (hup le_rfl))
  have hlen₃ : μ₃.store.length = L + 3 := by rw [hfr₃.length_eq, hlen₂]
  refine (ginibrePerturb_writes_word hS hL hSmp (sG := sG) (nq := qs.length) (τ := tape)
    (a := (L, 0)) (by simp [Mem.Live, hlen₃]; omega) hW₃
    (hB₂₃.get_of hql (by simpa using Store.get_of_readBlock hq₁ (j := 0) (by omega) 0))
    ).frame_seq_le rfl rfl
    (by simp [Mem.Live, hlen₃]; omega) (hab _ _ _ le_rfl) ?_
  rintro μ₄ hfr₄ ⟨-, hW₄⟩
  have hlen₄ : μ₄.store.length = L + 3 := by rw [hfr₄.length_eq, hlen₃]
  refine (hessenbergReduceLast_terminates hS hC (τ := tape) (a := (L, 0))
    (by simp [Mem.Live, hlen₄]) hW₄).frame_seq_le rfl rfl
    (by simp [Mem.Live, hlen₄]) (hab _ _ _ le_rfl) ?_
  rintro μ₅ hfr₅ ⟨H₅, hH₅⟩
  have hB₂₅ := (hB₂₃.trans (hfr₄.below_of_above (hup le_rfl))).trans
    (hfr₅.below_of_above (hup le_rfl))
  have hFl : s₁.len (L + 1) = 1 := by simpa using hlens 1 (by simp)
  have hd : ∀ k, Fp.Disj (Store.inBlock L 0 k) (Store.inBlock (L + 2) 0 1) :=
    fun _ => Fp.disj_inBlock_of_ne (by omega)
  have hTh₅ : μ₅.store.get (L + 2) 0 = some (qs.getD 6 0) :=
    hfr₅.keep (Store.readsOnly_get _ _ _) (hd _) (hfr₄.keep (Store.readsOnly_get _ _ _) (hd _)
      (hfr₃.keep (Store.readsOnly_get _ _ _) (hd _) hTh₂))
  have hlenB : ∀ b, μ₅.store.len b = s₁.len b := fun b => by
    rw [hfr₅.len_eq, hfr₄.len_eq, hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]
  have hin : SmallEigCoreInput qs (L, 0) (L + 2, 0) q o (L + 1, 0) H₅ μ₅ :=
    smallEigCoreInput_of_scratch hql hol (by rw [hfr₅.length_eq, hlen₄]) (by rw [hlenB, hW])
      (by rw [hlenB, hFl]) (by rw [hlenB, hTh]) (by rw [hlenB, (hBelow o.1 hol).1]; exact hroom)
      hlen hqo hH₅ hTh₅ ((hB₂₅.readBlock hql _ _).trans hq₁)
  refine ((smallEigCore_terminates_stored hS hL (n := n + 1) hNat hQ hC hSmp hDisk hqs hlen
    (tape := tape) (F := T) hin).in_frame rfl rfl hin.1).mono
    (sup_le (sup_le (hab _ _ _ le_rfl) le_sup_left) (hab _ _ _ (by omega))) fun _ _ h => h ?_
  exact ⟨_, (hB₂₅.readBlock hol _ _).trans hO₁.1⟩

/-- **The small-eigenvalue program terminates on every tape** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], with every loop capped): on a scalar machine with index literals, exact natural
literals up to $k_{\max}$, exact comparisons and conversion, draws that store the tape entry and
an exact polar sampler, for at least twelve words `qs` with valid cap words for the cap $T$
(`NLAlib.SmallEig.SmallEigCaps`), `NLAlib.SmallEig.smallEigProg` is a
terminating small-eigenvalue routine (`NLAlib.ShiftedQR.TerminatingSmallEig`) on orders at most
$k_{\max}$: from any matrix and on every tape the run is total, writes only its output and leaves
the output words stored. A run with junk cap words fails at a bounded index read, so the cap
words are a hypothesis; the core reads the words $8$ to $11$, so twelve words are. -/
theorem smallEigProg_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I)
    {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I) {T : ℕ} {qs : List ℝ}
    (hqs : SmallEigCaps T qs) (hlen : 12 ≤ qs.length) {kmax : ℕ}
    (hNat : IsExactNatLit id M kmax) :
    TerminatingSmallEig kmax T qs (smallEigProg (O := O) (Q := Q) sG) I := by
  intro d w q o tape μ B hd hB hq hl hroom hwo hqo
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · unfold smallEigProg
    refine (writes_ifPos (n := 2 - d)
      (P := fun μ' => ∃ ys, μ'.store.readBlock o.1 o.2 (2 * d) = some ys) rfl ?_).seq_le le_rfl ?_
    · rw [if_pos (by omega)]
      exact ((copyLeaf_terminates hS d qs T B le_rfl hB hq hl hroom hwo hqo :
        Writes .total I tape _ _ _ _ μ).in_frame rfl rfl hl)
    · intro μ₁ _ h₁
      refine writes_ifPos (n := d - 1) rfl ?_
      rw [if_neg (by omega)]
      exact h₁
  · obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
    exact smallEigProg_terminates_of_two_le hS hL hQ hC hSmp hDisk hqs hlen
      (hNat.mono hd) hB hq hl hroom hwo hqo

end Theorems

end NLAlib.SmallEig
