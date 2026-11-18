/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Dense

/-!
# The dense Schur pipeline completes on any scalar machine

The run of the pipeline needs no rounding model to succeed: with stages that complete
(`NLAlib.Schur.CompletingNormEstimate`, `NLAlib.Schur.CompletingReducer`,
`NLAlib.Schur.CompletingSchurCore`) it succeeds on every tape of any scalar machine with exact
natural literals, index literals and exact comparisons, writing only the matrix, the accumulator
and the flag (`NLAlib.Schur.schurPipelineWith_completes`). The four stages of the dense Schur
solver complete, so `NLAlib.Schur.denseSchur` does (`NLAlib.Schur.denseSchur_completes`); the
certificate's admitted sizes need no standard model.

## Main definitions

* `NLAlib.Schur.CompletingNormEstimate`, `NLAlib.Schur.CompletingReducer`,
  `NLAlib.Schur.CompletingSchurCore`: the stages that complete.

## Main results

* `NLAlib.Schur.schurPipelineWith_completes`: the pipeline completes.
* `NLAlib.Schur.denseSchur_completes`: the dense Schur solver completes.
-/

@[expose] public section

open NLAlib.Ops NLAlib.ShiftedQR NLAlib.SmallEig

/-- Every machine has the standard model at $\boldsymbol{u} = 1$ for the zero decoding: a
trivial model, whose laws still give the totality of the lowered programs. -/
theorem _root_.NLAlib.Ops.stdModel_one_zero {K : Type} (M : Machine K) :
    StdModel 1 (fun _ => (0 : ℝ)) M where
  lit q := by simp
  add _ _ := by simp
  sub _ _ := by simp
  mul _ _ := by simp
  div _ _ h := absurd rfl h
  neg _ := by simp
  sqrt _ _ := by simp

open RoundedScalarBlas in
/-- The scalar-lowered norm completes on any scalar machine and stores a word (the trivial model
`NLAlib.Ops.stdModel_one_zero`). -/
theorem _root_.NLAlib.Ops.RoundedScalarBlas.writes_nrm2 {Op Tst : Type} [Has ScalarOp Op]
    {M : Machine ℝ} {I : Interp Op Tst ℝ} (hS : IsScalar M I) {n : ℕ} {τ : Tape ℝ} {m : Mem ℝ}
    {x z : ℕ × ℕ} {xs : List ℝ} (hl : m.Live [x, z])
    (hx : m.store.readBlock x.1 x.2 n = some xs) (hz : z.2 < m.store.len z.1) (hxz : x.1 ≠ z.1) :
    Writes .total I τ nrm2.body (Env.frame [n] [x, z]) (Store.inBlock z.1 z.2 1)
      (fun μ => ∃ v : ℝ, μ.store.get z.1 z.2 = some v) m := by
  let rename : Table ScalarOp Op Tst := fun o => .inr (Has.inj o)
  let J := I.link rename
  have hJ : IsScalar M J := fun o => Interp.link_meets_kept rfl (hS o)
  have hB := (laws (stdModel_one_zero M) zero_le_one hJ).2
  have hw := writes_call_cell (τ := τ) (m := m) (I := J.link table) hB.nrm2
    (ρ := Env.frame [n] [x, z]) (d := [n]) (a := [x]) (z := z) (k := 0)
    (ds := [.var 0]) (ins := [⟨0, .var 1⟩]) (outs := [⟨1, .var 2⟩])
    rfl rfl rfl rfl rfl rfl (by simpa [OutApart] using hxz)
    (fun _ => ⟨hl, ⟨[xs], by simp [Mem.readBlocks, nrm2Rel, hx], trivial⟩, hz⟩)
  have hw' := hw.mono (P' := fun μ => ∃ v : ℝ, μ.store.get z.1 z.2 = some v) le_rfl
    (fun μ _ hp => by obtain ⟨-, -, value, -, hvalue, -⟩ := hp; exact ⟨value, hvalue⟩)
  change Writes .total I τ _ _ _ _ m
  simpa only [Writes, Wp, nrm2, run_link, J, rename] using hw'

namespace NLAlib.Schur

variable {O Q : Type}

/-- **A norm stage that completes**: for every order $N \le N_{\max}$ and every stored matrix,
`[N] (A) → (S)` succeeds on every tape, writes only the output cell and stores a word. -/
def CompletingNormEstimate (nmax : ℕ) (Nm : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {N : ℕ} {a s : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (A : Matrix (Fin N) (Fin N) ℂ),
    N ≤ nmax → HoldsMatrix a A μ.store → μ.Live [a, s] → s.2 + 1 ≤ μ.store.len s.1 →
    a.1 ≠ s.1 →
    Writes .total I tape Nm.body (Env.frame [N] [a, s]) (Store.inBlock s.1 s.2 1)
      (fun μ' => ∃ x : ℝ, μ'.store.get s.1 s.2 = some x) μ

/-- **A reducer that completes**: for every order $N \le N_{\max}$ and every stored pair,
`[N] (A, U) → (A, U)` succeeds on every tape, writes only the pair and stores a pair. -/
def CompletingReducer (nmax : ℕ) (Red : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {N : ℕ} {a uo : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (A U : Matrix (Fin N) (Fin N) ℂ),
    N ≤ nmax → HoldsSchurPair a uo U A μ.store → μ.Live [a, uo] →
    Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock uo.1 uo.2 (2 * (N * N))) →
    Writes .total I tape Red.body (Env.frame [N] [a, uo, a, uo])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock uo.1 uo.2 (2 * (N * N)))
      (fun μ' => ∃ U' H : Matrix (Fin N) (Fin N) ℂ, HoldsSchurPair a uo U' H μ'.store) μ

/-- The rounded Frobenius norm completes on any scalar machine. -/
theorem frobNormStage_completing [Has ScalarOp O] {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (nmax : ℕ) :
    CompletingNormEstimate nmax (frobNormStage (O := O) (Q := Q)) I := by
  intro N a s τ μ A _ hA hl hs has
  have hn := RoundedScalarBlas.writes_nrm2 (τ := τ) (xs := matrixWords A)
    (n := 2 * (N * N)) hS hl hA (by omega) has
  exact ((hn.in_frame rfl rfl hl).in_frame rfl rfl hl).mono le_rfl fun _ _ h => h


/-- The reduction with its accumulated unitary completes on any scalar machine with exact
comparisons and `toNat`, index literals and exact natural literals up to $N_{\max} \ge 1$ (the
open of the log needs only the literal $0$ exact, the replay no rounding model). -/
theorem hessenbergReduceQ_completing [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]
    [Has IdxTst Q] {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) (hC : IsCmp id I)
    (hQ : IsToNat id I) (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M nmax)
    (h1 : 1 ≤ nmax) : CompletingReducer nmax (hessenbergReduceQ (O := O) (Q := Q)) I := by
  intro N a uo τ μ A U hN ⟨hA, hU⟩ hl hd
  have h0 : M.lit 0 = 0 := by simpa using hNat 0 (by omega)
  have hal : a.1 < μ.store.length := hl a (by simp)
  have hul : uo.1 < μ.store.length := hl uo (by simp)
  set Sl := hessenbergReduceLastSlots M A
  unfold hessenbergReduceQ
  change Writes .total I τ (Stmt.allocs [_] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [N * (1 + 5 * (N - 1))]) rfl
    (fun hBelow ⟨U', H, h₁, h₂⟩ => ⟨U', H, h₁.of_below hBelow hal, h₂.of_below hBelow hul⟩) ?_
  intro s₁ hlen hlens hBelow
  set Lc := μ.store.length with hLc
  simp only [List.length_cons, List.length_nil] at hlen
  have hLg : s₁.len Lc = N * (1 + 5 * (N - 1)) := by simpa using hlens 0 (by simp)
  have hA₀ := hA.of_below hBelow hal
  have hU₀ := hU.of_below hBelow hul
  have hFp : Store.inBlock Lc 0 (N * (1 + 5 * (N - 1))) ≤
      Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock uo.1 uo.2 (2 * (N * N)) ⊔
        Fp.above Lc := fun b z h => Or.inr (h.1 ▸ le_rfl)
  refine (slottedLogOpen_writes_of_lit_zero (τ := τ) (μ := ⟨s₁, μ.pos⟩) (ns := N) (w := N - 1)
    (lg := (Lc, 0)) hS h0 (by simp [hLg])).frame_seq_le rfl rfl
    (by simp [Mem.Live]; omega) hFp ?_
  rintro μ₁ hfr₁ ⟨hp₁, hlog₁⟩
  have hdl : ∀ {b o n}, b < Lc → Fp.Disj (Store.inBlock b o n)
      (Store.inBlock Lc 0 (N * (1 + 5 * (N - 1)))) := fun hb => Fp.disj_inBlock_of_ne (by omega)
  refine (hessenbergReduceLast_writes_word (τ := τ) (m := μ₁) (L := []) hS hC hL hNat h1
    (by omega) hlog₁ (by simp) (by omega) (by simp [Mem.Live, hfr₁.length_eq]; omega)
    (hA₀.of_eqOff hfr₁ (hdl hal).symm) (hdl hal)).frame_seq_le rfl rfl
    (by simp [Mem.Live, hfr₁.length_eq]; omega)
    (sup_le (le_sup_left.trans le_sup_left) hFp) ?_
  rintro μ₂ hfr₂ ⟨hp₂, hH₂, hlog₂⟩
  have hlog₃ := hlog₂.close
  have hU₂ : HoldsMatrix uo U μ₂.store := (hU₀.of_eqOff hfr₁ (hdl hul).symm).of_eqOff hfr₂
    (Fp.disj_sup_left.mpr ⟨hd, (hdl hul).symm⟩)
  have hpl := hessenbergReduceLastSlots_closed_planes M A (N - 1)
  have hlo : slotEntries (N - 1) ([] ++ Sl.map some ++
      List.replicate (N - ([] ++ Sl.map some).length) none) = [] ∨ 0 + 1 < N := by
    by_cases h2 : 2 ≤ N
    · exact Or.inr (by omega)
    · refine Or.inl ?_
      have : Sl = [] := List.eq_nil_of_length_eq_zero (by
        rw [length_hessenbergReduceLastSlots]; omega)
      rw [this]
      simp [slotEntries]
  have hrow : ∀ e ∈ slotEntries (N - 1) ([] ++ Sl.map some ++
      List.replicate (N - ([] ++ Sl.map some).length) none), 0 + e.1 + 1 < N := by
    intro e he
    rcases hlo with h | h
    · rw [h] at he; simp at he
    · rcases hpl e he with h' | rfl
      · omega
      · simpa using h
  refine ((givensReplayColumns_writes_word (τ := τ) (μ := μ₂) (lo := 0) (i0 := 0) (nr := N) hS
    hQ hC (by omega) hrow hlog₃ (by simp [Sl, length_hessenbergReduceLastSlots]) hU₂
    (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq]; omega) (hdl hul).symm).in_frame rfl
    rfl (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq]; omega)).mono
    (le_sup_right.trans le_sup_left) ?_
  rintro μ₃ hfr₃ ⟨-, hU'⟩
  exact ⟨_, _, hH₂.of_eqOff hfr₃ hd.symm, hU'⟩


/-- **A Schur core that completes**: for every order at most $N_{\max}$, every stored pair and the
words `ps`, `[N, np, k, F, T] (A, P, U) → (A, U, Fl)` succeeds on every tape, writes only the
pair and the flag and stores a pair. -/
def CompletingSchurCore (k F T nmax : ℕ) (ps : List ℝ) (Core : Impl O Q) (I : Interp O Q ℝ) :
    Prop :=
  ∀ {n : ℕ} {a p uo f : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), n + 1 ≤ nmax →
    HoldsSchurPair a uo U H μ.store → μ.store.readBlock p.1 p.2 ps.length = some ps →
    μ.Live [a, p, uo, f] → f.2 + 1 ≤ μ.store.len f.1 →
    Fp.Apart [a, p, uo, f] [2 * ((n + 1) * (n + 1)), ps.length, 2 * ((n + 1) * (n + 1)), 1] →
    Writes .total I tape Core.body (Env.frame [n + 1, ps.length, k, F, T] [a, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => ∃ U' Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsSchurPair a uo U' Tm μ'.store) μ

/-- The rounded shifted QR algorithm in Schur form with a completing small-block Schur solver
completes on any scalar machine (`NLAlib.ShiftedQR.solveRoundedWith_completes`), with index
literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons and an exact polar
disk sampler. -/
theorem roundedShQRSchurWith_completing [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O]
    [Has CmpTst Q] [Has IdxTst Q] {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) {sU : ℕ} (hDisk : IsPolarDiskSampler sU I) {k : ℕ}
    {B Γ S δ φ : ℝ} (hk : k = shqrDegree (4 * B)) {T : ℕ} {qs : List ℝ} {L : Impl O Q}
    (hLeaf : CompletingLeafRoutine (min k (n + 1)) qs T L I) (hqs : qs.length = 12) :
    CompletingSchurCore k (shqrCap n B Γ S δ) T (n + 1)
      (shqrDeflationThreshold n k B Γ S δ φ :: (shqrParams n k B Γ S δ φ ++ qs))
      (roundedShQRSchurWith L) I := by
  intro n' a p uo f tape μ H U hn hHU hp hl hf ha
  set ps := shqrParams n k B Γ S δ φ ++ qs with hps
  set thr := shqrDeflationThreshold n k B Γ S δ φ
  have hkq : k = 2 ^ Nat.log 2 k := by rw [hk, shqrDegree, Nat.log_pow (by norm_num)]
  have hD : TerminatingDecouplerRoutine n' k (shqrCap n B Γ S δ) T ps
      (shqrCap n B Γ S δ * (k + 1 + ps.length)) (k * (n' + 1))
      (roundedDecoupleWith (schurDiag L)) I := by
    by_cases hkn : k ≤ n' + 1
    · exact roundedDecoupleWith_terminatingDecouplerRoutine_at (F := shqrCap n B Γ S δ) hS hL
        (hNat.mono (by omega)) hC hQ hDisk hkq (shqrLoopThreshold n k B Γ S δ φ)
        (shqrRadius n B Γ S δ) (shqrScanThreshold n k B Γ S δ φ) 0.2 (4 * B)
        (shqrAlpha k (4 * B)) (shqrEps k (4 * B))
        (CompletingLeafRoutine.terminatingSmallEigAt_schurDiag hS
          (CompletingLeafRoutine.mono_kmax hLeaf (kmax' := k) (le_min le_rfl (by omega))) hqs)
        (Or.inr hqs) rfl
        (Nat.mul_le_mul_left _ (by
          simp only [hps, shqrParams, List.length_append, length_roundedDecoupleParams]; omega))
        (Nat.mul_le_mul_left _ (by omega))
    · intro n'' w q f tape μ' H' hk' hn''
      omega
  have hp' : μ.store.readBlock p.1 (p.2 + 1) ps.length = some ps :=
    Store.readBlock_append_right (xs := [thr]) hp
  have ht : μ.store.get p.1 p.2 = some thr := by
    simpa using Store.get_of_readBlock hp (j := 0) (by simp) 0
  have hpl : p.2 + (1 + ps.length) ≤ μ.store.len p.1 := by
    simpa [Nat.add_comm 1] using Store.le_len_of_readBlock hp (by simp)
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, sup_bot_eq] at ha
  have hsub1 : Store.inBlock p.1 p.2 1 ≤ Store.inBlock p.1 p.2 (thr :: ps).length :=
    Fp.inBlock_le_inBlock le_rfl (by simp)
  have hsub2 : Store.inBlock p.1 (p.2 + 1) ps.length ≤ Store.inBlock p.1 p.2 (thr :: ps).length :=
    Fp.inBlock_le_inBlock (by omega) (by simp; omega)
  have hw := solveRoundedWith_completes (n := n') (F := shqrCap n B Γ S δ) (T := T)
    (tape := tape) (t := p) (p := (p.1, p.2 + 1)) hS hL (hNat.mono (by omega)) hQ hC
    (roundedDecoupleWith (schurDiag L)) hD (leafOnTailWords L)
    (CompletingLeafRoutine.onTailWords
      (hLeaf.mono_kmax (kmax' := min k (n' + 1)) (min_le_min le_rfl (by omega))) hqs _)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h | h <;> rw [h]
      exacts [hl a (by simp), hl p (by simp), hl p (by simp), hl uo (by simp), hl f (by simp)])
    ⟨Store.le_len_of_readBlock hHU.1 (by positivity), by omega, by dsimp only; omega,
      Store.le_len_of_readBlock hHU.2 (by positivity), hf, trivial⟩
    (by
      simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, sup_bot_eq]
      exact ⟨⟨ha.1.1.mono le_rfl hsub1, ha.1.1.mono le_rfl hsub2, ha.1.2.1, ha.1.2.2⟩,
        ⟨Fp.disj_inBlock_of_le le_rfl, ha.2.1.1.mono hsub1 le_rfl, ha.2.1.2.mono hsub1 le_rfl⟩,
        ⟨ha.2.1.1.mono hsub2 le_rfl, ha.2.1.2.mono hsub2 le_rfl⟩, ha.2.2.1,
        fun _ _ _ h => h, trivial⟩)
    hHU.1 hHU.2 ht hp'
  unfold roundedShQRSchurWith
  refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h | h | h | h <;> rw [h]
      exacts [hl a (by simp), hl p (by simp), hl p (by simp), hl uo (by simp), hl a (by simp),
        hl uo (by simp), hl f (by simp)])).mono le_rfl ?_
  rintro μ' - ⟨Tm, U', hTm, hU'⟩
  exact ⟨U', Tm, hTm, hU'⟩


/-- A block whose words were all multiplied by `r` holds a matrix. -/
theorem exists_holdsMatrix_of_mul {M : Machine ℝ} {N : ℕ} {b : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} {s s' : Store ℝ} {r : ℝ} (hA : HoldsMatrix b A s)
    (h : ∀ t < 2 * (N * N), ∀ w, s.get b.1 (b.2 + t) = some w →
      s'.get b.1 (b.2 + t) = some (M.mul w r)) :
    ∃ A' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix b A' s' := by
  have hlt : ∀ (i j : Fin N), 2 * (j * N + i) + 1 < 2 * (N * N) := fun i j => by
    have := Idx.add_lt_mul j.isLt i.isLt; omega
  refine ⟨Matrix.of fun i j => ⟨M.mul (A i j).re r, M.mul (A i j).im r⟩,
    HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)⟩
  · exact h _ (by have := hlt i j; omega) _ (hA.get_re i j)
  · rw [Nat.add_assoc]; exact h _ (hlt i j) _ (by rw [← Nat.add_assoc]; exact hA.get_im i j)

section Steps

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

omit [Has IndexOp O] [Has CmpTst Q] in
/-- The identity program stores the identity when the literals $0$ and $1$ are exact. -/
theorem writes_identity_holdsMatrix_one_of_lit {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (h0 : Mch.lit 0 = 0) (h1 : Mch.lit 1 = 1) {τ : Tape ℝ}
    {m : Mem ℝ} {N : ℕ} {b : ℕ × ℕ} (hroom : b.2 + 2 * (N * N) ≤ m.store.len b.1) :
    Writes .total I τ (PairMatrix.identity (Op := O) (Tst := Q)).body (Env.frame [N] [b])
      (Store.inBlock b.1 b.2 (2 * (N * N)))
      (fun m' => HoldsMatrix b (1 : Matrix (Fin N) (Fin N) ℂ) m'.store) m := by
  refine (PairMatrix.writes_identity hS hroom).mono le_rfl fun m' _ hv => ?_
  refine holdsMatrix_one_of_holdsVec fun i hi => ?_
  rw [hv.1 i hi, h0, h1]

omit [Has IndexOp O] [Has CmpTst Q] in
/-- The scaling of the pipeline on any scalar machine: from a run memory holding a matrix and a
word $x$ in $S$, the scaling stores some matrix. -/
theorem schurPipeline_scale_completes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) {n nr nq k F T L : ℕ} {qs : List ℝ} {a p uo f : ℕ × ℕ} {τ : Tape ℝ}
    {m : Mem ℝ} (hm : SchurPipelineMem n qs a p uo f L m)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : HoldsMatrix a A m.store) {x : ℝ}
    (hx : m.store.get L 0 = some x) :
    Writes .total I τ
      ((Stmt.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨6, .const 0⟩]).seq
        ((Stmt.call (Has.inj ScalarOp.div) [] [⟨6, .const 0⟩, ⟨5, .const 0⟩] [⟨6, .const 0⟩]).seq
          (.loop (.const 2 * (.var 0 * .var 0)) (.call (Has.inj ScalarOp.mul) []
            [⟨0, .var 6 + .var 11⟩, ⟨6, .const 0⟩] [⟨0, .var 6 + .var 11⟩]))))
      (schurPipelineEnv n nr nq k F T a p uo f L)
      (Store.inBlock (L + 1) 0 1 ⊔ Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (fun m' => SchurPipelineMem n qs a p uo f L m' ∧ m'.store.get L 0 = some x ∧
        ∃ A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A₁ m'.store) m := by
  obtain ⟨hlen, ha, -, -, -, -, hL, hL', -⟩ := id hm
  have hRroom : (0 : ℕ) < m.store.len (L + 1) := by omega
  refine (writes_call_const (hS (.lit 1)) (z := (L + 1, 0)) rfl trivial hRroom).seq_le
    le_sup_left fun m₁ hfr₁ hR₁ => ?_
  have hx₁ : m₁.store.get L 0 = some x := by
    rw [hfr₁.2 L 0 (by simp [Store.inBlock]), hx]
  have hlive₁ : m₁.Live [(L + 1, 0), (L, 0), (L + 1, 0)] := by
    have := hm.live.congr hfr₁.length_eq
    exact fun z hz => this z (by simp at hz ⊢; tauto)
  refine (writes_call_bin (hS .div) (x := (L + 1, 0)) (y := (L, 0)) (z := (L + 1, 0)) rfl rfl
    trivial hR₁.2 hx₁ rfl fun _ => ⟨hlive₁, by rw [hfr₁.len_eq]; omega⟩).seq_le le_sup_left
    fun m₂ hfr₂ hR₂ => ?_
  have hfr₁₂ := hfr₁.trans hfr₂
  have hA₂ : HoldsMatrix a A m₂.store := hA.of_eqOff hfr₁₂ (Fp.disj_inBlock_of_ne (by omega))
  have hx₂ : m₂.store.get L 0 = some x := by
    rw [hfr₂.2 L 0 (by simp [Store.inBlock]), hx₁]
  refine (writes_loop_mul_cell hS (N := 2 * ((n + 1) * (n + 1))) (b := a.1) (o := a.2)
    (y := (L + 1, 0)) (r := Mch.div (Mch.lit 1) x) rfl (fun t _ => rfl) (fun t _ => rfl) ?_
    (fun t ht => ⟨_, Store.get_of_readBlock hA₂ ht 0⟩) hR₂.2 ?_).mono le_sup_right ?_
  · have := hm.live.congr hfr₁₂.length_eq
    exact fun z hz => this z (by simp at hz ⊢; tauto)
  · rintro ⟨h, -⟩; omega
  rintro m₃ hfr₃ ⟨-, hmul⟩
  have hfr : m.store.EqOff (Store.inBlock (L + 1) 0 1 ⊔
      Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) m₃.store :=
    (hfr₁₂.mono fun _ _ h => Or.inl h).trans (hfr₃.mono fun _ _ h => Or.inr h)
  exact ⟨hm.of_eqOff hfr (hm.disj_words.mono (by simp only [schurFp]; fp_sub) le_rfl),
    by rw [hfr₃.2 L 0 (by simp [Store.inBlock]; omega), hx₂],
    exists_holdsMatrix_of_mul hA₂ hmul⟩


omit [Has IndexOp O] [Has CmpTst Q] in
/-- The positive branch of the pipeline runs to completion on any scalar machine with completing
stages. -/
theorem schurPipeline_pos_completes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (h0 : Mch.lit 0 = 0) (h1 : Mch.lit 1 = 1)
    {Reg Red Core : Impl O Q} {n k F T L : ℕ} {qR qC : List ℝ}
    (hReg : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {a q : ℕ × ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      HoldsMatrix a A μ.store → μ.store.readBlock q.1 q.2 qR.length = some qR → μ.Live [a, q] →
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock q.1 q.2 qR.length) →
      Writes .total I τ Reg.body (Env.frame [n + 1, qR.length] [a, q, a])
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (fun μ' => ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A' μ'.store) μ)
    (hRed : CompletingReducer (n + 1) Red I) (hCore : CompletingSchurCore k F T (n + 1) qC Core I)
    {a p uo f : ℕ × ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {m : Mem ℝ} (hm : SchurPipelineMem n (qR ++ qC) a p uo f L m)
    (hA : HoldsMatrix a A m.store) {x : ℝ} (hx : m.store.get L 0 = some x) (τ : Tape ℝ) :
    Writes .total I τ ((Stmt.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨6, .const 0⟩]).seq
        ((Stmt.call (Has.inj ScalarOp.div) [] [⟨6, .const 0⟩, ⟨5, .const 0⟩] [⟨6, .const 0⟩]).seq
          ((Stmt.loop (.const 2 * (.var 0 * .var 0)) (.call (Has.inj ScalarOp.mul) []
            [⟨0, .var 6 + .var 11⟩, ⟨6, .const 0⟩] [⟨0, .var 6 + .var 11⟩])).seq
          ((Stmt.frame [.var 0, .var 1] [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩] Reg.body).seq
            ((Stmt.frame [.var 0] [⟨3, .var 9⟩]
              (PairMatrix.identity (Op := O) (Tst := Q)).body).seq
            ((Stmt.frame [.var 0] [⟨0, .var 6⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩]
              Red.body).seq
            ((Stmt.frame [.var 0, .var 2, .var 3, .var 4, .var 5]
              [⟨0, .var 6⟩, ⟨1, .var 7 + .var 1⟩, ⟨3, .var 9⟩, ⟨0, .var 6⟩, ⟨3, .var 9⟩,
                ⟨4, .var 10⟩] Core.body).seq (.loop (.const 2 * (.var 0 * .var 0))
              (.call (Has.inj ScalarOp.mul) [] [⟨0, .var 6 + .var 11⟩, ⟨5, .const 0⟩]
                [⟨0, .var 6 + .var 11⟩])))))))))
      (schurPipelineEnv n qR.length qC.length k F T a p uo f L)
      (schurFp n a uo f ⊔ Store.inBlock (L + 1) 0 1) (fun _ => True) m := by
  obtain ⟨hlen, ha, hp, hu, hf, -, -, -, hap, hq⟩ := id hm
  obtain ⟨h1', h2, h3, -, -, h6⟩ := apart_four hap
  set G := schurFp n a uo f ⊔ Store.inBlock (L + 1) 0 1
  have hFa : Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ≤ G :=
    fun _ _ h => Or.inl (Or.inl (Or.inl h))
  have hFu : Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ≤ G :=
    fun _ _ h => Or.inl (Or.inl (Or.inr h))
  have hdG : Fp.Disj G (Store.inBlock p.1 p.2 (qR ++ qC).length) :=
    hm.disj_words.mono (sup_le (fun _ _ h => Or.inl (Or.inl h)) (fun _ _ h => Or.inr h)) le_rfl
  refine Writes.congr_eval (eval_seq_seq_seq_assoc _ _ _ _ _ _ _) ?_
  refine (schurPipeline_scale_completes hS hm hA hx).seq_le
    (sup_le (fun _ _ h => Or.inr h) hFa) fun m₁ hfr₁ h₁ => ?_
  obtain ⟨hm₁, hx₁, A₁, hA₁⟩ := h₁
  refine (hReg A₁ hA₁ (Store.readBlock_append_left hm₁.2.2.2.2.2.2.2.2.2)
    (hm₁.live_of_subset (by simp)) (h1'.mono le_rfl (Fp.inBlock_le_inBlock le_rfl
      (by simp)))).frame_seq_le rfl rfl (hm₁.live_of_subset (by simp)) hFa
    fun m₂ hfr₂ h₂ => ?_
  obtain ⟨A₂, hA₂⟩ := h₂
  have hm₂ := hm₁.of_eqOff hfr₂ (hdG.mono hFa le_rfl)
  refine (writes_identity_holdsMatrix_one_of_lit (N := n + 1) hS h0 h1 hm₂.room_uo).frame_seq_le
    rfl rfl (hm₂.live_of_subset (by simp)) hFu fun m₃ hfr₃ hU => ?_
  have hm₃ := hm₂.of_eqOff hfr₃ (hdG.mono hFu le_rfl)
  refine (hRed A₂ 1 le_rfl ⟨hA₂.of_eqOff hfr₃ h2.symm, hU⟩ (hm₃.live_of_subset (by simp))
    h2).frame_seq_le rfl rfl (hm₃.live_of_subset (by simp)) (sup_le hFa hFu)
    fun m₄ hfr₄ h₄ => ?_
  obtain ⟨U₁, H, hp₄⟩ := h₄
  have hm₄ := hm₃.of_eqOff hfr₄ (hdG.mono (sup_le hFa hFu) le_rfl)
  obtain ⟨hlen₄, -, -, -, -, -, -, -, -, hq₄⟩ := id hm₄
  refine (hCore H U₁ le_rfl hp₄ (Store.readBlock_append_right hq₄) (fun z hz => ?_)
    (by have := hm₄.room_f; omega) (apart_tail hap)).frame_seq_le rfl rfl
    (fun z hz => ?_) (fun _ _ h => Or.inl h) fun m₅ hfr₅ h₅ => ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp only [hlen₄] <;> omega
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [hlen₄] <;> omega
  obtain ⟨U₂, Tm, hT₅, hU₅⟩ := h₅
  have hm₅ := hm₄.of_eqOff hfr₅ (hdG.mono (fun _ _ h => Or.inl h) le_rfl)
  have hx₅ : m₅.store.get L 0 = some x := by
    rw [hfr₅.2 L 0 (not_schurFp_of_le ha hu hf le_rfl), hfr₄.2 L 0 (fun h => by
      rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> omega), hfr₃.2 L 0 (fun h => by obtain ⟨h, -⟩ := h; omega),
      hfr₂.2 L 0 (fun h => by obtain ⟨h, -⟩ := h; omega), hx₁]
  exact (writes_loop_mul_cell hS (N := 2 * ((n + 1) * (n + 1))) (b := a.1) (o := a.2)
    (y := (L, 0)) (r := x) rfl (fun t _ => rfl) (fun t _ => rfl)
    (hm₅.live_of_subset (by simp)) (fun t ht => ⟨_, Store.get_of_readBlock hT₅ ht 0⟩) hx₅
    (by rintro ⟨h, -⟩; omega)).mono hFa fun _ _ _ => trivial

omit [Has CmpTst Q] in
/-- The zero branch of the pipeline runs to completion on any scalar machine. -/
theorem schurPipeline_zero_completes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) {n nr nq k F T L : ℕ} {qs : List ℝ}
    {a p uo f : ℕ × ℕ} {τ : Tape ℝ} {m : Mem ℝ} (hm : SchurPipelineMem n qs a p uo f L m) :
    Writes .total I τ (.seq (.frame [.var 0] [⟨3, .var 9⟩]
        (PairMatrix.identity (Op := O) (Tst := Q)).body)
        (.call (Has.inj IndexOp.lit) [.const 0] [] [⟨4, .var 10⟩]))
      (schurPipelineEnv n nr nq k F T a p uo f L) (schurFp n a uo f) (fun _ => True) m := by
  refine (PairMatrix.writes_identity (n := n + 1) hS hm.room_uo).frame_seq_le rfl rfl
    (hm.live_of_subset (by simp)) (by simp only [schurFp]; fp_sub) fun m' hfr _ => ?_
  have hf : f.2 < m'.store.len f.1 := by have := hm.room_f; rw [hfr.len_eq]; omega
  exact (writes_indexLit hL (n := 0) rfl rfl hf).mono (by simp only [schurFp]; fp_sub)
    fun _ _ _ => trivial

/-- The pipeline runs to completion on any scalar machine with exact natural literals up to
$n + 1$, index literals and exact comparisons, given stages that complete: it writes only the
matrix, the accumulator and the flag. No rounding model is needed. -/
theorem schurPipelineWith_completes {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hC : IsCmp id I) {Nm Reg Red Core : Impl O Q} {k F T : ℕ} {qR qC : List ℝ}
    (hNm : CompletingNormEstimate (n + 1) Nm I)
    (hReg : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {a q : ℕ × ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      HoldsMatrix a A μ.store → μ.store.readBlock q.1 q.2 qR.length = some qR → μ.Live [a, q] →
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock q.1 q.2 qR.length) →
      Writes .total I τ Reg.body (Env.frame [n + 1, qR.length] [a, q, a])
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (fun μ' => ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A' μ'.store) μ)
    (hRed : CompletingReducer (n + 1) Red I) (hCore : CompletingSchurCore k F T (n + 1) qC Core I)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (qR ++ qC) a p uo f A μ) (τ : Tape ℝ) :
    Writes .total I τ (schurPipelineWith Nm Reg Red Core).body
      (Env.frame [n + 1, qR.length, qC.length, k, F, T] [a, p, a, uo, f]) (schurFp n a uo f)
      (fun _ => True) μ := by
  have h1 : Mch.lit 1 = 1 := by simpa using hNat 1 (by omega)
  have h0 : Mch.lit 0 = 0 := by simpa using hNat 0 (by omega)
  change Writes .total I τ (Stmt.allocs [.const 1, .const 1] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [1, 1]) rfl (fun _ _ => trivial) ?_
  intro s₁ hlen hlens hBelow
  obtain ⟨hm, hA⟩ := hin.mem_of_alloc (q := μ.pos) hlen hlens hBelow
  set L := μ.store.length
  change Writes .total I τ _ (schurPipelineEnv n qR.length qC.length k F T a p uo f L) _ _ _
  obtain ⟨-, ha, hp, hu, hf, -, hLl, -⟩ := id hm
  have hlive : (⟨s₁, μ.pos⟩ : Mem ℝ).Live [a, (L, 0)] := hm.live_of_subset (by simp)
  have hFL : Store.inBlock L 0 1 ≤ schurFp n a uo f ⊔ Fp.above L :=
    fun _ _ h => Or.inr (h.1 ▸ le_rfl)
  refine (hNm A le_rfl hA hlive (show 0 + 1 ≤ s₁.len L by simp at hLl ⊢; omega)
    (show a.1 ≠ L by omega)).frame_seq_le rfl rfl hlive hFL fun m hfr ⟨x, hx⟩ => ?_
  have hm' := hm.of_eqOff hfr (Fp.disj_inBlock_of_ne (by omega))
  have hA' := hA.of_eqOff hfr (Fp.disj_inBlock_of_ne (by omega))
  refine writes_ite rfl rfl (hC.test_isPos (x := (L, 0)) (d := []) hx) ?_
  by_cases hx0 : 0 < x
  · simp only [id, hx0, decide_true, if_true]
    exact (schurPipeline_pos_completes hS h0 h1 hReg hRed hCore hm' hA' hx τ).mono
      (sup_le le_sup_left (fun b _ h => Or.inr (show L ≤ b by rw [h.1]; omega))) fun _ _ h => h
  · simp only [id, hx0, decide_false, Bool.false_eq_true, if_false]
    exact (schurPipeline_zero_completes hS hL hm').mono le_sup_left fun _ _ h => h

end Steps

section Dense

variable [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]

/-- The dense Schur solver runs to completion on every tape and on any scalar machine: with
index literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons, draws that
store the tape entry and an exact polar disk sampler, for any $\delta, \varphi$ and every complex
$\mathbf{A}$ of order $n + 1$, the run of `denseSchur` from a memory holding $\mathbf{A}$ and the
words of `denseSchurParams` succeeds and writes only $\mathbf{A}$, $\widehat{\mathbf{U}}$ and the
flag. No rounding model is needed (`NLAlib.Schur.schurPipelineWith_completes`); the
orthogonality under the standard model is `NLAlib.Schur.denseSchur_terminates`. -/
theorem denseSchur_completes {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ φ : ℝ}
    {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (denseSchurParams n δ φ) a p uo f A μ) (τ : Tape ℝ) :
    Writes .total I τ (denseSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDims n δ φ) [a, p, a, uo, f]) (schurFp n a uo f) (fun _ => True)
      μ := by
  have hReg : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {a q : ℕ × ℕ}
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), HoldsMatrix a A μ.store →
      μ.store.readBlock q.1 q.2 (denseSchurRegParams n δ φ).length =
        some (denseSchurRegParams n δ φ) → μ.Live [a, q] →
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock q.1 q.2 (denseSchurRegParams n δ φ).length) →
      Writes .total I τ (ginibrePerturb (O := O) (Q := Q) sG).body
        (Env.frame [n + 1, (denseSchurRegParams n δ φ).length] [a, q, a])
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (fun μ' => ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A' μ'.store) μ :=
    fun A hA hq hl _ => (SmallEig.ginibrePerturb_writes_word hS hL hSmp hl hA
      (Store.get_of_readBlock hq (j := 0) (by simp [denseSchurRegParams,
        SmallEig.length_smallEigParams]) 0)).mono le_rfl fun _ _ h => ⟨_, h.2⟩
  have hCore : CompletingSchurCore (denseSchurDegree n δ φ) (denseSchurCap n δ φ)
      (denseSchurLeafCap n δ φ) (n + 1)
      (denseSchurThreshold n δ φ :: (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ))
      (roundedShQRSchur (O := O) (Q := Q) sG) I := by
    rw [← shqrSchurParams_eq]
    have h12 := length_smallEigParams (denseSchurDegree n δ φ) (4 * 8)
      (forwardBackwardError (denseSchurDegree n δ φ) (4 * 8)
        (shqrSmallEigAccuracy n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
          (denseSchurDelta n δ)))
      (shqrSmallEigFailure n (2 * denseSchurB n δ φ) (denseSchurΓ n δ φ / 2) 8
        (denseSchurDelta n δ) (φ / 2)) ginibreGapTail ginibreConditionTail
    intro n' a p uo f tape μ H U hn hHU hp hl hf ha
    exact roundedShQRSchurWith_completing (B := 2 * denseSchurB n δ φ)
      (Γ := denseSchurΓ n δ φ / 2) (S := 8) (δ := denseSchurDelta n δ) (φ := φ / 2)
      hS hL hNat hQ hC hDisk rfl
      (smallEigProg_completes (kmax := min (denseSchurDegree n δ φ) (n + 1)) hS hL
        (hNat.mono (min_le_right _ _)) hC hQ hSmp hDisk (smallEigCaps_smallEigParams _ _ _ _ _ _)
        h12.ge) h12 H U hn hHU hp hl hf ha
  exact schurPipelineWith_completes hS hL hNat hC (frobNormStage_completing hS (n + 1)) hReg
    (hessenbergReduceQ_completing hS hC hQ hL hNat (by omega)) hCore hin τ

end Dense

end NLAlib.Schur
