/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.ResidualCheck
public import NLAlib.Eigensolvers.Schur.Pipeline

/-!
# A verified Schur solver

`NLAlib.Schur.verifiedSchurWith Solve` runs any Schur solver `Solve` (the interface of the
pipeline, `[N, nr, nq, k, F, T] (A, P) → (A, U, Fl)`) on the matrix, keeping a copy
$\mathbf{A}_0$, and then the residual check `NLAlib.Schur.schurResidualCheck` on
$(\mathbf{A}_0, \widehat{\mathbf{U}}, \widehat{\mathbf{T}})$ with the words $\theta, \kappa$, which
writes the flag. The flag is then a certificate: **on every tape**, flag $0$ implies that
$\widehat{\mathbf{T}}$ is upper triangular and
$\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le
\delta\|\mathbf{A}\|_2$, whatever the solver did. Only the chance of a nonzero flag depends on the
solver's probabilistic contract.

## Main definitions

* `NLAlib.Schur.TerminatingSchurSolver`: a solver that terminates on every tape.
* `NLAlib.Schur.verifiedSchurWith`: the verified program.
* `NLAlib.Schur.VerifiedSchurOutput`: its every-tape output.

## Main results

* `NLAlib.Schur.verifiedSchurWith_writes`: termination and the flag-conditional Schur output on
  every tape.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops MeasureTheory
open scoped Matrix

variable {O Q : Type}

/-- **A Schur solver that terminates on every tape** at the order $n + 1$, the dimensions `d` and
the words `qs`: from every input of the pipeline (`NLAlib.Schur.SchurPipelineInput`) and on every
tape, the run writes only the matrix, the accumulator and the flag, and stores a matrix and an
accumulator $\widehat{\mathbf{U}}$ with $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} -
\mathbf{I}\|_2 \le e_U$ (`NLAlib.Schur.SchurOrth`). -/
def TerminatingSchurSolver (eU : ℝ) (n : ℕ) (d : List ℕ) (qs : List ℝ) (Solve : Impl O Q)
    (I : Interp O Q ℝ) : Prop :=
  ∀ {τ : Tape ℝ} {μ : Mem ℝ} {a p uo f : ℕ × ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    SchurPipelineInput qs a p uo f A μ →
    Writes .total I τ Solve.body (Env.frame d [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOrth (n := n) a uo eU) μ

/-- **The output of a verified Schur solver** on every tape: the stored matrix and accumulator
of `NLAlib.Schur.SchurOrth`, the flag the literal $0$ or the literal $1$, and, if the flag is
$0$, a Schur output (`NLAlib.Schur.SchurOutput`) of $\mathbf{A}$ with the errors $\delta$ and
$e_U$. -/
def VerifiedSchurOutput (M : Machine ℝ) {n : ℕ} (a uo f : ℕ × ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (δ eU : ℝ) (μ' : Mem ℝ) : Prop :=
  SchurOrth (n := n) a uo eU μ' ∧
    (μ'.store.get f.1 f.2 = some 0 ∨ μ'.store.get f.1 f.2 = some (M.lit 1)) ∧
    (μ'.store.get f.1 f.2 = some 0 → SchurOutput a uo f A δ eU μ')

/-- **A probabilistic block from its failure bound at one memory**: under a measurable
interpretation whose operations read the tape only in their windows, if the run of `c` from `m`
misses its frame or `Post` with probability at most $\varphi$ under every tape with the stream
laws, and the outcomes (the frame and `Post`) form a measurable set, then the block meets
`NLAlib.Ops.PWrites` from `m`, with the good set "the run succeeds". -/
theorem _root_.NLAlib.Ops.PWrites.of_measureReal_le {Op Tst : Type} {I : Interp Op Tst ℝ}
    (hI : I.IsMeasurable) {win : Op → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {c : Stmt Op Tst} {ρ : Env} {F : Fp} {Post : Mem ℝ → Prop} {φ : ℝ}
    {m : Mem ℝ}
    (hT : MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧ Post x.2})
    (h : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ},
      IsTapeLaw law P ξ → P.real {ω | ¬ Writes .total I (ξ ω) c ρ F Post m} ≤ φ) :
    PWrites law I c ρ F (· = m) Post φ := by
  have hev := hI.measurable_eval c ρ
  have hsw : Measurable fun x : Mem ℝ × Tape ℝ => (x.2, x.1) :=
    measurable_snd.prodMk measurable_fst
  refine ⟨fun m' => {τ | Writes .total I τ c ρ F Post m'}, ?_, fun m' τ τ' hττ' => ?_,
    fun m' hm' => ?_⟩
  · have e : {x : Mem ℝ × Tape ℝ | x.2 ∈ {τ | Writes .total I τ c ρ F Post x.1}} =
        {x | (eval I x.2 c ρ x.1).isSome = true} ∩
          {x | (x.1, (eval I x.2 c ρ x.1).getD x.1) ∈
            {y : Mem ℝ × Mem ℝ | y.1.store.EqOff F y.2.store ∧ Post y.2}} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Writes, Wp, Mode.Holds]
      cases eval I x.2 c ρ x.1 <;> simp
    rw [e]
    exact ((hev.1.comp hsw) (measurableSet_singleton true)).inter
      ((measurable_fst.prodMk (hev.2.comp hsw)) hT)
  · have := Follows.eq_of_agree (f := fun τ m => eval I τ c ρ m)
      (fun τ τ' => run_follows hloc τ τ' c ρ) (m := m') hττ'
    simp only [Set.mem_ofPred_eq, Writes, Wp, this]
  · subst hm'
    exact ⟨fun τ hτ => hτ, fun P ξ hξ => h hξ⟩

/-! ### The memory of a verified run -/

/-- The input of the pipeline is kept by any memory agreeing with it below a bound on its
buffers. -/
theorem SchurPipelineInput.of_below {n : ℕ} {qs : List ℝ} {a p uo f : ℕ × ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {μ μ' : Mem ℝ}
    (h : SchurPipelineInput qs a p uo f A μ) {L : ℕ} (hB : Store.Below L μ.store μ'.store)
    (hlt : ∀ z ∈ [a, p, uo, f], z.1 < L) (hlen : L ≤ μ'.store.length) :
    SchurPipelineInput qs a p uo f A μ' := by
  obtain ⟨hl, hroom, hap, hA, hP⟩ := h
  refine ⟨fun z hz => lt_of_lt_of_le (hlt z hz) hlen, ?_, hap,
    hA.of_below hB (hlt a (by simp)), by rw [hB.readBlock (hlt p (by simp))]; exact hP⟩
  rw [Mem.room_eq_of_below hB hlt]
  exact hroom

/-- The input of the verified solver, with the words $\theta, \kappa$ after the solver's words
`qs`, holds the input of the solver. -/
theorem SchurPipelineInput.head {n : ℕ} {θ κ : ℝ} {qs : List ℝ} {a p uo f : ℕ × ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {μ : Mem ℝ}
    (h : SchurPipelineInput (qs ++ [θ, κ]) a p uo f A μ) :
    SchurPipelineInput qs a p uo f A μ := by
  obtain ⟨hl, hroom, hap, hA, hP⟩ := h
  have hsub : Store.inBlock p.1 p.2 qs.length ≤ Store.inBlock p.1 p.2 (qs ++ [θ, κ]).length :=
    Fp.inBlock_le_inBlock le_rfl (by simp)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := apart_four hap
  refine ⟨hl, ?_, ?_, hA, Store.readBlock_append_left hP⟩
  · simp only [Mem.Room, List.length_append] at hroom ⊢
    exact ⟨hroom.1, by simp at hroom; omega, hroom.2.2⟩
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨h1.mono le_rfl hsub, h2, h3⟩, ⟨h4.mono hsub le_rfl, h5.mono hsub le_rfl⟩, h6⟩

section Program

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The verified Schur solver** with a Schur solver `Solve`: copy $\mathbf{A}$ into scratch,
run `Solve` on its $n_r + n_q$ words `P[0]`, …, then the residual check
`NLAlib.Schur.schurResidualCheck` on the copy, the accumulator and the matrix with the words
$\theta$, $\kappa$ after the solver's; the check writes the flag. The interface is
`[N, nr, nq, k, F, T] (A, P) → (A, U, Fl)`.
Algorithm: verified-schur -/
def verifiedSchurWith (Solve : Impl O Q) : Impl O Q :=
  opsImpl% [N, nr, nq, k, F, T] (A, P) → (A, U, Fl) {
    let A0 ← alloc (2 * (N * N));
    run (PairMatrix.copy (Op := O) (Tst := Q)).body [N, N] (A, A0);
    run Solve.body [N, nr, nq, k, F, T] (A, P, A, U, Fl);
    run (schurResidualCheck (O := O) (Q := Q)).body [N] (A0, U, A, P[nr + nq], A, Fl)
  }

end Program

/-! ### Every tape -/

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- The size condition of the check at the order $n + 1$: $64(n + 2)^3\boldsymbol{u} \le 1$
gives $(2(n + 1)^2 + 2)\boldsymbol{u} \le 1/16$. -/
theorem norm_check_size_le {u : ℝ} (hu0 : 0 ≤ u) {n : ℕ} (hu : 64 * ((n : ℝ) + 2) ^ 3 * u ≤ 1) :
    (2 * (((n + 1 : ℕ)) : ℝ) ^ 2 + 2) * u ≤ 1 / 16 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  have : 2 * ((n : ℝ) + 1) ^ 2 + 2 ≤ 4 * ((n : ℝ) + 2) ^ 3 := by nlinarith
  nlinarith

omit [Has IndexOp O] [Has CmpTst Q] in
/-- The rounded Frobenius norm is a two-sided estimate with the factors $(15/16, 17/16)$ at the
order $n + 1$ when $64(n + 2)^3\boldsymbol{u} \le 1$. -/
theorem frobNormStage_frobNormEstimateContract_check {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu0 : 0 ≤ u) {n : ℕ}
    (hu : 64 * ((n : ℝ) + 2) ^ 3 * u ≤ 1) :
    FrobNormEstimateContract (15 / 16) (17 / 16) (n + 1) (frobNormStage (O := O) (Q := Q)) I :=
  FrobNormEstimateContract.mono (frobNormStage_frobNormEstimateContract hS hM
    (by linarith [norm_check_size_le hu0 hu])) (by linarith [norm_check_size_le hu0 hu])
    (by linarith [norm_check_size_le hu0 hu])

/-- The words of a stored Schur form: if the matrix block holds the same matrix in two stores,
the two stores agree on the block. -/
theorem HoldsMatrix.get_eq {rows cols : ℕ} {b : ℕ × ℕ} {X : Matrix (Fin rows) (Fin cols) ℂ}
    {s s' : Store ℝ} (h : HoldsMatrix b X s) (h' : HoldsMatrix b X s') {i : ℕ}
    (hi : b.2 ≤ i ∧ i < b.2 + 2 * (cols * rows)) : s'.get b.1 i = s.get b.1 i := by
  have e1 := Store.get_of_readBlock h (j := i - b.2) (by omega) 0
  have e2 := Store.get_of_readBlock h' (j := i - b.2) (by omega) 0
  rw [show b.2 + (i - b.2) = i by omega] at e1 e2
  rw [e1, e2]

/-- **The verified Schur solver on every tape**: on a scalar machine with the standard model at
$\boldsymbol{u}$, index literals and exact comparisons, with $64(n + 2)^3\boldsymbol{u} \le 1$,
$\kappa \ge 32(n + 2)^2\boldsymbol{u}$, $\theta \ge 0$ and $2\theta\sqrt{n + 1} \le \delta$, let
`Solve` be a Schur solver that terminates on every tape at the order $n + 1$, the dimensions
$(n + 1, n_r, n_q, k, F, T)$ and the words `qs`, with the accumulator within $e_U$ of
orthonormal (`NLAlib.Schur.TerminatingSchurSolver`). Then from a memory holding a complex
$\mathbf{A}$ of order $n + 1$ and the words $\theta, \kappa$, `qs`
(`NLAlib.Schur.SchurPipelineInput`),
on every tape, `NLAlib.Schur.verifiedSchurWith` terminates, writes only $\mathbf{A}$,
$\widehat{\mathbf{U}}$ and the flag, stores the flag $0$ or $1$, and if the flag is $0$:
$\widehat{\mathbf{T}}$ is upper triangular,
$\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le
\delta\|\mathbf{A}\|_2$ and $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} -
\mathbf{I}\|_2 \le e_U$. No probability and no hypothesis on $\mathbf{A}$. No printed source. -/
theorem verifiedSchurWith_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {n nr nq k F T : ℕ} {qs : List ℝ} {Solve : Impl O Q} {eU δ θ κ : ℝ}
    (hSolve : TerminatingSchurSolver eU n [n + 1, nr, nq, k, F, T] qs Solve I)
    (hu : 64 * ((n : ℝ) + 2) ^ 3 * u ≤ 1) (hκ : 32 * ((n : ℝ) + 2) ^ 2 * u ≤ κ) (hθ0 : 0 ≤ θ)
    (hθ : 2 * θ * √((n : ℝ) + 1) ≤ δ) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {a p uo f : ℕ × ℕ} {μ : Mem ℝ} (hq : qs.length = nr + nq)
    (hin : SchurPipelineInput (qs ++ [θ, κ]) a p uo f A μ)
    (τ : Tape ℝ) :
    Writes .total I τ (verifiedSchurWith Solve).body
      (Env.frame [n + 1, nr, nq, k, F, T] [a, p, a, uo, f]) (schurFp n a uo f)
      (VerifiedSchurOutput M a uo f A δ eU) μ := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hNm : FrobNormEstimateContract (15 / 16) (17 / 16) (n + 1)
      (frobNormStage (O := O) (Q := Q)) I :=
    frobNormStage_frobNormEstimateContract_check hS hM hu0 hu
  have hcast : (((n + 1 : ℕ)) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  obtain ⟨hl, hroom, hap, hA, hP⟩ := id hin
  have hlt : ∀ z ∈ [a, p, uo, f], z.1 < μ.store.length := hl
  obtain ⟨ha, hp, huo, hf⟩ : a.1 < μ.store.length ∧ p.1 < μ.store.length ∧
      uo.1 < μ.store.length ∧ f.1 < μ.store.length :=
    ⟨hlt a (by simp), hlt p (by simp), hlt uo (by simp), hlt f (by simp)⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := apart_four hap
  unfold verifiedSchurWith
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0)] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2 * ((n + 1) * (n + 1))]) rfl
    (fun hBelow h => ?keep) ?_
  case keep =>
    obtain ⟨⟨⟨T, hT⟩, U, hU, ho⟩, hfl, hout⟩ := h
    have hg := (hBelow f.1 hf).2 f.2
    refine ⟨⟨⟨T, hT.of_below hBelow ha⟩, U, hU.of_below hBelow huo, ho⟩, by rw [hg]; exact hfl,
      fun h0 => ?_⟩
    obtain ⟨-, U', T', hT', hU', hTu, hr, ho'⟩ := hout (by rw [← hg]; exact h0)
    exact ⟨h0, U', T', hT'.of_below hBelow ha, hU'.of_below hBelow huo, hTu, hr, ho'⟩
  intro s₁ hlen hlens hBelow
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  have hL0 : s₁.len L = 2 * ((n + 1) * (n + 1)) := by simpa using hlens 0 (by simp)
  have hin₁ := hin.of_below (μ' := ⟨s₁, μ.pos⟩) hBelow hlt (by simp only; omega)
  have hlv : ∀ (m : Mem ℝ), m.store.length = s₁.length → ∀ zs : List (ℕ × ℕ),
      (∀ z ∈ zs, z.1 = a.1 ∨ z.1 = p.1 ∨ z.1 = uo.1 ∨ z.1 = f.1 ∨ z.1 = L) → m.Live zs := by
    intro m hm zs hzs z hz
    rw [hm, hlen]
    rcases hzs z hz with h | h | h | h | h <;> rw [h] <;> omega
  have hne : ∀ {b o n b' o' n' : ℕ}, b ≠ b' →
      Fp.Disj (Store.inBlock b o n) (Store.inBlock b' o' n') := fun h => Fp.disj_inBlock_of_ne h
  -- the copy
  refine (PairMatrix.writes_copy (K := ℝ) (Op := O) (Tst := Q) hS (md := .total) (τ := τ)
    (m := ⟨s₁, μ.pos⟩) (rows := n + 1) (cols := n + 1) (x := a) (y := (L, 0))
    (hlv _ rfl _ (by simp)) (Or.inl (hne (by simp; omega))) hin₁.2.2.2.1
    (by simp only [hL0]; omega)).frame_seq_le rfl rfl (hlv _ rfl _ (by simp))
    (fun _ _ h => Or.inr (h.1 ▸ le_rfl)) fun m₁ hfr₁ ⟨_, hA0⟩ => ?_
  have hB₁ : Store.Below L s₁ m₁.store := hfr₁.below_of_above fun b i h => h.1 ▸ le_rfl
  have hin₂ := hin₁.of_below (μ' := m₁) hB₁ hlt (by rw [hfr₁.length_eq]; simp only; omega)
  have hA0' : HoldsMatrix (L, 0) A m₁.store := hA0
  -- the solver
  refine (hSolve A hin₂.head).frame_seq_le rfl rfl (hlv _ hfr₁.length_eq _ (by simp))
    (fun _ _ h => Or.inl h) fun m₂ hfr₂ ⟨⟨T, hT⟩, U, hU, ho⟩ => ?_
  have hA0₂ : HoldsMatrix (L, 0) A m₂.store := hA0'.of_eqOff hfr₂ (by
    simp only [schurFp, Fp.disj_sup_left]
    exact ⟨⟨hne (by simp; omega), hne (by simp; omega)⟩, hne (by simp; omega)⟩)
  have hl₂ := hlv m₂ (hfr₂.length_eq.trans hfr₁.length_eq)
  have hdp : Fp.Disj (schurFp n a uo f) (Store.inBlock p.1 p.2 (qs ++ [θ, κ]).length) := by
    simp only [schurFp, Fp.disj_sup_left]
    exact ⟨⟨h1, h4.symm⟩, h5.symm⟩
  have hp₂ : m₂.store.readBlock p.1 (p.2 + nr + nq) [θ, κ].length = some [θ, κ] := by
    rw [Nat.add_assoc, ← hq]
    exact Store.readBlock_append_right (hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) hdp
      hin₂.2.2.2.2)
  have hroom₂ : f.2 < m₂.store.len f.1 := by
    have := hin₂.2.1.2.2.2.1; rw [hfr₂.len_eq]; omega
  have hp2 : Store.inBlock p.1 (p.2 + nr + nq) 2 ≤
      Store.inBlock p.1 p.2 (qs ++ [θ, κ]).length :=
    Fp.inBlock_le_inBlock (by omega) (by simp; omega)
  have hap' : Fp.Apart [(L, 0), uo, a, (p.1, p.2 + nr + nq), f]
      [2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), 2, 1] := by
    simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨hne (by simp; omega), hne (by simp; omega), hne (by simp; omega),
      hne (by simp; omega)⟩, ⟨h2.symm, h4.symm.mono le_rfl hp2, h6⟩, ⟨h1.mono le_rfl hp2, h3⟩,
      h5.mono hp2 le_rfl⟩
  -- the check
  refine ((schurResidualCheck_writes hS hM hL hC hNm (a0 := (L, 0)) (uo := uo) (t := a)
    (p := (p.1, p.2 + nr + nq)) (f := f) hA0₂ hU hT hp₂ (hl₂ _ (by simp)) hroom₂
    hap').in_frame rfl rfl
    (hl₂ _ (by simp))).mono (sup_le (fun _ _ h => Or.inl (Or.inl (Or.inl h)))
      (fun _ _ h => Or.inl (Or.inr h))) fun m₃ hfr₃ hout => ?_
  have hU₃ : HoldsMatrix uo U m₃.store := hU.of_eqOff hfr₃ (by
    simp only [Fp.disj_sup_left]; exact ⟨h2, h6.symm⟩)
  have hz : M.lit 0 = 0 := hM.zero
  refine ⟨⟨⟨upperPart T, hout.1⟩, U, hU₃, ho⟩, by rw [← hz]; exact hout.flag_cases,
    fun h0 => ⟨h0, U, upperPart T, hout.1, hU₃, upperPart_isUpperTriangular T, ?_, ho⟩⟩
  have hF := hout.frobNorm_sub_le hM (by rw [hcast]; exact hu) (by rw [hcast]; exact hκ) hθ0 h0
  have hFA := frobNorm_le_sqrt_card_mul_specNorm A
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hFA
  have hsA := specNorm_nonneg A
  calc specNorm (A - U * upperPart T * Uᴴ) ≤ frobNorm (A - U * upperPart T * Uᴴ) :=
        specNorm_le_frobNorm _
    _ ≤ 2 * θ * frobNorm A := hF
    _ ≤ 2 * θ * (√((n : ℝ) + 1) * specNorm A) :=
        mul_le_mul_of_nonneg_left hFA (by positivity)
    _ = 2 * θ * √((n : ℝ) + 1) * specNorm A := by ring
    _ ≤ δ * specNorm A := mul_le_mul_of_nonneg_right hθ hsA

omit [Has IndexOp O] [Has CmpTst Q] in
/-- The norm of a residual in the Frobenius norm from the spectral one: at order $n + 1$,
$\|\mathbf{A} - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_2 \le \delta'\|\mathbf{A}\|_2$ with
$\sqrt{n + 1}\,\delta' \le \theta/8$ gives the Frobenius residual at most
$(\theta/8)\|\mathbf{A}\|_{\mathsf F}$. -/
theorem frobNorm_sub_le_of_specNorm_sub_le {n : ℕ} {A U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {δ' θ : ℝ} (h : specNorm (A - U * T * Uᴴ) ≤ δ' * specNorm A) (hθ : 0 ≤ θ)
    (hδ' : √((n : ℝ) + 1) * δ' ≤ θ / 8) :
    frobNorm (A - U * T * Uᴴ) ≤ θ / 8 * frobNorm A := by
  have h1 := frobNorm_le_sqrt_card_mul_specNorm (A - U * T * Uᴴ)
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at h1
  have hs := Real.sqrt_nonneg ((n : ℝ) + 1)
  have hA := specNorm_le_frobNorm A
  have hA0 := specNorm_nonneg A
  have hδ0 : 0 ≤ δ' * specNorm A := le_trans (specNorm_nonneg _) h
  calc frobNorm (A - U * T * Uᴴ) ≤ √((n : ℝ) + 1) * (δ' * specNorm A) :=
        h1.trans (mul_le_mul_of_nonneg_left h hs)
    _ = √((n : ℝ) + 1) * δ' * specNorm A := by ring
    _ ≤ θ / 8 * specNorm A := by
        rcases le_or_gt 0 (√((n : ℝ) + 1) * δ') with h0 | h0
        · exact mul_le_mul_of_nonneg_right hδ' hA0
        · nlinarith
    _ ≤ θ / 8 * frobNorm A := mul_le_mul_of_nonneg_left hA (by linarith)

/-- **The check passes on an accurate Schur output**: on a scalar machine with the standard model
at $\boldsymbol{u}$, index literals and exact comparisons, with $64(n + 2)^3\boldsymbol{u} \le 1$,
$0 \le \kappa \le 64(n + 2)^2\boldsymbol{u}$, $\theta \le 1$,
$4096(n + 2)^3\boldsymbol{u} \le \theta$, $e_U \le 1/2$ and $\sqrt{n + 1}\,\delta' \le \theta/8$,
from a memory holding a Schur output of $\mathbf{A}$ with the errors $\delta', e_U$, a copy of
$\mathbf{A}$ at `a0`, the words $\theta, \kappa$ at `p` and room for the flag, pairwise apart, the
check writes the flag $0$ and changes no other cell. -/
theorem schurResidualCheck_writes_of_schurOutput {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) {n : ℕ}
    {θ κ δ' eU : ℝ} (hu : 64 * ((n : ℝ) + 2) ^ 3 * u ≤ 1) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 64 * ((n : ℝ) + 2) ^ 2 * u) (hθ1 : θ ≤ 1) (huθ : 4096 * ((n : ℝ) + 2) ^ 3 * u ≤ θ)
    (heU : eU ≤ 1 / 2) (hδ' : √((n : ℝ) + 1) * δ' ≤ θ / 8) {τ : Tape ℝ} {μ : Mem ℝ}
    {a0 uo a p f : ℕ × ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hout : SchurOutput a uo f A δ' eU μ) (hA : HoldsMatrix a0 A μ.store)
    (hp : μ.store.readBlock p.1 p.2 2 = some [θ, κ]) (hl : μ.Live [a0, uo, a, p, f])
    (hf : f.2 < μ.store.len f.1)
    (hap : Fp.Apart [a0, uo, a, p, f]
      [2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), 2, 1]) :
    Writes .total I τ (schurResidualCheck (O := O) (Q := Q)).body
      (Env.frame [n + 1] [a0, uo, a, p, a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ μ.store.EqOff (Store.inBlock f.1 f.2 1) μ'.store)
      μ := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hcast : (((n + 1 : ℕ)) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  obtain ⟨-, U, T, hT, hU, hTu, hr, ho⟩ := hout
  refine (schurResidualCheck_writes hS hM hL hC
    (frobNormStage_frobNormEstimateContract_check hS hM hu0 hu) hA hU hT hp hl hf hap).mono
    le_rfl fun μ' hfr hc => ⟨?_, ?_⟩
  · refine hc.flag_eq_zero hM (by rw [hcast]; exact hu) hκ0 (by rw [hcast]; exact hκ) hθ1
      (by rw [hcast]; exact huθ) (ho.trans heU) ?_
    rw [upperPart_eq_self hTu]
    exact frobNorm_sub_le_of_specNorm_sub_le hr (le_trans (by positivity) huθ) hδ'
  · have hT' := hc.1
    rw [upperPart_eq_self hTu] at hT'
    refine ⟨hfr.1, fun b i hi => ?_⟩
    by_cases ha : Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) b i
    · obtain ⟨rfl, h1, h2⟩ := ha
      exact HoldsMatrix.get_eq hT hT' ⟨h1, h2⟩
    · exact hfr.get_eq fun h => h.elim ha hi

/-- **The verified Schur solver fails rarely, for any solver postcondition** (generic, the failure
event is the flag $\ne 0$ or the solver's postcondition missed): on a scalar machine with the
standard model at $\boldsymbol{u}$, index literals and exact comparisons, a measurable
interpretation reading the tape only in its windows, with $64(n + 2)^3\boldsymbol{u} \le 1$,
$0 \le \kappa \le 64(n + 2)^2\boldsymbol{u}$, $\theta \le 1$,
$4096(n + 2)^3\boldsymbol{u} \le \theta$, $e_U \le 1/2$ and $\sqrt{n + 1}\,\delta' \le \theta/8$,
let the solver `Solve`, from every input memory, end in a postcondition `Post` (measurable with its
frame) except with probability at most $\varphi$, where `Post` implies a Schur output of
$\mathbf{A}$ with the errors $\delta', e_U$, is kept when only the flag is rewritten to $0$, and is
kept by the release of scratch buffers. Then from a memory holding $\mathbf{A}$ and the words
$\theta, \kappa$, `qs`, under a tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{verifiedSchurWith}(\mathbf{A}) \text{ fails, writes outside }
  \mathbf{A}, \widehat{\mathbf{U}} \text{ and the flag, or does not store the flag } 0 \text{ and
  `Post`}\bigr] \le \varphi\,.$$
No printed source. -/
theorem verifiedSchurWith_measureReal_not_flag_le {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {n nr nq k F T : ℕ} {qs : List ℝ} {Solve : Impl O Q}
    {δ' eU θ κ φ : ℝ} {Post : Mem ℝ → Prop} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hSolve : ∀ μ', SchurPipelineInput qs a p uo f A μ' →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ}, IsTapeLaw law P ξ →
        P.real {ω | ¬ Writes .total I (ξ ω) Solve.body
          (Env.frame [n + 1, nr, nq, k, F, T] [a, p, a, uo, f]) (schurFp n a uo f)
          Post μ'} ≤ φ)
    (hPm : MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff (schurFp n a uo f) x.2.store ∧
      Post x.2})
    (hPS : ∀ μ', Post μ' → SchurOutput a uo f A δ' eU μ')
    (hPf : ∀ μ' μ'', Post μ' → μ'.store.EqOff (Store.inBlock f.1 f.2 1) μ''.store →
      μ''.store.get f.1 f.2 = some 0 → Post μ'')
    (hPb : ∀ {s s' : Store ℝ} {q : ℕ}, Store.Below μ.store.length s s' → Post ⟨s, q⟩ →
      Post ⟨s', q⟩)
    (hu : 64 * ((n : ℝ) + 2) ^ 3 * u ≤ 1) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 64 * ((n : ℝ) + 2) ^ 2 * u)
    (hθ1 : θ ≤ 1) (huθ : 4096 * ((n : ℝ) + 2) ^ 3 * u ≤ θ) (heU : eU ≤ 1 / 2)
    (hδ' : √((n : ℝ) + 1) * δ' ≤ θ / 8)
    (hq : qs.length = nr + nq) (hin : SchurPipelineInput (qs ++ [θ, κ]) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (verifiedSchurWith Solve).body
      (Env.frame [n + 1, nr, nq, k, F, T] [a, p, a, uo, f]) (schurFp n a uo f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ Post μ') μ} ≤ φ := by
  have := hξ.isProbabilityMeasure
  have hφ : 0 ≤ φ := measureReal_nonneg.trans (hSolve μ hin.head hξ)
  obtain ⟨hl, hroom, hap, hA, hP⟩ := id hin
  have hlt : ∀ z ∈ [a, p, uo, f], z.1 < μ.store.length := hl
  obtain ⟨ha, hp, huo, hf⟩ : a.1 < μ.store.length ∧ p.1 < μ.store.length ∧
      uo.1 < μ.store.length ∧ f.1 < μ.store.length :=
    ⟨hlt a (by simp), hlt p (by simp), hlt uo (by simp), hlt f (by simp)⟩
  refine PWrites.measureReal_not_writes_le (Pre := (· = μ)) ?_ rfl hξ
  unfold verifiedSchurWith
  change PWrites law I (Stmt.allocs [.const 2 * (.var 0 * .var 0)] _) _ _ _ _ _
  refine PWrites.allocs (ns := [2 * ((n + 1) * (n + 1))]) rfl
    (Pre₁ := fun L m => L = μ.store.length ∧ m.store.length = L + 1 ∧
      m.store.len L = 2 * ((n + 1) * (n + 1)) ∧ SchurPipelineInput (qs ++ [θ, κ]) a p uo f A m)
    (fun m s₁ hm hlen hlens hBelow => ?_) (fun m hm s s' q hBelow hout => ?_) fun L => ?_
  · subst hm
    simp only [List.length_cons, List.length_nil] at hlen
    exact ⟨rfl, by simpa using hlen, by simpa using hlens 0 (by simp),
      hin.of_below (μ' := ⟨s₁, m.pos⟩) hBelow hlt (by simp only; omega)⟩
  · subst hm
    exact ⟨((hBelow f.1 hf).2 f.2).trans hout.1, hPb hBelow hout.2⟩
  have hne : ∀ {b o n b' o' n' : ℕ}, b ≠ b' →
      Fp.Disj (Store.inBlock b o n) (Store.inBlock b' o' n') := fun h => Fp.disj_inBlock_of_ne h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := apart_four hap
  have hp2 : Store.inBlock p.1 (p.2 + nr + nq) 2 ≤
      Store.inBlock p.1 p.2 (qs ++ [θ, κ]).length :=
    Fp.inBlock_le_inBlock (by omega) (by simp; omega)
  have hliv : ∀ (m : Mem ℝ) (zs : List (ℕ × ℕ)), L = μ.store.length →
      m.store.length = L + 1 →
      (∀ z ∈ zs, z.1 = a.1 ∨ z.1 = p.1 ∨ z.1 = uo.1 ∨ z.1 = f.1 ∨ z.1 = L) → m.Live zs := by
    intro m zs hL hm hzs z hz
    rw [hm]
    rcases hzs z hz with h | h | h | h | h <;> rw [h] <;> omega
  refine (PWrites.seq hI hloc (φ₁ := 0) (φ₂ := φ + 0) (by linarith)
    (F₁ := Store.inBlock L 0 (2 * ((n + 1) * (n + 1))))
    (F₂ := schurFp n a uo f ⊔ (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock f.1 f.2 1))
    (Mid := fun m => L = μ.store.length ∧ m.store.length = L + 1 ∧
      SchurPipelineInput (qs ++ [θ, κ]) a p uo f A m ∧ HoldsMatrix (L, 0) A m.store) ?_
    (PWrites.seq hI hloc le_rfl (F₁ := schurFp n a uo f)
      (F₂ := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Mid := fun m => Post m ∧ L = μ.store.length ∧
      m.store.length = L + 1 ∧ HoldsMatrix (L, 0) A m.store ∧
      m.store.readBlock p.1 (p.2 + nr + nq) [θ, κ].length = some [θ, κ] ∧
        f.2 < m.store.len f.1) ?_ ?_)).mono
    (fun _ h => h) ?_ (fun _ h => h) (by linarith)
  -- the copy
  · refine PWrites.of_writes le_rfl fun m τ ⟨hL, hlen, hlenL, hin'⟩ => ?_
    have hl' := hliv m [a, (L, 0)] hL hlen (by simp)
    refine ((PairMatrix.writes_copy (K := ℝ) (Op := O) (Tst := Q) hS (md := .total) (τ := τ)
      (m := m) (rows := n + 1) (cols := n + 1) (x := a) (y := (L, 0)) hl'
      (Or.inl (hne (by simp; omega))) hin'.2.2.2.1 (by simp only [hlenL]; omega)).in_frame
      rfl rfl hl').mono le_rfl fun m₁ hfr₁ ⟨_, hA0⟩ => ⟨hL, by rw [hfr₁.length_eq, hlen],
        hin'.of_below (L := L) (hfr₁.below_of_above fun b i h => h.1 ▸ le_rfl)
          (fun z hz => by have := hlt z hz; omega) (by rw [hfr₁.length_eq]; omega), hA0⟩
  -- the solver
  · refine PWrites.mono_eqOff (PWrites.in_frame (PWrites.of_forall_eq hI hloc
      (Pre := fun m => SchurPipelineInput qs a p uo f A m)
      (fun m hm => PWrites.of_measureReal_le hI hloc hPm (hSolve m hm)) hPm) rfl rfl
      fun m hm => ?_) (fun m hm => hm.2.2.1.head) fun m m' ⟨hL, hlen, hin', hA0⟩ hfr hpost => ?_
    · obtain ⟨hl', -⟩ := hm
      have hl'' : ∀ z ∈ [a, p, uo, f], z.1 < m.store.length := hl'
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      exacts [hl'' _ (by simp), hl'' _ (by simp), hl'' _ (by simp), hl'' _ (by simp),
        hl'' _ (by simp)]
    · have hdp : Fp.Disj (schurFp n a uo f) (Store.inBlock p.1 p.2 (qs ++ [θ, κ]).length) := by
        simp only [schurFp, Fp.disj_sup_left]
        exact ⟨⟨h1, h4.symm⟩, h5.symm⟩
      refine ⟨hpost, hL, by rw [hfr.length_eq, hlen], hA0.of_eqOff hfr (by
        simp only [schurFp, Fp.disj_sup_left]
        exact ⟨⟨hne (by simp; omega), hne (by simp; omega)⟩, hne (by simp; omega)⟩),
        by rw [Nat.add_assoc, ← hq]; exact Store.readBlock_append_right (hfr.keep
          (Store.readsOnly_readBlock _ _ _ _) hdp hin'.2.2.2.2),
        by have := hin'.2.1.2.2.2.1; rw [hfr.len_eq]; omega⟩
  -- the check
  · refine PWrites.of_writes le_rfl fun m τ ⟨hpost, hLμ, hlen, hA0, hpw, hfm⟩ => ?_
    have hl' := hliv m [(L, 0), uo, a, (p.1, p.2 + nr + nq), f] hLμ hlen (by simp)
    have hap' : Fp.Apart [(L, 0), uo, a, (p.1, p.2 + nr + nq), f]
        [2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), 2, 1] := by
      simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
        and_true]
      exact ⟨⟨hne (by simp; omega), hne (by simp; omega), hne (by simp; omega),
        hne (by simp; omega)⟩, ⟨h2.symm, h4.symm.mono le_rfl hp2, h6⟩, ⟨h1.mono le_rfl hp2, h3⟩,
        h5.mono hp2 le_rfl⟩
    refine ((schurResidualCheck_writes_of_schurOutput hS hM hL hC hu hκ0 hκ hθ1 huθ heU hδ'
      (hPS m hpost) hA0 hpw hl' hfm hap').in_frame rfl rfl
      (hliv m _ hLμ hlen (by simp))).mono le_rfl
      fun m'' _ ⟨h0, hfr⟩ => ⟨h0, hPf m m'' hpost hfr h0⟩
  -- the footprint
  · refine sup_le (fun _ _ h => Or.inr (h.1 ▸ le_rfl)) (sup_le le_sup_left ?_)
    intro b i h
    rcases h with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr h)

/-! ### Work -/

omit [Has IndexOp O] [Has CmpTst Q] in
/-- The instructions of the copy of a square matrix: the instrumented static count of
`NLAlib.Ops.PairMatrix.copy` at the order $n + 1$ and zero offsets is at most $32(n + 1)^2$. -/
theorem size_stmtCost_copy_le (n : ℕ) :
    Count.size (stmtCost (PairMatrix.copy (Op := O) (Tst := Q)).body.instrument
      [n + 1, n + 1, 0, 0]) ≤ 32 * (n + 1) ^ 2 := by
  have hw : stmtWorkMono (PairMatrix.copy (Op := O) (Tst := Q)).body.instrument
      [⟨1, [1]⟩, ⟨1, [1]⟩, WorkMono.const 0, WorkMono.const 0] = ⟨32, [2]⟩ := by
    rw [stmtWorkMono_instrument]; kernel_rfl
  have hσ : SlotsLe [n + 1] [n + 1, n + 1, 0, 0]
      [⟨1, [1]⟩, ⟨1, [1]⟩, WorkMono.const 0, WorkMono.const 0] := by
    simp [SlotsLe, WorkMono.eval, WorkMono.const]
  have h := size_stmtCost_le_stmtWorkMono (by simp)
    (PairMatrix.copy (Op := O) (Tst := Q)).body.instrument hσ
  rw [hw] at h
  simpa [WorkMono.eval] using h

/-- **The instructions of the residual check**: the instrumented static count of
`NLAlib.Schur.schurResidualCheck` at the order $n + 1$, the words at the offset $q$ and the other
offsets zero is at most $1619(n + 1)^3$ (the monomial bound, by `kernel_rfl`); the two products
dominate. -/
theorem size_stmtCost_schurResidualCheck_le (n q : ℕ) :
    Count.size (stmtCost (schurResidualCheck (O := O) (Q := Q)).body.instrument
      [n + 1, 0, 0, 0, q, 0, 0]) ≤ 1619 * (n + 1) ^ 3 := by
  have hw : stmtWorkMono (schurResidualCheck (O := O) (Q := Q)).body.instrument
      [⟨1, [1]⟩, WorkMono.const 0, WorkMono.const 0, WorkMono.const 0, ⟨1, [0, 1]⟩,
        WorkMono.const 0, WorkMono.const 0] = ⟨1619, [3]⟩ := by
    rw [stmtWorkMono_instrument]; kernel_rfl
  have hσ : SlotsLe [n + 1, q + 1] [n + 1, 0, 0, 0, q, 0, 0]
      [⟨1, [1]⟩, WorkMono.const 0, WorkMono.const 0, WorkMono.const 0, ⟨1, [0, 1]⟩,
        WorkMono.const 0, WorkMono.const 0] := by
    simp [SlotsLe, WorkMono.eval, WorkMono.const]
  have h := size_stmtCost_le_stmtWorkMono (by simp)
    (schurResidualCheck (O := O) (Q := Q)).body.instrument hσ
  rw [hw] at h
  simpa [WorkMono.eval] using h

/-- **The instructions of the verified solver** (on every tape): the instrumented static count of
`NLAlib.Schur.verifiedSchurWith Solve` at the order $n + 1$, the dimensions
$(n_r, n_q, k, F, T)$ and zero offsets is at most the solver's count at the same arguments, plus
$1619(n + 1)^3$ for the check, $32(n + 1)^2$ for the copy and $64$ for the frames: the
verification costs $O(n^3)$ on top of the solver. -/
theorem size_stmtCost_verifiedSchurWith_le (Solve : Impl O Q) (n nr nq k F T : ℕ) :
    Count.size (stmtCost (verifiedSchurWith Solve).body.instrument
        [n + 1, nr, nq, k, F, T, 0, 0, 0, 0, 0]) ≤
      Count.size (stmtCost Solve.body.instrument [n + 1, nr, nq, k, F, T, 0, 0, 0, 0, 0]) +
        1619 * (n + 1) ^ 3 + 32 * (n + 1) ^ 2 + 64 := by
  have h1 := size_stmtCost_copy_le (O := O) (Q := Q) n
  have h2 := size_stmtCost_schurResidualCheck_le (O := O) (Q := Q) n (nr + nq)
  simp only [verifiedSchurWith, Stmt.alloc, Stmt.instrument, tally,
    indexBookkeeping, operandBookkeeping, IExp.bookkeeping, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, stmtCost, useCost,
    IExp.evalList, IExp.eval, List.map_cons, List.map_nil, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.map_some, Option.getD_some, zero_add, add_zero, map_add,
    Count.one, size_single]
  linarith

end Theorems

end NLAlib.Schur
