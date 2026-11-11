/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Count
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Profiles.BlasCert

/-!
# Test case: the matrix product in finite precision

`NLAlib.Ops.Examples.gemm` computes `C = A B` by `m p` calls of `dot`: `A` is `m × n` stored by
rows, `B` is `n × p` stored by columns (so that a row of `A` and a column of `B` are contiguous
blocks), `C` is `m × p` stored by rows.

## Main results

* Mathematics: the postcondition `NLAlib.Ops.Examples.GemmRounded` is the classical componentwise
  forward bound `|ĉ_ij - Σ_k a_ik b_kj| ≤ ε Σ_k |a_ik| |b_kj|`; nothing else is needed.
* The certificate (`NLAlib.Ops.Examples.gemm_spec`): for every interpretation meeting the
  level-1 contracts at `ε`, `gemm` meets its contract in operand form
  (`NLAlib.Ops.Examples.gemmRel`). This is the statement of an implementation of an operation;
  it is proved in the program logic (`NLAlib.Ops.Logic`) by the relational 2-D fill rule.
* Abstract theorem (`NLAlib.Ops.Examples.runs_gemm_rounded`), from the certificate by the
  bridge `NLAlib.Ops.Impl.Triple.runs_rel`: `m p` calls of `dot` at the length `n`.
* Corollaries, one application of `Profile.Refines.runs` each
  (`NLAlib.Ops.Examples.runs_gemm_link_seq`, `NLAlib.Ops.Examples.runs_gemm_link_pairwise`):
  `ε = (1 + u) ^ n - 1` under sequential summation and `(1 + u) ^ (⌈log₂ n⌉ + 1) - 1` under
  pairwise summation, with the scalar counts of
  `NLAlib.Ops.Examples.push_seq_gemmCount` and `NLAlib.Ops.Examples.push_pairwise_gemmCount`:
  `m p n` multiplications and `m p (n - 1)` additions in both.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} [Has Blas1Op Op]

/-- **The matrix product by rows times columns.** Index variables: `m`, `n`, `p`, the offsets of
`A`, `B`, `C`, then `i`, `j`; buffer variables: `A`, `B`, `C`. -/
def gemm : Stmt Op Tst :=
  .loop (.var 0) (.loop (.var 2) (.call (Has.inj Blas1Op.dot) [.var 1]
    [⟨0, .var 3 + .var 6 * .var 1⟩, ⟨1, .var 4 + .var 7 * .var 1⟩]
    [⟨2, .var 5 + (.var 6 * .var 2 + .var 7)⟩]))

/-- The call counts of `gemm`: `m p` calls of `dot` at the length `n`. -/
noncomputable def gemmCount (m n p : ℕ) : Count Op Tst :=
  (m * p) • Count.one (Has.inj Blas1Op.dot) [n]

theorem staticCost_gemm (m n p a b c : ℕ) :
    stmtCost (gemm (Op := Op) (Tst := Tst)) [m, n, p, a, b, c] = gemmCount m n p := by
  simp [gemm, stmtCost, useCost, gemmCount, mul_smul]

theorem staticPeak_gemm_le (W : Op → List ℕ → ℕ) (m n p a b c : ℕ) :
    stmtPeak W (gemm (Op := Op) (Tst := Tst)) [m, n, p, a, b, c] ≤
      W (Has.inj Blas1Op.dot) [n] := by
  simp only [gemm, stmtPeak]
  exact Finset.sup_le fun i _ => Finset.sup_le fun j _ => by simp

/-- **`gemm` as an implementation**: three dimensions `m`, `n`, `p`, two inputs `A`, `B`, one
output `C`. -/
def gemmImpl : Impl Op Tst := ⟨3, 2, 1, gemm⟩

variable [Inhabited K]

/-- The componentwise forward bound of the matrix product:
`|ĉ_ij - Σ_k a_ik b_kj| ≤ e Σ_k |a_ik| |b_kj|`. -/
def GemmForward (dec : K → ℝ) (e : ℝ) (m n p : ℕ) (as bs cs : List K) : Prop :=
  ∀ i < m, ∀ j < p,
    |dec (vec cs (i * p + j)) - ∑ k ∈ Finset.range n, dec (vec as (i * n + k)) *
      dec (vec bs (j * n + k))| ≤
      e * ∑ k ∈ Finset.range n, |dec (vec as (i * n + k)) * dec (vec bs (j * n + k))|

/-- **The contract of `gemm`**, in operand form: at the dimensions `[m, n, p]`, from the blocks
`A` (`m n` cells, by rows) and `B` (`p n` cells, by columns) to the block `C` (`m p` cells, by
rows), with the componentwise forward bound at the error `e n` of `dot`. -/
@[simps (attr := storeNF)]
def gemmRel (dec : K → ℝ) (e : ℕ → ℝ) : BlockRel K where
  nd := 3
  inLens d := match d with
    | [m, n, p] => [m * n, p * n]
    | _ => []
  outLens d := match d with
    | [m, _, p] => [m * p]
    | _ => []
  rel d X _ Y := match d, X, Y with
    | [m, n, p], [as, bs], [cs] => GemmForward dec (e n) m n p as bs cs
    | _, _, _ => False

/-- The admitted operands of `gemm`: the length `n` is covered by the contract of `dot`, and `A`
and `B` are in other buffers than `C`. -/
@[admNF] def GemmOperands (ok : ℕ → Prop) : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => ok (d.getD 1 0) ∧ ∀ a ∈ ins, ∀ z ∈ outs, a.1 ≠ z.1

/-- **The postcondition of `gemm`**: the block `C` holds `cs`, nothing else is written, and every
entry satisfies the componentwise forward bound. -/
def GemmRounded (dec : K → ℝ) (e : ℝ) (m n p : ℕ) (C : ℕ × ℕ) (as bs : List K)
    (μ μ' : Mem K) : Prop :=
  ∃ cs : List K, μ' = μ.updBlock C cs ∧ cs.length = m * p ∧ GemmForward dec e m n p as bs cs

/-- **The certificate of `gemm`**: for every interpretation meeting the level-1 contracts at
`ε`, `gemm` meets its contract, with the error `ε.dot n` of `dot`. The same statement as the
certificate of an implementation of a level-1 operation, so `gemm` is an operation for the
algorithms above it. Proved with the relational 2-D fill rule: `C` is the layout of `Cᵀ` by
columns, one `step` per entry. -/
theorem gemm_spec {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {J : Interp Op Tst K}
    (hJ : IsBlas1 dec ε ok J) :
    (gemmImpl (Op := Op) (Tst := Tst)).Triple J .total
      ((gemmRel dec ε.dot).spec (GemmOperands ok)) := by
  cert_intro [m, n, p] (A, B) → (C) reads (as, bs)
  refine Writes.mono (writes_fillRel₂ ⟨C.1, C.2, p, m, p⟩ le_rfl rfl (fun _ => rfl)
    (fun j i x => IsDotErr dec (ε.dot n) n (fun k => vec as (i * n + k))
      (fun k => vec bs (j * n + k)) x) (fun _ => μ.pos) rfl fun i hi j hj m₁ hfr _ hpos => ?_)
    ((MatLayout.fp_le_inBlock le_rfl).trans (by fp_sub)) fun m' _ ⟨⟨Cm, hC, hR⟩, hpos⟩ => ?_
  · dsimp only at hi hj
    step hJ.dot as m₂ hfr₂ ⟨hpos₂, v, hv, hrel⟩
    exact ⟨⟨v, by simpa [MatLayout.cell, Nat.add_assoc] using hv,
      hrel.congr (fun k hk => vec_drop_take hk) fun k hk => vec_drop_take hk⟩,
      by simp [hpos₂, hpos]⟩
  · obtain ⟨cs, hcs, -, hcC⟩ := hC.readBlock rfl
    exact ⟨by simp [hpos], [cs], Mem.readBlocks_of_cons hcs rfl,
      fun i hi j hj => by rw [hcC j hj i hi]; exact hR j hj i hi⟩

/-- **The abstract theorem of `gemm`**, from its certificate by the bridge: for every
interpretation meeting the level-1 contracts at `ε` for the length `n`, the run terminates within
`m p` calls of `dot` and the workspace of one, and the computed product satisfies the
componentwise forward bound with `ε.dot n`. -/
theorem runs_gemm_rounded {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {J : Interp Op Tst K}
    (hJ : IsBlas1 dec ε ok J) (W : Op → List ℕ → ℕ) {τ : Tape K} {m n p : ℕ} {A B C : ℕ × ℕ}
    {μ : Mem K} {as bs : List K} (hok : ok n) (hAC : A.1 ≠ C.1) (hBC : B.1 ≠ C.1)
    (hl : μ.Live [A, B, C]) (hA : μ.store.readBlock A.1 A.2 (m * n) = some as)
    (hB : μ.store.readBlock B.1 B.2 (p * n) = some bs)
    (hC : C.2 + m * p ≤ μ.store.len C.1) :
    ConditionalRuns J W τ gemm (Env.frame [m, n, p] [A, B, C]) μ (gemmCount m n p)
      (W (Has.inj Blas1Op.dot) [n]) (GemmRounded dec (ε.dot n) m n p C as bs μ) := by
  refine ((gemm_spec hJ).runs_rel W (d := [m, n, p]) (ins := [A, B]) (outs := [C]) (τ := τ)
    (xs := [as, bs]) rfl
    ⟨hok, by simp [hAC, hBC]⟩ hl (by simp [gemmRel, Mem.readBlocks, hA, hB]) trivial
    ⟨hC, trivial⟩).mono (le_of_eq (staticCost_gemm ..)) (staticPeak_gemm_le ..) ?_
  rintro μ' ⟨ys, hlen, hb, rfl⟩
  obtain ⟨cs, rfl, hcs⟩ := map_length_eq_one hlen
  exact ⟨cs, rfl, hcs, hb⟩

/-! ### The two profiles -/

variable [Has ScalarOp Op] [Apart Blas1Op ScalarOp Op] {M : Machine K} {u : ℝ}

/-- **`gemm` under sequential summation**: over scalar arithmetic meeting the standard model at
`u`, the linked program computes `C` with `|Ĉ - A B| ≤ ((1 + u) ^ n - 1) |A| |B|`
componentwise (`n ≥ 1`), within the pushed-forward counts and `n` scratch cells. One application
of the certificate of the profile. -/
theorem runs_gemm_link_seq {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u)
    {I : Interp Op Tst K} (hI : IsScalar M I) {τ : Tape K} {m n p : ℕ} (hn : 1 ≤ n)
    {A B C : ℕ × ℕ} {μ : Mem K} {as bs : List K} (hAC : A.1 ≠ C.1) (hBC : B.1 ≠ C.1)
    (hl : μ.Live [A, B, C]) (hA : μ.store.readBlock A.1 A.2 (m * n) = some as)
    (hB : μ.store.readBlock B.1 B.2 (p * n) = some bs)
    (hC : C.2 + m * p ≤ μ.store.len C.1) :
    ConditionalRuns I (Blas.ws 0) τ (gemm.link Blas.seq.table) (Env.frame [m, n, p] [A, B, C]) μ
      ((m * p) • (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) • Blas.sc .copy +
        (n - 1) • Blas.sc .add)))) (Blas.ws 0 (Has.inj Blas1Op.dot : Op) [n])
      (GemmRounded dec ((1 + u) ^ n - 1) m n p C as bs μ) :=
  (Blas.seq.err_dot u hn ▸ (Blas.seq_certifies hM hu fun _ => True).runs
    (fun _ hJ => runs_gemm_rounded hJ.2 _ trivial hAC hBC hl hA hB hC) hI).mono
    (by count_eval [gemmCount]) le_rfl fun _ h => h

/-- **`gemm` under pairwise summation** of depth `k`, for `⌈log₂ n⌉ < k`:
`|Ĉ - A B| ≤ ((1 + u) ^ (⌈log₂ n⌉ + 1) - 1) |A| |B|` componentwise. -/
theorem runs_gemm_link_pairwise {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u)
    {I : Interp Op Tst K} (hI : IsScalar M I) {τ : Tape K} {k m n p : ℕ}
    (hk : Nat.clog 2 n < k) {A B C : ℕ × ℕ} {μ : Mem K} {as bs : List K} (hAC : A.1 ≠ C.1)
    (hBC : B.1 ≠ C.1) (hl : μ.Live [A, B, C])
    (hA : μ.store.readBlock A.1 A.2 (m * n) = some as)
    (hB : μ.store.readBlock B.1 B.2 (p * n) = some bs)
    (hC : C.2 + m * p ≤ μ.store.len C.1) :
    ConditionalRuns I (Blas.ws Blas.pairWs) τ (gemm.link (Blas.pairwise k).table)
      (Env.frame [m, n, p] [A, B, C]) μ
      ((m * p) • (n • Blas.sc .mul + Blas.pairCount n))
      (Blas.ws Blas.pairWs (Has.inj Blas1Op.dot : Op) [n])
      (GemmRounded dec ((1 + u) ^ (Nat.clog 2 n + 1) - 1) m n p C as bs μ) := by
  have h := (Blas.pairwise_certifies hM hu k).runs (τ := τ)
    (fun _ hJ => runs_gemm_rounded hJ.2 _ hk hAC hBC hl hA hB hC) hI
  rw [Blas.pairwise_wsLo, Blas.pairwise.err_dot] at h
  exact h.mono (by count_eval [gemmCount]) le_rfl fun _ h => h

omit [Inhabited K] in
/-- **The scalar counts of `gemm` under sequential summation**: per entry, `n` multiplications,
`n - 1` additions, a literal and a copy. -/
theorem push_seq_gemmCount (m n p : ℕ) :
    Count.push Blas.seq.cost (gemmCount (Op := Op) (Tst := Tst) m n p) =
      (m * p) • (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) • Blas.sc .copy +
        (n - 1) • Blas.sc .add))) := by
  count_eval [gemmCount]

omit [Inhabited K] in
/-- **The scalar counts of `gemm` under pairwise summation**: per entry, `n` multiplications,
`n - 1` additions and `n` copies. -/
theorem push_pairwise_gemmCount (k m n p : ℕ) (hk : Nat.clog 2 n < k) :
    Count.push (Blas.pairwise k).cost (gemmCount (Op := Op) (Tst := Tst) m n p) =
      (m * p) • (n • Blas.sc .mul + Blas.pairCount n) := by
  count_eval [gemmCount]

end NLAlib.Ops.Examples
