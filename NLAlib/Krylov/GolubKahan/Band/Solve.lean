/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.GolubKahan.Band.Run
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# The block Golub–Kahan driver meets its specifications

`NLAlib.Krylov.GolubKahan.Band.solveRoutine` is
`[m, n, b, q] () → (U, V, G, R, S : write)`, drawing `n * b` tape positions. Its specification
names the five written blocks and the draws relative to the position of the call: the first
`n * b` words of the stream are the start block.

## Main definitions

* `NLAlib.Krylov.GolubKahan.Band.solveSpecOf`: the specification for given contracts;
  `NLAlib.Krylov.GolubKahan.Band.solveSpec` and
  `NLAlib.Krylov.GolubKahan.Band.Rounded.solveSpec` are the exact and the rounded instances.

## Main results

* `NLAlib.Krylov.GolubKahan.Band.solveRoutine_nodup`: the five operands are in different
  buffers.
* `NLAlib.Krylov.GolubKahan.Band.solveSpecOf_post`: the postcondition read on operands.
* `NLAlib.Krylov.GolubKahan.Band.solveRoutine_meets_of`: the routine meets the specification of
  its contracts.
* `NLAlib.Krylov.GolubKahan.Band.solveRoutine_meets`: the routine meets its exact specification.
* `NLAlib.Krylov.GolubKahan.Band.Rounded.solveRoutine_meets`: the routine meets its rounded
  specification.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.GolubKahan.Band

open Ops

variable {K Op Tst : Type} [Has OrthOp Op] [Has OperatorPairOp Op] [Has SampleOp Op]
variable [Inhabited K]

/-- The specification of the driver for an admission `ok` of the basis extension and a family
`Run` of run predicates, one for each block size and count. At the row and column counts `m`,
`n`, and at a block size `b` and count `q` at which the extension is admitted for every block of
the run, the five written blocks decode to a run `Run b q` from the start block in the first
`n * b` words drawn from the stream. -/
def solveSpecOf (stream : ℕ) (dec : K → ℝ) (m n : ℕ) (ok : ℕ → ℕ → ℕ → Prop)
    (Run : (b q : ℕ) → RunPred m n b q) : Routine.Spec K where
  pre d _ _ := d.headD 0 = m ∧ d.getD 1 0 = n ∧ ok n 0 (d.getD 2 0) ∧
    ∀ j < d.getD 3 0, ok m (j * d.getD 2 0) (d.getD 2 0) ∧
      ok n ((j + 1) * d.getD 2 0) (d.getD 2 0)
  post d ω _ Y := match Y with
    | [us, vs, gs, rs, ss] => StoredOut dec m n (d.getD 2 0) (d.getD 3 0)
        (Run (d.getD 2 0) (d.getD 3 0)) (ω.window stream 0 (n * d.getD 2 0)) us vs gs rs ss
    | _ => False

/-- At the row and column counts `m`, `n` of the matrix $\mathbf{A}$, the five written blocks
decode to an exact run for $\mathbf{A}$ from the start block in the first `n * b` words drawn
from the stream. Every block size and count is admitted. -/
def solveSpec (stream : ℕ) (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Routine.Spec K :=
  solveSpecOf stream dec m n (fun _ _ _ => True) (IsExactStoredRun A)

omit [Inhabited K] in
/-- The separation of the operands of the driver: five different buffers. -/
theorem solveRoutine_nodup {stream : ℕ} {U V G R S : ℕ × ℕ}
    (hsep : (solveRoutine (Op := Op) (Tst := Tst) stream).Separated [U, V, G, R, S]) :
    [U.1, V.1, G.1, R.1, S.1].Nodup := hsep.1

/-- The postcondition of the specification of the driver, read on five operands holding the
reported blocks: the blocks decode to a run from the start block drawn at the position `p` of
the call. -/
theorem solveSpecOf_post {stream : ℕ} {dec : K → ℝ} {m n b q p : ℕ} {ok : ℕ → ℕ → ℕ → Prop}
    {Run : (b q : ℕ) → RunPred m n b q} {τ : Tape K} {μ : Mem K} {U V G R S : ℕ × ℕ}
    {ys : List (List K)} (hys : μ.readBlocks [U, V, G, R, S] (outLens m n b q) = some ys)
    (hpost : (solveSpecOf stream dec m n ok Run).post [m, n, b, q] (τ.shift p) [] ys) :
    ∃ us vs gs rs ss,
      μ.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
      StoredOut dec m n b q (Run b q) (τ.window stream p (n * b)) us vs gs rs ss := by
  rcases ys with _ | ⟨us, _ | ⟨vs, _ | ⟨gs, _ | ⟨rs, _ | ⟨ss, _ | ⟨t, ts⟩⟩⟩⟩⟩⟩
  all_goals first
    | exact False.elim hpost
    | refine ⟨us, vs, gs, rs, ss, hys, ?_⟩
      have h : StoredOut dec m n b q (Run b q) ((τ.shift p).window stream 0 (n * b))
          us vs gs rs ss := hpost
      rwa [Tape.window_shift] at h

/-- The tree of the driver on five operands in different buffers, for any contracts: the step of
the proof of `NLAlib.Krylov.GolubKahan.Band.solveRoutine_meets_of`, split from it for length.
The block size `b` is fixed here; the judgment states it for every block size. -/
private theorem solve_writes {dec : K → ℝ} {m n b q : ℕ} {Ext : ExtendPred ℝ}
    {ok : ℕ → ℕ → ℕ → Prop} {Mv : Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin b) ℝ → Prop}
    {Rmv : Matrix (Fin m) (Fin b) ℝ → Matrix (Fin n) (Fin b) ℝ → Prop} {I : Interp Op Tst K}
    (hMv : AppliesColumns dec I (Has.inj OperatorPairOp.matvec) m n b Mv)
    (hRmv : AppliesColumns dec I (Has.inj OperatorPairOp.rmatvec) n m b Rmv)
    (hO : I.Satisfies .total (Has.inj OrthOp.extend) ((extendRelOf dec ok Ext).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) (hok₀ : ok n 0 b) (hokU : ∀ j < q, ok m (j * b) b)
    (hokV : ∀ j < q, ok n ((j + 1) * b) b) {τ : Tape K} {μ : Mem K} {U V G R S : ℕ × ℕ}
    (hbuf : [U.1, V.1, G.1, R.1, S.1].Nodup) (hl : μ.Live [U, V, G, R, S])
    (hz : μ.Room [U, V, G, R, S] (outLens m n b q)) :
    Writes .total I τ (solve stream) (Env.frame [m, n, b, q] [U, V, G, R, S])
      (Fp.blocks [U, V, G, R, S] (outLens m n b q))
      (fun μ' => μ'.pos = μ.pos + n * b ∧ ∃ us vs gs rs ss,
        μ'.readBlocks [U, V, G, R, S] (outLens m n b q) = some [us, vs, gs, rs, ss] ∧
        StoredOut dec m n b q (IsStoredRun Ext Mv Rmv) (τ.window stream μ.pos (n * b))
          us vs gs rs ss) μ := by
  obtain ⟨hUL, hVL, hGL, hRL, hSL⟩ : U.1 < μ.store.length ∧ V.1 < μ.store.length ∧
      G.1 < μ.store.length ∧ R.1 < μ.store.length ∧ S.1 < μ.store.length := by simpa using hl
  refine writes_allocs_preserving_post (lens := [(.var 0 + (.var 1 - .var 0)) * .var 2])
    (ns := [(m + (n - m)) * b]) rfl (fun hBelow hp => ⟨hp.1, ?_⟩)
    fun s₁ hlength hlens hBelow => ?_
  · obtain ⟨us, vs, gs, rs, ss, hr, hout⟩ := hp.2
    exact ⟨us, vs, gs, rs, ss, (Mem.readBlocks_eq_of_below hBelow hl).trans hr, hout⟩
  have hlen : s₁.length = μ.store.length + 1 := by simpa using hlength
  have hW : s₁.len μ.store.length = (m + (n - m)) * b := by simpa using hlens 0 (by simp)
  have hz₀ : (Mem.mk s₁ μ.pos).Room [U, V, G, R, S] (outLens m n b q) :=
    (Mem.room_eq_of_below (μ := μ) (μ' := ⟨s₁, μ.pos⟩) hBelow hl).mpr hz
  have hWm : b * m ≤ (m + (n - m)) * b := by
    rw [Nat.mul_comm b m]
    exact Nat.mul_le_mul_right b (by omega)
  have hWn : b * n ≤ (m + (n - m)) * b := by
    rw [Nat.mul_comm b n]
    exact Nat.mul_le_mul_right b (by omega)
  have hnb : n * b = b * n := Nat.mul_comm n b
  have hne := hbuf
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hne
  have hLive : (Mem.mk s₁ μ.pos).Live [(μ.store.length, 0)] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    omega
  have hroomW : (Mem.mk s₁ μ.pos).Room [(μ.store.length, 0)] [n * b] := by
    simp only [Mem.room_cons, Mem.room_nil, and_true]
    omega
  call (sampleRoutine_meets hSample stream) [n * b] ((μ.store.length, 0)) as μ₁ hfr₁ hp₁ (ws) hpost
  have hfr₁ : s₁.EqOff (Store.inBlock μ.store.length 0 (n * b)) μ₁.store :=
    hfr₁.mono (by fp_sub)
  have hω : μ₁.store.readBlock μ.store.length 0 (n * b) =
      some (τ.window stream μ.pos (n * b)) := by
    have h : ws = (τ.shift μ.pos).window stream 0 (n * b) := hpost
    rw [h, Tape.window_shift] at hws
    exact hws
  have hz₁ := hz₀.congr hfr₁.len_eq
  have hW₁ := (hfr₁.len_eq μ.store.length).trans hW
  have hL₁ := hfr₁.length_eq.trans hlen
  have hb1 := block_le (show 0 < q + 1 by omega) b n
  have hzz := hz₁
  simp only [outLens, Mem.room_cons, Mem.room_nil, and_true] at hzz
  refine Writes.seq_le (extend_writes hO (Q := V) (W := (μ.store.length, 0)) (C := G)
    (qs := []) (ws := τ.window stream μ.pos (n * b)) rfl rfl (by rw [Nat.zero_mul]; rfl)
    hVL.ne (by omega) hGL.ne' hok₀
    (by simp only [Mem.live_cons, Mem.live_nil, and_true, hL₁]; omega)
    (by rw [Nat.zero_mul]; rfl) (by rw [← hnb]; exact hω) (by omega)
    (show 0 + b * n ≤ μ₁.store.len μ.store.length by omega)
    (by rw [Nat.zero_add]; exact hzz.2.2.1)) ?_ fun μ₂ hfr₂ ⟨hp₂, hstart⟩ => ?_
  · unfold outLens
    refine sup_le ?_ (sup_le (Fp.inBlock_le_sup_above le_rfl) (sup_le ?_ bot_le))
    · exact le_sup_of_le_left (le_sup_of_le_right (le_sup_of_le_left
        (Fp.inBlock_le_inBlock (by omega) (by omega))))
    · exact le_sup_of_le_left (le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_left
        (Fp.inBlock_le_inBlock le_rfl (by rw [Nat.zero_add])))))
  have hlen₂ : ∀ B, μ₂.store.len B = μ₁.store.len B := hfr₂.len_eq
  refine (steps_writes hMv hRmv hO hokU hokV (W := (μ.store.length, 0)) rfl (fun _ => rfl)
    (fun _ => rfl) hbuf hl
    (by simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₂.length_eq, hL₁]; omega)
    (hz₁.congr hlen₂) (by rw [hlen₂]; change 0 + b * m ≤ μ₁.store.len μ.store.length; omega)
    (by rw [hlen₂]; change 0 + b * n ≤ μ₁.store.len μ.store.length; omega)
    (StoredPrefix.zero hstart)
    fun j hj => stepFp_le hj le_rfl).mono le_rfl ?_
  rintro μ₃ - ⟨hp₃, hpre⟩
  exact ⟨by rw [hp₃, hp₂, hp₁], hpre.exists_storedOut⟩

/-- The driver meets the specification of its contracts. If the loops over the columns of a
block with `matvec` and `rmatvec` compute blocks related by `Mv b` and `Rmv b` to their inputs
at every block size `b`, `extend` satisfies the contract of a basis extension for the predicate
`Ext` with the admission `ok`, and the draws return the words of the tape, then on five live
output blocks in distinct buffers with room for the output lengths the program terminates,
writes only the output blocks, consumes exactly $nb$ samples and releases its scratch; the
stored blocks decode to matrices related block by block
(`NLAlib.Krylov.GolubKahan.Band.IsStoredRun`), from the start block decoded from the window of
the tape. The exact and the rounded judgments are instances. -/
theorem solveRoutine_meets_of {dec : K → ℝ} {m n : ℕ} {Ext : ExtendPred ℝ}
    {ok : ℕ → ℕ → ℕ → Prop}
    {Mv : (b : ℕ) → Matrix (Fin n) (Fin b) ℝ → Matrix (Fin m) (Fin b) ℝ → Prop}
    {Rmv : (b : ℕ) → Matrix (Fin m) (Fin b) ℝ → Matrix (Fin n) (Fin b) ℝ → Prop}
    {I : Interp Op Tst K}
    (hMv : ∀ b, AppliesColumns dec I (Has.inj OperatorPairOp.matvec) m n b (Mv b))
    (hRmv : ∀ b, AppliesColumns dec I (Has.inj OperatorPairOp.rmatvec) n m b (Rmv b))
    (hO : I.Satisfies .total (Has.inj OrthOp.extend)
      ((extendRelOf dec ok Ext).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) :
    (solveRoutine (Op := Op) (Tst := Tst) stream).Meets I
      (solveSpecOf stream dec m n ok fun b _ => IsStoredRun Ext (Mv b) (Rmv b)) := by
  routine_intro [m', n', b, q] (U, V, G, R, S) reads () memory μ
  obtain ⟨hm, hn, hok₀, hok⟩ := hpre
  obtain rfl : m' = m := hm
  obtain rfl : n' = n := hn
  have hbuf : [U.1, V.1, G.1, R.1, S.1].Nodup := solveRoutine_nodup hsep
  have hokU : ∀ j < q, ok m' (j * b) b := fun j hj => (hok j hj).1
  have hokV : ∀ j < q, ok n' ((j + 1) * b) b := fun j hj => (hok j hj).2
  have hMv := hMv b
  have hRmv := hRmv b
  have hl : μ.Live [U, V, G, R, S] := hlive
  have hz : μ.Room [U, V, G, R, S] (outLens m' n' b q) := hrooms
  suffices hw : Writes .total I τ (solve stream) (Env.frame [m', n', b, q] [U, V, G, R, S])
      (Fp.blocks [U, V, G, R, S] (outLens m' n' b q))
      (fun μ' => μ'.pos = μ.pos + n' * b ∧ ∃ us vs gs rs ss,
        μ'.readBlocks [U, V, G, R, S] (outLens m' n' b q) = some [us, vs, gs, rs, ss] ∧
        StoredOut dec m' n' b q (IsStoredRun Ext (Mv b) (Rmv b))
          (τ.window stream μ.pos (n' * b)) us vs gs rs ss) μ by
    refine hw.mono le_rfl ?_
    rintro μ' - ⟨hpos, us, vs, gs, rs, ss, hread, hout⟩
    refine ⟨hpos, [us, vs, gs, rs, ss], hread, ?_⟩
    change StoredOut dec m' n' b q _ ((τ.shift μ.pos).window stream 0 (n' * b))
      us vs gs rs ss
    rw [Tape.window_shift]
    exact hout
  apply solve_writes hMv hRmv hO hSample stream hok₀ hokU hokV hbuf hl hz

/-- The driver meets its exact specification: under the exact contracts of the two products
with $\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$, of the basis extension and of the draws. No rank
or nonbreakdown hypothesis is needed. -/
theorem solveRoutine_meets {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Interp Op Tst K} (hA : IsExactMatvecPair dec A I)
    (hO : I.Satisfies .total (Has.inj OrthOp.extend) ((exactExtendRel dec).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) :
    (solveRoutine (Op := Op) (Tst := Tst) stream).Meets I (solveSpec stream dec A) :=
  solveRoutine_meets_of (Ext := fun _ _ _ Q W Q' H R => IsBasisExtension Q W Q' H R)
    (ok := fun _ _ _ => True) (Mv := fun _ X W => W = A * X) (Rmv := fun _ X W => W = Aᴴ * X)
    (fun _ _ _ _ _ _ hxy hl hx hy => applyColumns_writes hA.matvec hxy hl hx hy)
    (fun _ _ _ _ _ _ hxy hl hx hy => applyColumns_writes hA.rmatvec hxy hl hx hy)
    hO hSample stream

namespace Rounded

/-- At the row and column counts `m`, `n` of the matrix $\mathbf{A}$, and at the block size and
count at which `ok` admits every extension of the run, the five written blocks decode to a
rounded run for $\mathbf{A}$ with product allowances $\delta$, $\delta'$ and extension parameters
$(\eta_0, \mu, \varepsilon)$, from the start block in the first `n * b` words drawn from the
stream. -/
def solveSpec (stream : ℕ) (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (δ δ' η₀ μ ε : ℝ) (ok : ℕ → ℕ → ℕ → Prop) : Routine.Spec K :=
  solveSpecOf stream dec m n ok (IsRoundedStoredRun A δ δ' η₀ μ ε)

/-- The driver meets its rounded specification, with the executed history: under the normwise
contracts of the products with $\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$ at the allowances
$\delta$, $\delta'$, the rounded contract of a basis extension and the draws. There is no
orthogonality, rank or nonbreakdown hypothesis. -/
theorem solveRoutine_meets {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {δ δ' η₀ μ ε : ℝ} {ok : ℕ → ℕ → ℕ → Prop} {I : Interp Op Tst K}
    (hA : IsMatvecPair dec A δ δ' I)
    (hO : I.Satisfies .total (Has.inj OrthOp.extend)
      ((extendRel dec η₀ μ ε ok).spec ExtendOperands))
    (hSample : IsSample I) (stream : ℕ) :
    (solveRoutine (Op := Op) (Tst := Tst) stream).Meets I
      (solveSpec stream dec A δ δ' η₀ μ ε ok) :=
  solveRoutine_meets_of (Ext := fun _ _ _ Q W Q' H R => IsBasisExtensionErr η₀ μ ε Q W Q' H R)
    (fun _ _ _ _ _ _ hxy hl hx hy => applyColumns_writes_error hA.matvec hxy hl hx hy)
    (fun _ _ _ _ _ _ hxy hl hx hy => applyColumns_writes_error hA.rmatvec hxy hl hx hy)
    hO hSample stream

end Rounded

end NLAlib.Krylov.GolubKahan.Band
