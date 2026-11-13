/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.Computation.StaticCost
public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Computation.Loops

/-!
# A Hoare logic for the weighted kernel count of the spectral bisection program

The weighted kernel count of a run of `NLAlib.eighProg`, by an invariant of the run:
`NLAlib.EighWeight.Triple` is a Hoare triple for the cost and for the cells of one tracked buffer
(the size arena), and `NLAlib.EighWeight.BuilderFrame` is the same for a builder that keeps the
tracked buffer, through any continuation.
Frame rules for every block that does not write the tracked buffer; no semantic contract, the
kernels are arbitrary.

## Main results

* `NLAlib.EighWeight.triple_seq`, `NLAlib.EighWeight.triple_run`, `NLAlib.EighWeight.frame_run`:
  the rules.
* `NLAlib.EighWeight.triple_downSlot`: a slot of the downward pass.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

namespace EighWeight

omit [AddMonoid C] [Inhabited K]

/-- The cells of buffer `b` at tag `p`. -/
def cells (s : Store P K) (p : P) (b : ℕ) : ℕ → Option K := fun i => s.read p b i

/-- Every successful run of `s` from a state whose buffer `b` reads `V₀` adds at most `c T(m)` to
the weighted count and ends with buffer `b` satisfying `Q`. -/
def Triple (I : Interp P ι K (OpCount P ι)) (T : ℕ → ℕ) (p : P) (b m : ℕ)
    (V₀ : ℕ → Option K) (s : Stmt P ι ℕ ℕ) (c : ℕ) (Q : (ℕ → Option K) → Prop) : Prop :=
  Monotone T → (IsUnitCharge I) → ∀ st st' : St P K (OpCount P ι),
    b < st.store.size → cells st.store p b = V₀ → exec I s st = some st' →
    Finsupp.weight (OpKind.kernelWeight T) st'.cnt ≤
        Finsupp.weight (OpKind.kernelWeight T) st.cnt + c * T m ∧ Q (cells st'.store p b)

/-- A statement that keeps buffer `b` and costs at most `c T(m)`. -/
def Frame (I : Interp P ι K (OpCount P ι)) (T : ℕ → ℕ) (p : P) (b m : ℕ)
    (s : Stmt P ι ℕ ℕ) (c : ℕ) : Prop :=
  ∀ V₀, Triple I T p b m V₀ s c (· = V₀)

/-- The run of a builder with a continuation. -/
def runCont (x : Builder P ι ℕ ℕ Unit) (k : Unit → Stmt P ι ℕ ℕ) : Stmt P ι ℕ ℕ :=
  @ContT.run (Stmt P ι ℕ ℕ) Id Unit x k

/-- A builder that keeps buffer `b` and costs at most `c T(m)`, through every continuation. -/
def BuilderFrame (I : Interp P ι K (OpCount P ι)) (T : ℕ → ℕ) (p : P) (b m : ℕ)
    (x : Builder P ι ℕ ℕ Unit) (c : ℕ) : Prop :=
  ∀ (k : Unit → Stmt P ι ℕ ℕ) (c' : ℕ) V₀ Q, Triple I T p b m V₀ (k ()) c' Q →
    Triple I T p b m V₀ (runCont x k) (c + c') Q

/-- The buffer an instruction writes. -/
def instrDst : Instr P ℕ ℕ → ℕ
  | .lit _ d _ => d.buf
  | .litIdx _ d _ => d.buf
  | .bin _ _ d _ _ => d.buf
  | .un _ _ d _ => d.buf
  | .copy _ d _ => d.buf
  | .draw _ _ d => d.buf
  | .convert _ _ d _ => d.buf

variable {I : Interp P ι K (OpCount P ι)} {T : ℕ → ℕ} {p : P} {b m : ℕ}

omit [DecidableEq P] in
/-- The weight of a count plus one operation. -/
private theorem weight_add_single (T : ℕ → ℕ) (c : OpCount P ι) (κ : OpKind P ι) :
    Finsupp.weight (OpKind.kernelWeight T) (c + Finsupp.single κ 1) =
      Finsupp.weight (OpKind.kernelWeight T) c + OpKind.kernelWeight T κ := by
  rw [map_add, Finsupp.weight_single, one_smul]

/-- A successful run keeps the number of buffers. -/
theorem size_eq_of_exec_eq_some {s : Stmt P ι ℕ ℕ} {st st' : St P K (OpCount P ι)}
    (h : exec I s st = some st') : st'.store.size = st.store.size :=
  Store.size_eq_of_shape_eq (shape_eq_of_exec_eq_some h)

/-- Weakening: a larger cost, a larger bound $m$, a weaker postcondition. -/
theorem triple_mono {V₀ : ℕ → Option K} {s : Stmt P ι ℕ ℕ} {c c' m' : ℕ}
    {Q Q' : (ℕ → Option K) → Prop} (h : Triple I T p b m V₀ s c Q) (hc : c ≤ c')
    (hm : m ≤ m') (hQ : ∀ V, Q V → Q' V) : Triple I T p b m' V₀ s c' Q' := by
  intro hT hch st st' hb hV hex
  obtain ⟨h1, h2⟩ := h hT hch st st' hb hV hex
  exact ⟨h1.trans (Nat.add_le_add_left (Nat.mul_le_mul hc (hT hm)) _), hQ _ h2⟩

/-- `skip` costs nothing and keeps the tracked buffer. -/
theorem triple_skip {V₀ : ℕ → Option K} {Q : (ℕ → Option K) → Prop} (hQ : Q V₀) :
    Triple I T p b m V₀ .skip 0 Q := by
  intro _ _ st st' _ hV hex
  rw [exec_skip] at hex
  cases hex
  exact ⟨by omega, hV ▸ hQ⟩

/-- Sequencing: the costs add. -/
theorem triple_seq {V₀ : ℕ → Option K} {s t : Stmt P ι ℕ ℕ} {c₁ c₂ : ℕ}
    {Q₁ Q : (ℕ → Option K) → Prop} (h₁ : Triple I T p b m V₀ s c₁ Q₁)
    (h₂ : ∀ V₁, Q₁ V₁ → Triple I T p b m V₁ t c₂ Q) :
    Triple I T p b m V₀ (.seq s t) (c₁ + c₂) Q := by
  intro hT hch st st' hb hV hex
  rw [exec_seq] at hex
  obtain ⟨st₁, hs, ht⟩ := Option.bind_eq_some_iff.mp hex
  obtain ⟨a1, a2⟩ := h₁ hT hch st st₁ hb hV hs
  obtain ⟨b1, b2⟩ := h₂ _ a2 hT hch st₁ st' (by rw [size_eq_of_exec_eq_some hs]; exact hb) rfl ht
  refine ⟨?_, b2⟩
  rw [add_mul]
  omega

/-- An allocation: the body runs with a fresh handle above the tracked one. -/
private theorem triple_alloc {V₀ : ℕ → Option K} {q : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {c : ℕ} {Q : (ℕ → Option K) → Prop} (h : ∀ h, b < h → Triple I T p b m V₀ (body h) c Q) :
    Triple I T p b m V₀ (.alloc q len body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_alloc] at hex
  obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp hex
  have hs₂ := size_eq_of_exec_eq_some h₂
  simp only [Array.size_push] at hs₂
  obtain ⟨a1, a2⟩ := h st.store.size hb hT hch _ st₂ (by simp; omega)
    (by rw [← hV]; funext i; exact Store.read_push_of_lt hb) h₂
  refine ⟨a1, ?_⟩
  have : cells (Array.pop st₂.store) p b = cells st₂.store p b := by
    funext i; exact Store.read_pop_of_lt (by omega)
  simpa [this] using a2

/-- A named kernel runs as its body. -/
private theorem triple_named {V₀ : ℕ → Option K} {nm : String} {args : List (Arg ℕ ℕ)}
    {body : Stmt P ι ℕ ℕ} {c : ℕ} {Q : (ℕ → Option K) → Prop}
    (h : Triple I T p b m V₀ body c Q) : Triple I T p b m V₀ (.named nm args body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_named] at hex
  exact h hT hch st st' hb hV hex

/-- A branch costs at most the sum of its two arms. -/
private theorem triple_ite {V₀ : ℕ → Option K} {q : P} {cmp : CmpOp} {x y : Cell ℕ ℕ}
    {t e : Stmt P ι ℕ ℕ} {c₁ c₂ : ℕ} {Q : (ℕ → Option K) → Prop}
    (ht : Triple I T p b m V₀ t c₁ Q) (he : Triple I T p b m V₀ e c₂ Q) :
    Triple I T p b m V₀ (.ite q cmp x y t e) (c₁ + c₂) Q := by
  intro hT hch st st' hb hV hex
  rw [exec_ite] at hex
  obtain ⟨r, hr, hex⟩ := Option.bind_eq_some_iff.mp hex
  unfold cmpStep at hr
  obtain ⟨a, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨a', -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.mp hr
  have hw : Finsupp.weight (OpKind.kernelWeight T) (st.cnt + I.charge (.cmp q)) =
      Finsupp.weight (OpKind.kernelWeight T) st.cnt := by
    rw [hch.charge_eq, weight_add_single]; rfl
  split_ifs at hex
  · obtain ⟨a1, a2⟩ := ht hT hch { st with cnt := st.cnt + I.charge (.cmp q) } st' hb hV hex
    refine ⟨?_, a2⟩
    rw [hw] at a1; rw [add_mul]; omega
  · obtain ⟨a1, a2⟩ := he hT hch { st with cnt := st.cnt + I.charge (.cmp q) } st' hb hV hex
    refine ⟨?_, a2⟩
    rw [hw] at a1; rw [add_mul]; omega

/-- An index binder costs at most its body at every index up to the bound. -/
private theorem triple_bindIdx {V₀ : ℕ → Option K} {q : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {c : ℕ} {Q : (ℕ → Option K) → Prop}
    (h : ∀ v ≤ bound.eval, Triple I T p b m V₀ (body v) c Q) :
    Triple I T p b m V₀ (.bindIdx q x bound body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_bindIdx] at hex
  obtain ⟨r, hr, hex⟩ := Option.bind_eq_some_iff.mp hex
  unfold toNatStep at hr
  obtain ⟨a, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.mp hr
  dsimp only at hex
  split_ifs at hex with hle
  obtain ⟨a1, a2⟩ := h _ hle hT hch { st with cnt := st.cnt + I.charge (.toNat q) } st' hb hV hex
  refine ⟨?_, a2⟩
  rw [hch.charge_eq, weight_add_single] at a1
  exact a1

/-- the value a binder reads from cell `i` of the tracked buffer -/
def readNat (I : Interp P ι K (OpCount P ι)) (p : P) (V : ℕ → Option K) (i : ℕ) : ℕ :=
  ((V i).bind (I.sem.toNat p)).getD 0

/-- An index binder that reads the tracked buffer: the body at the index it reads. -/
private theorem triple_bindIdx_read {V₀ : ℕ → Option K} {e : IExp ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {c : ℕ} {Q : (ℕ → Option K) → Prop}
    (h : Triple I T p b m V₀ (body (min (readNat I p V₀ e.eval) bound.eval)) c Q) :
    Triple I T p b m V₀ (.bindIdx p ⟨b, e⟩ bound body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_bindIdx] at hex
  obtain ⟨r, hr, hex⟩ := Option.bind_eq_some_iff.mp hex
  unfold toNatStep at hr
  obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hr
  have hf : readNat I p V₀ e.eval = r' := by
    rw [← hV]; simp only [readNat, cells]; rw [ha]; simp [hr']
  dsimp only at hex
  split_ifs at hex with hle
  rw [← min_eq_left hle, ← hf] at hex
  obtain ⟨a1, a2⟩ := h hT hch { st with cnt := st.cnt + I.charge (.toNat p) } st' hb hV hex
  refine ⟨?_, a2⟩
  rw [hch.charge_eq, weight_add_single] at a1
  exact a1

/-- A loop of zero trips costs nothing. -/
private theorem triple_loop_zero {V₀ : ℕ → Option K} {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {Q : (ℕ → Option K) → Prop} (hn : n.eval = 0) (hQ : Q V₀) :
    Triple I T p b m V₀ (.loop n body) 0 Q := by
  intro _ _ st st' _ hV hex
  rw [exec_loop, hn] at hex
  simp only [List.range_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at hex
  subst hex
  exact ⟨by omega, hV ▸ hQ⟩

/-- A loop of one trip costs its body at index $0$. -/
private theorem triple_loop_one {V₀ : ℕ → Option K} {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {c : ℕ}
    {Q : (ℕ → Option K) → Prop} (hn : n.eval = 1) (h : Triple I T p b m V₀ (body 0) c Q) :
    Triple I T p b m V₀ (.loop n body) c Q := by
  intro hT hch st st' hb hV hex
  rw [exec_loop, hn] at hex
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil] at hex
  obtain ⟨s, hs, hex⟩ := Option.bind_eq_some_iff.mp hex
  simp only [Option.pure_def, Option.some.injEq] at hex
  subst hex
  exact h hT hch st s hb hV hs

/-- An index literal written to the tracked buffer updates its cell and costs nothing. -/
theorem triple_litIdx {V₀ : ℕ → Option K} {e m' : IExp ℕ} :
    Triple I T p b m V₀ (.instr (.litIdx p ⟨b, e⟩ m')) 0
      (· = Function.update V₀ e.eval (I.sem.lit p (m'.eval : ℚ))) := by
  intro _ hch st st' _ hV hex
  rw [exec_instr] at hex
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hex
  simp only [Instr.run] at hr
  obtain ⟨v, hv, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp hr
  refine ⟨?_, ?_⟩
  · rw [hch.charge_eq, weight_add_single]; simp [OpKind.kernelWeight, Instr.kind]
  · rw [← hV, hv]
    funext i
    simp only [cells]
    by_cases hi : i = e.eval
    · subst hi; rw [Function.update_self]; exact Store.read_of_write_eq_some hw
    · rw [Function.update_of_ne hi]; exact Store.read_of_write_eq_some_of_ne hw (Or.inr hi)

/-- A scalar instruction writes one cell of its destination buffer. -/
private theorem exists_write_instrDst {sem : ScalarSem P K} {tape : Dist → ℕ → K} {s : Store P K}
    {pos : Dist → ℕ} {r : Store P K × (Dist → ℕ)} (i : Instr P ℕ ℕ)
    (h : i.run sem tape s pos = some r) :
    ∃ q j v, s.write q (instrDst i) j v = some r.1 := by
  cases i with
  | lit p' d q' =>
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | litIdx p' d e =>
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | bin p' o d x y =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a', -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | un p' o d x =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | copy p' d x =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | draw p' dd d =>
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩
  | convert p' q' d x =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, _, _, hw⟩

omit [DecidableEq P] in
/-- A scalar instruction has weight $0$. -/
private theorem kernelWeight_kind (i : Instr P ℕ ℕ) :
    OpKind.kernelWeight (ι := ι) T i.kind = 0 := by
  cases i <;> rfl

/-- A scalar instruction that does not write the tracked buffer. -/
private theorem frame_instr {i : Instr P ℕ ℕ} (hi : instrDst i ≠ b) :
    Frame I T p b m (.instr i) 0 := by
  intro V₀ _ hch st st' hb hV hex
  rw [exec_instr] at hex
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hex
  obtain ⟨q, j, v, hw⟩ := exists_write_instrDst i hr
  refine ⟨?_, ?_⟩
  · rw [hch.charge_eq, weight_add_single, kernelWeight_kind]; omega
  · rw [← hV]; funext i'
    exact Store.read_of_write_eq_some_of_ne hw (Or.inl (Ne.symm hi))

/-- The maximum of a list of naturals bounded by $m$ is at most $m$. -/
private theorem foldr_max_le {l : List ℕ} (h : ∀ x ∈ l, x ≤ m) : l.foldr max 0 ≤ m := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-- The output blocks of a kernel call are in the buffers of its outputs. -/
private theorem exists_mem_of_mem_kcallBlocks {outs : List (ℕ × ℕ)} {lens : List ℕ} {x : ℕ × ℕ × ℕ}
    (hx : x ∈ kcallBlocks outs lens) : ∃ y ∈ outs, x.1 = y.1 := by
  induction outs generalizing lens with
  | nil => simp [kcallBlocks] at hx
  | cons y outs ih =>
    cases lens with
    | nil => simp [kcallBlocks] at hx
    | cons l lens =>
      simp only [kcallBlocks, List.zipWith_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨y, by simp, rfl⟩
      · obtain ⟨y', hy', h⟩ := ih hx
        exact ⟨y', by simp [hy'], h⟩

/-- A kernel call that does not write the tracked buffer, with dimensions at most $m$, costs
at most $T(m)$. -/
private theorem frame_kcall {o : ι} {q : P} {dims : List (IExp ℕ)} {ins outs : List (ℕ × IExp ℕ)}
    (ho : ∀ x ∈ outs, x.1 ≠ b) (hd : ∀ d ∈ dims, d.eval ≤ m) :
    Frame I T p b m (.kcall o q dims ins outs) 1 := by
  intro V₀ hT hch st st' hb hV hex
  simp only [exec] at hex
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hex
  unfold Interp.kcallStore at hs
  split_ifs at hs with hcond
  obtain ⟨xs, -, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨ys, -, hs⟩ := Option.bind_eq_some_iff.mp hs
  refine ⟨?_, ?_⟩
  · rw [hch.charge_eq, weight_add_single]
    simp only [OpKind.kernelWeight, one_mul]
    refine Nat.add_le_add_left (hT (foldr_max_le ?_)) _
    intro x hx
    obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hx
    exact hd d hdm
  · rw [← hV]; funext i'
    refine Store.read_of_writeBlocks_eq_some_of_forall hs fun x hx => Or.inl ?_
    obtain ⟨y, hy, hxy⟩ := exists_mem_of_mem_kcallBlocks hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    rw [hxy]; exact Ne.symm (ho z hz)

/-- A loop of frame statements costs its trip count times the cost of the body. -/
private theorem frame_loop {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {c : ℕ}
    (h : ∀ i, Frame I T p b m (body i) c) : Frame I T p b m (.loop n body) (n.eval * c) := by
  intro V₀ hT hch st st' hb hV hex
  have := forall_of_exec_loop_eq_some I (fun i s => b < s.store.size ∧ cells s.store p b = V₀ ∧
      Finsupp.weight (OpKind.kernelWeight T) s.cnt ≤
        Finsupp.weight (OpKind.kernelWeight T) st.cnt + i * c * T m)
    ⟨hb, hV, by simp⟩ (fun i _ s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      obtain ⟨a1, a2⟩ := h i V₀ hT hch s₁ s₂ h1 h2 hs
      refine ⟨by rw [size_eq_of_exec_eq_some hs]; exact h1, a2, ?_⟩
      rw [add_mul, add_mul, one_mul]; omega) hex
  obtain ⟨-, h2, h3⟩ := this
  exact ⟨h3, h2⟩

/-- `skip` is a frame statement of cost $0$. -/
private theorem frame_skip : Frame I T p b m .skip 0 := fun _ => triple_skip rfl

/-! Builder rules -/

/-- Weakening the cost of a builder. -/
theorem builderFrame_mono {x : Builder P ι ℕ ℕ Unit} {c c' : ℕ} (h : BuilderFrame I T p b m x c)
    (hc : c ≤ c') : BuilderFrame I T p b m x c' :=
  fun k c'' V₀ Q hk => triple_mono (h k c'' V₀ Q hk) (by omega) le_rfl fun _ h => h

/-- `pure ()` costs nothing. -/
theorem builderFrame_pure : BuilderFrame I T p b m (pure () : Builder P ι ℕ ℕ Unit) 0 :=
  fun _ _ _ _ hk => triple_mono hk (by omega) le_rfl fun _ h => h

/-- Binding two builders: the costs add. -/
theorem builderFrame_bind {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ}
    (hx : BuilderFrame I T p b m x c₁) (hf : BuilderFrame I T p b m (f ()) c₂) :
    BuilderFrame I T p b m (x >>= f) (c₁ + c₂) := fun k c' V₀ Q hk =>
  triple_mono (hx (fun a => runCont (f a) k) (c₂ + c') V₀ Q (hf k c' V₀ Q hk)) (by omega)
    le_rfl fun _ h => h

/-- A frame statement followed by a triple. -/
private theorem triple_seq_frame {V₀ : ℕ → Option K} {s t : Stmt P ι ℕ ℕ} {c₁ c₂ : ℕ}
    {Q : (ℕ → Option K) → Prop} (h₁ : Frame I T p b m s c₁) (h₂ : Triple I T p b m V₀ t c₂ Q) :
    Triple I T p b m V₀ (.seq s t) (c₁ + c₂) Q :=
  triple_seq (h₁ V₀) fun _ h => by subst h; exact h₂

/-- A frame statement as a builder. -/
private theorem builderFrame_stmt {s : Stmt P ι ℕ ℕ} {c : ℕ} (h : Frame I T p b m s c) :
    BuilderFrame I T p b m (stmt s) c := fun _ _ _ _ hk => triple_seq_frame h hk

/-- A scalar instruction that does not write the tracked buffer. -/
theorem builderFrame_ins {i : Instr P ℕ ℕ} (hi : instrDst i ≠ b) :
    BuilderFrame I T p b m (ins i) 0 :=
  builderFrame_stmt (frame_instr hi)

/-- A kernel call that does not write the tracked buffer, with dimensions at most $m$, costs
at most $T(m)$. -/
theorem builderFrame_kcall {o : ι} {q : P} {dims : List (IExp ℕ)} {ins outs : List (ℕ × IExp ℕ)}
    (ho : ∀ x ∈ outs, x.1 ≠ b) (hd : ∀ d ∈ dims, d.eval ≤ m) :
    BuilderFrame I T p b m (stmt (.kcall o q dims ins outs)) 1 :=
  builderFrame_stmt (frame_kcall ho hd)

/-- The run of a builder that keeps the tracked buffer is a frame statement. -/
theorem frame_run {x : Builder P ι ℕ ℕ Unit} {c : ℕ} (h : BuilderFrame I T p b m x c) :
    Frame I T p b m x.run c := fun V₀ =>
  triple_mono (h (fun _ => .skip) 0 V₀ _ (triple_skip (Q := (· = V₀)) rfl)) (by omega) le_rfl
    fun _ h => h

/-- An allocation followed by a builder of the fresh handle. -/
theorem builderFrame_allocBind {q : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ∀ h, b < h → BuilderFrame I T p b m (f h) c) :
    BuilderFrame I T p b m (alloc q len >>= f) c := fun k c' V₀ Q hk =>
  triple_alloc fun h' hh => h h' hh k c' V₀ Q hk

/-- A loop costs its trip count times the cost of the body. -/
theorem builderFrame_forRange {n : IExp ℕ} {body : ℕ → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ∀ i, BuilderFrame I T p b m (body i) c) :
    BuilderFrame I T p b m (forRange n body) (n.eval * c) :=
  fun _ _ _ _ hk => triple_seq_frame (frame_loop fun i => frame_run (h i)) hk

/-- A scope costs its body. -/
theorem builderFrame_scope {x : Builder P ι ℕ ℕ Unit} {c : ℕ} (h : BuilderFrame I T p b m x c) :
    BuilderFrame I T p b m (scope x) c := fun _ _ _ _ hk => triple_seq_frame (frame_run h) hk

/-- A named kernel costs its body. -/
theorem builderFrame_named {nm : String} {args : List (Arg ℕ ℕ)} {x : Builder P ι ℕ ℕ Unit}
    {c : ℕ}
    (h : BuilderFrame I T p b m x c) : BuilderFrame I T p b m (named nm args x) c :=
  fun _ _ _ _ hk => triple_seq_frame (fun V₀ => triple_named (frame_run h V₀)) hk

/-- A branch costs at most the sum of its two arms. -/
theorem builderFrame_ite {q : P} {cmp : CmpOp} {x y : Cell ℕ ℕ} {t e : Builder P ι ℕ ℕ Unit}
    {c₁ c₂ : ℕ} (ht : BuilderFrame I T p b m t c₁) (he : BuilderFrame I T p b m e c₂) :
    BuilderFrame I T p b m (ifThenElse q cmp x y t e) (c₁ + c₂) := fun _ _ _ _ hk =>
  triple_seq_frame (fun V₀ => triple_ite (frame_run ht V₀) (frame_run he V₀)) hk

/-- An index binder costs at most its body at every index up to the bound. -/
theorem builderFrame_bindIdx {q : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ∀ v ≤ bound.eval, BuilderFrame I T p b m (body v) c) :
    BuilderFrame I T p b m (bindIdx q x bound body) c := fun _ _ _ _ hk =>
  triple_seq_frame (fun V₀ => triple_bindIdx fun v hv => frame_run (h v hv) V₀) hk

/-- A guarded block costs at most its body. -/
theorem builderFrame_eighWhen {e : IExp ℕ} {body : Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : BuilderFrame I T p b m body c) : BuilderFrame I T p b m (eighWhen e body) c := by
  unfold eighWhen
  refine builderFrame_mono (builderFrame_forRange fun _ => h) ?_
  simp only [IExp.eval_sub, IExp.eval_ofNat]
  exact (Nat.mul_le_mul_right c (show 1 - (1 - e.eval) ≤ 1 by omega)).trans (by simp)

/-- Binding two builders of cost $0$. -/
theorem builderFrame_bind_zero {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit}
    (hx : BuilderFrame I T p b m x 0) (hf : BuilderFrame I T p b m (f ()) 0) :
    BuilderFrame I T p b m (x >>= f) 0 := builderFrame_bind hx hf

/-- A loop of a body of cost $0$. -/
theorem builderFrame_forRange_zero {n : IExp ℕ} {body : ℕ → Builder P ι ℕ ℕ Unit}
    (h : ∀ i, BuilderFrame I T p b m (body i) 0) : BuilderFrame I T p b m (forRange n body) 0 :=
  builderFrame_mono (builderFrame_forRange h) (by simp)

/-- A branch of two arms of cost $0$. -/
theorem builderFrame_ite_zero {q : P} {cmp : CmpOp} {x y : Cell ℕ ℕ} {t e : Builder P ι ℕ ℕ Unit}
    (ht : BuilderFrame I T p b m t 0) (he : BuilderFrame I T p b m e 0) :
    BuilderFrame I T p b m (ifThenElse q cmp x y t e) 0 := builderFrame_ite ht he

/-- Close the side conditions of a frame rule: the written buffers are not the tracked one, the
dimensions are at most the bound. -/
scoped macro (name := frameSide) "frame_side" : tactic => `(tactic| (simp only [instrDst,
  List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq, List.not_mem_nil,
  IsEmpty.forall_iff, implies_true, and_true,
  IExp.eval_var, IExp.eval_add, IExp.eval_sub, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat,
  ne_eq, false_or, or_false, false_implies, forall_const, true_and] at * <;> omega))

/-- Prove `BuilderFrame … 0` for a block of scalar instructions, loops, binders and branches. -/
scoped macro (name := frameZero) "frame_zero" : tactic => `(tactic| repeat (first
  | exact builderFrame_pure
  | (apply builderFrame_ins; frame_side)
  | (apply builderFrame_forRange_zero; intro _)
  | apply builderFrame_scope
  | apply builderFrame_named
  | apply builderFrame_ite_zero
  | (apply builderFrame_bindIdx; intro _ _)
  | apply builderFrame_eighWhen
  | (apply builderFrame_allocBind; intro _ _)
  | apply builderFrame_bind_zero))

/-- `zmirror` keeps the tracked buffer when it does not write it, at cost $0$. -/
private theorem builderFrame_zmirror {q : P} {n : IExp ℕ} {Y : ℕ} {yo : IExp ℕ} (hY : Y ≠ b) :
    BuilderFrame I T p b m (zmirror q n Y yo) 0 := by
  unfold zmirror; frame_zero

/-- `zhermShift` keeps the tracked buffer when it does not write it, at cost $0$. -/
theorem builderFrame_zhermShift {q : P} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {c : Cell ℕ ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : BuilderFrame I T p b m (zhermShift q n X xo c Y yo) 0 := by
  unfold zhermShift; frame_zero

/-- `zhermScale` keeps the tracked buffer when it does not write it, at cost $0$. -/
theorem builderFrame_zhermScale {q : P} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {c : Cell ℕ ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : BuilderFrame I T p b m (zhermScale q n X xo c Y yo) 0 := by
  unfold zhermScale; frame_zero

/-- `zhermAvg` keeps the tracked buffer when it does not write it, at cost $0$. -/
theorem builderFrame_zhermAvg {q : P} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {c : Cell ℕ ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : BuilderFrame I T p b m (zhermAvg q n X xo c Y yo) 0 := by
  unfold zhermAvg; frame_zero

/-- `zcopy` keeps the tracked buffer when it does not write it, at cost $0$. -/
theorem builderFrame_zcopy {q : P} {n n' : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : BuilderFrame I T p b m (zcopy q n n' X xo Y yo) 0 := by
  unfold zcopy; frame_zero

/-- `zneg` keeps the tracked buffer when it does not write it, at cost $0$. -/
theorem builderFrame_zneg {q : P} {n n' : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : BuilderFrame I T p b m (zneg q n n' X xo Y yo) 0 := by
  unfold zneg; frame_zero

/-- `zconjTranspose` keeps the tracked buffer when it does not write it, at cost $0$. -/
theorem builderFrame_zconjTranspose {q : P} {n n' : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : BuilderFrame I T p b m (zconjTranspose q n n' X xo Y yo) 0 := by
  unfold zconjTranspose; frame_zero

/-- `zidentity` keeps the tracked buffer when it does not write it, at cost $0$. -/
theorem builderFrame_zidentity {q : P} {n : IExp ℕ} {Y : ℕ}
    {yo : IExp ℕ} (hY : Y ≠ b) : BuilderFrame I T p b m (zidentity q n Y yo) 0 := by
  unfold zidentity; frame_zero

/-- `ztraceRe` keeps the tracked buffer when it does not write it, at cost $0$. -/
theorem builderFrame_ztraceRe {q : P} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {d : Cell ℕ ℕ}
    (hd : d.buf ≠ b) : BuilderFrame I T p b m (ztraceRe q n X xo d) 0 := by
  unfold ztraceRe; frame_zero

/-- `zboxTest` keeps the tracked buffer when it does not write it, at cost $0$. -/
theorem builderFrame_zboxTest {q : P} {n n' : IExp ℕ} {X : ℕ} {xo : IExp ℕ} {lo hi fl : Cell ℕ ℕ}
    (hd : fl.buf ≠ b) : BuilderFrame I T p b m (zboxTest q n n' X xo lo hi fl) 0 := by
  unfold zboxTest; frame_zero

/-- Apply the frame rule of one of the complex BLAS blocks. -/
scoped macro (name := frameKernel) "frame_kernel" : tactic => `(tactic| first
  | (with_reducible apply builderFrame_zhermShift); frame_side
  | (with_reducible apply builderFrame_zhermScale); frame_side
  | (with_reducible apply builderFrame_zhermAvg); frame_side
  | (with_reducible apply builderFrame_zcopy); frame_side
  | (with_reducible apply builderFrame_zneg); frame_side
  | (with_reducible apply builderFrame_zconjTranspose); frame_side
  | (with_reducible apply builderFrame_zidentity); frame_side
  | (with_reducible apply builderFrame_ztraceRe); frame_side
  | (with_reducible apply builderFrame_zboxTest); frame_side)

/-- Prove `BuilderFrame` for a block of instructions, kernel calls and BLAS blocks. -/
scoped macro (name := frameBuilder) "frame_builder" : tactic => `(tactic| repeat (first
  | (with_reducible exact builderFrame_pure)
  | (with_reducible apply builderFrame_ins); frame_side
  | (with_reducible apply builderFrame_kcall) <;> frame_side
  | frame_kernel
  | (with_reducible apply builderFrame_forRange_zero); intro _; frame_zero; done
  | (with_reducible apply builderFrame_forRange); intro _
  | (with_reducible apply builderFrame_scope)
  | (with_reducible apply builderFrame_named)
  | (with_reducible apply builderFrame_ite)
  | (with_reducible apply builderFrame_bindIdx); intro _ _
  | (with_reducible apply builderFrame_eighWhen)
  | (with_reducible apply builderFrame_allocBind); intro _ _
  | (with_reducible apply builderFrame_bind)))

/-- The convergence test of the sign iteration: one kernel call. -/
private theorem builderFrame_newtonSchulzTestBlock {q : P} {mm : ι} {n : IExp ℕ} {X : ℕ}
    {xo : IExp ℕ} {W V : ℕ}
    {one lo hi fl : Cell ℕ ℕ} (hW : W ≠ b) (hV : V ≠ b) (hfl : fl.buf ≠ b) (hn : n.eval ≤ m) :
    BuilderFrame I T p b m (newtonSchulzTestBlock q mm n X xo W V one lo hi fl) 1 := by
  unfold newtonSchulzTestBlock
  apply builderFrame_mono
  · frame_builder
  · simp

/-- A step of the sign iteration: one kernel call. -/
private theorem builderFrame_newtonSchulzStepBlock {q : P} {mm : ι} {n : IExp ℕ} {X : ℕ}
    {xo : IExp ℕ} {W V : ℕ}
    {c : Cell ℕ ℕ} (hX : X ≠ b) (hW : W ≠ b) (hV : V ≠ b) (hc : c.buf ≠ b) (hn : n.eval ≤ m) :
    BuilderFrame I T p b m (newtonSchulzStepBlock q mm n X xo W V c) 1 := by
  unfold newtonSchulzStepBlock
  apply builderFrame_mono
  · frame_builder
  · simp

/-- The sign block: at most $2F + 1$ kernel calls of dimension at most $m$. -/
theorem builderFrame_eighSignBlock {q : P} {mm : ι} {n F : IExp ℕ} {A : ℕ} {ao : IExp ℕ} {par : ℕ}
    {po : IExp ℕ} {X : ℕ} {xo : IExp ℕ} (hX : X ≠ b) (hn : n.eval ≤ m) :
    BuilderFrame I T p b m (eighSignBlock q mm n F A ao par po X xo) (2 * F.eval + 1) := by
  unfold eighSignBlock
  apply builderFrame_mono
  · repeat (first
      | (with_reducible apply builderFrame_newtonSchulzTestBlock) <;> frame_side
      | (with_reducible apply builderFrame_newtonSchulzStepBlock) <;> frame_side
      | (with_reducible exact builderFrame_pure)
      | (with_reducible apply builderFrame_ins); frame_side
      | frame_kernel
      | (with_reducible apply builderFrame_forRange); intro _
      | (with_reducible apply builderFrame_scope)
      | (with_reducible apply builderFrame_ite)
      | (with_reducible apply builderFrame_allocBind); intro _ _
      | (with_reducible apply builderFrame_bind))
  · simp; omega

/-- The deflation block: two kernel calls of dimension at most $m$. -/
theorem builderFrame_eighDeflateBlock {q : P} {mm qr : ι} {n k r lo : IExp ℕ} {side : ℕ} {Sg : ℕ}
    {sq : Cell ℕ ℕ} {Pm G Y Qf Rf Qa : ℕ} {qo : IExp ℕ} (hG : G ≠ b) (hY : Y ≠ b) (hQf : Qf ≠ b)
    (hRf : Rf ≠ b) (hQa : Qa ≠ b) (hk : k.eval ≤ m) :
    BuilderFrame I T p b m (eighDeflateBlock q mm qr n k r lo side Sg sq Pm G Y Qf Rf Qa qo) 2 := by
  unfold eighDeflateBlock
  apply builderFrame_mono
  · frame_builder
  · simp

/-- The compression block: two kernel calls of dimension at most $m$. -/
theorem builderFrame_eighCompressBlock {q : P} {mm : ι} {k r : IExp ℕ} {Qa : ℕ} {qo : IExp ℕ}
    {Ma : ℕ}
    {mo co : IExp ℕ} {two sg : Cell ℕ ℕ} {Qh C1 C2 C3 : ℕ} (hMa : Ma ≠ b) (hQh : Qh ≠ b)
    (hC1 : C1 ≠ b) (hC2 : C2 ≠ b) (hC3 : C3 ≠ b) (hk : k.eval ≤ m) (hr : r.eval ≤ m) :
    BuilderFrame I T p b m (eighCompressBlock q mm k r Qa qo Ma mo co two sg Qh C1 C2 C3) 2 := by
  unfold eighCompressBlock
  apply builderFrame_mono
  · frame_builder
  · simp

/-- The leaf block keeps the tracked buffer, at cost $0$. -/
theorem builderFrame_eighLeafBlock {q : P} {diag : Bool} {k : IExp ℕ} {Ma : ℕ} {mo : IExp ℕ}
    {Ua : ℕ}
    {uo : IExp ℕ} {Ea : ℕ} {eo : IExp ℕ} {kd : Cell ℕ ℕ} (hUa : Ua ≠ b) (hEa : Ea ≠ b)
    (hkd : kd.buf ≠ b) :
    BuilderFrame I T p b m (eighLeafBlock q diag k Ma mo Ua uo Ea eo kd) 0 := by
  unfold eighLeafBlock
  cases diag <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> frame_zero

/-- The clamp block keeps the tracked buffer, at cost $0$. -/
theorem builderFrame_eighClampBlock {q : P} {k : IExp ℕ} {x z kc : Cell ℕ ℕ} (hx : x.buf ≠ b)
    (hz : z.buf ≠ b) (hkc : kc.buf ≠ b) : BuilderFrame I T p b m (eighClampBlock q k x z kc) 0 := by
  unfold eighClampBlock; frame_zero

/-! HT rules with continuations -/

section K

variable {V₀ : ℕ → Option K} {k : Unit → Stmt P ι ℕ ℕ} {Q : (ℕ → Option K) → Prop}

/-- A builder that keeps the tracked buffer, then the rest of a `bind`. -/
theorem triple_runCont_bind_of_builderFrame {x : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit}
    {c₁ c₂ : ℕ}
    (hx : BuilderFrame I T p b m x c₁) (hf : Triple I T p b m V₀ (runCont (f ()) k) c₂ Q) :
    Triple I T p b m V₀ (runCont (x >>= f) k) (c₁ + c₂) Q :=
  hx (fun a => runCont (f a) k) c₂ V₀ Q hf

/-- A builder that keeps the tracked buffer, then the continuation. -/
theorem triple_runCont_of_builderFrame {x : Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ}
    (hx : BuilderFrame I T p b m x c₁) (hk : Triple I T p b m V₀ (k ()) c₂ Q) :
    Triple I T p b m V₀ (runCont x k) (c₁ + c₂) Q :=
  hx k c₂ V₀ Q hk

/-- Reassociating a `bind` under a continuation. -/
theorem triple_runCont_bind {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : Triple I T p b m V₀ (runCont x (fun a => runCont (f a) k)) c Q) :
    Triple I T p b m V₀ (runCont (x >>= f) k) c Q := h

/-- An allocation under a continuation: a fresh handle above the tracked one. -/
theorem triple_runCont_alloc {q : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ∀ h, b < h → Triple I T p b m V₀ (runCont (f h) k) c Q) :
    Triple I T p b m V₀ (runCont (alloc q len >>= f) k) c Q :=
  triple_alloc h

/-- An index literal written to the tracked buffer, then the continuation. -/
theorem triple_runCont_litIdx {e m' : IExp ℕ} {c : ℕ}
    (h : Triple I T p b m (Function.update V₀ e.eval (I.sem.lit p (m'.eval : ℚ))) (k ()) c Q) :
    Triple I T p b m V₀ (runCont (ins (.litIdx p ⟨b, e⟩ m')) k) c Q := by
  change Triple I T p b m V₀ (.seq (.instr (.litIdx p ⟨b, e⟩ m')) (k ())) c Q
  exact triple_mono (triple_seq triple_litIdx fun _ h' => by subst h'; exact h) (by omega) le_rfl
    fun _ h => h

/-- A guarded block whose guard is $0$ is skipped. -/
private theorem triple_runCont_eighWhen_zero {e : IExp ℕ} {B : Builder P ι ℕ ℕ Unit} {c : ℕ}
    (he : 1 - (1 - e.eval) = 0) (h : Triple I T p b m V₀ (k ()) c Q) :
    Triple I T p b m V₀ (runCont (eighWhen e B) k) c Q := by
  change Triple I T p b m V₀ (.seq (.loop (1 - (1 - e)) fun _ => B.run) (k ())) c Q
  exact triple_mono (triple_seq (c₂ := c) (triple_loop_zero (Q := (· = V₀)) (by simpa using he) rfl)
    fun _ h' => by rw [h']; exact h) (by omega) le_rfl fun _ h => h

/-- A guarded block whose guard is $1$ runs once. -/
private theorem triple_runCont_eighWhen_one {e : IExp ℕ} {B : Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ}
    {Q₁ : (ℕ → Option K) → Prop} (he : 1 - (1 - e.eval) = 1)
    (hB : Triple I T p b m V₀ B.run c₁ Q₁) (h : ∀ V₁, Q₁ V₁ → Triple I T p b m V₁ (k ()) c₂ Q) :
    Triple I T p b m V₀ (runCont (eighWhen e B) k) (c₁ + c₂) Q :=
  triple_seq (triple_loop_one (n := 1 - (1 - e)) (body := fun _ => B.run) (by simpa using he) hB) h

/-- A scope, then the continuation. -/
theorem triple_runCont_scope {x : Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ} {Q₁ : (ℕ → Option K) → Prop}
    (hx : Triple I T p b m V₀ x.run c₁ Q₁) (h : ∀ V₁, Q₁ V₁ → Triple I T p b m V₁ (k ()) c₂ Q) :
    Triple I T p b m V₀ (runCont (scope x) k) (c₁ + c₂) Q :=
  triple_seq hx h

/-- A branch, then the continuation. -/
private theorem triple_runCont_ite {q : P} {cmp : CmpOp} {x y : Cell ℕ ℕ}
    {t e : Builder P ι ℕ ℕ Unit}
    {c₁ c₂ c₃ : ℕ} {Q₁ : (ℕ → Option K) → Prop}
    (ht : Triple I T p b m V₀ t.run c₁ Q₁) (he : Triple I T p b m V₀ e.run c₂ Q₁)
    (h : ∀ V₁, Q₁ V₁ → Triple I T p b m V₁ (k ()) c₃ Q) :
    Triple I T p b m V₀ (runCont (ifThenElse q cmp x y t e) k) (c₁ + c₂ + c₃) Q :=
  triple_seq (triple_ite ht he) h

/-- An index binder, then the continuation. -/
private theorem triple_runCont_bindIdx {q : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ} {Q₁ : (ℕ → Option K) → Prop}
    (hb : ∀ v ≤ bound.eval, Triple I T p b m V₀ (body v).run c₁ Q₁)
    (h : ∀ V₁, Q₁ V₁ → Triple I T p b m V₁ (k ()) c₂ Q) :
    Triple I T p b m V₀ (runCont (bindIdx q x bound body) k) (c₁ + c₂) Q :=
  triple_seq (triple_bindIdx hb) h

/-- An index binder that reads the tracked buffer, then the continuation. -/
theorem triple_runCont_bindIdx_read {e : IExp ℕ} {bound : IExp ℕ}
    {body : ℕ → Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ} {Q₁ : (ℕ → Option K) → Prop}
    (hb : Triple I T p b m V₀ (body (min (readNat I p V₀ e.eval) bound.eval)).run c₁ Q₁)
    (h : ∀ V₁, Q₁ V₁ → Triple I T p b m V₁ (k ()) c₂ Q) :
    Triple I T p b m V₀ (runCont (bindIdx p ⟨b, e⟩ bound body) k) (c₁ + c₂) Q :=
  triple_seq (triple_bindIdx_read hb) h

/-- The run of a builder is its run with the continuation `skip`. -/
theorem triple_run {x : Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : Triple I T p b m V₀ (runCont x fun _ => .skip) c Q) :
    Triple I T p b m V₀ x.run c Q := h

/-- A loop, then the continuation. -/
theorem triple_runCont_forRange {n : IExp ℕ} {body : ℕ → Builder P ι ℕ ℕ Unit} {c₁ c₂ : ℕ}
    {Q₁ : (ℕ → Option K) → Prop}
    (hl : Triple I T p b m V₀ (.loop n fun i => (body i).run) c₁ Q₁)
    (h : ∀ V₁, Q₁ V₁ → Triple I T p b m V₁ (k ()) c₂ Q) :
    Triple I T p b m V₀ (runCont (forRange n body) k) (c₁ + c₂) Q :=
  triple_seq hl h

/-- The continuation `skip`. -/
theorem triple_cont_skip (hQ : Q V₀) : Triple I T p b m V₀ ((fun _ => Stmt.skip) ()) 0 Q :=
  triple_skip hQ

end K

/-- the child block -/
private theorem triple_eighChildBlock {k : IExp ℕ} {Ma : ℕ} {mo mo' : IExp ℕ} {sg kd : Cell ℕ ℕ}
    {e : IExp ℕ}
    {code : ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hkd : kd.buf ≠ b) :
    Triple I T p b m V₀ (eighChildBlock p k Ma mo mo' sg ⟨b, e⟩ kd code).run 0
      (· = Function.update V₀ e.eval (I.sem.lit p (k.eval : ℚ))) := by
  unfold eighChildBlock
  apply triple_mono (c := 0 + (0 + 0)) _ (by omega) le_rfl fun _ h => h
  apply triple_runCont_bind_of_builderFrame (builderFrame_zhermShift hMa)
  apply triple_runCont_bind
  apply triple_runCont_litIdx
  apply triple_runCont_of_builderFrame (builderFrame_ins ?_)
  · exact triple_cont_skip rfl
  · exact hkd

/-- Apply the frame rule of one block of the spectral bisection program. -/
scoped macro (name := frameBlock) "frame_block" : tactic => `(tactic| first
  | (with_reducible apply builderFrame_eighDeflateBlock) <;> frame_side
  | (with_reducible apply builderFrame_eighCompressBlock) <;> frame_side
  | (with_reducible apply builderFrame_eighSignBlock) <;> frame_side
  | (with_reducible apply builderFrame_eighLeafBlock) <;> frame_side
  | (with_reducible apply builderFrame_eighClampBlock) <;> frame_side
  | (with_reducible apply builderFrame_ins); frame_side
  | (with_reducible apply builderFrame_kcall) <;> frame_side
  | frame_kernel
  | frame_builder)

/-- Prove `Triple` for a run through allocations, literal writes to the tracked buffer and
blocks that keep it. -/
scoped macro (name := frameTriple) "frame_triple" : tactic => `(tactic| repeat (first
  | (with_reducible apply triple_runCont_alloc); intro _ _
  | (with_reducible apply triple_runCont_bind); (with_reducible apply triple_runCont_litIdx)
  | (with_reducible apply triple_runCont_litIdx)
  | (with_reducible apply triple_runCont_bind_of_builderFrame); on_goal 1 => (frame_block; done)
  | (with_reducible apply triple_runCont_of_builderFrame); on_goal 1 => (frame_block; done)
  | exact triple_cont_skip rfl))

/-- A split writes the sizes of the two children, with at most eight kernel calls. -/
private theorem triple_eighSplitBlock {mm qr : ι} {n d lo k kp : IExp ℕ} {Sg Pp Pm Ma Qa Kd Kp : ℕ}
    {two sg nsg sq : Cell ℕ ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hQa : Qa ≠ b)
    (hKd : Kd ≠ b) (hKp : Kp ≠ b) (hk : k.eval ≤ m) (hkp : kp.eval ≤ k.eval) :
    Triple I T p b m V₀
      (eighSplitBlock p mm qr n d lo k kp Sg Pp Pm Ma Qa b Kd Kp two sg nsg sq).run 8
      (· = Function.update (Function.update V₀ (eighSlotOff n (d + 1) lo).eval
        (I.sem.lit p (kp.eval : ℚ))) (eighSlotOff n (d + 1) (lo + kp)).eval
        (I.sem.lit p ((k - kp).eval : ℚ))) := by
  unfold eighSplitBlock
  apply triple_run
  apply triple_mono (hm := le_rfl) (hQ := fun _ h => h)
  · apply triple_runCont_scope
    · apply triple_run
      dsimp only
      frame_triple
    · intro V h; exact triple_cont_skip h.symm
  · norm_num

/-- the effect of a node step on the size cells -/
def NodeEffect (I : Interp P ι K (OpCount P ι)) (p : P) (V₀ : ℕ → Option K) (i₀ k : ℕ)
    (V : ℕ → Option K) : Prop :=
  ∃ kp ≤ k, ((kp = 0 ∨ kp = k) ∧ V = Function.update V₀ i₀ (I.sem.lit p (k : ℚ))) ∨
    (0 < kp ∧ kp < k ∧ V = Function.update (Function.update V₀ i₀ (I.sem.lit p (kp : ℚ)))
      (i₀ + kp) (I.sem.lit p ((k - kp : ℕ) : ℚ)))

/-- The end of a node, at the split $k_+$ it read: the child or split blocks. -/
private theorem triple_nodeTail {mm qr : ι} {n d lo k : IExp ℕ} {Sg Pp Pm Ma Qa Kd Kp : ℕ}
    {two sg nsg sqh : Cell ℕ ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hQa : Qa ≠ b)
    (hKd : Kd ≠ b) (hKp : Kp ≠ b) (hk2 : 2 ≤ k.eval) (hkm : k.eval ≤ m) (v : ℕ)
    (hv : v ≤ k.eval) :
    Triple I T p b m V₀ (do
        eighWhen (1 - (k - IExp.var v))
          (eighChildBlock p k Ma (eighBlockOff n d lo) (eighBlockOff n (d + 1) lo) sg
            ⟨b, eighSlotOff n (d + 1) lo⟩ ⟨Kd, eighSlotOff n d lo⟩ 2)
        eighWhen (1 - IExp.var v)
          (eighChildBlock p k Ma (eighBlockOff n d lo) (eighBlockOff n (d + 1) lo) nsg
            ⟨b, eighSlotOff n (d + 1) lo⟩ ⟨Kd, eighSlotOff n d lo⟩ 3)
        eighWhen (IExp.var v * (k - IExp.var v))
          (eighSplitBlock p mm qr n d lo k (IExp.var v) Sg Pp Pm Ma Qa b Kd Kp two sg nsg sqh)
        : Builder P ι ℕ ℕ Unit).run 8
      (NodeEffect I p V₀ (eighSlotOff n (d + 1) lo).eval k.eval) := by
  apply triple_run
  apply triple_runCont_bind
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · -- the negative child
    apply triple_mono (c := 0 + 0) _ (by omega) le_rfl fun _ h => h
    apply triple_runCont_eighWhen_zero (by simp; omega)
    apply triple_runCont_bind
    apply triple_runCont_eighWhen_one (by simp) (triple_eighChildBlock hMa (by simpa using hKd))
    intro V₁ h₁
    apply triple_runCont_eighWhen_zero (by simp)
    apply triple_cont_skip
    exact ⟨0, by omega, Or.inl ⟨Or.inl rfl, h₁⟩⟩
  rcases Nat.lt_or_ge v k.eval with hvk | hvk
  · -- a split
    apply triple_mono (c := 8 + 0) _ (by omega) le_rfl fun _ h => h
    apply triple_runCont_eighWhen_zero (by simp; omega)
    apply triple_runCont_bind
    apply triple_runCont_eighWhen_zero (by simp; omega)
    have hvk' := Nat.mul_pos hv0 (Nat.sub_pos_of_lt hvk)
    apply triple_runCont_eighWhen_one (by simp; omega)
      (triple_eighSplitBlock hMa hQa hKd hKp hkm (by simp; omega))
    intro V₁ h₁
    apply triple_cont_skip
    refine ⟨v, by omega, Or.inr ⟨hv0, hvk, ?_⟩⟩
    rw [h₁]
    simp [eighSlotOff, Nat.add_assoc]
  · -- the positive child
    have hvk' : v = k.eval := by omega
    subst hvk'
    apply triple_mono (c := 0 + 0) _ (by omega) le_rfl fun _ h => h
    apply triple_runCont_eighWhen_one (by simp) (triple_eighChildBlock hMa (by simpa using hKd))
    intro V₁ h₁
    apply triple_runCont_bind
    apply triple_runCont_eighWhen_zero (by simp; omega)
    apply triple_runCont_eighWhen_zero (by simp)
    apply triple_cont_skip
    exact ⟨k.eval, le_rfl, Or.inl ⟨Or.inr rfl, h₁⟩⟩

/-- A node of size $k \ge 2$: at most $2F + 9$ kernel calls of dimension at most $m$, and the
effect `NLAlib.EighWeight.NodeEffect` on the size cells. -/
private theorem triple_eighNodeBlock {mm qr : ι} {n L F d lo k : IExp ℕ}
    {par Lv Su Sg Ma Qa Kd Kp : ℕ}
    {one two half negone sqh : Cell ℕ ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hQa : Qa ≠ b)
    (hKd : Kd ≠ b) (hKp : Kp ≠ b) (hk2 : 2 ≤ k.eval) (hkm : k.eval ≤ m) :
    Triple I T p b m V₀ (eighNodeBlock p mm qr n L F d lo k par Lv Su Sg Ma Qa b Kd Kp one two
      half negone sqh).run (2 * F.eval + 9)
      (NodeEffect I p V₀ (eighSlotOff n (d + 1) lo).eval k.eval) := by
  unfold eighNodeBlock
  apply triple_run
  apply triple_mono (hm := le_rfl) (hQ := fun _ h => h)
  · apply triple_runCont_scope
    · apply triple_run
      dsimp only
      frame_triple
      exact triple_runCont_bindIdx (fun v hv => triple_nodeTail hMa hQa hKd hKp hk2 hkm v hv)
        fun V h => triple_cont_skip h
    · intro V h; exact triple_cont_skip h
  · simp only [Nat.add_zero, Nat.zero_add]
    omega

/-- the body of a slot of a downward level, at the size `k` it reads -/
def downSlot (p : P) (mm qr : ι) (n L F d : IExp ℕ)
    (par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp t : ℕ)
    (one two half negone sqh : Cell ℕ ℕ) (lo k : ℕ) : Builder P ι ℕ ℕ Unit :=
  eighWhen (IExp.var k) do
    eighWhen (1 - (IExp.var k - 1))
      (eighLeafBlock p true (IExp.var k) Ma (eighBlockOff n d (IExp.var lo)) Ua
        (eighBlockOff n d (IExp.var lo)) Ea (eighSlotOff n d (IExp.var lo))
        ⟨Kd, eighSlotOff n d (IExp.var lo)⟩)
    eighWhen (IExp.var k - 1) do
      ins (.bin p .mul ⟨t, 4⟩ ⟨Lv, 2 * d + 1⟩ ⟨par, 0⟩)
      ifThenElse p .le ⟨Lv, 2 * d⟩ ⟨t, 4⟩
        (eighLeafBlock p false (IExp.var k) Ma (eighBlockOff n d (IExp.var lo)) Ua
          (eighBlockOff n d (IExp.var lo)) Ea (eighSlotOff n d (IExp.var lo))
          ⟨Kd, eighSlotOff n d (IExp.var lo)⟩)
        (eighNodeBlock p mm qr n L F d (IExp.var lo) (IExp.var k) par Lv Su Sg Ma Qa Sz Kd Kp one
          two half negone sqh)

/-- A slot of the downward pass at the size $k \le m$ it reads: at most $2F + 9$ kernel calls of
dimension at most $m$, and the size cells kept or changed by a node of size $k \ge 2$. -/
theorem triple_downSlot {mm qr : ι} {n L F d : IExp ℕ} {par Lv Su Sg Ma Ua Qa Ea Kd Kp t : ℕ}
    {one two half negone sqh : Cell ℕ ℕ} {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hUa : Ua ≠ b)
    (hQa : Qa ≠ b) (hEa : Ea ≠ b) (hKd : Kd ≠ b) (hKp : Kp ≠ b) (ht : t ≠ b) (lo k : ℕ)
    (hkm : k ≤ m) :
    Triple I T p b m V₀ (downSlot p mm qr n L F d par Lv Su Sg Ma Ua Qa Ea b Kd Kp t one two
      half negone sqh lo k).run (2 * F.eval + 9)
      (fun V => V = V₀ ∨
        (2 ≤ k ∧ NodeEffect I p V₀ (eighSlotOff n (d + 1) (IExp.var lo)).eval k V)) := by
  unfold downSlot
  apply triple_run
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · apply triple_mono (c := 0) _ (by omega) le_rfl fun _ h => h
      exact triple_runCont_eighWhen_zero (by simp) (triple_cont_skip (Or.inl rfl))
    · have hk1 : k = 1 := by omega
      subst hk1
      apply triple_mono (c := 0 + 0) _ (by omega) le_rfl fun _ h => h
      apply triple_runCont_eighWhen_one (by simp) _ fun V h => triple_cont_skip h
      apply triple_run
      apply triple_runCont_bind
      apply triple_mono (c := 0 + 0) _ (by omega) le_rfl fun _ h => h
      apply triple_runCont_eighWhen_one (by simp)
        (frame_run (builderFrame_eighLeafBlock hUa hEa (by simpa using hKd)) V₀)
      intro V₁ h₁
      apply triple_runCont_eighWhen_zero (by simp)
      exact triple_cont_skip (Or.inl h₁)
  · apply triple_mono (c := (2 * F.eval + 9) + 0) _ (by omega) le_rfl fun _ h => h
    apply triple_runCont_eighWhen_one (by simp; omega) _ fun V h => triple_cont_skip h
    apply triple_run
    apply triple_runCont_bind
    apply triple_runCont_eighWhen_zero (by simp; omega)
    apply triple_mono (c := (2 * F.eval + 9) + 0) _ (by omega) le_rfl fun _ h => h
    apply triple_runCont_eighWhen_one (by simp; omega) _ fun V h => triple_cont_skip h
    apply triple_run
    apply triple_mono (c := 0 + (0 + (2 * F.eval + 9) + 0)) _ (by omega) le_rfl fun _ h => h
    apply triple_runCont_bind_of_builderFrame (builderFrame_ins (by simpa [instrDst] using ht))
    apply triple_runCont_ite (Q₁ := fun V => V = V₀ ∨ (2 ≤ k ∧
      NodeEffect I p V₀ (eighSlotOff n (d + 1) (IExp.var lo)).eval k V))
    · exact triple_mono (frame_run (builderFrame_eighLeafBlock hUa hEa (by simpa using hKd)) V₀)
        le_rfl le_rfl
        fun V h => Or.inl h
    · exact triple_mono
        (triple_eighNodeBlock hMa hQa hKd hKp (by simpa using hk) (by simpa using hkm))
        le_rfl le_rfl fun V h => Or.inr ⟨hk, by simpa using h⟩
    · intro V h; exact triple_cont_skip h

end EighWeight

end NLAlib
