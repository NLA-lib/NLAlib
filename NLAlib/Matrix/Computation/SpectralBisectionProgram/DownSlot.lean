/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionNode
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Levels

/-!
# One slot of the downward level of the spectral bisection program

The slot of a node in one level of the downward pass of `NLAlib.eighProg`: the window a slot writes
(its record at depth $d$ and its children at depth $d + 1$), the run of the instructions and loops a
level uses, the equivalence of builders that differ only by the index normal form (a level at an
index variable runs as at the constant of its value), and the slot of a node: its record and its
children are written, and every cell outside its window is kept.

## Main results

* `NLAlib.holds_of_exec_eighSlotBody`: the slot of a node.
* `NLAlib.BuilderEquiv`, `NLAlib.exec_eighNodeBlock_var`, `NLAlib.exec_eighLeafBlock_var`:
  builders with the same index normal form.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! #### Helpers of `NLAlib.holds_of_exec_eighDownLevel` -/

omit [AddMonoid C] [Inhabited K] in
/-- A size written as a literal reads back as the size. -/
theorem readsIdx_of_read_eq_lit {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {s : Store P K} {p : P} {b i k : ℕ} (hk : k ≤ B)
    (h : s.read p b i = I.sem.lit p ((k : ℕ) : ℚ)) : ReadsIdx I.sem s p b i k := by
  obtain ⟨z, hz, -⟩ := hlit p k hk
  unfold ReadsIdx
  rw [h, hz, Option.bind_some]
  exact hlit.toNat_eq_of_lit_eq_some htn hk hz

omit [AddMonoid C] [Inhabited K] in
/-- A read of an index transfers along equal reads. -/
theorem readsIdx_of_read_eq {sem : ScalarSem P K} {s s' : Store P K} {p : P} {b i k : ℕ}
    (he : s'.read p b i = s.read p b i) (h : ReadsIdx sem s p b i k) : ReadsIdx sem s' p b i k := by
  unfold ReadsIdx at h ⊢
  rw [he]
  exact h

/-- The slots of the children of a node step at slot `lo`: none at a leaf, `lo` for one child,
`lo` and `lo + k₊` for a split. -/
def EighChildSlot {F' : Type*} {k : ℕ} (s : EighStep F' k) (lo j : ℕ) : Prop :=
  match s with
  | .leaf _ _ => False
  | .shift _ _ _ => j = lo
  | .split kp _ _ _ _ _ _ => j = lo ∨ j = lo + kp

/-- The cells the slot `lo` of depth $d$ may write, for a node of size $k$ whose children
start at the slots `cs`. -/
def EighSlotWindow (H : EighArenas) (n d lo k : ℕ) (cs : ℕ → Prop) (b i : ℕ) : Prop :=
  ((b = H.Qa ∨ b = H.Ua) ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * d + 2 * n * (lo + k)) ∨
    (b = H.Ma ∧ 2 * (n * n) * (d + 1) + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) ∨
    (b = H.Ea ∧ n * d + lo ≤ i ∧ i < n * d + lo + k) ∨
    ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo) ∨
    (b = H.Sz ∧ ∃ j, lo ≤ j ∧ j < lo + k ∧ cs j ∧ i = n * (d + 1) + j)

/-- The slot `lo` of depth $d$ is done for the node $y$: its record (as
`NLAlib.EighArenas.RecordHolds`) and its children's sizes and matrices are written. -/
def EighSlotDone (H : EighArenas) (sem : ScalarSem P K) (s : Store P K) (p : P)
    (M : FloatMachine K ℕ ℕ) (n F d : ℕ) (R₀ β : K) (lo : ℕ) (y : EighNode K) : Prop :=
  (match eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
      | .leaf U e => ReadsIdx sem s p H.Kd (n * d + lo) 1 ∧
          pairLayout.Holds s p H.Ua (2 * (n * n) * d + 2 * n * lo) U ∧
          ∀ i : Fin y.k, s.read p H.Ea (n * d + lo + i) = some (e i)
      | .shift b _ _ => ReadsIdx sem s p H.Kd (n * d + lo) (if b then 2 else 3)
      | .split kp _ Qp Qm _ _ _ => ReadsIdx sem s p H.Kd (n * d + lo) 4 ∧
          ReadsIdx sem s p H.Kp (n * d + lo) kp ∧
          pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
          pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (y.k * kp)) Qm) ∧
    ∀ (b : Bool) (lo' : ℕ) (y' : EighNode K), eighLoc M n F R₀ β d lo y [b] = some (lo', y') →
      ReadsIdx sem s p H.Sz (n * (d + 1) + lo') y'.k ∧
        pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo') y'.A

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- Two paths of one length that reach the same slot reach the same node: the nodes of a depth
have disjoint nonempty ranges. -/
theorem eq_of_eighLoc_slot {M : FloatMachine K ℕ ℕ} {N F : ℕ} {R₀ β : K}
    {A : Matrix (Fin N) (Fin N) (K × K)} {ε : K} {ℓ₀ : ℕ} (hN : 1 ≤ N) {a a' : List Bool}
    {lo : ℕ} {y y' : EighNode K} (hlen : a.length = a'.length)
    (h : eighLoc M N F R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (h' : eighLoc M N F R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a' = some (lo, y')) : y = y' := by
  by_cases hae : a = a'
  · subst hae
    rw [h] at h'
    exact (Prod.mk.inj (Option.some_inj.mp h')).2
  · have h1 := (eighLoc_bounds hN h).1
    have h2 := (eighLoc_bounds hN h').1
    rcases eighLoc_disjoint hlen hae h h' with h0 | h0 <;> omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The range of a node at an earlier slot of the same depth ends before a later node's slot. -/
theorem le_of_eighLoc_lt {M : FloatMachine K ℕ ℕ} {N F : ℕ} {R₀ β : K}
    {A : Matrix (Fin N) (Fin N) (K × K)} {ε : K} {ℓ₀ : ℕ} {a a' : List Bool} {lo lo' : ℕ}
    {y y' : EighNode K} (hlen : a'.length = a.length)
    (h : eighLoc M N F R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (h' : eighLoc M N F R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a' = some (lo', y')) (hlt : lo' < lo) :
    lo' + y'.k ≤ lo := by
  have hae : a' ≠ a := by
    rintro rfl
    rw [h] at h'
    have := (Prod.mk.inj (Option.some_inj.mp h')).1
    omega
  rcases eighLoc_disjoint hlen hae h' h with h0 | h0 <;> omega

omit [AddMonoid C] [Inhabited K] in
/-- A split of a node step is proper. -/
theorem lt_of_eighStep_split {M : FloatMachine K ℕ ℕ} {N F : ℕ} {R₀ β R ε : K} {ℓ k : ℕ}
    {A : Matrix (Fin k) (Fin k) (K × K)} {s : EighSample ℕ ℕ N} {kp : ℕ} {h : kp ≤ k}
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {Ap : Matrix (Fin kp) (Fin kp) (K × K)} {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)}
    {σ : K} (hs : eighStep M N F R₀ β A R ε ℓ s = .split kp h Qp Qm Ap Am σ) : 0 < kp ∧ kp < k := by
  unfold eighStep at hs
  dsimp only at hs
  split_ifs at hs
  cases hs
  omega

omit [AddMonoid C] [Inhabited K] in
/-- A slot of a child is reached by a path of one step. -/
theorem exists_eighLoc_of_eighChildSlot {M : FloatMachine K ℕ ℕ} {n F d lo j : ℕ} {R₀ β : K}
    {y : EighNode K}
    (h : EighChildSlot (eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo j) :
    ∃ (b : Bool) (y' : EighNode K), eighLoc M n F R₀ β d lo y [b] = some (j, y') := by
  revert h
  cases hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e => intro h; exact h.elim
  | shift b A' σ =>
    intro h
    change j = lo at h
    subst h
    exact ⟨b, ⟨y.k, A', (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
      y.ℓ + 1⟩, by simp [eighLoc, hs]⟩
  | split kp hkp Qp Qm Ap Am σ =>
    intro h
    change j = lo ∨ j = lo + kp at h
    rcases h with rfl | rfl
    · exact ⟨true, ⟨kp, Ap, (eighNextParams M y.R y.ε y.ℓ).1,
        (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩, by simp [eighLoc, hs]⟩
    · exact ⟨false, ⟨y.k - kp, Am, (eighNextParams M y.R y.ε y.ℓ).1,
        (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩, by simp [eighLoc, hs]⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A node window covers the cells a node step writes. -/
theorem mem_of_eighSlotWindow {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (h : EighSlotWindow H n d lo k cs b i) : b ∈ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ <;> omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The windows of slots with disjoint ranges are disjoint. -/
theorem false_of_eighSlotWindow_of_eighSlotWindow {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k
    lo' k' : ℕ}
    {cs cs' : ℕ → Prop} {b i : ℕ} (hk' : 1 ≤ k') (hlt : lo' + k' ≤ lo)
    (h₁ : EighSlotWindow H n d lo' k' cs' b i)
    (h₂ : EighSlotWindow H n d lo k cs b i) : False := by
  have e1 : 2 * n * (lo' + k') ≤ 2 * n * lo := Nat.mul_le_mul_left _ hlt
  unfold EighSlotWindow at h₁ h₂
  rcases h₁ with ⟨rfl | rfl, h1a, h1b⟩ | ⟨rfl, h1a, h1b⟩ | ⟨rfl, h1a, h1b⟩ | ⟨rfl | rfl, h1a⟩ |
      ⟨rfl, j1, hj1a, hj1b, -, hj1⟩ <;>
    rcases h₂ with ⟨hb2 | hb2, h2a, h2b⟩ | ⟨hb2, h2a, h2b⟩ | ⟨hb2, h2a, h2b⟩ | ⟨hb2 | hb2, h2a⟩ |
      ⟨hb2, j2, hj2a, hj2b, -, hj2⟩ <;>
    first | omega | simp [EighArenas.handles, hb2] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A cell of the size arena below depth $d + 1$ is in no window of depth $d$. -/
theorem not_eighSlotWindow_sz {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k : ℕ}
    {cs : ℕ → Prop} {i : ℕ} (hi : i < n * (d + 1)) : ¬ EighSlotWindow H n d lo k cs H.Sz i := by
  unfold EighSlotWindow
  intro h
  rcases h with ⟨hb | hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb | hb, -⟩ | ⟨-, j, -, -, -, hj⟩
  all_goals first | omega | simp [EighArenas.handles, hb] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A cell of the node arena below depth $d + 1$ is in no window of depth $d$. -/
theorem not_eighSlotWindow_ma {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k : ℕ}
    {cs : ℕ → Prop} {i : ℕ} (hi : i < 2 * (n * n) * (d + 1)) : ¬ EighSlotWindow H n d lo k cs H.Ma
        i := by
  unfold EighSlotWindow
  intro h
  rcases h with ⟨hb | hb, -⟩ | ⟨-, h1, -⟩ | ⟨hb, -⟩ | ⟨hb | hb, -⟩ | ⟨hb, -⟩
  all_goals first | omega | simp [EighArenas.handles, hb] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A cell of a buffer other than seven arenas is in no window. -/
theorem not_eighSlotWindow_of_not_mem {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hb : b ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz]) : ¬ EighSlotWindow H n d lo k cs b i :=
  fun h => hb (mem_of_eighSlotWindow h)

omit [AddMonoid C] [Inhabited K] in
/-- The done facts of a slot transfer along equal reads of its window. -/
theorem EighSlotDone.of_read_eq {H : EighArenas} {sem : ScalarSem P K} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F d : ℕ} {R₀ β : K} {lo : ℕ} {y : EighNode K} (hk1 : 1 ≤ y.k)
    (hk : lo + y.k ≤ n)
    (h : ∀ b i, EighSlotWindow H n d lo y.k
      (EighChildSlot (eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo) b i →
        s'.read p b i = s.read p b i)
    (hd : EighSlotDone H sem s p M n F d R₀ β lo y) : EighSlotDone H sem s' p M n F d R₀ β lo y :=
        by
  have hkn : y.k ≤ n := by omega
  have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ hkn
  have e1 : 2 * n * (lo + y.k) = 2 * n * lo + 2 * (n * y.k) := by ring
  obtain ⟨hr, hc⟩ := hd
  unfold EighSlotDone
  cases hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e =>
    simp only [hs] at hr h
    obtain ⟨h1, h2, h3⟩ := hr
    refine ⟨⟨readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)))))
      h1, pairLayout_holds_of_read_eq h2 fun i hi1 hi2 => h _ _ (Or.inl ⟨Or.inr rfl, hi1, by
          omega⟩),
      fun i => (h _ _ (Or.inr (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)))).trans (h3 i)⟩, ?_⟩
    intro b lo' y' hl
    simp [eighLoc, hs] at hl
  | shift b A' σ =>
    simp only [hs] at hr h
    refine ⟨readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩))))) hr,
      ?_⟩
    intro b' lo' y' hl
    obtain ⟨c1, c2⟩ := hc b' lo' y' hl
    simp only [eighLoc, hs] at hl
    split_ifs at hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
    refine ⟨readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl,
      by omega, rfl, rfl⟩))))) c1, pairLayout_holds_of_read_eq c2 fun i hi1 hi2 => h _ _
      (Or.inr (Or.inl ⟨rfl, hi1, by dsimp only at hi2; omega⟩))⟩
  | split kp hkp Qp Qm Ap Am σ =>
    obtain ⟨hkp0, hkpk⟩ := lt_of_eighStep_split hs
    have q1 : y.k * kp + y.k * (y.k - kp) = y.k * y.k := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hkp]
    have q2 : kp * kp ≤ n * y.k := Nat.mul_le_mul (by omega) hkp
    have q3 : (y.k - kp) * (y.k - kp) ≤ n * (y.k - kp) := Nat.mul_le_mul_right _ (by omega)
    have q5 : 2 * n * (lo + kp) = 2 * n * lo + 2 * (n * kp) := by ring
    have q4 : 2 * n * (lo + kp) + 2 * (n * (y.k - kp)) = 2 * n * (lo + y.k) := by
      rw [show lo + y.k = lo + kp + (y.k - kp) by omega]; ring
    simp only [hs] at hr h
    obtain ⟨h1, h2, h3, h4⟩ := hr
    refine ⟨⟨readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)))))
      h1, readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, rfl⟩))))) h2,
      pairLayout_holds_of_read_eq h3 fun i hi1 hi2 => h _ _ (Or.inl ⟨Or.inl rfl, hi1, by omega⟩),
      pairLayout_holds_of_read_eq h4 fun i hi1 hi2 => h _ _ (Or.inl ⟨Or.inl rfl, by omega, by
          omega⟩)⟩, ?_⟩
    intro b' lo' y' hl
    obtain ⟨c1, c2⟩ := hc b' lo' y' hl
    cases b' <;> simp only [eighLoc, hs, Bool.false_eq_true, if_true, if_false] at hl <;>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
    · refine ⟨readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo + kp,
        by omega, by omega, Or.inr rfl, rfl⟩))))) c1, pairLayout_holds_of_read_eq c2 fun i hi1 hi2
            => h _ _
        (Or.inr (Or.inl ⟨rfl, by omega, by dsimp only at hi2; omega⟩))⟩
    · refine ⟨readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl,
        by omega, Or.inl rfl, rfl⟩))))) c1, pairLayout_holds_of_read_eq c2 fun i hi1 hi2 => h _ _
        (Or.inr (Or.inl ⟨rfl, hi1, by dsimp only at hi2; omega⟩))⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A size cell in a window is a child slot. -/
theorem exists_eq_of_eighSlotWindow_sz {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k : ℕ}
    {cs : ℕ → Prop} {i : ℕ} (h : EighSlotWindow H n d lo k cs H.Sz i) :
    ∃ j, cs j ∧ i = n * (d + 1) + j := by
  rcases h with ⟨hb | hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb | hb, -⟩ | ⟨-, j, -, -, hj, hi⟩
  all_goals first | exact ⟨j, hj, hi⟩ | (exfalso; simp [EighArenas.handles, hb] at hnd)

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The cells outside a window of a leaf are outside its blocks. -/
private theorem bounds_of_eighSlotWindow_leaf {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i :
    ℕ}
    (hk : lo + k ≤ n) (hW : ¬ EighSlotWindow H n d lo k cs b i) :
    blockDisjoint (b, i, 1) (H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)) = true ∧
      blockDisjoint (b, i, 1) (H.Ea, n * d + lo, k) = true ∧
      blockDisjoint (b, i, 1) (H.Kd, n * d + lo, 1) = true := by
  have hkk : k * k ≤ n * k := Nat.mul_le_mul_right _ (by omega)
  have e1 : 2 * n * (lo + k) = 2 * n * lo + 2 * (n * k) := by ring
  have h1 : ¬ ((b = H.Qa ∨ b = H.Ua) ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * d + 2 * n * (lo + k)) := fun h => hW (Or.inl h)
  have h3 : ¬ (b = H.Ea ∧ n * d + lo ≤ i ∧ i < n * d + lo + k) :=
    fun h => hW (Or.inr (Or.inr (Or.inl h)))
  have h4 : ¬ ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo) :=
    fun h => hW (Or.inr (Or.inr (Or.inr (Or.inl h))))
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_⟩ <;> omega

omit [DecidableEq P] [Inhabited K] in
/-- The arenas stay allocated under a change of store of the same shape at the arenas. -/
theorem EighArenas.Shaped.of_shape_eq {H : EighArenas} {s s' : Store P K} {p : P} {n D : ℕ}
    (h : ∀ b ∈ H.handles, s'.shape[b]? = s.shape[b]?) (hH : H.Shaped s p n D) :
    H.Shaped s' p n D := by
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := hH
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := h
  exact ⟨hnd, l1.trans hMa, l2.trans hUa, l3.trans hQa, l4.trans hEa, l5.trans hSz, l6.trans hKd,
    l7.trans hKp, l8.trans hLv⟩

/-- The window test of a node of size `k` at the slot `lo` of `NLAlib.eighDownLevel`: the product
$\mathrm{fl}(\varepsilon R_0)$ in the cell $4$ of the scratch buffer `t`, then a leaf if
$R \le \mathrm{fl}(\varepsilon R_0)$ and the node step otherwise. -/
def eighSlotTest (p : P) (mm qr : ι)
    (n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo k : ℕ) : Builder P ι ℕ ℕ Unit := do
  ins (.bin p .mul ⟨t, 4⟩ ⟨Lv, 2 * .const d + 1⟩ ⟨par, 0⟩)
  ifThenElse p .le ⟨Lv, 2 * .const d⟩ ⟨t, 4⟩
    (eighLeafBlock p false (.var k) Ma (eighBlockOff (.const n) (.const d) (.var lo)) Ua
      (eighBlockOff (.const n) (.const d) (.var lo)) Ea
      (eighSlotOff (.const n) (.const d) (.var lo))
      ⟨Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩)
    (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.var lo) (.var k)
      par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)

/-- The slot `lo` of `NLAlib.eighDownLevel` for a node of stored size `k` (at least $1$): a leaf
of size $1$, or the window test of a larger node. -/
def eighSlotCase (p : P) (mm qr : ι)
    (n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo k : ℕ) : Builder P ι ℕ ℕ Unit := do
  eighWhen (1 - (.var k - 1))
    (eighLeafBlock p true (.var k) Ma (eighBlockOff (.const n) (.const d) (.var lo)) Ua
      (eighBlockOff (.const n) (.const d) (.var lo)) Ea
      (eighSlotOff (.const n) (.const d) (.var lo))
      ⟨Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩)
  eighWhen (.var k - 1)
    (eighSlotTest p mm qr n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo k)

/-- The body of the slot loop of `NLAlib.eighDownLevel` at slot `lo`, with the scratch
buffer `t` and the constants in `c`. -/
def eighSlotBody (p : P) (mm qr : ι)
    (n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo : ℕ) : Builder P ι ℕ ℕ Unit :=
  Builder.bindIdx p ⟨Sz, eighSlotOff (.const n) (.const d) (.var lo)⟩ (.const n - .var lo)
    fun k => eighWhen (.var k)
      (eighSlotCase p mm qr n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo k)

/-- Two builders run the same under continuations that run the same (used to move index
variables to constants inside a block, piece by piece). -/
def BuilderEquiv (I : Interp P ι K C) (X Y : Builder P ι ℕ ℕ Unit) : Prop :=
  ∀ k k' : Unit → Stmt P ι ℕ ℕ, (∀ st, exec I (k ()) st = exec I (k' ()) st) →
    ∀ st, exec I (ContT.run X k) st = exec I (ContT.run Y k') st

omit [Inhabited K] in
/-- Statements that run the same give builders that run the same. -/
private theorem BuilderEquiv.stmt {S S' : Stmt P ι ℕ ℕ} (h : ∀ st, exec I S st = exec I S' st) :
    BuilderEquiv I (Builder.stmt S) (Builder.stmt S') := by
  intro k k' hk st
  change exec I (.seq S (k ())) st = exec I (.seq S' (k' ())) st
  rw [exec_seq, exec_seq, h st]
  congr 1
  funext s
  exact hk s

omit [Inhabited K] in
/-- Instructions with the same index normal form run the same. -/
theorem BuilderEquiv.ins {i i' : Instr P ℕ ℕ} (h : i.normIdx = i'.normIdx) :
    BuilderEquiv I (Builder.ins i) (Builder.ins i') :=
  BuilderEquiv.stmt fun st => exec_eq_of_normIdx_eq I (by simp only [Stmt.normIdx, h]) st

omit [Inhabited K] in
/-- Kernel calls with the same index normal form run the same. -/
theorem BuilderEquiv.kcall {o : ι} {p : P} {dims dims' : List (IExp ℕ)}
    {ins ins' outs outs' : List (ℕ × IExp ℕ)}
    (h : (Stmt.kcall o p dims ins outs).normIdx = (Stmt.kcall o p dims' ins' outs').normIdx) :
    BuilderEquiv I (Builder.stmt (.kcall o p dims ins outs))
      (Builder.stmt (.kcall o p dims' ins' outs')) :=
  BuilderEquiv.stmt fun st => exec_eq_of_normIdx_eq I h st

omit [Inhabited K] in
/-- The empty builder runs as itself. -/
theorem BuilderEquiv.pure : BuilderEquiv I (pure () : Builder P ι ℕ ℕ Unit) (pure ()) :=
  fun _ _ hk st => hk st

omit [Inhabited K] in
/-- A sequence of builders that run the same runs the same. -/
theorem BuilderEquiv.bind {a a' : Builder P ι ℕ ℕ Unit} {f f' : Unit → Builder P ι ℕ ℕ Unit}
    (ha : BuilderEquiv I a a') (hf : BuilderEquiv I (f ()) (f' ())) :
    BuilderEquiv I (a >>= f) (a' >>= f') := fun k k' hk st =>
  ha (fun u => ContT.run (f u) k) (fun u => ContT.run (f' u) k') (fun st => hf k k' hk st) st

omit [Inhabited K] in
/-- Allocations of the same length, then bodies that run the same, run the same. -/
theorem BuilderEquiv.allocBind {p : P} {len len' : IExp ℕ} {f f' : ℕ → Builder P ι ℕ ℕ Unit}
    (hl : len.eval = len'.eval) (hf : ∀ h, BuilderEquiv I (f h) (f' h)) :
    BuilderEquiv I (Builder.alloc p len >>= f) (Builder.alloc p len' >>= f') := by
  intro k k' hk st
  change exec I (.alloc p len fun h => ContT.run (f h) k) st =
    exec I (.alloc p len' fun h => ContT.run (f' h) k') st
  rw [exec_alloc, exec_alloc, hl, hf _ k k' hk]

omit [Inhabited K] in
/-- Scopes of builders that run the same run the same. -/
theorem BuilderEquiv.scope {b b' : Builder P ι ℕ ℕ Unit} (hb : BuilderEquiv I b b') :
    BuilderEquiv I (Builder.scope b) (Builder.scope b') := by
  intro k k' hk st
  change exec I (.seq b.run (k ())) st = exec I (.seq b'.run (k' ())) st
  rw [exec_seq, exec_seq,
    show exec I b.run st = exec I b'.run st from hb (fun _ => .skip) (fun _ => .skip)
      (fun _ => rfl) st]
  congr 1
  funext s
  exact hk s

omit [Inhabited K] in
/-- Loops of the same length over bodies that run the same run the same. -/
theorem BuilderEquiv.forRange {n n' : IExp ℕ} {body body' : ℕ → Builder P ι ℕ ℕ Unit}
    (hn : n.eval = n'.eval) (hb : ∀ i, BuilderEquiv I (body i) (body' i)) :
    BuilderEquiv I (Builder.forRange n body) (Builder.forRange n' body') := by
  apply BuilderEquiv.stmt
  intro st
  rw [exec_loop, exec_loop, hn]
  congr 1
  funext s i
  exact hb i _ _ (fun _ => rfl) s

omit [Inhabited K] in
/-- Index binders on cells of the same normal form, with bounds of the same value and bodies
that run the same, run the same. -/
theorem BuilderEquiv.bindIdx {p : P} {x x' : Cell ℕ ℕ} {bound bound' : IExp ℕ}
    {body body' : ℕ → Builder P ι ℕ ℕ Unit} (hx : x.normIdx = x'.normIdx)
    (hb : bound.eval = bound'.eval) (h : ∀ i, BuilderEquiv I (body i) (body' i)) :
    BuilderEquiv I (Builder.bindIdx p x bound body) (Builder.bindIdx p x' bound' body') := by
  apply BuilderEquiv.stmt
  intro st
  have e1 : toNatStep I p x st = toNatStep I p x' st := by
    rw [show toNatStep I p x st = toNatStep I p x.normIdx st from rfl, hx]
    rfl
  rw [exec_bindIdx, exec_bindIdx, e1, hb]
  congr 1
  funext r
  split_ifs
  · exact h _ _ _ (fun _ => rfl) _
  · rfl

omit [Inhabited K] in
/-- Comparisons of cells of the same normal form, with branches that run the same, run the
same. -/
theorem BuilderEquiv.ite {p : P} {c : CmpOp} {x y x' y' : Cell ℕ ℕ}
    {t e t' e' : Builder P ι ℕ ℕ Unit} (hx : x.normIdx = x'.normIdx) (hy : y.normIdx = y'.normIdx)
    (ht : BuilderEquiv I t t') (he : BuilderEquiv I e e') :
    BuilderEquiv I (Builder.ifThenElse p c x y t e) (Builder.ifThenElse p c x' y' t' e') := by
  apply BuilderEquiv.stmt
  intro st
  have e1 : cmpStep I p c x y st = cmpStep I p c x' y' st := by
    rw [show cmpStep I p c x y st = cmpStep I p c x.normIdx y.normIdx st from rfl, hx, hy]
    rfl
  rw [exec_ite, exec_ite, e1]
  congr 1
  funext r
  split
  · exact ht _ _ (fun _ => rfl) _
  · exact he _ _ (fun _ => rfl) _

omit [Inhabited K] in
/-- Named blocks of builders that run the same run the same. -/
theorem BuilderEquiv.named {nm nm' : String} {args args' : List (Arg ℕ ℕ)}
    {b b' : Builder P ι ℕ ℕ Unit} (h : BuilderEquiv I b b') :
    BuilderEquiv I (Builder.named nm args b) (Builder.named nm' args' b') := by
  apply BuilderEquiv.stmt
  intro st
  rw [exec_named, exec_named]
  exact h _ _ (fun _ => rfl) st

omit [Inhabited K] in
/-- The node step at index variables runs as at the constants of their values. -/
private theorem builderEquiv_eighNodeBlock (p : P) (mm qr : ι) (n ℓ₀ F d lo k par Lv Su Sg Ma Qa Sz
    Kd Kp
    c : ℕ) :
    BuilderEquiv I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.var lo)
      (.var k) par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
    (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩) := by
  -- unfold every block down to the builder primitives, then walk them at reducible transparency
  unfold eighNodeBlock eighChildBlock eighClampBlock eighWhen eighSignBlock newtonSchulzTestBlock
    newtonSchulzStepBlock eighSplitBlock eighDeflateBlock eighCompressBlock
  unfold zhermShift zhermScale zneg ztraceRe zboxTest zhermAvg zcopy zconjTranspose
  unfold zmirror
  repeat' first
    | with_reducible exact BuilderEquiv.pure
    | with_reducible apply BuilderEquiv.ins
    | with_reducible apply BuilderEquiv.kcall
    | with_reducible apply BuilderEquiv.forRange
    | with_reducible apply BuilderEquiv.bindIdx
    | with_reducible apply BuilderEquiv.ite
    | with_reducible apply BuilderEquiv.named
    | with_reducible apply BuilderEquiv.scope
    | with_reducible apply BuilderEquiv.allocBind
    | with_reducible apply BuilderEquiv.bind
    | with_reducible intro _
    | rfl

omit [Inhabited K] in
/-- The node step at index variables runs as at the constants of their values. -/
theorem exec_eighNodeBlock_var (p : P) (mm qr : ι) (n ℓ₀ F d lo k par Lv Su Sg Ma Qa Sz Kd Kp
    c : ℕ) (st : St P K C) :
    exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.var lo) (.var k)
      par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
    exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st :=
  builderEquiv_eighNodeBlock p mm qr n ℓ₀ F d lo k par Lv Su Sg Ma Qa Sz Kd Kp c (fun _ => .skip)
    (fun _ => .skip) (fun _ => rfl) st

omit [Inhabited K] in
/-- A leaf at an index variable runs as at the constant of its value. -/
theorem exec_eighLeafBlock_var (p : P) (diag : Bool) (k Ma Ua Ea : ℕ) (mo uo eo : IExp ℕ)
    (kd : Cell ℕ ℕ) (st : St P K C) :
    exec I (eighLeafBlock (ι := ι) p diag (.var k) Ma mo Ua uo Ea eo kd).run st =
      exec I (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd).run st := by
  have hE : BuilderEquiv I (eighLeafBlock (ι := ι) p diag (.var k) Ma mo Ua uo Ea eo kd)
      (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd) := by
    cases diag <;> unfold eighLeafBlock <;>
    repeat' first
      | rfl
      | exact BuilderEquiv.pure
      | apply BuilderEquiv.ins
      | apply BuilderEquiv.kcall
      | apply BuilderEquiv.forRange
      | apply BuilderEquiv.bindIdx
      | apply BuilderEquiv.ite
      | apply BuilderEquiv.named
      | apply BuilderEquiv.scope
      | apply BuilderEquiv.allocBind
      | apply BuilderEquiv.bind
      | intro _
  exact hE (fun _ => .skip) (fun _ => .skip) (fun _ => rfl) st

omit [AddMonoid C] [Inhabited K] in
/-- A slot whose node step is a shift is done once the shifted matrix, its size and the kind are
written. -/
private theorem done_of_shift {dec : P → K → ℝ} {s : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F d lo : ℕ} {R₀ β : K} {H : EighArenas}
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) {y : EighNode K}
    (hkn : lo + y.k ≤ n) {b : Bool} {A' : Matrix (Fin y.k) (Fin y.k) (K × K)} {σ : K}
    (hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) = .shift b A' σ)
    (x1 : pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) A')
    (x2 : s.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((y.k : ℕ) : ℚ))
    (x3 : s.read p H.Kd (n * d + lo) = I.sem.lit p (((if b then 2 else 3 : ℕ)) : ℚ)) :
    EighSlotDone H I.sem s p M n F d R₀ β lo y := by
  unfold EighSlotDone
  rw [hs]
  refine ⟨readsIdx_of_read_eq_lit hlit htn (by split <;> omega) x3, fun b' lo' y' hl => ?_⟩
  simp only [eighLoc, hs] at hl
  split_ifs at hl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
  exact ⟨readsIdx_of_read_eq_lit (k := y.k) hlit htn (by omega) x2, x1⟩

omit [AddMonoid C] [Inhabited K] in
/-- A slot whose node step is a split is done once the bases, the children's matrices and
sizes, the kind and the split are written. -/
private theorem done_of_split {dec : P → K → ℝ} {s : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F d lo : ℕ} {R₀ β : K} {H : EighArenas}
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) {y : EighNode K}
    (hkn : lo + y.k ≤ n) {kp : ℕ} {hkp : kp ≤ y.k} {Qp : Matrix (Fin y.k) (Fin kp) (K × K)}
    {Qm : Matrix (Fin y.k) (Fin (y.k - kp)) (K × K)} {Ap : Matrix (Fin kp) (Fin kp) (K × K)}
    {Am : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) (K × K)} {σ : K}
    (hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) =
      .split kp hkp Qp Qm Ap Am σ)
    (x1 : pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (x2 : pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (y.k * kp)) Qm)
    (x3 : pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) Ap)
    (x4 : pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Am)
    (x5 : s.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ))
    (x6 : s.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((y.k - kp : ℕ) : ℚ))
    (x7 : s.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ))
    (x8 : s.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) :
    EighSlotDone H I.sem s p M n F d R₀ β lo y := by
  unfold EighSlotDone
  rw [hs]
  refine ⟨⟨readsIdx_of_read_eq_lit hlit htn (by omega) x7, readsIdx_of_read_eq_lit hlit htn (by
      omega) x8, x1, x2⟩,
    fun b' lo' y' hl => ?_⟩
  cases b' <;> simp only [eighLoc, hs, Bool.false_eq_true, if_true, if_false] at hl <;>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
  · exact ⟨readsIdx_of_read_eq_lit (k := y.k - kp) hlit htn (by omega) x6, x4⟩
  · exact ⟨readsIdx_of_read_eq_lit (k := kp) hlit htn (by omega) x5, x3⟩

/-! #### The blocks a slot writes, and its inputs -/

/-- The blocks the slot `lo` of depth $d$ writes for a node of size $k$ whose step has the
outcome `s`: a leaf writes its output, eigenvalues and kind, one child its matrix, size and kind
(`NLAlib.eighChildWindow`), a split its window (`NLAlib.eighSplitWindow`). -/
def eighSlotFp {F' : Type*} (H : EighArenas) (n d lo k : ℕ) : EighStep F' k → List (ℕ × ℕ × ℕ)
  | .leaf _ _ => [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)), (H.Ea, n * d + lo, k),
      (H.Kd, n * d + lo, 1)]
  | .shift _ _ _ => eighChildWindow H n d lo k
  | .split kp _ _ _ _ _ _ => eighSplitWindow H n d lo k kp

/-- A cell outside the window of a slot is disjoint from every block of the slot's footprint
(`NLAlib.eighSlotFp`). -/
theorem blockDisjoint_eighSlotFp {F' : Type*} {H : EighArenas} {n d lo k b i : ℕ}
    (s : EighStep F' k) (hk1 : 1 ≤ k) (hk : lo + k ≤ n)
    (hs : ∀ kp h Qp Qm Ap Am σ, s = .split kp h Qp Qm Ap Am σ → 0 < kp ∧ kp < k)
    (hW : ¬ EighSlotWindow H n d lo k (EighChildSlot s lo) b i) :
    ∀ x ∈ eighSlotFp H n d lo k s, blockDisjoint (b, i, 1) x = true := by
  cases s with
  | leaf U e =>
    obtain ⟨b1, b2, b3⟩ := bounds_of_eighSlotWindow_leaf hk hW
    simp [eighSlotFp, b1, b2, b3]
  | shift bb A σ =>
    refine blockDisjoint_eighChildWindow hk (j := lo) fun hN => hW ?_
    rcases hN with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, hi⟩ | ⟨hb, rfl⟩
    · exact Or.inl ⟨Or.inl rfl, h1, h2⟩
    · exact Or.inr (Or.inl ⟨rfl, h1, h2⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl, by omega, rfl, by
        rcases hi with rfl | rfl <;> rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, rfl⟩)))
  | split kp h Qp Qm Ap Am σ =>
    obtain ⟨hkp0, hkpk⟩ := hs _ _ _ _ _ _ _ rfl
    refine blockDisjoint_eighSplitWindow hk hkpk fun hN => hW ?_
    rcases hN with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, hi⟩ | ⟨hb, rfl⟩
    · exact Or.inl ⟨Or.inl rfl, h1, h2⟩
    · exact Or.inr (Or.inl ⟨rfl, h1, h2⟩)
    · rcases hi with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl, by omega, Or.inl rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo + kp, by omega, by omega, Or.inr rfl,
          rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, rfl⟩)))

/-- The inputs of the slot `lo` of depth $d$ for the node $y$ that are plain reads of the store:
its matrix, the window and tolerance of the depth, the stored $R_0$ and $\beta$, for a node of
size at least $2$ the node's uniform word and the level's Gaussian words, and the constants
(cells $0$ to $4$ of `c`: one, $\mathrm{fl}(2)$, $\mathrm{fl}(1/2)$, $-1$, the stored
$\sqrt{1/2}$). -/
def EighSlotIn (I : Interp P ι K C) (mmR : MatMulMap (K × K)) (qrR : QRMap (K × K)) (p : P)
    (H : EighArenas) (n d lo par Su Sg c : ℕ) (R₀ β : K) (y : EighNode K) (s : Store P K) :
    Prop :=
  pairLayout.Holds s p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A ∧
    s.read p H.Lv (2 * d) = some y.R ∧ s.read p H.Lv (2 * d + 1) = some y.ε ∧
    s.read p par 0 = some R₀ ∧ s.read p par 2 = some β ∧
    (2 ≤ y.k → s.read p Su lo = some (I.tape .uniform (n * d + lo)) ∧
      ∀ w < 4 * (n * n), s.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))) ∧
    s.read p c 0 = I.sem.lit p 1 ∧ s.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
    s.read p c 2 = some ((eighTapeMachine I p mmR qrR).div (eighTapeMachine I p mmR qrR).one
      ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
    s.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg (eighTapeMachine I p mmR qrR).one) ∧
    s.read p c 4 = some (I.sem.sqrtHalf p)

omit [AddMonoid C] in
/-- The inputs of a slot transfer along equal reads of the cells they read. -/
theorem EighSlotIn.of_read_eq {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)} {p : P}
    {H : EighArenas} {n d lo par Su Sg c : ℕ} {R₀ β : K} {y : EighNode K} {s s' : Store P K}
    (h : EighSlotIn I mmR qrR p H n d lo par Su Sg c R₀ β y s)
    (hr : ∀ q b i, (b = H.Lv ∨ b = par ∨ b = c ∨
      (b = H.Ma ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧
        i < 2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k)) ∨
      (2 ≤ y.k ∧ ((b = Su ∧ i = lo) ∨ (b = Sg ∧ i < 4 * (n * n))))) →
      s'.read q b i = s.read q b i) :
    EighSlotIn I mmR qrR p H n d lo par Su Sg c R₀ β y s' := by
  obtain ⟨hA, hR, hε, h0, h2, hS, c0, c1, c2, c3, c4⟩ := h
  refine ⟨pairLayout_holds_of_read_eq hA fun i h1 h2 => hr p _ i
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h2⟩)))),
    (hr _ _ _ (Or.inl rfl)).trans hR, (hr _ _ _ (Or.inl rfl)).trans hε,
    (hr _ _ _ (Or.inr (Or.inl rfl))).trans h0, (hr _ _ _ (Or.inr (Or.inl rfl))).trans h2,
    fun hk => ⟨(hr _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨hk, Or.inl ⟨rfl, rfl⟩⟩))))).trans
        (hS hk).1, fun w hw => (hr _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨hk,
          Or.inr ⟨rfl, hw⟩⟩))))).trans ((hS hk).2 w hw)⟩, ?_⟩
  exact ⟨(hr _ _ _ (Or.inr (Or.inr (Or.inl rfl)))).trans c0,
    (hr _ _ _ (Or.inr (Or.inr (Or.inl rfl)))).trans c1,
    (hr _ _ _ (Or.inr (Or.inr (Or.inl rfl)))).trans c2,
    (hr _ _ _ (Or.inr (Or.inr (Or.inl rfl)))).trans c3,
    (hr _ _ _ (Or.inr (Or.inr (Or.inl rfl)))).trans c4⟩

omit [AddMonoid C] [Inhabited K] in
/-- The window of the node step's branch at the split index of `NLAlib.eighStep` is the
footprint of the step's outcome (`NLAlib.eighSlotFp`), when the window test fails. -/
theorem eighBranchWindow_eq_eighSlotFp {M : FloatMachine K ℕ ℕ} {n F d lo k ℓ : ℕ}
    (hk2 : 2 ≤ k) (H : EighArenas) {A : Matrix (Fin k) (Fin k) (K × K)} {R R₀ ε β : K}
    (s : EighSample ℕ ℕ n) (hRt : M.le R (M.mul ε R₀) = false)
    {B Pp : Matrix (Fin k) (Fin k) (K × K)}
    (hB : B = newtonSchulzSign M β (M.mul (M.ofNat 2) R) F
      (M.hermShift A (M.unif (M.div R (M.ofNat ℓ)) s.1)))
    (hPp : Pp = M.hermScale (M.hermShift B (M.neg M.one)) (M.ofNat 2)) :
    eighBranchWindow H n d lo k (min k (M.toNat (M.add (M.traceRe Pp) (M.div M.one (M.ofNat 2)))))
      = eighSlotFp H n d lo k (eighStep M n F R₀ β A R ε ℓ s) := by
  subst hB hPp
  have hk : ¬ k ≤ 1 := by omega
  unfold eighStep
  simp only [hk, hRt, if_false, Bool.false_eq_true]
  unfold eighBranchWindow
  split_ifs <;> first | (exfalso; omega) | simp [eighSlotFp]

/-- The node step as a routine specification of `NLAlib.eighStep`: for a node $y$ of size at
least $2$ at the slot $lo$ of depth $d$ whose window test fails, the run of `NLAlib.eighNodeBlock`
modifies only the footprint of the step's outcome (`NLAlib.eighSlotFp`) and keeps the tape
positions, and the slot is then done (`NLAlib.EighSlotDone`). In mode `total` it also succeeds,
given the standard model, $R$ decoding to a nonzero value and $\ell_0 + d \ge 1$. No printed
source. -/
theorem spec_eighNodeStep {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F d D lo : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    (H : EighArenas) {par Su Sg c b : ℕ} {R₀ β : K} {y : EighNode K} (hk2 : 2 ≤ y.k)
    (hkn : lo + y.k ≤ n) (hℓ : y.ℓ = ℓ₀ + d) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlt : ∀ x ∈ H.handles ++ [par, Su, Sg, c], x < b)
    (hRt : (eighTapeMachine I p mmR qrR).le y.R
      ((eighTapeMachine I p mmR qrR).mul y.ε R₀) = false) :
    RoutineSpec md I (fun st => st.store.size = b ∧ H.Shaped st.store p n D ∧
        EighSlotIn I mmR qrR p H n d lo par Su Sg c R₀ β y st.store ∧
        md.Needs (dec p y.R ≠ 0 ∧ 1 ≤ ℓ₀ + d ∧ d < D))
      (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
        (.const y.k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
      (eighSlotFp H n d lo y.k (eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε
        y.ℓ (eighTapeSample n d lo)))
      fun st st' => EighSlotDone H I.sem st'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β
        lo y ∧ PosKept st st' := by
  obtain ⟨-, o, -, hl1, -, -⟩ := id hflag
  obtain ⟨z₂, hz₂, hdz₂⟩ := hlit p 2 (by omega)
  have hM1 : some (eighTapeMachine I p mmR qrR).one = some o := by
    change some ((I.sem.lit p 1).getD default) = _
    rw [hl1, Option.getD_some]
  have hM2 : some ((eighTapeMachine I p mmR qrR).ofNat 2) = some z₂ := by
    change some ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default) = _
    rw [hz₂, Option.getD_some]
  have hM : ∀ w, (eighTapeMachine I p mmR qrR).toNat w = ⌊dec p w⌋₊ := fun w => by
    change (I.sem.toNat p w).getD 0 = _
    rw [htn p w]
    split_ifs with h0
    · rfl
    · exact (Nat.floor_eq_zero.mpr (by linarith [not_le.mp h0])).symm
  let M := eighTapeMachine I p mmR qrR
  let B := newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) F (M.hermShift y.A
    (M.unif (M.div y.R (M.ofNat (ℓ₀ + d))) (eighTapeSample n d lo).1))
  let Pp := M.hermScale (M.hermShift B (M.neg M.one)) (M.ofNat 2)
  let Pm := M.hermScale (M.negMat (M.hermShift B M.one)) (M.ofNat 2)
  have hwin := eighBranchWindow_eq_eighSlotFp (d := d) (lo := lo) (ℓ := ℓ₀ + d) hk2 H (A := y.A)
    (R₀ := R₀) (β := β) (F := F) (eighTapeSample n d lo) hRt (B := B) (Pp := Pp) rfl rfl
  have hn := spec_eighNodeBlock (u := u) (safe := safe) hmm hqr md p n ℓ₀ F d lo y.k hsem hflag
    hcmp (fun q m hm => hlit q m (by omega)) htn hkn hk2 H hbufs hlt y.A B Pp Pm y.R β
    (I.tape .uniform (n * d + lo)) M.one (M.ofNat 2) (M.div M.one (M.ofNat 2)) (M.neg M.one)
    (fun w => I.tape .gaussian (4 * (n * n) * d + w))
    (min y.k (M.toNat (M.add (M.traceRe Pp) (M.div M.one (M.ofNat 2))))) rfl rfl rfl
    (by simp only [M, hM])
  have hwin' : eighBranchWindow H n d lo y.k (min y.k (M.toNat (M.add (M.traceRe Pp)
      (M.div M.one (M.ofNat 2))))) = eighSlotFp H n d lo y.k (eighStep M n F R₀ β y.A y.R y.ε
        y.ℓ (eighTapeSample n d lo)) := by
    rw [hℓ]
    exact hwin
  rw [← hwin']
  refine hn.conseq (fun st ⟨hsz, hH, hIn, hN⟩ => ?_) (fun x hx => hx)
    (fun st st' _ ⟨hbr, hp⟩ => ⟨?_, hp⟩)
  · obtain ⟨hA, hR, hε, h0, h2, hS, c0, c1, c2, c3, c4⟩ := hIn
    refine ⟨hsz, ⟨hA, hR, h2, (hS hk2).1, c0.trans (hl1.trans hM1.symm),
      c1.trans (hz₂.trans hM2.symm), c2, c3, c4, (hS hk2).2⟩, fun _ _ _ => rfl, ?_⟩
    refine (Mode.needs_and.mpr ⟨hsem, hN⟩).mono fun ⟨⟨hs, hsafe, hu⟩, hR, hℓ1, hdD⟩ => ⟨?_, hR, hℓ1,
      writableBlocks_eighBranchWindow hkn (by omega) hdD hH, fun q => hs.lit_ok p q (hsafe p q)⟩
    rw [Option.some.inj hM2, hdz₂]
    norm_num
  · have hmatch := eighStep_holds_of_branch (I := I) (mmR := mmR) (qrR := qrR) (n := n) (F := F)
      (d := d) (lo := lo) (ℓ₀ := ℓ₀) (N := b) hk2 H (p := p) (R := y.R) (R₀ := R₀) (ε := y.ε)
      (β := β) (A := y.A) (s := st'.store) (s' := st'.store)
      (fun x hx => hlt x (List.mem_append_left _ hx)) (fun _ => rfl) hRt
      (hbr (fun _ _ => rfl) rfl)
    dsimp only at hmatch
    cases hs : eighStep M n F R₀ β y.A y.R y.ε (ℓ₀ + d) (eighTapeSample n d lo) with
    | leaf U e => rw [hs] at hmatch; exact hmatch.elim
    | shift bb A' σ =>
      rw [hs] at hmatch
      exact done_of_shift hlit htn hkn (by rw [hℓ]; exact hs) hmatch.1 hmatch.2.1 hmatch.2.2
    | split kp hkp Qp Qm Ap Am σ =>
      rw [hs] at hmatch
      obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := hmatch
      exact done_of_split hlit htn hkn (by rw [hℓ]; exact hs) x1 x2 x3 x4 x5 x6 x7 x8

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The output, eigenvalue and kind blocks of a leaf at the slot $lo$ of depth $d < D$ are
writable in arenas shaped for $n$ and $D$. -/
theorem writableBlocks_eighSlotFp_leaf {H : EighArenas} {s : Store P K} {p : P}
    {n d lo k D : ℕ} (hd : d < D) (hk1 : 1 ≤ k) (hkn : lo + k ≤ n) (hH : H.Shaped s p n D) :
    WritableBlocks s p [(H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)),
      (H.Ea, n * d + lo, k), (H.Kd, n * d + lo, 1)] := by
  obtain ⟨-, -, hUa, -, hEa, -, hKd, -, -⟩ := hH
  have hkk : k * k ≤ n * k := Nat.mul_le_mul_right _ (by omega)
  have e5 : 2 * n * lo + 2 * (n * k) ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul_left (2 * n) hkn
    nlinarith
  have e6 : 2 * (n * n) * d + 2 * (n * n) ≤ 2 * (n * n) * (D + 1) := by
    have := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 ≤ D + 1 by omega)
    nlinarith
  have e7 : n * d + n ≤ n * D := by
    have := Nat.mul_le_mul_left n (show d + 1 ≤ D by omega)
    nlinarith
  have e8 : n * D ≤ n * (D + 1) := Nat.mul_le_mul_left n (by omega)
  simp only [WritableBlocks, List.forall_mem_cons]
  exact ⟨writable_of_shape_eq rfl hUa (by omega), writable_of_shape_eq rfl hEa (by omega),
    writable_of_shape_eq rfl hKd (by omega), fun x hx => absurd hx List.not_mem_nil⟩

/-- A leaf at the slot $lo$ of depth $d$ whose node step is a leaf (from the size test when
`diag`, from the window test otherwise) as a routine specification: the leaf block modifies only
the footprint of the step's outcome (`NLAlib.eighSlotFp`) and keeps the tape positions, and the
slot is then done. No printed source. -/
theorem spec_eighSlotLeaf (md : Mode) {dec : P → K → ℝ} (p : P) (diag : Bool) (n d D lo F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    (H : EighArenas) (hnd : H.handles.Nodup) {R₀ β : K} {y : EighNode K} (hk1 : 1 ≤ y.k)
    (hkn : lo + y.k ≤ n)
    (hstep : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
      (eighTapeSample n d lo) = .leaf ((eighTapeMachine I p mmR qrR).identityMat y.k)
        fun i => if diag then (y.A i i).1 else (eighTapeMachine I p mmR qrR).zero) :
    RoutineSpec md I (fun st => H.Shaped st.store p n D ∧
        pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A ∧ md.Needs (d < D))
      (eighLeafBlock p diag (.var y.k) H.Ma (eighBlockOff (.const n) (.const d) (.var lo)) H.Ua
        (eighBlockOff (.const n) (.const d) (.var lo)) H.Ea
        (eighSlotOff (.const n) (.const d) (.var lo))
        ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩)
      (eighSlotFp H n d lo y.k (eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε
        y.ℓ (eighTapeSample n d lo)))
      fun st st' => EighSlotDone H I.sem st'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β
        lo y ∧ PosKept st st' := by
  have e1 : (eighBlockOff (.const n) (.const d) (.var lo) : IExp ℕ).eval =
      2 * (n * n) * d + 2 * n * lo := by simp [eval_eighBlockOff]
  have e2 : (eighSlotOff (.const n) (.const d) (.var lo) : IExp ℕ).eval = n * d + lo := by
    simp [eval_eighSlotOff]
  have dMaUa : H.Ma ≠ H.Ua := fun h => by simp [EighArenas.handles, h] at hnd
  have dMaEa : H.Ma ≠ H.Ea := fun h => by simp [EighArenas.handles, h] at hnd
  have dUaEa : H.Ua ≠ H.Ea := fun h => by simp [EighArenas.handles, h] at hnd
  have dKdMa : H.Kd ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hnd
  have dKdUa : H.Kd ≠ H.Ua := fun h => by simp [EighArenas.handles, h] at hnd
  have dKdEa : H.Kd ≠ H.Ea := fun h => by simp [EighArenas.handles, h] at hnd
  have h1 := spec_eighLeafBlock (I := I) (toNat := fun x => (I.sem.toNat p x).getD 0)
    (mmR := mmR) (qrR := qrR) (unif := I.sem.tapeUnif p (I.tape .uniform))
    (normal := I.sem.tapeNormal p (I.tape .gaussian)) md p diag y.k (Ma := H.Ma) (Ua := H.Ua)
    (Ea := H.Ea) (mo := eighBlockOff (.const n) (.const d) (.var lo))
    (uo := eighBlockOff (.const n) (.const d) (.var lo))
    (eo := eighSlotOff (.const n) (.const d) (.var lo))
    (kd := ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩) y.A
    (blockDisjoint_of_fst_ne dMaUa.symm) (blockDisjoint_of_fst_ne dMaEa.symm)
    (blockDisjoint_of_fst_ne dUaEa) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨blockDisjoint_of_fst_ne dKdMa, blockDisjoint_of_fst_ne dKdUa,
        blockDisjoint_of_fst_ne dKdEa⟩)
  have h2 := h1.congr (r' := eighLeafBlock (ι := ι) p diag (.var y.k) H.Ma
    (eighBlockOff (.const n) (.const d) (.var lo)) H.Ua
    (eighBlockOff (.const n) (.const d) (.var lo)) H.Ea
    (eighSlotOff (.const n) (.const d) (.var lo))
    ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩) (by
      unfold eighLeafBlock; cases diag <;> exec_composable)
    fun st => exec_eighLeafBlock_var p diag y.k H.Ma H.Ua H.Ea _ _ _ _ st
  refine h2.conseq (fun st ⟨hH, hA, hdD⟩ => ⟨by simpa [e1] using hA, ?_⟩) (fun x hx => ?_)
    (fun st st' _ ⟨hU, hE, hK, hp⟩ => ⟨?_, hp⟩)
  · obtain ⟨z0, hz0, -⟩ := hlit p 0 (Nat.zero_le _)
    obtain ⟨z1, hz1, -⟩ := hlit p 1 (by omega)
    refine hdD.mono fun hdD => ⟨⟨z0, by simpa using hz0⟩, ⟨z1, by simpa using hz1⟩, ?_⟩
    simpa [e1, e2] using writableBlocks_eighSlotFp_leaf hdD hk1 hkn hH
  · rw [hstep]
    simpa [eighSlotFp, e1, e2] using hx
  · unfold EighSlotDone
    rw [hstep]
    refine ⟨⟨readsIdx_of_read_eq_lit (k := 1) hlit htn (by omega) (by simpa [e2] using hK),
      by rw [e1] at hU; exact hU, fun i => by have := hE i; rw [e2] at this; exact this⟩,
      fun b lo' y' hl => ?_⟩
    simp [eighLoc, hstep] at hl

omit [AddMonoid C] [Inhabited K] in
/-- A node of size at most $1$ is a leaf with the real diagonal. -/
theorem eighStep_eq_leaf_of_le_one {M : FloatMachine K ℕ ℕ} {N F k : ℕ} {R₀ β R ε : K} {ℓ : ℕ}
    {A : Matrix (Fin k) (Fin k) (K × K)} {s : EighSample ℕ ℕ N} (hk : k ≤ 1) :
    eighStep M N F R₀ β A R ε ℓ s = .leaf (M.identityMat k) fun i => (A i i).1 := by
  rw [eighStep, if_pos hk]

omit [AddMonoid C] [Inhabited K] in
/-- A node of size at least $2$ whose window test succeeds is a leaf with zero eigenvalues. -/
theorem eighStep_eq_leaf_of_le {M : FloatMachine K ℕ ℕ} {N F k : ℕ} {R₀ β R ε : K} {ℓ : ℕ}
    {A : Matrix (Fin k) (Fin k) (K × K)} {s : EighSample ℕ ℕ N} (hk : 2 ≤ k)
    (hle : M.le R (M.mul ε R₀) = true) :
    eighStep M N F R₀ β A R ε ℓ s = .leaf (M.identityMat k) fun _ => M.zero := by
  rw [eighStep, if_neg (by omega), if_pos hle]

omit [DecidableEq P] [AddMonoid C] in
/-- The window of a node whose window test fails decodes to a nonzero value: it is positive when
$R_0$ is, and $0$ only if $R_0$ is, in which case the test
$R \le \mathrm{fl}(\varepsilon R_0)$ would hold. -/
theorem dec_ne_zero_of_window {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop} {p : P}
    (hsem : IsRelErrSem u dec safe I.sem) (hsafe : ∀ p x, safe p x)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    {ε R₀ R : K} (hR₀ : 0 ≤ dec p R₀) (hRpos : 0 < dec p R₀ → 0 < dec p R)
    (hRz : dec p R₀ = 0 → dec p R = 0)
    (hr : (I.sem.cmp p .le R ((I.sem.bin p .mul ε R₀).getD default)).getD false = false) :
    dec p R ≠ 0 := by
  obtain ⟨v, hv⟩ := hsem.bin_ok p .mul ε R₀ trivial (fun h => by cases h) (hsafe p _)
  rw [hv, Option.getD_some, hcmp] at hr
  have hnle : ¬ dec p R ≤ dec p v := by simpa using hr
  refine (hR₀.lt_or_eq.elim hRpos fun h => absurd ?_ hnle).ne'
  obtain ⟨δ, -, hvd⟩ := hsem.bin_err p .mul ε R₀ v trivial hv
  rw [hRz h.symm, hvd, ← h]
  simp [BinOp.realOp]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- An exact comparison with a known outcome. -/
theorem cmp_eq_of_getD_eq {dec : P → K → ℝ} {p : P}
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y))) {a b : K}
    {r : Bool} (h : (I.sem.cmp p .le a b).getD false = r) : I.sem.cmp p .le a b = some r := by
  rw [hcmp] at h ⊢
  exact congrArg some h

omit [Inhabited K] in
/-- A specified routine from a false precondition: any composable builder. -/
theorem routineSpec_of_false {md : Mode} {r : Builder P ι ℕ ℕ Unit} (h : ExecutionComposable I r)
    (fp : List (ℕ × ℕ × ℕ)) (post : St P K C → St P K C → Prop) :
    RoutineSpec md I (fun _ => False) r fp post := ⟨h, fun _ hst => hst.elim⟩

/-- The product $\mathrm{fl}(\varepsilon R_0)$ of the window test, stored in the cell $4$ of the
scratch buffer `t`: it modifies only that cell, and the inputs of the slot are kept. In mode
`total` it succeeds under the standard model and the cell writable. No printed source. -/
theorem spec_eighSlotMul (md : Mode) {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (p : P) (n d D lo : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (H : EighArenas) {par Su Sg c t b : ℕ} {R₀ β : K} {y : EighNode K}
    (ht : t ∉ H.handles ++ [par, c]) (hSuT : Su = t → lo ≠ 4) (hSgT : Sg ≠ t) :
    RoutineSpec md I (fun st => st.store.size = b ∧ H.Shaped st.store p n D ∧
        EighSlotIn I mmR qrR p H n d lo par Su Sg c R₀ β y st.store ∧
        md.Needs (Writable st.store p t 4 1))
      (Builder.ins (.bin p .mul ⟨t, 4⟩ ⟨H.Lv, 2 * .const d + 1⟩ ⟨par, 0⟩))
      [(t, 4, 1)] fun st st' => st'.store.size = b ∧ H.Shaped st'.store p n D ∧
        EighSlotIn I mmR qrR p H n d lo par Su Sg c R₀ β y st'.store ∧
        st'.store.read p t 4 = some ((eighTapeMachine I p mmR qrR).mul y.ε R₀) ∧
        PosKept st st' := by
  have dt : ∀ b ∈ H.handles ++ [par, c], b ≠ t := fun b hb h => ht (h ▸ hb)
  have dLv := dt H.Lv (by simp [EighArenas.handles])
  have dMa := dt H.Ma (by simp [EighArenas.handles])
  have dpar := dt par (by simp)
  have dc := dt c (by simp)
  have s₁ := spec_bin_getD (m := md) (I := I) (p := p) (op := .mul) (dst := ⟨t, 4⟩)
    (x := ⟨H.Lv, 2 * .const d + 1⟩) (y := ⟨par, 0⟩) (a := y.ε) (b := R₀)
  have h1 : RoutineSpec md I _ (Builder.ins (.bin p .mul ⟨t, 4⟩ ⟨H.Lv, 2 * .const d + 1⟩ ⟨par, 0⟩))
      _ _ := ⟨(RoutineSpec.ins s₁).composable, (RoutineSpec.ins s₁).spec.with_modifies⟩
  refine h1.conseq (fun st ⟨hsz, hH, hIn, hN⟩ => ⟨hIn.2.2.1, hIn.2.2.2.1, ?_⟩)
    (fun x hx => hx) fun st st' ⟨hsz, hH, hIn, _⟩ ⟨hm, hr4, hp⟩ => ?_
  · refine (Mode.needs_and.mpr ⟨hsem, hN⟩).mono fun ⟨⟨hs, hsafe, _⟩, hW⟩ => ⟨?_, hW⟩
    exact hs.bin_ok p .mul y.ε R₀ trivial (fun h => by cases h) (hsafe p _)
  · refine ⟨hsz ▸ Store.size_eq_of_shape_eq hm.1, EighArenas.Shaped.of_shape_eq
      (fun b' _ => by rw [hm.1]) hH, hIn.of_read_eq fun q b' i hb => hm.2 q b' i ?_, hr4, hp⟩
    rcases hb with h | h | h | ⟨h, -⟩ | ⟨-, ⟨h, hi⟩ | ⟨h, -⟩⟩ <;> intro x hx <;>
      rw [List.mem_singleton] at hx <;> subst hx <;> rw [h]
    · exact blockDisjoint_of_fst_ne dLv
    · exact blockDisjoint_of_fst_ne dpar
    · exact blockDisjoint_of_fst_ne dc
    · exact blockDisjoint_of_fst_ne dMa
    · by_cases h' : Su = t
      · have := hSuT h'
        rw [blockDisjoint_iff]
        simp only [IExp.eval_ofNat]
        omega
      · exact blockDisjoint_of_fst_ne h'
    · exact blockDisjoint_of_fst_ne hSgT

/-- The precondition of the window test and of the slot of a node $y$: the arenas are shaped, the
inputs are stored, and in mode `total` the scratch cell is writable, $R_0 \ge 0$, the window
decodes to a positive value when $R_0$ does and to $0$ when it does, and $\ell_0 + d \ge 1$. -/
def EighSlotPre (I : Interp P ι K C) (mmR : MatMulMap (K × K)) (qrR : QRMap (K × K))
    (md : Mode) (dec : P → K → ℝ) (p : P) (H : EighArenas) (n ℓ₀ d D lo par Su Sg c t b : ℕ)
    (R₀ β : K) (y : EighNode K) (st : St P K C) : Prop :=
  st.store.size = b ∧ H.Shaped st.store p n D ∧
    EighSlotIn I mmR qrR p H n d lo par Su Sg c R₀ β y st.store ∧
    md.Needs (Writable st.store p t 4 1 ∧ 0 ≤ dec p R₀ ∧ (0 < dec p R₀ → 0 < dec p y.R) ∧
      (dec p R₀ = 0 → dec p y.R = 0) ∧ 1 ≤ ℓ₀ + d ∧ d < D)

/-- The window test of a node of size at least $2$ as a routine specification, when it fails: the
product, then the node step; it modifies only the scratch cell and the footprint of the step's
outcome, and the slot is then done. No printed source. -/
theorem spec_eighSlotTest_node {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F d D lo : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    (H : EighArenas) {par Su Sg c t b : ℕ} {R₀ β : K} {y : EighNode K} (hk2 : 2 ≤ y.k)
    (hkn : lo + y.k ≤ n) (hℓ : y.ℓ = ℓ₀ + d) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (ht : t ∉ H.handles ++ [par, c]) (hSuT : Su = t → lo ≠ 4) (hSgT : Sg ≠ t)
    (hlt : ∀ x ∈ H.handles ++ [par, Su, Sg, c], x < b)
    (hr : (eighTapeMachine I p mmR qrR).le y.R
      ((eighTapeMachine I p mmR qrR).mul y.ε R₀) = false) :
    RoutineSpec md I (EighSlotPre I mmR qrR md dec p H n ℓ₀ d D lo par Su Sg c t b R₀ β y)
      (eighSlotTest p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t lo y.k)
      ((t, 4, 1) :: eighSlotFp H n d lo y.k (eighStep (eighTapeMachine I p mmR qrR) n F R₀ β
        y.A y.R y.ε y.ℓ (eighTapeSample n d lo)))
      fun st st' => EighSlotDone H I.sem st'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β
        lo y ∧ PosKept st st' := by
  unfold eighSlotTest
  have hmul := (spec_eighSlotMul (I := I) (mmR := mmR) (qrR := qrR) md p n d D lo hsem H ht hSuT
    hSgT (b := b) (R₀ := R₀) (β := β) (y := y)).conseq
    (pre' := EighSlotPre I mmR qrR md dec p H n ℓ₀ d D lo par Su Sg c t b R₀ β y)
    (fun st ⟨hsz, hH, hIn, hN⟩ => ⟨hsz, hH, hIn, hN.mono (·.1)⟩) (fun x hx => hx)
    (fun _ _ _ h => h)
  have hnode := (spec_eighNodeStep hmm hqr md p n ℓ₀ F d D lo hsem hflag hcmp hlit htn H hk2
    hkn hℓ hbufs hlt hr (R₀ := R₀) (β := β)).congr (r' := eighNodeBlock p mm qr (.const n)
    (.const ℓ₀) (.const F) (.const d) (.var lo) (.var y.k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd
    H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩) (by unfold eighNodeBlock; exec_composable)
    fun st => exec_eighNodeBlock_var p mm qr n ℓ₀ F d lo y.k par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd
      H.Kp c st
  have hleaf := routineSpec_of_false (md := md) (I := I) (r := eighLeafBlock p false (.var y.k)
    H.Ma (eighBlockOff (.const n) (.const d) (.var lo)) H.Ua
    (eighBlockOff (.const n) (.const d) (.var lo)) H.Ea
    (eighSlotOff (.const n) (.const d) (.var lo))
    ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩) (by unfold eighLeafBlock; exec_composable)
    (eighSlotFp H n d lo y.k (eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε
      y.ℓ (eighTapeSample n d lo))) (fun _ _ => True)
  have hcm := cmp_eq_of_getD_eq hcmp hr
  have hite := RoutineSpec.ifThenElse (m := md) (I := I) (p := p) (c := .le) (r := false)
    (x := ⟨H.Lv, 2 * IExp.const d⟩) (y := ⟨t, 4⟩) (pre := fun st => st.store.size = b ∧
      H.Shaped st.store p n D ∧ EighSlotIn I mmR qrR p H n d lo par Su Sg c R₀ β y st.store ∧
      st.store.read p t 4 = some ((eighTapeMachine I p mmR qrR).mul y.ε R₀) ∧
      md.Needs (dec p y.R ≠ 0 ∧ 1 ≤ ℓ₀ + d ∧ d < D)) hleaf hnode
    (fun st ⟨_, _, hIn, hr4, _⟩ => ⟨y.R, _, by simpa using hIn.2.1, hr4, hcm⟩)
    (fun _ _ h => (Bool.false_ne_true h).elim) fun st ⟨hsz, hH, hIn, _, hN⟩ _ =>
      ⟨hsz, hH, hIn, hN⟩
  refine (RoutineSpec.bind hmul hite ?_).conseq (fun _ h => h) (fun x hx => hx) ?_
  · rintro st st₁ ⟨-, -, -, hN⟩ - ⟨hsz, hH, hIn, hr4, -⟩
    refine ⟨hsz, hH, hIn, hr4, (Mode.needs_and.mpr ⟨hsem, hN⟩).mono ?_⟩
    rintro ⟨⟨hs, hsafe, -⟩, -, hR0, hRp, hRz, hℓ1, hdD⟩
    exact ⟨dec_ne_zero_of_window hs hsafe hcmp hR0 hRp hRz hr, hℓ1, hdD⟩
  · rintro st st' - ⟨st₁, ⟨-, -, -, -, hp₁⟩, -, hp₂⟩
    exact ⟨(hp₂ rfl).1, (hp₂ rfl).2.trans hp₁⟩

/-- The window test of a node of size at least $2$ as a routine specification, when it succeeds:
the product, then a leaf with zero eigenvalues; it modifies only the scratch cell and the
footprint of the step's outcome, and the slot is then done. No printed source. -/
theorem spec_eighSlotTest_leaf {mm qr : ι} (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F d D lo : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    (H : EighArenas) (hnd : H.handles.Nodup) {par Su Sg c t b : ℕ} {R₀ β : K} {y : EighNode K}
    (hk2 : 2 ≤ y.k) (hkn : lo + y.k ≤ n) (ht : t ∉ H.handles ++ [par, c])
    (hSuT : Su = t → lo ≠ 4) (hSgT : Sg ≠ t)
    (hr : (eighTapeMachine I p mmR qrR).le y.R
      ((eighTapeMachine I p mmR qrR).mul y.ε R₀) = true) :
    RoutineSpec md I (EighSlotPre I mmR qrR md dec p H n ℓ₀ d D lo par Su Sg c t b R₀ β y)
      (eighSlotTest p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t lo y.k)
      ((t, 4, 1) :: eighSlotFp H n d lo y.k (eighStep (eighTapeMachine I p mmR qrR) n F R₀ β
        y.A y.R y.ε y.ℓ (eighTapeSample n d lo)))
      fun st st' => EighSlotDone H I.sem st'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β
        lo y ∧ PosKept st st' := by
  unfold eighSlotTest
  have hmul := (spec_eighSlotMul (I := I) (mmR := mmR) (qrR := qrR) md p n d D lo hsem H ht hSuT
    hSgT (b := b) (R₀ := R₀) (β := β) (y := y)).conseq
    (pre' := EighSlotPre I mmR qrR md dec p H n ℓ₀ d D lo par Su Sg c t b R₀ β y)
    (fun st ⟨hsz, hH, hIn, hN⟩ => ⟨hsz, hH, hIn, hN.mono (·.1)⟩) (fun x hx => hx)
    (fun _ _ _ h => h)
  have hleaf := spec_eighSlotLeaf (I := I) (mmR := mmR) (qrR := qrR) md p false n d D lo F hlit
    htn H hnd (R₀ := R₀) (β := β) (y := y) (by omega) hkn (by
      rw [eighStep_eq_leaf_of_le hk2 hr]; rfl)
  have hnode := routineSpec_of_false (md := md) (I := I) (r := eighNodeBlock p mm qr (.const n)
    (.const ℓ₀) (.const F) (.const d) (.var lo) (.var y.k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp
    ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩) (by unfold eighNodeBlock; exec_composable)
    (eighSlotFp H n d lo y.k (eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε
      y.ℓ (eighTapeSample n d lo))) (fun _ _ => True)
  have hcm := cmp_eq_of_getD_eq hcmp hr
  have hite := RoutineSpec.ifThenElse (m := md) (I := I) (p := p) (c := .le) (r := true)
    (x := ⟨H.Lv, 2 * IExp.const d⟩) (y := ⟨t, 4⟩) (pre := fun st => st.store.size = b ∧
      H.Shaped st.store p n D ∧ EighSlotIn I mmR qrR p H n d lo par Su Sg c R₀ β y st.store ∧
      st.store.read p t 4 = some ((eighTapeMachine I p mmR qrR).mul y.ε R₀) ∧ md.Needs (d < D))
    hleaf hnode (fun st ⟨_, _, hIn, hr4, _⟩ => ⟨y.R, _, by simpa using hIn.2.1, hr4, hcm⟩)
    (fun st ⟨_, hH, hIn, _, hdD⟩ _ => ⟨hH, hIn.1, hdD⟩)
    fun _ _ h => (Bool.false_ne_true h.symm).elim
  refine (RoutineSpec.bind hmul hite ?_).conseq (fun _ h => h) (fun x hx => hx) ?_
  · rintro st st₁ ⟨-, -, -, hN⟩ - ⟨hsz, hH, hIn, hr4, -⟩
    exact ⟨hsz, hH, hIn, hr4, hN.mono (·.2.2.2.2.2)⟩
  · rintro st st' - ⟨st₁, ⟨-, -, -, -, hp₁⟩, hp₂, -⟩
    exact ⟨(hp₂ rfl).1, (hp₂ rfl).2.trans hp₁⟩

/-- The window test of a node of size at least $2$ as a routine specification: the product, then
a leaf or the node step by the outcome of the comparison; it modifies only the scratch cell and
the footprint of the step's outcome, and the slot is then done. No printed source. -/
theorem spec_eighSlotTest {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F d D lo : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    (H : EighArenas) {par Su Sg c t b : ℕ} {R₀ β : K} {y : EighNode K} (hk2 : 2 ≤ y.k)
    (hkn : lo + y.k ≤ n) (hℓ : y.ℓ = ℓ₀ + d) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (ht : t ∉ H.handles ++ [par, c]) (hSuT : Su = t → lo ≠ 4) (hSgT : Sg ≠ t)
    (hlt : ∀ x ∈ H.handles ++ [par, Su, Sg, c], x < b) :
    RoutineSpec md I (EighSlotPre I mmR qrR md dec p H n ℓ₀ d D lo par Su Sg c t b R₀ β y)
      (eighSlotTest p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t lo y.k)
      ((t, 4, 1) :: eighSlotFp H n d lo y.k (eighStep (eighTapeMachine I p mmR qrR) n F R₀ β
        y.A y.R y.ε y.ℓ (eighTapeSample n d lo)))
      fun st st' => EighSlotDone H I.sem st'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β
        lo y ∧ PosKept st st' := by
  cases hr : (eighTapeMachine I p mmR qrR).le y.R ((eighTapeMachine I p mmR qrR).mul y.ε R₀)
  · exact spec_eighSlotTest_node hmm hqr md p n ℓ₀ F d D lo hsem hflag hcmp hlit htn H hk2 hkn
      hℓ hbufs ht hSuT hSgT hlt hr
  · exact spec_eighSlotTest_leaf md p n ℓ₀ F d D lo hsem hcmp hlit htn H
      (hbufs.sublist (List.sublist_append_left _ _)) hk2 hkn ht hSuT hSgT hr

/-- The slot of a node of size $1$ as a routine specification: the leaf of the size test; the
window test is skipped. No printed source. -/
theorem spec_eighSlotCase_one {mm qr : ι} (md : Mode) {dec : P → K → ℝ} (p : P)
    (n ℓ₀ F d D lo : ℕ) (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    (H : EighArenas) (hnd : H.handles.Nodup) {par Su Sg c t b : ℕ} {R₀ β : K}
    {y : EighNode K} (hk1 : y.k = 1) (hkn : lo + y.k ≤ n) :
    RoutineSpec md I (EighSlotPre I mmR qrR md dec p H n ℓ₀ d D lo par Su Sg c t b R₀ β y)
      (eighSlotCase p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t lo y.k)
      (eighSlotFp H n d lo y.k (eighStep (eighTapeMachine I p mmR qrR) n F R₀ β
        y.A y.R y.ε y.ℓ (eighTapeSample n d lo)))
      fun st st' => EighSlotDone H I.sem st'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β
        lo y ∧ PosKept st st' := by
  have hstep : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
      (eighTapeSample n d lo) = .leaf ((eighTapeMachine I p mmR qrR).identityMat y.k)
        fun i => if true then (y.A i i).1 else (eighTapeMachine I p mmR qrR).zero :=
    eighStep_eq_leaf_of_le_one hk1.le
  have hA := (spec_eighWhen (I := I) (m := md) (e := (1 - (.var y.k - 1) : IExp ℕ))
    (fun _ => (spec_eighSlotLeaf (mmR := mmR) (qrR := qrR) md p true n d D lo F hlit htn H hnd
      (R₀ := R₀) (β := β) (by omega) hkn hstep).spec)).conseq
    (pre' := EighSlotPre I mmR qrR md dec p H n ℓ₀ d D lo par Su Sg c t b R₀ β y)
    (fun st ⟨_, hH, hIn, hN⟩ => ⟨hH, hIn.1, hN.mono (·.2.2.2.2.2)⟩) (fun x hx => hx)
    (fun _ _ _ h => h)
  have hC := spec_eighWhen (I := I) (m := md) (e := (.var y.k - 1 : IExp ℕ))
    (body := eighSlotTest p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t
      lo y.k) (pre := fun _ => True) (fp := []) (post := fun _ _ => True)
    (fun h => absurd h (by change ¬ 0 < y.k - 1; omega))
  unfold eighSlotCase
  refine (RoutineSpec.bind hA hC fun _ _ _ _ _ => trivial).conseq (fun _ h => h)
    (fun x hx => by simpa using hx) ?_
  rintro st st' - ⟨st₁, ⟨-, hA1⟩, hC1, -⟩
  have hk : 0 < (1 - (IExp.var y.k - 1) : IExp ℕ).eval := by
    change 0 < 1 - (y.k - 1)
    omega
  obtain ⟨hdone, hp⟩ := hA1 hk
  obtain rfl := hC1 (by change y.k - 1 = 0; omega)
  exact ⟨hdone, hp⟩

/-- The slot of a node of size at least $2$ as a routine specification: the leaf of the size test
is skipped, and the window test runs. No printed source. -/
theorem spec_eighSlotCase_two {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F d D lo : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    (H : EighArenas) {par Su Sg c t b : ℕ} {R₀ β : K} {y : EighNode K} (hk2 : 2 ≤ y.k)
    (hkn : lo + y.k ≤ n) (hℓ : y.ℓ = ℓ₀ + d) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (ht : t ∉ H.handles ++ [par, c]) (hSuT : Su = t → lo ≠ 4) (hSgT : Sg ≠ t)
    (hlt : ∀ x ∈ H.handles ++ [par, Su, Sg, c], x < b) :
    RoutineSpec md I (EighSlotPre I mmR qrR md dec p H n ℓ₀ d D lo par Su Sg c t b R₀ β y)
      (eighSlotCase p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t lo y.k)
      ((t, 4, 1) :: eighSlotFp H n d lo y.k (eighStep (eighTapeMachine I p mmR qrR) n F R₀ β
        y.A y.R y.ε y.ℓ (eighTapeSample n d lo)))
      fun st st' => EighSlotDone H I.sem st'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β
        lo y ∧ PosKept st st' := by
  have hA := spec_eighWhen (I := I) (m := md) (e := (1 - (.var y.k - 1) : IExp ℕ))
    (body := eighLeafBlock p true (.var y.k) H.Ma (eighBlockOff (.const n) (.const d) (.var lo))
      H.Ua (eighBlockOff (.const n) (.const d) (.var lo)) H.Ea
      (eighSlotOff (.const n) (.const d) (.var lo))
      ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩)
    (pre := EighSlotPre I mmR qrR md dec p H n ℓ₀ d D lo par Su Sg c t b R₀ β y) (fp := [])
    (post := fun _ _ => True) (fun h => absurd h (by change ¬ 0 < 1 - (y.k - 1); omega))
  have hC := spec_eighWhen (I := I) (m := md) (e := (.var y.k - 1 : IExp ℕ))
    (fun _ => (spec_eighSlotTest hmm hqr md p n ℓ₀ F d D lo hsem hflag hcmp hlit htn H hk2 hkn
      hℓ hbufs ht hSuT hSgT hlt (R₀ := R₀) (β := β)).spec)
  unfold eighSlotCase
  refine (RoutineSpec.bind hA hC ?_).conseq (fun _ h => h) (fun x hx => by simpa using hx) ?_
  · rintro st st₁ hpre - ⟨hA0, -⟩
    obtain rfl := hA0 (by change 1 - (y.k - 1) = 0; omega)
    exact hpre
  · rintro st st' - ⟨st₁, ⟨hA0, -⟩, -, hC1⟩
    obtain rfl := hA0 (by change 1 - (y.k - 1) = 0; omega)
    exact hC1 (by change 0 < y.k - 1; omega)

/-- The slot of a node of depth $d$ as a routine specification: from a store holding the node's
size, matrix, window and tolerance, the samples and the constants, the run of
`NLAlib.eighSlotBody` modifies only the footprint of the node step's outcome
(`NLAlib.eighSlotFp`) and the scratch cell `t[4]`, keeps the tape positions, and the slot is
done (`NLAlib.EighSlotDone`). In mode `total` it also succeeds, given the standard model with
every value in range, $R_0 \ge 0$ with the windows positive when it is and zero when it is,
$\ell_0 + d \ge 1$, $d < D$ and the scratch cell writable. No printed source. -/
theorem spec_eighSlotBody {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F d D lo : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    (H : EighArenas) {par Su Sg c t b : ℕ} {R₀ β : K} {y : EighNode K} (hk1 : 1 ≤ y.k)
    (hkn : lo + y.k ≤ n) (hℓ : y.ℓ = ℓ₀ + d) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (ht : t ∉ H.handles ++ [par, c]) (hSuT : 2 ≤ y.k → Su = t → lo ≠ 4)
    (hSgT : 2 ≤ y.k → Sg ≠ t) (hlt : 2 ≤ y.k → ∀ x ∈ H.handles ++ [par, Su, Sg, c], x < b)
    (v : K) (hv : I.sem.toNat p v = some y.k) :
    RoutineSpec md I (fun st => st.store.read p H.Sz (n * d + lo) = some v ∧
        EighSlotPre I mmR qrR md dec p H n ℓ₀ d D lo par Su Sg c t b R₀ β y st)
      (eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t lo)
      (eighSlotFp H n d lo y.k (eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
        (eighTapeSample n d lo)) ++ [(t, 4, 1)])
      fun st st' => EighSlotDone H I.sem st'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β
        lo y ∧ PosKept st st' := by
  have hnd : H.handles.Nodup := hbufs.sublist (List.sublist_append_left _ _)
  have hbound : y.k ≤ (IExp.const n - IExp.var lo).eval := by
    change y.k ≤ n - lo
    omega
  have hcase : RoutineSpec md I
      (EighSlotPre I mmR qrR md dec p H n ℓ₀ d D lo par Su Sg c t b R₀ β y)
      (eighSlotCase p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c t lo y.k)
      ((t, 4, 1) :: eighSlotFp H n d lo y.k (eighStep (eighTapeMachine I p mmR qrR) n F R₀ β
        y.A y.R y.ε y.ℓ (eighTapeSample n d lo)))
      fun st st' => EighSlotDone H I.sem st'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β
        lo y ∧ PosKept st st' := by
    rcases Nat.lt_or_ge y.k 2 with hk | hk
    · exact (spec_eighSlotCase_one (mm := mm) (qr := qr) md p n ℓ₀ F d D lo hlit htn H hnd
        (par := par) (Su := Su) (Sg := Sg) (c := c) (t := t) (b := b) (R₀ := R₀) (β := β)
        (by omega) hkn).conseq (fun _ h => h) (fun x hx => List.mem_cons_of_mem _ hx)
        fun _ _ _ h => h
    · exact spec_eighSlotCase_two hmm hqr md p n ℓ₀ F d D lo hsem hflag hcmp hlit htn H hk hkn hℓ
        hbufs ht (hSuT hk) (hSgT hk) (hlt hk)
  have hw := spec_eighWhen (I := I) (m := md) (e := (.var y.k : IExp ℕ)) (fun _ => hcase.spec)
  refine RoutineSpec.conseq (RoutineSpec.bindIdx_of_read
    (x := ⟨H.Sz, eighSlotOff (.const n) (.const d) (.var lo)⟩) (bound := .const n - .var lo)
    (v := v) (k := y.k) (fun st hst => by simpa [eighSlotOff] using hst.1) hv
    (Mode.needs_of hbound md) (fun _ => hw.spec) (fun st hst => hst.2)) (fun _ h => h)
    (fun x hx => ?_) ?_
  · rcases List.mem_cons.mp hx with rfl | h
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ h
  · rintro st st' - ⟨-, h0, hpos⟩
    exact hpos (by change 0 < y.k; omega)

omit [Inhabited K] in
/-- A slot that starts no node (its size cell reads $0$) as a routine specification: the run
changes nothing but the count. No printed source. -/
theorem spec_eighSlotBody_skip {mm qr : ι} (md : Mode) (p : P)
    (n ℓ₀ F d lo par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t : ℕ) (v : K)
    (hv : I.sem.toNat p v = some 0) :
    RoutineSpec md I (fun st => st.store.read p Sz (n * d + lo) = some v)
      (eighSlotBody p mm qr n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo) []
      fun st st' => st'.store = st.store ∧ PosKept st st' := by
  have hw := spec_eighWhen (I := I) (m := md) (e := (.var 0 : IExp ℕ))
    (body := eighSlotCase p mm qr n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo 0)
    (pre := fun _ => True) (fp := []) (post := fun _ _ => True) (fun h => absurd h (by simp))
  unfold eighSlotBody
  refine RoutineSpec.conseq (RoutineSpec.bindIdx_of_read
    (x := ⟨Sz, eighSlotOff (.const n) (.const d) (.var lo)⟩) (bound := .const n - .var lo)
    (v := v) (k := 0) (fun st hst => by simpa [eighSlotOff] using hst) hv
    (Mode.needs_of (Nat.zero_le _) md) (fun _ => hw.spec) fun _ _ => trivial) (fun _ h => h)
    (fun x hx => hx) ?_
  rintro st st' - ⟨-, h0, -⟩
  obtain rfl := h0 rfl
  exact ⟨rfl, rfl⟩

omit [AddMonoid C] [Inhabited K] in
/-- A cell outside the window of a slot and the scratch cell `t[4]` keeps its value. -/
theorem read_eq_of_modifies_eighSlotFp {F' : Type*} {H : EighArenas} {n d lo k t b i : ℕ}
    {q : P} (s : EighStep F' k) (hk1 : 1 ≤ k) (hk : lo + k ≤ n)
    (hs : ∀ kp h Qp Qm Ap Am σ, s = .split kp h Qp Qm Ap Am σ → 0 < kp ∧ kp < k)
    {S S' : Store P K} (hm : Modifies (eighSlotFp H n d lo k s ++ [(t, 4, 1)]) S S')
    (hW : ¬ EighSlotWindow H n d lo k (EighChildSlot s lo) b i) (ht4 : ¬ (b = t ∧ i = 4)) :
    S'.read q b i = S.read q b i := by
  refine hm.2 q b i fun x hx => ?_
  rcases List.mem_append.mp hx with hx | hx
  · exact blockDisjoint_eighSlotFp s hk1 hk hs hW x hx
  · rw [List.mem_singleton] at hx
    subst hx
    simp only [blockDisjoint_iff]
    omega


/-- The slot of a node of depth $d$: its record and its children are written, and every cell
outside its window and the scratch cell `t[4]` is kept. -/
theorem holds_of_exec_eighSlotBody {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P)
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d D : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {par Su Sg c t lo : ℕ} {s s' : St P K C} {R₀ β : K} {y : EighNode K} (hk1 : 1 ≤ y.k)
    (hkn : lo + y.k ≤ n) (hℓ : y.ℓ = ℓ₀ + d) (hH : H.Shaped s.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (ht : t ∉ H.handles ++ [par, c])
    (hSz : ReadsIdx I.sem s.store p H.Sz (n * d + lo) y.k)
    (hA : pairLayout.Holds s.store p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A)
    (hR : s.store.read p H.Lv (2 * d) = some y.R)
    (hε : s.store.read p H.Lv (2 * d + 1) = some y.ε)
    (hpar : s.store.read p par 0 = some R₀ ∧ s.store.read p par 2 = some β)
    (hSu : 2 ≤ y.k → s.store.read p Su lo = some (I.tape .uniform (n * d + lo)) ∧
      (Su = t → lo ≠ 4))
    (hSg : 2 ≤ y.k → (∀ w < 4 * (n * n),
      s.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))) ∧ Sg ≠ t)
    (hc : s.store.read p c 0 = I.sem.lit p 1 ∧ s.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      s.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      s.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      s.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
      H.Kp c t lo).run s = some s') :
    EighSlotDone H I.sem s'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β lo y ∧
      (∀ q b i, ¬ EighSlotWindow H n d lo y.k (EighChildSlot (eighStep (eighTapeMachine I p mmR qrR)
          n F
          R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo) b i → ¬ (b = t ∧ i = 4) →
        s'.store.read q b i = s.store.read q b i) ∧
      s'.store.shape = s.store.shape ∧ s'.pos = s.pos := by
  obtain ⟨v, hvr, hv⟩ := Option.bind_eq_some_iff.mp hSz
  obtain ⟨-, o, -, hl1, -, -⟩ := id hflag
  have hlt : 2 ≤ y.k → ∀ x ∈ H.handles ++ [par, Su, Sg, c], x < s.store.size := fun hk =>
    hH.forall_lt_size ((hSg hk).1 0 (by have : 0 < n := by omega
                                        positivity)) hpar.2 ⟨lo, (hSu hk).1⟩ (hc.1.trans hl1)
  obtain ⟨hm, hdone, hp⟩ := (spec_eighSlotBody (u := fun _ => 0) (safe := fun _ _ => True) hmm
    hqr .liberal p n ℓ₀ F d D lo trivial hflag hcmp hlit htn H hk1 hkn hℓ hbufs ht
    (fun hk h => (hSu hk).2 h) (fun hk => (hSg hk).2) hlt v hv).spec.holds_of_exec
    ⟨hvr, rfl, hH, ⟨hA, hR, hε, hpar.1, hpar.2, fun hk => ⟨(hSu hk).1, (hSg hk).1⟩, hc.1, hc.2.1,
      hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩, trivial⟩ h
  exact ⟨hdone, fun q b i hW ht4 => read_eq_of_modifies_eighSlotFp _ hk1 hkn
    (fun kp h Qp Qm Ap Am σ hs => lt_of_eighStep_split hs) hm hW ht4, hm.1, hp⟩

end NLAlib
