/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.FrameRules

/-!
# The weighted kernel cost of the spectral bisection program

The weighted kernel bound of [Shah2024, Section 4] for the registered tree
`NLAlib.eighProg.compiled`: for a cost $T$ of a kernel call by its largest dimension that is
monotone and superadditive, every successful run adds at most $(\ell_0 + 1)(2F + 12)\,T(N)$ to the
weighted kernel count: per level, the nodes have sizes summing to at most $N$ (they stay packed in
$[0, N)$), each with at most $2F + 12$ kernel calls of largest dimension at most its size.

## Main results

* `NLAlib.eighProg.weight_le_of_exec_compiled`: the weighted kernel bound.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

namespace EighWeight

omit [AddMonoid C] [Inhabited K]

variable {I : Interp P ι K (OpCount P ι)} {T : ℕ → ℕ} {p : P} {b m : ℕ}

/-! Packing -/

/-- the positive entries of `g` on `[a, c)` are disjoint ranges inside `[a, c)` -/
private def Packed (g : ℕ → ℕ) (a c : ℕ) : Prop :=
  ∀ j, a ≤ j → j < c → 0 < g j → j + g j ≤ c ∧ ∀ i, j < i → i < j + g j → g i = 0

omit [DecidableEq P] in
/-- A superadditive cost vanishes at $0$. -/
private theorem eq_zero_of_superadditive (hTs : ∀ a b, T a + T b ≤ T (a + b)) : T 0 = 0 := by
  have := hTs 0 0; simp at this; omega

/-- Packed sizes on $[a, c)$ cost at most $T(c - a)$ in all, for a monotone superadditive $T$. -/
private theorem sum_le_of_packed (hT : Monotone T) (hTs : ∀ a b, T a + T b ≤ T (a + b)) {g : ℕ → ℕ}
    {c : ℕ} : ∀ a, Packed g a c → ∑ j ∈ Finset.Ico a c, T (g j) ≤ T (c - a) := by
  have hT0 := eq_zero_of_superadditive hTs
  intro a
  induction h : c - a using Nat.strong_induction_on generalizing a with
  | _ r ih =>
    intro hp
    rcases Nat.lt_or_ge a c with hac | hac
    · rcases Nat.eq_zero_or_pos (g a) with hg | hg
      · rw [Finset.sum_eq_sum_Ico_succ_bot hac, hg, hT0, zero_add]
        refine (ih (c - (a + 1)) (by omega) (a + 1) rfl fun j h1 h2 h3 =>
          hp j (by omega) h2 h3).trans (hT (by omega))
      · obtain ⟨h1, h2⟩ := hp a le_rfl hac hg
        rw [← Finset.sum_Ico_consecutive _ (show a ≤ a + g a by omega) h1,
          Finset.sum_eq_sum_Ico_succ_bot (show a < a + g a by omega)]
        have hz : ∑ j ∈ Finset.Ico (a + 1) (a + g a), T (g j) = 0 :=
          Finset.sum_eq_zero fun j hj => by
            rw [Finset.mem_Ico] at hj; rw [h2 j (by omega) (by omega), hT0]
        rw [hz, add_zero]
        have := ih (c - (a + g a)) (by omega) (a + g a) rfl fun j h1 h2 h3 => hp j (by omega) h2 h3
        calc T (g a) + ∑ j ∈ Finset.Ico (a + g a) c, T (g j) ≤ T (g a) + T (c - (a + g a)) :=
              Nat.add_le_add_left this _
          _ ≤ T (g a + (c - (a + g a))) := hTs _ _
          _ ≤ T r := hT (by omega)
    · rw [Finset.Ico_eq_empty (by omega)]; simp

/-- Packing extends by zero sizes. -/
private theorem packed_extend {g : ℕ → ℕ} {a c c' : ℕ} (h : Packed g a c) (hcc : c ≤ c')
    (hz : ∀ j, c ≤ j → j < c' → g j = 0) : Packed g a c' := by
  intro j h1 h2 h3
  rcases Nat.lt_or_ge j c with hj | hj
  · obtain ⟨h4, h5⟩ := h j h1 hj h3; exact ⟨by omega, h5⟩
  · rw [hz j hj h2] at h3; omega

/-- Packings of two adjacent ranges append. -/
private theorem packed_append {g : ℕ → ℕ} {a c e : ℕ} (h : Packed g a c)
    (h' : Packed g c e) (hce : c ≤ e) : Packed g a e := by
  intro j h1 h2 h3
  rcases Nat.lt_or_ge j c with hj | hj
  · obtain ⟨h4, h5⟩ := h j h1 hj h3; exact ⟨by omega, h5⟩
  · exact h' j hj h2 h3

/-- Packing depends only on the sizes in the range. -/
private theorem packed_congr {g g' : ℕ → ℕ} {a c : ℕ} (h : Packed g a c)
    (he : ∀ j, a ≤ j → j < c → g' j = g j) : Packed g' a c := by
  intro j h1 h2 h3
  rw [he j h1 h2] at h3 ⊢
  obtain ⟨h4, h5⟩ := h j h1 h2 h3
  exact ⟨h4, fun i hi1 hi2 => by rw [he i (by omega) (by omega)]; exact h5 i hi1 hi2⟩

/-- Zero sizes are packed. -/
private theorem packed_of_eq_zero {g : ℕ → ℕ} {a c : ℕ} (hz : ∀ j, a ≤ j → j < c → g j = 0) :
    Packed g a c := by
  intro j h1 h2 h3; rw [hz j h1 h2] at h3; omega

/-- A child of size $s$ placed at $lo$ extends a packing to $lo + s$. -/
private theorem packed_child {g g' : ℕ → ℕ} {lo s N : ℕ} (hpk : Packed g 0 lo)
    (hz : ∀ j, lo ≤ j → j < N → g j = 0) (hs : lo + s ≤ N) (hs0 : 0 < s)
    (hg' : ∀ j, g' j = if j = lo then s else g j) :
    Packed g' 0 (lo + s) ∧ ∀ j, lo + s ≤ j → j < N → g' j = 0 := by
  refine ⟨packed_append (packed_congr hpk fun j _ h2 => by rw [hg', if_neg (by omega)])
    ?_ (by omega), fun j h1 h2 => by rw [hg', if_neg (by omega)]; exact hz j (by omega) h2⟩
  intro j h1 h2 h3
  rcases Nat.lt_or_ge lo j with hj | hj
  · rw [hg', if_neg (by omega), hz j (by omega) (by omega)] at h3; omega
  · have : j = lo := by omega
    subst this
    rw [hg', if_pos rfl]
    refine ⟨le_rfl, fun i hi1 hi2 => ?_⟩
    rw [hg', if_neg (by omega)]; exact hz i (by omega) (by omega)

/-- The two children of a split of size $s$ at $lo$ extend a packing to $lo + s$. -/
private theorem packed_split {g g' : ℕ → ℕ} {lo s kp N : ℕ} (hpk : Packed g 0 lo)
    (hz : ∀ j, lo ≤ j → j < N → g j = 0) (hs : lo + s ≤ N) (hkp0 : 0 < kp) (hkp : kp < s)
    (hg' : ∀ j, g' j = if j = lo + kp then s - kp else if j = lo then kp else g j) :
    Packed g' 0 (lo + s) ∧ ∀ j, lo + s ≤ j → j < N → g' j = 0 := by
  refine ⟨packed_append (packed_congr hpk fun j _ h2 => by
      rw [hg', if_neg (by omega), if_neg (by omega)])
    ?_ (by omega), fun j h1 h2 => by
      rw [hg', if_neg (by omega), if_neg (by omega)]; exact hz j (by omega) h2⟩
  have hzero : ∀ i, lo ≤ i → i < lo + s → i ≠ lo → i ≠ lo + kp → g' i = 0 := fun i h1 h2 h3 h4 => by
    rw [hg', if_neg h4, if_neg h3]; exact hz i h1 (by omega)
  intro j h1 h2 h3
  by_cases hj1 : j = lo
  · subst hj1
    rw [hg', if_neg (by omega), if_pos rfl]
    exact ⟨by omega, fun i hi1 hi2 => hzero i (by omega) (by omega) (by omega) (by omega)⟩
  by_cases hj2 : j = lo + kp
  · subst hj2
    rw [hg', if_pos rfl]
    exact ⟨by omega, fun i hi1 hi2 => hzero i (by omega) (by omega) (by omega) (by omega)⟩
  · rw [hzero j h1 h2 hj1 hj2] at h3; omega

omit [DecidableEq P] in
/-- The value read back from an updated cell. -/
private theorem readNat_update {V : ℕ → Option K} {i : ℕ} {v : Option K} (j : ℕ) :
    readNat I p (Function.update V i v) j =
      if j = i then (v.bind (I.sem.toNat p)).getD 0 else readNat I p V j := by
  unfold readNat
  by_cases h : j = i
  · subst h; simp
  · simp [h]

omit [DecidableEq P] in
/-- An exact integer literal reads back as itself. -/
private theorem lit_bind_toNat {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {j : ℕ} (hj : j ≤ B) :
    ((I.sem.lit p (j : ℚ)).bind (I.sem.toNat p)).getD 0 = j := by
  obtain ⟨z, hz, -⟩ := hlit p j hj
  rw [hz]
  simp [IsExactIntLit.toNat_eq_of_lit_eq_some hlit htn hj hz]

/-- the invariant of the slot loop of a downward level, after the slots below `lo` -/
private def DownInv (I : Interp P ι K (OpCount P ι)) (p : P) (V₀ : ℕ → Option K) (N d lo : ℕ)
    (V : ℕ → Option K) : Prop :=
  ∃ C, lo ≤ C ∧ C ≤ N ∧ (∀ i, (i < N * (d + 1) ∨ N * (d + 1) + N ≤ i) → V i = V₀ i) ∧
    Packed (fun j => readNat I p V (N * (d + 1) + j)) 0 C ∧
    (∀ j, C ≤ j → j < N → readNat I p V (N * (d + 1) + j) = 0) ∧
    (∀ j, lo ≤ j → j < C → readNat I p V₀ (N * d + j) = 0)

omit [DecidableEq P] in
/-- One slot of a downward level keeps the invariant `DownInv`. -/
private theorem downInv_succ {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {V₀ V V' : ℕ → Option K} {N d lo : ℕ} (hNB : N ≤ B)
    (hlo : lo < N) (hpk : Packed (fun j => readNat I p V₀ (N * d + j)) 0 N)
    (hinv : DownInv I p V₀ N d lo V)
    (hQ : V' = V ∨ (2 ≤ min (readNat I p V (N * d + lo)) (N - lo) ∧
      NodeEffect I p V (N * (d + 1) + lo) (min (readNat I p V (N * d + lo)) (N - lo)) V')) :
    DownInv I p V₀ N d (lo + 1) V' := by
  obtain ⟨C, hC1, hC2, hfr, hpC, hzC, hz0⟩ := hinv
  have hD : N * (d + 1) = N * d + N := Nat.mul_succ N d
  have hgs : readNat I p V (N * d + lo) = readNat I p V₀ (N * d + lo) := by
    unfold readNat; rw [hfr _ (Or.inl (by omega))]
  rw [hgs] at hQ
  set s := readNat I p V₀ (N * d + lo) with hs
  -- the slot's range at depth `d`
  have hsr : 0 < s → C = lo ∧ lo + s ≤ N ∧ ∀ j, lo < j → j < lo + s →
      readNat I p V₀ (N * d + j) = 0 := by
    intro hs0
    have hCl : C = lo := by
      rcases Nat.lt_or_ge lo C with h | h
      · have := hz0 lo le_rfl h; omega
      · omega
    obtain ⟨h1, h2⟩ := hpk lo (Nat.zero_le _) hlo hs0
    exact ⟨hCl, h1, h2⟩
  rcases hQ with rfl | ⟨hk2, kp, hkp, hRN⟩
  · -- no write
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · rcases Nat.lt_or_ge lo C with h | h
      · exact ⟨C, h, hC2, hfr, hpC, hzC, fun j h1 h2 => hz0 j (by omega) h2⟩
      · refine ⟨lo + 1, le_rfl, by omega, hfr, packed_extend hpC (by omega) fun j h1 h2 =>
          hzC j h1 (by omega), fun j h1 h2 => hzC j (by omega) h2, fun j h1 h2 => by omega⟩
    · obtain ⟨hCl, hsN, hsz⟩ := hsr hs0
      subst hCl
      refine ⟨C + s, by omega, hsN, hfr, packed_extend hpC (by omega) fun j h1 h2 =>
          hzC j h1 (by omega), fun j h1 h2 => hzC j (by omega) h2,
          fun j h1 h2 => hsz j (by omega) h2⟩
  · have hs0 : 0 < s := by omega
    obtain ⟨hCl, hsN, hsz⟩ := hsr hs0
    subst hCl
    have hmin : min s (N - C) = s := by omega
    rw [hmin] at hkp hRN hk2
    have hlit' : ∀ j ≤ N, ((I.sem.lit p (j : ℚ)).bind (I.sem.toNat p)).getD 0 = j :=
      fun j hj => lit_bind_toNat hlit htn (hj.trans hNB)
    rcases hRN with ⟨-, rfl⟩ | ⟨hkp0, hkps, rfl⟩
    · obtain ⟨h1, h2⟩ := packed_child (g := fun j => readNat I p V (N * (d + 1) + j))
        (g' := fun j => readNat I p (Function.update V (N * (d + 1) + C) (I.sem.lit p (s : ℚ)))
          (N * (d + 1) + j)) hpC hzC hsN hs0 fun j => by
          simp only [readNat_update, hlit' s (by omega)]
          by_cases hj : j = C <;> simp [hj]
      refine ⟨C + s, by omega, hsN, fun i hi => ?_, h1, h2, fun j h1 h2 => hsz j (by omega) h2⟩
      rw [Function.update_of_ne (by omega)]; exact hfr i hi
    · obtain ⟨h1, h2⟩ := packed_split (g := fun j => readNat I p V (N * (d + 1) + j))
        (g' := fun j => readNat I p (Function.update (Function.update V (N * (d + 1) + C)
          (I.sem.lit p (kp : ℚ))) (N * (d + 1) + C + kp) (I.sem.lit p ((s - kp : ℕ) : ℚ)))
          (N * (d + 1) + j)) hpC hzC hsN hkp0 hkps fun j => by
          simp only [readNat_update, hlit' kp (by omega), hlit' (s - kp) (by omega)]
          by_cases hj : j = C + kp
          · simp [hj, Nat.add_assoc]
          · by_cases hj' : j = C
            · simp [hj']
            · simp [hj, hj', show ¬ (N * (d + 1) + j = N * (d + 1) + C + kp) by omega]
      refine ⟨C + s, by omega, hsN, fun i hi => ?_, h1, h2, fun j h1 h2 => hsz j (by omega) h2⟩
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hfr i hi

/-- The slot loop of a downward level: the sizes of depth $d$ cost at most $(2F + 9)T(N)$ in all. -/
private theorem triple_downLoop {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {mm qr : ι} {n L F d : IExp ℕ}
    {par Lv Su Sg Ma Ua Qa Ea Kd Kp t : ℕ} {one two half negone sqh : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hUa : Ua ≠ b)
    (hQa : Qa ≠ b) (hEa : Ea ≠ b) (hKd : Kd ≠ b) (hKp : Kp ≠ b) (ht : t ≠ b) (hNB : n.eval ≤ B)
    (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : Packed (fun j => readNat I p V₀ (n.eval * d.eval + j)) 0 n.eval)
    (hz : ∀ j, j < n.eval → readNat I p V₀ (n.eval * (d.eval + 1) + j) = 0) :
    Triple I T p b n.eval V₀ (.loop n fun lo => (bindIdx p ⟨b, eighSlotOff n d (IExp.var lo)⟩
      (n - IExp.var lo) fun k => downSlot p mm qr n L F d par Lv Su Sg Ma Ua Qa Ea b Kd Kp t
        one two half negone sqh lo k).run) (2 * F.eval + 9)
      (DownInv I p V₀ n.eval d.eval n.eval) := by
  intro hT hch st st' hb hV hex
  set N := n.eval
  set c := 2 * F.eval + 9
  set g₀ : ℕ → ℕ := fun j => readNat I p V₀ (N * d.eval + j)
  have := forall_of_exec_loop_eq_some I (fun lo s => b < s.store.size ∧
      Finsupp.weight (OpKind.kernelWeight T) s.cnt ≤ Finsupp.weight (OpKind.kernelWeight T) st.cnt +
        c * ∑ j ∈ Finset.range lo, T (g₀ j) ∧ DownInv I p V₀ N d.eval lo (cells s.store p b))
    ⟨hb, by simp, 0, le_rfl, Nat.zero_le _, fun i _ => by rw [hV],
      fun j _ h => absurd h (Nat.not_lt_zero _), fun j _ h => by rw [hV]; exact hz j h,
      fun j h1 h2 => absurd h2 (by omega)⟩
    (fun lo hlo s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      have hslot : Triple I T p b
          (min (readNat I p (cells s₁.store p b) (N * d.eval + lo)) (N - lo))
          (cells s₁.store p b) ((bindIdx p ⟨b, eighSlotOff n d (IExp.var lo)⟩
          (n - IExp.var lo) fun k => downSlot p mm qr n L F d par Lv Su Sg Ma Ua Qa Ea b Kd Kp
            t one two half negone sqh lo k).run) (c + 0)
          (fun V => V = cells s₁.store p b ∨
            (2 ≤ min (readNat I p (cells s₁.store p b) (N * d.eval + lo)) (N - lo) ∧
            NodeEffect I p (cells s₁.store p b) (N * (d.eval + 1) + lo)
              (min (readNat I p (cells s₁.store p b) (N * d.eval + lo)) (N - lo)) V)) := by
        apply triple_run
        apply triple_runCont_bindIdx_read _ fun V h => triple_cont_skip h
        have e1 : (eighSlotOff n d (IExp.var lo)).eval = N * d.eval + lo := by
          simp [eval_eighSlotOff, N]
        have e2 : (eighSlotOff n (d + 1) (IExp.var lo)).eval = N * (d.eval + 1) + lo := by
          simp [eval_eighSlotOff, N]
        have e3 : (n - IExp.var lo).eval = N - lo := by simp [N]
        rw [e1, e3]
        have := triple_downSlot (I := I) (T := T) (p := p) (b := b) (V₀ := cells s₁.store p b)
          (mm := mm) (qr := qr) (n := n) (L := L) (F := F) (d := d) (par := par) (Lv := Lv)
          (Su := Su) (Sg := Sg) (one := one) (two := two) (half := half) (negone := negone)
          (sqh := sqh) hMa hUa hQa hEa hKd hKp ht lo
          (min (readNat I p (cells s₁.store p b) (N * d.eval + lo)) (N - lo)) le_rfl
        rw [e2] at this
        exact this
      obtain ⟨a1, a2⟩ := hslot hT hch s₁ s₂ h1 rfl hs
      rw [Nat.add_zero] at a1
      have h3' := h3
      obtain ⟨C, -, -, hfr, -⟩ := h3'
      have hg : readNat I p (cells s₁.store p b) (N * d.eval + lo) = g₀ lo := by
        simp only [g₀, readNat]; rw [hfr _ (Or.inl (by rw [Nat.mul_succ]; omega))]
      refine ⟨by rw [size_eq_of_exec_eq_some hs]; exact h1, ?_,
        downInv_succ hlit htn hNB hlo hpk h3 a2⟩
      rw [Finset.sum_range_succ, Nat.mul_add]
      have : T (min (readNat I p (cells s₁.store p b) (N * d.eval + lo)) (N - lo)) ≤ T (g₀ lo) :=
        hT (by rw [hg]; exact min_le_left _ _)
      have := Nat.mul_le_mul_left c this
      omega) hex
  obtain ⟨-, h2, h3⟩ := this
  refine ⟨h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left c ?_) _), h3⟩
  have := sum_le_of_packed hT hTs 0 hpk
  rwa [← Finset.range_eq_Ico, Nat.sub_zero] at this

/-- A downward level: at most $(2F + 9)T(N)$, and the sizes of depth $d + 1$ packed. -/
private theorem triple_eighDownLevel {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {mm qr : ι} {n L F d : IExp ℕ}
    {par Lv Su Sg Ma Ua Qa Ea Kd Kp : ℕ} {one two half negone sqh : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hLv : Lv ≠ b) (hSu : Su ≠ b) (hSg : Sg ≠ b) (hMa : Ma ≠ b)
    (hUa : Ua ≠ b) (hQa : Qa ≠ b) (hEa : Ea ≠ b) (hKd : Kd ≠ b) (hKp : Kp ≠ b)
    (hNB : n.eval ≤ B) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : Packed (fun j => readNat I p V₀ (n.eval * d.eval + j)) 0 n.eval)
    (hz : ∀ j, j < n.eval → readNat I p V₀ (n.eval * (d.eval + 1) + j) = 0) :
    Triple I T p b n.eval V₀ (eighDownLevel p mm qr n L F d par Lv Su Sg Ma Ua Qa Ea b Kd Kp one
      two half negone sqh).run (2 * F.eval + 9) (DownInv I p V₀ n.eval d.eval n.eval) := by
  unfold eighDownLevel
  apply triple_run
  apply triple_mono (hm := le_rfl) (hQ := fun _ h => h)
  · apply triple_runCont_scope
    · apply triple_run
      frame_triple
      exact triple_runCont_forRange
        (triple_downLoop hlit htn hMa hUa hQa hEa hKd hKp (by omega) hNB hTs
        hpk hz) fun V h => triple_cont_skip h
    · intro V h; exact triple_cont_skip h
  · simp only [Nat.add_zero, Nat.zero_add]
    omega

/-- the body of a slot of an upward level, at the size `k` it reads -/
private def upSlot (p : P) (mm : ι) (n d : IExp ℕ) (Ua Qa Ea Kd Kp t : ℕ) (lo k : ℕ) :
    Builder P ι ℕ ℕ Unit :=
  eighWhen (IExp.var k) <| bindIdx p ⟨Kd, eighSlotOff n d (IExp.var lo)⟩ 4 fun c => do
    eighWhen (eighEqInd (IExp.var c) 2) do
      zcopy p (IExp.var k) (IExp.var k) Ua (eighBlockOff n (d + 1) (IExp.var lo)) Ua
        (eighBlockOff n d (IExp.var lo))
      forRange (IExp.var k) fun i => ins (.bin p .add ⟨Ea, eighSlotOff n d (IExp.var lo) + .var i⟩
        ⟨Ea, eighSlotOff n (d + 1) (IExp.var lo) + .var i⟩ ⟨t, 0⟩)
    eighWhen (eighEqInd (IExp.var c) 3) do
      zcopy p (IExp.var k) (IExp.var k) Ua (eighBlockOff n (d + 1) (IExp.var lo)) Ua
        (eighBlockOff n d (IExp.var lo))
      forRange (IExp.var k) fun i => ins (.bin p .add ⟨Ea, eighSlotOff n d (IExp.var lo) + .var i⟩
        ⟨Ea, eighSlotOff n (d + 1) (IExp.var lo) + .var i⟩ ⟨t, 1⟩)
    eighWhen (eighEqInd (IExp.var c) 4) <|
      bindIdx p ⟨Kp, eighSlotOff n d (IExp.var lo)⟩ (IExp.var k) fun kp => do
        let qo := eighBlockOff n d (IExp.var lo)
        stmt (.kcall mm p [IExp.var k, IExp.var kp, IExp.var kp]
          [(Qa, qo), (Ua, eighBlockOff n (d + 1) (IExp.var lo))]
          [(Ua, eighBlockOff n d (IExp.var lo))])
        stmt (.kcall mm p [IExp.var k, IExp.var k - IExp.var kp, IExp.var k - IExp.var kp]
          [(Qa, qo + 2 * (IExp.var k * IExp.var kp)),
            (Ua, eighBlockOff n (d + 1) (IExp.var lo + IExp.var kp))]
          [(Ua, eighBlockOff n d (IExp.var lo) + 2 * (IExp.var k * IExp.var kp))])
        forRange (IExp.var kp) fun j => ins (.bin p .add
          ⟨Ea, eighSlotOff n d (IExp.var lo) + .var j⟩
          ⟨Ea, eighSlotOff n (d + 1) (IExp.var lo) + .var j⟩ ⟨t, 0⟩)
        forRange (IExp.var k - IExp.var kp) fun j => ins (.bin p .sub
          ⟨Ea, eighSlotOff n d (IExp.var lo) + IExp.var kp + .var j⟩
          ⟨Ea, eighSlotOff n (d + 1) (IExp.var lo) + IExp.var kp + .var j⟩ ⟨t, 0⟩)

/-- A slot of an upward level: at most two kernel calls of dimension at most its size. -/
private theorem builderFrame_upSlot {mm : ι} {n d : IExp ℕ} {Ua Qa Ea Kd Kp t : ℕ} (hUa : Ua ≠ b)
    (hEa : Ea ≠ b) (lo k : ℕ) :
    BuilderFrame I T p b k (upSlot p mm n d Ua Qa Ea Kd Kp t lo k) 2 := by
  unfold upSlot
  apply builderFrame_mono
  · dsimp only
    frame_builder
  · simp

/-- The slot loop of an upward level: at most $2T(N)$. -/
private theorem triple_upLoop {mm : ι} {n d : IExp ℕ} {Ua Qa Ea Kd Kp t : ℕ} {V₀ : ℕ → Option K}
    (hUa : Ua ≠ b) (hEa : Ea ≠ b) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : Packed (fun j => readNat I p V₀ (n.eval * d.eval + j)) 0 n.eval) :
    Triple I T p b n.eval V₀ (.loop n fun lo => (bindIdx p ⟨b, eighSlotOff n d (IExp.var lo)⟩
      (n - IExp.var lo) fun k => upSlot p mm n d Ua Qa Ea Kd Kp t lo k).run) 2 (· = V₀) := by
  intro hT hch st st' hb hV hex
  set N := n.eval
  set g₀ : ℕ → ℕ := fun j => readNat I p V₀ (N * d.eval + j)
  have := forall_of_exec_loop_eq_some I (fun lo s => b < s.store.size ∧
      Finsupp.weight (OpKind.kernelWeight T) s.cnt ≤ Finsupp.weight (OpKind.kernelWeight T) st.cnt +
        2 * ∑ j ∈ Finset.range lo, T (g₀ j) ∧ cells s.store p b = V₀)
    ⟨hb, by simp, hV⟩
    (fun lo hlo s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      have hslot : Triple I T p b (min (readNat I p V₀ (N * d.eval + lo)) (N - lo))
          V₀ ((bindIdx p ⟨b, eighSlotOff n d (IExp.var lo)⟩
          (n - IExp.var lo) fun k => upSlot p mm n d Ua Qa Ea Kd Kp t lo k).run) (2 + 0)
          (· = V₀) := by
        apply triple_run
        apply triple_runCont_bindIdx_read _ fun V h => triple_cont_skip h
        have e1 : (eighSlotOff n d (IExp.var lo)).eval = N * d.eval + lo := by
          simp [eval_eighSlotOff, N]
        have e3 : (n - IExp.var lo).eval = N - lo := by simp [N]
        rw [e1, e3]
        exact frame_run (builderFrame_upSlot hUa hEa lo _) V₀
      obtain ⟨a1, a2⟩ := hslot hT hch s₁ s₂ h1 h3 hs
      rw [Nat.add_zero] at a1
      refine ⟨by rw [size_eq_of_exec_eq_some hs]; exact h1, ?_, a2⟩
      rw [Finset.sum_range_succ, Nat.mul_add]
      have : T (min (readNat I p V₀ (N * d.eval + lo)) (N - lo)) ≤ T (g₀ lo) :=
        hT (min_le_left _ _)
      omega) hex
  obtain ⟨-, h2, h3⟩ := this
  refine ⟨h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 ?_) _), h3⟩
  have := sum_le_of_packed hT hTs 0 hpk
  rwa [← Finset.range_eq_Ico, Nat.sub_zero] at this

/-- An upward level: at most $2T(N)$, the tracked buffer kept. -/
private theorem triple_eighUpLevel {mm : ι} {n d : IExp ℕ} {Lv Ua Qa Ea Kd Kp : ℕ} {two : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hUa : Ua ≠ b) (hEa : Ea ≠ b) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : Packed (fun j => readNat I p V₀ (n.eval * d.eval + j)) 0 n.eval) :
    Triple I T p b n.eval V₀ (eighUpLevel p mm n d Lv Ua Qa Ea b Kd Kp two).run 2 (· = V₀) := by
  unfold eighUpLevel
  apply triple_run
  apply triple_mono (hm := le_rfl) (hQ := fun _ h => h)
  · apply triple_runCont_scope
    · apply triple_run
      frame_triple
      exact triple_runCont_forRange (triple_upLoop hUa hEa hTs hpk) fun V h => triple_cont_skip h
    · intro V h; exact triple_cont_skip h
  · simp only [Nat.add_zero, Nat.zero_add]
    omega

/-- The bottom level keeps the tracked buffer, at cost $0$. -/
private theorem builderFrame_eighBottomLevel {n D : IExp ℕ} {Ua Ea : ℕ} (hUa : Ua ≠ b)
    (hEa : Ea ≠ b) :
    BuilderFrame I T p b m (eighBottomLevel p n D Ua Ea b) 0 := by
  unfold eighBottomLevel; frame_zero

/-- The loop that zeroes the size arena. -/
private theorem triple_zeroLoop {M : IExp ℕ} {V₀ : ℕ → Option K} :
    Triple I T p b m V₀ (.loop M fun w => (ins (.litIdx p ⟨b, IExp.var w⟩ 0)).run) 0
      (fun V => ∀ w, V w = if w < M.eval then I.sem.lit p 0 else V₀ w) := by
  intro hT hch st st' hb hV hex
  have := forall_of_exec_loop_eq_some I (fun i s => b < s.store.size ∧
      Finsupp.weight (OpKind.kernelWeight T) s.cnt ≤ Finsupp.weight (OpKind.kernelWeight T) st.cnt ∧
      ∀ w, cells s.store p b w = if w < i then I.sem.lit p 0 else V₀ w)
    ⟨hb, le_rfl, fun w => by simp [hV]⟩
    (fun i _ s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      have hl : Triple I T p b m (cells s₁.store p b)
          (.seq (.instr (.litIdx p ⟨b, IExp.var i⟩ 0)) .skip) (0 + 0)
          (· = Function.update (cells s₁.store p b) (IExp.var i).eval
            (I.sem.lit p ((0 : IExp ℕ).eval : ℚ))) :=
        triple_seq triple_litIdx fun V₁ h => triple_skip h
      obtain ⟨a1, a2⟩ := hl hT hch s₁ s₂ h1 rfl hs
      refine ⟨by rw [size_eq_of_exec_eq_some hs]; exact h1, by omega, fun w => ?_⟩
      rw [a2]
      by_cases hw : w = i
      · subst hw; simp
      · rw [Function.update_of_ne (by simpa using hw), h3 w]
        by_cases hwi : w < i
        · simp [hwi, show w < i + 1 by omega]
        · simp [hwi, show ¬ w < i + 1 by omega]) hex
  obtain ⟨-, h2, h3⟩ := this
  exact ⟨by omega, h3⟩

/-- The downward pass: at most $(\ell_0 + 1)(2F + 9)T(N)$, the sizes of every depth packed. -/
private theorem triple_downPass {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {mm qr : ι} {n L F : IExp ℕ}
    {par Lv Su Sg Ma Ua Qa Ea Kd Kp : ℕ} {one two half negone sqh : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hLv : Lv ≠ b) (hSu : Su ≠ b) (hSg : Sg ≠ b) (hMa : Ma ≠ b)
    (hUa : Ua ≠ b) (hQa : Qa ≠ b) (hEa : Ea ≠ b) (hKd : Kd ≠ b) (hKp : Kp ≠ b)
    (hNB : n.eval ≤ B) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : Packed (fun j => readNat I p V₀ (n.eval * 0 + j)) 0 n.eval)
    (hz : ∀ e, 0 < e → e ≤ L.eval + 1 → ∀ j, j < n.eval → readNat I p V₀ (n.eval * e + j) = 0) :
    Triple I T p b n.eval V₀ (.loop (L + 1) fun d => (eighDownLevel p mm qr n L F (IExp.var d)
      par Lv Su Sg Ma Ua Qa Ea b Kd Kp one two half negone sqh).run)
      ((L.eval + 1) * (2 * F.eval + 9))
      (fun V => ∀ e ≤ L.eval + 1, Packed (fun j => readNat I p V (n.eval * e + j)) 0 n.eval) := by
  intro hT hch st st' hb hV hex
  have := forall_of_exec_loop_eq_some I (fun d s => b < s.store.size ∧
      Finsupp.weight (OpKind.kernelWeight T) s.cnt ≤
        Finsupp.weight (OpKind.kernelWeight T) st.cnt + d * ((2 * F.eval + 9) * T n.eval) ∧
      (∀ e ≤ d, Packed (fun j => readNat I p (cells s.store p b) (n.eval * e + j)) 0 n.eval) ∧
      (∀ e, d < e → e ≤ L.eval + 1 → ∀ j, j < n.eval →
        readNat I p (cells s.store p b) (n.eval * e + j) = 0))
    ⟨hb, by simp, fun e he => by
      rw [Nat.le_zero.mp he, hV]; exact hpk, fun e h1 h2 => by rw [hV]; exact hz e h1 h2⟩
    (fun d hd s₁ s₂ ⟨h1, h2, h3, h4⟩ hs => by
      have hdn := triple_eighDownLevel (I := I) (T := T) (p := p) (b := b) (mm := mm) (qr := qr)
        (n := n)
        (L := L) (F := F) (d := IExp.var d) (par := par) (one := one) (two := two) (half := half)
        (negone := negone) (sqh := sqh) hlit htn hLv hSu hSg hMa hUa hQa hEa hKd hKp hNB hTs
        (h3 d le_rfl) (h4 (d + 1) (by omega) (by simpa using hd))
      obtain ⟨a1, ⟨C, hC1, hC2, hfr, hpC, -, -⟩⟩ := hdn hT hch s₁ s₂ h1 rfl hs
      simp only [IExp.eval_var] at hfr hpC
      have hCN : C = n.eval := by omega
      rw [hCN] at hpC
      refine ⟨by rw [size_eq_of_exec_eq_some hs]; exact h1, by rw [Nat.succ_mul]; omega,
        fun e he => ?_,
        fun e h5 h6 j hj => ?_⟩
      · rcases Nat.lt_or_ge d e with hde | hde
        · have : e = d + 1 := by omega
          subst this; exact hpC
        · refine packed_congr (h3 e hde) fun j _ hj => ?_
          have : n.eval * e ≤ n.eval * d := Nat.mul_le_mul_left n.eval hde
          simp only [readNat]; rw [hfr _ (Or.inl (by rw [Nat.mul_succ]; omega))]
      · have : n.eval * (d + 2) ≤ n.eval * e := Nat.mul_le_mul_left n.eval (by omega)
        have h7 := h4 e (by omega) h6 j hj
        have e1 : n.eval * (d + 2) = n.eval * d + n.eval + n.eval := by ring
        have e2 : n.eval * (d + 1) = n.eval * d + n.eval := by ring
        simp only [readNat] at h7 ⊢; rw [hfr _ (Or.inr (by omega))]
        exact h7) hex
  obtain ⟨-, h2, h3, -⟩ := this
  refine ⟨?_, h3⟩
  simp only [IExp.eval_add, IExp.eval_ofNat] at h2
  rw [Nat.mul_assoc]; exact h2

/-- The upward pass: at most $2(\ell_0 + 1)T(N)$. -/
private theorem triple_upPass {mm : ι} {n L : IExp ℕ} {Lv Ua Qa Ea Kd Kp : ℕ} {two : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hUa : Ua ≠ b) (hEa : Ea ≠ b) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ∀ e ≤ L.eval, Packed (fun j => readNat I p V₀ (n.eval * e + j)) 0 n.eval) :
    Triple I T p b n.eval V₀ (.loop (L + 1) fun d' => (eighUpLevel p mm n (L - IExp.var d') Lv Ua
      Qa Ea b Kd Kp two).run) ((L.eval + 1) * 2) (· = V₀) := by
  intro hT hch st st' hb hV hex
  have := forall_of_exec_loop_eq_some I (fun d s => b < s.store.size ∧
      Finsupp.weight (OpKind.kernelWeight T) s.cnt ≤
        Finsupp.weight (OpKind.kernelWeight T) st.cnt + d * (2 * T n.eval) ∧
      cells s.store p b = V₀)
    ⟨hb, by simp, hV⟩
    (fun d hd s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      have hup := triple_eighUpLevel (I := I) (T := T) (p := p) (b := b) (mm := mm) (n := n)
        (d := L - IExp.var d) (Lv := Lv) (Qa := Qa) (Kd := Kd) (Kp := Kp) (two := two) hUa hEa hTs
        (hpk (L - IExp.var d).eval (by simp))
      obtain ⟨a1, a2⟩ := hup hT hch s₁ s₂ h1 h3 hs
      exact ⟨by rw [size_eq_of_exec_eq_some hs]; exact h1, by rw [Nat.succ_mul]; omega, a2⟩) hex
  obtain ⟨-, h2, h3⟩ := this
  refine ⟨?_, h3⟩
  simp only [IExp.eval_add, IExp.eval_ofNat] at h2
  rw [Nat.mul_assoc]; exact h2

/-- a cost bound for a run before the tracked buffer is allocated, `j` allocations ahead -/
private def PreTriple (I : Interp P ι K (OpCount P ι)) (T : ℕ → ℕ) (b m j : ℕ) (s : Stmt P ι ℕ ℕ)
    (c : ℕ) : Prop :=
  Monotone T → (IsUnitCharge I) → ∀ st st' : St P K (OpCount P ι),
    st.store.size + j = b → exec I s st = some st' →
    Finsupp.weight (OpKind.kernelWeight T) st'.cnt ≤
      Finsupp.weight (OpKind.kernelWeight T) st.cnt + c * T m

/-- An allocation before the tracked buffer. -/
private theorem preTriple_alloc_succ {j : ℕ} {q : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit}
    {k : Unit → Stmt P ι ℕ ℕ} {c : ℕ}
    (h : ∀ h, h + (j + 1) = b → PreTriple I T b m j (runCont (f h) k) c) :
    PreTriple I T b m (j + 1) (runCont (alloc q len >>= f) k) c := by
  intro hT hch st st' hb hex
  change exec I (.alloc q len fun h => runCont (f h) k) st = some st' at hex
  rw [exec_alloc] at hex
  obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp hex
  have := h st.store.size hb hT hch _ st₂ (by simp only [Array.size_push]; omega) h₂
  exact this

/-- The allocation of the tracked buffer, which starts empty. -/
private theorem preTriple_alloc_zero {q : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit}
    {k : Unit → Stmt P ι ℕ ℕ} {c : ℕ} {Q : (ℕ → Option K) → Prop}
    (h : Triple I T p b m (fun _ => none) (runCont (f b) k) c Q) :
    PreTriple I T b m 0 (runCont (alloc q len >>= f) k) c := by
  intro hT hch st st' hb hex
  change exec I (.alloc q len fun h => runCont (f h) k) st = some st' at hex
  rw [exec_alloc] at hex
  obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp hex
  rw [Nat.add_zero] at hb
  subst hb
  have := (h hT hch _ st₂ (by simp) (by
    funext i; simp only [cells]; rw [Store.read_push_size]
    rw [Array.getElem?_replicate]; split_ifs <;> rfl) h₂).1
  exact this

/-- A scope before the tracked buffer is allocated. -/
private theorem preTriple_scope {j : ℕ} {x : Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : PreTriple I T b m j (runCont x fun _ => .skip) c) :
    PreTriple I T b m j (scope x).run c := by
  intro hT hch st st' hb hex
  change exec I (.seq (runCont x fun _ => .skip) .skip) st = some st' at hex
  rw [exec_seq_skip] at hex
  exact h hT hch st st' hb hex

omit [DecidableEq P] in
/-- The size arena after its initialization: the root of size $N$ at depth $0$, no node below. -/
private theorem packed_init {dec : P → K → ℝ} (N ℓ₀ : ℕ) (hlit : IsExactIntLit dec I.sem (N + 4))
    (htn : IsExactToNat dec I.sem) {V₀ V₁ : ℕ → Option K}
    (h₁ : ∀ w, V₁ w = if w < N * (ℓ₀ + 1 + 1) + 1 then I.sem.lit p 0 else V₀ w) :
    Packed (fun j => readNat I p (Function.update V₁ 0 (I.sem.lit p (N : ℚ))) (N * 0 + j)) 0 N ∧
      ∀ e, 0 < e → e ≤ ℓ₀ + 1 → ∀ j, j < N →
        readNat I p (Function.update V₁ 0 (I.sem.lit p (N : ℚ))) (N * e + j) = 0 := by
  have hz : ∀ i, i ≠ 0 → i < N * (ℓ₀ + 1 + 1) + 1 →
      readNat I p (Function.update V₁ 0 (I.sem.lit p (N : ℚ))) i = 0 := by
    intro i hi hiM
    rw [readNat_update, if_neg hi]
    unfold readNat; rw [h₁, if_pos hiM]
    exact_mod_cast lit_bind_toNat (j := 0) hlit htn (Nat.zero_le _)
  have hbig : ∀ e ≤ ℓ₀ + 1, ∀ j < N, N * e + j < N * (ℓ₀ + 1 + 1) + 1 := by
    intro e he j hj
    have : N * e ≤ N * (ℓ₀ + 1) := Nat.mul_le_mul_left N he
    have : N * (ℓ₀ + 1 + 1) = N * (ℓ₀ + 1) + N := Nat.mul_succ _ _
    omega
  have hf0 : readNat I p (Function.update V₁ 0 (I.sem.lit p (N : ℚ))) 0 = N := by
    rw [readNat_update, if_pos rfl]; exact lit_bind_toNat hlit htn (by omega)
  have hb0 : ∀ j < N, j < N * (ℓ₀ + 1 + 1) + 1 := fun j hj => by simpa using hbig 0 (by omega) j hj
  refine ⟨fun j _ hj hpos => ?_, fun e he0 he j hj => hz _ ?_ (hbig e he j hj)⟩
  · dsimp only at hpos ⊢
    rw [Nat.mul_zero, Nat.zero_add] at hpos ⊢
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hf0]
      refine ⟨by omega, fun i hi1 hi2 => ?_⟩
      rw [Nat.zero_add]
      exact hz i (by omega) (hb0 i (by omega))
    · rw [hz j (by omega) (hb0 j hj)] at hpos
      omega
  · have : N * e ≥ N := Nat.le_mul_of_pos_right N he0
    omega

/-- The end of the program, from the bottom level on: the upward pass and the copies of the
outputs, when the size cells of every depth are packed. -/
private theorem triple_upTail {mm : ι} (N ℓ₀ : ℕ) {c Lv Ua Qa Ea Kd Kp : ℕ} {V₂ : ℕ → Option K}
    (hTs : ∀ a b, T a + T b ≤ T (a + b)) (hb5 : 5 ≤ b) (hUa : Ua ≠ b) (hEa : Ea ≠ b)
    (h₂ : ∀ e ≤ ℓ₀ + 1, Packed (fun j => readNat I p V₂ (N * e + j)) 0 N) :
    Triple I T p b N V₂ (runCont (do
        eighBottomLevel p (IExp.const N) (IExp.const ℓ₀ + 1) Ua Ea b
        forRange (IExp.const ℓ₀ + 1) fun d' =>
          eighUpLevel p mm (IExp.const N) (IExp.const ℓ₀ - IExp.var d') Lv Ua Qa Ea b Kd Kp ⟨c, 1⟩
        zcopy p (IExp.const N) (IExp.const N) Ua 0 2 0
        forRange (IExp.const N) fun i => ins (.copy p ⟨3, IExp.var i⟩ ⟨Ea, IExp.var i⟩))
      fun _ => .skip) ((ℓ₀ + 1) * 2) fun _ => True := by
  apply triple_mono (hm := le_rfl) (hQ := fun _ _ => trivial)
  · apply triple_runCont_of_builderFrame (builderFrame_eighBottomLevel hUa hEa)
    · apply triple_runCont_bind
      apply triple_runCont_forRange (triple_upPass hUa hEa hTs fun e he =>
        h₂ e (by simp at he ⊢; omega))
      · intro V₃ h₃
        frame_triple
        exact triple_cont_skip (Q := fun _ => True) trivial
  · simp only [IExp.eval_const, Nat.zero_add, Nat.add_zero]
    exact le_rfl

/-- The program after the size arena is zeroed: the size of the root, the copies of the input,
the downward pass and `triple_upTail`. -/
private theorem triple_downTail {dec : P → K → ℝ} {mm qr : ι} (N ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem)
    (hTs : ∀ a b, T a + T b ≤ T (a + b)) (hb5 : 5 ≤ b) {c Ma Ua Qa Ea Kd Kp Lv Su Sg : ℕ}
    (hMa : Ma < b) (hUa : Ua < b) (hQa : Qa < b) (hEa : Ea < b) (hKd : b < Kd)
    (hKp : b < Kp) (hLv : b < Lv) (hSu : b < Su) (hSg : b < Sg) {V₁ : ℕ → Option K}
    (h₁ : ∀ w, V₁ w = if w < N * (ℓ₀ + 1 + 1) + 1 then I.sem.lit p 0 else none) :
    Triple I T p b N V₁ (runCont (do
        ins (.litIdx p ⟨b, 0⟩ (IExp.const N))
        zcopy p (IExp.const N) (IExp.const N) 0 0 Ma 0
        ins (.copy p ⟨Lv, 0⟩ ⟨1, 0⟩)
        ins (.copy p ⟨Lv, 1⟩ ⟨1, 1⟩)
        forRange (IExp.const ℓ₀ + 1) fun d =>
          eighDownLevel p mm qr (IExp.const N) (IExp.const ℓ₀) (IExp.const F) (IExp.var d) 1 Lv Su
            Sg Ma Ua Qa Ea b Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩
        eighBottomLevel p (IExp.const N) (IExp.const ℓ₀ + 1) Ua Ea b
        forRange (IExp.const ℓ₀ + 1) fun d' =>
          eighUpLevel p mm (IExp.const N) (IExp.const ℓ₀ - IExp.var d') Lv Ua Qa Ea b Kd Kp ⟨c, 1⟩
        zcopy p (IExp.const N) (IExp.const N) Ua 0 2 0
        forRange (IExp.const N) fun i => ins (.copy p ⟨3, IExp.var i⟩ ⟨Ea, IExp.var i⟩))
      fun _ => .skip) ((ℓ₀ + 1) * (2 * F + 9) + (ℓ₀ + 1) * 2) fun _ => True := by
  apply triple_mono (hm := le_rfl) (hQ := fun _ _ => trivial)
  · apply triple_runCont_bind
    apply triple_runCont_litIdx
    frame_triple
    · obtain ⟨hpk, hz⟩ := packed_init (I := I) (p := p) N ℓ₀ hlit htn (V₀ := fun _ => none)
        (V₁ := V₁) h₁
      apply triple_runCont_bind
      apply triple_runCont_forRange (triple_downPass hlit htn (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp) hTs
        (by simpa using hpk) (by simpa using hz))
      · intro V₂ h₂
        exact triple_upTail N ℓ₀ hTs hb5 (by omega) (by omega) h₂
  · simp only [IExp.eval_const, Nat.zero_add]
    exact le_rfl

/-- The weighted kernel count of a run of `NLAlib.eighProg`, five allocations before the size
arena. -/
private theorem preTriple_eighProg {dec : P → K → ℝ} {mm qr : ι} (N ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem)
    (hTs : ∀ a b, T a + T b ≤ T (a + b)) (hb5 : 5 ≤ b) :
    PreTriple I T b N 5 (eighProg p mm qr (.const N) (.const ℓ₀) (.const F) 0 1 2 3).run
      ((ℓ₀ + 1) * (2 * F + 9) + (ℓ₀ + 1) * 2) := by
  unfold eighProg
  apply preTriple_scope
  dsimp only
  apply preTriple_alloc_succ; intro hc hhc
  apply preTriple_alloc_succ; intro hMa hhMa
  apply preTriple_alloc_succ; intro hUa hhUa
  apply preTriple_alloc_succ; intro hQa hhQa
  apply preTriple_alloc_succ; intro hEa hhEa
  apply preTriple_alloc_zero (p := p) (Q := fun _ => True)
  apply triple_mono (hm := le_rfl) (hQ := fun _ _ => trivial)
  · frame_triple
    apply triple_runCont_bind
    apply triple_runCont_forRange triple_zeroLoop
    · intro V₁ h₁
      exact triple_downTail N ℓ₀ F hlit htn hTs hb5 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by simpa using h₁)
  · simp only [Nat.zero_add]
    exact le_rfl

end EighWeight

omit [Inhabited K] in
/-- **The kernel cost of the registered tree, weighted** ([Shah2024, Section 4], the operation count
of Theorem 4.2): for a cost $T$ of a kernel call by its largest dimension that is monotone and
superadditive ($T(a) + T(b) \le T(a + b)$, as a convex $T$ with $T(0) = 0$ is), under the standard
charge, exact integer literals up to $N + 4$ and the exact floor conversion (the sizes, kinds and
$k_+$ are control data in rounded cells, read back by binders: without the contracts a slot that
starts no node can read back a size $\ge 1$, design note §8), every successful run of
`NLAlib.eighProg.compiled` at the sizes $N$ and $(\ell_0, F)$ adds
at most $(\ell_0 + 1)(2F + 12)\,T(N)$ to the weighted kernel count (the weight
`NLAlib.Computation.OpKind.kernelWeight`): per level, the nodes have sizes
summing to at most $N$, each with at most $2F + 12$ kernel calls of largest dimension at most its
size. The static bound `NLAlib.eighCount` charges every size at every slot, a factor of about $N^2$
more. No printed source. -/
theorem eighProg.weight_le_of_exec_compiled {mm qr : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : IsUnitCharge I) {dec : P → K → ℝ} (p : P) (N ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem) (T : ℕ → ℕ)
    (hT : Monotone T) (hTsup : ∀ a b, T a + T b ≤ T (a + b)) {st st' : St P K (OpCount P ι)}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F] st = some st') :
    Finsupp.weight (OpKind.kernelWeight T) st'.cnt ≤
      Finsupp.weight (OpKind.kernelWeight T) st.cnt + (ℓ₀ + 1) * (2 * F + 12) * T N := by
  rw [Prog.exec_eq_exec_toStmt, eighProg.toStmt_compiled] at h
  have h' : exec I (eighProg p mm qr (.const N) (.const ℓ₀) (.const F) 0 1 2 3).run st =
      some st' := h
  have := EighWeight.preTriple_eighProg (I := I) (T := T) (p := p) (b := st.store.size + 5)
    (mm := mm) (qr := qr)
    N ℓ₀ F hlit htn hTsup (by omega) hT hc st st' rfl h'
  refine this.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _)
  rw [← Nat.mul_add]
  exact Nat.mul_le_mul_left _ (by omega)

end NLAlib
