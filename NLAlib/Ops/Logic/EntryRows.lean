/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.EntryFill

/-!
# Filling variable-length rows of entries

An inner loop may fill a different number of entries in each column. Its footprint is the
union of the actual entry blocks, so triangular matrix kernels retain their scalar operation
counts and do not initialize unused cells merely to simplify a proof.

## Main results

* `NLAlib.Ops.writes_loop_rows`: dependent inner bounds with ordinary mathematical invariants.
* `NLAlib.Ops.writes_fillEntryRows`: fixed-width matrix entries with variable column lengths.
* `NLAlib.Ops.Store.readsOnly_holdsRowEntries`: the ordinary frame rule preserves filled regions.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K E : Type} {md : Mode} {I : Interp Op Tst K} {τ : Tape K}
  {ρ : Env} {m : Mem K}

/-- Nested counted loops whose inner bound depends on the outer index. Their invariant and
footprint are indexed by the two mathematical loop indices. -/
theorem writes_loop_rows {n₁ n₂ : IExp} {body : Stmt Op Tst} {M : ℕ} (N : ℕ → ℕ)
    (hn₁ : n₁.eval ρ.idx = some M) (hn₂ : ∀ i, n₂.eval (ρ.pushIdx i).idx = some (N i))
    (F : ℕ → ℕ → Fp) (hF : ∀ i < M, ∀ j < N i, F i j ≤ F i (j + 1))
    (hrow : ∀ i < M, F i (N i) ≤ F (i + 1) 0)
    (P : ℕ → ℕ → Mem K → Prop) (h0 : P 0 0 m)
    (hnext : ∀ i < M, ∀ m', P i (N i) m' → P (i + 1) 0 m')
    (hstep : ∀ i < M, ∀ j < N i, ∀ m', m.store.EqOff (F i j) m'.store → P i j m' →
      Writes md I τ body ((ρ.pushIdx i).pushIdx j) (F i (j + 1)) (P i (j + 1)) m') :
    Writes md I τ (.loop n₁ (.loop n₂ body)) ρ (F M 0) (P M 0) m := by
  refine writes_loop hn₁ (fun i => F i 0) (fun i hi =>
    (Fp.le_of_chain (hF i hi) 0 (N i) (by omega) le_rfl).trans (hrow i hi))
    (fun i => P i 0) h0 fun i hi m' hfr hp => ?_
  refine Writes.mono (writes_loop (hn₂ i) (fun j => F i j) (hF i hi)
    (fun j m'' => m.store.EqOff (F i j) m''.store ∧ P i j m'') ⟨hfr, hp⟩
    fun j hj m'' _ hm => Writes.mono (hstep i hi j hj m'' hm.1 hm.2) le_rfl
      fun _ hfr' hp' => ⟨(hm.1.mono (hF i hi j hj)).trans hfr', hp'⟩) (hrow i hi)
    fun _ _ hm => hnext i hi _ hm.2

namespace EntryCodec

/-- The word block for an entry at a flat logical index. -/
def entryBlock (C : EntryCodec K E) (b off i : ℕ) : Fp :=
  Store.inBlock b (off + C.width * i) C.width

/-- Every bounded logical entry occupies a sub-block of the containing word array. -/
theorem entryBlock_le_inBlock (C : EntryCodec K E) (b off entries : ℕ) {i : ℕ}
    (hi : i < entries) : C.entryBlock b off i ≤ Store.inBlock b off (C.width * entries) := by
  intro b' x hx
  have hb := Nat.mul_le_mul_left C.width (show i + 1 ≤ entries by omega)
  rw [Nat.mul_succ] at hb
  exact ⟨hx.1, by have := hx.2.1; omega, by have := hx.2.2; omega⟩

/-- Different logical entries occupy disjoint word blocks. -/
theorem disj_entryBlock_of_lt (C : EntryCodec K E) {b off i j : ℕ} (h : i < j) :
    Fp.Disj (C.entryBlock b off i) (C.entryBlock b off j) := by
  apply Fp.disj_inBlock_of_le
  have hh := Nat.mul_le_mul_left C.width (show i + 1 ≤ j by omega)
  rw [Nat.mul_succ] at hh
  omega

/-- Distinct logical entries occupy disjoint word blocks, independent of traversal order. -/
theorem disj_entryBlock_of_ne (C : EntryCodec K E) {b off i j : ℕ} (h : i ≠ j) :
    Fp.Disj (C.entryBlock b off i) (C.entryBlock b off j) := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact C.disj_entryBlock_of_lt h
  · exact (C.disj_entryBlock_of_lt h).symm

/-- The entries already visited by a fill with column-dependent row counts. -/
def regionUpto (C : EntryCodec K E) (b off : ℕ) (index : ℕ → ℕ → ℕ) (N : ℕ → ℕ) (j i : ℕ) : Fp :=
  fun b' x => ∃ r c, ((c < j ∧ r < N c) ∨ (c = j ∧ r < i)) ∧
    C.entryBlock b off (index r c) b' x

/-- The full region filled by column-dependent row counts. -/
def regionFp (C : EntryCodec K E) (b off cols : ℕ) (index : ℕ → ℕ → ℕ) (N : ℕ → ℕ) : Fp :=
  C.regionUpto b off index N cols 0

/-- Visiting another row enlarges the written region. -/
theorem regionUpto_mono (C : EntryCodec K E) (b off : ℕ) (index : ℕ → ℕ → ℕ) (N : ℕ → ℕ) (j i : ℕ) :
    C.regionUpto b off index N j i ≤ C.regionUpto b off index N j (i + 1) := by
  rintro b' x ⟨r, c, hc | ⟨rfl, hr⟩, hx⟩
  · exact ⟨r, c, Or.inl hc, hx⟩
  · exact ⟨r, c, Or.inr ⟨rfl, by omega⟩, hx⟩

/-- Finishing a column begins the next column without changing the written region. -/
theorem regionUpto_next (C : EntryCodec K E) (b off : ℕ) (index : ℕ → ℕ → ℕ) (N : ℕ → ℕ) (j : ℕ) :
    C.regionUpto b off index N j (N j) ≤ C.regionUpto b off index N (j + 1) 0 := by
  rintro b' x ⟨r, c, hc | ⟨rfl, hr⟩, hx⟩
  · exact ⟨r, c, Or.inl ⟨by omega, hc.2⟩, hx⟩
  · exact ⟨r, c, Or.inl ⟨by omega, hr⟩, hx⟩

/-- Every prefix reached during a valid visit lies in the full region footprint. -/
theorem regionUpto_le_regionFp (C : EntryCodec K E) (b off cols : ℕ)
    (index : ℕ → ℕ → ℕ) (N : ℕ → ℕ) {j i : ℕ} (hj : j < cols) (hi : i ≤ N j) :
    C.regionUpto b off index N j i ≤ C.regionFp b off cols index N := by
  rintro b' x ⟨r, c, hc | ⟨hc, hr⟩, hx⟩
  · exact ⟨r, c, Or.inl ⟨hc.1.trans hj, hc.2⟩, hx⟩
  · subst c
    exact ⟨r, j, Or.inl ⟨hj, hr.trans_le hi⟩, hx⟩

/-- Disjoint logical entry indices give disjoint physical region footprints. This supports
in-place permutations that read one region while writing another. -/
theorem disj_regionFp (C : EntryCodec K E) (b off cols cols' : ℕ)
    (index index' : ℕ → ℕ → ℕ) (N N' : ℕ → ℕ)
    (hne : ∀ j < cols, ∀ i < N j, ∀ j' < cols', ∀ i' < N' j',
      index i j ≠ index' i' j') :
    Fp.Disj (C.regionFp b off cols index N) (C.regionFp b off cols' index' N') := by
  rintro b' x ⟨i, j, hj | ⟨_, hi⟩, hx⟩ ⟨i', j', hj' | ⟨_, hi'⟩, hx'⟩
  · exact (C.disj_entryBlock_of_ne (hne j hj.1 i hj.2 j' hj'.1 i' hj'.2)) b' x hx hx'
  all_goals omega

/-- Upper and strict lower triangle words occupy disjoint blocks, for every fixed-width
entry representation. The two index maps are the ordinary and transposed column-major maps. -/
theorem disj_regionFp_triangles (C : EntryCodec K E) (n b off : ℕ) :
    Fp.Disj (C.regionFp b off n (fun i j => i * n + j) (fun j => j))
      (C.regionFp b off n (fun i j => j * n + i) (fun j => j + 1)) := by
  apply C.disj_regionFp
  intro j hj i hi c hc r hr he
  have hrn : r < n := by omega
  have hd := congrArg (· / n) he
  have hm := congrArg (· % n) he
  simp only [Idx.div_add hj, Idx.div_add hrn] at hd
  simp only [Idx.mod_add hj, Idx.mod_add hrn] at hm
  omega

/-- A bound on every visited logical index bounds the full region by an ordinary word block. -/
theorem regionFp_le_inBlock (C : EntryCodec K E) (b off cols entries : ℕ)
    (index : ℕ → ℕ → ℕ) (N : ℕ → ℕ)
    (hindex : ∀ j < cols, ∀ i < N j, index i j < entries) :
    C.regionFp b off cols index N ≤ Store.inBlock b off (C.width * entries) := by
  rintro b' x ⟨i, j, hj | ⟨_, hi⟩, hx⟩
  · have hb := hindex j hj.1 i hj.2
    have hw := Nat.mul_le_mul_left C.width (show index i j + 1 ≤ entries by omega)
    rw [Nat.mul_succ] at hw
    exact ⟨hx.1, by have := hx.2.1; omega, by have := hx.2.2; omega⟩
  · omega

/-- Strict upper-triangle entries and diagonal entries occupy disjoint word blocks. -/
theorem disj_regionFp_upper_diagonal (C : EntryCodec K E) (n b off : ℕ) :
    Fp.Disj (C.regionFp b off n (fun i j => j * n + i) (fun j => j))
      (C.regionFp b off n (fun _ j => j * n + j) (fun _ => 1)) := by
  apply C.disj_regionFp
  intro j hj i hi c hc r _ he
  have hin : i < n := hi.trans hj
  have hd := congrArg (· / n) he
  have hm := congrArg (· % n) he
  simp only [Idx.div_add hin, Idx.div_add hc] at hd
  simp only [Idx.mod_add hin, Idx.mod_add hc] at hm
  omega

end EntryCodec

namespace Store

/-- Actual component reads on a matrix region with column-dependent row counts. -/
def HoldsEntryRegion (s : Store K) (C : EntryCodec K E) (b off cols : ℕ) (index : ℕ → ℕ → ℕ)
    (N : ℕ → ℕ) (A : ℕ → ℕ → E) : Prop :=
  ∀ j < cols, ∀ i < N j, ∀ z : Fin C.width,
    s.get b (off + C.width * (index i j) + z) = some (C.words (A i j) z)

/-- Region facts use precisely the word blocks visited by the fill and are preserved by the
existing frame rule on disjoint footprints. -/
theorem readsOnly_holdsEntryRegion (C : EntryCodec K E) (b off cols : ℕ) (index : ℕ → ℕ → ℕ)
    (N : ℕ → ℕ) (A : ℕ → ℕ → E) :
    ReadsOnly (C.regionFp b off cols index N)
      (fun s : Store K => s.HoldsEntryRegion C b off cols index N A) := by
  intro s s' hg hp j hj i hi z
  rw [hg b (off + C.width * (index i j) + z) ?_]
  · exact hp j hj i hi z
  · exact ⟨i, j, Or.inl ⟨hj, hi⟩, rfl, by omega, by have := z.isLt; omega⟩

end Store

/-- A variable-length inner loop fills one fixed-width entry at each visit. This includes
triangular regions without extra initialization or extra scalar operations. The step gives
only its actual component words; preservation and assembly of all earlier entries are shared. -/
theorem writes_fillEntryRegion {n₁ n₂ : IExp} {body : Stmt Op Tst}
    (C : EntryCodec K E) (b off cols : ℕ) (index : ℕ → ℕ → ℕ) (N : ℕ → ℕ)
    (hindex : Set.InjOn (fun p : ℕ × ℕ => index p.1 p.2)
      {p | p.2 < cols ∧ p.1 < N p.2})
    (hn₁ : n₁.eval ρ.idx = some cols) (hn₂ : ∀ j, n₂.eval (ρ.pushIdx j).idx = some (N j))
    (A : ℕ → ℕ → E) (pos : ℕ → ℕ → ℕ) (hpos : m.pos = pos 0 0)
    (hnext : ∀ j < cols, pos j (N j) = pos (j + 1) 0)
    (hstep : ∀ j < cols, ∀ i < N j, ∀ m',
      m.store.EqOff (C.regionUpto b off index N j i) m'.store → m'.pos = pos j i →
      Writes md I τ body ((ρ.pushIdx j).pushIdx i)
        (C.entryBlock b off (index i j))
        (fun m'' => (∀ z : Fin C.width,
          m''.store.get b (off + C.width * (index i j) + z) =
            some (C.words (A i j) z)) ∧ m''.pos = pos j (i + 1)) m') :
    Writes md I τ (.loop n₁ (.loop n₂ body)) ρ (C.regionFp b off cols index N)
      (fun m' => m'.store.HoldsEntryRegion C b off cols index N A ∧ m'.pos = pos cols 0) m := by
  let P := fun j i (m' : Mem K) =>
    (∀ r c, (c < j ∧ r < N c) ∨ (c = j ∧ r < i) → ∀ z : Fin C.width,
      m'.store.get b (off + C.width * (index r c) + z) =
        some (C.words (A r c) z)) ∧ m'.pos = pos j i
  have h := writes_loop_rows (md := md) (I := I) (τ := τ) (body := body) N hn₁ hn₂
    (C.regionUpto b off index N) (fun j _ i _ => C.regionUpto_mono b off index N j i)
    (fun j _ => C.regionUpto_next b off index N j) P
    ⟨fun _ _ h => by rcases h with h | h <;> omega, hpos⟩
    (fun j hj m' hp => ⟨fun r c hc z => by
      rcases hc with ⟨hc, hr⟩ | ⟨_, hr⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
        · exact hp.1 r c (Or.inl ⟨hc, hr⟩) z
        · exact hp.1 r c (Or.inr ⟨rfl, hr⟩) z
      · omega, hp.2.trans (hnext j hj)⟩)
    fun j hj i hi m' hfr hp => ?_
  · exact h.mono le_rfl fun _ _ hp =>
      ⟨fun j hj i hi z => hp.1 i j (Or.inl ⟨hj, hi⟩) z, hp.2⟩
  · refine (hstep j hj i hi m' hfr hp.2).mono
      (fun b' x hx => ⟨i, j, Or.inr ⟨rfl, by omega⟩, hx⟩) fun m'' hfr' hs => ⟨?_, hs.2⟩
    have hold : ∀ r c, (c < j ∧ r < N c) ∨ (c = j ∧ r < i) → ∀ z : Fin C.width,
        m''.store.get b (off + C.width * (index r c) + z) =
          m'.store.get b (off + C.width * (index r c) + z) := by
      intro r c hc z
      have hne : index r c ≠ index i j := by
        intro he
        have hm : c < cols ∧ r < N c := by
          rcases hc with ⟨hc, hr⟩ | ⟨rfl, hr⟩
          · exact ⟨hc.trans hj, hr⟩
          · exact ⟨hj, hr.trans hi⟩
        have heq : (r, c) = (i, j) := hindex hm ⟨hj, hi⟩ he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rcases hc with ⟨hc, _⟩ | ⟨_, hr⟩ <;> omega
      refine hfr'.get_eq fun hx => ?_
      exact (C.disj_entryBlock_of_ne hne).symm _ _ hx
        ⟨rfl, by omega, by have := z.isLt; omega⟩
    intro r c hc z
    rcases hc with ⟨hc, hr⟩ | ⟨rfl, hr⟩
    · rw [hold r c (Or.inl ⟨hc, hr⟩) z]
      exact hp.1 r c (Or.inl ⟨hc, hr⟩) z
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · rw [hold r c (Or.inr ⟨rfl, hr⟩) z]
        exact hp.1 r c (Or.inr ⟨rfl, hr⟩) z
      · exact hs.1 z

namespace EntryCodec

/-- The filled prefix in an ordinary column-major logical layout. -/
abbrev rowsUpto (C : EntryCodec K E) (L : MatLayout) (N : ℕ → ℕ) (j i : ℕ) : Fp :=
  C.regionUpto L.buf L.off (fun i j => j * L.ld + i) N j i

/-- The full column-major region for the specified row counts. -/
abbrev rowsFp (C : EntryCodec K E) (L : MatLayout) (N : ℕ → ℕ) : Fp :=
  C.regionFp L.buf L.off L.cols (fun i j => j * L.ld + i) N

end EntryCodec

namespace Store

/-- Actual component reads on a column-major matrix region. -/
abbrev HoldsRowEntries (s : Store K) (C : EntryCodec K E) (L : MatLayout)
    (N : ℕ → ℕ) (A : ℕ → ℕ → E) : Prop :=
  s.HoldsEntryRegion C L.buf L.off L.cols (fun i j => j * L.ld + i) N A

/-- Column-major region facts are preserved on their exact word footprint. -/
theorem readsOnly_holdsRowEntries (C : EntryCodec K E) (L : MatLayout)
    (N : ℕ → ℕ) (A : ℕ → ℕ → E) :
    ReadsOnly (C.rowsFp L N) (fun s : Store K => s.HoldsRowEntries C L N A) :=
  readsOnly_holdsEntryRegion C L.buf L.off L.cols (fun i j => j * L.ld + i) N A

/-- A strict upper triangle and a diagonal assemble the inclusive upper region. The two
facts refer to actual component words; no initialized lower entry is needed. -/
theorem HoldsRowEntries.of_upper_and_diagonal {s : Store K} {C : EntryCodec K E}
    {n b off : ℕ} {F : ℕ → ℕ → E} {G : ℕ → E}
    (hu : s.HoldsRowEntries C ⟨b, off, n, n, n⟩ (fun j => j) F)
    (hd : s.HoldsEntryRegion C b off n (fun _ j => j * n + j) (fun _ => 1)
      (fun _ j => G j)) :
    s.HoldsRowEntries C ⟨b, off, n, n, n⟩ (fun j => j + 1)
      (fun i j => if i = j then G i else F i j) := by
  intro j hj i hi z
  change i < j + 1 at hi
  by_cases hij : i = j
  · subst i
    simpa using hd j hj 0 Nat.zero_lt_one z
  · simpa only [if_neg hij] using hu j hj i (by change i < j; omega) z

end Store

/-- The fixed-width region fill rule in an ordinary column-major matrix layout. -/
theorem writes_fillEntryRows {n₁ n₂ : IExp} {body : Stmt Op Tst}
    (C : EntryCodec K E) (L : MatLayout) (hL : L.Valid) (N : ℕ → ℕ)
    (hN : ∀ j < L.cols, N j ≤ L.rows)
    (hn₁ : n₁.eval ρ.idx = some L.cols) (hn₂ : ∀ j, n₂.eval (ρ.pushIdx j).idx = some (N j))
    (A : ℕ → ℕ → E) (pos : ℕ → ℕ → ℕ) (hpos : m.pos = pos 0 0)
    (hnext : ∀ j < L.cols, pos j (N j) = pos (j + 1) 0)
    (hstep : ∀ j < L.cols, ∀ i < N j, ∀ m',
      m.store.EqOff (C.rowsUpto L N j i) m'.store → m'.pos = pos j i →
      Writes md I τ body ((ρ.pushIdx j).pushIdx i)
        (C.entryBlock L.buf L.off (j * L.ld + i))
        (fun m'' => (∀ z : Fin C.width,
          m''.store.get L.buf (L.off + C.width * (j * L.ld + i) + z) =
            some (C.words (A i j) z)) ∧ m''.pos = pos j (i + 1)) m') :
    Writes md I τ (.loop n₁ (.loop n₂ body)) ρ (C.rowsFp L N)
      (fun m' => m'.store.HoldsRowEntries C L N A ∧ m'.pos = pos L.cols 0) m := by
  apply writes_fillEntryRegion C L.buf L.off L.cols (fun i j => j * L.ld + i) N
    ?_ hn₁ hn₂ A pos hpos hnext hstep
  intro p hp q hq he
  have hp' : p.1 < L.ld := hp.2.trans_le ((hN p.2 hp.1).trans hL)
  have hq' : q.1 < L.ld := hq.2.trans_le ((hN q.2 hq.1).trans hL)
  have hr := congrArg (· % L.ld) he
  have hc := congrArg (· / L.ld) he
  simp only [Idx.mod_add hp', Idx.mod_add hq'] at hr
  simp only [Idx.div_add hp', Idx.div_add hq'] at hc
  exact Prod.ext hr hc

end NLAlib.Ops
