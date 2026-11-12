/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedState
public import NLAlib.Krylov.Lanczos.InitialState
public import NLAlib.Krylov.Lanczos.Zero
public import NLAlib.Krylov.Lanczos.RoundedInterface

/-!
# Initializing the actual rounded Lanczos prefix

Literal calls zero every requested output cell. The actual self-dot, square root and guarded
scaling supply the input norm, direction defect and near-unit bound. Zero input is included;
no exact parallelism between the initial direction and the right-hand side is assumed.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.initialize_writes`: successful rounded initialization.
* `NLAlib.Krylov.Lanczos.Rounded.initialize_writes_with_suffix`: initialized extra coefficients.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops

/-- Initial mathematical names, with no executed Lanczos round and all later values zero. -/
noncomputable def Values.initial {n : ℕ} (q : Fin n → ℝ) (nu : ℝ) : Values n :=
  ⟨Function.update 0 1 q, 0, 0, nu⟩

variable {K : Type} [Inhabited K]

/-- Initial normalization changes only the first direction and the retained input norm. -/
theorem Packed.initialize {dec : K → ℝ} {n cap clen L : ℕ} {V C : ℕ × ℕ}
    {s s' : Store K} (hlen : 2 * cap + 2 ≤ clen)
    (hvc : V.1 ≠ C.1) (hv : V.1 < L) (hc : C.1 < L)
    (hV : StoresVec dec V (0 : Fin ((cap + 1) * n) → ℝ) s)
    (hC : StoresVec dec C (0 : Fin clen → ℝ) s)
    (hprev : StoresVec dec (L, 0) (0 : Fin n → ℝ) s)
    (hf : s.EqOff (normalizeFp n cap V C) s') {q : Fin n → ℝ} {nu : ℝ}
    (hq : StoresVec dec V q s')
    (hn : StoresCell dec (C.1, C.2 + (2 * cap + 1)) nu s') :
    Packed dec cap 0 V C (Values.initial q nu) s' ∧
      StoresVec dec (L, 0) (0 : Fin n → ℝ) s' := by
  have hcoeff : ∀ i < clen, i ≠ 2 * cap + 1 → StoresCell dec (C.1, C.2 + i) 0 s' :=
    fun i hi he => (hC.cell ⟨i, hi⟩).keep hf (normalizeFp_disj_coeff hvc he)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hn⟩, ?_⟩
  · intro j hj
    have : j = 0 := by omega
    subst j
    simpa [Values.initial] using hq
  · intro j hj hcap
    exact (hV.zero_sub (Idx.mul_add_le_mul (show j < cap + 1 by omega) n)).keep hf
      (normalizeFp_disj_basis hvc hj)
  · intro j hj; omega
  · intro j _ hj
    exact hcoeff j (by omega) (by omega)
  · intro j hj
    have : j = 0 := by omega
    subst j
    simpa [Values.initial] using hcoeff cap (by omega) (by omega)
  · intro j _ hj
    exact hcoeff (cap + j) (by omega) (by omega)
  · refine hprev.keep hf ?_
    simp only [normalizeFp, Fp.blocks, Fp.disj_sup_left, Fp.disj_bot_left, and_true]
    exact ⟨Fp.disj_inBlock_of_ne (by omega), Fp.disj_inBlock_of_ne (by omega)⟩

/-- The primitive normalization guarantees assemble the initial state without another run
assumption. The first direction's norm and its input mismatch are derived quantities. -/
theorem State.initial {dec : K → ℝ} {n cap L : ℕ} {V C : ℕ × ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ}
    {em u E : ℝ} {e : Blas1Err} {s : Store K} {bs ys : List K} {b sigma : K}
    (hp : Precision em u E e n)
    (hpack : Packed dec cap 0 V C (Values.initial (decv dec n ys) (dec b)) s)
    (hprev : StoresVec dec (L, 0) (0 : Fin n → ℝ) s)
    (hn : IsNrm2Err dec (e.dot n) u n (vec bs) b)
    (hs : IsScalErr dec e.scal n b (vec bs) (vec ys))
    (hz : decv dec n bs = 0 → decv dec n ys = 0)
    (hread : s.get (L + 2) 0 = some sigma)
    (hd : IsDotErr dec (e.dot n) n (vec bs) (vec bs) sigma) :
    State dec A (decv dec n bs) E cap 0 V C L
      (Values.initial (decv dec n ys) (dec b)) s := by
  obtain ⟨hbn, herr, hunit⟩ := hp.norm_bounds hn hs
  have hguard := hp.guard_iff hn hd
  refine ⟨⟨⟨hbn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inl ?_⟩, hpack⟩, ?_, ?_⟩
  · simpa [Values.initial] using herr
  · constructor
    · intro hb
      by_contra hne
      exact (hn.dec_pos_of_ne_zero hp.dot_lt hp.scalar_lt hne).ne' hb
    · exact hn.eq_zero_of_decoded_eq_zero
  · simpa [Values.initial] using hunit
  · simpa [Values.initial] using hz
  · intro j hj; simp [Values.initial, Function.update_of_ne (show j ≠ 1 by omega)]
  · intro j _; simp [Values.initial]
  · intro _; exact Or.inl rfl
  · simp [Values.initial]
  · simpa [Values.initial] using hprev
  · exact ⟨sigma, hread, hguard.1, by simpa [Values.initial] using hguard.2⟩

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- Rounded initialization retains its complete zero coefficient suffix beyond the ordinary
Lanczos output. Reorthogonalized drivers use this suffix for saved raw residual norms. -/
theorem initialize_writes_with_suffix {M : Machine K} {dec : K → ℝ} {n cap clen L : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {em u E : ℝ} {e : Blas1Err}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec e ok I)
    (hok : ok n) (hCmp : IsCmp dec I) (hprec : Precision em u E e n)
    {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hBL : B.1 < L) (hVL : V.1 < L) (hCL : C.1 < L)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n)
    (ht : μ.store.len (L + 2) = 2) (hclen : 2 * cap + 2 ≤ clen)
    (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hv : V.2 + (cap + 1) * n ≤ μ.store.len V.1)
    (hc : C.2 + clen ≤ μ.store.len C.1) :
    Writes .total I τ initializeState
      (Env.frame [n, cap, clen] [B, V, C, (L, 0), (L + 2, 0)])
      (Fp.blocks [V, C] [(cap + 1) * n, clen] ⊔ Fp.above L)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ z,
        State dec A (decv dec n bs) E cap 0 V C L z μ'.store ∧
        ∀ i, 2 * cap + 2 ≤ i → i < clen →
          StoresCell dec (C.1, C.2 + i) 0 μ'.store) μ := by
  refine Writes.seq_le (writes_frame rfl rfl (by simp [Mem.Live]; omega)
    (zero_writes hS (by omega) hv)) (by fp_sub) fun μ₁ hfr₁ ⟨hpos₁, hv₁⟩ => ?_
  have hc₁ : C.2 + clen ≤ μ₁.store.len C.1 := by simpa [hfr₁.len_eq] using hc
  refine Writes.seq_le (writes_frame rfl rfl (by simp [Mem.Live, hfr₁.length_eq]; omega)
    (zero_writes hS (by rw [hfr₁.length_eq]; omega) hc₁)) (by fp_sub)
    fun μ₂ hfr₂ ⟨hpos₂, hc₂⟩ => ?_
  have hp₂ : μ₂.store.len L = n := by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hp
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq]; omega)
    (zero_writes hS (by rw [hfr₂.length_eq, hfr₁.length_eq]; omega)
      (by simpa only [Nat.zero_add] using hp₂.ge))) (by fp_sub)
    fun μ₃ hfr₃ ⟨hpos₃, hp₃⟩ => ?_
  step hB.dot as μ₄ hfr₄ ⟨hpos₄, sigma, hsig, hself⟩
  have hV : StoresVec dec V (0 : Fin ((cap + 1) * n) → ℝ) μ₄.store :=
    StoresVec.of_zero_readBlock (by kept) hM.zero
  have hC : StoresVec dec C (0 : Fin clen → ℝ) μ₄.store :=
    StoresVec.of_zero_readBlock (by kept) hM.zero
  have hP : StoresVec dec (L, 0) (0 : Fin n → ℝ) μ₄.store :=
    StoresVec.of_zero_readBlock (by kept) hM.zero
  obtain ⟨qs, hqs, hqzero⟩ := hV.zero_sub (n := n) (o := 0)
    (by simp only [Nat.add_mul, Nat.one_mul]; omega)
  obtain ⟨b0, hb0, hbzero⟩ := hC.cell ⟨2 * cap + 1, by omega⟩
  have hncap : n ≤ (cap + 1) * n := by
    simpa only [Nat.add_mul, Nat.one_mul] using Nat.le_add_left n (cap * n)
  have hnroom : μ₄.Room [V, (C.1, C.2 + 2 * cap + 1)] [n, 1] := by
    simp only [Mem.room_cons, Mem.room_nil, and_true, hfr₄.len_eq, hfr₃.len_eq,
      hfr₂.len_eq, hfr₁.len_eq]
    constructor <;> omega
  refine (writes_frame rfl rfl (by
    simp [Mem.Live, hfr₄.length_eq, hfr₃.length_eq, hfr₂.length_eq, hfr₁.length_eq]; omega)
    (normalize_rounded_writes (w := B) (s := (L + 2, 0)) (q := V)
      (b := (C.1, C.2 + 2 * cap + 1)) hS hM hprec.scalar_lt hprec.dot_lt hB hok hCmp
      (by omega) hBV hBC (by omega) (by omega) hVC
      (by simp [Mem.Live, hfr₄.length_eq, hfr₃.length_eq, hfr₂.length_eq, hfr₁.length_eq]; omega)
      (by kept) hsig (by simpa using hqs) hb0 hself hqzero hbzero hnroom)).mono (by fp_sub) ?_
  rintro μ₅ hfr₅ ⟨hpos₅, ys, b, hys, hb, hn, hscal, hzero⟩
  obtain ⟨hpacked, hprev⟩ := Packed.initialize hclen hVC hVL hCL hV hC hP hfr₅
    ⟨ys, hys, rfl⟩ ⟨b, by simpa only [Nat.add_assoc] using hb, rfl⟩
  refine ⟨by simp [hpos₅, hpos₄, hpos₃, hpos₂, hpos₁], _,
    State.initial hprec hpacked hprev hn hscal hzero (by kept) hself, ?_⟩
  intro i hlo hi
  exact (hC.cell ⟨i, hi⟩).keep hfr₅ (normalizeFp_disj_coeff (n := n) (cap := cap) (V := V) (C := C)
    (i := i) hVC (by omega))

/-- Readable inputs and input precision suffice for initialization at every cap. Every
output tail is initialized, and zero input avoids division by zero. -/
theorem initialize_writes {M : Machine K} {dec : K → ℝ} {n cap clen L : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {em u E : ℝ} {e : Blas1Err}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec e ok I)
    (hok : ok n) (hCmp : IsCmp dec I) (hprec : Precision em u E e n)
    {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hBL : B.1 < L) (hVL : V.1 < L) (hCL : C.1 < L)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n)
    (ht : μ.store.len (L + 2) = 2) (hclen : 2 * cap + 2 ≤ clen)
    (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hv : V.2 + (cap + 1) * n ≤ μ.store.len V.1)
    (hc : C.2 + clen ≤ μ.store.len C.1) :
    Writes .total I τ initializeState
      (Env.frame [n, cap, clen] [B, V, C, (L, 0), (L + 2, 0)])
      (Fp.blocks [V, C] [(cap + 1) * n, clen] ⊔ Fp.above L)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ z,
        State dec A (decv dec n bs) E cap 0 V C L z μ'.store) μ := by
  refine (initialize_writes_with_suffix (A := A) hS hM hB hok hCmp hprec hBV hBC hVC
    hBL hVL hCL hlen hp ht hclen hb hv hc).mono le_rfl ?_
  rintro μ' _ ⟨hpos, z, hstate, _⟩
  exact ⟨hpos, z, hstate⟩

end NLAlib.Krylov.Lanczos.Rounded
