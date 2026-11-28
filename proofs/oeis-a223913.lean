import OMAStatements.S_oeis_a223913
import Mathlib

set_option maxHeartbeats 4000000

namespace OMA.S_oeis_a223913

section generic
variable {S : Type} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]

def Chain (n : ℕ) := {y : Fin (n + 1) → S // ∀ i : Fin n, R (y i.castSucc) (y i.succ)}

instance (n : ℕ) : Fintype (Chain R n) := by unfold Chain; infer_instance

def V : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then V n t else 0

theorem cardStart (n : ℕ) (s : S) :
    Fintype.card {y : Chain R n // y.1 0 = s} = V R n s := by
  induction n generalizing s with
  | zero =>
    simp only [V]
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨fun _ => s, fun i => i.elim0⟩, rfl⟩, ?_⟩
    rintro ⟨⟨y, hy⟩, h0⟩
    apply Subtype.ext; apply Subtype.ext
    funext j
    have : j = 0 := Fin.ext (by have := j.2; omega)
    subst this; exact h0
  | succ n ih =>
    have e : {y : Chain R (n + 1) // y.1 0 = s} ≃
        Σ t : S, {z : Chain R n // z.1 0 = t ∧ R s t} :=
      { toFun := fun y => ⟨y.1.1 1, ⟨⟨fun j => y.1.1 j.succ, fun i => y.1.2 i.succ⟩, rfl, by
          have h := y.1.2 0
          have h0 : y.1.1 (Fin.castSucc 0) = s := y.2
          rw [h0] at h
          exact h⟩⟩
        invFun := fun p => ⟨⟨Fin.cons s p.2.1.1, by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · have h2 := p.2.2.2
            rw [← p.2.2.1] at h2
            simpa using h2
          · simpa using p.2.1.2 j⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨y, hy⟩, h0⟩
          apply Subtype.ext; apply Subtype.ext
          funext j
          refine Fin.cases ?_ (fun k => ?_) j
          · simpa using h0.symm
          · simp
        right_inv := by
          rintro ⟨t, ⟨⟨z, hz⟩, h1, h2⟩⟩
          simp only [Fin.cons_succ]
          have : (Fin.cons s z : Fin (n + 2) → S) 1 = t := by
            have : (1 : Fin (n + 2)) = Fin.succ 0 := rfl
            rw [this, Fin.cons_succ]; exact h1
          subst this
          rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [V]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : R s t
    · simp only [h, if_true, and_true]
      exact ih t
    · simp only [h, if_false, and_false]
      simp [Fintype.card_eq_zero_iff]

theorem cardChain (n : ℕ) : Fintype.card (Chain R n) = ∑ s, V R n s := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun y : Chain R n => y.1 0)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact cardStart R n s

theorem rec_gen (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) :
    ∀ n s, ∑ j ∈ Finset.range (m + 1), c j * (V R (n + j) s : ℤ) = 0 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro s
    have : ∀ j, (V R (n + 1 + j) s : ℤ) = ∑ t, if R s t then (V R (n + j) t : ℤ) else 0 := by
      intro j
      rw [show n + 1 + j = (n + j) + 1 by omega]
      simp [V]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h : R s t
    · have := ih t
      simp only [h, if_true]
      simpa [← Finset.mul_sum] using this
    · simp [h]

theorem rec_total (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (∑ s, (V R (n + j) s : ℤ)) = 0 := by
  have h := Finset.sum_eq_zero (s := (Finset.univ : Finset S)) (fun s _ => rec_gen R m c h0 n s)
  rw [Finset.sum_comm] at h
  simpa [Finset.mul_sum] using h
end generic

open PowerSeries in
theorem gf_gen (b : ℕ → ℚ) (m q : ℕ) (d p : ℕ → ℚ) (D N : PowerSeries ℚ)
    (hD : D = ∑ j ∈ Finset.range (m + 1), C (d j) * X ^ j)
    (hN : N = ∑ j ∈ Finset.range (q + 1), C (p j) * X ^ j) (hD0 : d 0 ≠ 0) (hp : ∀ n, q < n → p n = 0)
    (hb : ∀ n, ∑ j ∈ Finset.range (m + 1), d j * (if j ≤ n then b (n - j) else 0) =
      if n ≤ q then p n else 0) :
    mk b = N * D⁻¹ := by
  have hc : constantCoeff D ≠ 0 := by
    rw [hD]
    simp only [map_sum, map_mul, map_pow, constantCoeff_C, constantCoeff_X]
    rw [Finset.sum_eq_single 0]
    · simpa using hD0
    · intro j _ hj; simp [hj]
    · intro h; exfalso; exact h (by simp)
  rw [eq_mul_inv_iff_mul_eq hc, hD, hN]
  ext n
  simp only [Finset.mul_sum, map_sum]
  have : ∀ j ∈ Finset.range (m + 1), coeff n (mk b * (C (d j) * X ^ j)) =
      d j * (if j ≤ n then b (n - j) else 0) := by
    intro j _
    rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow']
    simp
  rw [Finset.sum_congr rfl this, hb n]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single n]
  · by_cases h : n ≤ q
    · simp [h]
    · simp [h, hp n (by omega)]
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; simp at h; simp [hp n (by omega)]

section pairs
variable {X : Type} [Fintype X] [DecidableEq X] (P : X → Prop) (B : X → X → Prop) (T3 : X → X → X → Prop)
  [DecidablePred P] [∀ a b, Decidable (B a b)] [∀ a b c, Decidable (T3 a b c)]

abbrev PS := {p : X × X // P p.1 ∧ P p.2 ∧ B p.1 p.2}

def PRel (p q : PS P B) : Prop := p.1.2 = q.1.1 ∧ T3 p.1.1 p.1.2 q.1.2

def goodF {n : ℕ} (x : Fin (n + 2) → X) : Prop :=
  (∀ i, P (x i)) ∧ (∀ i : Fin (n + 1), B (x i.castSucc) (x i.succ)) ∧
  ∀ i : Fin n, T3 (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ)

def xs {n : ℕ} (y : Chain (PRel P B T3) n) : Fin (n + 2) → X :=
  Fin.snoc (α := fun _ => X) (fun i : Fin (n + 1) => (y.1 i).1.1) (y.1 (Fin.last n)).1.2

theorem xs_cs {n : ℕ} (y : Chain (PRel P B T3) n) (i : Fin (n + 1)) : xs P B T3 y i.castSucc = (y.1 i).1.1 := by
  simp [xs]

theorem xs_last {n : ℕ} (y : Chain (PRel P B T3) n) : xs P B T3 y (Fin.last (n + 1)) = (y.1 (Fin.last n)).1.2 := by
  simp [xs]

theorem xs_succ {n : ℕ} (y : Chain (PRel P B T3) n) (i : Fin (n + 1)) : xs P B T3 y i.succ = (y.1 i).1.2 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.succ_last, xs_last]
  · have h := (y.2 j).1
    rw [Fin.succ_castSucc, xs_cs]
    exact h.symm

theorem good_xs {n : ℕ} (y : Chain (PRel P B T3) n) : goodF P B T3 (xs P B T3 y) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [xs_last]; exact (y.1 (Fin.last n)).2.2.1
    · rw [xs_cs]; exact (y.1 j).2.1
  · rw [xs_cs, xs_succ]; exact (y.1 i).2.2.2
  · rw [xs_cs, xs_succ, xs_succ]
    exact (y.2 i).2

def toF {n : ℕ} (x : {x : Fin (n + 2) → X // goodF P B T3 x}) : Chain (PRel P B T3) n :=
  ⟨fun i => ⟨(x.1 i.castSucc, x.1 i.succ), x.2.1 _, x.2.1 _, x.2.2.1 i⟩, by
      intro i
      refine ⟨?_, ?_⟩
      · show x.1 i.castSucc.succ = x.1 i.succ.castSucc
        rw [Fin.succ_castSucc]
      · exact x.2.2.2 i⟩

theorem xs_toF {n : ℕ} (x : {x : Fin (n + 2) → X // goodF P B T3 x}) : xs P B T3 (toF P B T3 x) = x.1 := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [xs_last]
    show x.1 (Fin.last n).succ = x.1 (Fin.last (n + 1))
    rw [Fin.succ_last]
  · rw [xs_cs]
    rfl

def pe (n : ℕ) : {x : Fin (n + 2) → X // goodF P B T3 x} ≃ Chain (PRel P B T3) n where
  toFun := toF P B T3
  invFun y := ⟨xs P B T3 y, good_xs P B T3 y⟩
  left_inv x := Subtype.ext (xs_toF P B T3 x)
  right_inv y := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    apply Prod.ext
    · exact xs_cs P B T3 y i
    · exact xs_succ P B T3 y i

end pairs


def PP (u : Fin 3 → Fin 3) : Prop := LineOK u

instance : DecidablePred PP := fun u => by unfold PP LineOK; infer_instance

instance : DecidableRel BlockOK := fun u v => by unfold BlockOK; infer_instance
instance : ∀ u v w, Decidable (TriOK u v w) := fun u v w => by unfold TriOK; infer_instance
instance {L : ℕ} : DecidablePred (@Good L) := fun x => by unfold Good LineOK BlockOK TriOK; infer_instance

abbrev S := PS PP BlockOK

instance : DecidableRel (PRel PP BlockOK TriOK) := fun p q => by unfold PRel; infer_instance

abbrev Rel : S → S → Prop := PRel PP BlockOK TriOK

theorem good_iff {n : ℕ} (x : Fin (n + 2) → Fin 3 → Fin 3) : Good x ↔ goodF PP BlockOK TriOK x := by
  unfold goodF PP
  constructor
  · intro h
    exact ⟨h.1, fun i => h.2.1 _ _ (by simp), fun i => h.2.2 _ _ _ (by simp) (by simp)⟩
  · intro h
    refine ⟨h.1, ?_, ?_⟩
    · intro i j hj
      have hj2 := j.2
      obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1), k.castSucc = i := ⟨⟨i, by omega⟩, rfl⟩
      subst hk
      have : j = k.succ := Fin.ext (by simp [hj])
      subst this
      exact h.2.1 k
    · intro i j l hj hl
      have hl2 := l.2
      obtain ⟨k, hk⟩ : ∃ k : Fin n, k.castSucc.castSucc = i := ⟨⟨i, by omega⟩, Fin.ext rfl⟩
      subst hk
      have e1 : j = k.castSucc.succ := Fin.ext (by simp [hj])
      subst e1
      have e2 : l = k.succ.succ := Fin.ext (by simp [hl, hj])
      subst e2
      exact h.2.2 k

@[irreducible] def T (n : ℕ) : ℕ := ∑ s : S, V Rel n s

theorem a_eq (n : ℕ) : T n = ∑ s : S, V Rel n s := by unfold T; rfl

theorem a_succ2 (n : ℕ) : a (n + 2) = T n := by
  rw [a_eq]
  have e : {x : Fin (n + 2) → Fin 3 → Fin 3 // Good x} ≃ {x // goodF PP BlockOK TriOK x} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x => good_iff x)
  unfold a
  rw [Nat.card_congr (e.trans (pe PP BlockOK TriOK n)), Nat.card_eq_fintype_card, cardChain]
theorem vT0 : T 0 = 158 := by rw [a_eq]; decide +kernel

def cc : ℕ → ℤ := fun j => [(0 : ℤ), (-1 : ℤ), (7 : ℤ), (-21 : ℤ), (35 : ℤ), (-35 : ℤ), (21 : ℤ), (-7 : ℤ), (1 : ℤ)].getD j 0

theorem hrec (k : ℕ) : (T (k + 8) : ℤ) = (1 : ℤ) * T (k + 1) + (-7 : ℤ) * T (k + 2) + (21 : ℤ) * T (k + 3) + (-35 : ℤ) * T (k + 4) + (35 : ℤ) * T (k + 5) + (-21 : ℤ) * T (k + 6) + (7 : ℤ) * T (k + 7) := by
  have h := rec_total Rel 8 cc (by decide +kernel) k
  have e0 : cc 0 = 0 := rfl
  have e1 : cc 1 = -1 := rfl
  have e2 : cc 2 = 7 := rfl
  have e3 : cc 3 = -21 := rfl
  have e4 : cc 4 = 35 := rfl
  have e5 : cc 5 = -35 := rfl
  have e6 : cc 6 = 21 := rfl
  have e7 : cc 7 = -7 := rfl
  have e8 : cc 8 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7, e8] at h
  simp only [a_eq]
  push_cast
  simp only [Nat.add_zero, zero_mul, zero_add] at h ⊢
  linarith

theorem vT1 : T 1 = 666 := by rw [a_eq]; decide +kernel
theorem vT2 : T 2 = 2111 := by rw [a_eq]; decide +kernel
theorem vT3 : T 3 = 5548 := by rw [a_eq]; decide +kernel
theorem vT4 : T 4 = 12752 := by rw [a_eq]; decide +kernel
theorem vT5 : T 5 = 26494 := by rw [a_eq]; decide +kernel
theorem vT6 : T 6 = 50863 := by rw [a_eq]; decide +kernel
theorem vT7 : T 7 = 91634 := by rw [a_eq]; decide +kernel

theorem closedT (n : ℕ) (hn : 1 ≤ n) : (T n : ℚ) = (23 / 360) * ((n : ℚ) + 2) ^ 6 + (23 / 40) * ((n : ℚ) + 2) ^ 5 + (205 / 72) * ((n : ℚ) + 2) ^ 4 + (143 / 24) * ((n : ℚ) + 2) ^ 3 + (364 / 45) * ((n : ℚ) + 2) ^ 2 + (82 / 15) * ((n : ℚ) + 2) - 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 7
    · interval_cases n
      · rw [vT1]; norm_num
      · rw [vT2]; norm_num
      · rw [vT3]; norm_num
      · rw [vT4]; norm_num
      · rw [vT5]; norm_num
      · rw [vT6]; norm_num
      · rw [vT7]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
      have r : (T (k + 8) : ℚ) = (1 : ℚ) * T (k + 1) + (-7 : ℚ) * T (k + 2) + (21 : ℚ) * T (k + 3) + (-35 : ℚ) * T (k + 4) + (35 : ℚ) * T (k + 5) + (-21 : ℚ) * T (k + 6) + (7 : ℚ) * T (k + 7) := by exact_mod_cast hrec k
      have i1 := ih (k + 1) (by omega) (by omega)
      have i2 := ih (k + 2) (by omega) (by omega)
      have i3 := ih (k + 3) (by omega) (by omega)
      have i4 := ih (k + 4) (by omega) (by omega)
      have i5 := ih (k + 5) (by omega) (by omega)
      have i6 := ih (k + 6) (by omega) (by omega)
      have i7 := ih (k + 7) (by omega) (by omega)
      rw [r, i1, i2, i3, i4, i5, i6, i7]
      push_cast
      ring

theorem v0 : a 0 = 1 := by unfold a; rw [Nat.card_eq_fintype_card]; decide +kernel
theorem v1 : a 1 = 22 := by unfold a; rw [Nat.card_eq_fintype_card]; decide +kernel
theorem v2 : a 2 = 158 := by rw [a_succ2 0, a_eq]; decide +kernel
theorem v3 : a 3 = 666 := by rw [a_succ2 1, a_eq]; decide +kernel
theorem v4 : a 4 = 2111 := by rw [a_succ2 2, a_eq]; decide +kernel
theorem v5 : a 5 = 5548 := by rw [a_succ2 3, a_eq]; decide +kernel
theorem v6 : a 6 = 12752 := by rw [a_succ2 4, a_eq]; decide +kernel
theorem v7 : a 7 = 26494 := by rw [a_succ2 5, a_eq]; decide +kernel
theorem v8 : a 8 = 50863 := by rw [a_succ2 6, a_eq]; decide +kernel
theorem closedQ (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (23 / 360) * (n : ℚ) ^ 6 + (23 / 40) * (n : ℚ) ^ 5 + (205 / 72) * (n : ℚ) ^ 4 + (143 / 24) * (n : ℚ) ^ 3 + (364 / 45) * (n : ℚ) ^ 2 + (82 / 15) * (n : ℚ) - 1 := by
  by_cases h2 : 3 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [a_succ2]
    have := closedT k (by omega)
    rw [this]; push_cast; ring
  · have h3 : n < 3 := by omega
    interval_cases n
    · rw [v1]; norm_num
    · rw [v2]; norm_num

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  apply gf_gen _ 7 7 (fun j => [(1 : ℚ), (-7 : ℚ), (21 : ℚ), (-35 : ℚ), (35 : ℚ), (-21 : ℚ), (7 : ℚ), (-1 : ℚ)].getD j 0) (fun j => [(0 : ℚ), (22 : ℚ), (4 : ℚ), (22 : ℚ), (-3 : ℚ), (-3 : ℚ), (5 : ℚ), (-1 : ℚ)].getD j 0)
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · norm_num
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp_all
  · intro n
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | k
    · simp [Finset.sum_range_succ]
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have c0 := closedQ (k + 8) (by omega)
      have c1 := closedQ (k + 7) (by omega)
      have c2 := closedQ (k + 6) (by omega)
      have c3 := closedQ (k + 5) (by omega)
      have c4 := closedQ (k + 4) (by omega)
      have c5 := closedQ (k + 3) (by omega)
      have c6 := closedQ (k + 2) (by omega)
      have c7 := closedQ (k + 1) (by omega)
      simp [c0, c1, c2, c3, c4, c5, c6, c7]
      ring


end OMA.S_oeis_a223913

open OMA.S_oeis_a223913 in
theorem OMA.solution : type_of% @OMA.S_oeis_a223913.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    have e1 : k + 8 - 1 = k + 7 := by omega
    have e2 : k + 8 - 2 = k + 6 := by omega
    have e3 : k + 8 - 3 = k + 5 := by omega
    have e4 : k + 8 - 4 = k + 4 := by omega
    have e5 : k + 8 - 5 = k + 3 := by omega
    have e6 : k + 8 - 6 = k + 2 := by omega
    have e7 : k + 8 - 7 = k + 1 := by omega
    rw [e1, e2, e3, e4, e5, e6, e7]
    have c0 := closedQ (k + 8) (by omega)
    have c1 := closedQ (k + 7) (by omega)
    have c2 := closedQ (k + 6) (by omega)
    have c3 := closedQ (k + 5) (by omega)
    have c4 := closedQ (k + 4) (by omega)
    have c5 := closedQ (k + 3) (by omega)
    have c6 := closedQ (k + 2) (by omega)
    have c7 := closedQ (k + 1) (by omega)
    have hq : ((a (k + 8) : ℤ) : ℚ) = (((7 : ℤ) * (a (k + 7) : ℤ) + (-21 : ℤ) * (a (k + 6) : ℤ) + (35 : ℤ) * (a (k + 5) : ℤ) + (-35 : ℤ) * (a (k + 4) : ℤ) + (21 : ℤ) * (a (k + 3) : ℤ) + (-7 : ℤ) * (a (k + 2) : ℤ) + (1 : ℤ) * (a (k + 1) : ℤ) : ℤ) : ℚ) := by
      push_cast; rw [c0, c1, c2, c3, c4, c5, c6, c7]; push_cast; ring
    have hz : (a (k + 8) : ℤ) = (7 : ℤ) * (a (k + 7) : ℤ) + (-21 : ℤ) * (a (k + 6) : ℤ) + (35 : ℤ) * (a (k + 5) : ℤ) + (-35 : ℤ) * (a (k + 4) : ℤ) + (21 : ℤ) * (a (k + 3) : ℤ) + (-7 : ℤ) * (a (k + 2) : ℤ) + (1 : ℤ) * (a (k + 1) : ℤ) := by exact_mod_cast hq
    linarith
  · exact OMA.S_oeis_a223913.gf
  · intro n hn
    exact OMA.S_oeis_a223913.closedQ n hn
