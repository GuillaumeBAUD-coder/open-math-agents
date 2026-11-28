import OMAStatements.S_oeis_a224185
import Mathlib

namespace OMA.S_oeis_a224185

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

instance : DecidablePred LineOK := fun u => by unfold LineOK; infer_instance

abbrev S := {u : Fin 3 → Fin 3 // LineOK u}

def Rel : S → S → Prop := fun u v => BlockOK u.1 v.1

instance : DecidableRel Rel := fun u v => by unfold Rel BlockOK; infer_instance

@[irreducible] def T (n : ℕ) : ℕ := ∑ s, V Rel n s

theorem a_eq (n : ℕ) : T n = ∑ s, V Rel n s := by unfold T; rfl

theorem a_succ (n : ℕ) : a (n + 1) = T n := by
  rw [a_eq]
  unfold a
  have e : {x : Fin (n + 1) → Fin 3 → Fin 3 // Good x} ≃ Chain Rel n :=
    ⟨fun x => ⟨fun i => ⟨x.1 i, x.2.1 i⟩, fun i => x.2.2 i.castSucc i.succ (by simp)⟩,
     fun y => ⟨fun i => (y.1 i).1, fun i => (y.1 i).2, fun i j hij => by
        obtain ⟨k, hk⟩ : ∃ k : Fin n, k.castSucc = i := ⟨⟨i, by omega⟩, rfl⟩
        subst hk
        have : j = k.succ := Fin.ext (by simp [hij])
        subst this
        exact y.2 k⟩,
     fun x => rfl, fun y => rfl⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, cardChain]

def cc : ℕ → ℤ := fun j => [(-1 : ℤ), (7 : ℤ), (-21 : ℤ), (35 : ℤ), (-35 : ℤ), (21 : ℤ), (-7 : ℤ), (1 : ℤ)].getD j 0

set_option maxHeartbeats 4000000 in
theorem hrec (k : ℕ) : (T (k + 7) : ℤ) = (1 : ℤ) * T (k + 0) + (-7 : ℤ) * T (k + 1) + (21 : ℤ) * T (k + 2) + (-35 : ℤ) * T (k + 3) + (35 : ℤ) * T (k + 4) + (-21 : ℤ) * T (k + 5) + (7 : ℤ) * T (k + 6) := by
  have h := rec_total Rel 7 cc (by decide +kernel) k
  have e0 : cc 0 = -1 := rfl
  have e1 : cc 1 = 7 := rfl
  have e2 : cc 2 = -21 := rfl
  have e3 : cc 3 = 35 := rfl
  have e4 : cc 4 = -35 := rfl
  have e5 : cc 5 = 21 := rfl
  have e6 : cc 6 = -7 := rfl
  have e7 : cc 7 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7] at h
  simp only [a_eq]
  push_cast
  simp only [Nat.add_zero, zero_mul, zero_add] at h ⊢
  linarith

theorem vT0 : T 0 = 22 := by rw [a_eq]; decide +kernel

theorem vT1 : T 1 = 158 := by rw [a_eq]; decide +kernel
theorem vT2 : T 2 = 684 := by rw [a_eq]; decide +kernel
theorem vT3 : T 3 = 2205 := by rw [a_eq]; decide +kernel
theorem vT4 : T 4 = 5852 := by rw [a_eq]; decide +kernel
theorem vT5 : T 5 = 13524 := by rw [a_eq]; decide +kernel
theorem vT6 : T 6 = 28176 := by rw [a_eq]; decide +kernel
theorem vT7 : T 7 = 54153 := by rw [a_eq]; decide +kernel

theorem closedT (n : ℕ) (hn : 0 ≤ n) : (T n : ℚ) = (23 / 360) * ((n : ℚ) + 1) ^ 6 + (27 / 40) * ((n : ℚ) + 1) ^ 5 + (205 / 72) * ((n : ℚ) + 1) ^ 4 + (49 / 8) * ((n : ℚ) + 1) ^ 3 + (319 / 45) * ((n : ℚ) + 1) ^ 2 + (21 / 5) * ((n : ℚ) + 1) + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 6
    · interval_cases n
      · rw [vT0]; norm_num
      · rw [vT1]; norm_num
      · rw [vT2]; norm_num
      · rw [vT3]; norm_num
      · rw [vT4]; norm_num
      · rw [vT5]; norm_num
      · rw [vT6]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
      have r : (T (k + 7) : ℚ) = (1 : ℚ) * T (k + 0) + (-7 : ℚ) * T (k + 1) + (21 : ℚ) * T (k + 2) + (-35 : ℚ) * T (k + 3) + (35 : ℚ) * T (k + 4) + (-21 : ℚ) * T (k + 5) + (7 : ℚ) * T (k + 6) := by exact_mod_cast hrec k
      have i0 := ih (k + 0) (by omega) (by omega)
      have i1 := ih (k + 1) (by omega) (by omega)
      have i2 := ih (k + 2) (by omega) (by omega)
      have i3 := ih (k + 3) (by omega) (by omega)
      have i4 := ih (k + 4) (by omega) (by omega)
      have i5 := ih (k + 5) (by omega) (by omega)
      have i6 := ih (k + 6) (by omega) (by omega)
      rw [r, i0, i1, i2, i3, i4, i5, i6]
      push_cast
      ring


theorem v1 : a 1 = 22 := (a_succ 0).trans vT0
theorem v2 : a 2 = 158 := (a_succ 1).trans vT1
theorem v3 : a 3 = 684 := (a_succ 2).trans vT2
theorem v4 : a 4 = 2205 := (a_succ 3).trans vT3
theorem v5 : a 5 = 5852 := (a_succ 4).trans vT4
theorem v6 : a 6 = 13524 := (a_succ 5).trans vT5
theorem v7 : a 7 = 28176 := (a_succ 6).trans vT6
theorem closedQ (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (23 / 360) * (n : ℚ) ^ 6 + (27 / 40) * (n : ℚ) ^ 5 + (205 / 72) * (n : ℚ) ^ 4 + (49 / 8) * (n : ℚ) ^ 3 + (319 / 45) * (n : ℚ) ^ 2 + (21 / 5) * (n : ℚ) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a_succ]
  have := closedT k (by omega)
  rw [this]; push_cast; ring

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  apply gf_gen _ 7 7 (fun j => [(1 : ℚ), (-7 : ℚ), (21 : ℚ), (-35 : ℚ), (35 : ℚ), (-21 : ℚ), (7 : ℚ), (-1 : ℚ)].getD j 0) (fun j => [(0 : ℚ), (22 : ℚ), (4 : ℚ), (40 : ℚ), (-35 : ℚ), (21 : ℚ), (-7 : ℚ), (1 : ℚ)].getD j 0)
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


end OMA.S_oeis_a224185

open OMA.S_oeis_a224185 in
theorem OMA.solution : type_of% @OMA.S_oeis_a224185.main := by
  refine ⟨?_, gf, ?_⟩
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
  · intro n hn
    exact closedQ n hn
