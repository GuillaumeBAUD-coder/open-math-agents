import OMAStatements.S_oeis_a184368
import Mathlib

namespace OMA.S_oeis_a184368

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

open Finset

abbrev Row := Fin 2 → Fin 3

instance (u v : Row) : Decidable (BlockOK u v) := by unfold BlockOK; infer_instance

lemma N_eq (n : ℕ) : N n = ∑ s : Row, V BlockOK n s := by
  unfold N
  rw [Nat.card_eq_fintype_card]
  exact cardChain BlockOK n

def cc : ℕ → ℤ := fun j => [(-9 : ℤ), -6, 1].getD j 0

theorem recN (n : ℕ) : (N (n + 2) : ℤ) = 6 * N (n + 1) + 9 * N n := by
  have h := rec_total BlockOK 2 cc (by decide +kernel) n
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have e0 : cc 0 = -9 := rfl
  have e1 : cc 1 = -6 := rfl
  have e2 : cc 2 = 1 := rfl
  rw [e0, e1, e2] at h
  simp only [N_eq]
  push_cast
  simp only [add_zero, zero_add] at h
  linarith

theorem N0 : N 0 = 9 := by rw [N_eq]; decide +kernel
theorem N1 : N 1 = 63 := by rw [N_eq]; decide +kernel

theorem dvd3 (n : ℕ) : 3 ∣ N n ∧ 3 ∣ N (n + 1) := by
    induction n with
    | zero => rw [N0, N1]; omega
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨h2, ?_⟩
      have := recN n
      show 3 ∣ N (n + 2)
      omega
theorem N3 (n : ℕ) : N n = 3 * a n := by
  have ha : a n = N n / 3 := rfl
  rw [ha]
  have := (dvd3 n).1
  omega

theorem a0 : a 0 = 3 := by have := N3 0; rw [N0] at this; omega
theorem a1 : a 1 = 21 := by have := N3 1; rw [N1] at this; omega

theorem reca (n : ℕ) : a (n + 2) = 6 * a (n + 1) + 9 * a n := by
  have := recN n
  rw [N3, N3, N3] at this
  omega

theorem a2 : a 2 = 153 := by rw [reca 0, a0, a1]

theorem closedAll (n : ℕ) : (a n : ℝ) = ((3 - 3 * Real.sqrt 2) ^ n * (-4 + 3 * Real.sqrt 2) +
      (3 * (1 + Real.sqrt 2)) ^ n * (4 + 3 * Real.sqrt 2)) / (2 * Real.sqrt 2) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : Real.sqrt 2 ≠ 0 := by positivity
  set s := Real.sqrt 2 with hsdef
  have hα : (3 - 3 * s) ^ 2 = 6 * (3 - 3 * s) + 9 := by linear_combination 9 * hs
  have hβ : (3 * (1 + s)) ^ 2 = 6 * (3 * (1 + s)) + 9 := by linear_combination 9 * hs
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      rw [a0]; field_simp; push_cast; ring_nf
    | 1, _ =>
      rw [a1]; field_simp; push_cast; ring_nf
    | n + 2, ih =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      rw [reca]
      push_cast
      rw [h1, h0]
      have key : (3 - 3 * s) ^ (n + 2) * (-4 + 3 * s) + (3 * (1 + s)) ^ (n + 2) * (4 + 3 * s) = 6 * ((3 - 3 * s) ^ (n + 1) * (-4 + 3 * s) + (3 * (1 + s)) ^ (n + 1) * (4 + 3 * s)) + 9 * ((3 - 3 * s) ^ n * (-4 + 3 * s) + (3 * (1 + s)) ^ n * (4 + 3 * s)) := by
        linear_combination ((3 - 3 * s) ^ n * (-4 + 3 * s)) * hα + ((3 * (1 + s)) ^ n * (4 + 3 * s)) * hβ
      rw [key]; ring

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  have h6 : (C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat _ 6
  have h9 : (C (9 : ℚ) : PowerSeries ℚ) = 9 := map_ofNat _ 9
  have h21 : (C (21 : ℚ) : PowerSeries ℚ) = 21 := map_ofNat _ 21
  have h27 : (C (27 : ℚ) : PowerSeries ℚ) = 27 := map_ofNat _ 27
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hF
  have e1 : F * (1 - 6 * X - 9 * X ^ 2) = F - C 6 * (X * F) - C 9 * (X * (X * F)) := by
    rw [h6, h9]; ring
  have e2 : (3 * X * (7 + 9 * X) : PowerSeries ℚ) = C 21 * X + C 27 * X ^ 2 := by
    rw [h21, h27]; ring
  have key : F * (1 - 6 * X - 9 * X ^ 2) = 3 * X * (7 + 9 * X) := by
    rw [e1, e2]
    have c : ∀ n, coeff n F = if n = 0 then 0 else (a n : ℚ) := fun n => by rw [hF, coeff_mk]
    ext n
    rcases n with _ | _ | _ | k
    · have h0 : constantCoeff F = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply, c]; simp
      simp [c, h0]
    · simp [c, a1, coeff_succ_X_mul, coeff_C_mul]
    · simp [c, a1, a2, coeff_succ_X_mul, coeff_C_mul, coeff_X_pow]
      norm_num
    · simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, c]
      rw [coeff_X_pow, coeff_X]
      have hq : (a (k + 3) : ℚ) = 6 * a (k + 2) + 9 * a (k + 1) := by exact_mod_cast reca (k + 1)
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, add_eq_zero, OfNat.ofNat_ne_zero]
      rw [if_neg (by omega), if_neg (by omega)]
      simp only [show k + 3 = k + 2 + 1 from rfl] at hq ⊢
      linarith
  have hD : constantCoeff (1 - 6 * X - 9 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by simp
  unfold G
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hD, mul_one]

end OMA.S_oeis_a184368

theorem OMA.solution : type_of% @OMA.S_oeis_a184368.main := by
  refine ⟨fun n hn => ?_, OMA.S_oeis_a184368.gf, fun n _ => OMA.S_oeis_a184368.closedAll n⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 + 1 := ⟨n - 3, by omega⟩
  simpa using OMA.S_oeis_a184368.reca (k + 1)
