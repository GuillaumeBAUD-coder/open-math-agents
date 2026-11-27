import OMAReductions.R_OeisA7406_conjecture_R1
import Mathlib.FieldTheory.Finite.Basic

/-! Clearing denominators reduces the numerator to the inverse-square power sum in the prime field. -/

open Finset

private lemma inverse_square_sum (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∑ k ∈ Ico 1 p, ((k : ZMod p)⁻¹)^2 = 0 := by
  have reindex : (∑ k ∈ Ico 1 p, ((k : ZMod p)⁻¹)^2) =
      ∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹)^2 :=
    Finset.sum_bij'
      (fun v hv ↦ Units.mk0 (v : ZMod p) (mt (ZMod.natCast_eq_zero_iff v p).mp (by
        exact Nat.not_dvd_of_pos_of_lt (by have := (mem_Ico.mp hv).1; omega) (mem_Ico.mp hv).2)))
      (fun u _ ↦ (u : ZMod p).val)
      (fun _ _ ↦ Finset.mem_univ _)
      (fun u _ ↦ by grind [u.ne_zero, ZMod.val_ne_zero, ZMod.val_lt])
      (fun v hv ↦ by simp [ZMod.val_cast_of_lt (Finset.mem_Ico.mp hv).2])
      (fun u _ ↦ Units.ext (ZMod.natCast_zmod_val _))
      (fun _ _ ↦ rfl)
  rw [reindex]
  calc ∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹)^2 = ∑ u : (ZMod p)ˣ, (u : ZMod p)^2 :=
        by simpa only [Equiv.inv_apply, Units.val_inv_eq_inv_val] using Equiv.sum_comp (Equiv.inv (ZMod p)ˣ) (fun u : (ZMod p)ˣ ↦ (u : ZMod p)^2)
    _ = 0 := by
      rw [FiniteField.sum_pow_units, ZMod.card, if_neg]
      exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)

theorem OMA.solution : OMA.R_OeisA7406_conjecture_R1.H1 := by
  intro p hp hprime
  let : Fact p.Prime := ⟨hprime⟩
  let F := (p - 1).factorial
  let S := ∑ k ∈ Ico 1 p, (1 : ℚ) / (k : ℚ)^2
  let N := ∑ k ∈ Ico 1 p, (F / k)^2
  have hk {k} (h : k ∈ Ico 1 p) : 0 < k ∧ k ≤ p - 1 := by
    obtain ⟨_, _⟩ := mem_Ico.mp h
    omega
  have cancel {k} (h : k ∈ Ico 1 p) : F / k * k = F :=
    Nat.div_mul_cancel (Nat.dvd_factorial (hk h).1 (hk h).2)
  have hsum : S * (F : ℚ)^2 = N := by
    simp only [S, N, Finset.sum_mul, Nat.cast_sum, Nat.cast_pow]
    apply sum_congr rfl
    intro k h
    have hprod : ((F / k : ℕ) : ℚ) * k = F := by exact_mod_cast cancel h
    have hne : (k : ℚ) ≠ 0 := by exact_mod_cast (hk h).1.ne'
    field_simp
    linear_combination -congrArg (fun z : ℚ ↦ z ^ 2) hprod
  have hN : (N : ZMod p) = 0 := by
    calc (N : ZMod p) = ∑ k ∈ Ico 1 p, (F : ZMod p)^2 * ((k : ZMod p)⁻¹)^2 := by
           simp only [N, Nat.cast_sum, Nat.cast_pow]
           apply sum_congr rfl
           intro k h
           have hprod : ((F / k : ℕ) : ZMod p) * k = F := by rw [← Nat.cast_mul, cancel h]
           have hne : (k : ZMod p) ≠ 0 :=
             mt (ZMod.natCast_eq_zero_iff k p).mp
               (Nat.not_dvd_of_pos_of_lt (hk h).1 (mem_Ico.mp h).2)
           rw [← mul_pow, ← hprod, mul_inv_cancel_right₀ hne]
         _ = 0 := by rw [← Finset.mul_sum, inverse_square_sum p hp, mul_zero]
  have hcross : S.num * (F : ℤ)^2 = (N : ℤ) * S.den := by
    have he := Rat.num_div_den S
    have hden : (S.den : ℚ) ≠ 0 := by exact_mod_cast S.den_ne_zero
    have hnum := (div_eq_iff hden).mp he
    exact_mod_cast (show (S.num : ℚ) * (F : ℚ)^2 = (N : ℚ) * S.den by
      rw [hnum, mul_right_comm, hsum])
  have hcrossmod := congrArg (fun z : ℤ ↦ (z : ZMod p)) hcross
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, hN, zero_mul] at hcrossmod
  have hF : (F : ZMod p) ≠ 0 :=
    mt (ZMod.natCast_eq_zero_iff F p).mp (fun h ↦ by
      have := hprime.dvd_factorial.mp h
      omega)
  have hnum := (mul_eq_zero.mp hcrossmod).resolve_right (pow_ne_zero _ hF)
  have hdvd := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd S.num p).mp hnum)
  rw [OeisA89026.a, if_pos hprime, Nat.gcd_eq_left_iff_dvd]
  have hi : Icc 1 (p - 1) = Ico 1 p := by ext; simp; omega
  simpa only [OeisA7406.a, hi, S] using hdvd
