import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1
import Mathlib

-- Step Erdos137.erdos_137.variants.perfect_power.R1.H1: hypothesis H1 of reduction Erdos137.erdos_137.variants.perfect_power.R1
-- Credit: @ivillar
-- H1 := ∀ (n x l : ℕ), 2 ≤ l → (∏ m ∈ Ioc n (n + 2), m) ≠ x ^ l
-- Proof: n+1 and n+2 are coprime, so both are l-th powers a^l and b^l;
-- then b^l = a^l + 1 with 1 ≤ a < b, impossible since (a+1)^l ≥ a^l + 2.

open Finset

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H1 := by
  unfold OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H1
  intro n x l hl h
  have hset : Ioc n (n + 2) = {n + 1, n + 2} := by
    ext m
    simp only [mem_Ioc, mem_insert, mem_singleton]
    omega
  have hprod : (∏ m ∈ Ioc n (n + 2), m) = (n + 1) * (n + 2) := by
    rw [hset, prod_insert (by simp)]
    simp
  rw [hprod] at h
  have hcop : Nat.Coprime (n + 1) (n + 2) := by
    rw [show n + 2 = (n + 1) + 1 by ring]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hu1 : IsUnit (GCDMonoid.gcd (n + 1) (n + 2)) := by
    rw [Nat.isUnit_iff]
    exact hcop
  have hu2 : IsUnit (GCDMonoid.gcd (n + 2) (n + 1)) := by
    rw [Nat.isUnit_iff]
    exact hcop.symm
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow hu1 h
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow hu2 (by rw [mul_comm]; exact h)
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 2 := ⟨l - 2, by omega⟩
  have hba : b ^ (k + 2) = a ^ (k + 2) + 1 := by omega
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hlt : a < b := by
    have : a ^ (k + 2) < b ^ (k + 2) := by omega
    exact lt_of_pow_lt_pow_left₀ (k + 2) (Nat.zero_le _) this
  have hb1 : (a + 1) ^ (k + 2) ≤ b ^ (k + 2) := Nat.pow_le_pow_left hlt _
  have h2 : 2 ≤ (a + 1) ^ (k + 1) := by
    calc 2 ≤ a + 1 := by omega
      _ = (a + 1) ^ 1 := (pow_one _).symm
      _ ≤ (a + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : a ^ (k + 1) ≤ (a + 1) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
  have h4 : (a + 1) ^ (k + 2) = (a + 1) ^ (k + 1) * a + (a + 1) ^ (k + 1) := by ring
  have h5 : a ^ (k + 2) = a ^ (k + 1) * a := by ring
  have h6 : a ^ (k + 1) * a ≤ (a + 1) ^ (k + 1) * a := Nat.mul_le_mul_right _ h3
  omega
