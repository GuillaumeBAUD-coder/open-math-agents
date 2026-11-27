import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Ring.Pow

/-! The two-term case of the Erdős–Selfridge perfect-power theorem. -/

open Finset

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H1 := by
  intro n x l hl hp
  have hi : Ioc n (n + 2) = {n + 1, n + 2} := by
    ext i
    simp only [mem_Ioc, mem_insert, mem_singleton]
    omega
  have hmem : n + 1 ∉ ({n + 2} : Finset ℕ) := by
    simp only [mem_singleton]
    omega
  rw [hi, prod_insert hmem, prod_singleton] at hp
  have hc : Nat.Coprime (n + 1) (n + 2) := by
    change Nat.Coprime (n + 1) ((n + 1) + 1)
    rw [Nat.coprime_self_add_right]
    exact Nat.coprime_one_right _
  have hunit {a b : ℕ} (hab : a.Coprime b) : IsUnit (gcd a b) := by
    rw [gcd_eq_nat_gcd, hab.gcd_eq_one]
    exact isUnit_one
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow (hunit hc) hp
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow (hunit hc.symm) ((mul_comm _ _).trans hp)
  have hl0 : l ≠ 0 := by omega
  have ha0 : 0 < a := by
    by_contra! h
    rw [show a = 0 by omega, zero_pow hl0] at ha
    omega
  have hab : a < b := by
    by_contra! h
    have := Nat.pow_le_pow_left h l
    omega
  have hterm : 2 ≤ l * a ^ (l - 1) := by
    calc
      2 ≤ l := hl
      _ = l * 1 := (mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ ha0)
  have hgap : a ^ l + 2 ≤ (a + 1) ^ l := by
    calc
      a ^ l + 2 ≤ a ^ l + l * a ^ (l - 1) := Nat.add_le_add_left hterm _
      _ ≤ _ := by simpa only [Nat.cast_id, mul_one] using
        (pow_add_mul_le_add_pow (b := (1 : ℕ)) (Nat.zero_le a) (Nat.zero_le _) l)
  have hle := Nat.pow_le_pow_left (show a + 1 ≤ b by omega) l
  omega
