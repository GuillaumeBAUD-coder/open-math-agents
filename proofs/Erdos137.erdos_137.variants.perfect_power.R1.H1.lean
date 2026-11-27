import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1

-- Step Erdos137.erdos_137.variants.perfect_power.R1.H1: hypothesis H1 of reduction Erdos137.erdos_137.variants.perfect_power.R1
-- Credit: @ronak14p
-- H1 := ∀ (n x l : ℕ), 2 ≤ l → (∏ m ∈ Ioc n (n + 2), m) ≠ x ^ l  -- Below the least prime at least k, Bertrand's postulate provides -- a prime that occurs exactly once in the product.

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H1 := by
  intro n x l hl h
  have hp : ∏ m ∈ Finset.Ioc n (n + 2), m = (n + 1) * (n + 2) := by
    rw [Finset.prod_Ioc_succ_top (by omega), Nat.Ioc_succ_singleton, Finset.prod_singleton]
  rw [hp] at h
  have hcop : Nat.Coprime (n + 1) (n + 2) := by
    have : n + 2 = (n + 1) + 1 := by omega
    rw [this]; exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hu : IsUnit (GCDMonoid.gcd (n + 1) (n + 2)) := by
    rw [Nat.isUnit_iff]; exact hcop
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow hu h
  have hu' : IsUnit (GCDMonoid.gcd (n + 2) (n + 1)) := by
    rw [Nat.isUnit_iff]; exact hcop.symm
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow hu' ((mul_comm _ _).trans h)
  have hl0 : l ≠ 0 := by omega
  have hab : a < b := by
    have : a ^ l < b ^ l := by omega
    exact lt_of_pow_lt_pow_left₀ l (Nat.zero_le _) this
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0; rw [zero_pow hl0] at ha; omega
    · exact h0
  have key : a ^ l + 2 ≤ (a + 1) ^ l := by
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 2 := ⟨l - 2, by omega⟩
    have hk : a ^ k ≤ (a + 1) ^ k := Nat.pow_le_pow_left (by omega) k
    have hk1 : 1 ≤ a ^ k := Nat.one_le_pow _ _ ha1
    have e1 : (a + 1) ^ (k + 2) = (a + 1) ^ k * (a + 1) ^ 2 := by ring
    have e2 : a ^ (k + 2) = a ^ k * a ^ 2 := by ring
    rw [e1, e2]
    nlinarith
  have hmono : (a + 1) ^ l ≤ b ^ l := Nat.pow_le_pow_left hab l
  omega
