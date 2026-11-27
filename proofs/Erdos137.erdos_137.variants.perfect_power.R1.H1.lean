import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1

-- Step Erdos137.erdos_137.variants.perfect_power.R1.H1: hypothesis H1 of reduction Erdos137.erdos_137.variants.perfect_power.R1
-- Credit: @OrangeHeadz

/-!
Informal plan (the case k = 2 of Erdős and Selfridge: (n + 1)(n + 2) is never a perfect power).

The product over Ioc n (n + 2) is (n + 1)(n + 2). The two factors are coprime, so if the
product is x ^ l then each factor is an l-th power (exists_eq_pow_of_mul_eq_pow in Mathlib):
n + 1 = d ^ l and n + 2 = e ^ l. Then d ≥ 1 and e > d, so for l = j + 2
  e ^ l ≥ (d + 1) ^ l ≥ d ^ j * (d + 1) ^ 2 = d ^ l + 2 d ^ (j + 1) + d ^ j ≥ d ^ l + 3,
contradicting e ^ l = d ^ l + 1.
-/

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H1 := by
  unfold OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H1
  intro n x l hl h
  have hprod : ∏ m ∈ Finset.Ioc n (n + 2), m = (n + 1) * (n + 2) := by
    rw [show n + 2 = (n + 1) + 1 from rfl, Finset.prod_Ioc_succ_top (by omega),
      Finset.prod_Ioc_succ_top (le_refl n), Finset.Ioc_self, Finset.prod_empty, one_mul]
  rw [hprod] at h
  have hcop : IsUnit (gcd (n + 1) (n + 2)) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff, show n + 2 = (n + 1) + 1 from rfl,
      Nat.gcd_self_add_right, Nat.gcd_one_right]
  have hcop' : IsUnit (gcd (n + 2) (n + 1)) := by
    rw [gcd_comm]
    exact hcop
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hcop h
  obtain ⟨e, he⟩ := exists_eq_pow_of_mul_eq_pow hcop' ((mul_comm _ _).trans h)
  obtain ⟨j, hj⟩ : ∃ j, l = j + 2 := ⟨l - 2, by omega⟩
  rw [hj] at hd he
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0] at hd
      simp at hd
    · exact h0
  have hde : d < e := (Nat.pow_lt_pow_iff_left (by omega : j + 2 ≠ 0)).mp (by omega)
  have h1 : (d + 1) ^ (j + 2) ≤ e ^ (j + 2) := Nat.pow_le_pow_left hde (j + 2)
  have h2 : d ^ j ≤ (d + 1) ^ j := Nat.pow_le_pow_left (Nat.le_succ d) j
  have h3 : 1 ≤ d ^ j := Nat.one_le_pow _ _ hd1
  have h4 : (d + 1) ^ (j + 2) = (d + 1) ^ j * (d + 1) ^ 2 := pow_add _ _ _
  have h5 : d ^ (j + 2) = d ^ j * d ^ 2 := pow_add _ _ _
  have h6 : d ^ j * (d + 1) ^ 2 ≤ (d + 1) ^ j * (d + 1) ^ 2 := Nat.mul_le_mul_right _ h2
  have h7 : d ^ j * (d + 1) ^ 2 = d ^ j * d ^ 2 + 2 * (d ^ j * d) + d ^ j := by ring
  have h8 : 1 ≤ d ^ j * d := Nat.mul_pos h3 hd1
  omega
