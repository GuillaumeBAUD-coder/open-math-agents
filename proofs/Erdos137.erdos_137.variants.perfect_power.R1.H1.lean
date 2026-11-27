import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1

-- Credit: @sturdy4days
-- Coprimality forces each factor to be an lth power. Two positive lth
-- powers have a gap of at least two when l is at least two.
theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H1 := by
  intro n x l hl h
  have hI : Finset.Ioc n (n + 2) = {n + 1, n + 2} := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hI, Finset.prod_pair (by omega : n + 1 ≠ n + 2)] at h
  have hc : Nat.Coprime (n + 1) (n + 2) :=
    Nat.coprime_self_add_right.mpr (Nat.coprime_one_right (n + 1))
  have unit_gcd (a b : ℕ) (hcab : Nat.Coprime a b) : IsUnit (gcd a b) := by
    rw [gcd_eq_nat_gcd, hcab.gcd_eq_one]
    exact isUnit_one
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow (unit_gcd _ _ hc) h
  have hrev : (n + 2) * (n + 1) = x ^ l := by rwa [Nat.mul_comm]
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow (unit_gcd _ _ hc.symm) hrev
  have ha_pos : 0 < a := by
    by_contra! hz
    have ha0 : a = 0 := by omega
    rw [ha0, zero_pow (by omega : l ≠ 0)] at ha
    omega
  have hab : a < b := by
    by_contra! hba
    have hpow := Nat.pow_le_pow_left hba l
    omega
  cases l with
  | zero => omega
  | succ k =>
    have hpow := Nat.pow_lt_pow_left hab (by omega : k ≠ 0)
    have hmul := Nat.mul_le_mul (show a ^ k + 1 ≤ b ^ k from hpow)
      (show a + 1 ≤ b from hab)
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hmul
    rw [pow_succ] at ha hb
    omega
