import OMAStatements.S_oeis_a130187

namespace OMA.P130187

open OMA.S_oeis_a130187

lemma fact_ne (k : ℕ) : (k.factorial : ℚ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero k

/-- The closed form of r(n) read off from the exponential generating function. -/
lemma r_eq (n : ℕ) :
    r n = ((2 * n + 1).factorial : ℚ) / ((4 : ℚ) ^ n * ((n + 1).factorial : ℚ)) := by
  unfold r z zEgf expSq
  rw [PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  have e1 : (2 * n + 1 + 1) % 2 = 0 := by omega
  have e2 : (2 * n + 1 + 1) / 2 = n + 1 := by omega
  have e3 : ¬ (2 * n + 1 + 1 = 0) := by omega
  rw [if_pos e1, if_neg e3, e2]
  have h := fact_ne (n + 1)
  field_simp
  ring

/-- Odd double factorials are odd. -/
lemma df_odd (n : ℕ) : Nat.doubleFactorial (2 * n + 1) % 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
    rw [e, Nat.doubleFactorial_add_two, Nat.mul_mod, ih]
    omega

/-- Every odd number up to 2n+1 divides (2n+1)!!. -/
lemma odd_dvd (n : ℕ) : ∀ j, j ≤ n → (2 * j + 1) ∣ Nat.doubleFactorial (2 * n + 1) := by
  induction n with
  | zero =>
    intro j hj
    have h0 : j = 0 := by omega
    subst h0
    simp
  | succ n ih =>
    intro j hj
    have e : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
    rw [e, Nat.doubleFactorial_add_two]
    rcases Nat.lt_or_ge j (n + 1) with h | h
    · exact Dvd.dvd.mul_left (ih j (by omega)) _
    · have h1 : 2 * j + 1 = 2 * n + 1 + 2 := by omega
      rw [h1]
      exact Nat.dvd_mul_right _ _

end OMA.P130187

open OMA.S_oeis_a130187 OMA.P130187 in
theorem OMA.solution : type_of% @OMA.S_oeis_a130187.main := by
  intro n
  obtain ⟨v, hv⟩ : ∃ v, v = padicValNat 2 (n + 1) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = Nat.doubleFactorial (2 * n + 1) := ⟨_, rfl⟩
  have hdvd : 2 ^ v ∣ n + 1 := by
    rw [hv]
    exact pow_padicValNat_dvd
  obtain ⟨q, hq⟩ := hdvd
  have hqdef : oddPart (n + 1) = q := by
    unfold oddPart
    rw [← hv]
    have h0 : (n + 1) / 2 ^ v = (2 ^ v * q) / 2 ^ v := by rw [← hq]
    rw [h0]
    exact Nat.mul_div_cancel_left q (by positivity)
  have hqodd : q % 2 = 1 := by
    by_contra hc
    have h2 : 2 ∣ q := by omega
    obtain ⟨s, hs⟩ := h2
    have hnd : ¬ 2 ^ (padicValNat 2 (n + 1) + 1) ∣ (n + 1) :=
      pow_succ_padicValNat_not_dvd (by omega)
    apply hnd
    rw [← hv]
    refine ⟨s, ?_⟩
    rw [hq, hs]
    ring
  have hqle : q ≤ n + 1 := Nat.le_of_dvd (by omega) ⟨2 ^ v, by rw [hq]; ring⟩
  have hqD : q ∣ D := by
    have h := odd_dvd n (q / 2) (by omega)
    have e : 2 * (q / 2) + 1 = q := by omega
    rw [e] at h
    rw [hD]
    exact h
  obtain ⟨t, ht⟩ := hqD
  have hDodd : (q * t) % 2 = 1 := by
    rw [← ht, hD]
    exact df_odd n
  have htodd : t % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · rw [Nat.mul_mod, h] at hDodd
      simp at hDodd
    · exact h
  have h1 : (2 * n + 1).factorial = D * (2 ^ n * n.factorial) := by
    rw [hD, Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]
  have h2 : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
  have h4 : (4 : ℚ) ^ n = 2 ^ n * 2 ^ n := by
    rw [← mul_pow]
    norm_num
  have hq0 : (q : ℚ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  have hf := fact_ne n
  have hr : r n = ((t : ℤ) : ℚ) / (((2 : ℤ) ^ (n + v) : ℤ) : ℚ) := by
    rw [r_eq, h1, h2, h4]
    have hc : ((n + 1 : ℕ) : ℚ) = (2 : ℚ) ^ v * (q : ℚ) := by
      rw [hq]
      push_cast
      ring
    rw [ht]
    push_cast at hc ⊢
    rw [hc]
    field_simp
    ring
  have hcop : Nat.Coprime (t : ℤ).natAbs (((2 : ℤ) ^ (n + v) : ℤ)).natAbs := by
    rw [Int.natAbs_natCast, Int.natAbs_pow]
    apply Nat.Coprime.pow_right
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)).symm
  have ha : a n = (t : ℤ) := by
    unfold a
    rw [hr]
    exact Rat.num_div_eq_of_coprime (by positivity) hcop
  rw [ha, hqdef, ← hD, ht]
  push_cast
  field_simp
