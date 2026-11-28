import OMAStatements.S_oeis_a023365

namespace OMA.P_oeis_a023365

open OMA.S_oeis_a023365

lemma form (n : ℕ) : ∃ m : ℤ, Odd m ∧ b n = (m : ℚ) / ((2 : ℚ) ^ (3 ^ n)) := by
  induction n with
  | zero => exact ⟨1, odd_one, by simp [b]⟩
  | succ n ih =>
    obtain ⟨m, hm, hb⟩ := ih
    have hk : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨j, hj⟩ : ∃ j, 3 ^ n = j + 1 := ⟨3 ^ n - 1, by omega⟩
    refine ⟨m * (3 * 2 ^ (2 * j + 1) - m ^ 2), ?_, ?_⟩
    · apply hm.mul
      have h1 : Even ((3 : ℤ) * 2 ^ (2 * j + 1)) := by
        rw [pow_succ]
        exact ⟨3 * 2 ^ (2 * j), by ring⟩
      exact h1.sub_odd (hm.pow)
    · rw [b, hb, hj, pow_succ 3 n, hj]
      have h2 : (2 : ℚ) ≠ 0 := by norm_num
      push_cast
      field_simp
      ring

end OMA.P_oeis_a023365

theorem OMA.solution : type_of% @OMA.S_oeis_a023365.main := by
  intro n
  obtain ⟨m, hm, hb⟩ := OMA.P_oeis_a023365.form n
  rw [hb, OMA.S_oeis_a023365.a, Nat.add_sub_cancel]
  have hpos : (0 : ℤ) < 2 ^ (3 ^ n) := by positivity
  have hcop : m.natAbs.Coprime ((2 : ℤ) ^ (3 ^ n)).natAbs := by
    rw [Int.natAbs_pow]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    show Nat.Coprime 2 m.natAbs
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs, dvd_abs]
    intro h2
    exact (Int.not_even_iff_odd.mpr hm) ((even_iff_two_dvd).mpr h2)
  have := Rat.den_div_eq_of_coprime hpos hcop
  have e : ((m : ℚ) / (2 : ℚ) ^ (3 ^ n)) = ((m : ℚ) / ((2 ^ (3 ^ n) : ℤ) : ℚ)) := by push_cast; rfl
  rw [e]
  exact_mod_cast this
