import OMAReductions.R_oeis_a070247_R1

-- Each row supplies a proper divisor of the corresponding generalized Fermat number.
-- Factors for k = 2 through 13 are listed in OEIS A185121. The last is from FactorDB.
namespace OMA.Fermat10

def squareValue : ℕ → ℕ
  | 0 => 10
  | k + 1 => let x := squareValue k; x * x

lemma squareValue_eq (k : ℕ) : squareValue k = 10 ^ (2 ^ k) := by
  induction k with
  | zero => simp [squareValue]
  | succ k ih => rw [squareValue, ih, pow_succ 2 k, pow_mul, pow_two]

end OMA.Fermat10

theorem OMA.solution : OMA.R_oeis_a070247_R1.H1 := by
  intro k hk hmax
  rw [← OMA.Fermat10.squareValue_eq]
  interval_cases k
  · exact Nat.not_prime_of_dvd_of_lt (m := 73) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
  · exact Nat.not_prime_of_dvd_of_lt (m := 17) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
  · exact Nat.not_prime_of_dvd_of_lt (m := 353) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
  · exact Nat.not_prime_of_dvd_of_lt (m := 19841) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
  · exact Nat.not_prime_of_dvd_of_lt (m := 1265011073) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
  · exact Nat.not_prime_of_dvd_of_lt (m := 257) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
  · exact Nat.not_prime_of_dvd_of_lt (m := 10753) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
  · exact Nat.not_prime_of_dvd_of_lt (m := 1514497) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
  · exact Nat.not_prime_of_dvd_of_lt (m := 1856104284667693057) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
  · exact Nat.not_prime_of_dvd_of_lt (m := 106907803649) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
  · exact Nat.not_prime_of_dvd_of_lt (m := 458924033) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
  · exact Nat.not_prime_of_dvd_of_lt (m := 3635898263938497962802538435084289) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
  · exact Nat.not_prime_of_dvd_of_lt (m := 1702047085242613845984907230501142529) (Nat.dvd_of_mod_eq_zero (by decide)) (by decide) (by decide)
