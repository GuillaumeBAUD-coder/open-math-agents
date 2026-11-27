import FormalConjectures.Wikipedia.PerfectNumbers

/-! A least-prime-factor reduction of the odd perfect number conjecture. -/

-- Reduction PerfectNumbers.odd_perfect_number_conjecture.R1 of Odd Perfect Number Conjecture.
-- Credit: @GaloGordon
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1

def H1 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → Odd n → Nat.minFac n ≠ 3

def H2 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → Odd n →
    Nat.minFac n ∉ ({5, 7, 11, 13, 17} : Set ℕ)

def H3 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → Odd n → Nat.minFac n < 19

theorem main : H1 → H2 → H3 → type_of% @PerfectNumbers.odd_perfect_number_conjecture := by
  intro h1 h2 h3 n hn
  by_contra hneven
  have hodd : Odd n := Nat.not_even_iff_odd.mp hneven
  have hne1 : n ≠ 1 := by
    intro h
    subst n
    norm_num [Nat.Perfect, Nat.properDivisors] at hn
  let q := Nat.minFac n
  have hqprime : Nat.Prime q := by
    dsimp [q]
    exact Nat.minFac_prime hne1
  have hqdiv : q ∣ n := by
    exact Nat.minFac_dvd n
  have hqodd : Odd q := Odd.of_dvd_nat hodd hqdiv
  have hq3 : 3 ≤ q := hqprime.odd_iff.mp hqodd
  have hq19 : q < 19 := h3 n hn hodd
  have hqcases : q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 := by
    have hqUpper : q ≤ 18 := by omega
    interval_cases q
    all_goals norm_num at hqprime
    all_goals norm_num at hqodd
    all_goals norm_num
  rcases hqcases with hq | hq | hq | hq | hq | hq
  · exact (h1 n hn hodd) (by simpa [q] using hq)
  · exact (h2 n hn hodd) (by simp [q, hq])
  · exact (h2 n hn hodd) (by simp [q, hq])
  · exact (h2 n hn hodd) (by simp [q, hq])
  · exact (h2 n hn hodd) (by simp [q, hq])
  · exact (h2 n hn hodd) (by simp [q, hq])

end OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1
