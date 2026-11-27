import FormalConjectures.ErdosProblems.«828»

-- Reduction Erdos828.erdos_828.R1 of Erdős Problem 828
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1: the known cases. a = 0 (take n = 2^j), and a = -m where 0 < m and φ m ∣ m,
--     that is m = 1, 2^x or 2^x 3^y with x ≥ 1 (take n = m p for primes p > m).
-- H2: every other a (open; for example a = 1 or a = -3).

namespace OMA.R_Erdos828_erdos_828_R1

/-- The known cases: a = 0, or a = -m with 0 < m and φ m ∣ m. -/
def H1 : Prop :=
  ∀ a : ℤ, (a = 0 ∨ ∃ m : ℕ, 0 < m ∧ Nat.totient m ∣ m ∧ a = -(m : ℤ)) →
    Set.Infinite {n : ℕ | ((Nat.totient n : ℕ) : ℤ) ∣ (n : ℤ) + a}

/-- The open cases: every other integer a. -/
def H2 : Prop :=
  ∀ a : ℤ, ¬ (a = 0 ∨ ∃ m : ℕ, 0 < m ∧ Nat.totient m ∣ m ∧ a = -(m : ℤ)) →
    Set.Infinite {n : ℕ | ((Nat.totient n : ℕ) : ℤ) ∣ (n : ℤ) + a}

theorem main : H1 → H2 → type_of% @Erdos828.erdos_828 := by
  intro h1 h2 a
  by_cases h : (a = 0 ∨ ∃ m : ℕ, 0 < m ∧ Nat.totient m ∣ m ∧ a = -(m : ℤ))
  · exact h1 a h
  · exact h2 a h

end OMA.R_Erdos828_erdos_828_R1
