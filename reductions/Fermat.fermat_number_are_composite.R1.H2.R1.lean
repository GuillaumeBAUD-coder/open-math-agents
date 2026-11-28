import OMAReductions.R_Fermat_fermat_number_are_composite_R1

-- Reduction Fermat.fermat_number_are_composite.R1.H2.R1 of step Fermat.fermat_number_are_composite.R1.H2
-- Credit: @arindale
--
-- The open part is `F_n` composite for every `n ≥ 20`.  The only structural handle on
-- Fermat numbers in the pinned library is `Nat.fermat_primeFactors_one_lt`: a prime
-- divisor of `F_n` (n > 1) has the form `k * 2^(n+2) + 1`.  That pins the exponent
-- arithmetic but gives no fixed small prime for an infinite family, so there is no
-- cheap infinite sub-case.  Splitting by the parity of `n` separates the two regimes
-- of the exponent `2^n` (even vs. odd index) into independent targets; each is still
-- open, but they can be attacked by different arguments (e.g. explicit factor
-- certificates vs. algebraic identities between consecutive Fermat numbers).

namespace OMA.R_Fermat_fermat_number_are_composite_R1_H2_R1

/-- `F_n` is composite for even `n ≥ 20`. -/
def H1 : Prop :=
  ∀ n : ℕ, 20 ≤ n → n % 2 = 0 → ¬ Prime n.fermatNumber

/-- `F_n` is composite for odd `n ≥ 21`. -/
def H2 : Prop :=
  ∀ n : ℕ, 21 ≤ n → n % 2 = 1 → ¬ Prime n.fermatNumber

theorem main : H1 → H2 → OMA.R_Fermat_fermat_number_are_composite_R1.H2 := by
  intro h1 h2 n hn
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · exact h1 n hn h
  · exact h2 n (by omega) h

end OMA.R_Fermat_fermat_number_are_composite_R1_H2_R1
