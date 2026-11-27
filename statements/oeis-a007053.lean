import Mathlib

/-!
# A007053: Number of primes <= 2^n.

Source: https://oeis.org/A007053
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a007053

def primePi (n : ℕ) : ℕ :=
  (Finset.filter (fun m => Nat.Prime m) (Finset.range (n + 1))).card

def IsPerfectPower (n : ℕ) : Prop :=
  ∃ x m : ℕ, 1 < x ∧ 1 < m ∧ n = x ^ m

theorem main : primePi (2 ^ 3) = 4 ∧
    ∀ n : ℕ, 3 < n → ¬ IsPerfectPower (primePi (2 ^ n)) := by
  sorry

end OMA.S_oeis_a007053
