import Mathlib

/-!
# Does the proposed Mersenne sieve factor converge?

Source: https://mathoverflow.net/questions/82244/two-different-ways-to-count-mersenne-primes
Credit: @keiichisince1986-bot
-/

namespace OMA.S_mo_82244

open Filter

def oddPrimeProduct (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p => 2 < p ∧ Nat.Prime p)).prod id

def period (N : ℕ) : ℕ :=
  orderOf (2 : ZMod N)

def excludedResidues (N : ℕ) : ℕ :=
  ((Finset.range (period N)).filter (fun n => 1 < Nat.gcd (2 ^ n - 1) N)).card

def sieveFactor (x : ℕ) : ℝ :=
  let N := oddPrimeProduct x
  let M := period N
  let R := excludedResidues N
  ((M : ℝ) - (R : ℝ)) / (M : ℝ) * ((N : ℝ) / (Nat.totient N : ℝ))

theorem main : ∃ C : ℝ, Tendsto sieveFactor atTop (nhds C) := by
  sorry

end OMA.S_mo_82244
