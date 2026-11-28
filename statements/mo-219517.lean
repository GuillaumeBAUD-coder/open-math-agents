import Mathlib

/-!
# Order of zeros for sparse polynomials in positive characteristic

Source: Brando, https://mathoverflow.net/questions/219517 (CC BY-SA 3.0).
Credit: @connoranderson.

Vesselin Dimitrov gives the sharp bound in the source comments. If a
nonzero polynomial has multiplicity m at a nonzero point, it has at least
the product of one plus each base-p digit of m many nonzero coefficients.
The binomial power attains the minimum for each m.
-/

namespace OMA.S_mo_219517

open Polynomial

def digitBound (p m : ℕ) : ℕ := ((Nat.digits p m).map (fun d => d+1)).prod

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p]
    (c : K), c ≠ 0 →
    (∀ f : K[X], f ≠ 0 → digitBound p (f.rootMultiplicity c) ≤ f.support.card) ∧
    (∀ m : ℕ, ((X-C c)^m).rootMultiplicity c = m ∧
      ((X-C c)^m).support.card = digitBound p m) := by
  sorry

end OMA.S_mo_219517
