import Mathlib

/-!
# A000720: pi(n), the number of primes <= n. Sometimes called PrimePi(n) to distinguish it from the number 3.14159...

Source: https://oeis.org/A000720
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a000720

def primePi (n : ℕ) : ℕ :=
  (Finset.filter (fun m => Nat.Prime m) (Finset.range (n + 1))).card

theorem main : ∀ x y : ℕ, 2 ≤ x → 2 ≤ y →
    primePi x + primePi y ≥ primePi (x + y) := by
  sorry

end OMA.S_oeis_a000720
