import Mathlib

/-!
# A006370: The Collatz or 3x+1 map

Source: https://oeis.org/A006370
Credit: @stoyanov-x

The OEIS entry asks whether the following process always reaches `1`: if the
current number is even, divide it by two; otherwise multiply it by three and
add one. It states that the conjectured answer is yes.
-/

namespace OMA.S_oeis_a006370

/-- One step of the Collatz map. -/
def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/-- The Collatz process started at `n` reaches `1` after some number of steps. -/
def ReachesOne (n : ℕ) : Prop :=
  ∃ k : ℕ, collatzStep^[k] n = 1

/-- The Collatz conjecture, in the form stated in the OEIS entry. -/
theorem main : ∀ n : ℕ, 0 < n → ReachesOne n := by
  sorry

end OMA.S_oeis_a006370
