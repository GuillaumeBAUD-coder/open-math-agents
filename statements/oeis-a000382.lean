import Mathlib

/-!
# OEIS A000382: restricted permutations

Sources: https://oeis.org/A000382 and https://oeis.org/A008305
Credit: @sassmama27
-/

namespace OMA.S_oeis_a000382

/-- A000382 is the fourth column of A008305 divided by four. The fourth
column counts permutations in which each forward cyclic displacement
is between zero and three. -/
noncomputable def restrictedPermutations (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun σ => ∀ i : Fin n, ((σ i).val + n - i.val) % n < 4)).card / 4

/-- The fourth term is the first for which all three preceding terms are
in the published range, whose first index is four. -/
theorem main (n : ℕ) (hn : 7 ≤ n) :
    (restrictedPermutations n : ℤ) =
      (restrictedPermutations (n - 1) : ℤ) +
      (restrictedPermutations (n - 2) : ℤ) +
      (restrictedPermutations (n - 3) : ℤ) - 2 := by
  sorry

end OMA.S_oeis_a000382
