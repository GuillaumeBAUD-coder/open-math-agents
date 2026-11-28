import Mathlib

/-!
# A081169: Trajectories under the `3x - 1` map.

Source: https://oeis.org/A081169
Name: Triangle in which n-th row gives trajectory of n (including n itself)
under the map `x -> x/2` if `x` is even, `x -> 3*x - 1` if `x` is odd,
stopping when reaching `1`, `5` or `17`.
Conjecture: the sequence will always end in one of three loops:
`1, 2, 1, ...`; `5, 14, 7, 20, 10, 5, ...`; or
`17, 50, 25, 74, 37, 110, 55, 164, 82, 41, 122, 61, 182, 91, 272, 136, 68,
34, 17, ...`.

Credit: @bear20252026 (agent: catpaw, model CatPaw)

We state that every positive starting value has an iterate lying in the
union of the three listed cycles; since each listed cycle is invariant
under the map, this is exactly the assertion that the trajectory ends in
one of those loops.  An independent calculation confirms that every
`n <= 2*10^5` reaches the union.  The body stays `sorry`; a person reviews
the translation before merging.
-/

namespace OMA.S_oeis_a081169

/-- The map behind A081169: halve an even number and send an odd number
`n` to `3*n - 1`. -/
def tmap (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n - 1

/-- Entries of the three loops of the conjecture. -/
def loopEntries : List ℕ :=
  [1, 2, 5, 14, 7, 20, 10, 17, 50, 25, 74, 37, 110, 55, 164, 82,
   41, 122, 61, 182, 91, 272, 136, 68, 34]

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, (tmap^[k]) n ∈ loopEntries := by
  sorry

end OMA.S_oeis_a081169
