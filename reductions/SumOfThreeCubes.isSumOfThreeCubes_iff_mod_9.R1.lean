import FormalConjectures.Wikipedia.SumOfThreeCubes

-- Reduction SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1 of Sum of three cubes
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Sum of three cubes: the two directions of the mod 9 criterion

The open problem is the equivalence

`IsSumOfThreeCubes n ↔ n ≢ 4, 5 (mod 9)`.

Its two directions have completely different content.

* `H1` is the elementary direction: a cube is `0, ±1 (mod 9)`, so a sum of three cubes is
  never `4` or `5 (mod 9)`.  The module already proves it as
  `SumOfThreeCubes.mod_9_of_isSumOfThreeCubes`; it is isolated here so that the remaining
  step is exactly the open direction.
* `H2` is the open direction: every integer outside the two forbidden classes is a sum of
  three cubes.  This is the whole difficulty of the problem — the cases `33` and `42` were
  only settled in 2019.

The reduction's content is the assembly `⟨H1, H2⟩`.
-/

namespace OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1

/-- The elementary direction: a sum of three integer cubes is never `4` or `5` mod `9`. -/
def H1 : Prop :=
  ∀ n : ℤ, SumOfThreeCubes.IsSumOfThreeCubes n →
    ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])

/-- The open direction: every integer that is not `4` or `5` mod `9` is a sum of three cubes. -/
def H2 : Prop :=
  ∀ n : ℤ, ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9]) →
    SumOfThreeCubes.IsSumOfThreeCubes n

theorem main : H1 → H2 → type_of% @SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9 := by
  intro h1 h2 n
  exact ⟨h1 n, h2 n⟩

end OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1
