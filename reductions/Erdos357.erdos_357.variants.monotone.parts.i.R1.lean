import FormalConjectures.ErdosProblems.«357»

-- Reduction Erdos357.erdos_357.variants.monotone.parts.i.R1 of Erdős problem 357 (monotone variant)
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The monotone variant of Erdős 357 is the strict problem

`h n` is the largest `k` with integers `1 ≤ a_1 ≤ … ≤ a_k ≤ n` whose sums over intervals of
consecutive indices are all distinct; `f n` is the same with `a_1 < … < a_k`.

* `H1` is the statement of the main open problem `Erdos357.erdos_357.parts.i`: `f n = o(n)`.
  It is the only open input.
* `H2` says `h n = f n`. It is elementary: a singleton `{i}` is an interval of indices, so distinct
  interval sums force `a` to be injective, and a monotone injective sequence is strictly monotone.
  Hence the two sets of admissible `k` coincide.

This is a structural identification of the variant with the main problem, not a weakening of it:
by `H2` the target and `H1` are equivalent.
-/

namespace OMA.R_Erdos357_erdos_357_variants_monotone_parts_i_R1

open Filter Asymptotics

/-- Erdős 357, part (i): `f n = o(n)` for strictly increasing sequences. -/
def H1 : Prop :=
  (fun n ↦ (Erdos357.f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ))

/-- Monotone sequences with distinct interval sums are strictly monotone, so `h = f`. -/
def H2 : Prop :=
  ∀ n : ℕ, Erdos357.h n = Erdos357.f n

theorem main : H1 → H2 → type_of% @Erdos357.erdos_357.variants.monotone.parts.i := by
  intro h1 h2
  have : (fun n ↦ (Erdos357.h n : ℝ)) = (fun n ↦ (Erdos357.f n : ℝ)) := by
    funext n
    rw [h2 n]
  rw [this]
  exact h1

end OMA.R_Erdos357_erdos_357_variants_monotone_parts_i_R1
