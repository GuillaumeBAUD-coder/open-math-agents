import Mathlib

/-!
# Rainbow AP(4) in an almost equinumerous coloring

Source: https://www.openproblemgarden.org/op/rainbow_ap_4_in_an_almost_equinumerous_coloring
Credit: @ishaanzee

**Problem** (D. Conlon). Do 4-colorings of `ℤ_p`, for `p` a large prime, always contain a
rainbow `AP(4)` if each of the color classes is of size either `⌊p/4⌋` or `⌈p/4⌉`?

An arithmetic progression is rainbow if no two of its terms have the same color. For
comparison, there are equinumerous colorings of `ℤ_{4m}` with no rainbow `AP(4)`
(Conlon–Jungić–Radoičić).

Formalization: we state the affirmative answer. "For `p` a large prime" is read as "for every
sufficiently large prime `p`". A 4-coloring is a map `c : ZMod p → Fin 4`; the class of color
`k` has `Nat.card {x // c x = k}` elements, and `⌊p/4⌋`, `⌈p/4⌉` are `p / 4` and `(p + 3) / 4`
in natural-number division. An `AP(4)` in `ℤ_p` is `a, a + d, a + 2d, a + 3d` with common
difference `d ≠ 0`; it is rainbow when its four terms get four different colors.
-/

namespace OMA.S_opg_rainbow_ap_4_in_an_almost_equinumerous_coloring

/-- **Conlon's question**, affirmative form: for every sufficiently large prime `p`, every
4-coloring of `ℤ_p` whose color classes all have size `⌊p/4⌋` or `⌈p/4⌉` contains a rainbow
4-term arithmetic progression. -/
theorem main : ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p → ∀ c : ZMod p → Fin 4,
    (∀ k : Fin 4, Nat.card {x : ZMod p // c x = k} = p / 4 ∨
      Nat.card {x : ZMod p // c x = k} = (p + 3) / 4) →
    ∃ a d : ZMod p, d ≠ 0 ∧ Function.Injective fun i : Fin 4 => c (a + (i : ℕ) * d) := by
  sorry

end OMA.S_opg_rainbow_ap_4_in_an_almost_equinumerous_coloring
