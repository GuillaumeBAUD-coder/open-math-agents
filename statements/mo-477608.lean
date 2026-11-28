import Mathlib

/-!
# A strengthening of an inequality for posets by Chan-Pak

Source: https://mathoverflow.net/questions/477608
Credit: @JeremyDevs

Question (MathOverflow 477608, 2024). Suppose that `P` is a (finite) poset, `x` and `y` are two
minimal elements of `P`, and `e(P)` denotes the number of linear extensions of `P`. Chan and Pak
proved `e(P) e(P - {x,y}) / (e(P - x) e(P - y)) ≤ 2`. If we further suppose that there does not
exist an element `z ∈ P` which (i) covers both `x` and `y` and (ii) does not cover any other
elements of `P`, then is it true that the upper bound can be strengthened to `3/2`? Is there an
easy counterexample?

The answer at the source is that the strengthening is false, the two-element antichain being a
counterexample (there `e(P) = 2` and `e(P - {x,y}) = e(P - x) = e(P - y) = 1`). `main` states
this negative answer: there is a finite poset with two distinct minimal elements `x, y`
satisfying the extra hypothesis for which the ratio exceeds `3/2`.

Conventions:
* A poset is a type with a `PartialOrder`, assumed `Finite`.
* A linear extension of a poset `α` with `n` elements is an injective strictly monotone map
  `f : α → ℕ` with all values `< n` (that is, an order-preserving bijection onto
  `{0, ..., n-1}`); `numLinExt α` is the number of these, so the empty poset has exactly one.
* `P - x`, `P - y`, `P - {x,y}` are the subtypes `{a // a ≠ x}`, `{a // a ≠ y}`,
  `{a // a ≠ x ∧ a ≠ y}` with the induced order.
* "Minimal" is `IsMin`; "`z` covers `w`" is `w ⋖ z` (`CovBy`).
* The ratio exceeding `3/2` is written without division:
  `3/2 * (e(P - x) * e(P - y)) < e(P) * e(P - {x,y})` in `ℚ` (the denominators are positive).
-/

namespace OMA.S_mo_477608

/-- The number of linear extensions of the poset `α`: injective strictly monotone maps to `ℕ`
with values below the number of elements. -/
noncomputable def numLinExt (α : Type) [PartialOrder α] : ℕ :=
  Nat.card {f : α → ℕ // StrictMono f ∧ Function.Injective f ∧ ∀ a, f a < Nat.card α}

/-- The bound `2` of Chan and Pak cannot be improved to `3/2` under the extra hypothesis that no
element covers exactly `x` and `y`. -/
theorem main :
    ∃ (P : Type) (_ : PartialOrder P) (_ : Finite P) (x y : P),
      x ≠ y ∧ IsMin x ∧ IsMin y ∧
      (¬ ∃ z : P, x ⋖ z ∧ y ⋖ z ∧ ∀ w : P, w ⋖ z → w = x ∨ w = y) ∧
      (3 / 2 : ℚ) * ((numLinExt {a : P // a ≠ x} : ℚ) * (numLinExt {a : P // a ≠ y} : ℚ)) <
        (numLinExt P : ℚ) * (numLinExt {a : P // a ≠ x ∧ a ≠ y} : ℚ) := by
  sorry

end OMA.S_mo_477608
