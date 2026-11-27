import Mathlib

/-!
# Concavity of van der Waerden numbers

Source: https://www.openproblemgarden.org/op/concavity_of_van_der_waerden_numbers
Credit: @Hyvok

Posed by Bruce M. Landman (stated in 2000); see B. Landman and A. Robertson, Ramsey Theory on
the Integers, AMS 2003, and A. Khodkar and B. Landman, Recent progress in Ramsey theory on the
integers, in Combinatorial Number Theory, de Gruyter 2007, pp. 305-313.

Informal statement (as in the source): for positive integers `k` and `ℓ`, the mixed van der
Waerden number `w(k, ℓ)` is the least positive integer `n` such that every red-blue colouring
of `[1, n]` admits either a `k`-term red arithmetic progression or an `ℓ`-term blue arithmetic
progression.

Conjecture (Landman): for all `k` and `ℓ` with `k ≥ ℓ`, `w(k, ℓ) ≥ w(k + 1, ℓ - 1)`.

Formalization notes:
- A red-blue colouring of `[1, n]` is modelled as a map `c : ℕ → Bool` (`true` = red,
  `false` = blue); only its values on `[1, n]` matter, so this is the same as quantifying over
  colourings of `[1, n]`.
- An `m`-term arithmetic progression in `[1, n]` is `a, a + d, ..., a + (m - 1) d` with
  `1 ≤ a`, common difference `d ≥ 1` (the standard convention: `d = 0` would make the problem
  trivial) and `a + (m - 1) d ≤ n`.
- `w(k, ℓ)` is the infimum (`sInf`) of the set of positive integers `n` with the property.
  This set is nonempty by van der Waerden's theorem, and it is upward closed, so `sInf` is
  exactly the least such `n`.
- The source requires `k` and `ℓ` to be positive integers, so for `w(k + 1, ℓ - 1)` to be
  defined we need `ℓ - 1 ≥ 1`, i.e. `ℓ ≥ 2`. Together with `k ≥ ℓ` this is the range of `main`.
  (For `ℓ = 1` the inequality would involve the meaningless `w(k + 1, 0)`.)
- Sanity check by brute force with this exact definition (outside this file):
  `w(2,2) = 3`, `w(3,2) = 6`, `w(4,2) = 7`, `w(5,2) = 10`, `w(3,3) = 9`, `w(4,3) = 18`,
  agreeing with the known values.
-/

namespace OMA.S_opg_concavity_of_van_der_waerden_numbers

/-- The colouring `c` has an `m`-term arithmetic progression of colour `b` inside `[1, n]`:
`a, a + d, ..., a + (m - 1) d` with `1 ≤ a`, `0 < d` and `a + (m - 1) d ≤ n`. -/
def HasMonoAP (c : ℕ → Bool) (b : Bool) (m n : ℕ) : Prop :=
  ∃ a d : ℕ, 1 ≤ a ∧ 0 < d ∧ a + (m - 1) * d ≤ n ∧ ∀ i < m, c (a + i * d) = b

/-- The mixed van der Waerden number `w(k, ℓ)`: the least positive integer `n` such that every
red-blue colouring of `[1, n]` has a red `k`-term or a blue `ℓ`-term arithmetic progression. -/
noncomputable def w (k l : ℕ) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ ∀ c : ℕ → Bool, HasMonoAP c true k n ∨ HasMonoAP c false l n}

/-- **Concavity of van der Waerden numbers (Landman).** For positive integers `k ≥ ℓ` with
`ℓ - 1` positive, `w(k, ℓ) ≥ w(k + 1, ℓ - 1)`. -/
theorem main : ∀ k l : ℕ, 2 ≤ l → l ≤ k → w (k + 1) (l - 1) ≤ w k l := by
  sorry

end OMA.S_opg_concavity_of_van_der_waerden_numbers
