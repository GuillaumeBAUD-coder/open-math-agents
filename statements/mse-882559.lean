import Mathlib

/-!
# On the indivisibility of odd perfect numbers by small numbers

Source: https://math.stackexchange.com/questions/882559
(cross-posted as https://mathoverflow.net/q/178286)

The source asks: "Is there a positive ODD integer `x < 105` for which it is known that `x` is
NOT a divisor of an odd perfect number?" The bound `105 = 3·5·7` is used because no odd perfect
number is divisible by 105 (Sylvester).

Reading choices (for the reviewer):
* "For which it is known" cannot be formalized; it is dropped. The statement asserts the
  mathematical content: some odd `x < 105` divides no odd perfect number.
* `x = 1` divides every integer, so it is excluded with `1 < x`. The source excludes it
  implicitly, since otherwise the question is trivial.
* "Perfect" is Mathlib's `Nat.Perfect` (the proper divisors sum to `n`, and `0 < n`).
* Like every statement about odd perfect numbers, this one holds vacuously if there is no odd
  perfect number. The source's question has the same feature, and it is not removed here.
* Already known on the page: the analogous claim for `x = 105` (Sylvester), and Roberts'
  congruences (`N ≡ 1 mod 12`, `N ≡ 81 mod 324` or `N ≡ 117 mod 468`). The source says these
  do not settle the question. The open content is `x < 105`.

Numeric sanity checks (the `example`s below): `Nat.Perfect` holds at 6 and 28 and fails at 12
and 15; the candidate range has 51 odd `x` with `1 < x < 105`. Outside the file, a Python
enumeration found no odd perfect number below `10^6`.
-/

namespace OMA.S_mse_882559

example : Nat.Perfect 6 := by unfold Nat.Perfect; decide
example : Nat.Perfect 28 := by unfold Nat.Perfect; decide
example : ¬ Nat.Perfect 12 := by unfold Nat.Perfect; decide
example : ¬ Nat.Perfect 15 := by unfold Nat.Perfect; decide
example : ((Finset.range 105).filter (fun x => Odd x ∧ 1 < x)).card = 51 := by decide

theorem main :
    ∃ x : ℕ, Odd x ∧ 1 < x ∧ x < 105 ∧ ∀ N : ℕ, Odd N → N.Perfect → ¬ x ∣ N := by
  sorry

end OMA.S_mse_882559
