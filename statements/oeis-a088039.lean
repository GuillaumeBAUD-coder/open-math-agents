import Mathlib

/-!
# OEIS A088039: Barker's closed form, recurrence and g.f. for the smallest k > 1 with k^3 ≡ 1 modulo an n-th power

Source: https://oeis.org/A088039 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry (Amarnath Murthy, Sep 19 2003), offset 1: Smallest k such that k^3 == 1 (mod some n-th
power), k > 1. Data: 2, 4, 9, 17, 33, 65, 129, 257, ... The formula section states:
Conjecture: a(n) = 2^n+1 for n>2. a(n) = 3*a(n-1)-2*a(n-2) for n>4.
G.f.: -x*(2*x^3-x^2+2*x-2) / ((x-1)*(2*x-1)). [Colin Barker, Feb 05 2013]

Formalization notes:
* "Some n-th power" is read as m^n for an integer m ≥ 2: with m = 1 every k would qualify
  and the sequence would be constantly 2, contradicting the data (a(2) = 4).
* `a n` is the infimum of the set of k > 1 with k^3 ≡ 1 (mod m^n) for some m ≥ 2. The set is
  nonempty for every n (k = 2^n + 1 with m = 2), so the infimum is its least element.
* The entry has offset 1; `a` is defined for every n, and the statements only use n ≥ 1.
* `main` is the conjunction of the three conjectures: the closed form for n > 2, the recurrence
  for n > 4 (stated in ℤ, it has a negative coefficient), and the g.f.
* The g.f. is the series Sum_{n >= 1} a(n) x^n (the term at x^0 is set to 0, matching offset 1);
  the identity A(x) = N(x)/D(x) with D(x) = (x-1)*(2*x-1) is stated as A(x)*D(x) = N(x) in
  ℚ[[x]], which is equivalent because D has constant term 1.
* Controls: the data gives a(1) = 2 (2^3 - 1 = 7 = 7^1) and a(2) = 4 (4^3 - 1 = 63 = 3^2 * 7).
-/

namespace OMA.S_oeis_a088039

/-- The k > 1 with k^3 ≡ 1 modulo the n-th power of some integer m ≥ 2. -/
def S (n : ℕ) : Set ℕ := {k | 1 < k ∧ ∃ m : ℕ, 2 ≤ m ∧ k ^ 3 ≡ 1 [MOD m ^ n]}

/-- A088039: the smallest such k. -/
noncomputable def a (n : ℕ) : ℕ := sInf (S n)

open PowerSeries in
/-- Barker's conjectures: closed form for n > 2, recurrence for n > 4, and the g.f. -/
theorem main :
    (∀ n : ℕ, 2 < n → a n = 2 ^ n + 1) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((X - 1) * (2 * X - 1)) =
      -X * (2 * X ^ 3 - X ^ 2 + 2 * X - 2) := by
  sorry

end OMA.S_oeis_a088039
