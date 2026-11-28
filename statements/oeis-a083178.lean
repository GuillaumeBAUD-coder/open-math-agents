import Mathlib

/-!
# A083178: Numbers with digit sum n and maximal digit product.

Source: https://oeis.org/A083178
Name: Numbers with a digit sum of n and a maximum product of digits. In case of
two identical products choose the largest number.
Conjecture (Colin Barker): a(n) = 10*a(n-3) + a(n-6) - 10*a(n-9) for n > 10.

Credit: @bear20252026 (agent: catpaw, model CatPaw)

We state the OEIS definition together with Barker's recurrence.  `a083178 n`
picks, among the numbers below `10^n` whose decimal digits sum to `n`, the one
with maximal digit product, breaking ties toward the larger number (scanning
the ascending list and keeping later entries on equal products does this).
The body stays `sorry`; a person reviews the translation before merging.
-/

noncomputable section

open scoped Classical

namespace OMA.S_oeis_a083178

/-- Product of the decimal digits of `m` (the empty product for `m = 0`). -/
def digitsProd (m : ℕ) : ℕ := (Nat.digits 10 m).prod

/-- Pick the entry of the ascending list `l` maximizing `f`, preferring the
later (hence larger) entry when several entries have the same value. -/
def argmaxKey (f : ℕ → ℕ) (l : List ℕ) : ℕ :=
  l.foldl (fun acc x => if f acc ≤ f x then x else acc) 0

/-- The OEIS A083178 sequence `1, 2, 3, 22, 32, 33, 322, ...`: among the numbers
below `10^n` whose decimal digits sum to `n`, the one with maximal digit
product, ties broken toward the larger number. -/
def a083178 (n : ℕ) : ℕ :=
  argmaxKey digitsProd
    (((Finset.range (10 ^ n)).filter (fun m => (Nat.digits 10 m).sum = n)).sort (· ≤ ·))

theorem main :
    ∀ n : ℕ, 10 < n →
      a083178 n = 10 * a083178 (n - 3) + a083178 (n - 6) - 10 * a083178 (n - 9) := by
  sorry

end OMA.S_oeis_a083178

end
