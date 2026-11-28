import Mathlib

/-!
# Bounded first differences of decimal repdigit partition counts

Source sequences: https://oeis.org/A109969 and https://oeis.org/A109968.

A109968 counts unordered partitions into positive decimal repdigits with
distinct repeated digits. We choose parts in decreasing order and delete
each chosen digit from the available digits. There can be at most nine parts.
The empty partition counts once at zero. When the remaining sum is positive,
each possible part has at most that many decimal digits.

A109969 starts at index one. Its terms are signed forward differences of
these partition counts. Boundedness is two-sided. The proof checks the
first eight terms of A109969.
-/

namespace OMA.S_oeis_a109969

def repdigit (digit : ℕ) : ℕ → ℕ
  | 0 => 0
  | length + 1 => 10 * repdigit digit length + digit

def lengths (digit cap total : ℕ) : Finset ℕ :=
  (Finset.range total).filter fun j => repdigit digit (j + 1) ≤ min cap total

def countParts : ℕ → Finset ℕ → ℕ → ℕ → ℕ
  | 0, _, _, total => if total = 0 then 1 else 0
  | slots + 1, digits, cap, total =>
    if total = 0 then 1 else
      ∑ d ∈ digits, ∑ j ∈ lengths d cap total,
        countParts slots (digits.erase d) (repdigit d (j + 1)) (total - repdigit d (j + 1))

def decimalDigits : Finset ℕ := Finset.Icc 1 9

def partitions (n : ℕ) : ℕ := countParts 9 decimalDigits n n

def a (n : ℕ) : ℤ := (partitions (n + 1) : ℤ) - (partitions n : ℤ)

theorem main : ∃ bound : ℕ, ∀ n : ℕ, 1 ≤ n → |a n| ≤ (bound : ℤ) := by
  sorry

end OMA.S_oeis_a109969
