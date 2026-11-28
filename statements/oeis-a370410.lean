import Mathlib

/-!
# A370410: Number of length-n binary strings that are the concatenation of two nonempty palindromes.

Source: https://oeis.org/A370410
Credit: @xor2k

Michael S. Branicky (Feb 18 2024), in the formula section of A370410:
  a(n) = A007055(n) - A056458(n) (conjectured).
This is the only claim of the row. (The entry also carries a proof sketch by Daniel Gabric,
Feb 21 2024, via Lemma 3 of Lyndon and Schützenberger.)

Conventions:
* Binary strings are lists over `Bool`; a string of length n is a `w : List Bool` with
  `w.length = n`. A palindrome is a string equal to its reversal (the empty string is one).
* A370410 (offset 1), `a n`: the number of strings w of length n with w = u ++ v for some nonempty
  palindromes u, v (the name of the entry).
* A007055 (offset 0), by its name (number of words of length n in the language SS, S the
  palindromes over {0,1}, the empty word included; the crossref of A370410 says: allows the
  palindromes to be empty): the number of strings w of length n with w = u ++ v for palindromes
  u, v, possibly empty.
* A056458 (offset 1), by its name (number of primitive (aperiodic) palindromes using a maximum of
  two different symbols): the number of palindromes of length n that are primitive. A string is
  primitive when it is nonempty and not a proper power z^k (k ≥ 2 concatenated copies of a
  string z, written `(List.replicate k z).flatten`); this is the notion used in Gabric's proof in
  the entry (w not primitive: w = z^i for a nonempty string z and an integer i ≥ 2), and for
  nonempty w it is the same as aperiodic (w has n distinct rotations).
* The counts are `Set.ncard` of sets of lists of length n (finite sets).
* The claim is stated for every n ≥ 1 (the offset of A370410 and of A056458), both without
  subtraction in ℕ, a(n) + A056458(n) = A007055(n), and in the form of the entry in ℤ,
  a(n) = A007055(n) - A056458(n). The two forms are equivalent. (For n = 0 the identity would
  fail with these definitions: 0 + 0 ≠ 1; n = 0 is outside the offsets.)

Numerical check: a Python copy of the three definitions (brute force over all strings) gives for
n = 1..20
  a:       0, 4, 6, 14, 26, 48, 86, 148, 232, 400, 622, 982, 1514, 2440, 3482, 5680, 8162, 12932,
           18398, 29146
  A007055: 2, 4, 8, 16, 32, 52, 100, 160, 260, 424, 684, 1036, 1640, 2552, 3728, 5920, 8672,
           13408, 19420, 30136   (and 1 for n = 0)
  A056458: 2, 0, 2, 2, 6, 4, 14, 12, 28, 24, 62, 54, 126, 112, 246, 240, 510, 476, 1022, 990
compared with DATA of the three entries: identical for these first 20 terms (21 for A007055), and
the identity holds for n = 1..20.
-/

namespace OMA.S_oeis_a370410

/-- A palindrome: a binary string equal to its reversal. -/
def IsPal (w : List Bool) : Prop := w.reverse = w

/-- A primitive string: nonempty and not a power z^k with k ≥ 2. -/
def IsPrimitive (w : List Bool) : Prop :=
  w ≠ [] ∧ ¬ ∃ (z : List Bool) (k : ℕ), 2 ≤ k ∧ w = (List.replicate k z).flatten

/-- A370410 (offset 1): the number of binary strings of length n that are the concatenation of
two nonempty palindromes. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {w : List Bool | w.length = n ∧
    ∃ u v : List Bool, u ≠ [] ∧ v ≠ [] ∧ IsPal u ∧ IsPal v ∧ w = u ++ v}

/-- A007055 (offset 0): the number of binary strings of length n that are the concatenation of
two (possibly empty) palindromes. -/
noncomputable def A007055 (n : ℕ) : ℕ :=
  Set.ncard {w : List Bool | w.length = n ∧ ∃ u v : List Bool, IsPal u ∧ IsPal v ∧ w = u ++ v}

/-- A056458 (offset 1): the number of primitive binary palindromes of length n. -/
noncomputable def A056458 (n : ℕ) : ℕ :=
  Set.ncard {w : List Bool | w.length = n ∧ IsPal w ∧ IsPrimitive w}

/-- Branicky's conjecture: a(n) = A007055(n) - A056458(n) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n + A056458 n = A007055 n ∧ (a n : ℤ) = (A007055 n : ℤ) - (A056458 n : ℤ) := by
  sorry

end OMA.S_oeis_a370410
