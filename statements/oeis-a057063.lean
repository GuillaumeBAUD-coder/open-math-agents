import Mathlib

/-!
# A057063: the limit of successive cyclic block rotations (prefix of length n fixed).

Source: https://oeis.org/A057063
Credit: @thatoneguy006

Name: Let P(n) of a sequence s(1),s(2),s(3),... be obtained by leaving s(1),...,s(n) fixed and
reverse-cyclically permuting every n consecutive terms thereafter; apply P(2) to 1,2,3,... to get
PS(2), then apply P(3) to PS(2) to get PS(3), then apply P(4) to PS(3), etc. The limit of PS(n)
is A057063. A057033 is the same construction with s(1),...,s(n-1) fixed.

The conjecture stated here, from the entry:

  Conjecture: a(n) = A057033(n-1) + 1 for n > 1 with a(1) = 1.
  - Mikhail Kurkov, Mar 10 2022

Reading.
* The permutation of each block is a cyclic rotation to the left, (x_1, ..., x_n) becomes
  (x_2, ..., x_n, x_1): the examples of the entry (PS(3) begins 1, 2, 4, 6, 5, 3, 7, from
  PS(2) = 1, 2, 4, 3, 6, 5, 8, ...) and the Mathematica program of A057033 (RotateLeft) show it.
* Positions are zero-based below. After stage m the first m (A057063) or m - 1 (A057033)
  positions are never moved again, so the limit at zero-based position i is the value after
  stage i + 1 (A057063) or stage i + 2 (A057033); `term` evaluates exactly that. With this,
  the terms are 1, 2, 4, 6, 3, 10, 12, 7, ... and 1, 3, 5, 2, 9, 11, 6, ..., the data.
-/

namespace OMA.S_oeis_a057063

/-- The position before stage `m` whose entry lands at position `i` after stage `m`, when the first
`fixed` positions stay put and each later block of `m` is rotated left. -/
def sourcePosition (m fixed i : ℕ) : ℕ :=
  if i < fixed then i else
    fixed + m * ((i - fixed) / m) + ((i - fixed) % m + 1) % m

/-- The entry at zero-based position `i` after the stages `m = 2, ..., r + 1`, starting from
`1, 2, 3, ...`; at stage `m` the first `m - 1 + extra` positions are fixed. -/
def afterStages (extra : ℕ) : ℕ → ℕ → ℕ
  | 0, i => i + 1
  | r + 1, i => afterStages extra r (sourcePosition (r + 2) (r + 1 + extra) i)

/-- A057063(n), `n ≥ 1`: the stable value at position `n - 1` (prefix of length `m` fixed). -/
def A057063 (n : ℕ) : ℕ := afterStages 1 (n - 1) (n - 1)

/-- A057033(n), `n ≥ 1`: the stable value at position `n - 1` (prefix of length `m - 1` fixed). -/
def A057033 (n : ℕ) : ℕ := afterStages 0 n (n - 1)

/-- Kurkov's conjecture. -/
theorem main : ∀ n : ℕ, 1 < n → A057063 n = A057033 (n - 1) + 1 := by
  sorry

end OMA.S_oeis_a057063
