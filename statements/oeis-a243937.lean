import Mathlib

/-!
# A243937: Even numbers n>=6 for which lpf(n-1) > lpf(n-3), where lpf = least prime factor.

Source: https://oeis.org/A243937
Credit: @xor2k

Vladimir Shevelev and Peter J. C. Moses (Jul 11 2014), in the comment section of A243937:
  Conjecture: All differences are 2, 4 or 6 such that there are no two consecutive terms 2
  (..., 2, 2, ...), no two consecutive terms 4, while consecutive terms 6 occur 1, 2, 3 or 4
  times; also consecutive pairs of terms 2, 4 appear 1, 2, 3 or 4 times.
(The entry carries a later comment of Jens Kruse Andersen sketching a proof by divisibility
by 3 and 5.)

Conventions:
* lpf is `Nat.minFac`. The terms are the even n ≥ 6 with lpf(n-3) < lpf(n-1), in increasing
  order, offset 1: a(n) is `Nat.nth (· ∈ S) (n - 1)`, the (n-1)-th element of S counted from 0.
* The differences are d(n) = a(n+1) - a(n) for n ≥ 1 (natural number subtraction; the sequence
  is increasing). The word terms in the conjecture refers to terms of the difference sequence.
* All five parts of the conjecture are stated, as a conjunction, in the order of the text:
  1. every difference is 2, 4 or 6;
  2. no two consecutive differences are both 2;
  3. no two consecutive differences are both 4;
  4. a run of consecutive differences 6 has length 1, 2, 3 or 4, read as: there are no five
     consecutive differences 6;
  5. a run of consecutive pairs of differences 2, 4 has length 1, 2, 3 or 4, read as: there
     are no five consecutive pairs 2, 4 (ten consecutive differences 2,4,2,4,2,4,2,4,2,4).
  In parts 4 and 5 the reading taken is the upper bound on the run length; that each of the
  run lengths 1, 2, 3, 4 actually occurs is not stated (it is seen numerically below 2*10^5).

Numerical check: a Python copy of the definition gives 6, 8, 12, 14, 18, 20, 24, 30, 32, 36, 38,
42, 44, 48, 54, 60, 62, 66, 68, 72, 74, 78, 80, 84, 90, 96, 98, 102, 104, 108 for the first 30
elements of S (the DATA of the entry is not available offline; this agrees with the start
6, 8, 12, 14, 18, 20, 24, 30, 32 as remembered), and all five parts hold for the terms below
2*10^5.
-/

namespace OMA.S_oeis_a243937

/-- Even numbers n ≥ 6 with lpf(n-1) > lpf(n-3). -/
def S : Set ℕ := {n | 6 ≤ n ∧ Even n ∧ (n - 3).minFac < (n - 1).minFac}

/-- A243937 (offset 1): the n-th element of S in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (· ∈ S) (n - 1)

/-- The differences of consecutive terms, d(n) = a(n+1) - a(n), n ≥ 1. -/
noncomputable def d (n : ℕ) : ℕ := a (n + 1) - a n

/-- The conjecture of Shevelev and Moses on the differences of A243937. -/
theorem main : (∀ n : ℕ, 1 ≤ n → d n = 2 ∨ d n = 4 ∨ d n = 6) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ (d n = 2 ∧ d (n + 1) = 2)) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ (d n = 4 ∧ d (n + 1) = 4)) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ (∀ i : ℕ, i < 5 → d (n + i) = 6)) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ (∀ i : ℕ, i < 5 → d (n + 2 * i) = 2 ∧ d (n + 2 * i + 1) = 4)) := by
  sorry

end OMA.S_oeis_a243937
