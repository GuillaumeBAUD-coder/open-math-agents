import Mathlib

/-!
# A277109: Starting from 2^n+1, the length of the longest sequence of consecutive numbers which all take the same number of steps to reach 1 in the Collatz (or '3x+1') problem.

Source: https://oeis.org/A277109
Credit: @xor2k

Comment in A277109 (the author of the entry is Dmitry Kamenetsky):
  Conjecture: If a(n) = 2^k - 1 for some k > 1, then a(n-1) = 2^(k-1) - 1. Conjecture holds for
  n <= 1812.
Hartmut F. W. Hoft (Aug 16 2018) comments that this conjecture is true and sketches the argument
(halve the even members of the run).

Only this first conjecture is stated here. Hoft's comment ends with a second, separate conjecture
of his own (on the subsequences between consecutive terms equal to 1); it is a different claim by
a different author, it is unproved, and it is NOT part of this statement.

Conventions:
* The Collatz map is `m ↦ m/2` (`m` even), `3m + 1` (`m` odd). `steps m` is the number of steps
  until the trajectory of `m` first reaches `1` (so `steps 1 = 0`), with values in `ℕ∞`: it is
  `⊤` if the trajectory never reaches `1`. Thus nothing about the Collatz conjecture is assumed;
  if it holds, `steps` is the usual finite step count A006577.
* Offset 0. `a(n) = L` is expressed by the predicate `RunLength n L`: `L ≥ 1`, the numbers
  `2^n + 1, ..., 2^n + L` all have the same step count, and `2^n + L + 1` has a different one
  (this is the PARI and Mathematica program of the entry). For each `n` at most one `L` satisfies
  `RunLength n L`, and a(n) is that `L`; no existence of `L` is assumed or needed.
* The conjecture is stated for all `n ≥ 1` (so that `a(n-1)` is a term of the sequence) and all
  `k > 1`: `RunLength n (2^k - 1) → RunLength (n-1) (2^(k-1) - 1)`.

Numerical check: a Python copy of the definition gives 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1,
3, 1, 3, 7, 15, 30, 1, 1, 3, 7, 15, 26, 26, 1, 1, 1, 3, 1, ... for n = 0, 1, 2, ...; compared with
DATA: identical for the first 92 terms (all of DATA); the conjecture was checked for n ≤ 91.
-/

namespace OMA.S_oeis_a277109

/-- The Collatz map. -/
def collatz (m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else 3 * m + 1

open Classical in
/-- Number of steps until the trajectory of `m` first reaches `1`; `⊤` if it never does. -/
noncomputable def steps (m : ℕ) : ℕ∞ :=
  if h : ∃ i : ℕ, collatz^[i] m = 1 then (Nat.find h : ℕ∞) else ⊤

/-- `a(n) = L`: the run of equal step counts starting at `2^n + 1` has length exactly `L`. -/
def RunLength (n L : ℕ) : Prop :=
  1 ≤ L ∧ (∀ i : ℕ, 1 ≤ i → i ≤ L → steps (2 ^ n + i) = steps (2 ^ n + 1)) ∧
    steps (2 ^ n + L + 1) ≠ steps (2 ^ n + 1)

/-- If a(n) = 2^k - 1 for some k > 1, then a(n-1) = 2^(k-1) - 1. -/
theorem main : ∀ n k : ℕ, 1 ≤ n → 1 < k →
    RunLength n (2 ^ k - 1) → RunLength (n - 1) (2 ^ (k - 1) - 1) := by
  sorry

end OMA.S_oeis_a277109
