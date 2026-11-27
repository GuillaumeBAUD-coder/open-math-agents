import Mathlib

/-!
# A261541: Least positive integer m such that both m and m*n belong to the set {k>0: prime(k)+2, prime(k)+6, prime(k)+8 are all prime}.

Source: https://oeis.org/A261541
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A261541):
(i) Each positive rational number `r` can be written as `m/n` with `m` and `n` in the set
`{k > 0 : prime(k) + 2, prime(k) + 6 and prime(k) + 8 are all prime}`.
(ii) Any positive rational number `r` can be written as `m/n` with `m` and `n` in the set
`{k > 0 : prime(k) + 4, prime(k) + 6 and prime(k) + 10 are all prime}`.

Formalization notes:
* `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`.
* `S a b c = {k > 0 : prime(k) + a, prime(k) + b, prime(k) + c are all prime}`.
* With this definition the least `m` with `m, m n ∈ S 2 6 8` is 3, 26, 26 for `n = 1, 9, 11`,
  matching the data of A261541.
-/

namespace OMA.S_oeis_a261541

/-- `{k > 0 : prime(k) + a, prime(k) + b, prime(k) + c are all prime}`. -/
def S (a b c : ℕ) : Set ℕ :=
  {k | 0 < k ∧ (Nat.nth Nat.Prime (k - 1) + a).Prime ∧ (Nat.nth Nat.Prime (k - 1) + b).Prime ∧
    (Nat.nth Nat.Prime (k - 1) + c).Prime}

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ r : ℚ, 0 < r → ∃ m ∈ S 2 6 8, ∃ n ∈ S 2 6 8, r = (m : ℚ) / n) ∧
      ∀ r : ℚ, 0 < r → ∃ m ∈ S 4 6 10, ∃ n ∈ S 4 6 10, r = (m : ℚ) / n := by
  sorry

end OMA.S_oeis_a261541
