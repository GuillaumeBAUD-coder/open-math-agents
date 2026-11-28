import Mathlib

/-!
# A085135: Numbers whose cyclic permutations are all 7-smooth (A002473).

Source: https://oeis.org/A085135
Credit: @darealpandaboi

Conjecture: there are finitely many nontrivial terms (not of the form k*10^r with k = 1 to 9).

Translation notes.
* A cyclic permutation of n rotates its decimal digit string; a leading zero produced by the
  rotation is dropped when it is read as a number (108 is a term: 108, 081 = 81 and 810 are all
  7-smooth). Rotating the little-endian digit list Nat.digits 10 n gives the same set of
  rotations as rotating the written string.
* m is 7-smooth when m is positive and every prime factor of m is at most 7.
* This reading reproduces the listed data 1, 2, ..., 10, 12, 18, 20, ..., 3000, 4000 (checked by
  computer). The trivial terms k*10^r (k = 1..9, r >= 0) make the sequence infinite; the
  statement says the remaining terms form a finite set.
-/

namespace OMA.S_oeis_a085135

/-- m is 7-smooth: positive with every prime factor at most 7. -/
def IsSmooth7 (m : ℕ) : Prop := 0 < m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ≤ 7

/-- Every cyclic permutation of the decimal digits of n is 7-smooth. -/
def AllRotationsSmooth (n : ℕ) : Prop :=
  ∀ i : ℕ, i < (Nat.digits 10 n).length → IsSmooth7 (Nat.ofDigits 10 ((Nat.digits 10 n).rotate i))

theorem main :
    {n : ℕ | 0 < n ∧ AllRotationsSmooth n ∧
      ¬ ∃ k r : ℕ, 1 ≤ k ∧ k ≤ 9 ∧ n = k * 10 ^ r}.Finite := by
  sorry

end OMA.S_oeis_a085135
