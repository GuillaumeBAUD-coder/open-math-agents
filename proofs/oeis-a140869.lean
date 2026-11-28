import OMAStatements.S_oeis_a140869
import Mathlib

/-!
# OEIS A140869: numbers `h` not of the form `⌊(2mn + m + n - 2)/2⌋` give primes `4h + 5`

Suppose `4h + 5` is not prime. It is odd and at least `5`, so `4h + 5 = (2n + 1)(2m + 1)`
with `1 ≤ n ≤ m`. Expanding, `2mn + m + n = 2h + 2`, hence `T(m, n) = (2h + 2 - 2)/2 = h`
and `h` is in the sequence.
-/

open OMA.S_oeis_a140869

namespace OMA.A140869

/-- A factorisation `4h + 5 = (2n+1)(2m+1)` with `1 ≤ n ≤ m` puts `h` in the sequence. -/
lemma inSeq_of_factor {h m n : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m)
    (hf : (2 * n + 1) * (2 * m + 1) = 4 * h + 5) : InSeq h := by
  refine ⟨m, n, hn, hnm, ?_⟩
  unfold T
  have h1 : 2 * m * n = 2 * (m * n) := by ring
  have h2 : 4 * (m * n) + 2 * m + 2 * n + 1 = 4 * h + 5 := by rw [← hf]; ring
  rw [h1]
  omega

end OMA.A140869

open OMA.A140869 in
theorem OMA.solution : type_of% @OMA.S_oeis_a140869.main := by
  intro h hh
  by_contra hnp
  -- a proper divisor `d` of `4h + 5`, with cofactor `e`
  obtain ⟨d, ⟨e, hde⟩, hd2, hdlt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnp
  -- both factors are odd and at least `3`
  have hdodd : d % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one d with h0 | h1
    · exfalso
      have : (d * e) % 2 = 0 := by rw [Nat.mul_mod, h0]; simp
      omega
    · exact h1
  have heodd : e % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one e with h0 | h1
    · exfalso
      have : (d * e) % 2 = 0 := by rw [Nat.mul_mod, h0]; simp
      omega
    · exact h1
  have he2 : 2 ≤ e := by
    by_contra hlt
    have : e = 0 ∨ e = 1 := by omega
    rcases this with rfl | rfl <;> omega
  obtain ⟨n, rfl⟩ : ∃ n, d = 2 * n + 1 := ⟨d / 2, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, e = 2 * m + 1 := ⟨e / 2, by omega⟩
  rcases le_total n m with hnm | hmn
  · exact hh (inSeq_of_factor (by omega) hnm hde.symm)
  · exact hh (inSeq_of_factor (by omega) hmn (by rw [mul_comm]; exact hde.symm))
