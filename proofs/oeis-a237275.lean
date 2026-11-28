import OMAStatements.S_oeis_a237275
import Mathlib

/-!
# A237275: the least number divisible by the `n`-th power of its last digit ends in `2`

Call `k` *admissible* if `k > 0`, its last digit `d` exceeds `1`, and `d ^ n ∣ k`.

* Some `j ∈ {1, 2, 3, 4}` makes `c = 2 ^ n * j` end in `2` (the last digit of `2 ^ n` is
  `1, 2, 4, 8` or `6`), so `c` is admissible and `a n ≤ c ≤ 4 * 2 ^ n`.
* If the last digit `d` of `a n` were at least `3`, then `3 ^ n ≤ d ^ n ≤ a n ≤ 4 * 2 ^ n`,
  which is impossible for `n ≥ 4`.
* For `n ≤ 3` the admissible numbers `2, 2, 12, 32` bound `a n`, and a finite check of the
  smaller numbers finishes the proof.
-/

namespace OMA.S_oeis_a237275

/-- The admissible set for exponent `n`. -/
def S (n : ℕ) : Set ℕ := {k : ℕ | 0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k}

/-- The last digit of a power of two. -/
lemma two_pow_mod (n : ℕ) :
    2 ^ n % 10 = 1 ∨ 2 ^ n % 10 = 2 ∨ 2 ^ n % 10 = 4 ∨ 2 ^ n % 10 = 8 ∨ 2 ^ n % 10 = 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ 2 n]; omega

/-- An admissible number ending in `2`, at most `4 * 2 ^ n`. -/
lemma exists_candidate (n : ℕ) : ∃ c ∈ S n, c ≤ 4 * 2 ^ n := by
  have hpos : 0 < 2 ^ n := by positivity
  have key : ∃ j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧ (2 ^ n * j) % 10 = 2 := by
    rcases two_pow_mod n with h | h | h | h | h
    · exact ⟨2, by norm_num, by norm_num, by omega⟩
    · exact ⟨1, by norm_num, by norm_num, by omega⟩
    · exact ⟨3, by norm_num, by norm_num, by omega⟩
    · exact ⟨4, by norm_num, by norm_num, by omega⟩
    · exact ⟨2, by norm_num, by norm_num, by omega⟩
  obtain ⟨j, hj1, hj4, hmod⟩ := key
  refine ⟨2 ^ n * j, ⟨Nat.mul_pos hpos hj1, by omega, ?_⟩, ?_⟩
  · rw [hmod]
    exact Dvd.intro j rfl
  · rw [mul_comm 4]
    exact Nat.mul_le_mul_left _ hj4

/-- `4 * 2 ^ n < 3 ^ n` from `n = 4` on. -/
lemma four_mul_two_pow_lt (n : ℕ) (hn : 4 ≤ n) : 4 * 2 ^ n < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ 2 n, pow_succ 3 n]; omega

/-- The finite check for `n ≤ 3`: a least admissible number ends in `2`. -/
lemma small (n v : ℕ) (hn : n < 4) (hv : v ∈ S n) (hmin : ∀ c ∈ S n, v ≤ c) : v % 10 = 2 := by
  obtain ⟨h0, h1, h2⟩ := hv
  interval_cases n
  · have hle := hmin 2 ⟨by norm_num, by norm_num, by norm_num⟩
    interval_cases v <;> first | rfl | (exfalso; revert h1; decide)
  · have hle := hmin 2 ⟨by norm_num, by norm_num, by norm_num⟩
    interval_cases v <;> first | rfl | (exfalso; revert h1; decide)
  · have hle := hmin 12 ⟨by norm_num, by norm_num, by norm_num⟩
    interval_cases v <;>
      first | rfl | (exfalso; revert h1; decide) | (exfalso; revert h2; decide)
  · have hle := hmin 32 ⟨by norm_num, by norm_num, by norm_num⟩
    interval_cases v <;>
      first | rfl | (exfalso; revert h1; decide) | (exfalso; revert h2; decide)

end OMA.S_oeis_a237275

open OMA.S_oeis_a237275 in
theorem OMA.solution : type_of% @OMA.S_oeis_a237275.main := by
  intro n
  obtain ⟨c, hcS, hc⟩ := exists_candidate n
  have hmem : a n ∈ S n := Nat.sInf_mem ⟨c, hcS⟩
  have hmin : ∀ k ∈ S n, a n ≤ k := fun k hk => Nat.sInf_le hk
  rcases Nat.lt_or_ge n 4 with hn | hn
  · exact small n (a n) hn hmem hmin
  · obtain ⟨h0, h1, h2⟩ := hmem
    by_contra hne
    have h3 : 3 ≤ a n % 10 := by omega
    have hchain : 3 ^ n ≤ a n :=
      (Nat.pow_le_pow_left h3 n).trans (Nat.le_of_dvd h0 h2)
    have := four_mul_two_pow_lt n hn
    have := hmin c hcS
    omega
