import OMAStatements.S_oeis_a190302
import Mathlib

/-!
# OEIS A190302: some multiple `m n` with `m ≤ 5` begins with the digit `1`

Let `T = 10^k` be the power of ten with `T ≤ n < 10 T`.

* If `n < 2T`, then `n` itself begins with `1` (`m = 1`).
* If `2T ≤ n < 4T`, then `10T ≤ 5n < 20T` (`m = 5`).
* If `4T ≤ n < 5T`, then `12T ≤ 3n < 15T` (`m = 3`).
* If `5T ≤ n < 10T`, then `10T ≤ 2n < 20T` (`m = 2`).

So the set of admissible `m` contains a number `≤ 5`, and its least element is `< 6`.
-/

open OMA.S_oeis_a190302

namespace OMA.A190302

/-- Some `m ∈ {1, 2, 3, 5}` works. -/
lemma exists_small (n : ℕ) (hn : 0 < n) : ∃ m : ℕ, 0 < m ∧ m ≤ 5 ∧ BeginsWithOne (m * n) := by
  have h1 : 10 ^ Nat.log 10 n ≤ n := Nat.pow_log_le_self 10 hn.ne'
  have h2 : n < 10 ^ (Nat.log 10 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  obtain ⟨k, hk⟩ : ∃ k, Nat.log 10 n = k := ⟨_, rfl⟩
  rw [hk] at h1 h2
  obtain ⟨T, hT⟩ : ∃ T, 10 ^ k = T := ⟨_, rfl⟩
  have hT1 : 10 ^ (k + 1) = 10 * T := by rw [pow_succ, hT]; ring
  rw [hT] at h1
  rw [hT1] at h2
  rcases Nat.lt_or_ge n (2 * T) with a | a
  · exact ⟨1, by norm_num, by norm_num, k, by rw [hT]; omega, by rw [hT]; omega⟩
  rcases Nat.lt_or_ge n (4 * T) with b | b
  · exact ⟨5, by norm_num, by norm_num, k + 1, by rw [hT1]; omega, by rw [hT1]; omega⟩
  rcases Nat.lt_or_ge n (5 * T) with c | c
  · exact ⟨3, by norm_num, by norm_num, k + 1, by rw [hT1]; omega, by rw [hT1]; omega⟩
  · exact ⟨2, by norm_num, by norm_num, k + 1, by rw [hT1]; omega, by rw [hT1]; omega⟩

end OMA.A190302

open OMA.A190302 in
theorem OMA.solution : type_of% @OMA.S_oeis_a190302.main := by
  intro n hn
  obtain ⟨m, hm0, hm5, hm⟩ := exists_small n hn
  have hex : ∃ m, 0 < m ∧ BeginsWithOne (m * n) := ⟨m, hm0, hm⟩
  classical
  refine ⟨Nat.find hex, ⟨Nat.find_spec hex, fun x hx => Nat.find_min' hex hx⟩, ?_⟩
  have := Nat.find_min' hex ⟨hm0, hm⟩
  omega
