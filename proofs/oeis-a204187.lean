import OMAStatements.S_oeis_a204187

open Finset OMA.S_oeis_a204187

theorem OMA.solution : type_of% @OMA.S_oeis_a204187.main := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hk : 1 ≤ k := by omega
    have hodd : Odd (2 * k - 1) := ⟨k - 1, by omega⟩
    have h3 : ∑ j ∈ Ico 1 k, (2 * k - j) ^ (2 * k - 1) = ∑ j ∈ Ico (k + 1) (2 * k), j ^ (2 * k - 1) := by
      have := Finset.sum_Ico_reflect (fun j => j ^ (2 * k - 1)) 1 (show k ≤ 2 * k + 1 by omega)
      simpa [show 2 * k + 1 - k = k + 1 by omega] using this
    have h1 : ∑ m ∈ Ico 1 (2 * k), m ^ (2 * k - 1) =
        ∑ m ∈ Ico 1 k, (m ^ (2 * k - 1) + (2 * k - m) ^ (2 * k - 1)) + k ^ (2 * k - 1) := by
      rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ k + 1 by omega) (show k + 1 ≤ 2 * k by omega),
        Finset.sum_Ico_succ_top hk, Finset.sum_add_distrib, h3]
      ring
    have h2 : 2 * k ∣ ∑ m ∈ Ico 1 k, (m ^ (2 * k - 1) + (2 * k - m) ^ (2 * k - 1)) :=
      Finset.dvd_sum fun m hm => by
        have := hodd.nat_add_dvd_pow_add_pow m (2 * k - m)
        rwa [show m + (2 * k - m) = 2 * k by have := Finset.mem_Ico.1 hm; omega] at this
    have key : a (2 * k) = k ^ (2 * k - 1) % (2 * k) := by
      rw [a, h1, Nat.add_mod, Nat.mod_eq_zero_of_dvd h2, zero_add, Nat.mod_mod]
    rw [key]
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have : (2 * j) ^ (2 * (2 * j) - 1) % (2 * (2 * j)) = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        rw [show 2 * (2 * j) - 1 = 2 + (4 * j - 3) by omega, pow_add]
        exact ⟨j * (2 * j) ^ (4 * j - 3), by ring⟩
      omega
    · have : (2 * j + 1) ^ (2 * (2 * j + 1) - 1) % (2 * (2 * j + 1)) = 2 * j + 1 := by
        rw [show 2 * (2 * j + 1) - 1 = 4 * j + 1 by omega, pow_succ]
        obtain ⟨q, hq⟩ : Odd ((2 * j + 1) ^ (4 * j)) := Odd.pow ⟨j, rfl⟩
        rw [hq, show (2 * q + 1) * (2 * j + 1) = 2 * j + 1 + 2 * (2 * j + 1) * q by ring,
          Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)
      omega
  · constructor <;> omega
