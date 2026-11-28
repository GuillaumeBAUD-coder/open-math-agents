import OMAStatements.S_oeis_a204187
import Mathlib

/-! Proof of OEIS A204187 (Neretin's conjecture): 2 a(n) = n iff n = 4k + 2.
Pair m with n - m: for even n the sum is h^(n-1) mod n, h = n/2. -/

namespace OMA.Helpers

open Finset

/-- For `n = 2 h`, the sum of `m ^ (2 h - 1)` over `1 ≤ m < 2 h`, cast to `ZMod (2 h)`, is
`h ^ (2 h - 1)`: the terms `m` and `2 h - m` cancel because the exponent is odd. -/
theorem a204187_sum_cast (h : ℕ) (hh : 1 ≤ h) :
    ((∑ m ∈ Ico 1 (2 * h), m ^ (2 * h - 1) : ℕ) : ZMod (2 * h)) =
      ((h ^ (2 * h - 1) : ℕ) : ZMod (2 * h)) := by
  have hodd : Odd (2 * h - 1) := ⟨h - 1, by omega⟩
  have split : ∑ m ∈ Ico 1 (2 * h), m ^ (2 * h - 1) =
      (∑ m ∈ Ico 1 h, m ^ (2 * h - 1)) + h ^ (2 * h - 1) +
        ∑ m ∈ Ico (h + 1) (2 * h), m ^ (2 * h - 1) := by
    rw [← sum_Ico_consecutive _ (show 1 ≤ h by omega) (show h ≤ 2 * h by omega),
      sum_eq_sum_Ico_succ_bot (show h < 2 * h by omega)]
    ring
  have hrefl : ∑ m ∈ Ico (h + 1) (2 * h), m ^ (2 * h - 1) =
      ∑ j ∈ Ico 1 h, (2 * h - j) ^ (2 * h - 1) := by
    have hI : Ico (h + 1) (2 * h) = Ico (2 * h + 1 - h) (2 * h + 1 - 1) := by
      congr 1 <;> omega
    rw [hI, ← sum_Ico_reflect (fun m => m ^ (2 * h - 1)) 1 (show h ≤ 2 * h + 1 by omega)]
  have key : ∀ j ∈ Ico 1 h, (((2 * h - j) ^ (2 * h - 1) : ℕ) : ZMod (2 * h)) =
      -((j ^ (2 * h - 1) : ℕ) : ZMod (2 * h)) := by
    intro j hj
    have hj2 : j ≤ 2 * h := by
      rw [mem_Ico] at hj
      omega
    have h0 : ((2 * h : ℕ) : ZMod (2 * h)) = 0 := ZMod.natCast_self _
    rw [Nat.cast_pow, Nat.cast_sub hj2, h0, zero_sub, hodd.neg_pow, Nat.cast_pow]
  rw [split, hrefl, Nat.cast_add, Nat.cast_add, Nat.cast_sum, Nat.cast_sum, sum_congr rfl key,
    sum_neg_distrib]
  ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a204187.main := by
  intro n hn
  unfold OMA.S_oeis_a204187.a
  rcases Nat.even_or_odd n with ⟨h, rfl⟩ | ⟨k, rfl⟩
  · have hh : 1 ≤ h := by omega
    rw [show h + h = 2 * h by ring]
    have hc := (ZMod.natCast_eq_natCast_iff' _ _ _).1 (OMA.Helpers.a204187_sum_cast h hh)
    rw [hc]
    rcases Nat.even_or_odd h with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · have hdvd : 2 * (t + t) ∣ (t + t) ^ (2 * (t + t) - 1) := by
        have he : 2 * (t + t) - 1 = 2 + (2 * (t + t) - 3) := by omega
        rw [he, pow_add]
        exact Dvd.dvd.mul_right ⟨t, by ring⟩ _
      rw [Nat.mod_eq_zero_of_dvd hdvd]
      omega
    · have hpo : Odd ((2 * t + 1) ^ (2 * (2 * t + 1) - 2)) := Odd.pow ⟨t, rfl⟩
      obtain ⟨s, hs⟩ := hpo
      have he : (2 * t + 1) ^ (2 * (2 * t + 1) - 1) = (2 * t + 1) + 2 * (2 * t + 1) * s := by
        have he1 : 2 * (2 * t + 1) - 1 = (2 * (2 * t + 1) - 2) + 1 := by omega
        rw [he1, pow_succ, hs]
        ring
      rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      omega
  · omega
