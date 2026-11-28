import OMAStatements.S_oeis_a147803
import Mathlib

/-!
# OEIS A147803: `rad(m (5^n - m) 5^n) = 5 · rad(m (5^n - m))` for `m` coprime to `5`

Since `m` is coprime to `5` and `m < 5^n`, we have `n ≥ 1`, and `5^n - m` is coprime to `5`
as well (otherwise `5` would divide `m`). So `m (5^n - m)` is coprime to `5^n`, the radical is
multiplicative on coprime factors, and `rad(5^n) = 5`.
-/

open UniqueFactorizationMonoid

theorem OMA.solution : type_of% @OMA.S_oeis_a147803.main := by
  intro n m hm hlt
  have h5 : Nat.Prime 5 := by norm_num
  have hm5 : ¬ 5 ∣ m := (Nat.Prime.coprime_iff_not_dvd h5).mp hm.symm
  -- `n ≥ 1`, since `m = 0` is not coprime to `5`
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      have : m = 0 := by simpa using hlt
      exact hm5 (this ▸ dvd_zero 5)
    · exact ⟨n - 1, by omega⟩
  -- `5 ∤ 5^n - m`
  have hsub : ¬ 5 ∣ 5 ^ (n' + 1) - m := by
    rw [pow_succ'] at hlt ⊢
    omega
  have hcop : Nat.Coprime (m * (5 ^ (n' + 1) - m)) (5 ^ (n' + 1)) :=
    Nat.Coprime.pow_right _
      (Nat.Coprime.mul_left hm ((Nat.Prime.coprime_iff_not_dvd h5).mpr hsub).symm)
  rw [radical_mul (Nat.coprime_iff_isRelPrime.mp hcop),
    radical_pow_of_prime h5.prime (Nat.succ_ne_zero n'), normalize_eq, mul_comm]
