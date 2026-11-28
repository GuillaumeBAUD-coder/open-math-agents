import OMAStatements.S_oeis_a369378
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a369378.main := by
  intro n hn k hk
  have hN : 1 < (2 : ℕ) ^ n := by
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn
  have hbig : 1 ≤ (2 : ℕ) ^ (2 ^ n + 1) :=
    show 0 < (2 : ℕ) ^ (2 ^ n + 1) by positivity
  by_cases hz : k = 0
  · subst k
    simp only [pow_zero, Nat.sub_add_cancel hbig]
    intro hp
    have hd : 2 ∣ (2 : ℕ) ^ (2 ^ n + 1) := by
      rw [pow_succ]
      exact dvd_mul_left _ _
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · omega
    · have hlt : 2 < (2 : ℕ) ^ (2 ^ n + 1) := by
        simpa using Nat.pow_lt_pow_right (by decide : 1 < 2)
          (show 1 < (2 : ℕ) ^ n + 1 by omega)
      omega
  · obtain ⟨r, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hz
    have hm1 : 1 ≤ m := by have := Nat.odd_iff.mp hm; omega
    have hr : r < n := by
      by_contra! h
      have hp : (2 : ℕ) ^ n ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) h
      have hmul := Nat.mul_le_mul_left ((2 : ℕ) ^ r) hm1
      rw [mul_one, ← hkm] at hmul
      omega
    let d : ℕ := 2 ^ ((2 : ℕ) ^ r) + 1
    have hd : 1 < d := by
      unfold d
      have : 0 < (2 : ℕ) ^ ((2 : ℕ) ^ r) := by positivity
      omega
    have hbase : (2 : ZMod d) ^ ((2 : ℕ) ^ r) = -1 := by
      have he : (d : ZMod d) = 0 := ZMod.natCast_self d
      push_cast [d] at he
      exact eq_neg_of_add_eq_zero_left he
    have hsq : (2 : ZMod d) ^ ((2 : ℕ) ^ (r + 1)) = 1 := by
      rw [pow_succ (2 : ℕ) r, pow_mul, hbase]
      ring
    have hExpo : (2 : ZMod d) ^ ((2 : ℕ) ^ n + 1) = 2 := by
      obtain ⟨s, hs⟩ : ∃ s : ℕ, n = (r + 1) + s := ⟨n - (r + 1), by omega⟩
      rw [hs, pow_add (2 : ℕ) (r + 1) s, pow_succ, pow_mul, hsq, one_pow, one_mul]
    have hK : (2 : ZMod d) ^ k = -1 := by
      rw [hkm, pow_mul, hbase]
      exact hm.neg_one_pow
    have hZ : ((2 ^ ((2 : ℕ) ^ n + 1) - 1 + 2 ^ k : ℕ) : ZMod d) = 0 := by
      push_cast [Nat.cast_sub hbig]
      rw [hExpo, hK]
      ring
    have hD := (ZMod.natCast_eq_zero_iff _ d).mp hZ
    have hLt : d < 2 ^ ((2 : ℕ) ^ n + 1) - 1 + 2 ^ k := by
      have hp : (2 : ℕ) ^ r < 2 ^ n := Nat.pow_lt_pow_right (by decide) hr
      have ht : (2 : ℕ) ^ ((2 : ℕ) ^ r + 1) ≤ 2 ^ ((2 : ℕ) ^ n + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      rw [pow_succ] at ht
      have hmin : 1 < (2 : ℕ) ^ ((2 : ℕ) ^ r) := by
        exact Nat.pow_lt_pow_right (by decide : 1 < 2)
          (show 0 < (2 : ℕ) ^ r by positivity)
      have hpos : 0 < (2 : ℕ) ^ k := by positivity
      dsimp [d]
      omega
    intro hPrime
    rcases (Nat.dvd_prime hPrime).mp hD with h | h <;> omega