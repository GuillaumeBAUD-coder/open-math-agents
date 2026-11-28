import OMAReductions.R_oeis_a397683_R1

-- Step oeis-a397683.R1.H3: hypothesis H3 of reduction oeis-a397683.R1
-- Credit: @luciusacarr
-- H3 := ∀ k : ℕ, 1 ≤ k → f (3 ^ k) = 0

/-! If `x` and `x + 1` are both units modulo `3^k`, then `x ≡ 1 (mod 3)`. Lifting the exponent
(`b ≡ 1 (mod 3^(i+1))` gives `b^3 ≡ 1 (mod 3^(i+2))`) shows `x^(3^(k-1)) ≡ 1 (mod 3^k)`, so the
order of `x` divides `3^(k-1)` and is odd. Reducing modulo `3`, `(x+1)^d ≡ 1` forces
`(-1)^d = 1`, so the order of `x + 1` is even. Hence the orders always differ. -/

open OMA.S_oeis_a397683

namespace OMA.S397683H3

theorem lte3 (a : ℤ) (ha : (3 : ℤ) ∣ a - 1) : ∀ i : ℕ, (3 : ℤ) ^ (i + 1) ∣ a ^ (3 ^ i) - 1 := by
  intro i
  induction i with
  | zero => simpa using ha
  | succ i ih =>
    set b := a ^ (3 ^ i) with hb
    have h3 : (3 : ℤ) ∣ b ^ 2 + b + 1 := by
      have hb1 : (3 : ℤ) ∣ b - 1 := (dvd_pow_self 3 (by omega)).trans ih
      have : b ^ 2 + b + 1 = (b - 1) * (b + 2) + 3 := by ring
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_left hb1 _) (dvd_refl 3)
    have : a ^ (3 ^ (i + 1)) - 1 = (b - 1) * (b ^ 2 + b + 1) := by
      rw [hb, pow_succ, pow_mul]; ring
    rw [this, pow_succ]
    exact mul_dvd_mul ih h3

end OMA.S397683H3

theorem OMA.solution : OMA.R_oeis_a397683_R1.H3 := by
  intro k hk
  have hne : 3 ^ k ≠ 1 := by
    have : 3 ≤ 3 ^ k := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  unfold f
  rw [if_neg hne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨hx, hx1, hord⟩
  have h3dvd : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  have hx3 : ¬ 3 ∣ x := fun h =>
    absurd (Nat.dvd_gcd h h3dvd) (by rw [hx]; norm_num)
  have hx13 : ¬ 3 ∣ x + 1 := fun h =>
    absurd (Nat.dvd_gcd h h3dvd) (by rw [hx1]; norm_num)
  have hxmod : x % 3 = 1 := by omega
  -- order of x is odd
  have hodd : Odd (orderOf (x : ZMod (3 ^ k))) := by
    have hdvd : (3 : ℤ) ^ (k - 1 + 1) ∣ (x : ℤ) ^ (3 ^ (k - 1)) - 1 :=
      OMA.S397683H3.lte3 (x : ℤ) (by omega) (k - 1)
    rw [show k - 1 + 1 = k by omega] at hdvd
    have hpow : (x : ZMod (3 ^ k)) ^ (3 ^ (k - 1)) = 1 := by
      have h0 : (((x : ℤ) ^ (3 ^ (k - 1)) - 1 : ℤ) : ZMod (3 ^ k)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact_mod_cast hdvd
      push_cast at h0
      exact sub_eq_zero.mp h0
    have hd := orderOf_dvd_of_pow_eq_one hpow
    exact Odd.of_dvd_nat (Odd.pow (by decide)) hd
  -- order of x + 1 is even
  have heven : Even (orderOf (((x + 1 : ℕ) : ZMod (3 ^ k)))) := by
    set d := orderOf (((x + 1 : ℕ) : ZMod (3 ^ k)))
    have hp : (((x + 1 : ℕ) : ZMod (3 ^ k))) ^ d = 1 := pow_orderOf_eq_one _
    have hmap := congrArg (ZMod.castHom h3dvd (ZMod 3)) hp
    rw [map_pow, map_natCast, map_one] at hmap
    have h2 : (((x + 1 : ℕ)) : ZMod 3) = 2 := by
      rw [← ZMod.natCast_mod, show (x + 1) % 3 = 2 by omega]
      rfl
    rw [h2] at hmap
    rcases Nat.even_or_odd d with he | ⟨j, hj⟩
    · exact he
    · exfalso
      rw [hj, pow_succ, pow_mul] at hmap
      have h4 : (2 : ZMod 3) ^ 2 = 1 := by decide
      rw [h4, one_pow, one_mul] at hmap
      exact absurd hmap (by decide)
  rw [hord] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) heven
