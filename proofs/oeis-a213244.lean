import OMAStatements.S_oeis_a213244

-- Proof of Colin Barker's conjectures in OEIS A213244 (original formalization by @ivillar).
-- Idea: the nonzero 5th powers of GF(2^n) form the image of y ↦ y^5 on the cyclic group
-- GF(2^n)ˣ of order M = 2^n - 1, so a(n) = M / gcd(M, 5) (the formula of the OEIS entry); as 5
-- divides 2^4 - 1, gcd(M, 5) is 4-periodic in n, which gives the recurrence and the g.f.

namespace OMAA213244Helpers

open PowerSeries OMA.S_oeis_a213244

theorem card_pow (n : ℕ) (hn : n ≠ 0) :
    a n = (2 ^ n - 1) / Nat.gcd (2 ^ n - 1) 5 := by
  classical
  have e : {x : GaloisField 2 n // x ≠ 0 ∧ ∃ y : GaloisField 2 n, y ^ 5 = x} ≃
      (powMonoidHom 5 : (GaloisField 2 n)ˣ →* (GaloisField 2 n)ˣ).range :=
    { toFun := fun x => ⟨Units.mk0 x.1 x.2.1, by
          obtain ⟨y, hy⟩ := x.2.2
          have hy0 : y ≠ 0 := by
            rintro rfl
            exact x.2.1 (by rw [← hy]; simp)
          exact ⟨Units.mk0 y hy0, Units.ext (by simp [hy])⟩⟩
      invFun := fun u => ⟨(u.1 : GaloisField 2 n), u.1.ne_zero, by
          obtain ⟨v, hv⟩ := u.2
          exact ⟨(v : GaloisField 2 n), by rw [← hv]; simp⟩⟩
      left_inv := fun x => by ext; simp
      right_inv := fun u => by ext; simp }
  unfold a
  rw [Nat.card_congr e, IsCyclic.card_powMonoidHom_range, Nat.card_units, GaloisField.card 2 n hn]

theorem gcd_period (m : ℕ) : Nat.gcd (2 ^ (m + 4) - 1) 5 = Nat.gcd (2 ^ m - 1) 5 := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have e : 2 ^ (m + 4) - 1 = (2 ^ m - 1) + (2 ^ m * 3) * 5 := by
    rw [pow_add]; norm_num; omega
  rw [e, Nat.gcd_add_mul_right_left]

theorem mul_a (n : ℕ) (hn : n ≠ 0) :
    ((Nat.gcd (2 ^ n - 1) 5 : ℕ) : ℤ) * a n = 2 ^ n - 1 := by
  rw [card_pow n hn, ← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
  push_cast [Nat.cast_sub Nat.one_le_two_pow]
  ring

theorem recur (n : ℕ) (hn : 8 < n) : (a n : ℤ) = 17 * a (n - 4) - 16 * a (n - 8) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 4 = m + 4 by omega, show m + 8 - 8 = m by omega]
  change (a (m + 4 + 4) : ℤ) = _
  have h0 := mul_a m (by omega)
  have h1 := mul_a (m + 4) (by omega)
  have h2 := mul_a (m + 4 + 4) (by omega)
  simp only [gcd_period] at h1 h2
  simp only [pow_add] at h1 h2
  have hg : ((Nat.gcd (2 ^ m - 1) 5 : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_right (2 ^ m - 1) (by decide : 0 < 5)).ne'
  apply mul_left_cancel₀ hg
  linear_combination h2 - 17 * h1 + 16 * h0

theorem key : mk (fun n => if n = 0 then (0 : ℚ) else a n) * ((X - 1) * (X + 1) * (2 * X - 1) * (2 * X + 1) * (X ^ 2 + 1) * (4 * X ^ 2 + 1)) = X * (8 * X ^ 6 + 12 * X ^ 5 + 14 * X ^ 4 + 3 * X ^ 3 + 7 * X ^ 2 + 3 * X + 1) := by
  set F := mk (fun n => if n = 0 then (0 : ℚ) else a n)
  have left : F * ((X - 1) * (X + 1) * (2 * X - 1) * (2 * X + 1) *
      (X ^ 2 + 1) * (4 * X ^ 2 + 1)) =
      F - C 17 * (X ^ 4 * F) + C 16 * (X ^ 8 * F) := by
    simp only [map_ofNat]
    ring
  have right : (X * (8 * X ^ 6 + 12 * X ^ 5 + 14 * X ^ 4 + 3 * X ^ 3 +
      7 * X ^ 2 + 3 * X + 1) : ℚ⟦X⟧) =
      X ^ 1 + C 3 * X ^ 2 + C 7 * X ^ 3 + C 3 * X ^ 4 + C 14 * X ^ 5 + C 12 * X ^ 6 + C 8 * X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [left, right]
  ext n
  simp only [F, map_add, map_sub, coeff_C_mul, coeff_mk, coeff_X_pow_mul', coeff_X_pow]
  by_cases hn : n ≤ 8
  · interval_cases n <;> norm_num [card_pow]
  · have h := congrArg (Int.cast : ℤ → ℚ) (recur n (by omega))
    push_cast at h
    simp (disch := omega) only [if_pos, if_neg, mul_zero, add_zero, zero_add, sub_zero]
    linear_combination h

end OMAA213244Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a213244.main := by
  refine ⟨OMAA213244Helpers.recur, ?_⟩
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp), OMAA213244Helpers.key]
