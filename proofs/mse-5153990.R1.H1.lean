import OMAReductions.R_mse_5153990_R1

/-! A Pythagorean area N, with a² + b² = c² and a b = 2N, is divisible by 6. Modulo 3, one leg
is divisible by 3. Modulo 8, a b ≡ 0 or 4, so 4 ∣ a b. Hence 12 ∣ 2N. If N = F_n, then
2 ∣ F_n and 3 ∣ F_n. Since gcd(F_n, F_k) = F_(gcd(n, k)) (`Nat.fib_gcd`) with F_3 = 2 and
F_4 = 3, this forces gcd(n, 3) = 3 and gcd(n, 4) = 4, so 3 ∣ n, 4 ∣ n and 12 ∣ n. -/

namespace OMA.MSE5153990

theorem three_dvd_mul (a b c : ℕ) (h : a ^ 2 + b ^ 2 = c ^ 2) : 3 ∣ a * b := by
  have key : ∀ x y z : ZMod 3, x ^ 2 + y ^ 2 = z ^ 2 → x * y = 0 := by decide
  have h' : (a : ZMod 3) ^ 2 + (b : ZMod 3) ^ 2 = (c : ZMod 3) ^ 2 := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 3) h
  have h0 := key _ _ _ h'
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h0
  exact h0

theorem four_dvd_mul (a b c : ℕ) (h : a ^ 2 + b ^ 2 = c ^ 2) : 4 ∣ a * b := by
  have key : ∀ x y z : ZMod 8, x ^ 2 + y ^ 2 = z ^ 2 → x * y = 0 ∨ x * y = 4 := by decide
  have h' : (a : ZMod 8) ^ 2 + (b : ZMod 8) ^ 2 = (c : ZMod 8) ^ 2 := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 8) h
  rcases key _ _ _ h' with h0 | h4
  · rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h0
    exact Nat.dvd_trans (by norm_num) h0
  · have h8 : ((a * b : ℕ) : ZMod 8) = ((4 : ℕ) : ZMod 8) := by
      push_cast
      exact h4
    rw [ZMod.natCast_eq_natCast_iff'] at h8
    omega

theorem three_dvd_of_two_dvd_fib (n : ℕ) (h : 2 ∣ Nat.fib n) : 3 ∣ n := by
  have hg := Nat.fib_gcd n 3
  have hf3 : Nat.fib 3 = 2 := by decide
  rw [hf3, Nat.gcd_eq_right h] at hg
  have hdn : Nat.gcd n 3 ∣ n := Nat.gcd_dvd_left n 3
  have hd : Nat.gcd n 3 ∣ 3 := Nat.gcd_dvd_right n 3
  have hpos : 0 < Nat.gcd n 3 := Nat.gcd_pos_of_pos_right n (by norm_num)
  have hle : Nat.gcd n 3 ≤ 3 := Nat.le_of_dvd (by norm_num) hd
  generalize Nat.gcd n 3 = g at hg hdn hd hpos hle
  interval_cases g
  · simp at hg
  · omega
  · exact hdn

theorem four_dvd_of_three_dvd_fib (n : ℕ) (h : 3 ∣ Nat.fib n) : 4 ∣ n := by
  have hg := Nat.fib_gcd n 4
  have hf4 : Nat.fib 4 = 3 := by decide
  rw [hf4, Nat.gcd_eq_right h] at hg
  have hdn : Nat.gcd n 4 ∣ n := Nat.gcd_dvd_left n 4
  have hd : Nat.gcd n 4 ∣ 4 := Nat.gcd_dvd_right n 4
  have hpos : 0 < Nat.gcd n 4 := Nat.gcd_pos_of_pos_right n (by norm_num)
  have hle : Nat.gcd n 4 ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  generalize Nat.gcd n 4 = g at hg hdn hd hpos hle
  interval_cases g
  · simp at hg
  · simp at hg
  · omega
  · exact hdn

end OMA.MSE5153990

theorem OMA.solution : OMA.R_mse_5153990_R1.H1 := by
  rintro n ⟨-, a, b, c, -, -, -, habc, hN⟩
  have h3 := OMA.MSE5153990.three_dvd_mul a b c habc
  have h4 := OMA.MSE5153990.four_dvd_mul a b c habc
  rw [hN] at h3 h4
  have h2f : 2 ∣ Nat.fib n := by omega
  have h3f : 3 ∣ Nat.fib n := by omega
  have := OMA.MSE5153990.three_dvd_of_two_dvd_fib n h2f
  have := OMA.MSE5153990.four_dvd_of_three_dvd_fib n h3f
  omega
