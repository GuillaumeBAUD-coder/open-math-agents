import OMAReductions.R_mse_5153990_R1
import Mathlib

-- Step mse-5153990.R1.H1: a Pythagorean Fibonacci number F_n has 12 | n.
-- The area of an integer right triangle is a multiple of 6, and 2 | F_n forces 3 | n
-- while 3 | F_n forces 4 | n.

namespace FibPyth

lemma sq_sum_zmod3 : ∀ x y z : ZMod 3, x ^ 2 + y ^ 2 = z ^ 2 → x * y = 0 := by
  decide

lemma sq_sum_zmod8 : ∀ x y z : ZMod 8, x ^ 2 + y ^ 2 = z ^ 2 → x * y = 0 ∨ x * y = 4 := by
  decide

lemma cast_sq_sum (a b c m : ℕ) (hs : a ^ 2 + b ^ 2 = c ^ 2) :
    (a : ZMod m) ^ 2 + (b : ZMod m) ^ 2 = (c : ZMod m) ^ 2 := by
  have := congr_arg (fun n : ℕ => (n : ZMod m)) hs
  simpa [Nat.cast_add, Nat.cast_pow] using this

lemma three_dvd_prod (a b c : ℕ) (hs : a ^ 2 + b ^ 2 = c ^ 2) : 3 ∣ a * b := by
  have h := sq_sum_zmod3 (a : ZMod 3) (b : ZMod 3) (c : ZMod 3) (cast_sq_sum a b c 3 hs)
  have : ((a * b : ℕ) : ZMod 3) = 0 := by simpa using h
  exact (ZMod.natCast_eq_zero_iff (a * b) 3).mp this

lemma four_dvd_prod (a b c : ℕ) (hs : a ^ 2 + b ^ 2 = c ^ 2) : 4 ∣ a * b := by
  have h := sq_sum_zmod8 (a : ZMod 8) (b : ZMod 8) (c : ZMod 8) (cast_sq_sum a b c 8 hs)
  have hz : ((a * b : ℕ) : ZMod 8) = 0 ∨ ((a * b : ℕ) : ZMod 8) = 4 := by simpa using h
  have hmod : (a * b) % 8 = 0 ∨ (a * b) % 8 = 4 := by
    rcases hz with hz | hz
    · left
      have hcong : (a * b) ≡ 0 [MOD 8] := (ZMod.natCast_eq_natCast_iff (a * b) 0 8).mp hz
      simpa [Nat.ModEq] using hcong
    · right
      have hcong : (a * b) ≡ 4 [MOD 8] := (ZMod.natCast_eq_natCast_iff (a * b) 4 8).mp hz
      simpa [Nat.ModEq] using hcong
  rcases hmod with h0 | h4
  · exact dvd_trans (by decide : 4 ∣ 8) ((Nat.dvd_iff_mod_eq_zero).mpr h0)
  · have hdiv : a * b = 4 + 8 * ((a * b) / 8) := by
      have := Nat.mod_add_div (a * b) 8
      omega
    exact ⟨1 + 2 * ((a * b) / 8), by omega⟩

lemma twelve_dvd_prod (a b c : ℕ) (hs : a ^ 2 + b ^ 2 = c ^ 2) : 12 ∣ a * b :=
  (by decide : Nat.Coprime 3 4).mul_dvd_of_dvd_of_dvd (three_dvd_prod a b c hs) (four_dvd_prod a b c hs)

lemma six_dvd_area (N : ℕ) (h : OMA.S_mse_5153990.IsPythagorean N) : 6 ∣ N := by
  rcases h with ⟨_, a, b, c, _, _, _, hs, hab⟩
  have h12 : 12 ∣ a * b := twelve_dvd_prod a b c hs
  rw [hab] at h12
  exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) h12

lemma two_dvd_fib_three (n : ℕ) (h : 2 ∣ Nat.fib n) : 3 ∣ n := by
  have hf3 : Nat.fib 3 = 2 := by decide
  have hfib : Nat.fib (n.gcd 3) = 2 := by
    rw [Nat.fib_gcd, hf3]
    exact Nat.gcd_eq_right h
  have hor : n.gcd 3 = 1 ∨ n.gcd 3 = 3 :=
    (Nat.dvd_prime (by decide : Nat.Prime 3)).mp (Nat.gcd_dvd_right n 3)
  rcases hor with h1 | h3
  · simp [h1, Nat.fib_one] at hfib
  · rw [← h3]
    exact Nat.gcd_dvd_left n 3

lemma three_dvd_fib_four (n : ℕ) (h : 3 ∣ Nat.fib n) : 4 ∣ n := by
  have hf4 : Nat.fib 4 = 3 := by decide
  have hfib : Nat.fib (n.gcd 4) = 3 := by
    rw [Nat.fib_gcd, hf4]
    exact Nat.gcd_eq_right h
  have hle : n.gcd 4 ≤ 4 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right n 4)
  have hpos : 0 < n.gcd 4 := Nat.gcd_pos_of_pos_right n (by decide)
  interval_cases hg : n.gcd 4
  · rw [Nat.fib_one] at hfib
    omega
  · rw [Nat.fib_two] at hfib
    omega
  · have hdv := Nat.gcd_dvd_right n 4
    rw [hg] at hdv
    exact absurd hdv (by decide : ¬ 3 ∣ 4)
  · simpa [hg] using Nat.gcd_dvd_left n 4

end FibPyth

theorem OMA.solution : OMA.R_mse_5153990_R1.H1 := by
  intro n hn
  have h6 : 6 ∣ Nat.fib n := FibPyth.six_dvd_area (Nat.fib n) hn
  have h2 : 2 ∣ Nat.fib n := dvd_trans (by decide : 2 ∣ 6) h6
  have h3 : 3 ∣ Nat.fib n := dvd_trans (by decide : 3 ∣ 6) h6
  have h3n : 3 ∣ n := FibPyth.two_dvd_fib_three n h2
  have h4n : 4 ∣ n := FibPyth.three_dvd_fib_four n h3
  exact (by decide : Nat.Coprime 3 4).mul_dvd_of_dvd_of_dvd h3n h4n
