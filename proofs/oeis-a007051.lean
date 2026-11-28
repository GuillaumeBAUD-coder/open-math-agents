import OMAStatements.S_oeis_a007051
import Mathlib

/-!
# A007051: the iteration s(n) = (2s(n−1) + 1)/(s(n−1) + 2)

Since 3^n is odd, a(n) = (3^n + 1)/2 exactly. By induction from s(1) = 2 = a(1)/(a(1) − 1): if
s(n) = A/(A − 1) with A = (x + 1)/2 and x = 3^n, then s(n) = (x + 1)/(x − 1), and
s(n+1) = (2s(n) + 1)/(s(n) + 2) = (3x + 1)/(3x − 1) = a(n+1)/(a(n+1) − 1).
-/

namespace PA007051

theorem cast_a (n : ℕ) : (OMA.S_oeis_a007051.a n : ℚ) = ((3 : ℚ) ^ n + 1) / 2 := by
  unfold OMA.S_oeis_a007051.a
  have h : 2 ∣ 3 ^ n + 1 := by
    have : Odd (3 ^ n) := Odd.pow (by decide)
    exact even_iff_two_dvd.mp (this.add_one)
  rw [Nat.cast_div h (by norm_num)]
  push_cast
  ring

end PA007051

theorem OMA.solution : type_of% @OMA.S_oeis_a007051.main := by
  intro s h1 hrec n hn
  induction n, hn using Nat.le_induction with
  | base => rw [h1, PA007051.cast_a]; norm_num
  | succ n hn ih =>
    rw [hrec (n + 1) (by omega), show n + 1 - 1 = n by omega, ih, PA007051.cast_a,
      PA007051.cast_a]
    have hx : (3 : ℚ) ≤ 3 ^ n := by
      calc (3 : ℚ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
    rw [pow_succ]
    generalize (3 : ℚ) ^ n = x at hx ⊢
    have hx1 : x - 1 ≠ 0 := by linarith
    have hA : (x + 1) / 2 / ((x + 1) / 2 - 1) = (x + 1) / (x - 1) := by
      rw [show (x + 1) / 2 - 1 = (x - 1) / 2 by ring]
      field_simp
    rw [hA, show (x * 3 + 1) / 2 - 1 = (3 * x - 1) / 2 by ring]
    have hd1 : (x + 1) / (x - 1) + 2 ≠ 0 := by
      have : 0 < (x + 1) / (x - 1) := div_pos (by linarith) (by linarith)
      linarith
    have hd2 : (3 * x - 1) / 2 ≠ 0 := by
      have : 0 < 3 * x - 1 := by linarith
      positivity
    rw [div_eq_div_iff hd1 hd2]
    field_simp
    ring
