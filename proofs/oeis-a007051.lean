import OMAStatements.S_oeis_a007051

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: with a(n) = (3^n+1)/2 we have 2*a(n) = 3^n + 1, so a(n)/(a(n)-1) = (3^n+1)/(3^n-1).
-- Induction on n >= 1: s(1) = 2 = 4/2, and if s = (t+1)/(t-1) with t = 3^n then
-- (2s+1)/(s+2) = (3t+1)/(3t-1).

namespace OMA.A007051Proof

open OMA.S_oeis_a007051

lemma a_cast (n : ℕ) : (a n : ℚ) = ((3 : ℚ) ^ n + 1) / 2 := by
  have h : 2 ∣ 3 ^ n + 1 := by
    have : Odd (3 ^ n) := Odd.pow (by decide)
    exact (this.add_one).two_dvd
  unfold a
  rw [Nat.cast_div h (by norm_num)]
  push_cast
  ring

lemma key (n : ℕ) : (a n : ℚ) / ((a n : ℚ) - 1) = ((3 : ℚ) ^ n + 1) / ((3 : ℚ) ^ n - 1) := by
  rw [a_cast]
  have h1 : ((3 : ℚ) ^ n + 1) / 2 - 1 = ((3 : ℚ) ^ n - 1) / 2 := by ring
  rw [h1, div_div_div_cancel_right₀ (by norm_num : (2 : ℚ) ≠ 0)]

end OMA.A007051Proof

open OMA.S_oeis_a007051 OMA.A007051Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a007051.main := by
  intro s h1 hrec n hn
  rw [key]
  induction n, hn using Nat.le_induction with
  | base => rw [h1]; norm_num
  | succ m hm ih =>
    rw [hrec (m + 1) (by omega), Nat.add_sub_cancel, ih]
    have ht : (1 : ℚ) < 3 ^ m := one_lt_pow₀ (by norm_num) (by omega)
    have hne : (3 : ℚ) ^ m - 1 ≠ 0 := by linarith
    have hne2 : (3 : ℚ) ^ (m + 1) - 1 ≠ 0 := by rw [pow_succ]; linarith
    have hn1 : (3 : ℚ) ^ m + 1 + 2 * ((3 : ℚ) ^ m - 1) ≠ 0 := by nlinarith
    have hn2 : (3 : ℚ) ^ m * 3 - 1 ≠ 0 := by nlinarith
    rw [pow_succ]
    have e : 2 * (((3 : ℚ) ^ m + 1) / ((3 : ℚ) ^ m - 1)) + 1
        = ((3 : ℚ) ^ m * 3 + 1) / ((3 : ℚ) ^ m - 1) := by
      field_simp; ring
    have e2 : ((3 : ℚ) ^ m + 1) / ((3 : ℚ) ^ m - 1) + 2
        = ((3 : ℚ) ^ m * 3 - 1) / ((3 : ℚ) ^ m - 1) := by
      field_simp; ring
    rw [e, e2, div_div_div_cancel_right₀ hne]
