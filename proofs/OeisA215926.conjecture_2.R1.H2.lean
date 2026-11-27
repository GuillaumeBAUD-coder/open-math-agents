import OMAReductions.R_OeisA215926_conjecture_2_R1

/-! For `q < 2 * 2^j`, the divisor sum of `2^j * q` is at least twice the number. -/
-- Credit: @Halldon

open Finset

private theorem two_power_sum (j : ℕ) :
    (∑ i ∈ range (j + 1), (2 : ℕ)^i) + 1 = 2 * 2^j := by
  induction j with
  | zero => decide
  | succ j ih => rw [sum_range_succ, pow_succ]; omega

theorem OMA.solution : OMA.R_OeisA215926_conjecture_2_R1.H2 := by
  intro j q hp hq hqBound
  let d := (2 : ℕ)^j
  let u := ∑ a ∈ d.divisors, a
  have hu : u + 1 = 2 * d := by
    change (∑ a ∈ ((2 : ℕ)^j).divisors, a) + 1 = 2 * (2 : ℕ)^j
    rw [Nat.sum_divisors_prime_pow Nat.prime_two]
    exact two_power_sum j
  have hqu : q ≤ u := by change q < 2*d at hqBound; omega
  have hcop : d.Coprime q :=
    (Nat.coprime_of_lt_prime (by decide : (2 : ℕ) ≠ 0) hq hp).symm.pow_left j
  have hsum : (∑ a ∈ (d*q).divisors, a) = u * (1 + q) := by
    rw [hcop.sum_divisors_mul, hp.divisors]
    simp [u, Ne.symm hp.ne_one, Nat.add_comm]
  have hpos : 0 < d*q := by dsimp [d]; exact Nat.mul_pos (by positivity) hp.pos
  have hle : 2 * (d*q) ≤ ∑ a ∈ (d*q).divisors, a := calc
    2 * (d*q) = (u+1)*q := by rw [hu]; ring
    _ = u*q+q := by ring
    _ ≤ u*q+u := Nat.add_le_add_left hqu _
    _ = u*(1+q) := by ring
    _ = ∑ a ∈ (d*q).divisors, a := hsum.symm
  change (d*q).Perfect ∨ (d*q).Abundant
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, Nat.abundant_iff_sum_divisors]
  omega
