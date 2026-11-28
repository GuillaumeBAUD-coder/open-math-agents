import OMAStatements.S_oeis_a173528
import Mathlib

/-!
# A173528: the rows `s(8 ^ k + j)` of base-8 digit sums stabilise

Adding `8 ^ k` to a number `x < 8 ^ k` just puts a digit `1` in position `k`, so the digit
sum grows by exactly `1` (induction on `k`, peeling off the last digit).  For `k ≥ n` we have
`n - 1 < 8 ^ k`, hence the entry in position `n - 1` of row `k` is `1 + s(n - 1)`.
-/

namespace OMA.S_oeis_a173528

/-- The digit sum splits off the last digit. -/
lemma sum_digits_step (b : ℕ) (hb : 1 < b) (n : ℕ) :
    (Nat.digits b n).sum = n % b + (Nat.digits b (n / b)).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.digits_def' hb hn, List.sum_cons]

/-- Adding `c * b ^ m` (a single digit `c` in position `m`) to `x < b ^ m` adds `c` to the
digit sum. -/
lemma sum_digits_mul_pow_add (b : ℕ) (hb : 1 < b) (c : ℕ) (hc : c < b) :
    ∀ m x, x < b ^ m → (Nat.digits b (c * b ^ m + x)).sum = c + (Nat.digits b x).sum := by
  intro m
  induction m with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    rw [pow_zero, mul_one, add_zero, sum_digits_step b hb c, Nat.mod_eq_of_lt hc,
      Nat.div_eq_of_lt hc, Nat.digits_zero, List.sum_nil]
  | succ m ih =>
    intro x hx
    have hb0 : 0 < b := by omega
    have h1 : (c * b ^ (m + 1) + x) % b = x % b := by
      rw [pow_succ, ← mul_assoc, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
    have h2 : (c * b ^ (m + 1) + x) / b = c * b ^ m + x / b := by
      rw [pow_succ, ← mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hb0, Nat.add_comm]
    have h3 : x / b < b ^ m := by
      rw [Nat.div_lt_iff_lt_mul hb0]
      rwa [pow_succ] at hx
    rw [sum_digits_step b hb (c * b ^ (m + 1) + x), sum_digits_step b hb x, h1, h2, ih _ h3]
    omega

end OMA.S_oeis_a173528

open OMA.S_oeis_a173528 in
theorem OMA.solution : type_of% @OMA.S_oeis_a173528.main := by
  intro n hn
  refine ⟨n, fun k hk => ?_⟩
  have hpow : k < 8 ^ k := Nat.lt_pow_self (by norm_num)
  have hlt : n - 1 < 8 ^ k := by omega
  refine ⟨by omega, ?_⟩
  have h := sum_digits_mul_pow_add 8 (by norm_num) 1 (by norm_num) k (n - 1) hlt
  rw [one_mul] at h
  exact h
