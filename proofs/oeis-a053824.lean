import OMAStatements.S_oeis_a053824
import Mathlib

/-!
# A053824: the rows `s(5 ^ k + j)` of base-5 digit sums stabilise

Adding `c * 5 ^ m` with a single digit `c < 5` to a number `x < 5 ^ m` adds exactly `c` to the
digit sum (induction on `m`, peeling off the last digit).

* For `j < 4 * 5 ^ k` write `j = c * 5 ^ k + j'` with `c ≤ 3`, `j' < 5 ^ k`.  Then
  `s(5 ^ (k+1) + j) = 1 + s(j) = 1 + c + s(j')` and `s(5 ^ k + j) = s((c+1) 5 ^ k + j') = c + 1 + s(j')`.
* For `k ≥ n` we have `n - 1 < 5 ^ k`, so the entry in position `n - 1` of row `k` is `1 + s(n - 1)`.
-/

namespace OMA.S_oeis_a053824

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

end OMA.S_oeis_a053824

open OMA.S_oeis_a053824 in
theorem OMA.solution : type_of% @OMA.S_oeis_a053824.main := by
  refine ⟨fun k j hj => ?_, fun n hn => ⟨n, fun k hk => ?_⟩⟩
  · -- split `j = c * 5 ^ k + j'`
    have hpos : 0 < 5 ^ k := by positivity
    have hj' : j % 5 ^ k < 5 ^ k := Nat.mod_lt _ hpos
    have hc : j / 5 ^ k < 4 := by
      rw [Nat.div_lt_iff_lt_mul hpos]
      exact hj
    have hsplit : j = j / 5 ^ k * 5 ^ k + j % 5 ^ k := (Nat.div_add_mod' j (5 ^ k)).symm
    have hjlt : j < 5 ^ (k + 1) := by rw [pow_succ]; omega
    -- the three digit sums
    have e1 := sum_digits_mul_pow_add 5 (by norm_num) 1 (by norm_num) (k + 1) j hjlt
    have e2 := sum_digits_mul_pow_add 5 (by norm_num) (j / 5 ^ k) (by omega) k (j % 5 ^ k) hj'
    have e3 := sum_digits_mul_pow_add 5 (by norm_num) (j / 5 ^ k + 1) (by omega) k (j % 5 ^ k) hj'
    rw [← hsplit] at e2
    have e4 : (j / 5 ^ k + 1) * 5 ^ k + j % 5 ^ k = 5 ^ k + j := by
      rw [add_mul, one_mul]
      omega
    rw [e4] at e3
    rw [one_mul] at e1
    show (Nat.digits 5 (5 ^ (k + 1) + j)).sum = (Nat.digits 5 (5 ^ k + j)).sum
    omega
  · have hpow : k < 5 ^ k := Nat.lt_pow_self (by norm_num)
    have hlt : n - 1 < 5 ^ k := by omega
    refine ⟨by omega, ?_⟩
    have h := sum_digits_mul_pow_add 5 (by norm_num) 1 (by norm_num) k (n - 1) hlt
    rw [one_mul] at h
    exact h
