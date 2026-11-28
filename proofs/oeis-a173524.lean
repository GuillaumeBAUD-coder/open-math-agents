import OMAStatements.S_oeis_a173524
import Mathlib

/-!
# A173524: `a(n) = 1 + s₄(n - 1)`, the limit of the rows `s₄(4 ^ k + j)`

Adding `c * 4 ^ m` with a single digit `c < 4` to a number `x < 4 ^ m` adds exactly `c` to the
base-4 digit sum (induction on `m`, peeling off the last digit).  Since `m < 4 ^ (m + 1)`,
this gives `a (m + 1) = 1 + s(m)`, and then:

* for `k ≥ n`, `s(4 ^ k + n - 1) = 1 + s(n - 1) = a n`;
* for `j = c * 4 ^ k + j'` with `c ≤ 2`, `s(4 ^ k + j) = c + 1 + s(j') = 1 + s(j) = a (j + 1)`;
* `s(4 i + j) = j + s(i)` for `j < 4`, so `a (4 i + j + 1) = a (i + 1) + j`.
-/

namespace OMA.S_oeis_a173524

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

/-- The closed form `a (m + 1) = 1 + s(m)`. -/
lemma a_succ (m : ℕ) : a (m + 1) = 1 + (Nat.digits 4 m).sum := by
  have hpow : m + 1 < 4 ^ (m + 1) := Nat.lt_pow_self (by norm_num)
  have h := sum_digits_mul_pow_add 4 (by norm_num) 1 (by norm_num) (m + 1) m (by omega)
  rw [one_mul] at h
  have e : 4 ^ (m + 1) + (m + 1) - 1 = 4 ^ (m + 1) + m := by omega
  unfold a A053737
  rw [e]
  exact h

end OMA.S_oeis_a173524

open OMA.S_oeis_a173524 in
theorem OMA.solution : type_of% @OMA.S_oeis_a173524.main := by
  refine ⟨fun n hn => ⟨n, fun k hk => ?_⟩, fun k j hj => ?_, ?_, fun i j hj => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hpow : k < 4 ^ k := Nat.lt_pow_self (by norm_num)
    have h := sum_digits_mul_pow_add 4 (by norm_num) 1 (by norm_num) k m (by omega)
    rw [one_mul] at h
    have e : 4 ^ k + (m + 1) - 1 = 4 ^ k + m := by omega
    rw [a_succ, e]
    exact h
  · have hpos : 0 < 4 ^ k := by positivity
    have hj' : j % 4 ^ k < 4 ^ k := Nat.mod_lt _ hpos
    have hc : j / 4 ^ k < 3 := by
      rw [Nat.div_lt_iff_lt_mul hpos]
      exact hj
    have hsplit : j = j / 4 ^ k * 4 ^ k + j % 4 ^ k := (Nat.div_add_mod' j (4 ^ k)).symm
    have e2 := sum_digits_mul_pow_add 4 (by norm_num) (j / 4 ^ k) (by omega) k (j % 4 ^ k) hj'
    have e3 := sum_digits_mul_pow_add 4 (by norm_num) (j / 4 ^ k + 1) (by omega) k (j % 4 ^ k) hj'
    rw [← hsplit] at e2
    have e4 : (j / 4 ^ k + 1) * 4 ^ k + j % 4 ^ k = 4 ^ k + j := by
      rw [add_mul, one_mul]
      omega
    rw [e4] at e3
    rw [a_succ]
    show (Nat.digits 4 (4 ^ k + j)).sum = 1 + (Nat.digits 4 j).sum
    omega
  · rw [a_succ 0]
    simp
  · have h := sum_digits_step 4 (by norm_num) (4 * i + j)
    have h1 : (4 * i + j) % 4 = j := by omega
    have h2 : (4 * i + j) / 4 = i := by omega
    rw [h1, h2] at h
    rw [a_succ, a_succ, h]
    omega
