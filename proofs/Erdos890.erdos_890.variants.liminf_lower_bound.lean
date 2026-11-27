import FormalConjectures.ErdosProblems.«890»

/-!
Every term contributes one prime factor. Apart from at most one power of two,
each even term contributes a second. For an odd-length interval, the only
additional case needed is that three successive large integers cannot all be
prime powers. This gives a lower bound of k + ⌊(k-1)/2⌋.
-/

namespace OMA.E890

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.omega Nat.Prime

-- The following modular calculations are from @rorcores's proof of
-- Erdos889.erdos_889.variants.v0_gt_1.
/-- Powers of `3` modulo `16` and modulo `5`: the two residues determine each other. -/
lemma three_pow_mod (c : ℕ) :
    (3 ^ c % 16 = 1 ∧ 3 ^ c % 5 = 1) ∨ (3 ^ c % 16 = 3 ∧ 3 ^ c % 5 = 3) ∨
    (3 ^ c % 16 = 9 ∧ 3 ^ c % 5 = 4) ∨ (3 ^ c % 16 = 11 ∧ 3 ^ c % 5 = 2) := by
  induction c with
  | zero => left; norm_num
  | succ k ih =>
    have e : 3 ^ (k + 1) = 3 ^ k * 3 := pow_succ 3 k
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; left; constructor <;> omega
    · right; right; left; constructor <;> omega
    · right; right; right; constructor <;> omega
    · left; constructor <;> omega

/-- Powers of `2` modulo `3`, according to the parity of the exponent. -/
lemma two_pow_mod_three (a : ℕ) :
    (a % 2 = 0 ∧ 2 ^ a % 3 = 1) ∨ (a % 2 = 1 ∧ 2 ^ a % 3 = 2) := by
  induction a with
  | zero => left; norm_num
  | succ k ih =>
    have e : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; constructor <;> omega
    · left; constructor <;> omega

lemma two_pow_mod_sixteen {x : ℕ} (hx : 4 ≤ x) : 2 ^ x % 16 = 0 := by
  obtain ⟨y, rfl⟩ : ∃ y, x = 4 + y := ⟨x - 4, by omega⟩
  rw [pow_add]
  norm_num

/-- `2 ^ x + 1` is not a power of `3` when `x ≥ 4`: modulo `16` the exponent of `3` would be a
multiple of `4`, and then `5` would divide `2 ^ x`. -/
lemma two_pow_add_one_ne_three_pow (x c : ℕ) (hx : 4 ≤ x) : 2 ^ x + 1 ≠ 3 ^ c := by
  intro h
  have h16 := two_pow_mod_sixteen hx
  have h3 := three_pow_mod c
  have h5 : 5 ∣ 2 ^ x := Nat.dvd_of_mod_eq_zero (by omega)
  have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h5
  omega


private lemma power_of_one {p m : ℕ} (hp : p.Prime) (hd : p ∣ m) (hw : ω m = 1) :
    ∃ a : ℕ, m = p ^ a := by
  obtain ⟨q, a, hq, _, he⟩ := (isPrimePow_nat_iff _).mp (cardDistinctFactors_eq_one_iff.mp hw)
  subst m
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd)
  exact ⟨_, rfl⟩

private lemma spaced {a b : ℕ} (h : 2 ^ a < 2 ^ b) : 2 * 2 ^ a ≤ 2 ^ b := by
  have hab : a < b := by_contra fun hc ↦ (not_lt_of_ge
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hc))) h
  simpa [pow_succ, Nat.mul_comm] using Nat.pow_le_pow_right (by decide : 0 < 2) hab

private lemma bad_pair {m : ℕ} (hm : 2 ≤ m) (h : ω m + ω (m + 1) < 3) :
    ∃ a : ℕ, m ≤ 2 ^ a ∧ 2 ^ a ≤ m + 1 := by
  have h₀ := cardDistinctFactors_pos.mpr (show 1 < m by omega)
  have h₁ := cardDistinctFactors_pos.mpr (show 1 < m + 1 by omega)
  by_cases he : 2 ∣ m
  · obtain ⟨a, ha⟩ := power_of_one Nat.prime_two he (by omega : ω m = 1)
    exact ⟨a, by omega, by omega⟩
  · obtain ⟨a, ha⟩ := power_of_one Nat.prime_two (by omega : 2 ∣ m + 1) (by omega : ω (m+1) = 1)
    exact ⟨a, by omega, by omega⟩

private lemma triple (m : ℕ) (hm : 32 ≤ m) : 4 ≤ ω m + ω (m + 1) + ω (m + 2) := by
  by_contra! h
  have h₀ := cardDistinctFactors_pos.mpr (show 1 < m by omega)
  have h₁ := cardDistinctFactors_pos.mpr (show 1 < m + 1 by omega)
  have h₂ := cardDistinctFactors_pos.mpr (show 1 < m + 2 by omega)
  by_cases he : 2 ∣ m
  · obtain ⟨a,ha⟩ := power_of_one Nat.prime_two he (by omega : ω m = 1)
    obtain ⟨b,hb⟩ := power_of_one Nat.prime_two (by omega : 2 ∣ m+2) (by omega : ω (m+2)=1)
    have := spaced (show 2^a < 2^b by omega)
    omega
  obtain ⟨a,ha⟩ := power_of_one Nat.prime_two (by omega : 2 ∣ m+1) (by omega : ω (m+1)=1)
  have ha4 : 4 ≤ a := by
    by_contra! hsmall
    interval_cases a <;> norm_num at ha <;> omega
  rcases two_pow_mod_three a with hmod | hmod
  · obtain ⟨b,hb⟩ := power_of_one Nat.prime_three (by omega : 3 ∣ m) (by omega : ω m=1)
    have h16 := two_pow_mod_sixteen ha4
    rcases three_pow_mod b with hh | hh | hh | hh <;> omega
  · obtain ⟨b,hb⟩ := power_of_one Nat.prime_three (by omega : 3 ∣ m+2) (by omega : ω (m+2)=1)
    exact two_pow_add_one_ne_three_pow a b ha4 (by omega)

private def total (n k : ℕ) := ∑ i ∈ range k, ω (n+i)

private lemma count_bound (k n : ℕ) (hn : 32 ≤ n) (hs : k ≤ n) :
    k + (k-1)/2 ≤ total n k := by
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    by_cases hsmall : k < 4
    · interval_cases k
      · simp [total]
      · simp only [total, sum_range_one, Nat.add_zero]
        have h := cardDistinctFactors_pos.mpr (show 1 < n by omega)
        omega
      · have h₀ := cardDistinctFactors_pos.mpr (show 1 < n by omega)
        have h₁ := cardDistinctFactors_pos.mpr (show 1 < n + 1 by omega)
        simp [total, sum_range_succ]
        omega
      · simpa [total, sum_range_succ] using triple n hn
    let j := k - 2
    have hj : k = j + 2 := by dsimp [j]; omega
    have hi := ih j (by omega) (n+2) (by omega) (by omega)
    have hi' := ih j (by omega) n hn (by omega)
    have right : total n k = total n j + ω (n+j) + ω (n+j+1) := by
      rw [hj]; simp [total, sum_range_succ, Nat.add_assoc]
    have left : total n k = ω n + ω (n+1) + total (n+2) j := by
      rw [show k = 2+j by omega]
      simp [total, sum_range_add, sum_range_succ, Nat.add_assoc]
    by_cases hg : 3 ≤ ω n + ω (n+1)
    · omega
    by_cases hg' : 3 ≤ ω (n+j) + ω (n+j+1)
    · omega
    obtain ⟨a, ha₀, ha₁⟩ := bad_pair (by omega : 2 ≤ n) (by omega)
    obtain ⟨b, hb₀, hb₁⟩ := bad_pair (by omega : 2 ≤ n+j) (by omega)
    have := spaced (show 2^a < 2^b by omega)
    omega

private lemma prime_bound (k : ℕ) : π k ≤ (k+1)/2 := by
  by_cases hk : k < 9
  · interval_cases k <;> decide
  obtain ⟨j,rfl⟩ : ∃ j, k = 9+j := ⟨k-9, by omega⟩
  have h := Nat.primeCounting_add_le (a := 2) (k := 9) (by decide) (by decide) j
  have h₉ : π 9 = 4 := by decide
  simp only [h₉, Nat.totient_two, one_mul] at h
  omega

end OMA.E890

open Finset Filter
open scoped Nat.Prime ArithmeticFunction.omega

theorem OMA.solution : type_of% @Erdos890.erdos_890.variants.liminf_lower_bound := by
  intro k
  apply le_liminf_of_le (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop (max 32 k)] with n hn
  have hnat := OMA.E890.count_bound k n ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
  have hprime := OMA.E890.prime_bound k
  have h : k + π k ≤ OMA.E890.total n k + 1 := by omega
  rw [OMA.E890.total] at h
  have hreal : (k : ℝ) + (π k : ℝ) - 1 ≤ ∑ i ∈ range k, (ω (n+i) : ℝ) := by
    have h' : (k : ℝ) + (π k : ℝ) ≤ (∑ i ∈ range k, (ω (n+i) : ℝ)) + 1 := by exact_mod_cast h
    linarith
  simp only [← Nat.cast_sum] at hreal ⊢
  simpa only [EReal.coe_sub, EReal.coe_add, EReal.coe_one, EReal.coe_natCast] using
    (EReal.coe_le_coe_iff.mpr hreal)
