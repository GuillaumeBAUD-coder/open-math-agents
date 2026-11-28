import OMAStatements.S_mse_2722327
import Mathlib

-- Problem: A limit involving the Thue–Morse sequence
-- Credit: @xor2k
-- Prouhet: t (2^n + k) = - t k for k < 2^n. Splitting the range k < 2^(n+1) into
-- k and 2^n + k and expanding (2^n + k)^j binomially shows by induction on n that
-- the sum of t k * k^j over k < 2^n vanishes for all j < n. Hence for n > m the
-- partial sums of the source are exactly 0 (the k = 0 term is 0 since m > 0).

open OMA.S_mse_2722327 Filter Topology Finset

lemma t_two_mul (i : ℕ) : t (2 * i) = t i := by
  rcases i with _ | i
  · rfl
  · have h : 2 * (i + 1) = (2 * i + 1) + 1 := by ring
    rw [h, t]
    have h2 : (2 * i + 1 + 1) / 2 = i + 1 := by omega
    rw [h2, show 2 * i + 1 + 1 = 2 * (i + 1) by ring, pow_mul]
    simp

lemma t_two_mul_add_one (i : ℕ) : t (2 * i + 1) = - t i := by
  rw [t]
  have h2 : (2 * i + 1) / 2 = i := by omega
  rw [h2, pow_succ, pow_mul]
  simp

lemma t_shift (n : ℕ) : ∀ k < 2 ^ n, t (2 ^ n + k) = - t k := by
  induction n with
  | zero =>
    intro k hk
    have : k = 0 := by simpa using hk
    subst this
    norm_num [t]
  | succ n ih =>
    intro k hk
    rcases Nat.even_or_odd' k with ⟨i, rfl | rfl⟩
    · have hi : i < 2 ^ n := by rw [pow_succ] at hk; omega
      rw [show 2 ^ (n + 1) + 2 * i = 2 * (2 ^ n + i) by ring, t_two_mul, t_two_mul, ih i hi]
    · have hi : i < 2 ^ n := by rw [pow_succ] at hk; omega
      rw [show 2 ^ (n + 1) + (2 * i + 1) = 2 * (2 ^ n + i) + 1 by ring,
        t_two_mul_add_one, t_two_mul_add_one, ih i hi]

lemma prouhet (n : ℕ) : ∀ j < n, ∑ k ∈ range (2 ^ n), t k * (k : ℤ) ^ j = 0 := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rw [pow_succ, mul_two, sum_range_add]
    have h2 : ∑ k ∈ range (2 ^ n), t (2 ^ n + k) * ((2 ^ n + k : ℕ) : ℤ) ^ j
        = - ∑ i ∈ range (j + 1), ((2 : ℤ) ^ n) ^ (j - i) * (j.choose i : ℤ) *
            ∑ k ∈ range (2 ^ n), t k * (k : ℤ) ^ i := by
      have hr : (∑ i ∈ range (j + 1), ((2 : ℤ) ^ n) ^ (j - i) * (j.choose i : ℤ) *
            ∑ k ∈ range (2 ^ n), t k * (k : ℤ) ^ i)
          = ∑ k ∈ range (2 ^ n), ∑ i ∈ range (j + 1),
            ((2 : ℤ) ^ n) ^ (j - i) * (j.choose i : ℤ) * (t k * (k : ℤ) ^ i) := by
        rw [sum_comm]; simp_rw [mul_sum]
      rw [hr, ← sum_neg_distrib]
      apply sum_congr rfl
      intro k hk
      rw [t_shift n k (mem_range.mp hk)]
      push_cast
      rw [add_comm, add_pow, mul_sum, ← sum_neg_distrib]
      apply sum_congr rfl
      intro i _
      ring
    rw [h2, sum_range_succ, Nat.sub_self, pow_zero, Nat.choose_self]
    have h3 : ∑ i ∈ range j, ((2 : ℤ) ^ n) ^ (j - i) * (j.choose i : ℤ) *
        ∑ k ∈ range (2 ^ n), t k * (k : ℤ) ^ i = 0 := by
      apply sum_eq_zero
      intro i hi
      rw [ih i (by have := mem_range.mp hi; omega), mul_zero]
    rw [h3]
    push_cast
    ring

theorem OMA.solution : type_of% @OMA.S_mse_2722327.main := by
  intro m hm
  apply tendsto_atTop_of_eventually_const (i₀ := m + 1)
  intro n hn
  have hpos : 0 < 2 ^ n := by positivity
  have key := prouhet n m (by omega)
  have e : ∑ k ∈ Ico 1 (2 ^ n), (t k : ℂ) * (k : ℂ) ^ (m : ℂ)
      = ((∑ k ∈ range (2 ^ n), t k * (k : ℤ) ^ m : ℤ) : ℂ) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hpos]
    push_cast
    simp only [Complex.cpow_natCast]
    simp [zero_pow (Nat.pos_iff_ne_zero.mp hm)]
  rw [e, key]
  simp
