import OMAStatements.S_oeis_a274232
import Mathlib

/-!
# A274232: closed form and recurrence

Let P(N) = Σ_{c ≤ N/3} (floor((N - c)/2) + 1 - c) be the number of partitions of N into at most
three parts. Every summand with c ≤ N/3 grows by 3 when N grows by 6, and the two new summands
contribute N mod 3 + 3, so P(N + 6) = P(N) + N + 6. Induction on q then gives
12 P(N) + 1 = (N + 3)^2 for N = 6q + 2 and N = 6q + 4 (base cases P(2) = 2, P(4) = 4). Since
2^n ≡ 2 or 4 (mod 6) for n ≥ 1, 12 a(n) = 4^n + 6*2^n + 8, and the recurrence follows because
1, 2 and 4 are the roots of x^3 - 7x^2 + 14x - 8.
-/

namespace PA274232

def P (N : ℕ) : ℕ := ∑ c ∈ Finset.range (N / 3 + 1), ((N - c) / 2 + 1 - c)

theorem a_eq (n : ℕ) : OMA.S_oeis_a274232.a n = P (2 ^ n) := by
  unfold OMA.S_oeis_a274232.a P
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]

theorem P_six (N : ℕ) : P (N + 6) = P N + N + 6 := by
  unfold P
  rw [show (N + 6) / 3 + 1 = N / 3 + 1 + 1 + 1 by omega, Finset.sum_range_succ,
    Finset.sum_range_succ]
  have h : ∑ c ∈ Finset.range (N / 3 + 1), ((N + 6 - c) / 2 + 1 - c) =
      ∑ c ∈ Finset.range (N / 3 + 1), (((N - c) / 2 + 1 - c) + 3) :=
    Finset.sum_congr rfl fun c hc => by
      rw [Finset.mem_range] at hc
      omega
  rw [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

theorem P_closed (q : ℕ) :
    12 * P (6 * q + 2) + 1 = (6 * q + 5) ^ 2 ∧ 12 * P (6 * q + 4) + 1 = (6 * q + 7) ^ 2 := by
  induction q with
  | zero => exact ⟨by decide, by decide⟩
  | succ q ih =>
    rw [show 6 * (q + 1) + 2 = 6 * q + 2 + 6 by ring, show 6 * (q + 1) + 4 = 6 * q + 4 + 6 by ring,
      P_six, P_six]
    constructor
    · nlinarith [ih.1]
    · nlinarith [ih.2]

theorem pow_mod_six (n : ℕ) (hn : 0 < n) : 2 ^ n % 6 = 2 ∨ 2 ^ n % 6 = 4 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      left
      norm_num
    · rw [pow_succ]
      rcases ih h with h' | h' <;> omega

theorem closed (n : ℕ) (hn : 0 < n) : 12 * P (2 ^ n) = 8 + 3 * 2 ^ (n + 1) + 4 ^ n := by
  have h4 : 4 ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  rw [h4, pow_succ]
  rcases pow_mod_six n hn with h | h
  · have hq := (P_closed (2 ^ n / 6)).1
    rw [show 6 * (2 ^ n / 6) + 2 = 2 ^ n by omega, show 6 * (2 ^ n / 6) + 5 = 2 ^ n + 3 by omega] at hq
    nlinarith [hq]
  · have hq := (P_closed (2 ^ n / 6)).2
    rw [show 6 * (2 ^ n / 6) + 4 = 2 ^ n by omega, show 6 * (2 ^ n / 6) + 7 = 2 ^ n + 3 by omega] at hq
    nlinarith [hq]

theorem closed_int (n : ℕ) (hn : 0 < n) :
    12 * (P (2 ^ n) : ℤ) = 8 + 3 * 2 ^ (n + 1) + 4 ^ n := by
  exact_mod_cast closed n hn

end PA274232

theorem OMA.solution : type_of% @OMA.S_oeis_a274232.main := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rw [PA274232.a_eq]
    exact PA274232.closed n hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, PA274232.a_eq]
    have h4 := PA274232.closed_int (m + 4) (by omega)
    have h3 := PA274232.closed_int (m + 3) (by omega)
    have h2 := PA274232.closed_int (m + 2) (by omega)
    have h1 := PA274232.closed_int (m + 1) (by omega)
    have key : 12 * ((PA274232.P (2 ^ (m + 4)) : ℤ) - 7 * PA274232.P (2 ^ (m + 3)) +
        14 * PA274232.P (2 ^ (m + 2)) - 8 * PA274232.P (2 ^ (m + 1))) = 0 := by
      linear_combination h4 - 7 * h3 + 14 * h2 - 8 * h1
    linarith
