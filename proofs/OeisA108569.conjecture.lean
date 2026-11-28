import FormalConjectures.OEIS.«108569»

open Nat

theorem OMA.disproof : ¬ (type_of% @OeisA108569.conjecture) := by
  intro all_even
  have w : OeisA108569.A 5095354107 := by
    refine ⟨by decide, ?_⟩
    rw [show (5095354107 : ℕ) = 3 * (1033 * 1644193) by decide,
      totient_mul (by decide), totient_mul (by decide)]
    norm_num [totient_prime]
    rw [show (8488966395 : ℕ) = 3 * (5 * (7 * (13 * (19 * 327317)))) by decide,
      totient_mul (by decide), totient_mul (by decide), totient_mul (by decide),
      totient_mul (by decide), totient_mul (by decide)]
    norm_num [totient_prime]
  have heven := all_even _ (lt_of_lt_of_le (show 0 < count OeisA108569.A 2 by decide)
    (count_monotone _ (by decide : 2 ≤ 5095354107)))
  change Even (nth OeisA108569.A (count OeisA108569.A 5095354107)) at heven
  rw [nth_count w] at heven
  exact (by decide : ¬ Even (5095354107 : ℕ)) heven
