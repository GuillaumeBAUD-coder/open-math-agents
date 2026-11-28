import OMAReductions.R_LegendreConjecture_legendre_conjecture_ferreira_large_n_R1

open Nat in
theorem OMA.solution : OMA.R_LegendreConjecture_legendre_conjecture_ferreira_large_n_R1.H2 := by
  intro N hN m hm
  have h : (Set.ofPred Nat.Prime).Infinite := infinite_setOfPred_prime
  have : N < count Nat.Prime (m ^ 2 + 1) := (lt_nth_iff_count_lt h).2 (by omega)
  obtain ⟨n, e⟩ := exists_eq_add_one.2 (zero_lt_of_lt this)
  refine ⟨_, ⟨(count_le_iff_le_nth h).1 e.le, ?_⟩, prime_nth_prime (n + 1)⟩
  have : √(nth Nat.Prime n) ≤ m := (Real.sqrt_le_left m.cast_nonneg).2 (by exact_mod_cast Order.lt_add_one_iff.1 ((lt_nth_iff_count_lt h).1 (by omega)))
  exact_mod_cast Real.lt_sq_of_sqrt_lt (by linarith [hN n (by omega)] : √(nth Nat.Prime (n + 1)) < m + 1)
