import FormalConjectures.ErdosProblems.«367»

open Erdos367 Finset

theorem OMA.solution : type_of% @Erdos367.erdos_367.variants.k_le_two := by
  intro k hk
  refine .of_bound 4 (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have h : ∏ m ∈ Ico n (n + k), B 2 m ≤ (n + 1) ^ 2 := by
    refine (prod_le_pow_card _ _ (n + 1) fun m hm => ?_).trans ?_
    · simp at hm
      exact (Nat.le_of_dvd (by omega) ((prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans
        (Nat.prod_factorization_pow_eq_self (by omega)).dvd)).trans (by omega)
    · simpa using Nat.pow_le_pow_right n.succ_pos hk
  rw [Real.norm_natCast, Real.rpow_two, norm_pow, Real.norm_natCast]
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : ((∏ m ∈ Ico n (n + k), B 2 m : ℕ) : ℝ) ≤ (n + 1) ^ 2 := by exact_mod_cast h
  nlinarith
