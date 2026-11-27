import FormalConjectures.ErdosProblems.«367»

/-! The full part divides its argument, so at most two terms give a quadratic bound. -/

open Erdos367 Asymptotics Filter

theorem OMA.solution : type_of% @Erdos367.erdos_367.variants.k_le_two := by
  intro k hk
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hprod : (∏ m ∈ Finset.Ico n (n + k), B 2 m) ≤ 4 * n ^ 2 := by
    calc
      _ ≤ (2 * n) ^ (Finset.Ico n (n + k)).card := by
        refine Finset.prod_le_pow_card _ _ _ fun m hm ↦ ?_
        obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
        have hd : B 2 m ∣ m.factorization.prod (· ^ ·) :=
          Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
        rw [Nat.prod_factorization_pow_eq_self (by omega)] at hd
        exact (Nat.le_of_dvd (by omega) hd).trans (by omega)
      _ ≤ (2 * n) ^ 2 := Nat.pow_le_pow_right (by omega) (by simpa using hk)
      _ = _ := by ring
  simp only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
    abs_of_nonneg (sq_nonneg (n : ℝ))]
  exact_mod_cast hprod
