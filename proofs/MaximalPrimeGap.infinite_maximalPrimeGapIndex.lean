import FormalConjectures.Wikipedia.MaximalPrimeGap

/-!
# Shorter proof of `MaximalPrimeGap.infinite_maximalPrimeGapIndex`
-/

open MaximalPrimeGap

theorem OMA.solution : type_of% @MaximalPrimeGap.infinite_maximalPrimeGapIndex := by
  classical
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  set M := (Finset.range (N + 1)).sup primeGap
  have hex : ∃ n, M < primeGap n := by
    set x := (M + 1).factorial + 1
    set c := Nat.count Nat.Prime (x + 1)
    have hc0 : 0 < c := lt_of_lt_of_le (by decide : 0 < Nat.count Nat.Prime 3)
      (Nat.count_monotone _ (by have := Nat.factorial_pos (M + 1); omega))
    refine ⟨c - 1, ?_⟩
    have hlow : Nat.nth Nat.Prime (c - 1) < x + 1 := Nat.nth_lt_of_lt_count (by omega)
    have hhigh : x + 1 ≤ Nat.nth Nat.Prime c := Nat.le_nth_count Nat.infinite_setOfPred_prime _
    have hp : (Nat.nth Nat.Prime c).Prime := Nat.prime_nth_prime c
    have hfar : x + M < Nat.nth Nat.Prime c := by
      by_contra h
      set j := Nat.nth Nat.Prime c - (M + 1).factorial
      have hd : j ∣ Nat.nth Nat.Prime c := by
        rw [show Nat.nth Nat.Prime c = (M + 1).factorial + j by omega]
        exact (Nat.dvd_factorial (by omega) (by omega)).add dvd_rfl
      rcases hp.eq_one_or_self_of_dvd j hd with h1 | h2 <;>
        (have := Nat.factorial_pos (M + 1); omega)
    rw [primeGap, show c - 1 + 1 = c by omega]; omega
  refine ⟨Nat.find hex, fun m hm => lt_of_le_of_lt (not_lt.mp (Nat.find_min hex hm)) (Nat.find_spec hex), ?_⟩
  by_contra hle
  exact absurd (Nat.find_spec hex) (not_lt.mpr (Finset.le_sup (f := primeGap) (Finset.mem_range.mpr (by omega))))
