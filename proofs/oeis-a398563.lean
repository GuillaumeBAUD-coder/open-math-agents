import OMAStatements.S_oeis_a398563
import Mathlib

open OMA.S_oeis_a398563

theorem OMA.solution : type_of% @OMA.S_oeis_a398563.main := by
  intro hT
  refine Set.Finite.subset ((((Set.finite_singleton 19).union (hT.image fun r => (r + 2) ^ 3 - 8)).union
    (hT.image fun r => (r + 2) ^ 3 - r ^ 3))) ?_
  rintro n ⟨⟨hn0, hΩ⟩, p, q, hp, hq, hqp, rfl⟩
  obtain ⟨d, rfl⟩ : ∃ d, p = q + d := ⟨p - q, by omega⟩
  have hfac : (q + d) ^ 3 - q ^ 3 = d * ((q + d) ^ 2 + (q + d) * q + q ^ 2) := by
    apply Nat.sub_eq_of_eq_add; ring
  have hq2 := hq.two_le
  have hp2 := hp.two_le
  rcases hq.eq_two_or_odd with hq2' | hqo <;> rcases hp.eq_two_or_odd with hp2' | hpo
  · omega
  · -- q = 2
    subst hq2'
    by_cases hd1 : d = 1
    · subst hd1; left; left; simp
    · have hd2 : 2 ≤ d := by omega
      have hM : 2 ≤ (2 + d) ^ 2 + (2 + d) * 2 + 2 ^ 2 := by nlinarith
      rw [hfac, ArithmeticFunction.cardFactors_mul (by omega) (by omega)] at hΩ
      have h1 : ArithmeticFunction.cardFactors d ≠ 0 := by
        rw [Ne, ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]; omega
      have h2 : ArithmeticFunction.cardFactors ((2 + d) ^ 2 + (2 + d) * 2 + 2 ^ 2) ≠ 0 := by
        rw [Ne, ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]; omega
      have hdp : d.Prime := ArithmeticFunction.cardFactors_eq_one_iff_prime.mp (by omega)
      left; right
      refine ⟨d, ⟨hdp, by rw [add_comm]; exact hp⟩, ?_⟩
      simp only
      rw [add_comm d 2]
      norm_num
  · omega
  · -- q odd, p odd
    have hd2 : 2 ≤ d := by omega
    have hM : 2 ≤ (q + d) ^ 2 + (q + d) * q + q ^ 2 := by nlinarith
    rw [hfac, ArithmeticFunction.cardFactors_mul (by omega) (by omega)] at hΩ
    have h1 : ArithmeticFunction.cardFactors d ≠ 0 := by
      rw [Ne, ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]; omega
    have h2 : ArithmeticFunction.cardFactors ((q + d) ^ 2 + (q + d) * q + q ^ 2) ≠ 0 := by
      rw [Ne, ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]; omega
    have hdp : d.Prime := ArithmeticFunction.cardFactors_eq_one_iff_prime.mp (by omega)
    have hd : d = 2 := by
      rcases hdp.eq_two_or_odd with h | h
      · exact h
      · omega
    subst hd
    right
    refine ⟨q, ⟨hq, hp⟩, ?_⟩
    simp only
