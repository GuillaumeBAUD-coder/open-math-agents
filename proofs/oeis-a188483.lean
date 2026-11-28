import OMAStatements.S_oeis_a188483
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

namespace OMA.D_oeis_a188483

open OMA.S_oeis_a188483

private lemma sigma_eq_arith (n : ℕ) : sigma n = ArithmeticFunction.sigma 1 n := by
  unfold sigma
  rw [ArithmeticFunction.sigma_apply]
  simp

private lemma sigma_prime_sq {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 (p ^ 2) = 1 + p + p ^ 2 := by
  rw [ArithmeticFunction.sigma_apply, Nat.divisors_prime_pow hp]
  rw [Finset.sum_map]
  simp [Finset.sum_range_succ]

private theorem disprove_main : ¬ (type_of% @OMA.S_oeis_a188483.main) := by
  intro h
  have h550564 := h (742 ^ 2) (by norm_num)
  apply h550564
  refine ⟨101, ?_⟩
  rw [sigma_eq_arith]
  have hfac : 742 ^ 2 = (2 ^ 2 * 7 ^ 2) * 53 ^ 2 := by norm_num
  have hcop1 : Nat.Coprime (2 ^ 2 * 7 ^ 2) (53 ^ 2) := by decide
  have hcop2 : Nat.Coprime (2 ^ 2) (7 ^ 2) := by decide
  have hmul := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  rw [hfac, hmul.map_mul_of_coprime hcop1, hmul.map_mul_of_coprime hcop2]
  rw [sigma_prime_sq (by decide), sigma_prime_sq (by decide), sigma_prime_sq (by decide)]
  norm_num

end OMA.D_oeis_a188483

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a188483.main) :=
  OMA.D_oeis_a188483.disprove_main
