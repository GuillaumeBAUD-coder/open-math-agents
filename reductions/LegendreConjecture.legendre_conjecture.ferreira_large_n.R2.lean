import FormalConjectures.Wikipedia.LegendreConjecture
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! A reduction to von Mangoldt mass in square intervals. An interval between consecutive
squares contains at most one power with each fixed exponent greater than one. Proper prime
powers therefore contribute at most a product of two logarithms. -/

namespace OMA.R_LegendreConjecture_legendre_conjecture_ferreira_large_n_R2

open Filter Finset ArithmeticFunction

/-- A short-interval analytic estimate, without a primality predicate in the summation. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop,
  (Nat.log 2 ((n+1)^2) : ℝ) * Real.log (((n+1)^2 : ℕ) : ℝ) <
    ∑ m ∈ Ioo (n^2) ((n+1)^2), vonMangoldt m

/-- The number of proper prime powers in an individual square interval. -/
def H2 : Prop := ∀ n : ℕ,
  (((Ioo (n^2) ((n+1)^2)).filter (fun m => IsPrimePow m ∧ ¬m.Prime)).card) ≤
    Nat.log 2 ((n+1)^2)

theorem main : H1 → H2 → type_of% @LegendreConjecture.legendre_conjecture.ferreira_large_n := by
  classical
  intro hl hc
  filter_upwards [hl] with n hn
  by_contra hnone
  let I := Ioo (n^2) ((n+1)^2)
  let S := I.filter (fun m => IsPrimePow m ∧ ¬m.Prime)
  have htotal : (∑ m ∈ I, vonMangoldt m) = ∑ m ∈ S, vonMangoldt m := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro m hm hnS
    apply vonMangoldt_eq_zero_iff.mpr
    intro hpow
    apply hnS
    refine Finset.mem_filter.mpr ⟨hm, hpow, ?_⟩
    exact fun hp => hnone ⟨m, Finset.mem_Ioo.mp hm, hp⟩
  have hlog : 0 ≤ Real.log (((n+1)^2 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ (n+1)^2 from Nat.succ_le_of_lt (by positivity)))
  have hle : (∑ m ∈ I, vonMangoldt m) ≤ _ := calc
    _ = ∑ m ∈ S, vonMangoldt m := htotal
    _ ≤ ∑ _m ∈ S, Real.log (((n+1)^2 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      obtain ⟨hlo,hhi⟩ := Finset.mem_Ioo.mp (Finset.mem_filter.mp hm).1
      exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hhi.le))
    _ = (S.card : ℝ) * Real.log (((n+1)^2 : ℕ) : ℝ) := by simp
    _ ≤ (Nat.log 2 ((n+1)^2) : ℝ) * Real.log (((n+1)^2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc n) hlog
  exact (not_lt_of_ge hle) hn

end OMA.R_LegendreConjecture_legendre_conjecture_ferreira_large_n_R2
