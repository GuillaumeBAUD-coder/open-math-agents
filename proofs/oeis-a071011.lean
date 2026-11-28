import OMAStatements.S_oeis_a071011
import Mathlib

namespace A071011

lemma geom_dvd (q : ℕ) (hq : 4 ∣ q + 1) (j : ℕ) : 4 ∣ ∑ k ∈ Finset.range (2 * j), q ^ k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
    have h : q ^ (2 * j) + q ^ (2 * j + 1) = q ^ (2 * j) * (q + 1) := by ring
    rw [add_assoc, h]
    exact dvd_add ih (dvd_mul_of_dvd_right hq _)

end A071011

theorem OMA.solution : type_of% @OMA.S_oeis_a071011.main := by
  intro m hm
  rw [Nat.eq_sq_add_sq_iff] at hm
  simp only [not_forall] at hm
  obtain ⟨q, hqm, hq4, hodd⟩ := hm
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqm
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hqm
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨j, hj⟩ := hodd
  set e := padicValNat q m with he
  have hfac : m.factorization q = e := Nat.factorization_def m hq
  have hsplit : q ^ e * (m / q ^ e) = m := by
    rw [← hfac]; exact Nat.ordProj_mul_ordCompl_eq_self m q
  have hcop : Nat.Coprime (q ^ e) (m / q ^ e) := by
    rw [← hfac]
    exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hq hm0)
  have h1 : ArithmeticFunction.sigma 1 m =
      ArithmeticFunction.sigma 1 (q ^ e) * ArithmeticFunction.sigma 1 (m / q ^ e) := by
    rw [← ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsplit]
  have h2 : 4 ∣ ArithmeticFunction.sigma 1 (q ^ e) := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hq, hj,
      show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
    exact A071011.geom_dvd q (by omega) (j + 1)
  rw [h1]
  exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left h2 _)
