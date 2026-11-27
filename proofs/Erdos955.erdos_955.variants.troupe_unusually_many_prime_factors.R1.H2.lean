import OMAReductions.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1
import Mathlib

/-! For composite n write n = p d with p the least prime factor, so p <= d. Then 1, d, n are distinct
divisors, s(n) >= 1 + d, and n = p d <= d^2 <= s(n)^2. -/

open scoped ArithmeticFunction.sigma

theorem OMA.solution : OMA.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1.H2 := by
  intro n hn hnp
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hp2 := hp.two_le
  obtain ⟨d, hd⟩ := Nat.minFac_dvd n
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hpd : n.minFac ≤ d := by
    have h2 : n.minFac * n.minFac ≤ n.minFac * d := by
      calc n.minFac * n.minFac = n.minFac ^ 2 := (sq _).symm
        _ ≤ n := hsq
        _ = n.minFac * d := hd
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  have hd1 : 1 < d := by omega
  have hdn : d < n := by
    rw [hd]; nlinarith
  have hsub : ({1, d, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Nat.mem_divisors]
    refine ⟨?_, by omega⟩
    rcases hx with rfl | rfl | rfl
    · exact one_dvd _
    · exact Dvd.intro_left _ hd.symm
    · exact dvd_rfl
  have hsum : ∑ x ∈ ({1, d, n} : Finset ℕ), x = 1 + d + n := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_singleton]
    ring
  have hσ : 1 + d + n ≤ σ 1 n := by
    rw [ArithmeticFunction.sigma_one_apply, ← hsum]
    exact Finset.sum_le_sum_of_subset hsub
  have hs : 1 + d ≤ Erdos955.s n := by
    unfold Erdos955.s; omega
  calc n = n.minFac * d := hd
    _ ≤ d * d := Nat.mul_le_mul_right d hpd
    _ ≤ (1 + d) * (1 + d) := Nat.mul_le_mul (by omega) (by omega)
    _ ≤ Erdos955.s n * Erdos955.s n := Nat.mul_le_mul hs hs
    _ = Erdos955.s n ^ 2 := (sq _).symm
