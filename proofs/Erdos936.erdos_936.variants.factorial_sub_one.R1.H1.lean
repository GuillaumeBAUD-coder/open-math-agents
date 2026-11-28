import OMAReductions.R_Erdos936_erdos_936_variants_factorial_sub_one_R1
import Mathlib

open scoped BigOperators

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_sub_one_R1.H1 := by
  intro c _ hc
  have hd (s : Finset ℕ) (hs : s ⊆ c.primeFactors) : (∏ p ∈ s, p ^ 2) ∣ c := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
      have hpc := hs (Finset.mem_insert_self p s)
      have hsc : s ⊆ c.primeFactors := fun _ h => hs (Finset.mem_insert_of_mem h)
      have hcop : (p ^ 2).Coprime (∏ q ∈ s, q ^ 2) := by
        apply Nat.coprime_prod_right_iff.mpr
        intro q hq
        exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hpc)
          (Nat.prime_of_mem_primeFactors (hsc hq))).mpr (fun h => hp (h ▸ hq))).pow 2 2
      rw [Finset.prod_insert hp]
      exact hcop.mul_dvd_of_dvd_of_dvd (hc p hpc) (ih hsc)
  rw [← Finset.prod_pow]
  exact hd _ Finset.Subset.rfl