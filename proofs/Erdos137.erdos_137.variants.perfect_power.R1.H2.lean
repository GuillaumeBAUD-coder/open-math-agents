import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1
import Mathlib.NumberTheory.Bertrand

/-! Bertrand gives a prime above half the upper endpoint. Since it is below k,
it lies inside the product interval and its next multiple lies beyond it. -/
open Finset in
theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H2 := by
  intro k n hk gap
  obtain ⟨p,hp,hhalf,hu⟩ := Nat.exists_prime_lt_and_le_two_mul ((n+k)/2) (by omega)
  have htop : p ≤ n+k := by omega
  have hpk : p < k := by
    by_contra! h
    exact gap ⟨p,h,htop,hp⟩
  have hmem : p ∈ Ioc n (n+k) := mem_Ioc.mpr ⟨by omega, htop⟩
  refine ⟨p,hp,?_⟩
  rw [Nat.factorization_prod_apply (fun m hm => (show m ≠ 0 by have := (mem_Ioc.mp hm).1; omega))]
  rw [sum_eq_single_of_mem p hmem, hp.factorization_self]
  intro m hm hne
  apply Nat.factorization_eq_zero_of_not_dvd
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hm
  rintro ⟨a,rfl⟩
  rcases a with _ | _ | a
  · simp at hlo
  · simp at hne
  · have := Nat.mul_le_mul_left p (show 2 ≤ a + 1 + 1 by omega)
    omega
