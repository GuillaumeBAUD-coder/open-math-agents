import OMAReductions.R_Erdos931_erdos_931_variants_exists_prime_R1
import Mathlib

open Finset

theorem L {q n k} :
    q ∈ (∏ i ∈ Icc 1 k, (n + i)).primeFactors ↔ q.Prime ∧ ∃ i, (1 ≤ i ∧ i ≤ k) ∧ q ∣ n + i := by
  simp +contextual [Nat.prime_iff, Prime.dvd_finsetProd_iff, prod_ne_zero_iff]
  omega

theorem OMA.solution : OMA.R_Erdos931_erdos_931_variants_exists_prime_R1.H1 := by
  intro _ _ _ n h e
  simp only [Finset.ext_iff, L] at *
  refine ⟨fun q p a b => ?_, fun q ⟨p, i, x, d⟩ => ?_⟩
  · have ⟨_, i, _, d⟩ := (e q).2 ⟨p, q - n, by omega, by simp [a.le]⟩
    linarith [Nat.le_of_dvd (by omega) d]
  · have ⟨_, j, _, f⟩ := (e q).1 ⟨p, i, x, d⟩
    have := Nat.le_of_dvd (by omega) (Nat.dvd_sub f d)
    omega
