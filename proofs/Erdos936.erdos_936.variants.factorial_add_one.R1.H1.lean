import OMAReductions.R_Erdos936_erdos_936_variants_factorial_add_one_R1
import Mathlib

-- Step Erdos936.erdos_936.variants.factorial_add_one.R1.H1: hypothesis H1 of reduction Erdos936.erdos_936.variants.factorial_add_one.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! (rad c)^2 is the product of the squares p^2 over the prime factors of c. These are pairwise
coprime and each divides the powerful number c, so their product divides c. -/

open Finset Filter Nat

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1.H1 := by
  intro c hc hpow
  rw [← Finset.prod_pow]
  have key : ∀ s : Finset ℕ, s ⊆ c.primeFactors → (∏ p ∈ s, p ^ 2) ∣ c := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | @insert a s ha ih =>
      intro hs
      rw [Finset.prod_insert ha]
      have has : a ∈ c.primeFactors := hs (Finset.mem_insert_self a s)
      have hsub : s ⊆ c.primeFactors := fun x hx => hs (Finset.mem_insert_of_mem hx)
      have hap : a.Prime := Nat.prime_of_mem_primeFactors has
      have hcop : Nat.Coprime (a ^ 2) (∏ p ∈ s, p ^ 2) := by
        apply Nat.Coprime.prod_right
        intro p hp
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors (hsub hp)
        have hne : a ≠ p := fun h => ha (h ▸ hp)
        exact ((Nat.coprime_primes hap hpp).mpr hne).pow 2 2
      exact hcop.mul_dvd_of_dvd_of_dvd (hpow a has) (ih hsub)
  exact key _ (subset_refl _)

