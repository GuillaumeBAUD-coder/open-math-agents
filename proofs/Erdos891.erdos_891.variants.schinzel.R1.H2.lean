import OMAReductions.R_Erdos891_erdos_891_variants_schinzel_R1

/-! Split each prime exponent into its quotient and remainder modulo three.
The remainder product is bounded uniformly in terms of the allowed primes. -/

open Finset

theorem OMA.solution : OMA.R_Erdos891_erdos_891_variants_schinzel_R1.H2 := by
  classical
  intro S
  refine ⟨Iic (∏ p ∈ S, (max 1 p)^2), ?_⟩
  intro m hm hs
  let e := m.factorization
  refine ⟨∏ p ∈ S, p ^ (e p % 3), mem_Iic.mpr ?_, ∏ p ∈ S, p ^ (e p / 3), ?_⟩
  · apply Finset.prod_le_prod'
    intro p _
    calc
      p ^ (e p % 3) ≤ (max 1 p) ^ (e p % 3) := Nat.pow_le_pow_left (le_max_right _ _) _
      _ ≤ (max 1 p) ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
  · have hprod : m = ∏ p ∈ S, p^(e p) := by
      calc
        m = m.factorization.prod (· ^ ·) := (Nat.prod_factorization_pow_eq_self hm.ne').symm
        _ = _ := Finsupp.prod_of_support_subset _ (by simpa [Nat.support_factorization] using hs)
          _ (fun _ _ => pow_zero _)
    rw [hprod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
