import OMAReductions.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1

/-! Local divisibility conditions and a reciprocal bound give the cofactor identity. -/

open Finset

theorem OMA.solution :
    OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1.H1 := by
  intro P _ hprime hlocal hrecip
  let cofactor (p : ℕ) := ∏ q ∈ P.erase p, q
  let product := ∏ p ∈ P, p
  let total := ∑ p ∈ P, cofactor p
  change product = 1 + total
  have hpos : 0 < product := prod_pos fun p hp => (hprime p hp).pos
  have hdiv (p : ℕ) (hp : p ∈ P) : p ∣ 1 + total := by
    have hrest : p ∣ ∑ q ∈ P.erase p, cofactor q := by
      apply dvd_sum
      intro q hq
      exact dvd_prod_of_mem id (mem_erase.mpr ⟨(mem_erase.mp hq).1.symm, hp⟩)
    rw [show total = cofactor p + ∑ q ∈ P.erase p, cofactor q from
      (add_sum_erase P cofactor hp).symm, ← add_assoc, add_comm 1]
    exact dvd_add (hlocal p hp) hrest
  have hsubset : P ⊆ (1 + total).primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hp, hdiv p hp, by omega⟩
  have hproductDvd : product ∣ 1 + total :=
    (prod_dvd_prod_of_subset _ _ id hsubset).trans (Nat.prod_primeFactors_dvd _)
  have hscaled : (∑ p ∈ P, (1 : ℚ) / p) * (product : ℚ) = (total : ℚ) := by
    rw [sum_mul]
    simp only [total, Nat.cast_sum]
    apply sum_congr rfl
    intro p hp
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
    have hfactor : product = cofactor p * p := (prod_erase_mul P id hp).symm
    rw [hfactor, Nat.cast_mul]
    field_simp
  have hlt : total < product := by
    have hposQ : 0 < (product : ℚ) := by exact_mod_cast hpos
    have hltQ := mul_lt_mul_of_pos_right hrecip hposQ
    rw [hscaled, one_mul] at hltQ
    exact_mod_cast hltQ
  exact le_antisymm (Nat.le_of_dvd (by omega) hproductDvd) (by omega)
