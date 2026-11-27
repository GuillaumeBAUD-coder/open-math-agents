import OMAReductions.R_Erdos945_erdos_945_variants_constant_R1

-- Step Erdos945.erdos_945.variants.constant.R1.H2: hypothesis H2 of reduction
-- Erdos945.erdos_945.variants.constant.R1
-- Credit: @JamesSlash. Nat.card_divisors gives the product of (exponent + 1) over the prime
-- factors; every exponent of a squarefree number is 1.

theorem OMA.solution : OMA.R_Erdos945_erdos_945_variants_constant_R1.H2 := by
  intro n hn
  have h0 : n ≠ 0 := hn.ne_zero
  show n.divisors.card = _
  rw [Nat.card_divisors h0, Finset.prod_congr rfl (g := fun _ => 2), Finset.prod_const]
  intro p hp
  have h1 : n.factorization p ≤ 1 := hn.natFactorization_le_one p
  have h2 : 0 < n.factorization p :=
    (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd h0 (Nat.dvd_of_mem_primeFactors hp)
  omega
