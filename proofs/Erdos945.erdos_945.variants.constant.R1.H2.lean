import OMAReductions.R_Erdos945_erdos_945_variants_constant_R1
import Mathlib

/-! A squarefree `n` has every prime exponent equal to `1`, so `Nat.card_divisors` gives
`τ n = ∏ (1 + 1) = 2 ^ ω(n)`. -/

theorem OMA.solution : OMA.R_Erdos945_erdos_945_variants_constant_R1.H2 := by
  intro n hn
  have hn0 : n ≠ 0 := hn.ne_zero
  show n.divisors.card = _
  rw [Nat.card_divisors hn0, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h1 : n.factorization p = 1 := by
    have hle := (Nat.squarefree_iff_factorization_le_one hn0).mp hn p
    have hpos := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn0
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  rw [h1]
