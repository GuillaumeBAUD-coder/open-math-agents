import OMAReductions.R_Erdos945_erdos_945_R1

/-! # Divisor count of a squarefree integer

`τ n = ∏_{p ∣ n} (v_p(n) + 1)`, and every exponent of a squarefree `n` is `1`. -/

theorem OMA.solution : OMA.R_Erdos945_erdos_945_R1.H2 := by
  intro n hn
  have hn0 : n ≠ 0 := hn.ne_zero
  show n.divisors.card = 2 ^ n.primeFactors.card
  rw [Nat.card_divisors hn0]
  rw [Finset.prod_congr rfl (g := fun _ => 2), Finset.prod_const]
  intro p hp
  have hle := hn.natFactorization_le_one p
  have hpos : 0 < n.factorization p :=
    (Nat.mem_primeFactors.mp hp).1.factorization_pos_of_dvd hn0 (Nat.mem_primeFactors.mp hp).2.1
  omega
