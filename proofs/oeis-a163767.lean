import OMAStatements.S_oeis_a163767

open Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a163767.main := by
  intro s hs
  set N := ∏ p ∈ s, p with hNdef
  have hN : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hs p hp).ne_zero
  have hsq : Squarefree N := by
    have := Finset.squarefree_prod_of_pairwise_isCoprime (s := s) (f := id)
      (fun p hp q hq hpq =>
        Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes (hs p hp) (hs q hq)).2 hpq))
      (fun p hp => (hs p hp).prime.squarefree)
    simpa using this
  have hω : ArithmeticFunction.cardDistinctFactors N = s.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
      Nat.toFinset_factors, hNdef, Nat.primeFactors_prod hs]
  show Nat.card {f : Fin N → ℕ // ∏ i, f i = N} = N ^ s.card
  rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun f => f ∈ Nat.finMulAntidiag N N)
      (fun f => by simp [Nat.mem_finMulAntidiag, hN])),
    Nat.card_eq_finsetCard, Nat.card_finMulAntidiag_of_squarefree hsq, hω]
