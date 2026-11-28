import OMAStatements.S_oeis_a088987

open OMA.S_oeis_a088987

private theorem primeIndexStrictMono : StrictMono (Nat.nth Nat.Prime) :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

private theorem primesBetween (i j : ℕ) :
    {p : ℕ | p.Prime ∧ Nat.nth Nat.Prime i < p ∧ p < Nat.nth Nat.Prime j} =
      Nat.nth Nat.Prime '' Set.Ioo i j := by
  ext p
  constructor
  · rintro ⟨hp, hl, hh⟩
    obtain ⟨l, rfl⟩ :=
      Nat.subset_range_nth (show p ∈ Set.ofPred Nat.Prime from hp)
    exact ⟨l, ⟨primeIndexStrictMono.lt_iff_lt.mp hl, primeIndexStrictMono.lt_iff_lt.mp hh⟩, rfl⟩
  · rintro ⟨l, ⟨hl, hh⟩, rfl⟩
    exact ⟨Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime l,
      primeIndexStrictMono hl, primeIndexStrictMono hh⟩

private theorem primeIsPrime (k : ℕ) : (prime k).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (k - 1)

private theorem betweenEq (k : ℕ) : between k = prime (k + 1) - prime k - 1 := by
  have h₀ := (primeIsPrime k).two_le
  have h₁ := (primeIsPrime (k + 1)).two_le
  unfold between ppi
  change ({p : ℕ | p.Prime ∧ Nat.nth Nat.Prime (prime k - 1) < p ∧
    p < Nat.nth Nat.Prime (prime (k + 1) - 1)} : Set ℕ).ncard = _
  rw [primesBetween, Set.ncard_image_of_injective _ primeIndexStrictMono.injective,
    Set.ncard_Ioo_nat]
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a088987.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [ppi, prime, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  · norm_num [ppi, prime, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
  · rw [betweenEq]
    norm_num [prime, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  · intro k hk
    have h₀ : 2 < prime k := by
      rw [← Nat.nth_prime_zero_eq_two]
      exact primeIndexStrictMono (by omega : 0 < k - 1)
    have h₁ : prime k < prime (k + 1) :=
      primeIndexStrictMono (by omega : k - 1 < k + 1 - 1)
    have h₂ := (primeIsPrime k).mod_two_eq_one_iff_ne_two.mpr (by omega)
    have h₃ := (primeIsPrime (k + 1)).mod_two_eq_one_iff_ne_two.mpr (by omega)
    rw [betweenEq, Nat.odd_iff]
    omega
