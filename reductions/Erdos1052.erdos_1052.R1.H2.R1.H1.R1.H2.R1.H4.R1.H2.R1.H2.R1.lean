import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1

/-!
# The exponent sieve and simple prime divisors above 11

The first step excludes eight prime divisors of half the exponent of 11.
The remaining step concerns only the number of large simple prime factors
in that sifted family. Subbarao and Warren's finiteness theorem for unitary
perfect numbers with a fixed number of prime factors then bounds the
2-adic valuation uniformly.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1_H2_R1

/-- Every odd prime below 29 is excluded from half the exponent of 11. -/
def H1 : Prop :=
  ∀ {n : ℕ}, Erdos1052.IsUnitaryPerfect n →
    (∀ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p = 11) →
    n.factorization 11 % 4 = 2 → ¬13 ∣ n →
    ∀ k ∈ ([3,5,7,11,13,17,19,23] : List ℕ), ¬ k ∣ n.factorization 11 / 2

/-- Uniformly bound the number of simple prime divisors above 11 that can
occur together after the exponent sieve in the given branch. -/
def H2 : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p = 11) →
    6 ≤ n.factorization 11 → n.factorization 11 % 4 = 2 →
    padicValNat 2 n % 4 = 2 → padicValNat 2 n % 20 ≠ 10 →
    padicValNat 2 n % 28 ≠ 14 → 7 ∣ n → ¬13 ∣ n →
    (∀ k ∈ ([3,5,7,11,13,17,19,23] : List ℕ), ¬ k ∣ n.factorization 11 / 2) →
    (n.primeFactors.filter fun p => 11 < p ∧ n.factorization p = 1).card ≤ B

theorem main : H1 → H2 →
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1.H2 := by
  rintro sieve ⟨B, bound⟩
  let U := ⋃ k ∈ Set.Iic (B + 5), {n : ℕ | Erdos1052.IsUnitaryPerfect n ∧ n.primeFactors.card = k}
  have finite : U.Finite := (Set.finite_Iic (B + 5)).biUnion
    fun k _ => OMA.R_Erdos1052_erdos_1052_R1.finite_card_primeFactors k
  obtain ⟨A, upper⟩ := (finite.image (padicValNat 2)).bddAbove
  refine ⟨A, fun n hn unique h6 he h4 h20 h28 h7 h13 => ?_⟩
  apply upper
  apply Set.mem_image_of_mem
  have large := bound n hn unique h6 he h4 h20 h28 h7 h13 (sieve hn unique he h13)
  let small := (Finset.range 12).filter Nat.Prime
  have split : n.primeFactors ⊆ small ∪
      (n.primeFactors.filter fun p => 11 < p ∧ n.factorization p = 1) := by
    intro p hp
    have prime := Nat.prime_of_mem_primeFactors hp
    by_cases h : 11 < p
    · apply Finset.mem_union_right
      refine Finset.mem_filter.mpr ⟨hp, h, ?_⟩
      have positive := prime.factorization_pos_of_dvd hn.2.ne' (Nat.dvd_of_mem_primeFactors hp)
      have simple : ¬p^2 ∣ n := fun d => (by omega : p ≠ 11) ((unique p).mp ⟨prime, by omega, d⟩)
      have := prime.pow_dvd_iff_le_factorization hn.2.ne' (k := 2)
      omega
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), prime⟩)
  have small_count : small.card = 5 := by decide
  have total := (Finset.card_le_card split).trans (Finset.card_union_le ..)
  exact Set.mem_iUnion.mpr ⟨n.primeFactors.card,
    Set.mem_iUnion.mpr ⟨(by change n.primeFactors.card ≤ B + 5; omega), hn, rfl⟩⟩

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1_H2_R1
