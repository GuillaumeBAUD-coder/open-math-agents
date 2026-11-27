import FormalConjectures.ErdosProblems.«470»

/-!
# Reduction of Erdős 470, variant odd_weird_prime_div (Liddy–Riedl 2018)

Reduction `Erdos470.erdos_470.variants.odd_weird_prime_div.R1`.
`main` proves that a positive multiple of a pseudoperfect number is pseudoperfect, identifies the
set of prime divisors with `Nat.primeFactors` and, by strong induction, reduces the target to odd
primitive abundant numbers (abundant, every proper divisor deficient). By Dickson's theorem there
are finitely many of these with a given number of distinct primes; the split is by that number:
- `H1` (finite, small): the odd primitive abundant numbers with at most 4 distinct primes
  (exactly 8 with three primes and 576 with four, all below 10^18) are pseudoperfect.
- `H2` (finite, large): the odd primitive abundant numbers with exactly 5 distinct primes are
  pseudoperfect.
-/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1

-- Odd primitive abundant numbers with at most four distinct primes are pseudoperfect.
def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    n.primeFactors.card ≤ 4 → n.Pseudoperfect

-- Odd primitive abundant numbers with exactly five distinct primes are pseudoperfect.
def H2 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    n.primeFactors.card = 5 → n.Pseudoperfect

/-- A positive multiple of a pseudoperfect number is pseudoperfect. -/
lemma pp_of_dvd {d n : ℕ} (hdn : d ∣ n) (hn : 0 < n) (hd : d.Pseudoperfect) :
    n.Pseudoperfect := by
  obtain ⟨k, rfl⟩ := hdn
  obtain ⟨_, s, hs, hsum⟩ := hd
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  refine ⟨hn, s.image (fun i => i * k), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' := hs hi
    rw [Nat.mem_properDivisors] at hi' ⊢
    exact ⟨Nat.mul_dvd_mul_right hi'.1 k, Nat.mul_lt_mul_of_pos_right hi'.2 hk⟩
  · rw [Finset.sum_image]
    · rw [← Finset.sum_mul, hsum]
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_right hk hab

/-- The set in the target is the finset of prime factors. -/
lemma ncard_eq (n : ℕ) :
    {m | m ∈ n.divisors ∧ m.Prime}.ncard = n.primeFactors.card := by
  have h : {m | m ∈ n.divisors ∧ m.Prime} = ↑n.primeFactors := by
    ext m
    simp only [Set.mem_setOf_eq, Nat.mem_divisors, Finset.mem_coe, Nat.mem_primeFactors]
    tauto
  rw [h, Set.ncard_coe_finset]

/-- Reduction to the primitive abundant case. -/
lemma all_pp (h1 : H1) (h2 : H2) :
    ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card ≤ 5 → n.Pseudoperfect := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hodd hab h5
    by_cases hprim : ∀ d ∈ n.properDivisors, d.Deficient
    · by_cases h4 : n.primeFactors.card ≤ 4
      · exact h1 n hodd hab hprim h4
      · exact h2 n hodd hab hprim (by omega)
    · simp only [not_forall] at hprim
      obtain ⟨d, hd, hdef⟩ := hprim
      rw [Nat.mem_properDivisors] at hd
      have hnpos : 0 < n := hab.pos
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hnpos
      have hdodd : Odd d := hodd.of_dvd_nat hd.1
      have hd5 : d.primeFactors.card ≤ 5 :=
        le_trans (Finset.card_le_card (Nat.primeFactors_mono hd.1 (by omega))) h5
      rcases Nat.deficient_or_perfect_or_abundant (n := d) (by omega) with h | h | h
      · exact absurd h hdef
      · exact pp_of_dvd hd.1 hnpos (ih d hd.2 hdodd h hd5)
      · exact pp_of_dvd hd.1 hnpos h.pseudoperfect

theorem main : H1 → H2 → type_of% @Erdos470.erdos_470.variants.odd_weird_prime_div := by
  intro h1 h2 n hodd hw
  rw [ncard_eq n]
  by_contra hlt
  exact hw.2 (all_pp h1 h2 n hodd hw.1 (by omega))

end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1
