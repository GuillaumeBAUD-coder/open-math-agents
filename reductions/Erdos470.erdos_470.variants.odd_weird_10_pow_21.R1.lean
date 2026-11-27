import FormalConjectures.ErdosProblems.«470»

/-!
# Reduction of Erdős 470, variant odd_weird_10_pow_21 (Fang 2022)

Reduction `Erdos470.erdos_470.variants.odd_weird_10_pow_21.R1`.
`main` proves that a positive multiple of a pseudoperfect number is pseudoperfect and, by strong
induction, reduces the target to odd primitive abundant numbers (abundant, every proper divisor
deficient). The remaining search is split by divisibility by 3:
- `H1` (known, Fang 2022): odd primitive abundant multiples of 3 below 10^21 are pseudoperfect.
- `H2` (known, Fang 2022): odd primitive abundant non-multiples of 3 below 10^21 are pseudoperfect
  (such numbers have at least 7 prime factors, all at least 5; a much smaller search).
-/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1

-- Fang 2022, multiples of 3: every odd primitive abundant multiple of 3 below 10^21 is pseudoperfect.
def H1 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) → 3 ∣ n →
    n.Pseudoperfect

-- Fang 2022, non-multiples of 3: every odd primitive abundant number below 10^21 that is
-- coprime to 3 is pseudoperfect.
def H2 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) → ¬ 3 ∣ n →
    n.Pseudoperfect

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

/-- Reduction to the primitive abundant case. -/
lemma all_pp (h1 : H1) (h2 : H2) :
    ∀ n : ℕ, n < 10 ^ 21 → Odd n → n.Abundant → n.Pseudoperfect := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hodd hab
    by_cases hprim : ∀ d ∈ n.properDivisors, d.Deficient
    · by_cases h3 : 3 ∣ n
      · exact h1 n hn hodd hab hprim h3
      · exact h2 n hn hodd hab hprim h3
    · simp only [not_forall] at hprim
      obtain ⟨d, hd, hdef⟩ := hprim
      rw [Nat.mem_properDivisors] at hd
      have hnpos : 0 < n := hab.pos
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hnpos
      have hdodd : Odd d := hodd.of_dvd_nat hd.1
      rcases Nat.deficient_or_perfect_or_abundant (n := d) (by omega) with h | h | h
      · exact absurd h hdef
      · exact pp_of_dvd hd.1 hnpos (ih d hd.2 (by omega) hdodd h)
      · exact pp_of_dvd hd.1 hnpos h.pseudoperfect

theorem main : H1 → H2 → type_of% @Erdos470.erdos_470.variants.odd_weird_10_pow_21 := by
  intro h1 h2 n hn hodd hw
  exact hw.2 (all_pp h1 h2 n hn hodd hw.1)

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1
