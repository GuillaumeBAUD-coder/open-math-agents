import FormalConjectures.ErdosProblems.«939»

/-!
The exponent-five example of Cambie handles the middle case. The
[discussion of Erdős Problem 939](https://www.erdosproblems.com/forum/thread/939)
gives a binomial construction for the range starting at six. The remaining
Diophantine question is the existence of a primitive triple at exponent four.
-/

namespace OMA.R_Erdos939_erdos_939_R1

/-- A positive primitive solution of the exponent-four equation. -/
def H1 : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧
    (4 : ℕ).Full a ∧ (4 : ℕ).Full b ∧ (4 : ℕ).Full (a + b)

/-- The large-exponent range addressed by the binomial construction. -/
def H2 : Prop :=
  ∀ r ≥ 6, (Erdos939.Erdos939Sums r).Nonempty

lemma four_iff_primitive_triple : (Erdos939.Erdos939Sums 4).Nonempty ↔ H1 := by
  constructor
  · rintro ⟨s, hcard, hcop, hsum, hterms⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have ha : a ∈ ({a, b} : Finset ℕ) := Finset.mem_insert_self _ _
    have hb : b ∈ ({a, b} : Finset ℕ) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hab' : a ∉ ({b} : Finset ℕ) := by simpa only [Finset.mem_singleton] using hab
    rw [Finset.sum_insert hab', Finset.sum_singleton] at hsum
    exact ⟨a, b, (hterms a ha).1, (hterms b hb).1, (Finset.Coprime_pair_iff _ _ _ rfl).mp hcop,
      (hterms a ha).2, (hterms b hb).2, hsum⟩
  · rintro ⟨a, b, ha, hb, hcop, hfa, hfb, hsum⟩
    have hab : a ≠ b := by
      intro heq
      subst b
      have hgcd : Nat.gcd a a = 1 := hcop
      rw [Nat.gcd_self] at hgcd
      subst a
      have htwo : 2 ∈ (2 : ℕ).primeFactors := Nat.mem_primeFactors.mpr
        ⟨Nat.prime_two, dvd_rfl, by decide⟩
      have hdvd : (2 : ℕ)^4 ∣ 2 := hsum 2 htwo
      norm_num at hdvd
    have hab' : a ∉ ({b} : Finset ℕ) := by simpa only [Finset.mem_singleton] using hab
    refine ⟨{a, b}, ?_, (Finset.Coprime_pair_iff _ _ _ rfl).mpr hcop, ?_, ?_⟩
    · simp only [Finset.card_insert_of_notMem hab', Finset.card_singleton]
    · simpa only [Finset.sum_insert hab', Finset.sum_singleton] using hsum
    · intro n hn
      rcases Finset.mem_insert.mp hn with rfl | h
      · exact ⟨ha, hfa⟩
      · rw [Finset.mem_singleton.mp h]
        exact ⟨hb, hfb⟩

/-- Cambie's example, also recorded in the upstream proof of the existential variant. -/
lemma five_nonempty : (Erdos939.Erdos939Sums 5).Nonempty := by
  unfold Erdos939.Erdos939Sums
  simp [Set.Nonempty]
  use {2^8 * 3^10 * 5^7, 2^12 * 23^6, 11^5 * 13^5}
  simp
  constructor
  · unfold Finset.Coprime
    aesop
  · norm_num [Nat.Full, Nat.primeFactors, Nat.primeFactorsList]

theorem main : H1 → H2 → type_of% @Erdos939.erdos_939 := by
  intro hfour htail r hr
  by_cases hlarge : 6 ≤ r
  · exact htail r hlarge
  · have small : r = 4 ∨ r = 5 := by omega
    rcases small with rfl | rfl
    · exact four_iff_primitive_triple.mpr hfour
    · exact five_nonempty

end OMA.R_Erdos939_erdos_939_R1
