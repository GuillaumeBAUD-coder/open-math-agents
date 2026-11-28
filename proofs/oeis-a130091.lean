import OMAStatements.S_oeis_a130091
import Mathlib

/-
A130091: numbers whose prime exponents are pairwise distinct. No number 36n - 6 (n >= 1) or
36n + 6 is a term, and there are no 24 consecutive terms.

36n - 6 = 6 (6n - 1) and 36n + 6 = 6 (6n + 1), where the cofactor is coprime to 6, so the primes
2 and 3 both occur with exponent exactly 1. Among any 24 consecutive positive integers one is
6 or 30 modulo 36, that is, of one of these two forms.
-/

namespace OMA.P130091

lemma val1 (p t : ℕ) (hp : p.Prime) (ht : ¬ p ∣ t) (ht0 : t ≠ 0) :
    (p * t).factorization p = 1 := by
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, padicValNat.mul hp.ne_zero ht0, padicValNat_self,
    padicValNat.eq_zero_of_not_dvd ht]

lemma notIn (t : ℕ) (h2 : ¬ 2 ∣ t) (h3 : ¬ 3 ∣ t) :
    ¬ (0 < 6 * t ∧ Set.InjOn (6 * t).factorization ((6 * t).primeFactors : Set ℕ)) := by
  rintro ⟨-, hinj⟩
  have e2 : (6 * t).factorization 2 = 1 := by
    rw [show 6 * t = 2 * (3 * t) by ring]
    exact val1 2 (3 * t) Nat.prime_two (by omega) (by omega)
  have e3 : (6 * t).factorization 3 = 1 := by
    rw [show 6 * t = 3 * (2 * t) by ring]
    exact val1 3 (2 * t) Nat.prime_three (by omega) (by omega)
  have m2 : 2 ∈ ((6 * t).primeFactors : Set ℕ) := by
    simp only [Finset.mem_coe, Nat.mem_primeFactors]
    exact ⟨Nat.prime_two, ⟨3 * t, by ring⟩, by omega⟩
  have m3 : 3 ∈ ((6 * t).primeFactors : Set ℕ) := by
    simp only [Finset.mem_coe, Nat.mem_primeFactors]
    exact ⟨Nat.prime_three, ⟨2 * t, by ring⟩, by omega⟩
  have := hinj m2 m3 (e2.trans e3.symm)
  omega

lemma main' :
    (∀ n : ℕ, 1 ≤ n → ¬ (0 < 36 * n - 6 ∧
      Set.InjOn (36 * n - 6).factorization ((36 * n - 6).primeFactors : Set ℕ))) ∧
    (∀ n : ℕ, ¬ (0 < 36 * n + 6 ∧
      Set.InjOn (36 * n + 6).factorization ((36 * n + 6).primeFactors : Set ℕ))) ∧
    (¬ ∃ m : ℕ, ∀ i : ℕ, i < 24 → (0 < m + i ∧
      Set.InjOn (m + i).factorization ((m + i).primeFactors : Set ℕ))) := by
  have A : ∀ n : ℕ, 1 ≤ n → ¬ (0 < 36 * n - 6 ∧
      Set.InjOn (36 * n - 6).factorization ((36 * n - 6).primeFactors : Set ℕ)) := by
    intro n hn
    rw [show 36 * n - 6 = 6 * (6 * n - 1) by omega]
    exact notIn (6 * n - 1) (by omega) (by omega)
  have B : ∀ n : ℕ, ¬ (0 < 36 * n + 6 ∧
      Set.InjOn (36 * n + 6).factorization ((36 * n + 6).primeFactors : Set ℕ)) := by
    intro n
    rw [show 36 * n + 6 = 6 * (6 * n + 1) by ring]
    exact notIn (6 * n + 1) (by omega) (by omega)
  refine ⟨A, B, ?_⟩
  rintro ⟨m, hm⟩
  have key : ∃ i < 24, (∃ q, m + i = 36 * q + 6) ∨ (∃ q, 1 ≤ q ∧ m + i = 36 * q - 6) := by
    rcases Nat.lt_or_ge (m % 36) 7 with h | h
    · exact ⟨6 - m % 36, by omega, Or.inl ⟨m / 36, by omega⟩⟩
    · rcases Nat.lt_or_ge (m % 36) 31 with h' | h'
      · exact ⟨30 - m % 36, by omega, Or.inr ⟨m / 36 + 1, by omega, by omega⟩⟩
      · exact ⟨42 - m % 36, by omega, Or.inl ⟨m / 36 + 1, by omega⟩⟩
  obtain ⟨i, hi, ⟨q, hq⟩ | ⟨q, hq1, hq⟩⟩ := key
  · exact B q (hq ▸ hm i hi)
  · exact A q hq1 (hq ▸ hm i hi)

end OMA.P130091

theorem OMA.solution : type_of% @OMA.S_oeis_a130091.main := OMA.P130091.main'
