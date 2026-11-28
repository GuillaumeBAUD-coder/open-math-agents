import OMAStatements.S_oeis_a176997
import Mathlib

/-!
# OEIS A176997: `2^(k-1) ≡ 1 (mod k)` holds exactly for `1`, the odd primes and the base-2 pseudoprimes

Let `k > 0` with `2^(k-1) ≡ 1 (mod k)`.

* `k = 1` qualifies trivially.
* If `k` is prime then `k ≠ 2` (since `2^1 = 2 ≢ 1 (mod 2)`), so `k` is an odd prime; conversely
  every odd prime qualifies by Fermat's little theorem.
* If `k > 1` is composite, the congruence says precisely that `k` is a Fermat pseudoprime to
  base `2`.

The second description is the same, because `{1} ∪ {odd primes}` is the set A006005.
-/

open OMA.S_oeis_a176997

namespace OMA.A176997

/-- The congruence and the divisibility used by `Nat.ProbablePrime` say the same thing. -/
lemma modEq_iff_dvd (k : ℕ) : 2 ^ (k - 1) ≡ 1 [MOD k] ↔ k ∣ 2 ^ (k - 1) - 1 := by
  have h1 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  constructor
  · intro h
    exact (Nat.modEq_iff_dvd' h1).mp h.symm
  · intro h
    exact ((Nat.modEq_iff_dvd' h1).mpr h).symm

/-- The characterisation of membership. -/
lemma key (k : ℕ) :
    k ∈ A176997 ↔ k = 1 ∨ (k.Prime ∧ Odd k) ∨ Nat.FermatPsp k 2 := by
  constructor
  · rintro ⟨hk, h⟩
    by_cases h1 : k = 1
    · exact Or.inl h1
    by_cases hp : k.Prime
    · -- a prime in the set is odd
      refine Or.inr (Or.inl ⟨hp, hp.odd_of_ne_two ?_⟩)
      rintro rfl
      exact absurd h (by decide)
    · exact Or.inr (Or.inr ⟨(modEq_iff_dvd k).mp h, hp, by omega⟩)
  · rintro (rfl | ⟨hp, hodd⟩ | ⟨hprob, -, h1⟩)
    · exact ⟨by norm_num, Nat.modEq_one⟩
    · -- Fermat's little theorem
      refine ⟨hp.pos, ?_⟩
      have hne : 2 ≠ k := by
        rintro rfl
        exact absurd hodd (by decide)
      have hcop : Nat.Coprime 2 k := (Nat.coprime_primes Nat.prime_two hp).mpr hne
      have := Nat.ModEq.pow_totient hcop
      rwa [Nat.totient_prime hp] at this
    · exact ⟨by omega, (modEq_iff_dvd k).mpr hprob⟩

end OMA.A176997

open OMA.A176997 in
theorem OMA.solution : type_of% @OMA.S_oeis_a176997.main := by
  constructor
  · ext k
    rw [key]
    simp only [Set.mem_union, Set.mem_singleton_iff, A065091, A001567, Set.mem_ofPred_eq]
    tauto
  · ext k
    rw [key]
    simp only [Set.mem_union, A006005, A001567, Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | ⟨hp, hodd⟩ | h)
      · exact Or.inl ⟨by decide, Or.inl rfl⟩
      · exact Or.inl ⟨hodd, Or.inr hp⟩
      · exact Or.inr h
    · rintro (⟨hodd, rfl | hp⟩ | h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨hp, hodd⟩)
      · exact Or.inr (Or.inr h)
