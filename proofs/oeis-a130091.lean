import OMAStatements.S_oeis_a130091
import Mathlib

/-!
# A130091: numbers whose prime exponents are pairwise distinct

A number `k` with `k ≡ 2 (mod 4)` and `k ≡ 3` or `6 (mod 9)` is divisible by `2` and by `3`
exactly once each, so the exponents of `2` and `3` coincide and `k` is not in the sequence.
This covers `36 n - 6` and `36 n + 6`, i.e. the residues `30` and `6` modulo `36`; these two
residues are `24` and `12` apart, so every block of `24` consecutive integers meets one of them.
-/

namespace OMA.S_oeis_a130091

/-- If `p ∣ k` but `p ^ 2 ∤ k` then the exponent of the prime `p` in `k` is exactly one. -/
lemma factorization_eq_one {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (h1 : p ∣ k)
    (h2 : ¬ p ^ 2 ∣ k) : k.factorization p = 1 := by
  have a1 : 1 ≤ k.factorization p :=
    (hp.pow_dvd_iff_le_factorization hk).mp (by simpa using h1)
  have a2 : ¬ 2 ≤ k.factorization p := fun h =>
    h2 ((hp.pow_dvd_iff_le_factorization hk).mpr h)
  omega

/-- Numbers that are `2 mod 4` and `3` or `6 mod 9` have equal exponents at `2` and `3`. -/
lemma not_inSeq {k : ℕ} (h4 : k % 4 = 2) (h9 : k % 9 = 3 ∨ k % 9 = 6) : ¬ InSeq k := by
  rintro ⟨hpos, hinj⟩
  have hk : k ≠ 0 := by omega
  have d2 : 2 ∣ k := by omega
  have d3 : 3 ∣ k := by omega
  have e2 : k.factorization 2 = 1 :=
    factorization_eq_one Nat.prime_two hk d2 (by norm_num; omega)
  have e3 : k.factorization 3 = 1 :=
    factorization_eq_one Nat.prime_three hk d3 (by norm_num; omega)
  have m2 : (2 : ℕ) ∈ (k.primeFactors : Set ℕ) := by
    simpa using Nat.mem_primeFactors.mpr ⟨Nat.prime_two, d2, hk⟩
  have m3 : (3 : ℕ) ∈ (k.primeFactors : Set ℕ) := by
    simpa using Nat.mem_primeFactors.mpr ⟨Nat.prime_three, d3, hk⟩
  have := hinj m2 m3 (e2.trans e3.symm)
  omega

/-- Every window of `24` consecutive residues modulo `36` contains `6` or `30`. -/
lemma window : ∀ r < 36, ∃ i < 24, (r + i) % 36 = 6 ∨ (r + i) % 36 = 30 := by decide

end OMA.S_oeis_a130091

open OMA.S_oeis_a130091 in
theorem OMA.solution : type_of% @OMA.S_oeis_a130091.main := by
  refine ⟨fun n hn => not_inSeq (by omega) (by omega),
    fun n => not_inSeq (by omega) (by omega), ?_⟩
  rintro ⟨m, hm⟩
  obtain ⟨i, hi, h⟩ := window (m % 36) (Nat.mod_lt _ (by norm_num))
  exact not_inSeq (k := m + i) (by omega) (by omega) (hm i hi)
