import OMAStatements.S_oeis_a165719
import Mathlib

/-!
# OEIS A165719: integers of the form `k (k + 9) / 8`

* `k` and `k + 9` have opposite parity, so `8 ∣ k (k + 9)` exactly when `8 ∣ k` or `8 ∣ k + 9`,
  that is `k = 8m` or `k = 8m - 1`.
* If `k = 8m` the term is `m (8m + 9)`, which is prime only for `m = 1` (value `17`).
  If `k = 8m - 1` the term is `(8m - 1)(m + 1)`, a product of two factors `≥ 2`, never prime.
-/

open OMA.S_oeis_a165719

namespace OMA.A165719

/-- `8 ∣ k (k + 9)` forces `k ≡ 0` or `7 (mod 8)`. -/
lemma mod_eight {k : ℕ} (h : 8 ∣ k * (k + 9)) : k % 8 = 0 ∨ k % 8 = 7 := by
  have h8 : (k * (k + 9)) % 8 = 0 := Nat.mod_eq_zero_of_dvd h
  rw [Nat.mul_mod, Nat.add_mod] at h8
  have hk : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : k % 8 <;> simp_all

/-- The valid `k` are `8m - 1` and `8m`. -/
lemma valid_k (k : ℕ) (hk : 1 ≤ k) :
    (8 ∣ k * (k + 9)) ↔ ∃ m : ℕ, 1 ≤ m ∧ (k = 8 * m - 1 ∨ k = 8 * m) := by
  constructor
  · intro h
    rcases mod_eight h with h0 | h7
    · exact ⟨k / 8, by omega, Or.inr (by omega)⟩
    · exact ⟨k / 8 + 1, by omega, Or.inl (by omega)⟩
  · rintro ⟨m, hm, rfl | rfl⟩
    · -- `k + 9 = 8 (m + 1)`
      have : 8 * m - 1 + 9 = 8 * (m + 1) := by omega
      rw [this]
      exact ⟨(8 * m - 1) * (m + 1), by ring⟩
    · exact ⟨m * (8 * m + 9), by ring⟩

/-- The only prime term is `17`. -/
lemma prime_term (v : ℕ) : (IsTerm v ∧ v.Prime) ↔ v = 17 := by
  constructor
  · rintro ⟨⟨k, hk, hkv⟩, hv⟩
    obtain ⟨m, hm, rfl | rfl⟩ := (valid_k k hk).mp ⟨v, hkv⟩
    · -- `v = (8m - 1)(m + 1)`: both factors are at least `2`
      exfalso
      have h9 : 8 * m - 1 + 9 = 8 * (m + 1) := by omega
      rw [h9] at hkv
      have hv' : v = (8 * m - 1) * (m + 1) := by
        have : 8 * ((8 * m - 1) * (m + 1)) = 8 * v := by rw [← hkv]; ring
        omega
      have hnp : ¬ ((8 * m - 1) * (m + 1)).Prime :=
        Nat.not_prime_mul (by omega) (by omega)
      exact hnp (hv' ▸ hv)
    · -- `v = m (8m + 9)`: prime only when `m = 1`
      have hv' : v = m * (8 * m + 9) := by
        have : 8 * (m * (8 * m + 9)) = 8 * v := by rw [← hkv]; ring
        omega
      rcases Nat.eq_or_lt_of_le hm with h1 | h1
      · subst h1; omega
      · exfalso
        have hnp : ¬ (m * (8 * m + 9)).Prime :=
          Nat.not_prime_mul (by omega) (by omega)
        exact hnp (hv' ▸ hv)
  · rintro rfl
    exact ⟨⟨8, by norm_num, by norm_num⟩, by norm_num⟩

end OMA.A165719

open OMA.A165719 in
theorem OMA.solution : type_of% @OMA.S_oeis_a165719.main :=
  ⟨valid_k, prime_term⟩
