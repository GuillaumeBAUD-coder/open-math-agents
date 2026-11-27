import OMAStatements.S_oeis_a372313
import Mathlib

namespace A372313Proof

lemma val_two (s : ℕ) (h : s % 4 = 2) : s.factorization 2 = 1 := by
  rw [Nat.factorization_def s Nat.prime_two]
  obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
  have ht : ¬ 2 ∣ t := by omega
  have ht0 : t ≠ 0 := by omega
  rw [padicValNat.mul (by norm_num) ht0, padicValNat_self, padicValNat.eq_zero_of_not_dvd ht]

lemma f_val (s : ℕ) (h : s % 100 = 66) : OMA.S_oeis_a372313.transform s % 100 = 33 := by
  have hv := val_two s (by omega)
  show (s * 2 ^ (s.factorization 2) + (4 ^ (s.factorization 2) - 1) / 3) % 100 = 33
  rw [hv]
  have e : (4 ^ 1 - 1) / 3 = 1 := by norm_num
  rw [e, pow_one]
  omega

end A372313Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a372313.main := by
  intro n hn h1 k hk
  have h1' : (2 * n - 1) % 100 = 33 := h1
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  clear hk
  induction j with
  | zero => exact h1
  | succ j ih =>
    show OMA.S_oeis_a372313.transform (OMA.S_oeis_a372313.entry n (j + 1) + (2 * n - 1)) % 100 = 33
    exact A372313Proof.f_val _ (by omega)
