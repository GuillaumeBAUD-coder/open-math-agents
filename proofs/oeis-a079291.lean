import OMAStatements.S_oeis_a079291
import Mathlib

namespace OMA.A079291Proof

open OMA.S_oeis_a079291

theorem step (n : ℕ) : A (n + 1) = A n + 2 * P n ∧ P (n + 1) = A n + P n := by
  induction n with
  | zero => simp [A, P]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · show 2 * A (n + 1) + A n = A (n + 1) + 2 * P (n + 1)
      rw [h2]; omega
    · show 2 * P (n + 1) + P n = A (n + 1) + P (n + 1)
      rw [h1, h2]; ring

theorem pell (n : ℕ) : (A n : ℤ) ^ 2 = 2 * (P n : ℤ) ^ 2 + (-1) ^ n := by
  induction n with
  | zero => simp [A, P]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := step n
    rw [h1, h2]; push_cast
    rw [pow_succ]
    linear_combination (-1 : ℤ) * ih

end OMA.A079291Proof

open OMA.A079291Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a079291.main := by
  intro n _
  have h := pell n
  refine ⟨fun he => ⟨n, ?_⟩, fun ho => ⟨n, ?_⟩⟩
  · rw [he.neg_one_pow] at h
    have : (OMA.S_oeis_a079291.A n) ^ 2 = 2 * (OMA.S_oeis_a079291.P n) ^ 2 + 1 := by
      exact_mod_cast h
    omega
  · rw [ho.neg_one_pow] at h
    have : (OMA.S_oeis_a079291.A n) ^ 2 + 1 = 2 * (OMA.S_oeis_a079291.P n) ^ 2 := by
      have h' : ((OMA.S_oeis_a079291.A n) ^ 2 + 1 : ℤ) = 2 * (OMA.S_oeis_a079291.P n) ^ 2 := by
        linear_combination h
      exact_mod_cast h'
    omega
