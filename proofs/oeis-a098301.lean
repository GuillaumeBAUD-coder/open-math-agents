import OMAStatements.S_oeis_a098301
import Mathlib

namespace OMA.A098301Proof

open OMA.S_oeis_a098301

/-- Squares below a bound: a bounded search decides `IsSquare`. -/
lemma isSquare_iff_bdd (k : ℕ) : IsSquare k ↔ ∃ r < k + 1, k = r * r := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_, hr⟩
    rcases Nat.eq_zero_or_pos r with h | h
    · omega
    · have : r ≤ r * r := Nat.le_mul_of_pos_left r h
      omega
  · rintro ⟨r, -, hr⟩
    exact ⟨r, hr⟩

instance : DecidablePred IsA007654 := fun k =>
  decidable_of_iff (12 ∣ k * (k + 1) ∧ ∃ r < k * (k + 1) / 12 + 1, k * (k + 1) / 12 = r * r)
    (by rw [IsA007654, isSquare_iff_bdd])

instance : DecidablePred IsA046184 := fun m =>
  decidable_of_iff (1 ≤ m ∧ ∃ r < m * (3 * m - 2) + 1, m * (3 * m - 2) = r * r)
    (by rw [IsA046184, isSquare_iff_bdd])

instance : DecidablePred IsA055793 := fun k =>
  decidable_of_iff ((∃ r < k + 1, k = r * r) ∧ ∃ r < k / 3 + 1, k / 3 = r * r)
    (by rw [IsA055793, isSquare_iff_bdd, isSquare_iff_bdd])

lemma A007654_two : A007654 2 = 3 := by
  have h : Nat.count IsA007654 3 = 1 := by decide
  have := Nat.nth_count (p := IsA007654) (n := 3) (by decide)
  rw [h] at this
  simpa [A007654] using this

lemma A007655_two : A007655 2 = 1 := by
  simp [A007655, A007654_two]

lemma A046184_one : A046184 1 = 1 := by
  have h : Nat.count IsA046184 1 = 0 := by decide
  have := Nat.nth_count (p := IsA046184) (n := 1) (by decide)
  rw [h] at this
  simpa [A046184] using this

lemma A055793_three : A055793 3 = 4 := by
  have h : Nat.count IsA055793 4 = 2 := by decide
  have := Nat.nth_count (p := IsA055793) (n := 4) (by decide)
  rw [h] at this
  simpa [A055793] using this

lemma a_two : a 2 = 16 := by
  have h : ((2 : ℕ) : ℤ) = 2 := rfl
  simp only [a, h, Polynomial.Chebyshev.T_two]
  norm_num

/-- At `n = 1` the identity reads `4*1 + 1 = 4 + 16`, which is false. -/
theorem main_disproof :
    ¬ (∀ n : ℕ, 1 ≤ n →
      4 * (A007655 (n + 1) : ℤ) + A046184 n = A055793 (n + 2) + a (n + 1)) := by
  intro h
  have h1 := h 1 le_rfl
  rw [A007655_two, A046184_one, A055793_three, a_two] at h1
  norm_num at h1

end OMA.A098301Proof

open OMA.A098301Proof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a098301.main) := main_disproof
