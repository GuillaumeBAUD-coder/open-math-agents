import OMAStatements.S_oeis_a007655
import Mathlib

namespace OMA.A007655Proof

open OMA.S_oeis_a007655

instance : DecidablePred IsA007654 := fun k => by unfold IsA007654; infer_instance
instance : DecidablePred IsA046184 := fun k => by unfold IsA046184; infer_instance
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

instance : DecidablePred IsA055793 := fun k =>
  decidable_of_iff ((∃ r < k + 1, k = r * r) ∧ ∃ r < k / 3 + 1, k / 3 = r * r)
    (by rw [IsA055793, isSquare_iff_bdd, isSquare_iff_bdd])

lemma s7654_two : A007654 2 = 3 := by
  have h : Nat.count IsA007654 3 = 1 := by decide
  have := Nat.nth_count (p := IsA007654) (n := 3) (by decide)
  rw [h] at this
  simpa [A007654] using this

lemma s7655_two : A007655 2 = 1 := by
  simp [A007655, s7654_two]

lemma s46184_one : A046184 1 = 1 := by
  have h : Nat.count IsA046184 1 = 0 := by decide
  have := Nat.nth_count (p := IsA046184) (n := 1) (by decide)
  rw [h] at this
  simpa [A046184] using this

lemma s55793_three : A055793 3 = 4 := by
  have h : Nat.count IsA055793 4 = 2 := by decide
  have := Nat.nth_count (p := IsA055793) (n := 4) (by decide)
  rw [h] at this
  simpa [A055793] using this

lemma s98301_two : A098301 2 = 16 := by
  have h : ((2 : ℕ) : ℤ) = 2 := rfl
  simp only [A098301, h, Polynomial.Chebyshev.T_two]
  norm_num

theorem main_disproof :
    ¬ (∀ n : ℕ, 1 ≤ n →
      (4 * (A007655 (n + 1) : ℤ) + A046184 n = A055793 (n + 2) + A098301 (n + 1)) ∧
      (4 * (A007655 (n + 1) : ℤ) + A098301 (n + 1) + A055793 (n + 2) = A046184 (n + 1)) ∧
      ((4 * (A007655 (n + 1) : ℤ)) ^ 2 = A098301 (2 * n + 1))) := by
  intro h
  have h1 := (h 1 le_rfl).1
  rw [s7655_two, s46184_one, s55793_three, s98301_two] at h1
  norm_num at h1

end OMA.A007655Proof

open OMA.A007655Proof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a007655.main) :=
  main_disproof
