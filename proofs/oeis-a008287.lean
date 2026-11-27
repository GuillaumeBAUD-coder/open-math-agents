import OMAStatements.S_oeis_a008287

namespace OMA.S_oeis_a008287

open Polynomial Finset

lemma expand_pow (n : ℕ) : (1 + X + X ^ 2 + X ^ 3 : ℤ[X]) ^ n =
    ∑ j ∈ range (n + 1), C ((-2 : ℤ) ^ j * (n.choose j : ℤ)) * (X ^ j * (1 + X) ^ (3 * n - 2 * j)) := by
  have h : (1 + X + X ^ 2 + X ^ 3 : ℤ[X]) = C (-2 : ℤ) * X * (1 + X) + (1 + X) ^ 3 := by
    simp only [map_neg, map_ofNat]; ring
  rw [h, add_pow]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [mul_pow, mul_pow, ← pow_mul]
  have e : 3 * n - 2 * j = j + 3 * (n - j) := by omega
  rw [e, pow_add]
  simp only [map_mul, map_pow, map_natCast]
  ring

theorem solution_main : ∀ n k : ℕ, k ≤ 3 * n →
    T n k = ∑ j ∈ Finset.range (k + 1),
      (-2 : ℤ) ^ j * (n.choose j : ℤ) * ((3 * n - 2 * j).choose (k - j) : ℤ) := by
  intro n k _
  set g : ℕ → ℤ := fun j => (-2 : ℤ) ^ j * (n.choose j : ℤ) * ((3 * n - 2 * j).choose (k - j) : ℤ)
    with hg
  have hT : T n k = ∑ j ∈ range (n + 1), (if j ≤ k then g j else 0) := by
    unfold T
    rw [expand_pow, finsetSum_coeff]
    apply sum_congr rfl
    intro j _
    rw [coeff_C_mul, coeff_X_pow_mul', coeff_one_add_X_pow]
    split_ifs <;> simp [hg]
  rw [hT]
  have h1 : ∑ j ∈ range (n + 1), (if j ≤ k then g j else 0) =
      ∑ j ∈ range (n + k + 1), (if j ≤ k then g j else 0) := by
    apply sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega)
    intro j hj hjn
    have : n < j := by simp at hj hjn; omega
    simp [hg, Nat.choose_eq_zero_of_lt this]
  have h2 : ∑ j ∈ range (k + 1), g j = ∑ j ∈ range (k + 1), (if j ≤ k then g j else 0) := by
    apply sum_congr rfl
    intro j hj
    have : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp [this]
  have h3 : ∑ j ∈ range (k + 1), (if j ≤ k then g j else 0) =
      ∑ j ∈ range (n + k + 1), (if j ≤ k then g j else 0) := by
    apply sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega)
    intro j hj hjn
    have : ¬ j ≤ k := by simp at hjn; omega
    simp [this]
  rw [h1, ← h3, ← h2]

end OMA.S_oeis_a008287

theorem OMA.solution : type_of% @OMA.S_oeis_a008287.main := OMA.S_oeis_a008287.solution_main
