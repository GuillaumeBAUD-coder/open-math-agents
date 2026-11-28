import OMAStatements.S_oeis_a203233

open PowerSeries OMA.S_oeis_a203233

private lemma step (n : ℕ) :
    (products (n+2)).1 = 6 * (products n).1 ∧ a (n+2) = 6 * a n + 5 * (products n).1 := by
  have h : n % 2 = 0 ∧ (n+1) % 2 = 1 ∨ n % 2 = 1 ∧ (n+1) % 2 = 0 := by omega
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    simp only [a, products, digit, h0, h1] <;> constructor <;> ring

private lemma rec4 (n : ℕ) : a (n+4) = 12 * a (n+2) - 36 * a n := by
  have h1 := step n
  have h2 := step (n+2)
  rw [show n+4 = n+2+2 from rfl, h2.2, h1.1]
  rw [h1.2]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a203233.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    exact rec4 m
  · have e : ((1 - C 6 * X^2 : ℤ⟦X⟧)^2 * mk a)
        = mk a - C 12 * (X^2 * mk a) + C 36 * (X^4 * mk a) := by
      have h12 : (C 12 : ℤ⟦X⟧) = 2 * C 6 := by
        rw [show (12 : ℤ) = 2 * 6 by norm_num, map_mul, map_ofNat C 2]
      have h36 : (C 36 : ℤ⟦X⟧) = C 6 * C 6 := by
        rw [← map_mul]; norm_num
      rw [h12, h36]; ring
    rw [e]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
    match n with
    | 0 => norm_num [a, products]
    | 1 => norm_num [a, products, digit]
    | 2 => norm_num [a, products, digit]
    | 3 => norm_num [a, products, digit]
    | m+4 =>
      have h := rec4 m
      simp [show 2 ≤ m+4 by omega, show 4 ≤ m+4 by omega, show m+4-2 = m+2 by omega, h]
