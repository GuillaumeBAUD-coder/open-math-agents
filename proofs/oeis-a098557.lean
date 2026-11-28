import OMAStatements.S_oeis_a098557
import Mathlib

namespace A098557Aux

lemma coeffS (n m : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (((2 * k + 1 : ℚ)⁻¹) • (Polynomial.X ^ (2 * k + 1) : Polynomial ℚ))).coeff m =
      if m % 2 = 1 ∧ m / 2 ≤ n then ((m : ℚ))⁻¹ else 0 := by
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases h : m % 2 = 1 ∧ m / 2 ≤ n
  · rw [if_pos h, Finset.sum_eq_single (m / 2)]
    · have hm : m = 2 * (m / 2) + 1 := by omega
      rw [if_pos hm]
      have hq : (m : ℚ) = 2 * ((m / 2 : ℕ) : ℚ) + 1 := by exact_mod_cast hm
      rw [hq]
    · intro b _ hne
      rw [if_neg (by omega)]
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_range]
      omega
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [if_neg (by omega)]

open OMA.S_oeis_a098557 in
lemma a_succ (m : ℕ) : a (m + 1) = ((m + 1).factorial : ℚ) *
    ((if (m + 1) % 2 = 1 ∧ (m + 1) / 2 ≤ m + 1 then (((m + 1 : ℕ) : ℚ))⁻¹ else 0) +
     (if m % 2 = 1 ∧ m / 2 ≤ m + 1 then ((m : ℚ))⁻¹ else 0)) := by
  unfold a polyTrunc
  rw [add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul, coeffS, coeffS]

open OMA.S_oeis_a098557 in
lemma a_odd (q : ℕ) : a (2 * q + 1) = ((2 * q).factorial : ℚ) := by
  rw [a_succ, if_pos (by omega), if_neg (by omega), Nat.factorial_succ]
  push_cast
  field_simp
  ring

open OMA.S_oeis_a098557 in
lemma a_even (q : ℕ) : a (2 * q + 2) = ((2 * q + 2).factorial : ℚ) / (2 * (q : ℚ) + 1) := by
  rw [show 2 * q + 2 = (2 * q + 1) + 1 by ring, a_succ, if_neg (by omega), if_pos (by omega)]
  push_cast
  field_simp
  ring

end A098557Aux

open OMA.S_oeis_a098557 A098557Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a098557.main := by
  intro n hn
  have hpos : ∀ q : ℕ, (2 * (q : ℚ) + 1) ≠ 0 := fun q => by positivity
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨q, rfl⟩ : ∃ q, n = 2 * q + 4 := ⟨(n - 4) / 2, by have := Nat.even_iff.mp he; omega⟩
    rw [show 2 * q + 4 - 1 = 2 * (q + 1) + 1 by omega, show 2 * q + 4 - 2 = 2 * q + 2 by omega,
      show 2 * q + 4 = 2 * (q + 1) + 2 by ring, a_even (q + 1), a_odd (q + 1), a_even q,
      show 2 * (q + 1) + 2 = (2 * q + 2) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      show 2 * (q + 1) = 2 * q + 2 by ring]
    have h1 := hpos q
    have h2 := hpos (q + 1)
    push_cast at h2 ⊢
    field_simp
    ring
  · obtain ⟨q, rfl⟩ : ∃ q, n = 2 * q + 3 := ⟨(n - 3) / 2, by have := Nat.odd_iff.mp ho; omega⟩
    rw [show 2 * q + 3 - 1 = 2 * q + 2 by omega, show 2 * q + 3 - 2 = 2 * q + 1 by omega,
      show 2 * q + 3 = 2 * (q + 1) + 1 by ring, a_odd (q + 1), a_even q, a_odd q,
      show 2 * (q + 1) = (2 * q + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    have h1 := hpos q
    push_cast
    field_simp
    ring
