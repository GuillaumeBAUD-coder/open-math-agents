import OMAStatements.S_oeis_a098557
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: closed forms a(2m+1)=(2m)! and a(2m+2)=(2m+2)(2m)! from the coefficients of the truncated series, then the recurrence by ring.

namespace OMA.S_oeis_a098557


noncomputable def S (N : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (N + 1), (((2 * k + 1 : ℚ)⁻¹) • (Polynomial.X ^ (2 * k + 1)))

lemma coeff_S (N j : ℕ) : (S N).coeff j =
    ∑ k ∈ Finset.range (N + 1), (if j = 2 * k + 1 then ((2 * k + 1 : ℚ)⁻¹) else 0) := by
  unfold S
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul]
  split_ifs <;> simp

lemma coeff_S_odd (N m : ℕ) (h : m ≤ N) : (S N).coeff (2 * m + 1) = ((2 * m + 1 : ℚ)⁻¹) := by
  rw [coeff_S, Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    rw [if_neg]
    omega
  · intro hm
    simp at hm
    omega

lemma coeff_S_even (N m : ℕ) : (S N).coeff (2 * m) = 0 := by
  rw [coeff_S]
  apply Finset.sum_eq_zero
  intro b _
  rw [if_neg]
  omega

lemma poly_coeff (n : ℕ) : (polyTrunc (n + 1)).coeff (n + 1) =
    (S (n + 1)).coeff (n + 1) + (S (n + 1)).coeff n := by
  have : polyTrunc (n + 1) = S (n + 1) + Polynomial.X * S (n + 1) := by
    unfold polyTrunc S
    ring
  rw [this, Polynomial.coeff_add, Polynomial.coeff_X_mul]

lemma a_odd (m : ℕ) : a (2 * m + 1) = ((2 * m).factorial : ℚ) := by
  unfold a
  rw [poly_coeff, coeff_S_odd _ _ (by omega), coeff_S_even, Nat.factorial_succ]
  push_cast
  have : (2 * (m : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

lemma a_even (m : ℕ) : a (2 * m + 2) = (2 * m + 2 : ℚ) * ((2 * m).factorial : ℚ) := by
  unfold a
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, poly_coeff,
    show 2 * m + 1 + 1 = 2 * (m + 1) by ring, coeff_S_even, coeff_S_odd _ _ (by omega),
    show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have : (2 * (m : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem main_proof :
    ∀ n : ℕ, 3 ≤ n →
      -a n + a (n - 1) + ((n : ℚ) - 1) * ((n : ℚ) - 3) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 3 ∨ n = 2 * m + 4 := ⟨(n - 3) / 2, by omega⟩
  · rw [show 2 * m + 3 - 1 = 2 * m + 2 by omega, show 2 * m + 3 - 2 = 2 * m + 1 by omega,
      show 2 * m + 3 = 2 * (m + 1) + 1 by ring, a_odd, a_even, a_odd,
      show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  · rw [show 2 * m + 4 - 1 = 2 * (m + 1) + 1 by omega, show 2 * m + 4 - 2 = 2 * m + 2 by omega,
      show 2 * m + 4 = 2 * (m + 1) + 2 by ring, a_odd, a_even, a_even,
      show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring


end OMA.S_oeis_a098557

theorem OMA.solution : type_of% @OMA.S_oeis_a098557.main := OMA.S_oeis_a098557.main_proof
