import OMAStatements.S_oeis_a068073

-- Problem: A068073: Period 4 sequence [ 1, 2, 3, 2, ...].
-- Upstream: formal-conjectures statements/oeis-a068073.lean:0 (declaration OMA.S_oeis_a068073.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Disproof: at n = 3 the summand does not depend on k; A001045(3) = 3 has two binary 1's and
-- A001045(2) = 1, so the summand is e^(i*Pi*(2 - 1)) = -1 and the sum is 4 * (-1) = -4, while
-- a(3) = 2.

namespace N12A068073D

open OMA.S_oeis_a068073

theorem s_odd (x : ℕ) : a000120 (2 * x + 1) = a000120 x + 1 := by
  unfold a000120
  rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * x + 1)]
  have h1 : (2 * x + 1) % 2 = 1 := by omega
  have h2 : (2 * x + 1) / 2 = x := by omega
  rw [h1, h2, List.count_cons_self]

theorem s_zero : a000120 0 = 0 := by
  unfold a000120
  simp

theorem s_three : a000120 3 = 2 := by
  have h1 : a000120 3 = a000120 1 + 1 := s_odd 1
  have h0 : a000120 1 = a000120 0 + 1 := s_odd 0
  have hz := s_zero
  omega

end N12A068073D

open OMA.S_oeis_a068073 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068073.main) := by
  intro h
  have h3 : (a 3 : ℂ) = ∑ _k ∈ Finset.range (3 + 1),
      Complex.exp (Complex.I * Real.pi *
        ((a000120 (a001045 3) : ℂ) - (a001045 (a000120 3) : ℂ))) := h 3
  have hJ3 : a001045 3 = 3 := rfl
  have hJ2 : a001045 2 = 1 := rfl
  have ha3 : a 3 = 2 := by decide
  have key : ∑ _k ∈ Finset.range (3 + 1),
      Complex.exp (Complex.I * Real.pi *
        ((a000120 (a001045 3) : ℂ) - (a001045 (a000120 3) : ℂ))) = -4 := by
    rw [hJ3, N12A068073D.s_three, hJ2, Finset.sum_const, Finset.card_range]
    have e : Complex.I * (Real.pi : ℂ) * (((2 : ℕ) : ℂ) - ((1 : ℕ) : ℂ)) =
        (Real.pi : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e, Complex.exp_pi_mul_I]
    norm_num
  rw [key, ha3] at h3
  norm_num at h3
