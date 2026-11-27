import OMAReductions.R_LittlewoodConjecture_littlewood_conjecture_R1

-- The Littlewood conjecture holds when alpha is rational.
-- Original Lean proof of the trivial case: for n a multiple of the denominator of alpha the number n * alpha is an
-- integer, so its distance to the nearest integer is 0; hence the sequence is 0 infinitely often, and it is
-- nonnegative everywhere, so its liminf is 0.
-- The elementary case, not progress on the Littlewood conjecture.

namespace OMA.Littlewood1

open Filter

theorem rational_case (α β : ℝ) (hq : ∃ q : ℚ, α = q) :
    atTop.liminf (fun (n : ℕ) ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) = 0 := by
  obtain ⟨q, rfl⟩ := hq
  have hnonneg : ∀ n : ℕ,
      0 ≤ (n : ℝ) * distToNearestInt (n * (q : ℝ)) * distToNearestInt (n * β) := fun n =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (distToNearestInt_nonneg _))
      (distToNearestInt_nonneg _)
  have hzero : ∀ a : ℕ, distToNearestInt (((q.den * a : ℕ) : ℝ) * (q : ℝ)) = 0 := by
    intro a
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
    have hx : ((q.den * a : ℕ) : ℝ) * (q : ℝ) = (((a : ℤ) * q.num : ℤ) : ℝ) := by
      rw [Rat.cast_def]
      push_cast
      field_simp
    unfold distToNearestInt
    rw [hx, round_intCast]
    simp
  have hfreq : ∃ᶠ n : ℕ in atTop,
      (n : ℝ) * distToNearestInt (n * (q : ℝ)) * distToNearestInt (n * β) ≤ 0 := by
    rw [frequently_atTop]
    intro a
    refine ⟨q.den * a, Nat.le_mul_of_pos_left a q.den_pos, ?_⟩
    rw [hzero a]
    simp
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun (n : ℕ) ↦ (n : ℝ) * distToNearestInt (n * (q : ℝ)) * distToNearestInt (n * β)) :=
    isBoundedUnder_of ⟨0, hnonneg⟩
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop
      (fun (n : ℕ) ↦ (n : ℝ) * distToNearestInt (n * (q : ℝ)) * distToNearestInt (n * β)) :=
    IsCoboundedUnder.of_frequently_le hfreq
  exact le_antisymm (liminf_le_of_frequently_le hfreq hbdd)
    (le_liminf_of_le hcobdd (Eventually.of_forall hnonneg))

end OMA.Littlewood1

theorem OMA.solution : OMA.R_LittlewoodConjecture_littlewood_conjecture_R1.H1 := by
  intro α β hq
  exact OMA.Littlewood1.rational_case α β hq
