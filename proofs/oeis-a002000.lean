import OMAStatements.S_oeis_a002000

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: by induction a n ≡ 1 (mod 3) and 3^(2n+2) ∣ a n ^ 2 - 4, using the identity
-- a(n+1)^2 - 4 = (a n ^ 2 - 4) * (a n ^ 2 - 1)^2 and 3 ∣ a n - 1. Then
-- a(n+1) - a n = a n * (a n ^ 2 - 4) is divisible by 3^(2n+2), and n + r + 2 ≤ 2n + 2.

namespace OMA.Sol_oeis_a002000
open OMA.S_oeis_a002000

lemma key (n : ℕ) : 3 ∣ a n - 1 ∧ (3 : ℤ) ^ (2 * n + 2) ∣ a n ^ 2 - 4 := by
  induction n with
  | zero => exact ⟨⟨2, by simp [a]⟩, ⟨5, by simp [a]⟩⟩
  | succ n ih =>
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := ih
    have ha : a (n + 1) = a n * (a n ^ 2 - 3) := rfl
    have hu' : a n = 3 * u + 1 := by linarith
    refine ⟨⟨9 * u ^ 3 + 9 * u ^ 2 - 1, ?_⟩, ?_⟩
    · rw [ha, hu']; ring
    · have : a n = 3 * u + 1 := by linarith
      have e : a (n + 1) ^ 2 - 4 = (a n ^ 2 - 4) * (a n ^ 2 - 1) ^ 2 := by rw [ha]; ring
      rw [e, hv]
      have e2 : a n ^ 2 - 1 = 3 * (u * (3 * u + 2)) := by rw [this]; ring
      rw [e2]
      exact ⟨v * (u * (3 * u + 2)) ^ 2, by ring⟩

end OMA.Sol_oeis_a002000

theorem OMA.solution : type_of% @OMA.S_oeis_a002000.main := by
  intro n r hr
  obtain ⟨-, ⟨v, hv⟩⟩ := OMA.Sol_oeis_a002000.key n
  have ha : OMA.S_oeis_a002000.a (n + 1) = OMA.S_oeis_a002000.a n * (OMA.S_oeis_a002000.a n ^ 2 - 3) := rfl
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  have : OMA.S_oeis_a002000.a (n + 1) - OMA.S_oeis_a002000.a n
      = OMA.S_oeis_a002000.a n * (OMA.S_oeis_a002000.a n ^ 2 - 4) := by rw [ha]; ring
  rw [this, hv]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (pow_dvd_pow 3 (by omega)) _) _
