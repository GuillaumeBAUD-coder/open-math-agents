import OMAStatements.S_mse_3767162

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: clear denominators: with D = den(a) den(b), n D^2 = P^2 + Q^2 for integers P, Q.
-- By the two-squares theorem (Nat.eq_sq_add_sq_iff), every prime q = 3 (mod 4) divides n D^2 to
-- an even power; since v_q(n D^2) = v_q(n) + 2 v_q(D), the same holds for n, so n itself is a
-- sum of two squares of natural numbers. No computer search.

namespace OMA.P_mse_3767162

theorem solution :
    ∀ n : ℕ, (∃ a b : ℚ, (n : ℚ) = a ^ 2 + b ^ 2) →
      ∃ c d : ℤ, (n : ℤ) = c ^ 2 + d ^ 2 := by
  rintro n ⟨a, b, h⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, by simp⟩
  have hda : (a.den : ℚ) ≠ 0 := by have := a.den_pos; positivity
  have hdb : (b.den : ℚ) ≠ 0 := by have := b.den_pos; positivity
  have hq : ((n * (a.den * b.den) ^ 2 : ℕ) : ℚ) =
      ((a.num * b.den : ℤ) : ℚ) ^ 2 + ((b.num * a.den : ℤ) : ℚ) ^ 2 := by
    push_cast
    rw [← Rat.mul_den_eq_num a, ← Rat.mul_den_eq_num b, h]
    ring
  have hz : ((n * (a.den * b.den) ^ 2 : ℕ) : ℤ) = (a.num * b.den) ^ 2 + (b.num * a.den) ^ 2 := by
    exact_mod_cast hq
  rw [← Int.natAbs_sq (a.num * b.den), ← Int.natAbs_sq (b.num * a.den)] at hz
  have hN : n * (a.den * b.den) ^ 2 =
      (a.num * b.den).natAbs ^ 2 + (b.num * a.den).natAbs ^ 2 := by exact_mod_cast hz
  have H := Nat.eq_sq_add_sq_iff.mp ⟨_, _, hN⟩
  have hD0 : (a.den * b.den) ^ 2 ≠ 0 := by
    have := a.den_pos; have := b.den_pos; positivity
  have hD1 : a.den * b.den ≠ 0 := by
    have := a.den_pos; have := b.den_pos; positivity
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
    apply Nat.eq_sq_add_sq_iff.mpr
    intro q hq hq4
    have hq' : q ∈ (n * (a.den * b.den) ^ 2).primeFactors :=
      Nat.primeFactors_mono (Dvd.intro _ rfl) (by positivity) hq
    have hp : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
    have := H q hq' hq4
    rw [padicValNat.mul (by omega) hD0, padicValNat.pow] at this
    exact (Nat.even_add.mp this).mpr (even_two_mul _)
  exact ⟨x, y, by exact_mod_cast hxy⟩

end OMA.P_mse_3767162

theorem OMA.solution : type_of% @OMA.S_mse_3767162.main := OMA.P_mse_3767162.solution
