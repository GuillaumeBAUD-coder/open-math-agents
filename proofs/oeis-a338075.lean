import OMAStatements.S_oeis_a338075

-- Problem: A338075: Diagonal terms in the expansion of (1+x*y*z)/(1-x-y-z).
-- Upstream: formal-conjectures statements/oeis-a338075.lean:0 (declaration OMA.S_oeis_a338075.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The g.f. identity is the definition of a(n) read coefficientwise. For the recurrence, t satisfies
(k+1)^2 t(k+1) = 3 (3k+1) (3k+2) t(k); the left side, multiplied by ((n+1)(n+2)(n+3)(n+4))^2, is a
polynomial combination of these relations for k = n, ..., n+3. -/

namespace A338075Aux

open OMA.S_oeis_a338075 PowerSeries

theorem tR (k : ℕ) : ((k : ℚ) + 1) ^ 2 * t (k + 1) = 3 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 2) * t k := by
  unfold t
  have e : 3 * (k + 1) = 3 * k + 2 + 1 := by ring
  rw [e]
  simp only [Nat.factorial_succ]
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  have h2 : (k : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem a_succ (k : ℕ) : a (k + 1) = t k + t (k + 1) := by
  simp [a]

theorem a_zero : a 0 = t 0 := by
  simp [a]

end A338075Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a338075.main := by
  refine ⟨?_, ?_⟩
  · ext n
    cases n with
    | zero =>
      simp [A338075Aux.a_zero, add_mul]
    | succ k =>
      rw [PowerSeries.coeff_mk, A338075Aux.a_succ, add_mul, one_mul, map_add, PowerSeries.coeff_mk,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
      ring
  · intro n
    rw [A338075Aux.a_succ n, A338075Aux.a_succ (n + 1), A338075Aux.a_succ (n + 2), A338075Aux.a_succ (n + 3)]
    have r0 := A338075Aux.tR n
    have r1 := A338075Aux.tR (n + 1)
    have r2 := A338075Aux.tR (n + 2)
    have r3 := A338075Aux.tR (n + 3)
    push_cast at r0 r1 r2 r3
    have key : (576 + 2400 * (n : ℚ) + 4180 * (n : ℚ) ^ 2 + 3980 * (n : ℚ) ^ 3 + 2273 * (n : ℚ) ^ 4 + 800 * (n : ℚ) ^ 5 + 170 * (n : ℚ) ^ 6 + 20 * (n : ℚ) ^ 7 + (n : ℚ) ^ 8) *
        ((-27 * (n : ℚ) ^ 2 - 27 * (n : ℚ) - 6) * (OMA.S_oeis_a338075.t n + OMA.S_oeis_a338075.t (n + 1)) +
        (-53 * (n : ℚ) ^ 2 - 214 * (n : ℚ) - 173) * (OMA.S_oeis_a338075.t (n + 1) + OMA.S_oeis_a338075.t (n + 1 + 1)) +
        (-25 * (n : ℚ) ^ 2 - 179 * (n : ℚ) - 319) * (OMA.S_oeis_a338075.t (n + 2) + OMA.S_oeis_a338075.t (n + 2 + 1)) +
        ((n : ℚ) ^ 2 + 8 * (n : ℚ) + 16) * (OMA.S_oeis_a338075.t (n + 3) + OMA.S_oeis_a338075.t (n + 3 + 1))) = 0 := by
      linear_combination (576 + 2400 * (n : ℚ) + 4180 * (n : ℚ) ^ 2 + 3980 * (n : ℚ) ^ 3 + 2273 * (n : ℚ) ^ 4 + 800 * (n : ℚ) ^ 5 + 170 * (n : ℚ) ^ 6 + 20 * (n : ℚ) ^ 7 + (n : ℚ) ^ 8) * r3 + (1728 + 7200 * (n : ℚ) + 12540 * (n : ℚ) ^ 2 + 11940 * (n : ℚ) ^ 3 + 6819 * (n : ℚ) ^ 4 + 2400 * (n : ℚ) ^ 5 + 510 * (n : ℚ) ^ 6 + 60 * (n : ℚ) ^ 7 + 3 * (n : ℚ) ^ 8) * r2 + (1728 + 7200 * (n : ℚ) + 12540 * (n : ℚ) ^ 2 + 11940 * (n : ℚ) ^ 3 + 6819 * (n : ℚ) ^ 4 + 2400 * (n : ℚ) ^ 5 + 510 * (n : ℚ) ^ 6 + 60 * (n : ℚ) ^ 7 + 3 * (n : ℚ) ^ 8) * r1 + (576 + 2400 * (n : ℚ) + 4180 * (n : ℚ) ^ 2 + 3980 * (n : ℚ) ^ 3 + 2273 * (n : ℚ) ^ 4 + 800 * (n : ℚ) ^ 5 + 170 * (n : ℚ) ^ 6 + 20 * (n : ℚ) ^ 7 + (n : ℚ) ^ 8) * r0
    have hD : (576 + 2400 * (n : ℚ) + 4180 * (n : ℚ) ^ 2 + 3980 * (n : ℚ) ^ 3 + 2273 * (n : ℚ) ^ 4 + 800 * (n : ℚ) ^ 5 + 170 * (n : ℚ) ^ 6 + 20 * (n : ℚ) ^ 7 + (n : ℚ) ^ 8) ≠ 0 := by
      have e : (576 + 2400 * (n : ℚ) + 4180 * (n : ℚ) ^ 2 + 3980 * (n : ℚ) ^ 3 + 2273 * (n : ℚ) ^ 4 + 800 * (n : ℚ) ^ 5 + 170 * (n : ℚ) ^ 6 + 20 * (n : ℚ) ^ 7 + (n : ℚ) ^ 8) = (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3) * ((n : ℚ) + 4)) ^ 2 := by ring
      rw [e]
      positivity
    have h := (mul_eq_zero.mp key).resolve_left hD
    linear_combination h
