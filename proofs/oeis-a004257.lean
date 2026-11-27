import OMAStatements.S_oeis_a004257

-- Problem: A004257: a(n) = round(log_2(n)).
-- Upstream: formal-conjectures statements/oeis-a004257.lean:0 (declaration OMA.S_oeis_a004257.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a004257

open OMA.S_oeis_a004257

lemma hermite (x : ℝ) : ⌊2 * x⌋ = ⌊x⌋ + ⌊x + 1 / 2⌋ := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  by_cases h : x < ⌊x⌋ + 1 / 2
  · have e1 : ⌊2 * x⌋ = 2 * ⌊x⌋ := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    have e2 : ⌊x + 1 / 2⌋ = ⌊x⌋ := by
      rw [Int.floor_eq_iff]
      constructor <;> linarith
    rw [e1, e2]
    ring
  · replace h := not_lt.mp h
    have e1 : ⌊2 * x⌋ = 2 * ⌊x⌋ + 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    have e2 : ⌊x + 1 / 2⌋ = ⌊x⌋ + 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    rw [e1, e2]
    ring

lemma floor_logb (m : ℕ) : ⌊Real.logb 2 (m : ℝ)⌋ = (Nat.log 2 m : ℤ) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp
  · have := Real.floor_logb_natCast (b := 2) (r := (m : ℝ)) (by positivity)
    rw [Int.log_natCast] at this
    exact_mod_cast this

lemma solve : ∀ n : ℕ, 1 ≤ n → a n = (Nat.log 2 (n ^ 2) : ℤ) - (Nat.log 2 n : ℤ) := by
  intro n hn
  have hx : Real.logb 2 ((n ^ 2 : ℕ) : ℝ) = 2 * Real.logb 2 (n : ℝ) := by
    push_cast
    rw [Real.logb_pow]
    norm_num
  rw [← floor_logb, ← floor_logb, hx, hermite, a, round_eq]
  ring

end OMA.P_oeis_a004257

theorem OMA.solution : type_of% @OMA.S_oeis_a004257.main := OMA.P_oeis_a004257.solve
