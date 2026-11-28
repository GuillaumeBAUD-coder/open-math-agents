import OMAReductions.R_oeis_a087664_R1

/-!
Even starts of the floor recurrence in OEIS A087664.
Source: https://oeis.org/A087664
Credit: @grp06
-/

open OMA.S_oeis_a087664

private def floorStep (x : ℚ) : ℚ :=
  x * (Int.floor x : ℚ)

private theorem floor_half (t : ℕ) :
    Int.floor ((t : ℚ) + 1 / 2) = (t : ℤ) := by
  apply Int.floor_eq_iff.mpr
  rw [Int.cast_natCast]
  constructor <;> linarith

private theorem even_step (r : ℕ) :
    floorStep (((2 * r : ℕ) : ℚ) + 1 / 2) =
      (((4 * r ^ 2 + r : ℕ) : ℤ) : ℚ) := by
  unfold floorStep
  rw [floor_half, Int.cast_natCast]
  push_cast
  ring

private theorem odd_step (s : ℕ) :
    floorStep (((2 * s + 1 : ℕ) : ℚ) + 1 / 2) =
      ((s * (4 * s + 5) + 1 : ℕ) : ℚ) + 1 / 2 := by
  unfold floorStep
  rw [floor_half, Int.cast_natCast]
  push_cast
  ring

-- For t = 2s + 1, the next half-integer has integer part
-- s * (4s + 5) + 1. The multiplier 4s + 5 is odd.
private theorem half_reaches_integer (j : ℕ) :
    ∀ t u : ℕ, Odd u → t = 2 ^ j * u + 1 →
      ∃ k : ℕ, ∃ m : ℤ, (floorStep^[k]) ((t : ℚ) + 1 / 2) = (m : ℚ) := by
  induction j with
  | zero =>
      intro t u hu ht
      obtain ⟨v, hv⟩ := hu
      have he : t = 2 * (v + 1) := by
        simp only [pow_zero, one_mul] at ht
        omega
      refine ⟨1, ((4 * (v + 1) ^ 2 + (v + 1) : ℕ) : ℤ), ?_⟩
      rw [he]
      exact even_step (v + 1)
  | succ j ih =>
      intro t u hu ht
      let s : ℕ := 2 ^ j * u
      let t' : ℕ := s * (4 * s + 5) + 1
      have hs : t = 2 * s + 1 := by
        rw [ht, pow_succ]
        dsimp [s]
        ring
      have hOdd : Odd (4 * s + 5) := by
        refine ⟨2 * s + 2, ?_⟩
        omega
      have ht' : t' = 2 ^ j * (u * (4 * s + 5)) + 1 := by
        dsimp [t', s]
        ring
      have hstep : floorStep ((t : ℚ) + 1 / 2) = (t' : ℚ) + 1 / 2 := by
        rw [hs]
        exact odd_step s
      obtain ⟨k, m, hm⟩ := ih t' (u * (4 * s + 5)) (hu.mul hOdd) ht'
      refine ⟨k.succ, m, ?_⟩
      rw [Function.iterate_succ_apply, hstep]
      exact hm

private theorem b_eq_iterate (n k : ℕ) :
    b n k = (floorStep^[k]) ((n : ℚ) / 4) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change floorStep (b n k) = floorStep ((floorStep^[k]) ((n : ℚ) / 4))
      rw [ih]

theorem OMA.solution : OMA.R_oeis_a087664_R1.H1 := by
  intro n hn he
  obtain ⟨a, ha⟩ := he
  obtain ⟨t, ht | ht⟩ := Nat.even_or_odd' a
  · have hn4 : n = 4 * t := by omega
    refine ⟨0, (t : ℤ), ?_⟩
    change (n : ℚ) / 4 = ((t : ℤ) : ℚ)
    rw [hn4, Int.cast_natCast]
    push_cast
    ring
  · have hn4 : n = 4 * t + 2 := by omega
    have ht2 : 2 ≤ t := by omega
    have hd : t - 1 ≠ 0 := by omega
    obtain ⟨j, u, hu, hj⟩ := Nat.exists_eq_two_pow_mul_odd hd
    have ht' : t = 2 ^ j * u + 1 := by omega
    have hstart : (n : ℚ) / 4 = (t : ℚ) + 1 / 2 := by
      rw [hn4]
      push_cast
      ring
    obtain ⟨k, m, hm⟩ := half_reaches_integer j t u hu ht'
    refine ⟨k, m, ?_⟩
    rw [b_eq_iterate, hstart]
    exact hm
