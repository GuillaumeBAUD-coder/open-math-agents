import OMAStatements.S_oeis_a078173

-- OEIS A078173: the largest two coordinates of solutions to r*s*t = n*(r+s+t).
-- Credit: @yuka30240

theorem OMA.solution : type_of% @OMA.S_oeis_a078173.main := by
  intro n hn
  constructor
  · constructor
    · exact ⟨1, n + 1, by decide, by omega, by nlinarith, by ring⟩
    · rintro t ⟨r, s, hr, hrs, _, he⟩
      have hsum : r + s ≤ r * s + 1 := by
        cases r <;> cases s <;> simp_all [Nat.succ_mul, Nat.mul_succ]
        omega
      have hp : n < r * s := Nat.lt_of_mul_lt_mul_right (a := t) (by
        rw [he]
        exact Nat.mul_lt_mul_of_pos_left (by omega) hn)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hp)
      rw [hk] at he hsum
      -- The positive factor k + 1 equals r*s - n.
      apply Nat.le_of_mul_le_mul_left (c := k + 1) _ (by omega)
      nlinarith only [he, Nat.mul_le_mul_left n hsum, Nat.zero_le (n * n * k),
        Nat.zero_le (n * k)]
  · constructor
    · exact ⟨1, 2 * n + 1, by decide, by omega, by omega, by ring⟩
    · rintro s ⟨r, t, hr, _, hst, he⟩
      have h : s * t ≤ n * (1 + s + t) := by
        apply Nat.le_of_mul_le_mul_left (c := r) _ hr
        rw [← Nat.mul_assoc, he]
        nlinarith only [Nat.mul_le_mul_left n (Nat.mul_le_mul_left (s + t) hr)]
      -- If s ≥ 2*n + 1, the left side is at least (2*n + 1)*t
      -- and the right side is at most n*(1 + 2*t), forcing t ≤ n.
      by_contra! hs
      nlinarith only [h, Nat.mul_le_mul_right t (Nat.succ_le_of_lt hs),
        Nat.mul_le_mul_left n hst, hs, hst]

