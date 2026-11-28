import OMAStatements.S_oeis_a261682

theorem OMA.solution : type_of% @OMA.S_oeis_a261682.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have u (i : ℕ) : ((2*i+1) * (2*i).choose i : ℚ) = (2*i+1).choose i * (i+1) := by
    rw [← Nat.choose_symm_half]
    exact_mod_cast Nat.add_one_mul_choose_eq (2*i) i
  have q (i : ℕ) : ((2*i+2).choose (i+1) : ℚ) = 2 * (2*i+1).choose i := by
    rw [Nat.choose_succ_succ', Nat.choose_symm_half]
    push_cast
    ring
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · have q0 := q i
    have u1 := u (i+1)
    have q1 := q (i+1)
    have u2 := u (i+2)
    simp [OMA.S_oeis_a261682.a, mul_add, add_assoc, pow_succ, show ∀ c, (2*i+c)/2 = i + c/2 by omega, show ∀ c, (2*i+c)%2 = c%2 by omega] at *
    linear_combination (-480*i^3-2416*i^2-3328*i-1392)*q0 -(840*i^2+3148*i+1444)*u1 +(300*i^3+1750*i^2+3092*i+1426)*q1 -(-120*i^2-364*i-136)*u2
  · have u1 := u (i+1)
    have q1 := q (i+1)
    have u2 := u (i+2)
    have q2 := q (i+2)
    simp [OMA.S_oeis_a261682.a, mul_add, add_assoc, pow_succ, show ∀ c, (2*i+c)/2 = i + c/2 by omega, show ∀ c, (2*i+c)%2 = c%2 by omega] at *
    linear_combination -(-720*i^2-3624*i-3720)*u1 +(360*i^3+2292*i^2+4020*i+1824)*q1 -(-120*i+12)*u2 +(-180*i^3-1356*i^2-3063*i-1827)*q2
