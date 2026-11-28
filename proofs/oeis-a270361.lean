import OMAStatements.S_oeis_a270361

-- Problem oeis-a270361: for an odd prime p, at most one odd prime q < p makes p q - 1 a square.
-- Upstream: statements/oeis-a270361.lean (declaration OMA.S_oeis_a270361.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: let p q1 = x^2 + 1 and p q2 = y^2 + 1 with q1, q2 < p, so x, y < p. Then p divides
-- x^2 - y^2 = (x - y)(x + y). If p | x - y then x = y and q1 = q2. Otherwise x + y = p, and substituting
-- y = p - x gives q2 + 2x = p + q1, which is impossible because p, q1, q2 are all odd.

theorem OMA.solution : type_of% @OMA.S_oeis_a270361.main := by
  intro p hp hpodd q1 h1 q2 h2
  obtain ⟨hq1, hq1o, hq1p, ⟨x, hx⟩⟩ := h1
  obtain ⟨hq2, hq2o, hq2p, ⟨y, hy⟩⟩ := h2
  have m1 := Nat.mul_pos hp.pos hq1.pos
  have m2 := Nat.mul_pos hp.pos hq2.pos
  have e1 : p * q1 = x * x + 1 := by omega
  have e2 : p * q2 = y * y + 1 := by omega
  have l1 : p * q1 < p * p := Nat.mul_lt_mul_of_pos_left hq1p hp.pos
  have l2 : p * q2 < p * p := Nat.mul_lt_mul_of_pos_left hq2p hp.pos
  have hxp : x < p := by
    by_contra h
    have h' : p ≤ x := Nat.le_of_not_lt h
    have := Nat.mul_le_mul h' h'
    omega
  have hyp : y < p := by
    by_contra h
    have h' : p ≤ y := Nat.le_of_not_lt h
    have := Nat.mul_le_mul h' h'
    omega
  have hx0 : 0 < x := by
    by_contra h
    have h0 : x = 0 := by omega
    subst h0
    nlinarith [hp.two_le, hq1.two_le]
  have E1 : (p : ℤ) * q1 = x * x + 1 := by exact_mod_cast e1
  have E2 : (p : ℤ) * q2 = y * y + 1 := by exact_mod_cast e2
  have hdiv : (p : ℤ) ∣ ((x : ℤ) - y) * (x + y) := ⟨(q1 : ℤ) - q2, by linear_combination E2 - E1⟩
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpos : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hxp' : (x : ℤ) < p := by exact_mod_cast hxp
  have hyp' : (y : ℤ) < p := by exact_mod_cast hyp
  have hx0' : (0 : ℤ) < x := by exact_mod_cast hx0
  have hy0' : (0 : ℤ) ≤ y := Int.natCast_nonneg y
  rcases hprime.dvd_or_dvd hdiv with h | h
  · have hxy : (x : ℤ) - y = 0 :=
      Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> linarith)
    have hxy' : x = y := by omega
    subst hxy'
    exact Nat.eq_of_mul_eq_mul_left hp.pos (by omega)
  · obtain ⟨c, hc⟩ := h
    have hc1 : c = 1 := by
      have h1 : (0 : ℤ) < p * c := by rw [← hc]; linarith
      have h2 : (p : ℤ) * c < p * 2 := by rw [← hc]; linarith
      have hc0 : 0 < c := (mul_pos_iff_of_pos_left hpos).mp h1
      have hc2 : c < 2 := lt_of_mul_lt_mul_left h2 hpos.le
      omega
    subst hc1
    have hy' : (y : ℤ) = p - x := by linarith [hc]
    have hkey : (p : ℤ) * ((q2 : ℤ) + 2 * x - p - q1) = 0 := by
      rw [hy'] at E2
      linear_combination E2 - E1
    have hsum : (q2 : ℤ) + 2 * x - p - q1 = 0 := by
      rcases mul_eq_zero.mp hkey with h0 | h0
      · exfalso
        linarith
      · exact h0
    obtain ⟨a, ha⟩ := hpodd
    obtain ⟨b, hb⟩ := hq1o
    obtain ⟨d, hd⟩ := hq2o
    omega
