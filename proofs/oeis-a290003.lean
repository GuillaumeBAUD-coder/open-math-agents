import OMAStatements.S_oeis_a290003

-- Problem: A290003: G.f.: A(x) = Sum_{n=-oo..+oo} (x - x^n)^n.
-- Upstream: formal-conjectures statements/oeis-a290003.lean (declaration OMA.S_oeis_a290003.main)
-- Credit: @Ciphore
-- The statement defines `a` through Bala's divisor-sum formula. For prime p > 3 the divisors
-- of p are 1 and p; the d = 1 term contributes 1 and the d = p term vanishes because both
-- binomial coefficients have lower index exceeding the upper one.

open OMA.S_oeis_a290003

theorem OMA.solution : type_of% @OMA.S_oeis_a290003.main := by
  intro p hp h3
  have hp0 : 0 < p := by omega
  have hne0 : p + 1 ≠ 0 := by omega
  have hne1 : p + 1 ≠ 1 := by omega
  have ha : a (p + 1) = ∑ d ∈ (p + 1 - 1).divisors, term (p + 1) d := by
    unfold a
    rw [if_neg hne0, if_neg hne1]
  have hp1m1 : p + 1 - 1 = p := by omega
  rw [ha, hp1m1, hp.divisors]
  have h1p : (1 : ℕ) ≠ p := by omega
  rw [Finset.sum_pair h1p]
  -- the d = 1 term
  have hterm1 : term (p + 1) 1 = 1 := by
    simp [term, firstChoose]
  -- the d = p term
  have hterm2 : term (p + 1) p = 0 := by
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    have heven : Even (p - 1) := by
      obtain ⟨m, hm⟩ := hodd
      use m
      omega
    have hsign : (-1 : ℤ) ^ (p - 1) = 1 := heven.neg_one_pow
    have hpd1 : (p + 1 - 1) / p = 1 := by
      rw [hp1m1]
      exact Nat.div_self hp0
    have hpd2 : (p + 1 + p - 1) / p = 2 := by
      have e : p + 1 + p - 1 = p * 2 := by omega
      rw [e]
      exact Nat.mul_div_cancel_left 2 hp0
    have hfc : firstChoose ((p + 1 - 1) / p) p = 0 := by
      rw [hpd1]
      unfold firstChoose
      rw [if_pos (by omega : 2 ≤ p)]
      exact Nat.choose_eq_zero_of_lt (by omega : 1 < p - 2)
    have hsc : Nat.choose ((p + 1 + p - 1) / p) (p - 1) = 0 := by
      rw [hpd2]
      exact Nat.choose_eq_zero_of_lt (by omega : 2 < p - 1)
    unfold term
    rw [hfc, hsc, hsign]
    simp
  rw [hterm1, hterm2]
  norm_num
