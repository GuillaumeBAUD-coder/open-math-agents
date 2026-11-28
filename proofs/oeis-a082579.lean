import OMAStatements.S_oeis_a082579

namespace OMA.S_oeis_a082579

/-- Shifting the argument by `j` does not change a descending factorial modulo `j`. -/
lemma descFactorial_shift_dvd (x j r : ℕ) :
    (j : ℤ) ∣ ((x + j).descFactorial r : ℤ) - (x.descFactorial r : ℤ) := by
  have h := Polynomial.sub_dvd_eval_sub ((x + j : ℕ) : ℤ) (x : ℤ) (descPochhammer ℤ r)
  rw [descPochhammer_eval_eq_descFactorial, descPochhammer_eval_eq_descFactorial] at h
  simpa using h

/-- Low terms: for `m < k`, the term `(n+k)!/m! * C(...)` is divisible by `k`. -/
lemma low_term_dvd (k n m : ℕ) (hk : 0 < k) (hm : m < k) :
    k ∣ (n + k).factorial / m.factorial * (n + k + m - 1).choose (n + k - m) := by
  apply Dvd.dvd.mul_right
  apply Nat.dvd_div_of_mul_dvd
  have h1 : m.factorial ∣ (k - 1).factorial := Nat.factorial_dvd_factorial (by omega)
  have h2 : k.factorial ∣ (n + k).factorial := Nat.factorial_dvd_factorial (by omega)
  rw [← Nat.mul_factorial_pred (by omega : k ≠ 0)] at h2
  exact dvd_trans (by rw [mul_comm]; exact Nat.mul_dvd_mul_left k h1) h2

/-- High terms: shifting both `n` and `m` by `k` preserves the term modulo `k`. -/
lemma high_term_modEq (k n m : ℕ) (hm : m ≤ n) :
    (k : ℤ) ∣ (((n + k).factorial / (k + m).factorial *
        (n + k + (k + m) - 1).choose (n + k - (k + m)) : ℕ) : ℤ) -
      ((n.factorial / m.factorial * (n + m - 1).choose (n - m) : ℕ) : ℤ) := by
  rcases Nat.eq_or_lt_of_le hm with h | h
  · subst h
    have e1 : m + k - (k + m) = 0 := by omega
    rw [e1, Nat.sub_self, Nat.choose_zero_right, Nat.choose_zero_right,
      show m + k = k + m by omega, Nat.div_self (Nat.factorial_pos _),
      Nat.div_self (Nat.factorial_pos _)]
    simp
  · set r := n - m with hr
    set N := n + m - 1 with hN
    have e1 : n + k - (k + m) = r := by omega
    have e2 : n + k + (k + m) - 1 = N + 2 * k := by omega
    have eD : n.factorial / m.factorial = n.descFactorial r := by
      rw [Nat.descFactorial_eq_div (by omega), show n - r = m by omega]
    have eD' : (n + k).factorial / (k + m).factorial = (n + k).descFactorial r := by
      rw [Nat.descFactorial_eq_div (by omega), show n + k - r = k + m by omega]
    rw [e1, e2, eD, eD']
    obtain ⟨q, hq⟩ := Nat.factorial_dvd_descFactorial n r
    have hC : ∀ y : ℕ, ((r.factorial * y.choose r : ℕ) : ℤ) = (y.descFactorial r : ℤ) := by
      intro y; rw [Nat.descFactorial_eq_factorial_mul_choose]
    have key : (((n + k).descFactorial r * (N + 2 * k).choose r : ℕ) : ℤ) -
        ((n.descFactorial r * N.choose r : ℕ) : ℤ) =
        (((n + k).descFactorial r : ℤ) - (n.descFactorial r : ℤ)) * ((N + 2 * k).choose r : ℤ)
        + (q : ℤ) * (((N + 2 * k).descFactorial r : ℤ) - (N.descFactorial r : ℤ)) := by
      rw [← hC (N + 2 * k), ← hC N, hq]
      push_cast
      ring
    rw [key]
    apply dvd_add
    · exact Dvd.dvd.mul_right (descFactorial_shift_dvd n k r) _
    · apply Dvd.dvd.mul_left
      have := descFactorial_shift_dvd N (2 * k) r
      push_cast at this
      exact dvd_trans ⟨2, by ring⟩ this

end OMA.S_oeis_a082579

open OMA.S_oeis_a082579

theorem OMA.solution : type_of% @OMA.S_oeis_a082579.main := by
  intro k hk n
  unfold a
  rw [show n + k + 1 = k + (n + 1) by omega, Finset.sum_range_add]
  push_cast
  have hlow : (k : ℤ) ∣ ∑ x ∈ Finset.range k,
      (((n + k).factorial / x.factorial * (n + k + x - 1).choose (n + k - x) : ℕ) : ℤ) := by
    apply Finset.dvd_sum
    intro m hm
    exact Int.natCast_dvd_natCast.mpr (low_term_dvd k n m (by omega) (Finset.mem_range.mp hm))
  have hhigh : (k : ℤ) ∣ ∑ x ∈ Finset.range (n + 1),
      ((((n + k).factorial / (k + x).factorial *
        (n + k + (k + x) - 1).choose (n + k - (k + x)) : ℕ) : ℤ) -
      ((n.factorial / x.factorial * (n + x - 1).choose (n - x) : ℕ) : ℤ)) := by
    apply Finset.dvd_sum
    intro m hm
    exact high_term_modEq k n m (by have := Finset.mem_range.mp hm; omega)
  rw [Finset.sum_sub_distrib] at hhigh
  push_cast at hlow hhigh
  have := dvd_add hlow hhigh
  rw [add_sub_assoc]
  exact this
