import OMAReductions.R_mo_342377_R1

/-!
# Proof of `mo-342377.R1.H1`

Proves that `Nat.ascFactorial a b ≠ Nat.ascFactorial c d + 2` whenever `2 ≤ a`, `2 ≤ c`, `2 ≤ d`,
and either `3 ≤ b` or `b = d = 2`.

- If `3 ≤ b`, then `Nat.ascFactorial a b` is divisible by `a * (a + 1) * (a + 2)`, hence
  `Nat.ascFactorial a b % 3 = 0`. Meanwhile, for `d ≥ 2`, `Nat.ascFactorial c d % 3 ∈ {0, 2}`
  (it is `0` when `d ≥ 3` and `c * (c + 1) % 3 ∈ {0, 2}` when `d = 2`), so
  `(Nat.ascFactorial c d + 2) % 3 ∈ {1, 2}`, contradiction.
- If `b = 2` and `d = 2`, then `a * (a + 1) = c * (c + 1) + 2`, impossible since
  `c * (c + 1) < c * (c + 1) + 2 < (c + 1) * (c + 2)` for `c ≥ 2`.
-/

namespace Mo342377R1H1Proof

private lemma three_dvd_ascFactorial {a b : ℕ} (hb : 3 ≤ b) : 3 ∣ Nat.ascFactorial a b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
  induction k with
  | zero =>
    simp only [add_zero, show (3 : ℕ) = 0 + 1 + 1 + 1 by rfl, Nat.ascFactorial_succ,
      Nat.ascFactorial_zero]
    have h : (a * (a + 1) * (a + 2)) % 3 = 0 := by
      have hm := Nat.mod_lt a (by decide : 0 < 3)
      have h1 : (a * (a + 1) * (a + 2)) % 3 = ((a % 3) * (a % 3 + 1) * (a % 3 + 2)) % 3 := by
        simp [Nat.mul_mod, Nat.add_mod]
      rw [h1]
      generalize a % 3 = r at hm
      interval_cases r <;> decide
    have heq : (a + 2) * ((a + 1) * (a * 1)) = a * (a + 1) * (a + 2) := by
      ring
    rw [heq]
    exact Nat.dvd_of_mod_eq_zero h
  | succ k ih =>
    rw [← add_assoc, Nat.ascFactorial_succ]
    exact dvd_mul_of_dvd_right (ih (by omega)) _

private lemma ascFactorial_mod_three_ne_one {c d : ℕ} (hd : 2 ≤ d) :
    Nat.ascFactorial c d % 3 ≠ 1 := by
  by_cases hd3 : 3 ≤ d
  · have h := Nat.mod_eq_zero_of_dvd (three_dvd_ascFactorial (a := c) hd3)
    omega
  · have hd2 : d = 2 := by omega
    subst hd2
    have heq : Nat.ascFactorial c 2 = c * (c + 1) := by
      simp [show (2 : ℕ) = 0 + 1 + 1 by rfl, Nat.ascFactorial_succ, Nat.ascFactorial_zero]
      ring
    rw [heq]
    have hm := Nat.mod_lt c (by decide : 0 < 3)
    have h1 : (c * (c + 1)) % 3 = ((c % 3) * (c % 3 + 1)) % 3 := by
      simp [Nat.mul_mod, Nat.add_mod]
    rw [h1]
    generalize c % 3 = r at hm
    interval_cases r <;> decide

end Mo342377R1H1Proof

theorem OMA.solution : OMA.R_mo_342377_R1.H1 := by
  intro a b c d ha hc hd hcase heq
  rcases hcase with hb3 | ⟨rfl, rfl⟩
  · have h0 : Nat.ascFactorial a b % 3 = 0 :=
      Nat.mod_eq_zero_of_dvd (Mo342377R1H1Proof.three_dvd_ascFactorial hb3)
    have hne1 : Nat.ascFactorial c d % 3 ≠ 1 :=
      Mo342377R1H1Proof.ascFactorial_mod_three_ne_one hd
    omega
  · have ha2 : Nat.ascFactorial a 2 = a * (a + 1) := by
      simp [show (2 : ℕ) = 0 + 1 + 1 by rfl, Nat.ascFactorial_succ, Nat.ascFactorial_zero]
      ring
    have hc2 : Nat.ascFactorial c 2 = c * (c + 1) := by
      simp [show (2 : ℕ) = 0 + 1 + 1 by rfl, Nat.ascFactorial_succ, Nat.ascFactorial_zero]
      ring
    rw [ha2, hc2] at heq
    have hlt1 : c < a := by
      by_contra hle
      have : a * (a + 1) ≤ c * (c + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hge : (c + 1) * (c + 2) ≤ a * (a + 1) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
