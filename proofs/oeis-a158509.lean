import OMAStatements.S_oeis_a158509

namespace OMA.A158509Proof

lemma not_prime_of_dvd (d r : ℕ) (hd : d ∣ r) (h1 : 2 ≤ d) (h2 : d < r) : ¬ r.Prime := by
  intro hr
  rcases hr.eq_one_or_self_of_dvd d hd with h | h <;> omega

lemma core (i : ℕ) (hsq : IsSquare (Nat.nth Nat.Prime i + 5))
    (heq : Nat.nth Nat.Prime i + 5 = Nat.nth Nat.Prime (i + 2) - 1) :
    Nat.nth Nat.Prime (i + 1) = Nat.nth Nat.Prime i + 2 ∧ Nat.nth Nat.Prime i % 10 = 1 ∧
      Nat.nth Nat.Prime (i + 1) % 10 = 3 := by
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hp := Nat.prime_nth_prime i
  have hq := Nat.prime_nth_prime (i + 1)
  have hs := Nat.prime_nth_prime (i + 2)
  have l1 : Nat.nth Nat.Prime i < Nat.nth Nat.Prime (i + 1) := hmono (by omega)
  have l2 : Nat.nth Nat.Prime (i + 1) < Nat.nth Nat.Prime (i + 2) := hmono (by omega)
  generalize Nat.nth Nat.Prime i = p at *
  generalize Nat.nth Nat.Prime (i + 1) = q at *
  generalize hS : Nat.nth Nat.Prime (i + 2) = s at *
  obtain ⟨r, hr⟩ := hsq
  have p2 := hp.two_le
  have hs6 : s = p + 6 := by omega
  subst hs6
  -- p is odd
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · subst h
      have : r ≤ 2 := by nlinarith
      interval_cases r <;> omega
    · exact h
  have hr3 : 3 ≤ r := by nlinarith
  -- q = p + 2
  have hq2 : q = p + 2 := by
    have hq1 : q ≠ p + 1 := by
      intro h; subst h
      exact not_prime_of_dvd 2 (p + 1) (by omega) le_rfl (by omega) hq
    have hq3 : q ≠ p + 3 := by
      intro h; subst h
      exact not_prime_of_dvd 2 (p + 3) (by omega) le_rfl (by omega) hq
    have hq5 : q ≠ p + 5 := by
      intro h; subst h
      exact not_prime_of_dvd 2 (p + 5) (by omega) le_rfl (by omega) hq
    have hq4 : q ≠ p + 4 := by
      intro h; subst h
      obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
      have hfac : p + 4 = (u + 2) * u := by nlinarith
      exact not_prime_of_dvd (u + 2) (p + 4) ⟨u, hfac⟩ (by omega) (by nlinarith) hq
    omega
  subst hq2
  -- last digits
  have h5p : ¬ 5 ∣ p := fun h => by
    rcases hp.eq_one_or_self_of_dvd 5 h with h' | h'
    · omega
    · subst h'
      have : r ≤ 3 := by nlinarith
      interval_cases r <;> omega
  have h5q : ¬ 5 ∣ p + 2 := fun h => by
    rcases hq.eq_one_or_self_of_dvd 5 h with h' | h'
    · omega
    · nlinarith
  have h5s : ¬ 5 ∣ p + 6 := fun h => by
    rcases hs.eq_one_or_self_of_dvd 5 h with h' | h' <;> omega
  have hmod : (r * r) % 5 = ((r % 5) * (r % 5)) % 5 := by simp [Nat.mul_mod]
  have hr5 : r % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have key : p % 10 = 1 := by
    generalize r % 5 = x at hmod hr5
    interval_cases x <;> omega
  omega

end OMA.A158509Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a158509.main := by
  intro n hn hsq heq
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 2 := ⟨n - 2, by omega⟩
  unfold OMA.S_oeis_a158509.prime at *
  simp only [show i + 2 + 1 - 1 = i + 2 by omega,
    show i + 2 - 1 = i + 1 by omega] at *
  exact OMA.A158509Proof.core i hsq heq
