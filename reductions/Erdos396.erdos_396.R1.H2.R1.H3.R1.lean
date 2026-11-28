import OMAReductions.R_Erdos396_erdos_396_R1_H2_R1

namespace OMA.R_Erdos396_erdos_396_R1_H2_R1_H3_R1

private theorem prime_hits_window (a L p : ℕ) (hp : p.Prime)
    (h : p ∣ (a+L).descFactorial L) :
    ∃ j : ℕ, 0 < j ∧ j ≤ L ∧ p ∣ a+j := by
  induction L with
  | zero => simp [hp.not_dvd_one] at h
  | succ L ih =>
    change p ∣ (a+L+1).descFactorial (L+1) at h
    rw [Nat.succ_descFactorial_succ] at h
    obtain ht | ht := hp.dvd_mul.mp h
    · exact ⟨L+1, by omega, by omega, by simpa [Nat.add_assoc] using ht⟩
    · obtain ⟨j, hj, hjL, hd⟩ := ih ht
      exact ⟨j, hj, by omega, hd⟩

/-- Advancing a window by one can only decrease the central coefficient's
p-valuation at a multiple of p. If such a multiple is reached, all preceding
terms in the window are units at p, so the certificate there suffices. -/
private theorem large_prime_window (a L p : ℕ) (hp : p.Prime) (hL : L < p)
    (h : ∀ j : ℕ, 0 < j → j ≤ L →
      (a+j).factorization p ≤ (a+j).centralBinom.factorization p) :
    ((a+L).descFactorial L).factorization p ≤ (a+L).centralBinom.factorization p := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hpos : (a+L).descFactorial L ≠ 0 := (Nat.descFactorial_pos.mpr (by omega)).ne'
    change ((a+L+1).descFactorial (L+1)).factorization p ≤ (a+L+1).centralBinom.factorization p
    rw [Nat.succ_descFactorial_succ,
      Nat.factorization_mul (show a+L+1 ≠ 0 by omega) hpos, Finsupp.add_apply]
    by_cases hd : p ∣ a+L+1
    · have hrest : ¬ p ∣ (a+L).descFactorial L := by
        intro hh
        obtain ⟨j, hj, hjL, hjp⟩ := prime_hits_window a L p hp hh
        have hdelta := Nat.dvd_sub hd hjp
        have := Nat.le_of_dvd (show 0 < (a+L+1)-(a+j) by omega) hdelta
        omega
      rw [Nat.factorization_eq_zero_of_not_dvd hrest, Nat.add_zero]
      simpa [Nat.add_assoc] using h (L+1) (by omega) (by omega)
    · rw [Nat.factorization_eq_zero_of_not_dvd hd, Nat.zero_add]
      apply le_trans (ih (by omega) (fun j hj hjL => h j hj (by omega)))
      have hdiv : (a+L).centralBinom ∣ (a+L+1) * (a+L+1).centralBinom := by
        rw [Nat.succ_mul_centralBinom_succ]
        exact dvd_mul_left _ _
      have hval := (Nat.factorization_le_iff_dvd (Nat.centralBinom_ne_zero (a+L))
        (mul_ne_zero (show a+L+1 ≠ 0 by omega) (Nat.centralBinom_ne_zero (a+L+1)))).mpr hdiv p
      simpa [Nat.factorization_mul (show a+L+1 ≠ 0 by omega) (Nat.centralBinom_ne_zero _),
        Nat.factorization_eq_zero_of_not_dvd hd] using hval

/-- Search only for individual large-prime certificates, each tested at its
own index. The endpoint progression reserves the factorial for small primes. -/
def H1 : Prop := ∀ k : ℕ, 17 ≤ k →
    (∃ n : ℕ, n.descFactorial (k+1) ∣ n.centralBinom) →
    ∃ a : ℕ, (k+2).factorial ^ 2 ∣ a + (k+2) + 1 ∧
      ∀ j : ℕ, 0 < j → j ≤ k+2 → ∀ p : ℕ, p.Prime → k+2 < p →
        (a+j).factorization p ≤ (a+j).centralBinom.factorization p

/-- A local congruence problem independent of the central binomial sequence:
on this progression the binomial quotient of the window by its factorial
has no prime factor in common with the factorial. Indeed, reducing the falling
product modulo (L!)² gives (-1)^L L! before division by L!. -/
def H2 : Prop := ∀ n L : ℕ, L ≤ n → L.factorial ^ 2 ∣ n+1 →
    Nat.Coprime (n.choose L) L.factorial

theorem main : H1 → H2 → OMA.R_Erdos396_erdos_396_R1_H2_R1.H3 := by
  intro h1 h2 k hk hw
  obtain ⟨a, halign, hrun⟩ := h1 k hk hw
  let L := k+2
  let n := a+L
  have hLn : L ≤ n := by dsimp [n]; omega
  refine ⟨n, (Nat.factorization_prime_le_iff_dvd
    (Nat.descFactorial_pos.mpr hLn).ne' (Nat.centralBinom_ne_zero n)).mp ?_⟩
  intro p hp
  by_cases hsmall : p ≤ L
  · have hc := h2 n L hLn halign
    have hunit : ¬ p ∣ n.choose L := fun hh =>
      Nat.not_coprime_of_dvd_of_dvd hp.one_lt hh (Nat.dvd_factorial hp.pos hsmall) hc
    have hfac : L.factorial ∣ n.centralBinom := dvd_trans
      (show L.factorial ∣ L.factorial ^ 2 by simp [pow_two])
      (dvd_trans halign (Nat.succ_dvd_centralBinom n))
    change (n.descFactorial L).factorization p ≤ _
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.factorization_mul
      (Nat.factorial_ne_zero _) (Nat.choose_pos hLn).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hunit, Nat.add_zero]
    exact (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero _) (Nat.centralBinom_ne_zero n)).mpr hfac p
  · exact large_prime_window a L p hp (by omega) (fun j hj hjL => hrun j hj hjL p hp (by omega))

end OMA.R_Erdos396_erdos_396_R1_H2_R1_H3_R1
