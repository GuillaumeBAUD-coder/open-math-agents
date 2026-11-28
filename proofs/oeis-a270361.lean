import OMAStatements.S_oeis_a270361

namespace OMA.P_oeis_a270361

/-- If `p * q - 1 = a * a` with odd primes `q < p`, then `a` is even and `a < p`. -/
lemma root_facts (p q : ℕ) (hp : p.Prime) (hpo : Odd p) (hq : q.Prime) (hqo : Odd q)
    (hlt : q < p) (hsq : IsSquare (p * q - 1)) :
    ∃ a : ℕ, p * q = a * a + 1 ∧ Even a ∧ a < p := by
  obtain ⟨a, ha⟩ := hsq
  have hpos : 1 ≤ p * q := Nat.mul_pos hp.pos hq.pos
  have hpq : p * q = a * a + 1 := by omega
  refine ⟨a, hpq, ?_, ?_⟩
  · have hodd : Odd (a * a + 1) := hpq ▸ hpo.mul hqo
    have : Even (a * a) := by
      rcases Nat.even_or_odd (a * a) with h | h
      · exact h
      · exact absurd hodd (by rw [Nat.not_odd_iff_even]; exact h.add_one)
    rcases Nat.even_mul.mp this with h | h <;> exact h
  · by_contra h
    push Not at h
    nlinarith

end OMA.P_oeis_a270361

/-- Two square roots `a, b < p` of `-1` mod `p` satisfy `a = b` or `a + b = p`; the latter is
impossible since both are even and `p` is odd. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a270361.main := by
  intro p hp hpo q₁ ⟨h1p, h1o, h1lt, h1s⟩ q₂ ⟨h2p, h2o, h2lt, h2s⟩
  obtain ⟨a, ha, hae, hap⟩ := OMA.P_oeis_a270361.root_facts p q₁ hp hpo h1p h1o h1lt h1s
  obtain ⟨b, hb, hbe, hbp⟩ := OMA.P_oeis_a270361.root_facts p q₂ hp hpo h2p h2o h2lt h2s
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have key : (p : ℤ) ∣ ((a : ℤ) - b) * ((a : ℤ) + b) :=
    ⟨(q₁ : ℤ) - q₂, by
      have ha' : (p : ℤ) * q₁ = a * a + 1 := by exact_mod_cast ha
      have hb' : (p : ℤ) * q₂ = b * b + 1 := by exact_mod_cast hb
      linear_combination hb' - ha'⟩
  rcases hpZ.dvd_or_dvd key with h | h
  · have hab : (a : ℤ) - b = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h
      rw [abs_lt]; constructor <;> omega
    have : a = b := by omega
    subst this
    have : p * q₁ = p * q₂ := by rw [ha, hb]
    exact Nat.eq_of_mul_eq_mul_left hp.pos this
  · exfalso
    obtain ⟨c, hc⟩ := h
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have hc2 : c < 2 := by
      by_contra hc2
      push Not at hc2
      have : (p : ℤ) * 2 ≤ p * c := by nlinarith
      omega
    have hc0 : 0 < c := by
      by_contra hc0
      push Not at hc0
      have : (p : ℤ) * c ≤ 0 := by nlinarith
      have ha0 : a = 0 := by omega
      subst ha0
      have : 2 * 2 ≤ p * q₁ := Nat.mul_le_mul hp.two_le h1p.two_le
      omega
    have hc1 : c = 1 := by omega
    subst hc1
    obtain ⟨x, hx⟩ := hae
    obtain ⟨y, hy⟩ := hbe
    obtain ⟨z, hz⟩ := hpo
    omega
