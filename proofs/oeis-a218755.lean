import OMAStatements.S_oeis_a218755

-- Problem: A218755: Denominators of Bernoulli numbers which are == 6 (mod 9).
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Proof: by von Staudt–Clausen (`Bernoulli.vonStaudt_clausen`), every denominator divisible
-- by 3 is twice an odd number, hence ≡ 2 (mod 4); with ≡ 6 (mod 9) this fixes it mod 36.

namespace OMA.A218755

open Finset

private lemma den_dvd_of_mul (q : ℚ) (n m : ℤ) (h : q * n = m) (hn : n ≠ 0) :
    (q.den : ℤ) ∣ n := by
  have hq : q = Rat.divInt m n := by
    rw [Rat.divInt_eq_div, ← h]
    field_simp
  rw [hq]
  exact Rat.den_dvd m n

private lemma mul_int_of_den_dvd (q : ℚ) (n : ℤ) (h : (q.den : ℤ) ∣ n) :
    ∃ z : ℤ, q * n = z := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨q.num * c, ?_⟩
  push_cast
  rw [← mul_assoc, Rat.mul_den_eq_num]

private lemma even_case (k : ℕ) (hk : 1 ≤ k) : (bernoulli (2 * k)).den % 4 = 2 := by
  obtain ⟨N, hN⟩ := Bernoulli.vonStaudt_clausen k
  set s := (range (2 * k + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ 2 * k) with hs
  have h2 : 2 ∈ s := by
    rw [hs, mem_filter, mem_range]
    exact ⟨by omega, Nat.prime_two, by simp⟩
  set u := s.erase 2 with hu
  have hsum : ∑ p ∈ s, (1 : ℚ) / p = 1 / 2 + ∑ p ∈ u, (1 : ℚ) / p := by
    rw [hu, ← add_sum_erase s _ h2]
    norm_num
  have hprime : ∀ p ∈ u, p.Prime ∧ p ≠ 2 := by
    intro p hp
    rw [hu, mem_erase] at hp
    rw [hs, mem_filter] at hp
    exact ⟨hp.2.2.1, hp.1⟩
  set Q : ℕ := ∏ p ∈ u, p with hQ
  have hQodd : ¬ 2 ∣ Q := by
    intro h
    rw [hQ, (Nat.prime_two.prime).dvd_finsetProd_iff] at h
    obtain ⟨p, hp, h2p⟩ := h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hprime p hp).1).1 h2p
    exact (hprime p hp).2 this.symm
  set M : ℕ := ∑ p ∈ u, ∏ x ∈ u.erase p, x with hM
  have hQM : (Q : ℚ) * ∑ p ∈ u, (1 : ℚ) / p = M := by
    rw [hQ, hM, mul_sum]
    push_cast
    refine sum_congr rfl fun p hp => ?_
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hprime p hp).1.ne_zero
    rw [← mul_prod_erase u (fun x => (x : ℚ)) hp]
    field_simp
  set B := bernoulli (2 * k) with hB
  have hBN : B = N - 1 / 2 - ∑ p ∈ u, (1 : ℚ) / p := by
    rw [hsum] at hN
    linarith
  -- B * (2Q) is an integer
  have h2Q : B * ((2 * Q : ℕ) : ℤ) = ((2 * Q * N - Q - 2 * M : ℤ) : ℚ) := by
    rw [hBN]
    push_cast
    have : (2 * (Q : ℚ)) * ∑ p ∈ u, (1 : ℚ) / p = 2 * M := by rw [mul_assoc, hQM]
    linear_combination (-1 : ℚ) * this
  have hQpos : 0 < Q := by
    rw [hQ]
    exact prod_pos fun p hp => (hprime p hp).1.pos
  have hdvd : (B.den : ℤ) ∣ ((2 * Q : ℕ) : ℤ) :=
    den_dvd_of_mul B _ _ h2Q (by positivity)
  have hdvd' : B.den ∣ 2 * Q := by exact_mod_cast hdvd
  -- the denominator is even
  have heven : 2 ∣ B.den := by
    by_contra hodd
    have hcop : Nat.Coprime B.den 2 :=
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd))
    have hdQ : B.den ∣ Q := hcop.dvd_of_dvd_mul_left hdvd'
    obtain ⟨z, hz⟩ := mul_int_of_den_dvd B (Q : ℤ) (by exact_mod_cast hdQ)
    have hhalf : ((Q : ℤ) : ℚ) = 2 * ((Q * N - M - z : ℤ) : ℚ) := by
      rw [hBN] at hz
      push_cast at hz ⊢
      have : (Q : ℚ) * ∑ p ∈ u, (1 : ℚ) / p = M := hQM
      linear_combination (-2 : ℚ) * hz - 2 * this
    have hQZ : (Q : ℤ) = 2 * (Q * N - M - z) := by exact_mod_cast hhalf
    apply hQodd
    have : (2 : ℤ) ∣ (Q : ℤ) := ⟨_, hQZ⟩
    exact_mod_cast this
  obtain ⟨e, he⟩ := heven
  have heQ : e ∣ Q := by
    rw [he] at hdvd'
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd'
  have heodd : ¬ 2 ∣ e := fun h => hQodd (h.trans heQ)
  omega

theorem den_mod_four (i : ℕ) (h3 : 3 ∣ (bernoulli i).den) : (bernoulli i).den % 4 = 2 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h3
    · exact even_case k hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [bernoulli_one] at h3
      norm_num at h3
    · have hz : bernoulli (2 * k + 1) = 0 := bernoulli_eq_zero_of_odd ⟨k, rfl⟩ (by omega)
      rw [hz] at h3
      simp at h3

end OMA.A218755

theorem OMA.solution : type_of% @OMA.S_oeis_a218755.main := by
  intro i j hi hj
  have hi4 := OMA.A218755.den_mod_four i (by omega)
  have hj4 := OMA.A218755.den_mod_four j (by omega)
  omega
