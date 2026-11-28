import OMAStatements.S_oeis_a249760

-- Problem: A249760, conjectures (2) and (3): k + 1 is a Fermat prime and σ(k) a Mersenne prime.
-- Credit: @ShoQo
-- Proof: write k = p^e * m with p = minFac k and p ∤ m. σ is multiplicative, so
-- σ(k) = σ(p^e) σ(m), and σ(p^e) ≥ p^e ≥ 2 forces σ(m) = 1, so m = 1 and k = p^e. If p were
-- odd, k + 1 would be an even prime, so k = 1, but σ(1) = 1 is not prime. So k = 2^e, and
-- 2^e + 1 prime makes e a power of 2 (Nat.pow_of_pow_add_prime), while σ(2^e) = 2^(e+1) - 1.

open OMA.S_oeis_a249760 ArithmeticFunction

namespace OMA_A249760_Proof

lemma le_sigma {n : ℕ} (hn : n ≠ 0) : n ≤ sigma 1 n := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self n hn)

lemma sigma_two_pow (e : ℕ) : sigma 1 (2 ^ e) = mersenne (e + 1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq le_rfl, mersenne]
  simp

/-- If σ(k) is prime then k is a power of its least prime factor. -/
lemma eq_pow {k : ℕ} (hs : (sigma 1 k).Prime) : ∃ e, k = k.minFac ^ e := by
  have hk0 : k ≠ 0 := by rintro rfl; simp [Nat.not_prime_zero] at hs
  have hk1 : k ≠ 1 := by rintro rfl; simp [Nat.not_prime_one] at hs
  have hp : k.minFac.Prime := Nat.minFac_prime hk1
  obtain ⟨e, m, hpm, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 k.minFac hp.one_lt.ne'
  have hm0 : m ≠ 0 := by rintro rfl; simp at hk; exact hk0 hk
  have hcop : Nat.Coprime (k.minFac ^ e) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have hmul : sigma 1 k = sigma 1 (k.minFac ^ e) * sigma 1 m := by
    conv_lhs => rw [hk]
    exact isMultiplicative_sigma.map_mul_of_coprime hcop
  have he : e ≠ 0 := by
    rintro rfl
    apply hpm
    simp at hk
    rw [← hk]; exact Nat.minFac_dvd k
  have h2 : 2 ≤ sigma 1 (k.minFac ^ e) :=
    hp.two_le.trans ((Nat.le_self_pow he _).trans (le_sigma (pow_ne_zero _ hp.ne_zero)))
  rw [hmul, Nat.prime_mul_iff] at hs
  rcases hs with ⟨_, h1⟩ | ⟨_, h1⟩
  · have : m ≤ 1 := h1 ▸ le_sigma hm0
    have hm1 : m = 1 := by omega
    rw [hm1, mul_one] at hk
    exact ⟨e, hk⟩
  · omega

end OMA_A249760_Proof

open OMA_A249760_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a249760.main := by
  intro k hk1 hs
  obtain ⟨e, he⟩ := eq_pow hs
  have hk0 : k ≠ 0 := by rintro rfl; simp [Nat.not_prime_zero] at hs
  have hk1' : k ≠ 1 := by rintro rfl; simp [Nat.not_prime_one] at hs
  have hp : k.minFac.Prime := Nat.minFac_prime hk1'
  have he0 : e ≠ 0 := by rintro rfl; simp at he; exact hk1' he
  -- the least prime factor is 2: otherwise k is odd and k + 1 an even prime
  have h2 : k.minFac = 2 := by
    rcases hp.eq_two_or_odd' with h | hodd
    · exact h
    · exfalso
      have hkodd : Odd k := he ▸ hodd.pow
      have hev : Even (k + 1) := hkodd.add_one
      have := (Nat.Prime.even_iff hk1).1 hev
      exact hk1' (by omega)
  rw [h2] at he
  subst he
  refine ⟨?_, ⟨e + 1, sigma_two_pow e⟩⟩
  obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (by norm_num : 1 < 2) he0 hk1
  exact ⟨m, by rw [hm, Nat.fermatNumber]⟩
