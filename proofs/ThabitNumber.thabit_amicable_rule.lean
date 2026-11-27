import FormalConjectures.Wikipedia.ThabitNumber

-- Problem: Thābit ibn Qurra's amicable number theorem
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/ThabitNumber.lean:76 (declaration ThabitNumber.thabit_amicable_rule)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- The sum of divisors of a power of two: `σ(2^k) + 1 = 2^(k+1)`. -/
theorem OMA.sigma_two_pow (k : ℕ) :
    ArithmeticFunction.sigma 1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ 2 (k + 1)]
    omega

/-- The sum of divisors of a prime `p` is `p + 1`. -/
theorem OMA.sigma_prime {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 p = p + 1 := by
  rw [ArithmeticFunction.sigma_one_apply, hp.sum_divisors]

/-- The arithmetic core of Thābit's rule, with `t = 2^(n-1)`, `N = 2^n`, `S = σ(N)`. -/
theorem OMA.thabit_core {t N P Q R : ℕ} (ht : 2 ≤ t) (hN : N = 2 * t)
    (hS : ArithmeticFunction.sigma 1 N + 1 = 4 * t)
    (hNP : Nat.Coprime N P) (hNQ : Nat.Coprime N Q) (hNR : Nat.Coprime N R)
    (hP : P + 1 = 3 * t) (hQ : Q + 1 = 6 * t) (hR : R + 1 = 18 * (t * t))
    (hp : P.Prime) (hq : Q.Prime) (hr : R.Prime) :
    IsAmicable (N * P * Q) (N * R) := by
  have hPQ : Nat.Coprime P Q := (Nat.coprime_primes hp hq).2 (by omega)
  have hsA : ArithmeticFunction.sigma 1 (N * P * Q)
      = ArithmeticFunction.sigma 1 N * (P + 1) * (Q + 1) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (Nat.Coprime.mul_left hNQ hPQ),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hNP,
      OMA.sigma_prime hp, OMA.sigma_prime hq]
  have hsB : ArithmeticFunction.sigma 1 (N * R)
      = ArithmeticFunction.sigma 1 N * (R + 1) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hNR,
      OMA.sigma_prime hr]
  generalize ArithmeticFunction.sigma 1 N = S at hS hsA hsB
  zify at hS hP hQ hR
  have zS : (S : ℤ) = 4 * t - 1 := by omega
  have zP : (P : ℤ) = 3 * t - 1 := by omega
  have zQ : (Q : ℤ) = 6 * t - 1 := by omega
  have zR : (R : ℤ) = 18 * (t * t) - 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hsA, hN]
    zify
    rw [zS, zP, zQ, zR]
    ring
  · rw [hsB, hN]
    zify
    rw [zS, zP, zQ, zR]
    ring
  · intro h
    have h2 : P * Q = R := by
      have hN0 : 0 < N := by omega
      have : N * (P * Q) = N * R := by rw [← mul_assoc]; exact h
      exact Nat.eq_of_mul_eq_mul_left hN0 this
    have z2 : (P : ℤ) * Q = R := by exact_mod_cast h2
    rw [zP, zQ, zR] at z2
    have ht' : (2 : ℤ) ≤ t := by exact_mod_cast ht
    nlinarith

theorem OMA.solution : type_of% @ThabitNumber.thabit_amicable_rule := by
  intro n hn hp hq hr
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  rw [Nat.add_sub_cancel] at hp
  have ht : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have e1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have e2 : 2 ^ (2 * (m + 1) - 1) = 2 * (2 ^ m * 2 ^ m) := by
    have : 2 * (m + 1) - 1 = m + m + 1 := by omega
    rw [this, pow_succ, pow_add]; ring
  have hS : ArithmeticFunction.sigma 1 (2 ^ (m + 1)) + 1 = 4 * 2 ^ m := by
    rw [OMA.sigma_two_pow, pow_succ, pow_succ]; ring
  unfold ThabitNumber.thabitNumber at hp hq ⊢
  rw [e2] at hr ⊢
  have hP : 3 * 2 ^ m - 1 + 1 = 3 * 2 ^ m := by omega
  have hQ : 3 * 2 ^ (m + 1) - 1 + 1 = 6 * 2 ^ m := by omega
  have hR : 9 * (2 * (2 ^ m * 2 ^ m)) - 1 + 1 = 18 * (2 ^ m * 2 ^ m) := by
    have : 0 < 2 ^ m * 2 ^ m := by positivity
    omega
  have odd_cop : ∀ {x : ℕ}, x.Prime → x ≠ 2 → Nat.Coprime (2 ^ (m + 1)) x := by
    intro x hx hx2
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hx).2 (Ne.symm hx2))
  have hp2 : 3 * 2 ^ m - 1 ≠ 2 := by omega
  have hq2 : 3 * 2 ^ (m + 1) - 1 ≠ 2 := by omega
  have hr2 : 9 * (2 * (2 ^ m * 2 ^ m)) - 1 ≠ 2 := by
    have : 4 ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul ht ht
    omega
  exact OMA.thabit_core ht e1 hS (odd_cop hp hp2) (odd_cop hq hq2)
    (odd_cop hr hr2) hP hQ hR hp hq hr
