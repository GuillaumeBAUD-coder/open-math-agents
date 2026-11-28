import OMAStatements.S_oeis_a279915

-- Problem: A279915: Numbers m that can be written as x*y with phi(x)*sigma(y) = 2*x*y, where x and y are positive integers, phi(.) is Euler's totient function and sigma(y) is the sum of all positive divisors of y.
-- Upstream: formal-conjectures statements/oeis-a279915.lean:0 (declaration OMA.S_oeis_a279915.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: x = 127 and y = 173369889 = 3^4 * 7^2 * 11^2 * 19^2. By multiplicativity
-- sigma(y) = 121 * 57 * 133 * 381 = 349491681, and phi(127) = 126, so
-- phi(x) * sigma(y) = 44035951806 = 2 * x * y although y is odd: part (i) fails.

namespace H11A279915

theorem sig_pp (p i v : ℕ) (hp : p.Prime) (hv : ∑ k ∈ Finset.range (i + 1), p ^ k = v) :
    ArithmeticFunction.sigma 1 (p ^ i) = v := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, hv]

theorem mulstep (a b va vb : ℕ) (hc : Nat.Coprime a b) (ha : ArithmeticFunction.sigma 1 a = va)
    (hb : ArithmeticFunction.sigma 1 b = vb) : ArithmeticFunction.sigma 1 (a * b) = va * vb := by
  have e := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hc
  rw [ha, hb] at e
  exact e

theorem p7 : Nat.Prime 7 := by norm_num

theorem p11 : Nat.Prime 11 := by norm_num

theorem p19 : Nat.Prime 19 := by norm_num

theorem s3 : ArithmeticFunction.sigma 1 (3 ^ 4) = 121 :=
  sig_pp 3 4 121 Nat.prime_three (by norm_num [Finset.sum_range_succ])

theorem s7 : ArithmeticFunction.sigma 1 (7 ^ 2) = 57 :=
  sig_pp 7 2 57 p7 (by norm_num [Finset.sum_range_succ])

theorem s11 : ArithmeticFunction.sigma 1 (11 ^ 2) = 133 :=
  sig_pp 11 2 133 p11 (by norm_num [Finset.sum_range_succ])

theorem s19 : ArithmeticFunction.sigma 1 (19 ^ 2) = 381 :=
  sig_pp 19 2 381 p19 (by norm_num [Finset.sum_range_succ])

theorem c3_7 : Nat.Coprime 3 7 := (Nat.coprime_primes Nat.prime_three p7).mpr (by norm_num)

theorem c3_11 : Nat.Coprime 3 11 := (Nat.coprime_primes Nat.prime_three p11).mpr (by norm_num)

theorem c3_19 : Nat.Coprime 3 19 := (Nat.coprime_primes Nat.prime_three p19).mpr (by norm_num)

theorem c7_11 : Nat.Coprime 7 11 := (Nat.coprime_primes p7 p11).mpr (by norm_num)

theorem c7_19 : Nat.Coprime 7 19 := (Nat.coprime_primes p7 p19).mpr (by norm_num)

theorem c11_19 : Nat.Coprime 11 19 := (Nat.coprime_primes p11 p19).mpr (by norm_num)

theorem sY : ArithmeticFunction.sigma 1 (3 ^ 4 * 7 ^ 2 * 11 ^ 2 * 19 ^ 2) =
    121 * 57 * 133 * 381 := by
  have h1 := mulstep (3 ^ 4) (7 ^ 2) 121 57 (Nat.Coprime.pow 4 2 c3_7) s3 s7
  have h2 := mulstep (3 ^ 4 * 7 ^ 2) (11 ^ 2) (121 * 57) 133
    (Nat.Coprime.mul_left (Nat.Coprime.pow 4 2 c3_11) (Nat.Coprime.pow 2 2 c7_11)) h1 s11
  exact mulstep (3 ^ 4 * 7 ^ 2 * 11 ^ 2) (19 ^ 2) (121 * 57 * 133) 381
    (Nat.Coprime.mul_left
      (Nat.Coprime.mul_left (Nat.Coprime.pow 4 2 c3_19) (Nat.Coprime.pow 2 2 c7_19))
      (Nat.Coprime.pow 2 2 c11_19)) h2 s19

theorem hsig : ArithmeticFunction.sigma 1 173369889 = 349491681 := by
  have hy : (173369889 : ℕ) = 3 ^ 4 * 7 ^ 2 * 11 ^ 2 * 19 ^ 2 := by norm_num
  calc ArithmeticFunction.sigma 1 173369889
      = ArithmeticFunction.sigma 1 (3 ^ 4 * 7 ^ 2 * 11 ^ 2 * 19 ^ 2) := by rw [hy]
    _ = 121 * 57 * 133 * 381 := sY
    _ = 349491681 := by norm_num

theorem hphi : Nat.totient 127 = 126 :=
  (Nat.totient_prime (by norm_num : Nat.Prime 127)).trans (by norm_num)

theorem key : Nat.totient 127 * ArithmeticFunction.sigma 1 173369889 = 2 * 127 * 173369889 := by
  calc Nat.totient 127 * ArithmeticFunction.sigma 1 173369889 = 126 * 349491681 := by
        rw [hphi, hsig]
    _ = 2 * 127 * 173369889 := by norm_num

end H11A279915

open OMA.S_oeis_a279915 H11A279915 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a279915.main) := by
  intro H
  have hc : ConjI := H.1
  unfold ConjI at hc
  have hev : Even 173369889 := hc.2 127 173369889 (by norm_num) (by norm_num) key
  obtain ⟨r, hr⟩ := hev
  omega
