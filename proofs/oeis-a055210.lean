import OMAStatements.S_oeis_a055210

/-!
Source: https://oeis.org/A055210
Credit: @anmolspace (Lean proof). Velin Yanev posed the ratio identity in 2019.
The prime-power computation below also recovers Vladeta Jovovic's 2001 evaluation.
-/

namespace OMA.A055210Proof

open ArithmeticFunction Finset OMA.S_oeis_a055210
open scoped ArithmeticFunction.zeta

private theorem square_coprime_mul {m n : ℕ} (h : m.Coprime n) :
    IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  refine ⟨fun hs => ?_, fun hmn => hmn.1.mul hmn.2⟩
  obtain ⟨r, hr⟩ := hs.exists_sq
  have hg : IsUnit (gcd m n) := by
    change IsUnit (Nat.gcd m n)
    rw [h.gcd_eq_one]
    exact isUnit_one
  have hg' : IsUnit (gcd n m) := by simpa [gcd_comm] using hg
  exact ⟨(isSquare_iff_exists_sq m).mpr (exists_eq_pow_of_mul_eq_pow hg hr),
    (isSquare_iff_exists_sq n).mpr (exists_eq_pow_of_mul_eq_pow hg' (by rwa [mul_comm n m]))⟩

private noncomputable def squareTotient : ArithmeticFunction ℕ :=
  ⟨fun n => if IsSquare n then n.totient else 0, by simp⟩

private theorem squareTotient_mult : squareTotient.IsMultiplicative := by
  refine ⟨by simp [squareTotient], ?_⟩
  intro m n h
  by_cases hm : IsSquare m <;> by_cases hn : IsSquare n <;>
    simp [squareTotient, square_coprime_mul h, Nat.totient_mul h, hm, hn]

private theorem eval_sum (n : ℕ) : (ζ * squareTotient) n = a n := by
  classical
  rw [zeta_mul_apply, a, Finset.sum_filter]
  simp [squareTotient]

private theorem prime_pow_square {p : ℕ} (hp : p.Prime) (j : ℕ) :
    IsSquare (p ^ j) ↔ Even j := by
  constructor
  · intro hs
    obtain ⟨d, hd⟩ := hs.exists_sq
    have he := congrArg (fun n : ℕ => n.factorization p) hd
    refine ⟨d.factorization p, ?_⟩
    simpa [hp.factorization_pow, Nat.factorization_pow, two_mul] using he
  · rintro ⟨u, rfl⟩
    exact ⟨p ^ u, pow_add p u u⟩

private def localSum (p j : ℕ) : ℕ :=
  ∑ i ∈ range (j + 1), if Even i then (p ^ i).totient else 0

private theorem eval_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (ζ * squareTotient) (p ^ j) = localSum p j := by
  rw [zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  simp [localSum, squareTotient, prime_pow_square hp]

private theorem local_succ (p j : ℕ) : localSum p (j + 1) =
    localSum p j + (if Even (j + 1) then (p ^ (j + 1)).totient else 0) := by
  simp only [localSum, sum_range_succ]

private theorem local_odd (p u : ℕ) : localSum p (2 * u + 1) = localSum p (2 * u) := by
  rw [local_succ]
  simp

private theorem local_even {p : ℕ} (hp : p.Prime) (u : ℕ) :
    localSum p (2 * u) * (p + 1) = p ^ (2 * u + 1) + 1 := by
  have hp2 : (p - 1) * (p + 1) + 1 = p ^ 2 := by
    obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
    simp only [Nat.succ_eq_add_one, Nat.add_one_sub_one]
    ring
  induction u with
  | zero => simp [localSum]
  | succ u ih =>
    have he : Even ((2 * u + 1) + 1) := ⟨u + 1, by omega⟩
    rw [show 2 * (u + 1) = (2 * u + 1) + 1 by omega, local_succ, if_pos he,
      local_odd, Nat.totient_prime_pow_succ hp, add_mul, ih]
    calc
      _ = p ^ (2 * u + 1) * ((p - 1) * (p + 1) + 1) + 1 := by ring
      _ = _ := by rw [hp2, pow_succ, pow_succ]; ring

/-- Sum the first 2m powers in two blocks, then in neighboring pairs. -/
private theorem geometric_blocks (p m : ℕ) :
    (p ^ m + 1) * (∑ i ∈ range m, p ^ i) = (p + 1) * (∑ i ∈ range m, p ^ (i * 2)) := by
  have blocks : (∑ i ∈ range (m + m), p ^ i) = (p ^ m + 1) * (∑ i ∈ range m, p ^ i) := by
    rw [sum_range_add]
    simp_rw [pow_add]
    rw [← mul_sum]
    ring
  rw [← blocks]
  clear blocks
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show (m + 1) + (m + 1) = (m + m + 1) + 1 by omega,
      sum_range_succ, sum_range_succ, sum_range_succ, ih]
    rw [show m + m = m * 2 by omega, pow_succ]
    ring

private theorem prime_power_identity {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (ζ * squareTotient) (p ^ j) * sigma 1 (p ^ (2 * (j / 2))) =
      sigma 2 (p ^ (2 * (j / 2))) := by
  have same : localSum p j = localSum p (2 * (j / 2)) := by
    rcases (show j = 2 * (j / 2) ∨ j = 2 * (j / 2) + 1 by omega) with he | ho
    · exact congrArg (localSum p) he
    · exact (congrArg (localSum p) ho).trans (local_odd p _)
  rw [eval_prime_pow hp, same, sigma_apply_prime_pow hp, sigma_apply_prime_pow hp]
  simp only [mul_one]
  apply Nat.eq_of_mul_eq_mul_right (show 0 < p + 1 by omega)
  calc
    _ = (localSum p (2 * (j / 2)) * (p + 1)) * ∑ i ∈ range (2 * (j / 2) + 1), p ^ i := by ring
    _ = _ := by rw [local_even hp, geometric_blocks, mul_comm]

private theorem sigma_squarePart (k n : ℕ) : sigma k (squarePart n) =
    ∏ p ∈ n.primeFactors, sigma k (p ^ (2 * (n.factorization p / 2))) := by
  apply isMultiplicative_sigma.map_prod
  intro p hp q hq hpq
  exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)).mpr hpq).pow _ _

end OMA.A055210Proof

open OMA.A055210Proof OMA.S_oeis_a055210 ArithmeticFunction Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a055210.main := by
  intro n hn
  rw [← eval_sum, (isMultiplicative_zeta.mul squareTotient_mult).multiplicative_factorization _ hn.ne',
    Nat.prod_factorization_eq_prod_primeFactors, sigma_squarePart, sigma_squarePart, ← prod_mul_distrib]
  exact prod_congr rfl fun p hp => prime_power_identity (Nat.prime_of_mem_primeFactors hp) _
